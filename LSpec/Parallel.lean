module
public import LSpec.LSpec
public import Std.Sync.Mutex

/-!
# Parallel test execution for `LSpec`

This module runs the *deferred* tests of a `TestSeq` — the `individualIO` and
`individualSeededIO` nodes produced by `checkIO` and `checkPlausibleIO` — concurrently,
in the spirit of Haskell's [`tasty`](https://github.com/UnkindPartition/tasty).

## Design

`tasty` separates *scheduling* from *reporting*: every test is launched concurrently, each
writing into its own result cell, while the reporter walks the test tree in its original order
and blocks on each cell in turn. Output is therefore byte-for-byte identical to a sequential
run, no matter how the tests interleave.

The same split is used here, and it falls out of `TestSeq` being a tree of `IO` actions:

1. `TestSeq.spawnIO` walks the sequence once and replaces each deferred action with an action
   that merely *waits* for an already-running `Task`. It returns a `TestSeq` of the same shape.
2. The existing `TestSeq.runIOAux` then renders that sequence exactly as before.

So the parallel runner reuses the sequential renderer verbatim rather than duplicating it, and
`runIO`/`runIOParallel` agree on ordering, formatting, indentation and the final `Bool`.

## Reproducibility

Plausible and SlimCheck both draw randomness from a global `stdGenRef` whose own documentation
warns that it "is not thread local, hence two threads accessing it at the same time will get the
exact same generator". Deferred property tests therefore take their seed from
`TestSeq.assignSeeds`, which derives it from the test's *position* in the sequence. Samples then
depend only on `baseSeed` and position, never on scheduling order, so a parallel run reproduces
the sequential one and a failing test can be replayed with the reported `randomSeed`.

## Concurrency level

- `maxConcurrent := none` (default): each test becomes a regular-priority `Task`. Lean's task
  scheduler allocates no more workers than there are cores, so this is the analogue of `tasty`'s
  default `-j <numCores>`. Override with the `LEAN_NUM_THREADS` environment variable.
- `maxConcurrent := some n`: a work-stealing pool of exactly `n` dedicated threads pulls tests
  off a shared queue, the analogue of passing `-j n`.

## Caveats

- Only *deferred* tests are parallelised. `test` and `check`/`checkPlausible` are evaluated
  during elaboration and are already values by the time a runner sees them.
- Tests must be independent. A test that touches shared mutable state, the working directory,
  or a fixed port is not safe to run this way; keep those in a sequential `runIO`.
- Unlike `lspecIO`, a parallel run holds every test's state live at once, so it trades memory
  for wall-clock time.
-/

namespace LSpec
public section

/-- Configuration for the parallel `TestSeq` runners. -/
structure ParallelConfig where
  /--
  Maximum number of tests to run at once. `none` defers to Lean's task scheduler, which uses
  one worker per core (configurable via `LEAN_NUM_THREADS`). `some n` uses a pool of exactly
  `n` dedicated threads; `some 0` is treated as `some 1`.
  -/
  maxConcurrent : Option Nat := none
  /--
  Base RNG seed for deferred property tests. The `i`-th deferred test uses
  `seedFor baseSeed i`, so re-running with the same `baseSeed` replays the same samples.
  -/
  baseSeed : Nat := 0
  deriving Inhabited

/-- The payload produced by a deferred (`IO`) test: `(success, numSamples, totalTests, errorMsg)`. -/
abbrev IOTestOutcome := Bool × Nat × Nat × Option String

section Spawning

/-- Turns a task carrying a possibly-failed test run back into an `IO` action, re-raising the
    original `IO.Error` so that a parallel run reports failures just like a sequential one. -/
private def awaitTask (task : Task (Except IO.Error IOTestOutcome)) : IO IOTestOutcome := do
  match ← IO.wait task with
  | .ok outcome => pure outcome
  | .error e => throw e

/-- Waits on a promise filled in by a worker thread. A `none` result means the promise was
    dropped without being resolved, which can only happen if the worker pool died. -/
private def awaitPromise (promise : IO.Promise (Except IO.Error IOTestOutcome)) :
    IO IOTestOutcome := do
  match ← IO.wait promise.result? with
  | some (.ok outcome) => pure outcome
  | some (.error e) => throw e
  | none => throw <| .userError "LSpec: test was never scheduled (worker pool terminated early)"

/-- Launches every deferred test as its own regular-priority `Task`, letting Lean's scheduler
    bound the concurrency to the number of cores. -/
private def spawnUnbounded : TestSeq → BaseIO TestSeq
  | .done => pure .done
  | .individual d p ps i n => (.individual d p ps i) <$> spawnUnbounded n
  | .individualIO d ps action n => do
    let task ← IO.asTask action
    pure <| .individualIO d ps (awaitTask task) (← spawnUnbounded n)
  | .individualSeededIO d ps action n =>
    -- Unreachable after `assignSeeds`; kept total so the traversal cannot silently drop a test.
    (.individualSeededIO d ps action) <$> spawnUnbounded n
  | .group d ts n => do
    let ts' ← spawnUnbounded ts
    pure <| .group d ts' (← spawnUnbounded n)

/-- One unit of queued work: the test's action and the promise its result is published to. -/
private structure Work where
  action : IO IOTestOutcome
  promise : IO.Promise (Except IO.Error IOTestOutcome)

/-- Replaces each deferred test with a wait on a fresh promise, collecting the corresponding
    work items in traversal order. -/
private def enqueue (queue : IO.Ref (Array Work)) : TestSeq → BaseIO TestSeq
  | .done => pure .done
  | .individual d p ps i n => (.individual d p ps i) <$> enqueue queue n
  | .individualIO d ps action n => do
    let promise ← IO.Promise.new
    queue.modify (·.push { action, promise })
    pure <| .individualIO d ps (awaitPromise promise) (← enqueue queue n)
  | .individualSeededIO d ps action n =>
    (.individualSeededIO d ps action) <$> enqueue queue n
  | .group d ts n => do
    let ts' ← enqueue queue ts
    pure <| .group d ts' (← enqueue queue n)

/-- A single pool worker: repeatedly claims the next unclaimed test and resolves its promise.
    Claiming is guarded by a mutex, which gives work-stealing rather than a static split, so a
    few slow properties cannot leave the other threads idle. -/
private partial def worker (queue : Array Work) (cursor : Std.Mutex Nat) : BaseIO Unit := do
  let idx ← cursor.atomically (do let idx ← get; set (idx + 1); pure idx)
  if let some work := queue[idx]? then
    -- `toBaseIO` keeps a throwing test from killing the worker and stranding later promises.
    work.promise.resolve (← work.action.toBaseIO)
    worker queue cursor

/-- Launches every deferred test onto a pool of exactly `n` dedicated threads. -/
private def spawnBounded (tSeq : TestSeq) (n : Nat) : BaseIO TestSeq := do
  let queueRef ← IO.mkRef #[]
  let rewritten ← enqueue queueRef tSeq
  let queue ← queueRef.get
  let cursor ← Std.Mutex.new 0
  -- Never spawn more threads than there is work, and never spawn zero threads for real work.
  for _ in [0 : min (max n 1) queue.size] do
    let _ ← IO.asTask (worker queue cursor) Task.Priority.dedicated
  pure rewritten

/--
Starts every deferred test in `tSeq` running concurrently and returns a `TestSeq` of the same
shape in which each deferred action waits for its already-running counterpart.

This is the scheduling half of the runner; pass the result to `TestSeq.runIOAux` (or just use
`TestSeq.runIOParallel`) to render it. Splitting the two makes the parallelism composable: a
caller can spawn several independent `TestSeq`s and only then start printing, which is how
`lspecIOParallel` overlaps work across suites.
-/
def TestSeq.spawnIO (tSeq : TestSeq) (cfg : ParallelConfig := {}) : BaseIO TestSeq := do
  let seeded := tSeq.assignSeeds cfg.baseSeed
  match cfg.maxConcurrent with
  | none => spawnUnbounded seeded
  | some n => spawnBounded seeded n

end Spawning

/--
Parallel counterpart to `TestSeq.runIO`: runs the sequence's deferred tests concurrently and
returns `(success, output)`.

The output is identical to `TestSeq.runIO`'s for the same sequence and `baseSeed` — same order,
same samples, same counterexamples — so this is a drop-in replacement whenever the tests are
independent.

```lean
def props : TestSeq :=
  checkPlausibleIO' "add_comm"  (∀ n m : Nat, n + m = m + n) ++
  checkPlausibleIO' "mul_comm"  (∀ n m : Nat, n * m = m * n) ++
  checkPlausibleIO' "append_nil" (∀ l : List Nat, l ++ [] = l)

-- All three properties are tested at the same time.
#eval do let (ok, out) ← props.runIOParallel; IO.println out; pure ok

-- Cap concurrency at two threads and replay a specific run.
#eval props.runIOParallel { maxConcurrent := some 2, baseSeed := 42 }
```
-/
def TestSeq.runIOParallel (tSeq : TestSeq) (cfg : ParallelConfig := {}) (indent := 0) :
    IO (Bool × String) := do
  (← tSeq.spawnIO cfg).runIOAux indent

open Std (HashMap) in
/--
Parallel counterpart to `lspecIO`. Returns `0` on success, `1` on failure.

Every test in every selected suite is scheduled up front, so properties run concurrently
*across* suites as well as within them; results are then printed suite by suite in the usual
order. Deferred tests are seeded per suite, so each suite reproduces exactly what it would
produce under `lspecIO` with the same `baseSeed`.

Because all suites are live simultaneously this gives up `lspecIO`'s incremental memory
behaviour (which releases each suite as it finishes). Prefer `lspecIO` for suites that are
memory-heavy rather than time-heavy, and note that tests sharing mutable state are not safe
to run here at all.

```lean
def main (args : List String) : IO UInt32 :=
  lspecIOParallel (.ofList [("math", [mathTests]), ("strings", [stringTests])]) args
```
-/
def lspecIOParallel (map : HashMap String (List TestSeq)) (args : List String)
    (cfg : ParallelConfig := {}) : IO UInt32 := do
  let entries : List (String × List TestSeq) :=
    if args.isEmpty then map.toList
    else Id.run do
      let mut acc := []
      for arg in args do
        for (key, tSeqs) in map do
          if key.startsWith arg then
            acc := (key, tSeqs) :: acc
      pure acc

  -- Schedule everything first so that suites overlap, then render in order.
  let spawned ← entries.mapM fun (key, tSeqs) =>
    (key, ·) <$> tSeqs.mapM (·.spawnIO cfg)

  let mut testsWithErrors : Array (String × Array String) := #[]
  for (key, tSeqs) in spawned do
    IO.println key
    let mut errors := #[]
    for tSeq in tSeqs do
      let (success, msg) ← tSeq.runIOAux (indent := 2)
      if success then
        IO.println msg
      else
        IO.eprintln msg
        errors := errors.push msg
    unless errors.isEmpty do
      testsWithErrors := testsWithErrors.push (key, errors)

  if testsWithErrors.isEmpty then return 0

  IO.eprintln "-------------------------------- Failing tests ---------------------------------"
  for (key, msgs) in testsWithErrors do
    IO.eprintln key
    for msg in msgs do
      IO.eprintln msg
  return 1

end
end LSpec
