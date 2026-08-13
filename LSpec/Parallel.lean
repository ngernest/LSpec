module
public import LSpec.LSpec

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
- `maxConcurrent := some n`: the tests are split into `n` chains of tasks linked by
  `IO.bindTask`, the analogue of passing `-j n`.

Both levels are built only from the task combinators in `Init.System.IO` — `IO.asTask` to launch
a test and `IO.bindTask` to make one test wait for another. There is no lock, no shared counter
and no promise anywhere: every ordering constraint is expressed as a dependency between tasks,
which is what the reference manual recommends over blocking on results.

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
  one worker per core (configurable via `LEAN_NUM_THREADS`). `some n` splits the tests into `n`
  chains of tasks, so at most `n` are ever in flight; `some 0` is treated as `some 1`.
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

/--
The tasks launched so far, in traversal order. Threading this through successive `TestSeq`s is
what lets `lspecIOParallel` bound concurrency across *all* suites rather than per suite.
-/
private abbrev SpawnState := Array (Task (Except IO.Error IOTestOutcome))

/--
Launches every deferred test onto one of `n` concurrent *chains* of tasks.

The `i`-th deferred test is chained onto the task of test `i - n` with `IO.bindTask`, so it only
starts once that task has finished. This partitions the tests into `n` chains that each run
their own tests one after another, which bounds the number of tests in flight at `n` without any
explicit synchronisation: the dependency is carried by the tasks themselves. The reference manual
recommends exactly this, preferring `Task.bind`/`IO.bindTask` over blocking on `Task.get` to set
up task dependencies, since blocking has to grow the thread pool to avoid starvation.

Each task still carries its own test's result, so the renderer waits on tests individually and
prints them in sequence order.

The chains are a static round-robin split rather than a work-stealing queue, so one very slow
property delays the rest of its chain. That is the trade for needing no shared mutable state;
with more tests than chains the imbalance averages out. Use the default `maxConcurrent := none`
to let Lean's scheduler balance the work itself.
-/
private def spawnChained (n : Nat) : TestSeq → SpawnState → BaseIO (TestSeq × SpawnState) :=
  go
where
  /-- `started` holds the task of every deferred test launched so far, in traversal order, so
      that `started[i - n]` is the tail of the chain the `i`-th test belongs to. -/
  go : TestSeq → SpawnState → BaseIO (TestSeq × SpawnState)
    | .done, started => pure (.done, started)
    | .individual d p ps i next, started => do
      let (next', started) ← go next started
      pure (.individual d p ps i next', started)
    | .individualIO d ps action next, started => do
      let idx := started.size
      -- The first `n` tests open the chains; later tests extend one. Note `idx - n` truncates
      -- to `0` on `Nat`, so the `idx < n` case has to come first.
      let task ←
        if idx < n then
          IO.asTask action Task.Priority.dedicated
        else
          match started[idx - n]? with
          | some tail =>
            -- The previous result is ignored, so a throwing test does not strand its chain.
            IO.bindTask tail fun _ => IO.asTask action Task.Priority.dedicated
          | none => IO.asTask action Task.Priority.dedicated
      let (next', started) ← go next (started.push task)
      pure (.individualIO d ps (awaitTask task) next', started)
    | .individualSeededIO d ps action next, started => do
      let (next', started) ← go next started
      pure (.individualSeededIO d ps action next', started)
    | .group d ts next, started => do
      let (ts', started) ← go ts started
      let (next', started) ← go next started
      pure (.group d ts' next', started)

/-- Assigns seeds, then spawns, continuing the chains recorded in `started` so that a caller
    spawning several `TestSeq`s in turn keeps one shared concurrency bound across all of them. -/
private def spawnIOFrom (cfg : ParallelConfig) (tSeq : TestSeq) (started : SpawnState) :
    BaseIO (TestSeq × SpawnState) := do
  let seeded := tSeq.assignSeeds cfg.baseSeed
  match cfg.maxConcurrent with
  | none => (·, started) <$> spawnUnbounded seeded
  | some n => spawnChained (max n 1) seeded started

/--
Starts every deferred test in `tSeq` running concurrently and returns a `TestSeq` of the same
shape in which each deferred action waits for its already-running counterpart.

This is the scheduling half of the runner; pass the result to `TestSeq.runIOAux` (or just use
`TestSeq.runIOParallel`) to render it. Splitting the two makes the parallelism composable: a
caller can spawn several independent `TestSeq`s and only then start printing, which is how
`lspecIOParallel` overlaps work across suites.
-/
def TestSeq.spawnIO (tSeq : TestSeq) (cfg : ParallelConfig := {}) : BaseIO TestSeq :=
  Prod.fst <$> spawnIOFrom cfg tSeq #[]

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

  -- Schedule everything first so that suites overlap, then render in order. The spawn state is
  -- threaded across suites so `maxConcurrent` bounds the whole run, not each suite separately.
  let mut started : SpawnState := #[]
  let mut spawned : Array (String × List TestSeq) := #[]
  for (key, tSeqs) in entries do
    let mut spawnedSeqs : Array TestSeq := #[]
    for tSeq in tSeqs do
      let (tSeq', started') ← spawnIOFrom cfg tSeq started
      started := started'
      spawnedSeqs := spawnedSeqs.push tSeq'
    spawned := spawned.push (key, spawnedSeqs.toList)

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
