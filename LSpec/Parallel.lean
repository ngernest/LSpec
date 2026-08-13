module
public import LSpec.LSpec
public import Std.Sync.Channel

/-!
# Parallel test execution for `LSpec`

This module runs the *deferred* tests of a `TestSeq` — the `individualIO` and
`individualSeededIO` nodes produced by `checkIO` and `checkPlausibleIO` — concurrently.

## Design

*Scheduling* is separated from *reporting*: every test is launched concurrently, each writing
into its own result cell, while the reporter walks the test tree in its original order and blocks
on each cell in turn. Output is therefore byte-for-byte identical to a sequential run, no matter
how the tests interleave.

That split falls out of `TestSeq` being a tree of `IO` actions:

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

`ParallelConfig.maxConcurrent` caps the tests in flight. It defaults to `numCores`, the number
of CPU cores available to the process. `some n` overrides it.

The cap is a thread pool: `n` workers pull tests off one shared `Std.CloseableChannel`, and each
publishes its test's result to an `IO.Promise` that the renderer waits on. Since a worker runs one
test at a time, at most `n` are ever in flight. Since the queue is shared, whichever worker is
free takes the next test, so one slow property does not hold up work the others could be doing.

Closing the queue after everything is enqueued is what stops the workers: a closed channel still
delivers whatever is already queued, then resolves its consumers to `none`.

Workers run on `Task.Priority.dedicated` threads. The reference manual recommends dedicated
threads for long-running work, and they reach full concurrency at once, whereas regular-priority
pool tasks ramp up lazily and measured slower on suites of many short tests.

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

/-- Memoises `numCores`, whose detection may cost a subprocess. -/
private initialize numCoresCache : IO.Ref (Option Nat) ← IO.mkRef none

/--
The number of tests to run at once by default: the number of CPU cores available to the process.

Resolved in this order:

1. `LEAN_NUM_THREADS`, since that is what bounds Lean's own task scheduler.
2. `NUMBER_OF_PROCESSORS`, which Windows publishes in the environment.
3. `sysctl -n hw.logicalcpu` on macOS, `nproc` elsewhere.
4. `1` if none of the above answer, which runs the tests one at a time.

Lean's core count is only reachable through an internal symbol that the interpreter cannot
resolve, which would break `#eval` on the parallel runners, so the count is read from the
environment or the OS instead. The runners resolve it once per run, not once per suite.
-/
def numCores : BaseIO Nat := do
  -- Detection can cost a subprocess, so only ever do it once per process.
  if let some cached ← numCoresCache.get then return cached
  let detected ← detect
  numCoresCache.set (some detected)
  return detected
where
  detect : BaseIO Nat := do
    if let some n ← envNat "LEAN_NUM_THREADS" then return n
    if let some n ← envNat "NUMBER_OF_PROCESSORS" then return n
    let (cmd, args) :=
      if System.Platform.isOSX then ("sysctl", #["-n", "hw.logicalcpu"]) else ("nproc", #[])
    match ← (IO.Process.output { cmd, args }).toBaseIO with
    | .ok out => return max 1 (out.stdout.trimAscii.toNat?.getD 1)
    | .error _ => return 1
  /-- Reads a positive `Nat` from the environment variable `name`. -/
  envNat (name : String) : BaseIO (Option Nat) := do
    let some raw ← IO.getEnv name | return none
    return (raw.trimAscii.toNat?).filter (· > 0)

/-- Configuration for the parallel `TestSeq` runners. -/
structure ParallelConfig where
  /--
  Maximum number of tests to run at once. `none`, the default, uses `numCores`. `some n` runs at
  most `n` tests at once; `some 0` is treated as `some 1`, which runs them one at a time.
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

/-- One queued test: the action to run, and the promise its result is published to. -/
private structure Work where
  /-- The test to run. -/
  action : IO IOTestOutcome
  /-- Where the worker publishes the result, successful or not. -/
  promise : IO.Promise (Except IO.Error IOTestOutcome)

/-- Waits for a worker to publish this test's result, re-raising the original `IO.Error` so that
    a parallel run reports a throwing test just like a sequential one. `Promise.result?` is used
    rather than `result!` so that a dropped promise is an error instead of a hang. -/
private def awaitResult (promise : IO.Promise (Except IO.Error IOTestOutcome)) :
    IO IOTestOutcome := do
  match ← IO.wait promise.result? with
  | some (.ok outcome) => pure outcome
  | some (.error e) => throw e
  | none => throw <| .userError "LSpec: a test's result was dropped before the test ran"

/-- A worker: runs queued tests until the queue closes, publishing each result to its promise.
    `toBaseIO` keeps a throwing test from killing the worker and stranding later promises. -/
private def worker (queue : Std.CloseableChannel Work) : BaseIO Unit := do
  for work in queue.sync do
    work.promise.resolve (← work.action.toBaseIO)

/-- Replaces every deferred test with a wait on a fresh promise, putting the work on `queue`.
    Returns a `TestSeq` of the same shape, so the renderer is unchanged. -/
private def enqueue (queue : Std.CloseableChannel Work) : TestSeq → BaseIO TestSeq
  | .done => pure .done
  | .individual d p ps i next => (.individual d p ps i) <$> enqueue queue next
  | .individualIO d ps action next => do
    let promise ← IO.Promise.new
    let _ ← queue.send { action, promise }
    pure <| .individualIO d ps (awaitResult promise) (← enqueue queue next)
  | .individualSeededIO d ps action next =>
    -- Unreachable after `assignSeeds`; kept total so the traversal cannot silently drop a test.
    (.individualSeededIO d ps action) <$> enqueue queue next
  | .group d ts next => do
    let ts' ← enqueue queue ts
    pure <| .group d ts' (← enqueue queue next)

/-- How many workers to start for `numTests` queued tests: the requested concurrency, but never
    more than there is work to do. `maxConcurrent := some 0` still gets one worker. -/
private def workerCount (cfg : ParallelConfig) (numTests : Nat) : BaseIO Nat := do
  let requested ← match cfg.maxConcurrent with
    | some n => pure n
    | none => numCores
  return min (max 1 requested) numTests

/-- Starts `n` workers on `queue`, each on its own thread. The reference manual recommends
    dedicated threads for long-running work; they also reach full concurrency at once, whereas
    regular-priority pool tasks ramp up lazily and measured slower on many short tests. -/
private def startWorkers (n : Nat) (queue : Std.CloseableChannel Work) : BaseIO Unit := do
  for _ in [0 : n] do
    let _ ← IO.asTask (worker queue) Task.Priority.dedicated

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
  let queue ← Std.CloseableChannel.new
  -- Start the workers first so tests begin running while the rest are still being queued.
  startWorkers (← workerCount cfg seeded.numIOTests) queue
  let spawned ← enqueue queue seeded
  -- Closing lets the workers stop once the queue drains; queued work is still delivered.
  let _ ← queue.close.toBaseIO
  pure spawned

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

-- Runs up to `numCores` properties at a time.
#eval do let (ok, out) ← props.runIOParallel; IO.println out; pure ok

-- Cap concurrency at two tests and replay a specific run.
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

  -- One queue and one pool of workers for the whole run, so `maxConcurrent` bounds the run
  -- rather than each suite, and tests overlap across suites as well as within them. Everything
  -- is queued before anything is rendered.
  let seeded : List (String × List TestSeq) :=
    entries.map fun (key, tSeqs) => (key, tSeqs.map (TestSeq.assignSeeds · cfg.baseSeed))
  let total : Nat := seeded.foldl (init := 0) fun acc (_, tSeqs) =>
    tSeqs.foldl (fun n (tSeq : TestSeq) => n + tSeq.numIOTests) acc
  let queue ← Std.CloseableChannel.new
  startWorkers (← workerCount cfg total) queue
  let mut spawned : Array (String × List TestSeq) := #[]
  for (key, tSeqs) in seeded do
    spawned := spawned.push (key, ← tSeqs.mapM fun tSeq => (enqueue queue tSeq : BaseIO _))
  let _ ← queue.close.toBaseIO

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
