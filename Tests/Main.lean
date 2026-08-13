import LSpec

open LSpec

/-! # LSpec test suite

Dogfoods `lspecIO` as the outer runner. Primary suites always run;
the memory stress suite is opt-in via `./tests memory`.
-/

private def String.containsSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Helper: run an IO action with stdout and stderr redirected to /dev/null.
def quietly (action : IO α) : IO α := do
  let devNull ← IO.FS.Handle.mk "/dev/null" .write
  let nullStream := IO.FS.Stream.ofHandle devNull
  let oldStdout ← (IO.setStdout nullStream : BaseIO _)
  let oldStderr ← (IO.setStderr nullStream : BaseIO _)
  try
    let result ← action
    let _ ← (IO.setStdout oldStdout : BaseIO _)
    let _ ← (IO.setStderr oldStderr : BaseIO _)
    pure result
  catch e =>
    let _ ← (IO.setStdout oldStdout : BaseIO _)
    let _ ← (IO.setStderr oldStderr : BaseIO _)
    throw e

-- Helper: run a TestSeq via runIO (no printing), then assert on the bool and
-- check that the output contains a given substring.
def assertRunIO (tSeq : TestSeq) (expectPass : Bool) (expectSubstr : String := "") :
    IO (Bool × Nat × Nat × Option String) := do
  let (pass, output) ← tSeq.runIO
  let boolOk := pass == expectPass
  let substrOk := expectSubstr.isEmpty || output.containsSub expectSubstr
  if boolOk && substrOk then
    pure (true, 0, 0, none)
  else
    let mut msg := ""
    unless boolOk do
      msg := msg ++ s!"expected pass={expectPass} but got pass={pass}"
    unless substrOk do
      if !msg.isEmpty then msg := msg ++ "; "
      msg := msg ++ s!"expected output to contain \"{expectSubstr}\" but got:\n{output}"
    pure (false, 0, 0, some msg)

section PrimarySuites

/-! ## TestSeq.runIO basics -/

def runIOBasics : TestSeq :=
  group "TestSeq.runIO basics" (
    .individualIO "passing test returns (true, _)" none
      (assertRunIO (test "t" (1 = 1)) true) .done ++
    .individualIO "failing test returns (false, _)" none
      (assertRunIO (test "t" (1 = 2)) false) .done ++
    .individualIO "multiple passing tests" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (2 = 2)) true) .done ++
    .individualIO "mixed pass/fail returns false" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (1 = 2)) false) .done ++
    .individualIO ".done is identity" none
      (assertRunIO .done true) .done
  )

/-! ## Grouping -/

def groupingTests : TestSeq :=
  group "Grouping" (
    .individualIO "group produces labeled output" none
      (assertRunIO (group "myGroup" (test "t" true)) true "myGroup") .done ++
    .individualIO "describe produces labeled output" none
      (assertRunIO (describe "myDescribe" (test "t" true)) true "myDescribe") .done ++
    .individualIO "context produces labeled output" none
      (assertRunIO (context "myContext" (test "t" true)) true "myContext") .done ++
    .individualIO "nested groups work" none
      (assertRunIO (group "outer" (group "inner" (test "t" true))) true "inner") .done
  )

/-! ## IO tests -/

def ioTests : TestSeq :=
  group "IO tests" (
    .individualIO "individualIO success" none (do
      let (pass, _) ← (TestSeq.individualIO "t" none (pure (true, 0, 0, none)) .done).runIO
      if pass then pure (true, 0, 0, none)
      else pure (false, 0, 0, some "expected pass=true")
    ) .done ++
    .individualIO "individualIO failure" none (do
      let (pass, _) ← (TestSeq.individualIO "t" none (pure (false, 0, 100, some "boom")) .done).runIO
      if !pass then pure (true, 0, 0, none)
      else pure (false, 0, 0, some "expected failure but got success")
    ) .done ++
    .individualIO "individualIO error message propagates" none
      (assertRunIO
        (TestSeq.individualIO "t" none (pure (false, 0, 100, some "specific error msg")) .done)
        false "specific error msg") .done
  )

/-! ## Combinators -/

def combinatorTests : TestSeq :=
  group "Combinators" (
    withOptionSome "withOptionSome on some" (some 42) (fun n =>
      test "value is 42" (n = 42)) ++
    withOptionNone "withOptionNone on none" (none : Option Nat)
      (test "reached" true) ++
    .individualIO "withOptionSome on none fails" none
      (assertRunIO
        (withOptionSome "got none" (none : Option Nat) (fun _ => test "unreachable" true))
        false) .done ++
    .individualIO "withOptionNone on some fails" none
      (assertRunIO
        (withOptionNone "got some" (some 42) (test "unreachable" true))
        false) .done ++
    withExceptOk "withExceptOk on ok" (Except.ok 10 : Except String Nat) (fun n =>
      test "value is 10" (n = 10)) ++
    withExceptError "withExceptError on error" (Except.error "oops" : Except String Nat) (fun e =>
      test "error is oops" (e = "oops"))
  )

/-! ## Append -/

def appendTests : TestSeq :=
  group "Append" (
    .individualIO "++ chains tests" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (2 = 2)) true) .done ++
    .individualIO "++ preserves order" none (do
      let (_, output) ← (test "first" (1 = 1) ++ test "second" (2 = 2)).runIO
      -- "first" should appear before "second" in the output
      let hasBoth := output.containsSub "first" && output.containsSub "second"
      -- Check ordering via splitOn: if we split on "first", "second" should be in the tail
      let afterFirst := (output.splitOn "first").getD 1 ""
      let ordered := afterFirst.containsSub "second"
      if hasBoth && ordered then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected 'first' before 'second' in:\n{output}")
    ) .done
  )

/-! ## Property tests -/

def propertyTests : TestSeq :=
  group "Property tests" (
    .individualIO "checkIO passing property" none
      (assertRunIO (checkIO "add_zero" (∀ n : Nat, n + 0 = n)) true) .done ++
    .individualIO "checkIO failing property" none
      (assertRunIO (checkIO "bad" (∀ n : Nat, n = n + 1)) false) .done
  )

-- Variant of `propertyTests` above which tests the Plausible integration
def plausiblePropertyTests : TestSeq :=
  group "Plausible property tests" (
    .individualIO "checkPlausibleIO passing property" none
      (assertRunIO (checkPlausibleIO "add_zero" (∀ n : Nat, n + 0 = n)) true) .done ++
    .individualIO "checkPlausibleIO failing property" none
      (assertRunIO (checkPlausibleIO "bad" (∀ n : Nat, n = n + 1)) false) .done
  )

/-! ## Parallel runner

`runIOParallel` must be observationally equivalent to `runIO`: same ordering, same formatting,
same samples, same verdict — only faster. These tests pin that down, plus the seeding
guarantees that make it true.
-/

-- A mixed sequence: passing and failing properties, plain IO tests, and a nested group.
def mixedSeq : TestSeq :=
  (checkPlausibleIO' "add_comm" (∀ n m : Nat, n + m = m + n)) ++
  (checkIO' "mul_comm" (∀ n m : Nat, n * m = m * n)) ++
  test "unit" (1 = 1) ++
  (checkPlausibleIO' "bogus" (∀ n : Nat, n < 40)) ++
  group "nested" (
    (checkIO' "sub_self" (∀ n : Nat, n - n = 0)) ++
    (checkPlausibleIO' "bogus2" (∀ l : List Nat, l.length < 3))
  )

-- `n` deferred tests that each sleep `ms` milliseconds.
def sleepers (n ms : Nat) : TestSeq :=
  match n with
  | 0 => .done
  | k + 1 =>
    .individualIO s!"sleep {k}" none
      (do IO.sleep (UInt32.ofNat ms); pure (true, 0, 0, none)) (sleepers k ms)

-- `n` deferred tests that record the high-water mark of how many ran at the same time.
def probes (live peak : IO.Ref Nat) (n : Nat) : TestSeq :=
  match n with
  | 0 => .done
  | k + 1 =>
    .individualIO s!"probe {k}" none (do
      let inFlight ← live.modifyGet fun l => (l + 1, l + 1)
      peak.modify (max · inFlight)
      IO.sleep 60
      live.modify (· - 1)
      pure (true, 0, 0, none)) (probes live peak k)

def parallelTests : TestSeq :=
  group "Parallel runner" (
    .individualIO "runIOParallel output matches runIO byte-for-byte" none (do
      let (seqPass, seqOut) ← mixedSeq.runIO
      let (parPass, parOut) ← mixedSeq.runIOParallel
      if seqPass == parPass && seqOut == parOut then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"sequential:\n{seqOut}\nparallel:\n{parOut}")
    ) .done ++
    .individualIO "bounded pool output matches runIO" none (do
      let (_, seqOut) ← mixedSeq.runIO
      let (_, out1) ← mixedSeq.runIOParallel { maxConcurrent := some 1 }
      let (_, out3) ← mixedSeq.runIOParallel { maxConcurrent := some 3 }
      if seqOut == out1 && seqOut == out3 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"j=1 match: {seqOut == out1}, j=3 match: {seqOut == out3}")
    ) .done ++
    .individualIO "failing property still reports failure" none (do
      let (pass, out) ← mixedSeq.runIOParallel
      if !pass && out.containsSub "bogus" && out.containsSub "Found problems!" then
        pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected a reported failure, got pass={pass}:\n{out}")
    ) .done ++
    .individualIO "indentation matches runIO at the same indent" none (do
      let (_, seqOut) ← mixedSeq.runIO (indent := 4)
      let (_, parOut) ← mixedSeq.runIOParallel (indent := 4)
      if seqOut == parOut && seqOut.containsSub "    ✓ " then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"sequential:\n{seqOut}\nparallel:\n{parOut}")
    ) .done ++
    -- Uses a bounded pool of dedicated threads, so the speedup comes from overlapping
    -- sleeps rather than from having multiple cores. Robust on single-core CI.
    .individualIO "deferred tests actually overlap" none (do
      let t0 ← IO.monoMsNow
      let _ ← (sleepers 6 200).runIOParallel { maxConcurrent := some 6 }
      let elapsed := (← IO.monoMsNow) - t0
      -- Sequentially this is ~1200 ms; overlapped it should be near 200 ms.
      if elapsed < 900 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"6x200ms overlapped took {elapsed} ms (expected < 900)")
    ) .done ++
    .individualIO "numCores is positive and honours LEAN_NUM_THREADS" none (do
      let cores ← numCores
      if cores == 0 then
        pure (false, 0, 0, some "numCores returned 0")
      else
        -- When the variable is set, it wins, since it also bounds Lean's own scheduler.
        match ← IO.getEnv "LEAN_NUM_THREADS" with
        | some raw =>
          match raw.trimAscii.toNat? with
          | some n =>
            if n == 0 || cores == n then pure (true, 0, 0, none)
            else pure (false, 0, 0, some s!"LEAN_NUM_THREADS={n} but numCores={cores}")
          | none => pure (true, 0, 0, none)
        | none => pure (true, 0, 0, none)
    ) .done ++
    -- The default `maxConcurrent := none` must actually reach `numCores` tests at once, given
    -- enough work to do so.
    .individualIO "the default concurrency is numCores" none (do
      let cores ← numCores
      let live ← IO.mkRef 0
      let peak ← IO.mkRef 0
      let _ ← (probes live peak (cores * 2)).runIOParallel
      let observed ← peak.get
      if observed == cores && (← live.get) == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0,
        some s!"peak={observed} with {cores * 2} tests, expected numCores={cores}")
    ) .done ++
    -- The worker pool must bound the tests in flight exactly, not just roughly: with
    -- `maxConcurrent := some n` the peak must be `min n (number of tests)`.
    .individualIO "maxConcurrent bounds the tests in flight exactly" none (do
      let mut bad := #[]
      for n in [1, 2, 3, 8, 20] do
        let live ← IO.mkRef 0
        let peak ← IO.mkRef 0
        let _ ← (probes live peak 8).runIOParallel { maxConcurrent := some n }
        let observed ← peak.get
        let expected := min n 8
        unless observed == expected do
          bad := bad.push s!"j={n}: peak={observed}, expected {expected}"
        unless (← live.get) == 0 do
          bad := bad.push s!"j={n}: {← live.get} tests still in flight"
      if bad.isEmpty then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"{bad.toList}")
    ) .done ++
    -- The shared queue distributes work dynamically: an idle worker takes the next test rather
    -- than being tied to a fixed subset. This suite is built so that a static round-robin split
    -- over 4 workers would put all three slow tests on one worker (indices 0, 4 and 8), costing
    -- ~1200ms, whereas any dynamic assignment finishes in ~400-500ms.
    .individualIO "slow tests do not monopolise one worker" none (do
      let durations := (List.range 12).map fun i => if i % 4 == 0 then 400 else 50
      let tSeq : TestSeq := durations.foldr (init := TestSeq.done) fun ms acc =>
        .individualIO s!"t{ms}" none
          (do IO.sleep (UInt32.ofNat ms); pure (true, 0, 0, none)) acc
      let t0 ← IO.monoMsNow
      let _ ← tSeq.runIOParallel { maxConcurrent := some 4 }
      let elapsed := (← IO.monoMsNow) - t0
      -- Generous margin: well under the ~1200ms a static split would cost, and safely above
      -- the ~412ms ideal so the test does not flake on a loaded machine.
      if elapsed < 800 then pure (true, 0, 0, none)
      else pure (false, 0, 0,
        some s!"took {elapsed}ms; a dynamic queue should be well under 800ms here")
    ) .done ++
    -- A worker catches a throwing test rather than dying on it, so the tests queued behind it
    -- must still run and resolve their promises.
    .individualIO "a throwing test does not kill its worker" none (do
      let ran ← IO.mkRef 0
      let mk (i : Nat) (next : TestSeq) : TestSeq :=
        .individualIO s!"t{i}" none (do
          ran.modify (· + 1)
          if i == 0 then throw (.userError "boom")
          pure (true, 0, 0, none)) next
      -- One worker, so every test is queued behind the throwing one.
      let spawned ← (mk 0 (mk 1 (mk 2 (mk 3 .done)))).spawnIO { maxConcurrent := some 1 }
      -- The renderer aborts at test 0, so wait for the queue to drain before counting.
      let _ ← (spawned.runIOAux : IO _).toBaseIO
      IO.sleep 300
      if (← ran.get) == 4 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"only {← ran.get} of 4 queued tests ran")
    ) .done ++
    .individualIO "same baseSeed replays, different baseSeed does not" none (do
      let (_, a) ← mixedSeq.runIOParallel { baseSeed := 7 }
      let (_, b) ← mixedSeq.runIOParallel { baseSeed := 7 }
      let (_, c) ← mixedSeq.runIOParallel { baseSeed := 12345 }
      if a == b && a != c then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"replay: {a == b}, differs: {a != c}")
    ) .done ++
    .individualIO "explicit cfg.randomSeed overrides the runner's seed" none (do
      -- Both copies pin the same seed, so they must find the same counterexample even
      -- though they sit at different positions in the sequence.
      let tSeq := checkPlausibleIO "a" (∀ n : Nat, n < 40) .done { randomSeed := some 99 } ++
                  checkPlausibleIO "b" (∀ n : Nat, n < 40) .done { randomSeed := some 99 }
      let (_, out) ← tSeq.runIOParallel
      let counterexamples := (out.splitOn "n := ").tail.map (·.takeWhile Char.isDigit)
      match counterexamples with
      | [x, y] =>
        if x == y then pure (true, 0, 0, none)
        else pure (false, 0, 0, some s!"pinned seed gave different counterexamples: {x} vs {y}")
      | other => pure (false, 0, 0, some s!"expected 2 counterexamples, got {other}")
    ) .done ++
    .individualIO "positional seeds are distinct and decorrelated" none (do
      -- 200 copies of one failing property must not all report the same counterexample.
      let many := (List.range 200).foldr (init := .done) fun i acc =>
        checkPlausibleIO s!"p{i}" (∀ n : Nat, n < 40) acc
      let (_, out) ← many.runIOParallel
      let vals := (out.splitOn "n := ").tail.map (·.takeWhile Char.isDigit)
      if vals.length == 200 && vals.eraseDups.length > 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0,
        some s!"got {vals.length} counterexamples, {vals.eraseDups.length} distinct")
    ) .done ++
    -- This is the whole reason `seedFor` mixes rather than returning `baseSeed + idx`. With
    -- unmixed seeds the k-th sample across tests is an arithmetic progression, and at k = 0 that
    -- pins the parity: all 200 first samples come out odd. Assert the parity is actually split.
    .individualIO "seedFor removes the low-position bias of baseSeed + idx" none (do
      let firstSample (seed : Nat) : Nat := (randNat (mkStdGen seed) 0 999).1
      let evens (seedOf : Nat → Nat) : Nat :=
        (((List.range 200).map (firstSample ∘ seedOf)).filter (· % 2 == 0)).length
      let mixed := evens (LSpec.seedFor 0)
      let unmixed := evens id
      -- The mixed seeds must be roughly balanced; the unmixed ones demonstrably are not.
      if 60 ≤ mixed && mixed ≤ 140 && (unmixed == 0 || unmixed == 200) then
        pure (true, 0, 0, none)
      else pure (false, 0, 0,
        some s!"seedFor gave {mixed}/200 even (want 60..140); baseSeed+idx gave {unmixed}/200")
    ) .done ++
    .individualIO "seedFor is injective" none (do
      let seeds := (List.range 2000).map (LSpec.seedFor 0)
      if seeds.eraseDups.length == seeds.length then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"only {seeds.eraseDups.length}/2000 distinct seeds")
    ) .done ++
    .individualIO "exceptions from deferred tests propagate" none (do
      let boom : TestSeq := .individualIO "boom" none (throw (.userError "kaboom")) .done
      try
        let _ ← boom.runIOParallel
        pure (false, 0, 0, some "expected the exception to propagate")
      catch e =>
        if (toString e).containsSub "kaboom" then pure (true, 0, 0, none)
        else pure (false, 0, 0, some s!"unexpected error: {e}")
    ) .done ++
    .individualIO "degenerate sequences and pool sizes" none (do
      let (d, dOut) ← TestSeq.done.runIOParallel
      let (u, _) ← (test "pure" (1 = 1)).runIOParallel
      -- `maxConcurrent := some 0` must still make progress rather than deadlock.
      let (z, _) ← (sleepers 3 1).runIOParallel { maxConcurrent := some 0 }
      if d && dOut.isEmpty && u && z then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"done={d} emptyOut={dOut.isEmpty} pure={u} j0={z}")
    ) .done ++
    .individualIO "spawnIO preserves shape and test count" none (do
      let spawned ← mixedSeq.spawnIO
      if spawned.numIOTests == mixedSeq.numIOTests then pure (true, 0, 0, none)
      else pure (false, 0, 0,
        some s!"spawned {spawned.numIOTests} IO tests, expected {mixedSeq.numIOTests}")
    ) .done
  )

def lspecIOParallelTests : TestSeq :=
  group "lspecIOParallel" (
    .individualIO "returns 0 on all-pass" none (quietly do
      let rc ← lspecIOParallel (.ofList [("s", [test "t" (1 = 1)])]) []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "returns 1 on any failure" none (quietly do
      let rc ← lspecIOParallel (.ofList [("s", [test "t" (1 = 2)])]) []
      if rc == 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=1, got rc={rc}")
    ) .done ++
    .individualIO "empty map returns 0" none (quietly do
      let rc ← lspecIOParallel (.ofList []) []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "suite filtering by name prefix" none (quietly do
      let map : Std.HashMap String (List TestSeq) := .ofList [
        ("math.add", [test "t" (1 + 1 = 2)]),
        ("string.bad", [test "t" (1 = 2)])
      ]
      -- Filtering out the failing suite must yield 0.
      let rc ← lspecIOParallel map ["math"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with filter, got rc={rc}")
    ) .done ++
    .individualIO "non-matching filter runs nothing (returns 0)" none (quietly do
      let rc ← lspecIOParallel (.ofList [("suite", [test "t" (1 = 2)])]) ["nonexistent"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with no matches, got rc={rc}")
    ) .done ++
    -- `maxConcurrent` must bound the whole run. One queue and one pool serve every suite, so
    -- five suites with `some 2` run two tests at a time in total, not two per suite.
    .individualIO "maxConcurrent bounds concurrency across suites" none (do
      let live ← IO.mkRef 0
      let peak ← IO.mkRef 0
      let map : Std.HashMap String (List TestSeq) := .ofList
        ((List.range 5).map fun i => (s!"suite{i}", [probes live peak 3]))
      let rc ← quietly (lspecIOParallel map [] { maxConcurrent := some 2 })
      let observed ← peak.get
      if rc == 0 && observed == 2 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"rc={rc}, peak={observed} across 5 suites (expected 2)")
    ) .done ++
    .individualIO "suites overlap in wall-clock time" none (quietly do
      let slow : TestSeq :=
        .individualIO "slow" none (do IO.sleep 200; pure (true, 0, 0, none)) .done
      let map : Std.HashMap String (List TestSeq) :=
        .ofList [("a", [slow]), ("b", [slow]), ("c", [slow]), ("d", [slow])]
      let t0 ← IO.monoMsNow
      let rc ← lspecIOParallel map [] { maxConcurrent := some 4 }
      let elapsed := (← IO.monoMsNow) - t0
      if rc == 0 && elapsed < 600 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"rc={rc}, 4 suites x 200ms took {elapsed} ms")
    ) .done
  )

/-! ## lspecIO integration -/

def lspecIOIntegration : TestSeq :=
  group "lspecIO integration" (
    .individualIO "returns 0 on all-pass" none (quietly do
      let map := Std.HashMap.ofList [("s", [test "t" (1 = 1)])]
      let rc ← lspecIO map []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "returns 1 on any failure" none (quietly do
      let map := Std.HashMap.ofList [("s", [test "t" (1 = 2)])]
      let rc ← lspecIO map []
      if rc == 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=1, got rc={rc}")
    ) .done ++
    .individualIO "empty map returns 0" none (quietly do
      let rc ← lspecIO (.ofList []) []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "suite filtering by name prefix" none (quietly do
      let map := Std.HashMap.ofList [
        ("math.add", [test "t" (1 + 1 = 2)]),
        ("string.concat", [test "t" ("a" ++ "b" = "ab")])
      ]
      let rc ← lspecIO map ["math"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with filter, got rc={rc}")
    ) .done ++
    .individualIO "non-matching filter runs nothing (returns 0)" none (quietly do
      let map := Std.HashMap.ofList [("suite", [test "t" (1 = 2)])]
      let rc ← lspecIO map ["nonexistent"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with no matches, got rc={rc}")
    ) .done
  )

/-! ## lspecEachIO -/

def lspecEachIOTests : TestSeq :=
  group "lspecEachIO" (
    .individualIO "returns 0 on all-pass" none (quietly do
      let rc ← lspecEachIO [1, 2, 3] fun n => pure (test s!"{n}" (n > 0))
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "returns 1 on any failure" none (quietly do
      let rc ← lspecEachIO [1, 0, 3] fun n =>
        pure (test s!"{n}>0" (decide (n > 0)))
      if rc == 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=1, got rc={rc}")
    ) .done
  )

end PrimarySuites

/-! ## Memory stress suite (opt-in: `./tests memory`)

Each of 50 tests allocates a 100 MB `ByteArray`. With the tail-recursive fix,
RSS should stay bounded rather than climbing to 5 GB+.
Run and watch in htop to verify.
-/

def memoryStressTests : TestSeq :=
  go 50
where
  go : Nat → TestSeq
    | 0 => .done
    | n + 1 =>
      .individualIO s!"alloc 100MB #{50 - n}" none (do
        -- Allocate 100 MB and touch it so it's not optimised away
        let arr := ByteArray.mk (.replicate (100 * 1024 * 1024) 0xFF)
        let ok := arr.size > 0
        pure (ok, 0, 0, none)
      ) (go n)

-- NOTE: the outer runner is deliberately `lspecIO`, not `lspecIOParallel`. Several tests here
-- use `quietly`, which swaps the *process-global* stdout/stderr; running those concurrently
-- with tests that print would swallow output nondeterministically. This suite is itself an
-- example of the "tests must be independent" caveat on the parallel runners.
def main (args : List String) : IO UInt32 := do
  let runMemory := args.contains "memory"
  let primarySuites : Std.HashMap String (List TestSeq) := .ofList [
    ("TestSeq.runIO basics", [runIOBasics]),
    ("Grouping", [groupingTests]),
    ("IO tests", [ioTests]),
    ("Combinators", [combinatorTests]),
    ("Append", [appendTests]),
    ("Property tests", [propertyTests]),
    ("Plausible property tests", [plausiblePropertyTests]),
    ("Parallel runner", [parallelTests]),
    ("lspecIOParallel", [lspecIOParallelTests]),
    ("lspecIO integration", [lspecIOIntegration]),
    ("lspecEachIO", [lspecEachIOTests])
  ]
  let filterArgs := args.filter (· != "memory")
  let rc ← lspecIO primarySuites filterArgs
  if runMemory then
    IO.println "\n=== Memory stress test (watch RSS in htop) ==="
    let memMap : Std.HashMap String (List TestSeq) := .ofList [
      ("memory stress (50 × 100MB)", [memoryStressTests])
    ]
    let rc2 ← lspecIO memMap []
    return max rc rc2
  return rc
