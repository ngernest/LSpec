# LSpec

A testing framework for Lean 4, inspired by Haskell's [Hspec](https://hspec.github.io/) package.

## Usage

### Composing tests

Sequences of tests are represented by the `TestSeq` datatype.
In order to instantiate terms of `TestSeq`, use the `test` helper function:

```lean
#check
  test "Nat equality" (4 = 4) $
  test "Nat inequality" (4 ≠ 5)
-- test "Nat equality" (4 = 4) (test "Nat inequality" (4 ≠ 5)) : TestSeq
```

`test` consumes a description a proposition and a next test
The proposition, however, must have its own instance of `Testable`.

You can also collect `TestSeq` into conceptual test groups by using the
helper function `group`:

```lean
#check
  test "Nat equality" (42 = 42) $
  group "manual group" $
    test "Nat equality inside group" (4 = 4)
```

### The `Testable` class

`Testable` is how Lean is instructed to decide whether certain propositions are resolved as `true` or `false`.

This is an example of a simple instance for decidability of equalities:

```lean
instance (x y : α) [DecidableEq α] [Repr α] : Testable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h s!"Not equal: {repr x} and {repr y}"
```

The custom failure message is optional.

There are more examples of `Testable` instances in [LSpec/Instances.lean](LSpec/Instances.lean).

The user is, of course, free to provide their own instances.

### Actually running the tests

#### The `#lspec` command

The `#lspec` command allows you to test interactively in a file.

Examples:

```lean
#lspec
  test "four equals four" (4 = 4) $
  test "five equals five" (5 = 5)
-- ✓ four equals four
-- ✓ five equals five
```

An important note is that a failing test will raise an error, interrupting the building process.

#### The `lspecIO` function

`lspecIO` is meant to be used in files to be compiled and integrated in a testing infrastructure, as shown below.

```lean
def aaSuite := [
    test "four equals four" (4 = 4)
  ]

def bbSuite := [
    test "five equals five" (5 = 5)
  ]

def main := lspecIO $ .ofList [
    ("aa", aaSuite),
    ("bb", bbSuite)
  ]
```

Once such `main` function is defined, its respective executable can be tagged as the `@[test_driver]` in the lakefile.
For further information, inspect the docstring of `lspecIO`.

## Integration with `SlimCheck`

There are 3 main typeclasses associated with any  `SlimCheck` test:

* `Shrinkable` : The typeclass that takes a type `a : α` and returns a `List α` of elements which
  should be thought of as being "smaller" than `a` (in some sense dependent on the type `α` being 
  considered).
* `SampleableExt` : The typeclass of a . 
  This is roughly equivalent to `QuickCheck`'s `Arbitrary` typeclass. 
* `Checkable` : The property to be checked by `SlimCheck` must have a `Checkable` instance.

In order to use `SlimCheck` tests for custom data types, the user will need to implement 
instances of the typeclasses `Shrinkable` and `SampleableExt` for the custom types appearing
in the properties being tested.

The module [LSpec.SlimCheck.Checkable](LSpec/SlimCheck/Checkable.lean) contains may of 
the useful definitions and instances that can be used to derive a Checkable instance 
for a wide variety of properties given just the instances above. If all else fails, the user can 
also define the Checkable instance by hand. 

Once this is done a `Slimcheck` test is evaluated in a similar way to 
`LSpec` tests: 

```lean
#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + n

#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + m
-- × add_comm

-- ===================
-- Found problems!
-- n := 1
-- m := 0
-- issue: 1 = 0 does not hold
-- (0 shrinks)
-- -------------------
```

## Integration with `Plausible`

LSpec also integrates with Lean's [Plausible](https://github.com/leanprover-community/plausible) property-based testing library. The Plausible backend lives alongside the SlimCheck-based `check`/`checkIO` 
described above rather than replacing them, so existing SlimCheck tests continue to work unchanged.

Plausible relies on the same core typeclasses as QuickCheck — `Shrinkable` and `SampleableExt`
to generate and shrink random values — plus `Plausible.Testable` for the property itself.
Instances for the common types (`Nat`, `Int`, `List`, etc.) ship with Plausible, and custom
types are supported by providing `Shrinkable`/`SampleableExt` instances just as with SlimCheck.

The module [LSpec.Plausible](LSpec/Plausible.lean) exposes two macros:

* `checkPlausible'` — a **compile-time** property test, evaluated during elaboration with a
  fixed random seed (deterministic across compilations). This is the Plausible-backed
  counterpart to `check'`.
* `checkPlausibleIO'` — a **runtime** property test, deferred until the test suite is run.
  This enables fresh random values on each run and configurable seeds via `cfg.randomSeed`.
  This is the Plausible-backed counterpart to `checkIO'`.

Both macros capture the property syntax so it appears in the output. (Non-syntax-capturing
`checkPlausible`/`checkPlausibleIO` functions are also available if you don't need the
property echoed back.)

A compile-time test with `#lspec`:

```lean
#lspec checkPlausible' "add_comm" (∀ n m : Nat, n + m = m + n)
-- ✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)

#lspec checkPlausible' "bad" (∀ n : Nat, n < 5)
-- × ∃¹⁰/₁₀₀: "bad" (∀ n : Nat, n < 5)

-- ===================
-- Found problems!
-- n := 6
-- issue: 6 < 5 does not hold
-- (0 shrinks)
-- -------------------
```

A runtime test, run via `lspecIO`. Because `checkPlausibleIO'` tests are skipped by the pure
`#lspec` runner, they must be executed with `lspecIO` (or `lspecEachIO`):

```lean
open LSpec

def plausibleTests : TestSeq :=
  checkPlausibleIO' "add_comm" (∀ n m : Nat, n + m = m + n)

def main : IO UInt32 := lspecIO (.ofList [("plausibleTests", [plausibleTests])]) []
```

Multiple property tests can be sequenced with `++`. Note that the `'`-suffixed macros
capture everything up to the end of the line as the property, so to chain them use the
non-capturing `checkPlausibleIO` function (which takes an explicit `next` argument):

```lean
def suite : TestSeq :=
  checkPlausibleIO "add_comm" (∀ n m : Nat, n + m = m + n) $
  checkPlausibleIO "mul_one"  (∀ n : Nat, n * 1 = n)
```

The `'`-suffixed macros always use the default configuration. To pass a fixed seed for
reproducible runs (or otherwise customise the `Plausible.Configuration`), call the underlying
`checkPlausibleIO` function directly:

```lean
def reproducible : TestSeq :=
  checkPlausibleIO "add_comm" (∀ n m : Nat, n + m = m + n) .done { randomSeed := some 42 }
```

## Running properties in parallel

Property tests are independent and CPU-bound, so they are worth running concurrently — the same
idea as Haskell's [`tasty`](https://github.com/UnkindPartition/tasty). The module
[LSpec.Parallel](LSpec/Parallel.lean) provides drop-in parallel counterparts to the runtime
runners:

| Sequential | Parallel |
|------------|----------|
| `TestSeq.runIO` | `TestSeq.runIOParallel` |
| `lspecIO` | `lspecIOParallel` |

```lean
def props : TestSeq :=
  checkPlausibleIO' "add_comm"   (∀ n m : Nat, n + m = m + n) ++
  checkPlausibleIO' "mul_comm"   (∀ n m : Nat, n * m = m * n) ++
  checkPlausibleIO' "append_nil" (∀ l : List Nat, l ++ [] = l)

def main : IO UInt32 := lspecIOParallel (.ofList [("props", [props])]) []
```

Like `tasty`, scheduling is separated from reporting: every deferred test is launched at once,
then the reporter walks the sequence in its original order and blocks on each result in turn.
Output is therefore **byte-for-byte identical** to the sequential runner — same order, same
samples, same counterexamples, same exit code — only faster.

`ParallelConfig` controls the two knobs:

```lean
-- Up to `numCores` tests at once (the default).
props.runIOParallel

-- `tasty`'s `-j 4`: at most four tests in flight.
props.runIOParallel { maxConcurrent := some 4 }

-- Replay an entire run, seeds included.
props.runIOParallel { baseSeed := 42 }
```

`maxConcurrent` defaults to `LSpec.numCores`, the number of CPU cores available to the process —
the same default `tasty` uses for `-j`, and the one Turnt's `ThreadPoolExecutor` inherits from
Python. It is read from `LEAN_NUM_THREADS` if set (that variable also bounds Lean's own
scheduler), then `NUMBER_OF_PROCESSORS` on Windows, then `sysctl -n hw.logicalcpu` or `nproc`,
and is memoised for the process.

The cap is built only from the task combinators in the standard library: `IO.asTask` launches a
test, and `IO.bindTask` links the tests into `n` chains so that test `i` starts only once test
`i - n` has finished. There is no lock, no shared counter and no promise — the ordering
constraint is carried by the tasks themselves, which is what the
[reference manual](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/) recommends
over blocking on results. `lspecIOParallel` threads the chains across suites, so the cap bounds
the whole run rather than each suite.

The chains are a static round-robin split, not a work-stealing queue. A suite whose slow tests
all have indices agreeing modulo `n` can cost about twice an ideal schedule. In exchange the
tests run on dedicated threads, which reach full concurrency immediately — regular-priority pool
tasks ramp up lazily and measured slower on suites of many short tests.

### Seeding and reproducibility

Plausible and SlimCheck both draw randomness from a global `stdGenRef`, which — per Plausible's
own documentation — "is not thread local, hence two threads accessing it at the same time will
get the exact same generator". Sharing it across threads would both race on the write-back and
silently collapse coverage.

So deferred property tests no longer touch it. Each takes a seed derived from its **position**
in the sequence, `seedFor baseSeed i`, spread with the SplitMix64 finalizer so that neighbouring
tests get uncorrelated sample streams. Samples then depend only on `baseSeed` and position, never
on scheduling order, which is what makes the parallel and sequential runners agree. A failing
property reports the seed that produced it:

```
× ∃⁴⁵/₁₀₀: "bogus" (∀ n : Nat, n < 40)
    Found problems!
    n := 42
    (replay with randomSeed := 7960286522194355700)
```

An explicit `cfg.randomSeed` always wins over the runner-supplied seed, so pinned tests stay
pinned.

### Caveats

* Only **deferred** tests are parallelised. `test`, `check` and `checkPlausible` are evaluated
  during elaboration and are already values by the time a runner sees them.
* Tests must be **independent**. A test that touches shared mutable state, the process-wide
  stdout, the working directory, or a fixed port is not safe here — keep those on `runIO`.
  (LSpec's own suite is an example: it swaps global stdout, so it runs sequentially.)
* `lspecIOParallel` holds every suite live at once, giving up `lspecIO`'s incremental memory
  behaviour. Prefer `lspecIO` for suites that are memory-heavy rather than time-heavy.
