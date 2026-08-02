-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- TestHarness.lean — shared failure accounting for the GQLdt test suites.
--
-- Why this exists: every suite in test/ previously printed "FAIL"/"✗" to stdout and
-- then carried on to print "All tests passed!" unconditionally, with `main : IO Unit`
-- so the process always exited 0. A failing test was therefore invisible to `lake test`,
-- to CI, and to a human skim-reading the tail of the log.
--
-- LexerTest even documented a failure counter — "Count of test failures, tracked via
-- IO.Ref" — that was never implemented.
--
-- This module supplies the counter that comment promised, and `summarise` turns it into
-- a process exit code. A suite is only honest if a failing check can turn it red.

namespace GnplTest

/-- Number of failed checks recorded so far, across every suite in this process. -/
initialize failureCount : IO.Ref Nat ← IO.mkRef 0

/-- Record a passing check. -/
def pass (name : String) : IO Unit :=
  IO.println s!"  PASS: {name}"

/-- Record a failing check. Increments the counter that `summarise` reads. -/
def fail (name : String) (detail : String := "") : IO Unit := do
  failureCount.modify (· + 1)
  if detail.isEmpty then
    IO.eprintln s!"  FAIL: {name}"
  else
    IO.eprintln s!"  FAIL: {name} — {detail}"

/-- Assert a boolean condition, recording the outcome either way. -/
def check (name : String) (passed : Bool) : IO Unit :=
  if passed then pass name else fail name

/--
Print the suite verdict and yield the process exit code: `0` iff nothing failed.

Use as the last line of `main`, whose type must be `IO UInt32` for the code to reach
the operating system.
-/
def summarise (suite : String) : IO UInt32 := do
  let n ← failureCount.get
  if n == 0 then
    IO.println s!"✅ {suite}: all checks passed"
    return 0
  else
    IO.eprintln s!"❌ {suite}: {n} check(s) FAILED"
    return 1

end GnplTest
