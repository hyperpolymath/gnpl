-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025 hyperpolymath
--
-- lakefile.lean - Lake build configuration for GQLdt

import Lake
open Lake DSL

package gqldt where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- Use unicode λ in pretty printing
    ⟨`autoImplicit, false⟩    -- Require explicit type annotations
  ]

-- Mathlib4 for tactics (omega, simp, etc.) and proof automation
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

-- Main library
@[default_target]
lean_lib GqlDt where
  srcDir := "src"
  roots := #[`GqlDt]

-- Shared test support (failure counter + exit-code summary).
-- Declared as a library so the individual test executables can `import TestHarness`;
-- a bare file under a target's srcDir is not otherwise resolvable as a module.
lean_lib TestSupport where
  srcDir := "test"
  roots := #[`TestHarness]

-- FFI Test executable (requires Zig library to be built first)
-- Build Zig lib: cd bridge && zig build
lean_exe ffi_test where
  srcDir := "test"
  root := `FFITest
  -- Link against the Zig FFI bridge library
  moreLinkArgs := #[
    "-Lbridge/zig-out/lib",
    "-llith_bridge"
  ]

-- Parser test executable
lean_exe parser_test where
  srcDir := "test"
  root := `ParserTest

-- Lexer test executable
lean_exe lexer_test where
  srcDir := "test"
  root := `LexerTest

-- Type-safety test executable.
-- test/TypeSafetyTests.lean existed but was declared by no target, so it was never
-- built and never run — it could not even fail to compile.
lean_exe type_safety_test where
  srcDir := "test"
  root := `TypeSafetyTests

-- Test driver: `lake test`.
--
-- Without this, `lake test` reported "no test driver configured" and exited non-zero,
-- so CI had to tolerate that failure — which meant CI also tolerated genuine test
-- failures. The suites below now return a real exit code (see test/TestHarness.lean).
--
-- ffi_test is deliberately excluded: it links against bridge/zig-out/lib/liblith_bridge.a,
-- which requires `cd bridge && zig build` first. It is run separately by the zig-ffi CI
-- job, where that artifact is guaranteed to exist. Including it here would make `lake test`
-- fail on a clean checkout for a reason unrelated to Lean.
@[test_driver]
script test do
  let suites := #["lexer_test", "parser_test", "type_safety_test"]
  let mut failed : Array String := #[]
  for suite in suites do
    let bin := System.mkFilePath [".lake", "build", "bin", suite]
    if !(← System.FilePath.pathExists bin) then
      IO.eprintln s!"✗ {suite}: binary not found at {bin} — run `lake build` first"
      failed := failed.push suite
      continue
    IO.println s!"\n▶ {suite}"
    let child ← IO.Process.spawn { cmd := bin.toString }
    if (← child.wait) != 0 then
      failed := failed.push suite
  if failed.isEmpty then
    IO.println s!"\n✅ all {suites.size} Lean suite(s) passed"
    return 0
  else
    IO.eprintln s!"\n❌ FAILED: {String.intercalate ", " failed.toList}"
    return 1

-- GQLdt CLI/REPL (with FFI persistence backend)
lean_exe gqldt where
  srcDir := "src"
  root := `Main
  -- Link against the Zig FFI bridge library for persistence
  moreLinkArgs := #[
    "-Lbridge/zig-out/lib",
    "-llith_bridge"
  ]
