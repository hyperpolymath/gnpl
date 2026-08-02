-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (@hyperpolymath)
--
-- Type Safety Tests
-- Demonstrate type safety enforcement at compile time

import GqlDt.TypeSafe
import TestHarness
import GqlDt.TypeChecker
import GqlDt.Types.BoundedNat
import GqlDt.Types.NonEmptyString
import GqlDt.Prompt

namespace GqlDt.Tests.TypeSafety

-- `Prompt` and `Provenance` are needed for PromptScores.create and Rationale respectively.
-- Their absence is why this file stopped compiling: it was declared by no Lake target, so
-- nothing ever built it and the rot went unnoticed.
open TypeSafe TypeChecker AST Types Prompt Provenance

-- Test 1: Valid insertion compiles
def test_valid_insert : InsertStmt evidenceSchema :=
  let title := NonEmptyString.mk "Test Evidence" (by decide)
  -- `min`/`max` are structure *parameters* of BoundedNat, not fields — the old
  -- `BoundedNat.mk 0 100 100 …` passed them as data, which is why this stopped
  -- elaborating. The anonymous constructor lets the expected type (PromptDimension,
  -- i.e. BoundedNat 0 100) supply them, leaving val + the two bound proofs.
  let scores := PromptScores.create
    ⟨100, by omega, by omega⟩
    ⟨100, by omega, by omega⟩
    ⟨95,  by omega, by omega⟩
    ⟨95,  by omega, by omega⟩
    ⟨100, by omega, by omega⟩
    ⟨95,  by omega, by omega⟩
  -- insertEvidence takes a Provenance.Rationale, not a bare NonEmptyString — the whole
  -- point of the type is that a rationale cannot be confused with any other string.
  let rationale := Rationale.fromString "Test rationale"

  insertEvidence title scores rationale

#check test_valid_insert  -- ✓ Type checks!

-- Test 2: Out of bounds value doesn't compile
-- def test_invalid_bounds : InsertStmt evidenceSchema :=
--   let title := NonEmptyString.mk "Test" (by decide)
--   let badScore := BoundedNat.mk 0 100 150 (by omega) (by omega)
--   -- ERROR: Proof fails! Cannot prove 150 ≤ 100
--   let scores := PromptScores.create badScore ...
--   insertEvidence title scores ...

-- Test 3: Empty string doesn't compile
-- def test_empty_string : InsertStmt evidenceSchema :=
--   let title := NonEmptyString.mk "" (by decide)
--   -- ERROR: Proof fails! Cannot prove "".length > 0
--   insertEvidence title ...

-- Test 4: Wrong type doesn't compile
-- def test_wrong_type : InsertStmt evidenceSchema :=
--   mkInsert evidenceSchema "evidence"
--     ["title"]
--     [ ⟨.string, .string "Plain string"⟩ ]  -- Wrong type!
--     -- ERROR: Type mismatch in typesMatch proof

-- Test 5: Proof obligations are generated
def test_proof_obligations : IO Unit := do
  let stmt := test_valid_insert
  let obligations := generateProofObligations stmt

  IO.println s!"Generated {obligations.length} proof obligations:"
  for obl in obligations do
    match obl with
    | .boundsCheck min max val _ =>
        IO.println s!"  - Bounds check: {min} ≤ {val} ≤ {max}"
    | .nonEmpty s _ =>
        IO.println s!"  - Non-empty: '{s}'"
    | .constraintCheck schema _ =>
        IO.println s!"  - Constraint: {schema.name}"
    | .customProof _ =>
        IO.println s!"  - Custom proof required"

-- Test 6: Type errors produce helpful messages
def test_error_messages : IO Unit := do
  let error := reportTypeError (.boundedNat 0 100) .nat
  IO.println s!"Error: {error.message}"
  match error.suggestion with
  | some sugg => IO.println s!"Suggestion: {sugg}"
  | none => pure ()

-- Test 7: Execute only accepts type-safe queries
def test_execution_safety : IO Unit := do
  let stmt := test_valid_insert
  -- At this point, the type system GUARANTEES:
  -- 1. All values have correct types
  -- 2. All bounds are satisfied
  -- 3. All strings are non-empty
  -- 4. All proofs are valid

  execute stmt
  IO.println "✓ Execution succeeded (type safety guaranteed)"

-- Helper: states the invariant for a single sigma-typed value pair.
-- When the type tag is .boundedNat or .nonEmptyString, the TypedValue
-- dependent index guarantees the corresponding constructor was used,
-- so the carried proofs are available.
private def valueInvariant (pair : Σ t : TypeExpr, TypedValue t) : Prop :=
  match pair with
  | ⟨.boundedNat min max, .boundedNat _ _ bn⟩ => min ≤ bn.val ∧ bn.val ≤ max
  | ⟨.nonEmptyString, .nonEmptyString nes⟩ => nes.val.length > 0
  | _ => True

-- Helper lemma: every well-typed sigma pair satisfies the invariant.
-- This is provable because TypedValue is indexed by TypeExpr, so the
-- dependent pattern match is exhaustive and the proofs are carried
-- in the BoundedNat/NonEmptyString structures.
private theorem valueInvariant_holds (pair : Σ t : TypeExpr, TypedValue t)
    : valueInvariant pair := by
  obtain ⟨t, v⟩ := pair
  match t, v with
  | .nat, .nat _ => trivial
  | .int, .int _ => trivial
  | .string, .string _ => trivial
  | .bool, .bool _ => trivial
  | .float, .float _ => trivial
  | .boundedNat min max, .boundedNat _ _ bn =>
      exact ⟨bn.min_le, bn.le_max⟩
  | .nonEmptyString, .nonEmptyString nes =>
      exact nes.nonempty
  | .promptScores, .promptScores _ => trivial

-- Theorem: Type-safe queries can't produce runtime type errors.
-- Uses List.get with a Fin index (not get!) to preserve the dependent
-- relationship between the type tag and the value, enabling Lean to see
-- that TypedValue (.boundedNat min max) can only be .boundedNat and
-- TypedValue .nonEmptyString can only be .nonEmptyString.
theorem typeSafeQueriesPreserveInvariants {schema : Schema} (stmt : InsertStmt schema) :
  ∀ (i : Fin stmt.values.length),
    valueInvariant (stmt.values.get i)
  := by
  intro i
  exact valueInvariant_holds (stmt.values.get i)

-- Run all tests
def main : IO UInt32 := do
  IO.println "=== GQLdt Type Safety Tests ==="
  IO.println ""

  IO.println "Test 1: Valid insertion"
  let _ := test_valid_insert
  IO.println "✓ Compiles successfully"
  IO.println ""

  IO.println "Test 2: Proof obligations"
  test_proof_obligations
  IO.println ""

  IO.println "Test 3: Error messages"
  test_error_messages
  IO.println ""

  IO.println "Test 4: Execution safety"
  test_execution_safety
  IO.println ""

  IO.println "=== Type-safety tests completed ==="
  GnplTest.summarise "TypeSafety"

end GqlDt.Tests.TypeSafety

/-- Top-level entry point. The suite's `main` lives inside `GqlDt.Tests.TypeSafety`, so
    without this alias the linker finds no `main` symbol and the executable fails to link. -/
def main : IO UInt32 := GqlDt.Tests.TypeSafety.main
