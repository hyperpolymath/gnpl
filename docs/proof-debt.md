<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Proof debt

Per [`hyperpolymath/standards` — Trusted-Base Reduction Policy](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc).

Enumerated 2026-07-21 by running the estate checker (`standards/scripts/check-trusted-base.sh`)
against this repository: **19 soundness-relevant escape hatches detected**, of which
**16 are real Lean `axiom` declarations** and 3 are detector false positives (§(e)).

## Read this first

`lake build` is green and Lean reports **no incomplete proofs** — no `sorry` is reached in
any proof position. That is true, and it is **not** the same as "the proofs are done".

Lean's `sorry` warning does not fire on `axiom`. This repository declares 16 axioms, and
**none of them is a necessary axiom** in the policy's §(c) sense (function extensionality,
classical choice, an extraction boundary). Every one is a **stub** — a declaration written
to make the file compile while the implementation or proof was deferred. Two consequences
that must not be understated:

1. **Five axioms occupy executable positions.** `parseToIR`, `deserializeIR`, `many`,
   `many1` and `sepBy` are declared as `axiom`, so they have *no implementation at all*.
   Code that calls them typechecks and cannot run. "34/35 targets build" is therefore a
   statement about typechecking, not about a working parser.
2. **`executePreservesTypes` proves nothing.** Its statement reduces to `… → True`, with
   the body commented `-- Placeholder`. It reads like a type-safety soundness theorem and
   discharges no obligation whatsoever. It is the most misleading item in this list.

Similarly, the worked examples in `TypeSafeQueries.lean` — the ones whose comments claim
`✓ Type-safe INSERT with valid score` and demonstrate that an out-of-range score
`-- Type error: failed to prove 150 ≤ 100` — are themselves axioms. They assert the
existence of the well-typed value rather than constructing it, so they demonstrate the
opposite of what the surrounding comments claim.

None of this is a regression introduced here; it is the inherited state of the imported
GQLdt sources, recorded honestly for the first time.

## (a) Discharged in this repo

- (none yet — entries are removed from §(d) and *not* listed here once a proof lands)

## (b) Budgeted — tested with refutation budget

- (none — this repo has **no executable test coverage**: `lake test` reports
  `no test driver configured`. Nothing here can currently be budgeted, because there is
  no refutation budget to cite. Adding a `@[test_driver]` is a prerequisite for moving
  any item into this section.)

## (c) Necessary axiom

- (none. No axiom in this repository is load-bearing in the §(c) sense.)

## (d) DEBT — actively to be closed

**Owner:** @hyperpolymath · **Deadline:** INDEFINITE — sequenced behind the GNPL narration
layer (see `docs/THEORY.adoc`), except D1 which is called out as urgent below.

### D1 — Fake soundness theorem (close first)

- `src/GqlDt/TypeSafe.lean:194` — `axiom executePreservesTypes`
  - **Kind**: asserted soundness theorem whose statement is vacuous (`… → True`).
  - **Why urgent**: it is the only item here that actively misinforms. A reader
    encountering `executePreservesTypes` reasonably concludes execution is proved
    type-preserving. Nothing of the sort has been established.
  - **Plan**: either state and prove the real property (execution preserves the schema
    typing of `stmt.values`), or **delete the axiom** and record the obligation as an
    open goal. Deleting is strictly better than keeping a vacuous placeholder.
  - **Blocked on**: the `satisfiesConstraints` signature issue noted in the source comment.

### D2 — Unimplemented parser combinators and entry points

Declared `axiom`, therefore **unimplemented**, not merely unproven:

| Location | Axiom | Note |
|---|---|---|
| `src/GqlDt/Parser.lean:130` | `many` | commented-out `partial def` below it; `-- TODO: Fix infinite loop in type checker` |
| `src/GqlDt/Parser.lean:141` | `many1` | as above |
| `src/GqlDt/Parser.lean:149` | `sepBy` | as above |
| `src/GqlDt/Parser.lean:347` | `parseSelectList` | |
| `src/GqlDt/Parser.lean:417` | `parseSelect` | |
| `src/GqlDt/Parser.lean:504` | `parseStatement` | |
| `src/GqlDt/Parser.lean:549` | `parseToIR` | pipeline entry point; DELETE→IR conversion commented out as not implemented |
| `src/GqlDt/IR.lean:348` | `deserializeIR` | `-- TODO: Implement full CBOR deserialization with schema reconstruction` |

- **Plan**: implement as `partial def` (or with an explicit termination measure /
  fuel parameter, which is the standard Lean 4 remedy for the combinator
  non-termination the source comment describes). `many`/`many1`/`sepBy` are the
  root — the four `parse*` axioms above them exist because these three do.
- **Consequence while open**: the M6 "parser substantially complete" status in
  `README.md` overstates what is executable. Corrected in `README.adoc`.

### D3 — Example/fixture values asserted rather than constructed

| Location | Axiom |
|---|---|
| `src/GqlDt/Parser.lean:268` | `evidenceSchema` — `/-- Dummy schema for type inference -/` |
| `src/GqlDt/IR.lean:721` | `exampleInsertIR` — "Simplified to use axioms to avoid complex PromptScores proof obligations" |
| `src/GqlDt/TypeSafeQueries.lean:44` | `insertWithValidScore` |
| `src/GqlDt/TypeSafeQueries.lean:73` | `validPromptScores` |
| `src/GqlDt/TypeSafeQueries.lean:99` | `insertWithProvenance` |
| `src/GqlDt/TypeSafeQueries.lean:119` | `selectHighQuality` |

- **Plan**: construct each concretely, discharging the `BoundedNat 0 100` /
  `NonEmptyString` / `Confidence` obligations with `by decide` or `by norm_num`. These
  are the *demonstrations* of the repo's central claim ("invalid insert won't compile"),
  so leaving them asserted defeats their purpose. Lowest difficulty, highest
  credibility-per-unit-effort of the three groups — **do these first after D1**.

### D4 — Dynamic-to-static reflection gap

- `src/GqlDt/Pipeline.lean:147` — `axiom inferredInsertTypesMatch`
  - **Kind**: the one item with a *reasoned* justification in-source — the dynamic schema
    lookup in `inferInsert` already performs the check, and reconstructing that proof
    structurally would require reflecting the schema into the type system.
  - **Assessment**: plausible, and closest of the 16 to a genuine §(b)/§(c) entry — but it
    cannot be promoted to §(b) today because there is no test suite to give it a
    refutation budget, and not to §(c) because it *is* derivable in principle.
  - **Plan**: promote to §(b) once a test driver exists and this path is property-tested;
    or discharge via schema reflection (the source's own "future work").

## (e) Detector false positives — no action

The estate checker matches `\bsorry\b` textually in `.lean` files. Three hits are not
escape hatches, and are listed here so the count reconciles (19 = 16 + 3):

| Location | What it actually is |
|---|---|
| `src/GqlDt/TypeInference.lean:179` | `\| .admit => "sorry"` — a **string literal** returned by a pretty-printer |
| `src/GqlDt/Lexer.lean:230` | `("sorry", .kwSorry)` — a **keyword table entry**; GQL-dt has a `sorry` token |
| `test/LexerTest.lean:147` | `runTest "sorry" (firstType "sorry" == some .kwSorry)` — a **test input** |

A fourth textual hit, `src/GqlDt/TypeSafeQueries.lean:90`
(`--     overall_correct := by sorry }`), is inside a comment and is already excluded by
the checker's own comment filter.

`scripts/check-lean-proofs.sh` in this repo excludes all four by design. See its header.

## Reconciliation with `scripts/check-lean-proofs.sh`

The two checks answer different questions and both are needed:

| Check | Question | Current answer |
|---|---|---|
| `scripts/check-lean-proofs.sh --build-log` | Does Lean report any incomplete proof (`sorry`/`sorryAx`)? | **No** ✅ |
| `standards/scripts/check-trusted-base.sh` | How large is the unproven trusted base (`axiom`)? | **16 axioms, all stubs** ❌ |

A green proof gate here means "nothing is admitted mid-proof". It does **not** mean
"nothing is assumed". This document is the record of what is assumed.
