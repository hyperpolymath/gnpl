-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Std

/-! Direct-evidence narration. No inference rules or probabilistic combination
are assumed. A claim assigns a value to a declared single-valued subject/slot.
The kernel depends only on Lean/Std, not the experimental storage substrate. -/
namespace Gnpl

structure Claim where
  subject : String
  slot : String
  value : String
  deriving Repr, DecidableEq

structure Evidence where
  id : String
  source : String
  claim : Claim
  rationale : String
  confidence : Nat
  audience : List String
  withdrawn : Bool
  deriving Repr, DecidableEq

/-- An immutable evidence snapshot; list order makes no temporal/causal claim. -/
structure Fabula where
  snapshot : String
  revision : Nat
  evidence : List Evidence
  deriving Repr, DecidableEq

structure Focalization where
  actor : String
  minimumConfidence : Nat
  deriving Repr, DecidableEq

structure AssertionRequest where
  claim : Claim
  evidenceId : String
  deriving Repr, DecidableEq

/-- Assertion order is the declared telling order, not an inferred event order. -/
structure Projection where
  name : String
  focalization : Focalization
  assertions : List AssertionRequest
  deriving Repr, DecidableEq

def nonblank (s : String) : Bool := !s.trim.isEmpty

def Claim.wellFormed (c : Claim) : Bool :=
  nonblank c.subject && nonblank c.slot && nonblank c.value

def Evidence.wellFormed (e : Evidence) : Bool :=
  nonblank e.id && nonblank e.source && e.claim.wellFormed &&
  nonblank e.rationale && e.confidence ≤ 100

def Fabula.wellFormed (f : Fabula) : Bool :=
  nonblank f.snapshot && f.evidence.all Evidence.wellFormed &&
  decide (f.evidence.map Evidence.id).Nodup

def Claim.conflicts (a b : Claim) : Bool :=
  a.subject == b.subject && a.slot == b.slot && a.value != b.value

def Projection.wellFormed (p : Projection) : Bool :=
  nonblank p.name && nonblank p.focalization.actor &&
  p.focalization.minimumConfidence ≤ 100 && !p.assertions.isEmpty &&
  p.assertions.all (fun r => r.claim.wellFormed && nonblank r.evidenceId) &&
  decide (p.assertions.map AssertionRequest.claim).Nodup &&
  !p.assertions.any (fun a => p.assertions.any (fun b => a.claim.conflicts b.claim))

/-- Support is traceability and admission under a stance, never external truth. -/
def Supports (f : Fabula) (s : Focalization) (r : AssertionRequest) (e : Evidence) : Prop :=
  e ∈ f.evidence ∧ e.id = r.evidenceId ∧ e.claim = r.claim ∧
  e.withdrawn = false ∧ s.actor ∈ e.audience ∧ e.wellFormed = true ∧
  s.minimumConfidence ≤ e.confidence

instance (f : Fabula) (s : Focalization) (r : AssertionRequest) (e : Evidence) :
    Decidable (Supports f s r e) := by
  unfold Supports
  infer_instance

/-- Indexed by the exact snapshot, stance and requested assertion. -/
structure Warrant (f : Fabula) (s : Focalization) (r : AssertionRequest) where
  evidence : Evidence
  support : Supports f s r evidence

/-- The index fixes both the claims and their telling order. -/
inductive Narration (f : Fabula) (s : Focalization) : List AssertionRequest → Type where
  | nil : Narration f s []
  | cons {r : AssertionRequest} {rs : List AssertionRequest}
      (warrant : Warrant f s r) (rest : Narration f s rs) : Narration f s (r :: rs)

structure Account (f : Fabula) (p : Projection) where
  snapshotValid : f.wellFormed = true
  projectionValid : p.wellFormed = true
  narration : Narration f p.focalization p.assertions

inductive RefusalCode where
  | invalidSnapshot | invalidProjection | missingEvidence | evidenceWithdrawn
  | inaccessibleEvidence | claimMismatch | belowThreshold | invalidEvidence
  deriving Repr, BEq, DecidableEq

structure Refusal where
  code : RefusalCode
  evidenceId : String := ""
  deriving Repr, BEq, DecidableEq

def checkWarrant (f : Fabula) (s : Focalization) (r : AssertionRequest) :
    Except Refusal (Warrant f s r) := do
  let some e := f.evidence.find? (fun e => e.id == r.evidenceId)
    | throw ⟨.missingEvidence, r.evidenceId⟩
  if e.withdrawn then throw ⟨.evidenceWithdrawn, r.evidenceId⟩
  if !e.audience.contains s.actor then throw ⟨.inaccessibleEvidence, r.evidenceId⟩
  if e.claim != r.claim then throw ⟨.claimMismatch, r.evidenceId⟩
  if e.confidence < s.minimumConfidence then throw ⟨.belowThreshold, r.evidenceId⟩
  if h : Supports f s r e then pure ⟨e, h⟩
  else throw ⟨.invalidEvidence, r.evidenceId⟩

def checkNarration (f : Fabula) (s : Focalization) :
    (rs : List AssertionRequest) → Except Refusal (Narration f s rs)
  | [] => .ok .nil
  | r :: rs => do
      let w ← checkWarrant f s r
      let rest ← checkNarration f s rs
      pure (.cons w rest)

def narrate (f : Fabula) (p : Projection) : Except Refusal (Account f p) :=
  if hf : f.wellFormed = true then
    if hp : p.wellFormed = true then do
      let narration ← checkNarration f p.focalization p.assertions
      pure ⟨hf, hp, narration⟩
    else .error ⟨.invalidProjection, ""⟩
  else .error ⟨.invalidSnapshot, ""⟩

/-- Counterfactual view only: does not mutate or persist the original snapshot. -/
def withdraw (f : Fabula) (id : String) : Except Refusal Fabula :=
  if f.evidence.any (fun e => e.id == id) then
    .ok { f with
      revision := f.revision + 1
      evidence := f.evidence.map (fun e => if e.id == id then { e with withdrawn := true } else e) }
  else .error ⟨.missingEvidence, id⟩

/-- A withdrawn item cannot satisfy the direct-evidence warrant rule. -/
theorem withdrawn_cannot_support (f : Fabula) (s : Focalization)
    (r : AssertionRequest) (e : Evidence) (h : e.withdrawn = true) :
    ¬ Supports f s r e := by
  intro hs
  have active : e.withdrawn = false := hs.2.2.2.1
  simp [h] at active

def Narration.claims {f : Fabula} {s : Focalization} {rs : List AssertionRequest} :
    Narration f s rs → List Claim
  | .nil => []
  | .cons w rest => w.evidence.claim :: rest.claims

/-- The checked output contains exactly the requested claims, in their order. -/
theorem narration_preserves_projection {f : Fabula} {s : Focalization}
    {rs : List AssertionRequest} (n : Narration f s rs) :
    n.claims = rs.map AssertionRequest.claim := by
  induction n with
  | nil => rfl
  | cons w rest ih =>
      have matched := w.support.2.2.1
      simp [Narration.claims, matched, ih]

/-- A limited relation on the single-valued claim fragment, not adjudication. -/
def rival {f : Fabula} {a b : Projection} (_ : Account f a) (_ : Account f b) : Bool :=
  a.assertions.any (fun x => b.assertions.any (fun y => x.claim.conflicts y.claim))

end Gnpl
