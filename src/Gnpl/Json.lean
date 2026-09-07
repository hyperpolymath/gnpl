-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Gnpl.Core
import Lean.Data.Json

namespace Gnpl.Wire
open Lean

private def fields (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  for key in object.fold (fun keys key _ => key :: keys) [] do
    if !allowed.contains key then throw s!"Unknown field: {key}"

private def claimFromJson (j : Json) : Except String Claim := do
  fields j ["subject", "slot", "value"]
  pure ⟨← j.getObjValAs? String "subject", ← j.getObjValAs? String "slot",
        ← j.getObjValAs? String "value"⟩

private def evidenceFromJson (j : Json) : Except String Evidence := do
  fields j ["id", "source", "claim", "rationale", "confidence", "audience", "withdrawn"]
  pure ⟨← j.getObjValAs? String "id", ← j.getObjValAs? String "source",
        ← claimFromJson (← j.getObjVal? "claim"), ← j.getObjValAs? String "rationale",
        ← j.getObjValAs? Nat "confidence", ← j.getObjValAs? (List String) "audience",
        ← j.getObjValAs? Bool "withdrawn"⟩

/-- Versioned evidence import, separate from the narration surface. The import
boundary trusts source attribution, audience declarations and recorded scores. -/
def decodeFabula (text : String) : Except String Fabula := do
  let j ← Json.parse text
  fields j ["format", "snapshot", "revision", "evidence"]
  let format ← j.getObjValAs? String "format"
  if format != "gnpl-evidence-v1" then throw "Unsupported evidence format"
  let evidence ← (← (← j.getObjVal? "evidence").getArr?).toList.mapM evidenceFromJson
  pure ⟨← j.getObjValAs? String "snapshot", ← j.getObjValAs? Nat "revision", evidence⟩

def claimToJson (c : Claim) : Json := Json.mkObj [
  ("subject", toJson c.subject), ("slot", toJson c.slot), ("value", toJson c.value)]

private def narrationToJson {f : Fabula} {s : Focalization} {rs : List AssertionRequest} :
    Narration f s rs → List Json
  | .nil => []
  | .cons w rest => Json.mkObj [
      ("claim", claimToJson w.evidence.claim),
      ("warrant", Json.mkObj [
        ("rule", toJson ("direct-evidence" : String)),
        ("evidence", toJson w.evidence.id), ("source", toJson w.evidence.source),
        ("rationale", toJson w.evidence.rationale),
        ("declaredConfidence", toJson w.evidence.confidence)])] :: narrationToJson rest

def accountToJson {f : Fabula} {p : Projection} (a : Account f p) : Json :=
  Json.mkObj [
    ("format", toJson ("gnpl-account-v1" : String)),
    ("status", toJson ("warranted" : String)), ("account", toJson p.name),
    ("snapshot", toJson f.snapshot), ("revision", toJson f.revision),
    ("focalization", Json.mkObj [("actor", toJson p.focalization.actor),
      ("minimumConfidence", toJson p.focalization.minimumConfidence)]),
    ("assertions", toJson (narrationToJson a.narration))]

def Refusal.codeName : RefusalCode → String
  | .invalidSnapshot => "invalid-snapshot"
  | .invalidProjection => "invalid-projection"
  | .missingEvidence => "missing-evidence"
  | .evidenceWithdrawn => "evidence-withdrawn"
  | .inaccessibleEvidence => "inaccessible-evidence"
  | .claimMismatch => "claim-mismatch"
  | .belowThreshold => "below-threshold"
  | .invalidEvidence => "invalid-evidence"

def refusalToJson (r : Refusal) : Json := Json.mkObj [
  ("status", toJson ("refused" : String)), ("code", toJson (Refusal.codeName r.code)),
  ("evidence", toJson r.evidenceId)]

end Gnpl.Wire
