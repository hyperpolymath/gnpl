-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Gnpl
import TestHarness

open Gnpl GnplTest Lean

private def closed : Claim := ⟨"bridge", "status", "closed"⟩
private def opened : Claim := ⟨"bridge", "status", "open"⟩
private def rain : Claim := ⟨"site", "weather", "rain"⟩
private def inspection : Evidence :=
  ⟨"inspection-17", "inspector", closed, "Recorded inspection", 90, ["analyst"], false⟩
private def witness : Evidence :=
  ⟨"witness-22", "witness", opened, "Recorded witness statement", 80, ["analyst"], false⟩
private def weather : Evidence :=
  ⟨"weather-3", "weather-log", rain, "Recorded weather", 95, ["analyst"], false⟩
private def snapshot : Fabula := ⟨"case", 7, [inspection, witness, weather]⟩
private def plan : Projection :=
  ⟨"inspection", ⟨"analyst", 70⟩, [⟨closed, "inspection-17"⟩, ⟨rain, "weather-3"⟩]⟩

private def refusalIs (f : Fabula) (p : Projection) (code : RefusalCode) : Bool :=
  match narrate f p with
  | .error refusal => refusal.code == code
  | .ok _ => false

private def source := "account \"inspection\"\nfocalized by \"analyst\"\nthreshold 70\nassert \"bridge\" \"status\" \"closed\" citing \"inspection-17\"\nassert \"site\" \"weather\" \"rain\" citing \"weather-3\""

def main : IO UInt32 := do
  check "source → projection → warranted account with declared order"
    (match Surface.parse source with
     | .error _ => false
     | .ok p => match narrate snapshot p with
       | .error _ => false
       | .ok a => a.narration.claims == [closed, rain])
  check "reversing telling order changes account without inventing claims"
    (match narrate snapshot { plan with assertions := plan.assertions.reverse } with
     | .ok a => a.narration.claims == [rain, closed] | .error _ => false)
  check "invented assertion refused despite a real citation"
    (refusalIs snapshot { plan with assertions := [⟨opened, "inspection-17"⟩] } .claimMismatch)
  check "missing citation refused"
    (refusalIs snapshot { plan with assertions := [⟨closed, "missing"⟩] } .missingEvidence)
  check "focalization restricts accessible evidence"
    (refusalIs snapshot { plan with focalization := ⟨"public", 70⟩ } .inaccessibleEvidence)
  check "threshold admits a boundary value"
    (match narrate snapshot { plan with focalization := ⟨"analyst", 90⟩ } with
     | .ok _ => true | .error _ => false)
  check "threshold refuses a lower recorded score"
    (refusalIs snapshot { plan with focalization := ⟨"analyst", 91⟩ } .belowThreshold)
  check "out-of-domain confidence refused"
    (refusalIs { snapshot with evidence := [{ inspection with confidence := 101 }, weather] }
      plan .invalidSnapshot)
  check "blank rationale refused"
    (refusalIs { snapshot with evidence := [{ inspection with rationale := " \t " }, weather] }
      plan .invalidSnapshot)
  check "duplicate evidence identifiers refused, independent of lookup order"
    (refusalIs { snapshot with evidence := inspection :: snapshot.evidence } plan .invalidSnapshot)
  check "empty account refused" (refusalIs snapshot { plan with assertions := [] } .invalidProjection)
  check "duplicated assertion refused"
    (refusalIs snapshot { plan with assertions := plan.assertions ++ plan.assertions } .invalidProjection)
  let other : Projection := ⟨"witness", ⟨"analyst", 70⟩, [⟨opened, "witness-22"⟩]⟩
  check "rival accounts both remain warranted without choosing a winner"
    (match narrate snapshot plan, narrate snapshot other with
     | .ok a, .ok b => rival a b && rival b a
     | _, _ => false)
  check "conflicting assertions cannot be blended into one account"
    (refusalIs snapshot { plan with assertions := plan.assertions ++ other.assertions } .invalidProjection)
  check "withdrawal invalidates an account that depends on that source"
    (match withdraw snapshot "inspection-17" with
     | .ok f => refusalIs f plan .evidenceWithdrawn && f.revision == 8
     | .error _ => false)
  check "withdrawing an uncited rival source preserves the account"
    (match withdraw snapshot "witness-22" with
     | .ok f => match narrate f plan with
       | .ok a => a.narration.claims == [closed, rain] | .error _ => false
     | .error _ => false)
  check "counterfactual leaves original snapshot warranted"
    (match narrate snapshot plan with | .ok _ => true | .error _ => false)
  check "withdrawal of unknown evidence is an error"
    (match withdraw snapshot "absent" with
     | .error r => r.code == .missingEvidence | .ok _ => false)
  for bad in [source ++ "\nextra", source ++ "\naccount \"second\"",
              source.replace "threshold 70" "threshold -1",
              source.replace "threshold 70" "threshold 101",
              source.replace "citing \"inspection-17\"" "citing", "account \"unterminated"] do
    check "malformed or trailing source refused"
      (match Surface.parse bad with | .error _ => true | .ok _ => false)
  check "quoted strings preserve escaped quotes and Unicode"
    (match Surface.parse (source.replace "account \"inspection\"" "account \"A \\\"quoted\\\" λ\"") with
     | .ok p => p.name == "A \"quoted\" λ" | .error _ => false)
  let fixture ← IO.FS.readFile "examples/narration/evidence.json"
  check "versioned evidence snapshot loads and warrants the projection"
    (match Wire.decodeFabula fixture with
     | .ok f => match narrate f plan with | .ok _ => true | .error _ => false
     | .error _ => false)
  check "unrecognised evidence fields are not silently discarded"
    (match Wire.decodeFabula (fixture.replace "\"revision\": 7" "\"revision\": 7, \"proof\": \"trust me\"") with
     | .error _ => true | .ok _ => false)
  check "unsupported evidence version refused"
    (match Wire.decodeFabula (fixture.replace "gnpl-evidence-v1" "gnpl-evidence-v2") with
     | .error _ => true | .ok _ => false)
  -- Real process boundary: input files → executable → JSON + exit status.
  -- The executable must have been built; failures never silently skip this slice.
  let evidenceArgs := #["--evidence", "examples/narration/evidence.json", "--projection"]
  for (mode, projection, extra, expectedCode, expectedStatus) in [
    ("narrate", "inspection.gnpl", #[], 0, "warranted"),
    ("narrate", "witness.gnpl", #[], 0, "warranted"),
    ("narrate", "inaccessible.gnpl", #[], 1, "refused"),
    ("counterfactual", "inspection.gnpl", #["--withdraw", "inspection-17"], 1, "invalidated"),
    ("counterfactual", "inspection.gnpl", #["--withdraw", "witness-22"], 0, "preserved")
  ] do
    let result ← IO.Process.output {
      cmd := ".lake/build/bin/gnpl"
      args := #[mode] ++ evidenceArgs ++ #["examples/narration/" ++ projection] ++ extra }
    let status := do
      let json ← Json.parse result.stdout
      json.getObjValAs? String "status"
    check s!"CLI {mode} {projection} {extra}: {expectedStatus}"
      (result.exitCode == expectedCode &&
        match status with | .ok value => value == expectedStatus | .error _ => false)
  let missing ← IO.Process.output {
    cmd := ".lake/build/bin/gnpl"
    args := #["narrate"] ++ evidenceArgs ++ #["examples/narration/nonexistent.gnpl"] }
  check "CLI missing input returns an input error, not an account" (missing.exitCode == 2)
  let afterFixture ← IO.FS.readFile "examples/narration/evidence.json"
  check "CLI counterfactual preserves the evidence file byte for byte" (afterFixture == fixture)
  summarise "GNPL narration"
