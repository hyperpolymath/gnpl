-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Gnpl

open Gnpl Lean

private def emit (j : Json) : IO Unit := IO.println j.compress

private def inputError (message : String) : IO UInt32 := do
  emit (Json.mkObj [("status", toJson ("input-error" : String)), ("message", toJson message)])
  return 2

private def loadInputs (evidencePath projectionPath : String) : IO (Except String (Fabula × Projection)) := do
  try
    let evidence ← IO.FS.readFile evidencePath
    let projection ← IO.FS.readFile projectionPath
    return do
      let fabula ← Wire.decodeFabula evidence
      let plan ← Surface.parse projection
      pure (fabula, plan)
  catch e => return .error e.toString

private def run (f : Fabula) (p : Projection) (withdrawId : Option String) : IO UInt32 := do
  match narrate f p with
  | .error refusal => emit (Wire.refusalToJson refusal); return 1
  | .ok before =>
    match withdrawId with
    | none => emit (Wire.accountToJson before); return 0
    | some id =>
      match withdraw f id with
      | .error refusal => emit (Wire.refusalToJson refusal); return 1
      | .ok changed =>
        let (status, after, code) := match narrate changed p with
          | .ok account => ("preserved", Wire.accountToJson account, 0)
          | .error refusal => ("invalidated", Wire.refusalToJson refusal, 1)
        emit (Json.mkObj [
          ("format", toJson ("gnpl-counterfactual-v1" : String)),
          ("status", toJson status), ("withdrawnEvidence", toJson id),
          ("before", Wire.accountToJson before), ("after", after)])
        return code.toUInt32

def main (args : List String) : IO UInt32 := do
  let params := match args with
    | ["narrate", "--evidence", e, "--projection", p] => some (e, p, none)
    | ["counterfactual", "--evidence", e, "--projection", p, "--withdraw", id] =>
        some (e, p, some id)
    | _ => none
  let some (e, p, withdrawal) := params
    | inputError "Usage: gnpl narrate --evidence FILE --projection FILE | gnpl counterfactual --evidence FILE --projection FILE --withdraw ID"
  match ← loadInputs e p with
  | .error message => inputError message
  | .ok (f, plan) => run f plan withdrawal
