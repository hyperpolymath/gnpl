-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Gnpl.Core
import Lean.Data.Json

namespace Gnpl.Surface
open Lean

inductive Token where
  | word : String → Token
  | quoted : String → Token
  deriving Repr, BEq

private def quoted (acc : List Char) (escaped : Bool) :
    List Char → Except String (String × List Char)
  | [] => .error "Unterminated quoted string"
  | c :: cs =>
      if c == '"' && !escaped then do
        let json ← Json.parse (String.mk (('"' :: acc).reverse))
        let value ← json.getStr?
        pure (value, cs)
      else quoted (c :: acc) (c == '\\' && !escaped) cs

private def scan : Nat → List Char → Except String (List Token)
  | _, [] => .ok []
  | 0, _ => .error "Token budget exhausted"
  | fuel + 1, chars@(c :: cs) => do
      if c.isWhitespace then scan fuel cs
      else if c == '"' then
        let (value, rest) ← quoted ['"'] false cs
        let tokens ← scan fuel rest
        pure (.quoted value :: tokens)
      else
        let word := chars.takeWhile (fun c => !c.isWhitespace && c != '"')
        let tokens ← scan fuel (chars.drop word.length)
        pure (.word (String.mk word) :: tokens)

def tokenizeLine (line : String) : Except String (List Token) :=
  scan (line.length + 1) line.toList

private def assertion (line : Nat) : List Token → Except String AssertionRequest
  | [.word "assert", .quoted subject, .quoted slot, .quoted value,
     .word "citing", .quoted evidenceId] =>
      .ok ⟨⟨subject, slot, value⟩, evidenceId⟩
  | _ => .error s!"Line {line}: expected assert SUBJECT SLOT VALUE citing EVIDENCE"

/-- One complete projection. Quoted strings use JSON escaping; comments occupy
their own lines. No trailing clauses or extra accounts are silently discarded. -/
def parse (source : String) : Except String Projection := do
  let mut lines : List (Nat × List Token) := []
  for (index, text) in source.splitOn "\n" |>.enum do
    let line := text.trim
    if line.isEmpty || line.startsWith "--" then continue
    match tokenizeLine line with
    | .error e => throw s!"Line {index + 1}: {e}"
    | .ok tokens => lines := lines ++ [(index + 1, tokens)]
  match lines with
  | (_, [.word "account", .quoted name]) ::
    (_, [.word "focalized", .word "by", .quoted actor]) ::
    (_, [.word "threshold", .word score]) :: rest =>
      let some minimum := score.toNat?
        | throw "Threshold must be a natural number in [0, 100]"
      if minimum > 100 then throw "Threshold must be in [0, 100]"
      let assertions ← rest.mapM (fun (line, tokens) => assertion line tokens)
      pure ⟨name, ⟨actor, minimum⟩, assertions⟩
  | _ => throw "Expected account NAME, focalized by ACTOR, threshold SCORE, then assertions"

end Gnpl.Surface
