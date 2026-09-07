-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (@hyperpolymath)
import GqlDt.Pipeline
import TestHarness

open GqlDt GqlDt.Pipeline GqlDt.IR GnplTest

private def config := defaultGQLConfig "substrate-test" "test"

private def insertSource (title : String) (score : Nat) :=
  s!"INSERT INTO evidence (title, prompt_provenance) VALUES ('{title}', {score}) RATIONALE 'Declared test evidence';"

private def rejects (source : String) : Bool :=
  match runPipeline source config with
  | .error _ => true
  | .ok _ => false

private def roundTrip : Bool :=
  match runPipeline (insertSource "First" 95) config,
        runPipeline (insertSource "Second" 75) config,
        runPipeline "SELECT title FROM evidence WHERE prompt_provenance > 80;" config with
  | .ok a, .ok b, .ok selected =>
      let (db1, _) := evalIR EvalDatabase.empty a
      let (db2, _) := evalIR db1 b
      match (evalIR db2 selected).2 with
      | .rows columns rows => columns == ["title"] && rows == [["First"]]
      | _ => false
  | _, _, _ => false

def main : IO UInt32 := do
  check "source → schema validation → insertion → filtered retrieval"
    roundTrip
  for (name, source) in [
    ("out-of-range evidence", insertSource "Bad" 150),
    ("unknown table", "INSERT INTO other (title) VALUES ('x') RATIONALE 'r';"),
    ("unknown column", "INSERT INTO evidence (missing) VALUES ('x') RATIONALE 'r';"),
    ("empty refined string", "INSERT INTO evidence (title) VALUES ('') RATIONALE 'r';"),
    ("empty rationale", "INSERT INTO evidence (title) VALUES ('x') RATIONALE '';"),
    ("column/value arity", "INSERT INTO evidence (title) VALUES ('x', 'y') RATIONALE 'r';"),
    ("incorrect annotation", "INSERT INTO evidence (title : Nat) VALUES ('x') RATIONALE 'r';"),
    ("trailing comma", "SELECT title, FROM evidence;"),
    ("malformed optional WHERE", "SELECT * FROM evidence WHERE title =;"),
    ("malformed optional LIMIT", "SELECT * FROM evidence LIMIT nope;"),
    ("unconsumed suffix", "SELECT * FROM evidence nonsense;"),
    ("second statement", "SELECT * FROM evidence; SELECT * FROM evidence;"),
    ("unknown projection", "SELECT missing FROM evidence;"),
    ("predicate type mismatch", "SELECT * FROM evidence WHERE prompt_provenance > '80';"),
    ("unsupported text ordering", "SELECT * FROM evidence ORDER BY title;"),
    ("unsupported ordered text predicate", "SELECT * FROM evidence WHERE title > '10';"),
    ("unsupported join", "SELECT * FROM evidence, other;"),
    ("unchecked update", "UPDATE evidence SET title = '' RATIONALE 'r';")
  ] do check ("reject " ++ name) (rejects source)
  check "explicit matching type annotation"
    (!rejects "INSERT INTO evidence (title :: NonEmptyString) VALUES ('x') RATIONALE 'r';")
  let custom := { config with schema := { config.schema with name := "accounts" } }
  check "use caller's schema"
    (match runPipeline "INSERT INTO accounts (title) VALUES ('x') RATIONALE 'r';" custom with
     | .ok _ => true | .error _ => false)
  check "reject non-consuming repetition"
    (match Parser.many (pure () : Parser.Parser Unit) { tokens := [], position := 0 } with
     | .error _ _ => true | .ok _ _ => false)
  check "attached-proof mode refuses unverified input"
    (match runPipeline (insertSource "First" 95) (defaultGQLdtConfig "test" "test") with
     | .error _ => true | .ok _ => false)
  check "incomplete wire codec refuses success"
    (match runPipelineAndSerialize "SELECT * FROM evidence WHERE title = 'First';" config with
     | .error _ => true | .ok _ => false)
  check "wire decoding refuses unsupported proof reconstruction"
    (match deserializeIR ByteArray.empty with | .error _ => true | .ok _ => false)
  check "persistent execution refuses success"
    (match ← parseAndExecute (insertSource "First" 95) config with
     | .error _ => true | .ok _ => false)
  summarise "GNPL private substrate"
