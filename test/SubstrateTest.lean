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

private def confidenceIs (expected : Nat)
    (result : Except String (Σ t : AST.TypeExpr, AST.TypedValue t)) : Bool :=
  match result with
  | .ok ⟨.confidence, .confidence value⟩ => value.val == expected
  | _ => false

def main : IO UInt32 := do
  check "source → schema validation → insertion → filtered retrieval"
    roundTrip
  for (name, source) in [
    ("empty INSERT", "INSERT INTO evidence () VALUES () RATIONALE 'r';"),
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
  let confidenceConfig := { config with schema := { config.schema with
    name := "scores", columns := [{
      name := "score", type := .confidence, isPrimaryKey := false, isUnique := false }] } }
  for score in [0, 85, 100] do
    check s!"preserve Confidence type and value {score} through lowering"
      (match runPipeline s!"INSERT INTO scores (score) VALUES ({score}) RATIONALE 'r';"
          confidenceConfig with
       | .ok (.insert stmt) =>
           match stmt.values with
           | [⟨.confidence, .confidence value⟩] =>
               value.val == score && typedValueToString (.confidence value) == toString score
           | _ => false
       | _ => false)
  check "reject Confidence above its upper bound"
    (match runPipeline "INSERT INTO scores (score) VALUES (101) RATIONALE 'r';"
        confidenceConfig with
     | .error _ => true | .ok _ => false)
  let confidence : Σ t : AST.TypeExpr, AST.TypedValue t :=
    ⟨.confidence, .confidence ⟨85, by decide, by decide⟩⟩
  check "Confidence JSON preserves the type and value"
    (confidenceIs 85 (Serialization.deserializeTypedValueJSON
      (Serialization.serializeTypedValueJSON confidence)))
  for format in [Serialization.Types.SerializationFormat.binary, .cbor] do
    check s!"Confidence {repr format} preserves the type and value"
      (confidenceIs 85 (Serialization.deserialize format
        (Serialization.serialize format confidence) .confidence))
  check "Confidence SQL conversion requires the distinct type hint"
    (confidenceIs 85 (Serialization.fromSQLValue
      (Serialization.toSQLValue confidence) .confidence))
  for bad in [-1.0, 85.5, 101.0] do
    check "Confidence JSON refuses out-of-range or fractional scores"
      (match Serialization.deserializeTypedValueJSON
        (.object [("type", .string "Confidence"), ("value", .number bad)]) with
       | .error _ => true | .ok _ => false)
  check "Confidence binary refuses an out-of-range score"
    (match Serialization.deserializeTypedValueBinary
        (ByteArray.mk #[0x09, 101, 0, 0, 0, 0, 0, 0, 0]) with
     | .error _ => true | .ok _ => false)
  check "CBOR eight-byte scores cannot collapse to zero"
    (match Serialization.decodeCBOR (ByteArray.mk #[0x1b, 0, 0, 0, 0, 0, 0, 1, 0]) with
     | .ok (.unsigned n) => n == 256 | _ => false)
  check "CBOR text rejects invalid UTF-8"
    (match Serialization.decodeCBOR (ByteArray.mk #[0x61, 0xff]) with
     | .error _ => true | .ok _ => false)
  check "reject non-consuming repetition"
    (match Parser.many (pure () : Parser.Parser Unit) { tokens := [], position := 0 } with
     | .error _ _ => true | .ok _ _ => false)
  check "attached-proof mode refuses unverified input"
    (match runPipeline (insertSource "First" 95) (defaultGQLdtConfig "test" "test") with
     | .error _ => true | .ok _ => false)
  check "unavailable proof strategy cannot emit an unchecked proof"
    (match TypeInference.generateProofTerm .admit with
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
