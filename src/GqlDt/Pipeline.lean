-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (@hyperpolymath)
--
-- Complete Parsing Pipeline: Source → IR
-- Orchestrates lexer, parser, type checker, IR generation

import GqlDt.Lexer
import GqlDt.Parser
import GqlDt.TypeChecker
import GqlDt.TypeInference
import GqlDt.IR
import GqlDt.Serialization

namespace GqlDt.Pipeline

section

open Lexer Parser TypeChecker TypeInference IR Serialization Serialization.Types AST Provenance

/-!
GNPL's private typed evidence substrate.

This module parses a limited storage notation, checks inserts against the supplied
schema, and builds IR for in-memory evaluation. It does not implement GNPL's
accounts, stances or warrants. Historical identifiers in this namespace are
compatibility details, not names of public languages.

Attached-proof verification, persistent execution and a complete IR wire codec
are unavailable and return errors. Local dependent witnesses are not transferable
proof certificates. See docs/executable-boundary.adoc.
-/

-- ============================================================================
-- Pipeline Configuration
-- ============================================================================

/-- Parsing mode -/
inductive ParsingMode where
  | gqld : ParsingMode   -- Explicit types, compile-time proofs
  | gql : ParsingMode    -- Type inference, runtime validation
  deriving Repr, BEq

/-- Pipeline configuration -/
structure PipelineConfig where
  mode : ParsingMode
  schema : Schema
  permissions : PermissionMetadata
  validationLevel : ValidationLevel
  serializationFormat : SerializationFormat
  deriving Repr

/-- Default configuration for GQL (user tier) -/
def defaultGQLConfig (userId roleId : String) : PipelineConfig := {
  mode := .gql,
  schema := evidenceSchema,  -- TODO: Schema registry lookup
  permissions := {
    userId := userId,
    roleId := roleId,
    validationLevel := .runtime,
    allowedTypes := [],  -- Empty = all types allowed
    timestamp := 0  -- TODO: Get current timestamp
  },
  validationLevel := .runtime,
  serializationFormat := .cbor
}

/-- Default configuration for GQL-DT (admin tier) -/
def defaultGQLdtConfig (userId roleId : String) : PipelineConfig := {
  mode := .gqld,
  schema := evidenceSchema,
  permissions := {
    userId := userId,
    roleId := roleId,
    validationLevel := .compile,
    allowedTypes := [],  -- Admin: all types allowed
    timestamp := 0
  },
  validationLevel := .compile,
  serializationFormat := .cbor
}

-- ============================================================================
-- Pipeline Stages
-- ============================================================================

/-- Stage 1: Tokenize source -/
def tokenizeSource (source : String) : Except String (List Token) :=
  tokenize source

/-- Stage 2: Parse tokens to AST -/
def parseTokens (tokens : List Token) (config : PipelineConfig) : Except String (List Statement) :=
  parseTokensComplete tokens config.schema

/-- Stage 3: Type check AST -/
def typeCheckAST (stmt : Statement) (config : PipelineConfig) : Except String Statement :=
  -- Runtime type validation does not check an attached proof. The latter
  -- needs an implemented verifier and is refused until one is connected.
  match config.mode with
  | .gql => .ok stmt  -- Type inference done, runtime validation will catch errors
  | .gqld =>
      .error "Attached-proof validation is not implemented"

/-- Convert parser-level ParsedSelect to IR.Select Unit -/
def parsedSelectToIR (ps : ParsedSelect) (permissions : PermissionMetadata) : IR :=
  .select {
    selectList := ps.selectList,
    from_ := ps.from_,
    where_ := ps.where_,
    orderBy := ps.orderBy,
    limit := ps.limit,
    returning := none,
    permissions := permissions
  }

/-- Convert an InferredInsert to IR.Insert using the pipeline schema.

    Each inferred value is lifted into a dependent (Σ t, TypedValue t) pair,
    and the typesMatch proof is constructed dynamically via validateInsert
    from the TypeChecker module.
-/
def inferredInsertToIR (inferred : InferredInsert) (config : PipelineConfig) : Except String IR := do
  -- Convert InferenceResult list to typed values
  let values : List (Σ t : TypeExpr, TypedValue t) := inferred.inferredValues.filterMap fun result =>
    match result.inferredType, result.value with
    | .nat, .nat n => some ⟨.nat, .nat n⟩
    | .int, .int i => some ⟨.int, .int i⟩
    | .string, .string s => some ⟨.string, .string s⟩
    | .bool, .bool b => some ⟨.bool, .bool b⟩
    | .float, .float f => some ⟨.float, .float f⟩
    | .nonEmptyString, .string s =>
        if h : s.length > 0 then
          some ⟨.nonEmptyString, .nonEmptyString ⟨s, h⟩⟩
        else none
    | .boundedNat min max, .nat n =>
        if h1 : min ≤ n then
          if h2 : n ≤ max then
            some ⟨.boundedNat min max, .boundedNat min max ⟨n, h1, h2⟩⟩
          else none
        else none
    | .confidence, .nat n =>
        if h1 : 0 ≤ n then
          if h2 : n ≤ 100 then
            some ⟨.confidence, .confidence ⟨n, h1, h2⟩⟩
          else none
        else none
    | _, _ => none

  if values.length ≠ inferred.inferredValues.length then
    .error s!"Failed to convert all inferred values to typed values"
  else
    -- Build rationale
    if h : inferred.rationale.length > 0 then
      let rationale : Provenance.Rationale := { text := ⟨inferred.rationale, h⟩ }
      -- Extract proof blobs from typed values
      let proofs := values.filterMap fun ⟨t, _v⟩ =>
        match t with
        | .boundedNat min max =>
            some (serializeProof "BoundedNat" s!"value ∈ [{min}, {max}]")
        | .nonEmptyString =>
            some (serializeProof "NonEmptyString" "length > 0")
        | .confidence =>
            some (serializeProof "Confidence" "value ∈ [0, 100]")
        | _ => none
      match TypeChecker.validateInsert config.schema inferred.columns values with
      | .error msg => .error msg
      | .ok ⟨witness⟩ => .ok (@IR.insert config.schema {
          table := inferred.table,
          columns := inferred.columns,
          values := values,
          rationale := rationale,
          proofs := proofs,
          permissions := config.permissions,
          typesMatch := witness
        })
    else
      .error "RATIONALE must be a non-empty string"

/-- Convert ParsedUpdate to IR.Update -/
def parsedUpdateToIR (pu : ParsedUpdate) (config : PipelineConfig) : IR :=
  @IR.update config.schema {
    table := pu.table,
    assignments := pu.assignments,
    where_ := pu.where_,
    rationale := pu.rationale,
    proofs := pu.assignments.filterMap fun a =>
      match a.value.1 with
      | .boundedNat min max =>
          some (serializeProof "BoundedNat" s!"value ∈ [{min}, {max}]")
      | .nonEmptyString =>
          some (serializeProof "NonEmptyString" "length > 0")
      | _ => none,
    permissions := config.permissions
  }

/-- Convert ParsedDelete to IR.Delete -/
def parsedDeleteToIR (pd : ParsedDelete) (config : PipelineConfig) : IR :=
  @IR.delete config.schema {
    table := pd.table,
    where_ := pd.where_,
    rationale := pd.rationale,
    permissions := config.permissions
  }

/-- Stage 4: Generate IR from AST -/
def generateIRFromAST (stmt : Statement) (config : PipelineConfig) : Except String IR :=
  match stmt with
  | .insertGQL inferred =>
      inferredInsertToIR inferred config
  | .insertGQLdt inferred =>
      inferredInsertToIR inferred config
  | .select selectStmt => do
      if selectStmt.from_.tables.length != 1 ||
          selectStmt.from_.tables.any (fun t => t.name != config.schema.name || t.alias.isSome) then
        throw "Selection requires exactly the configured table, without aliases"
      let known := fun name => config.schema.columns.any (·.name == name)
      match selectStmt.selectList with
      | .columns cols => if !cols.all known then throw "Unknown projection column"
      | .star => pure PUnit.unit
      | .typed _ _ => throw "Refined selection validation is not implemented"
      if let some wc := selectStmt.where_ then
        let (name, op, value) := wc.predicate
        let supported := config.schema.columns.any fun col =>
          col.name == name && match col.type, value with
          | .nat, .nat _ | .boundedNat _ _, .nat _ | .confidence, .nat _ => true
          | .string, .string _ | .nonEmptyString, .string _ | .bool, .bool _ =>
              op == "=" || op == "!="
          | _, _ => false
        if !supported then throw "Predicate type or comparison is unsupported by the in-memory evaluator"
      if let some ob := selectStmt.orderBy then
        let supportedOrder := fun name => config.schema.columns.any fun col =>
          col.name == name && match col.type with
          | .nat | .boundedNat _ _ | .confidence => true
          | _ => false
        if ob.columns.length != 1 || !ob.columns.all (fun c => supportedOrder c.1) then
          throw "Ordering requires one natural-number column"
      pure (parsedSelectToIR selectStmt config.permissions)
  | .update _ =>
      .error "UPDATE schema validation is not implemented in this pipeline"
  | .delete _ =>
      .error "DELETE schema validation is not implemented in this pipeline"

/-- Stage 5: Validate permissions -/
def validateIRPermissions (ir : IR) (_config : PipelineConfig) : Except String Unit :=
  validatePermissions ir

/-- Stage 6: Serialize IR -/
def serializeIRToBytes (ir : IR) (_config : PipelineConfig) : ByteArray :=
  serializeIR ir  -- TODO: Use config.serializationFormat

-- ============================================================================
-- Complete Pipeline
-- ============================================================================

/-- Run complete pipeline: Source → IR -/
def runPipeline (source : String) (config : PipelineConfig) : Except String IR :=
  -- Stage 1: Tokenize
  match tokenizeSource source with
  | .error msg => .error msg
  | .ok tokens =>
  -- Stage 2: Parse
  match parseTokens tokens config with
  | .error msg => .error msg
  | .ok stmts =>
  -- Get first statement (TODO: Handle multiple statements)
  match stmts.head? with
  | none => .error "No statements parsed"
  | some stmt =>
  -- Stage 3: Type check
  match typeCheckAST stmt config with
  | .error msg => .error msg
  | .ok checkedStmt =>
  -- Stage 4: Generate IR
  match generateIRFromAST checkedStmt config with
  | .error msg => .error msg
  | .ok ir =>
  -- Stage 5: Validate permissions
  match validateIRPermissions ir config with
  | .error msg => .error msg
  | .ok () => .ok ir

/-- Run pipeline and serialize to bytes -/
def runPipelineAndSerialize (source : String) (config : PipelineConfig) : Except String ByteArray :=
  match runPipeline source config with
  | .error msg => .error msg
  | .ok _ => .error "Complete IR serialization is not implemented; clauses would be lost"

-- ============================================================================
-- Convenience Functions
-- ============================================================================

/-- Parse GQL query (user tier) -/
def parseGQL (source : String) (userId roleId : String) : Except String IR :=
  runPipeline source (defaultGQLConfig userId roleId)

/-- Parse GQL-DT query (admin tier) -/
def parseGQLdt (source : String) (userId roleId : String) : Except String IR :=
  runPipeline source (defaultGQLdtConfig userId roleId)

/-- Parse and execute query -/
def parseAndExecute (source : String) (config : PipelineConfig) : IO (Except String Unit) := do
  match runPipeline source config with
  | .ok _ =>
      return .error "Persistent execution is not implemented in this pipeline"
  | .error msg =>
      IO.println s!"✗ Parse error: {msg}"
      .ok (.error msg)

-- ============================================================================
-- Error Reporting
-- ============================================================================

/-- Pipeline error with context -/
structure PipelineError where
  stage : String  -- Which stage failed
  message : String
  source : String  -- Original source (for error highlighting)
  line : Nat
  column : Nat
  deriving Repr

/-- Format error for display -/
def formatError (err : PipelineError) : String :=
  s!"{err.stage} error at line {err.line}, column {err.column}:\n{err.message}\n\nSource:\n{err.source}"

-- Executable positive and negative controls live in test/SubstrateTest.lean.
-- They exercise source parsing as well as IR evaluation.

end

end GqlDt.Pipeline
