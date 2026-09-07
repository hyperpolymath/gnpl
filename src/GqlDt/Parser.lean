-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (@hyperpolymath)
--
-- Parser for GQL-DT/GQL
-- Parses tokens into typed AST

import GqlDt.Lexer
import GqlDt.AST
import GqlDt.TypeInference
import GqlDt.IR
import GqlDt.Types
import GqlDt.Types.NonEmptyString
import GqlDt.Types.BoundedNat
import GqlDt.Types.Confidence
import GqlDt.Provenance

namespace GqlDt.Parser

open Lexer AST TypeInference IR Types

/-!
# GQL-DT/GQL Parser

Parses tokenized source into typed AST.

**Two parsing modes:**
1. **GQL-DT** - Explicit types, proofs required
2. **GQL** - Type inference, runtime validation

**Architecture:**
```
Tokens (from Lexer)
    ↓
Parser Combinators
    ↓
Typed AST (with or without explicit types)
    ↓
Type Checker (verify proofs)
    ↓
Typed IR (ready for execution)
```
-/

-- Universe declaration for polymorphic Parser
universe u v

-- ============================================================================
-- Parser State
-- ============================================================================

/-- Parser state: current position in token stream -/
structure ParserState where
  tokens : List Token
  position : Nat
  deriving Repr

/-- Parser result (universe-polymorphic) -/
inductive ParseResult (α : Type u) where
  | ok : α → ParserState → ParseResult α
  | error : String → ParserState → ParseResult α

-- Manual Repr instance (deriving doesn't work with universe polymorphism)
instance {α : Type u} : Repr (ParseResult α) where
  reprPrec
    | .ok _ _, _ => "ParseResult.ok ..."
    | .error msg _, _ => s!"ParseResult.error \"{msg}\""

/-- Parser monad (supports Type 1 for dependent types) -/
def Parser (α : Type u) := ParserState → ParseResult α

instance : Monad Parser where
  pure x := fun s => .ok x s
  bind p f := fun s =>
    match p s with
    | .ok x s' => f x s'
    | .error msg s' => .error msg s'

/-- Bind across universes: typed projections live in Type 1, tokens in Type.
The ordinary Monad instance is homogeneous and cannot perform this bind. -/
def bindAcross {α : Type u} {β : Type v} (p : Parser α) (f : α → Parser β) : Parser β := fun s =>
  match p s with
  | .ok x s' => f x s'
  | .error msg s' => .error msg s'

/-- Fail with error message -/
def fail {α : Type u} (msg : String) : Parser α :=
  fun s => .error msg s

-- ============================================================================
-- Basic Parser Combinators
-- ============================================================================

/-- Get current token without consuming -/
def peek : Parser (Option Token) := fun s =>
  match s.tokens.get? s.position with
  | some tok => .ok (some tok) s
  | none => .ok none s

/-- Consume current token -/
def advance : Parser Unit := fun s =>
  .ok () { s with position := s.position + 1 }

/-- Get current token and consume -/
def next : Parser (Option Token) := fun s =>
  match s.tokens.get? s.position with
  | some tok => .ok (some tok) { s with position := s.position + 1 }
  | none => .ok none s

/-- Expect specific token type -/
def expect (tokType : TokenType) : Parser Token := fun s =>
  match s.tokens.get? s.position with
  | some tok =>
      if tok.type == tokType then
        .ok tok { s with position := s.position + 1 }
      else
        .error s!"Expected {tokType}, got {tok.type}" s
  | none =>
      .error s!"Expected {tokType}, got EOF" s

/-- Expect identifier and return its name -/
def expectIdentifier : Parser String := fun s =>
  match s.tokens.get? s.position with
  | some tok =>
      match tok.type with
      | .identifier name => .ok name { s with position := s.position + 1 }
      | _ => .error s!"Expected identifier, got {tok.type}" s
  | none => .error "Expected identifier, got EOF" s

/-- Parse optional element -/
def optional {α : Type u} (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok x s' => .ok (some x) s'
  | .error msg s' =>
      if s'.position > s.position then .error msg s' else .ok none s

/-- Total repetition. Each successful step must consume input; a failure after
consumption is committed. Fuel is bounded by the initial token count. -/
private def manyFuel {α : Type u} (p : Parser α) : Nat → Parser (List α)
  | 0 => fail "Repetition exceeded the token budget"
  | fuel + 1 => fun s =>
      match p s with
      | .error msg s' =>
          if s'.position > s.position then .error msg s' else .ok [] s
      | .ok x s' =>
          if s'.position ≤ s.position || s'.position > s.tokens.length then
            .error "Repeated parser must consume input within the token stream" s'
          else
            match manyFuel p fuel s' with
            | .ok xs s'' => .ok (x :: xs) s''
            | .error msg s'' => .error msg s''

def many {α : Type u} (p : Parser α) : Parser (List α) := fun s =>
  manyFuel p (s.tokens.length + 1) s

def many1 {α : Type u} (p : Parser α) : Parser (List α) := do
  let xs ← many p
  if xs.isEmpty then fail "Expected at least one element" else pure xs

def sepBy {α : Type u} {β : Type v} (p : Parser α) (sep : Parser β) : Parser (List α) := do
  match ← optional p with
  | none => pure []
  | some x =>
      let xs ← many (bindAcross sep (fun _ => p))
      pure (x :: xs)

-- ============================================================================
-- Expression Parsing
-- ============================================================================

/-- Parse literal value -/
def parseLiteral : Parser InferredType := fun s =>
  match s.tokens.get? s.position with
  | some tok =>
      match tok.type with
      | .litNat n => .ok (.nat n) { s with position := s.position + 1 }
      | .litInt i => .ok (.int i) { s with position := s.position + 1 }
      | .litString str => .ok (.string str) { s with position := s.position + 1 }
      | .litBool b => .ok (.bool b) { s with position := s.position + 1 }
      | .litFloat f => .ok (.float f) { s with position := s.position + 1 }
      | _ => .error s!"Expected literal, got {tok.type}" s
  | none => .error "Expected literal, got EOF" s

-- ============================================================================
-- Type Expression Parsing
-- ============================================================================

/-- Parse type expression -/
def parseTypeExpr : Parser TypeExpr := fun s =>
  match s.tokens.get? s.position with
  | some tok =>
      match tok.type with
      | .kwNat => .ok .nat { s with position := s.position + 1 }
      | .kwInt => .ok .int { s with position := s.position + 1 }
      | .kwString => .ok .string { s with position := s.position + 1 }
      | .kwBool => .ok .bool { s with position := s.position + 1 }
      | .kwNonEmptyString => .ok .nonEmptyString { s with position := s.position + 1 }
      | .kwConfidence => .ok .confidence { s with position := s.position + 1 }

      | .kwBoundedNat =>
          -- BoundedNat min max
          let s1 := { s with position := s.position + 1 }
          match s1.tokens.get? s1.position with
          | some minTok =>
              match minTok.type with
              | .litNat min =>
                  let s2 := { s1 with position := s1.position + 1 }
                  match s2.tokens.get? s2.position with
                  | some maxTok =>
                      match maxTok.type with
                      | .litNat max =>
                          .ok (.boundedNat min max) { s2 with position := s2.position + 1 }
                      | _ => .error "Expected max value for BoundedNat" s2
                  | none => .error "Expected max value for BoundedNat" s2
              | _ => .error "Expected min value for BoundedNat" s1
          | none => .error "Expected min value for BoundedNat" s1

      | .kwPromptScores => .ok .promptScores { s with position := s.position + 1 }

      | _ => .error s!"Expected type expression, got {tok.type}" s
  | none => .error "Expected type expression, got EOF" s

-- ============================================================================
-- INSERT Parsing
-- ============================================================================

/-- Parse column list: (col1, col2, col3) -/
def parseColumnList : Parser (List String) := do
  let _ ← expect .leftParen
  let cols ← sepBy expectIdentifier (do let _ ← expect .comma; return ())
  let _ ← expect .rightParen
  return cols

/-- Parse column with optional type annotation: name or name : Type -/
def parseColumnWithType : Parser (String × Option TypeExpr) := do
  let name ← expectIdentifier
  let typeAnnot ← optional (do
    let tok ← peek
    match tok with
    | some t =>
        if t.type == .opColon || t.type == .opDoubleColon then advance
        else fail "Expected type annotation"
    | none => fail "Expected type annotation"
    parseTypeExpr)
  return (name, typeAnnot)

/-- Parse typed column list: (col1 : Type1, col2 : Type2) -/
def parseTypedColumnList : Parser (List (String × TypeExpr)) := do
  let _ ← expect .leftParen
  let cols ← sepBy (do
    let name ← expectIdentifier
    let tok ← next
    match tok with
    | some t => if t.type == .opColon || t.type == .opDoubleColon then pure () else fail "Expected type annotation"
    | none => fail "Expected type annotation"
    let ty ← parseTypeExpr
    return (name, ty)) (do let _ ← expect .comma; return ())
  let _ ← expect .rightParen
  return cols

/-- Parse VALUES clause -/
def parseValues : Parser (List InferredType) := do
  let _ ← expect .kwValues
  let _ ← expect .leftParen
  let vals ← sepBy parseLiteral (do let _ ← expect .comma; return ())
  let _ ← expect .rightParen
  return vals

/-- Parse RATIONALE clause -/
def parseRationale : Parser String := fun s =>
  match expect .kwRationale s with
  | .ok _ s' =>
      match s'.tokens.get? s'.position with
      | some tok =>
          match tok.type with
          | .litString str => .ok str { s' with position := s'.position + 1 }
          | _ => .error "Expected string for RATIONALE" s'
      | none => .error "Expected RATIONALE value" s'
  | .error msg s' => .error msg s'

/-- The concrete example schema; production callers supply their schema. -/
def evidenceSchema : Schema := GqlDt.TypeSafe.evidenceSchema

/-- Parse INSERT statement (GQL - no types) -/
def parseInsertGQL (schema : Schema := evidenceSchema) : Parser InferredInsert := do
  let _ ← expect .kwInsert
  let _ ← expect .kwInto
  let table ← expectIdentifier
  let columns ← parseColumnList
  let values ← parseValues
  let rationale ← parseRationale
  let _ ← optional (expect .semicolon)

  -- Type inference happens here
  match inferInsert schema table columns values rationale with
  | .ok inferred => return inferred
  | .error msg => fail msg

/-- Parse INSERT statement (GQL-DT - explicit types) -/
def parseInsertGQLdt (schema : Schema := evidenceSchema) : Parser InferredInsert := do
  let _ ← expect .kwInsert
  let _ ← expect .kwInto
  let table ← expectIdentifier
  let typedColumns ← parseTypedColumnList
  let values ← parseValues
  let rationale ← parseRationale
  let _ ← optional (expect .semicolon)

  -- Extract columns and types
  let columns := typedColumns.map (·.1)
  let expectedTypes := typedColumns.map (·.2)

  match inferInsert schema table columns values rationale with
  | .ok inferred =>
      if (expectedTypes.zip (inferred.inferredValues.map (·.inferredType))).all
          (fun (expected, actual) => expected == actual) then
        return inferred
      else fail "Explicit column types do not match the schema"
  | .error msg => fail msg

-- ============================================================================
-- Statement Types (must be defined before parsing functions)
-- ============================================================================

/-- Parser-level UPDATE statement (simpler than AST.UpdateStmt) -/
structure ParsedUpdate where
  table : String
  assignments : List Assignment
  where_ : Option WhereClause
  rationale : Provenance.Rationale
  deriving Repr

/-- Parser-level DELETE statement (simpler than AST.DeleteStmt) -/
structure ParsedDelete where
  table : String
  where_ : WhereClause
  rationale : Provenance.Rationale
  deriving Repr

/-- Parser-level SELECT statement (simpler than AST.SelectStmt) -/
structure ParsedSelect where
  selectList : SelectList
  from_ : FromClause
  where_ : Option WhereClause
  orderBy : Option OrderByClause
  limit : Option Nat
  deriving Repr

/-- Statement type for parsing -/
inductive Statement where
  | insertGQL : InferredInsert → Statement
  | insertGQLdt : InferredInsert → Statement
  | select : ParsedSelect → Statement
  | update : ParsedUpdate → Statement
  | delete : ParsedDelete → Statement
  deriving Repr

-- ============================================================================
-- SELECT Parsing
-- ============================================================================

/-- Parse the supported SELECT projection; richer refinements require a checker. -/
def parseSelectList : Parser SelectList := bindAcross peek fun tokOpt =>
  match tokOpt with
  | some tok =>
      if tok.type == .opStar then
        bindAcross next (fun _ => pure .star)
      else
        bindAcross (sepBy expectIdentifier (expect .comma)) fun cols =>
        if cols.isEmpty then fail "SELECT needs a projection" else pure (.columns cols)
  | none => fail "Expected SELECT projection"

/-- Parse FROM clause -/
def parseFromClause : Parser FromClause := do
  let _ ← expect .kwFrom
  let tables ← sepBy (do
    let name ← expectIdentifier
    let alias ← optional (do
      let _ ← expect .kwAs
      expectIdentifier)
    return { name := name, alias := alias }) (do let _ ← expect .comma; return ())
  return { tables := tables }

/-- Parse comparison operator -/
def parseComparisonOp : Parser String := fun s =>
  match s.tokens.get? s.position with
  | some tok =>
      match tok.type with
      | .opEq => .ok "=" { s with position := s.position + 1 }
      | .opLt => .ok "<" { s with position := s.position + 1 }
      | .opGt => .ok ">" { s with position := s.position + 1 }
      | .opLe => .ok "<=" { s with position := s.position + 1 }
      | .opGe => .ok ">=" { s with position := s.position + 1 }
      | .opNeq => .ok "!=" { s with position := s.position + 1 }
      | _ => .error "Expected comparison operator" s
  | none => .error "Expected comparison operator, got EOF" s

/-- Parse WHERE clause -/
def parseWhereClause : Parser WhereClause := do
  let _ ← expect .kwWhere
  -- Parse simple predicate (column op value)
  let column ← expectIdentifier
  let op ← parseComparisonOp
  let value ← parseLiteral
  return {
    predicate := (column, op, value),  -- Simplified for now
    proof := fun _ => trivial
  }

/-- Parse ORDER BY clause -/
def parseOrderBy : Parser OrderByClause := do
  let _ ← expect .kwOrder
  let _ ← expect .kwBy
  let columns ← sepBy (do
    let col ← expectIdentifier
    let direction ← optional (do
      let tok ← peek
      match tok with
      | some { type := .identifier "ASC", .. } => advance; pure "ASC"
      | some { type := .identifier "DESC", .. } => advance; pure "DESC"
      | _ => fail "Expected ASC or DESC")
    return (col, direction.getD "ASC")
  ) (do let _ ← expect .comma; return ())
  return { columns := columns }

/-- Parse LIMIT clause -/
def parseLimit : Parser Nat := fun s =>
  match expect .kwLimit s with
  | .ok _ s' =>
      match s'.tokens.get? s'.position with
      | some tok =>
          match tok.type with
          | .litNat n => .ok n { s' with position := s'.position + 1 }
          | _ => .error "Expected number for LIMIT" s'
      | none => .error "Expected LIMIT value" s'
  | .error msg s' => .error msg s'

def parseSelect : Parser ParsedSelect :=
  bindAcross (expect .kwSelect) fun _ =>
  bindAcross parseSelectList fun selectList =>
  bindAcross parseFromClause fun from_ =>
  if from_.tables.isEmpty then fail "FROM needs a table" else
    bindAcross (optional parseWhereClause) fun where_ =>
    bindAcross (optional parseOrderBy) fun orderBy =>
    bindAcross (optional parseLimit) fun limit =>
    bindAcross (optional (expect .semicolon)) fun _ =>
    pure { selectList, from_, where_, orderBy, limit }

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Helper: Infer TypeExpr from InferredType -/
private def inferTypeFromLiteral (lit : InferredType) : TypeExpr :=
  match lit with
  | .nat _ => .nat
  | .int _ => .int
  | .string _ => .string
  | .bool _ => .bool
  | .float _ => .float

/-- Helper: Create TypedValue from InferredType -/
private def typedValueFromLiteral (lit : InferredType) : TypedValue (inferTypeFromLiteral lit) :=
  match lit with
  | .nat n => .nat n
  | .int i => .int i
  | .string s => .string s
  | .bool b => .bool b
  | .float f => .float f

-- ============================================================================
-- UPDATE Parsing
-- ============================================================================

/-- Parse UPDATE statement -/
def parseUpdate : Parser ParsedUpdate := do
  let _ ← expect .kwUpdate
  let table ← expectIdentifier
  let _ ← expect .kwSet
  -- Parse assignments (column = value)
  let assignments ← sepBy (do
    let column ← expectIdentifier
    let _ ← expect .opEq
    let value ← parseLiteral
    return (column, value)
  ) (do let _ ← expect .comma; return ())
  let where_ ← optional parseWhereClause
  let rationale ← parseRationale
  let _ ← optional (expect .semicolon)

  -- Validate rationale is non-empty (parsed from source, so check at runtime)
  if h : rationale.length > 0 then
    return {
      table := table,
      assignments := assignments.map fun (col, val) => {
        column := col,
        value := ⟨inferTypeFromLiteral val, typedValueFromLiteral val⟩
      },
      where_ := where_,
      rationale := { text := { val := rationale, nonempty := h } }
    }
  else
    fail "RATIONALE must be a non-empty string"

-- ============================================================================
-- DELETE Parsing
-- ============================================================================

/-- Parse DELETE statement -/
def parseDelete : Parser ParsedDelete := do
  let _ ← expect .kwDelete
  let _ ← expect .kwFrom
  let table ← expectIdentifier
  -- WHERE is MANDATORY for safety
  let where_ ← parseWhereClause
  let rationale ← parseRationale
  let _ ← optional (expect .semicolon)

  -- Validate rationale is non-empty (parsed from source, so check at runtime)
  if h : rationale.length > 0 then
    return {
      table := table,
      where_ := where_,
      rationale := { text := { val := rationale, nonempty := h } }
    }
  else
    fail "RATIONALE must be a non-empty string"

-- ============================================================================
-- Top-Level Statement Parsing
-- ============================================================================

def parseStatement (schema : Schema := evidenceSchema) : Parser Statement := fun s =>
  match s.tokens.get? s.position with
  | none => .error "Expected statement" s
  | some tok =>
      match tok.type with
      | .kwSelect => (bindAcross parseSelect (fun x => pure (Statement.select x))) s
      | .kwUpdate => (bindAcross parseUpdate (fun x => pure (Statement.update x))) s
      | .kwDelete => (bindAcross parseDelete (fun x => pure (Statement.delete x))) s
      | .kwInsert =>
          let columns := (s.tokens.drop s.position).takeWhile (·.type != .rightParen)
          if columns.any (fun t => t.type == .opColon || t.type == .opDoubleColon) then
            (bindAcross (parseInsertGQLdt schema) (fun x => pure (Statement.insertGQLdt x))) s
          else (bindAcross (parseInsertGQL schema) (fun x => pure (Statement.insertGQL x))) s
      | _ => .error "Unsupported statement" s

/-- Consume exactly one statement and EOF. Never discard a trailing clause or
second statement. Callers that need batches must handle each statement explicitly. -/
def parseTokensComplete (tokens : List Token) (schema : Schema := evidenceSchema)
    : Except String (List Statement) :=
  match parseStatement schema { tokens, position := 0 } with
  | .error msg _ => .error msg
  | .ok stmt s =>
      match s.tokens.drop s.position with
      | [] => .ok [stmt]
      | [tok] => if tok.type == .eof then .ok [stmt] else .error "Unexpected trailing input"
      | _ => .error "Unexpected trailing input or multiple statements"

-- ============================================================================
-- Public API
-- ============================================================================

/-- Parse source string to statements -/
def parse (source : String) (schema : Schema := evidenceSchema) : Except String (List Statement) :=
  match tokenize source with
  | .error msg => .error msg
  | .ok tokens => parseTokensComplete tokens schema

/-- Parse a selection into the private IR. Mutation lowering needs a schema. -/
def parseToIR (source : String) (permissions : PermissionMetadata) : Except String IR := do
  match ← parse source with
  | [.select stmt] => pure (.select {
      selectList := stmt.selectList, from_ := stmt.from_, where_ := stmt.where_,
      orderBy := stmt.orderBy, limit := stmt.limit, returning := none, permissions })
  | _ => .error "Mutation lowering requires a schema: use Pipeline.runPipeline"

end GqlDt.Parser
