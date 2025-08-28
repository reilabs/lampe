import Lean

namespace Lampe

-- SYNTAX CATEGORIES ------------------------------------------------------------------------------
-- We start by defining the categories of syntax that can occur in the parse tree. These are generic
-- and make no description of what content is allowable for each; in other words they are just
-- distinct categories of syntax.

declare_syntax_cat noir_const_num
declare_syntax_cat noir_expr
declare_syntax_cat noir_func_param
declare_syntax_cat noir_funcref
declare_syntax_cat noir_gen_def
declare_syntax_cat noir_gen_val
declare_syntax_cat noir_ident
declare_syntax_cat noir_kind
declare_syntax_cat noir_lam_param
declare_syntax_cat noir_lambda
declare_syntax_cat noir_lval
declare_syntax_cat noir_pat
declare_syntax_cat noir_top_level
declare_syntax_cat noir_type

-- COMMON DEFINITIONS -----------------------------------------------------------------------------
-- Common definitions that can be used across multiple syntax definitions.

syntax noir_arrow := "->" <|> "→"

-- GLOBAL DEFINITIONS -----------------------------------------------------------------------------
-- These include functions, traits, trait implementations, and globals, as well as aliases.

syntax noir_alias := noir_ident "<" noir_gen_def,* ">" ":=" noir_type ";" -- A type alias

syntax noir_type_def := "<" noir_gen_def,* ">" "{"
  sepBy(noir_type, ",", ",", allowTrailingSep) "}" -- A type/struct definition

syntax noir_trait_method := "method" noir_ident "<" noir_gen_def,* ">"
  "(" noir_type,* ")" noir_arrow noir_type

syntax noir_trait_def := noir_ident "<" noir_gen_def,* ">" "[" noir_gen_def,* "]" ":="
  "{" sepBy(noir_trait_method, ";", ";", allowTrailingSep) "}" -- A trait definition

syntax noir_fn_def := noir_ident "<" noir_gen_def,* ">"
  "(" noir_func_param,* ")" noir_arrow noir_type ":=" noir_expr -- A function definition.

syntax noir_where_clause := noir_type ":" noir_ident "<" noir_gen_val,* ">" -- A trait where clause.

syntax noir_trait_impl_method := "noir_def" noir_fn_def -- A method in a trait implementation.

syntax noir_trait_impl := "<" noir_gen_def,* ">" noir_ident "<" noir_gen_val,* ">"
  "for" noir_type "where" "[" noir_where_clause,* "]" ":="
  "{" sepBy((noir_trait_impl_method), ";", ";", allowTrailingSep) "}" -- A noir trait implementation

-- IDENTIFIERS ------------------------------------------------------------------------------------

syntax "_" : noir_ident -- An ignored identifier.
syntax "from" : noir_ident -- The 'from' special form.
syntax ident : noir_ident -- Bare identifiers.
syntax ident "::" noir_ident : noir_ident -- Path identifiers.

-- TYPES ------------------------------------------------------------------------------------------
-- This is the language of terms that are syntactically allowable in place of a `noir_type`.

syntax ident : noir_type -- Identifiers can refer directly to types by name.
syntax "String<" noir_gen_val ">" : noir_type -- The type of strings of a given length.
syntax "FmtString<" noir_gen_val "," noir_gen_val ">" : noir_type -- Format strings of a given length and type.
syntax noir_ident "<" noir_gen_val,* ">" : noir_type -- Data types (struct-like, incl. array, tuple, slice).
syntax "&" noir_type : noir_type -- References, both mutable and immutable.
syntax "λ(" noir_type,* ")" ppSpace noir_arrow ppSpace noir_type : noir_type -- Function types.
syntax "_" : noir_type -- Placeholder type.
syntax "@" noir_ident "<" noir_gen_val,* ">" : noir_type -- Type aliases.

-- KINDS ------------------------------------------------------------------------------------------
-- This provides the language of kinds.

syntax "Type" : noir_kind -- Make the reserved identifier valid as a kind.
syntax ident : noir_kind -- Kinds in general

-- GENERIC DEFS -----------------------------------------------------------------------------------
-- This is the language of terms that are syntactically allowable where a generic is being defined.
-- In the extractor these are termed as "type patterns". The extractor will always output kinds for
-- generic definitions.

syntax ident ":" noir_kind : noir_gen_def -- Generics definition with kind annotation.

-- GENERIC VALUES ---------------------------------------------------------------------------------
-- This is the language of terms that are allowable where a generic is being provided. This includes
-- identifiers, and type-level arithmetic expressions.

syntax noir_type : noir_gen_val -- Types.
syntax noir_const_num ":" noir_kind : noir_gen_val -- Kind-annotated type-level numbers.

-- TYPE ARITHMETIC --------------------------------------------------------------------------------
-- The language of arithmetic that can be performed on type-level numbers. Note that the extractor
-- will always generate parentheses around operations even if they are otherwise unambiguous due to
-- precedence.

syntax num : noir_const_num -- Bare type-level numeric literals.
syntax ident : noir_const_num -- Type level number variables (generics).
syntax "(" noir_const_num ")" : noir_const_num -- Parentheses for precedence.
syntax noir_const_num "+" noir_const_num : noir_const_num -- Type-level addition
syntax noir_const_num "-" noir_const_num : noir_const_num -- Type-level subtraction
syntax noir_const_num "*" noir_const_num : noir_const_num -- Type-level multiplication
syntax noir_const_num "/" noir_const_num : noir_const_num -- Type-level division
syntax noir_const_num "%" noir_const_num : noir_const_num -- Type-level modulo

-- FUNCTION PARAMETERS ----------------------------------------------------------------------------
-- These are not lambda parameters, which accept a much broader pattern language.

syntax ident ppSpace ":" ppSpace noir_type : noir_func_param -- Bare function parameters
syntax "mut" ident ":" noir_type : noir_func_param -- Mutable function parameters.
syntax "_" ":" noir_type : noir_func_param -- An ignored function parameter.

-- LITERALS ---------------------------------------------------------------------------------------
-- Literal instances of Noir types. Note that we explicitly use constructor functions for structs,
-- slices, arrays, and format strings, and hence they are not included here.

syntax ("-" noWs)? num ppSpace ":" ppSpace noir_type : noir_expr -- Numeric literals.
syntax str : noir_expr -- String literals.
syntax "#_true" : noir_expr -- Boolean true.
syntax "#_false" : noir_expr -- Boolean false.
syntax "#_unit" : noir_expr -- Unit literals.

-- EXPRESSIONS ------------------------------------------------------------------------------------
-- The majority of the remaining non-literal expressions. We merge statements and expressions here,
-- as this is easier to represent in Lean. Recall that member access is handled by a `getMember`
-- builtin and hence no longer has a syntactic representation.

-- Blocks allow us to structure code.
syntax "{" sepBy(ppLine noir_expr, ";", ";", allowTrailingSep) ppLine ppDedent("}") : noir_expr -- Blocks.

-- These are the expression-like expressions.
syntax "#_skip" : noir_expr -- Simple skips.
syntax noir_ident : noir_expr -- Bare identifiers.
syntax "if" ppSpace noir_expr ppSpace "then" ppSpace noir_expr ppSpace ("else" ppSpace noir_expr)? : noir_expr -- If-then-(else).
syntax noir_funcref "(" noir_expr,* ")" : noir_expr -- Function call
syntax noir_lambda : noir_expr -- Lambdas are expressions.
syntax noir_funcref : noir_expr -- Bare function references without calls are also expressions.
syntax noir_expr "." num : noir_expr -- Field access
syntax "uConst!(" ident ppSpace ":" ppSpace noir_kind ")" : noir_expr -- UInt const generics to values.
syntax "fConst!(" ident ppSpace ":" ppSpace noir_kind ")" : noir_expr -- Field const generics to values.
syntax "(" noir_expr ")" : noir_expr -- Parenthesized expressions.
syntax "sorry" : noir_expr -- Sorry, useful for debugging

-- These are the statement-like expressions.
syntax noir_lval ppSpace "=" ppSpace noir_expr : noir_expr -- Assignments.
syntax "let" ppSpace noir_pat ppSpace "=" ppSpace noir_expr : noir_expr -- Let bindings.
syntax "for" ppSpace noir_ident ppSpace "in" ppSpace noir_expr ppSpace ".." ppSpace noir_expr ppSpace "do" ppSpace noir_expr : noir_expr  -- Bounded for loops.

-- FUNCTION REFERENCES ----------------------------------------------------------------------------
-- These are the different kinds of things that can be called.

syntax "(" noir_ident ppSpace "as" ppSpace noir_type ")" : noir_funcref -- An identifier call ref.
syntax "(" noir_lambda ")" : noir_funcref -- A lambda is callable.
syntax "(" "#_" ident ppSpace "returning" ppSpace noir_type ")" : noir_funcref -- A builtin name is callable.
syntax "(" noir_ident "<" noir_gen_val,* ">" ppSpace "as" ppSpace noir_type ")" : noir_funcref -- A function reference is callable.
syntax "(" "(" noir_type ppSpace "as" ppSpace noir_ident "<" noir_gen_val,* ">" ")"
  "::" noir_ident "<" noir_gen_val,* ">" ppSpace "as" ppSpace noir_type ")" : noir_funcref -- A trait method reference is also callable.

-- LAMBDAS ----------------------------------------------------------------------------------------

syntax "fn" "(" noir_pat,* ")" ppSpace ":" ppSpace noir_type ppSpace ":=" ppSpace noir_expr : noir_lambda -- Lambda expressions.

-- PATTERNS ---------------------------------------------------------------------------------------
-- These are used in let bindings and lambda parameters to destructure things.

syntax "(" noir_ident ppSpace ":" ppSpace noir_type ")" : noir_pat -- A bare identifier.
syntax "mut" ppSpace "(" noir_ident ppSpace ":" ppSpace noir_type ")" : noir_pat -- A mutable identifier.
syntax "(" noir_pat,* ")" : noir_pat -- A tuple pattern stands in for both tuples and structs.

-- L-VALUES ---------------------------------------------------------------------------------------
-- These are the things that can appear on the left side of an assignment. They get desugared to
-- lenses, but we provide syntax for ease of reading.

syntax ident : noir_lval -- A bare identifier.
syntax "(" noir_lval "." num ppSpace ":" ppSpace noir_type ")" : noir_lval -- A field access with numeric field selection.
syntax "(" noir_lval "[" noir_expr "]" ":" noir_type ")" : noir_lval -- An array access.
syntax "(" noir_lval "[[" noir_expr "]]" ":" noir_type ")" : noir_lval -- A slice access
syntax "(" "*" noir_expr ":" noir_type ")" : noir_lval -- A dereferenced value.

-- DEBUG ------------------------------------------------------------------------------------------
-- The following are splices that can be used to write Lean code directly in place of other kinds of
-- syntax, or to evaluate the DSL syntax in place.

syntax "${" term "}" : noir_expr -- Lean code in place of an expression.
syntax "${" term "}" : noir_type -- Lean code in place of a type.
