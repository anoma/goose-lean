import Lean
open Lean Parser

/-!
# Gusto Syntax Declarations

This file defines the syntax categories and grammar for the Gusto DSL,
a Python-like subset based on the official PEG grammar,
available at https://docs.python.org/3/reference/grammar.html.

## Supported Features

- Basic expressions (arithmetic, comparisons, calls)
- Simple statements (assignment, return, pass, expression statements)
- Compound statements (class definitions, function definitions, if statements)
- Type annotations
- Object-oriented programming constructs

Not python-related:
- Decorators for constructors, destructors, methods, multimethods
- context/ecosystem definitions
-/
namespace Gusto

/-!
## Syntax Categories
-/

declare_syntax_cat gusto_arg
declare_syntax_cat gusto_atom
declare_syntax_cat gusto_block
declare_syntax_cat gusto_block_stmt
declare_syntax_cat gusto_class_body
declare_syntax_cat gusto_class_member
declare_syntax_cat gusto_comp
declare_syntax_cat gusto_compound_stmt
declare_syntax_cat gusto_decorator
declare_syntax_cat gusto_expr
declare_syntax_cat gusto_factor
declare_syntax_cat gusto_param
declare_syntax_cat gusto_power
declare_syntax_cat gusto_primary
declare_syntax_cat gusto_return_type
declare_syntax_cat gusto_simple_stmt
declare_syntax_cat gusto_statement
declare_syntax_cat gusto_sum
declare_syntax_cat gusto_target
declare_syntax_cat gusto_term
declare_syntax_cat gusto_type
declare_syntax_cat gusto_type_annotation

/-!
## Atoms (lowest level expressions)
-/

-- atom:
--     | NAME
--     | NUMBER
--     | STRING+
--     | 'True'
--     | 'False'
--     | 'None'
--     | group
--     | tuple
syntax ident : gusto_atom
syntax num : gusto_atom
syntax str : gusto_atom
syntax "True" : gusto_atom
syntax "False" : gusto_atom
syntax "None" : gusto_atom

-- group:
--     | '(' expression ')'
syntax "(" gusto_expr ")" : gusto_atom

-- tuple:
--     | '(' expression ',' expression,* ')'
syntax "(" gusto_expr "," gusto_expr,* ")" : gusto_atom

/-!
## Primary (attribute access, calls, atoms)
-/

-- primary: atom
syntax gusto_atom : gusto_primary

-- primary:
--     | primary '.' NAME
syntax gusto_primary "." ident : gusto_primary

-- primary:
--     | primary '(' [arguments] ')'
-- arguments:
--     | args [',']
-- args:
--     | ','.expression+
--     | ','.keyword_arg+
-- keyword_arg:
--     | NAME '=' expression
syntax gusto_expr : gusto_arg
syntax ident "=" gusto_expr : gusto_arg

syntax gusto_primary "(" gusto_arg,* ")" : gusto_primary

/-!
## Expressions (operator precedence hierarchy)
-/

-- power:
--     | primary ['**' factor]
syntax gusto_primary : gusto_power
syntax gusto_primary "**" gusto_factor : gusto_power

-- factor:
--     | '+' factor
--     | '-' factor
--     | power
syntax gusto_power : gusto_factor
syntax "+" gusto_factor : gusto_factor
syntax "-" gusto_factor : gusto_factor

-- term:
--     | term '*' factor
--     | term '/' factor
--     | term '//' factor
--     | term '%' factor
--     | factor
syntax gusto_factor : gusto_term
syntax gusto_term "*" gusto_factor : gusto_term
syntax gusto_term "/" gusto_factor : gusto_term
syntax gusto_term "//" gusto_factor : gusto_term
syntax gusto_term "%" gusto_factor : gusto_term

-- sum:
--     | sum '+' term
--     | sum '-' term
--     | term
syntax gusto_term : gusto_sum
syntax gusto_sum "+" gusto_term : gusto_sum
syntax gusto_sum "-" gusto_term : gusto_sum

-- comparison:
--     | sum (comp_op sum)*
-- comp_op:
--     | '=='
--     | '!='
--     | '<'
--     | '>'
--     | '<='
--     | '>='
syntax gusto_sum : gusto_comp
syntax gusto_comp "==" gusto_sum : gusto_comp
syntax gusto_comp "!=" gusto_sum : gusto_comp
syntax gusto_comp "<" gusto_sum : gusto_comp
syntax gusto_comp ">" gusto_sum : gusto_comp
syntax gusto_comp "<=" gusto_sum : gusto_comp
syntax gusto_comp ">=" gusto_sum : gusto_comp

-- expression:
--     | comparison
syntax gusto_comp : gusto_expr

/-!
## Assignment Targets
-/

-- target:
--     | NAME
--     | primary '.' NAME
--     | '(' target ')'
syntax ident : gusto_target
syntax gusto_primary "." ident : gusto_target
syntax "(" gusto_target ")" : gusto_target

/-!
## Simple Statements
-/

-- expr_stmt:
--     | expression
syntax gusto_expr : gusto_simple_stmt

-- return_stmt:
--     | 'return' [expression]
syntax "return" : gusto_simple_stmt
syntax "return" gusto_expr : gusto_simple_stmt

-- pass_stmt:
--     | 'pass'
syntax "pass" : gusto_simple_stmt

-- destroy_stmt:
--     | 'destroy' expression
--     | 'del' expression  -- Python-style alias
syntax "destroy" gusto_expr : gusto_simple_stmt
syntax "del" gusto_expr : gusto_simple_stmt

-- assignment:
--     | target '=' expression
-- NOTE: another form to consider is
--     | target ':=' expression
--     | target '<-' expression
syntax gusto_target "=" gusto_expr : gusto_simple_stmt

/-!
## Decorators and Type Annotations
-/

-- decorator:
--     | '@' NAME
--     | '@' NAME '(' [arguments] ')'
syntax "@" ident : gusto_decorator
syntax "@" ident "(" gusto_expr,* ")" : gusto_decorator

-- type_annotation:
--     | NAME ':' NAME
syntax ident ":" ident : gusto_type_annotation

/-!
## Type Syntax
-/

-- type:
--     | NAME
syntax ident : gusto_type

-- return_type:
--     | type
--     | '(' type ',' type,* ')'  -- tuple return type
-- NOTE: we probably want to support multiple return types in the future
syntax gusto_type : gusto_return_type
syntax "(" gusto_type "," gusto_type,* ")" : gusto_return_type

/-!
## Parameters for function definitions
-/

-- param:
--     | NAME ['=' expression]
--     | NAME ':' type ['=' expression]
syntax ident : gusto_param
syntax ident "=" gusto_expr : gusto_param
syntax ident ":" gusto_type : gusto_param
syntax ident ":" gusto_type "=" gusto_expr : gusto_param

-- params:
--     | param_list
-- param_list:
--     | param (',' param)* [',']
-- This is a named parser, not a syntax category
syntax gusto_param_list := gusto_param,*

/-!
## Blocks
-/

-- block:
--     | NEWLINE INDENT gusto_statement+ DEDENT
-- Blocks should only contain simple statements
-- and if statements, NOT function/class definitions
-- This prevents method bodies from consuming subsequent class members
syntax gusto_simple_stmt : gusto_block_stmt
syntax "if" gusto_expr ":" ppLine gusto_block : gusto_block_stmt
syntax "if" gusto_expr ":" ppLine gusto_block ppLine "else" ":" ppLine gusto_block : gusto_block_stmt

syntax ppLine ppDedent(ppLine) colGt gusto_block_stmt+ : gusto_block

/-!
## Compound Statements
-/

-- function_def:
--     | decorator* 'def' NAME '(' [params] ')' ['->' return_type] ':' block
syntax gusto_decorator* "def" ident "(" gusto_param_list ")" ":" gusto_block : gusto_compound_stmt
syntax gusto_decorator* "def" ident "(" gusto_param_list ")" "->" gusto_return_type ":" gusto_block : gusto_compound_stmt

-- field_decl:
--     | NAME ':' NAME
-- Fields must appear before any function definitions
declare_syntax_cat gusto_function_def

syntax gusto_decorator* "def" ident "(" gusto_param_list ")" ":" gusto_block : gusto_function_def
syntax gusto_decorator* "def" ident "(" gusto_param_list ")" "->" gusto_return_type ":" gusto_block : gusto_function_def

-- class_body:
--     | NEWLINE INDENT [field_decl+] [function_def+] DEDENT
-- Fields must come before functions to match Python dataclass conventions.
-- Both sections are optional, but fields (if present) must appear first.
-- We require a ppLine before each member.
syntax (ppLine gusto_type_annotation)* (ppLine gusto_function_def)* : gusto_class_body

-- class_def:
--     | 'class' NAME ['(' [arguments] ')'] ':' class_body
syntax "class" ident ":" ppLine gusto_class_body : gusto_compound_stmt
syntax "class" ident "(" gusto_expr,* ")" ":" ppLine gusto_class_body : gusto_compound_stmt

-- if_stmt:
--     | 'if' expression ':' block ['else' ':' block]
syntax "if" gusto_expr ":" ppLine gusto_block : gusto_compound_stmt
syntax "if" gusto_expr ":" ppLine gusto_block ppLine "else" ":" ppLine gusto_block : gusto_compound_stmt

/-!
## Statements (top level)
-/

-- statement:
--     | compound_stmt
--     | simple_stmts
--
-- simple_stmts:
--     | simple_stmt NEWLINE
--     | ';'.simple_stmt+ [';'] NEWLINE
syntax gusto_compound_stmt : gusto_statement
syntax gusto_simple_stmt : gusto_statement

-- semicolon-separated simple statements
syntax gusto_simple_stmt ";" gusto_simple_stmt : gusto_statement
syntax gusto_statement ";" gusto_simple_stmt : gusto_statement

/-!
## Multi-method Definitions (ecosystem members)

Multi-methods are top-level functions in a gusto module that can operate on
multiple objects. They are automatically part of the ecosystem.
-/

-- Multi-method syntax (at module level, outside classes):
--     | decorator* 'def' NAME '(' [params] ')' ':' block
--     | decorator* 'def' NAME '(' [params] ')' '->' return_type ':' block
syntax gusto_decorator* "def" ident "(" gusto_param_list ")" ":" gusto_block : gusto_statement
syntax gusto_decorator* "def" ident "(" gusto_param_list ")" "->" gusto_return_type ":" gusto_block : gusto_statement

/-!
## Integration with Lean's term system (WIP)
-/

-- Block-form gusto command (higher priority - defined first)
-- Syntax: gusto ModuleName
--           <gusto statements>
--         end [ModuleName]
declare_syntax_cat gusto_module_body
syntax (ppLine gusto_statement)+ : gusto_module_body

-- Named module form
syntax (name := gustoModule)
  "gusto" ppSpace ident ppLine
  gusto_module_body
  ppLine "end" (ppSpace ident)? : command

-- These are useful for testing and debugging.
syntax "gusto(" gusto_expr ")" : term
syntax "gusto_block(" gusto_statement+ ")" : term

end Gusto
