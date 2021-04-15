%{
  open Back
  open Syntax
%}

%token SINGLE_ARROW
%token DOUBLE_ARROW
%token NOTHING
%token UNDEFINED
%token UNIT
%token <Back.Syntax.label> LABEL
%token LPAREN RPAREN
%token DECLARE
%token DEFINE
%token END
%token EOF

%start file
%type <Back.Syntax.prog> file

%start input
%type <Back.Syntax.stmt> input

%%

file:
  | p = prog
    { p }

input:
  | s = stmt EOF
    { s }

expr:
  | e = expr_abs
    { e }
  | e = expr_redex
    { e }
  | e = expr_value
    { e }

expr_abs:
  | x = LABEL DOUBLE_ARROW s = stmt
    { expr_abs x s }

expr_redex:
  | f = expr_func a = expr_value
    { expr_app f a }

expr_func:
  | x = LABEL
    { expr_var x }
  | LPAREN e = expr_group RPAREN
    { e }

expr_value:
  | e = expr_simple
    { e }
  | LPAREN e = expr_group RPAREN
    { e }

expr_simple:
  | UNDEFINED
    { expr_undefined }
  | UNIT
    { expr_unit }
  | x = LABEL
    { expr_var x }

expr_group:
  | e = expr_value DECLARE p = poly
    { expr_anno e p }
  | e = expr_abs
    { e }
  | e = expr_redex
    { e }

stmt:
  | x = LABEL DECLARE t = poly END s = stmt
    { stmt_decl x t s }
  | x = LABEL DEFINE e = expr END s = stmt
    { stmt_defn x e s }
  | e = expr
    { stmt_expr e }

prog:
  | x = LABEL DECLARE t = poly END p = prog
    { prog_decl x t p }
  | x = LABEL DEFINE e = expr END p = prog
    { prog_defn x e p }
  | EOF
    { prog_end }

poly:
  | s = poly_simple SINGLE_ARROW t = poly
    { poly_arrow s t }
  | x = LABEL DOUBLE_ARROW t = poly
    { poly_forall x t }
  | t = poly_simple
    { t }

poly_simple:
  | NOTHING
    { poly_nothing }
  | UNIT
    { poly_unit }
  | x = LABEL
    { poly_param x }
  | LPAREN t = poly RPAREN
    { t }
