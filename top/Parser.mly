%{
  open Bin
  open Syntax
%}

%token SINGLE_ARROW
%token DOUBLE_ARROW
%token UNIT
%token <Bin.Syntax.label> LABEL
%token LPAREN RPAREN
%token COLON
%token EOF

%start file
%type <Bin.Syntax.expr> file

%start input
%type <Bin.Syntax.expr> input

%%

file:
  | e = expr EOF
    { e }

input:
  | e = expr EOF
    { e }

expr:
  | x = LABEL DOUBLE_ARROW e = expr
    { expr_abs x e }
  | e = expr_app COLON p = poly
    { expr_anno e p }
  | e = expr_app
    { e }

expr_app:
  | e = expr_simple
    { e }
  | f = expr_app a = expr_simple
    { expr_app f a }

expr_simple:
  | UNIT
    { expr_unit }
  | x = LABEL
    { expr_var x }
  | LPAREN e = expr RPAREN
    { e }

poly:
  | s = poly_simple SINGLE_ARROW t = poly
    { poly_arrow s t }
  | x = LABEL DOUBLE_ARROW t = poly
    { poly_forall x t }
  | t = poly_simple
    { t }

poly_simple:
  | UNIT
    { poly_unit }
  | x = LABEL
    { poly_param x }
  | LPAREN t = poly RPAREN
    { t }
