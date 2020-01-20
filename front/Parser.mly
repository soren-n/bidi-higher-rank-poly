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
%token COLON
%token EOF

%start file
%type <Back.Syntax.expr> file

%start input
%type <Back.Syntax.expr> input

%%

file:
  | e = expr EOF
    { e }

input:
  | e = expr EOF
    { e }

expr:
  | e = expr_prime COLON p = poly
    { expr_anno e p }
  | e = expr_prime
    { e }

expr_prime:
  | x = LABEL DOUBLE_ARROW e = expr_prime
    { expr_abs x e }
  | e = expr_app
    { e }

expr_app:
  | e = expr_simple
    { e }
  | f = expr_app a = expr_simple
    { expr_app f a }

expr_simple:
  | UNDEFINED
    { expr_undefined }
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
  | NOTHING
    { poly_bot }
  | UNIT
    { poly_unit }
  | x = LABEL
    { poly_param x }
  | LPAREN t = poly RPAREN
    { t }
