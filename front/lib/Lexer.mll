{
  open Parser
  exception Error of string
}

let label = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let binary =
  (['0' '1']['0' '1']['0' '1']['0' '1']['0' '1']['0' '1']['0' '1']['0' '1'])+

rule token = parse
    [' ' '\t' '\r'] { token lexbuf }
  | '\n'            { Lexing.new_line lexbuf; token lexbuf }
  | "nothing"       { NOTHING }
  | "undefined"     { UNDEFINED }
  | "unit"          { UNIT }
  | "->"            { SINGLE_ARROW }
  | "=>"            { DOUBLE_ARROW }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ':'             { DECLARE }
  | '='             { DEFINE }
  | '.'             { END }
  | label           { LABEL (Lexing.lexeme lexbuf) }
  | binary          { BINARY (Lexing.lexeme lexbuf) }
  | eof             { EOF }
  | _ { raise (Error "Syntax error") }
