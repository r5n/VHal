{
open Parser
}

let white = [' ' '\t' '\n']+
let letter = ['a'-'z' 'A'-'Z']
let id = letter ['a'-'z' 'A'-'Z' '0'-'9']*

rule read =
  parse
  | white     { read lexbuf }
  | "("       { LPAREN }
  | ")"       { RPAREN }
  | "ALL"     { ALL }
  | "EX"      { EX }
  | "~"       { NEG }
  | "&"       { AND }
  | "|"       { OR }
  | ","       { COMMA }
  | "."       { PERIOD }
  | "?"       { QUESTION }
  | "-->"     { IMPL }
  | "<->"     { IFF }
  | id        { IDENT (Lexing.lexeme lexbuf) }
  | eof       { EOF }