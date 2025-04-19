{
open Parser

exception Syntax_error
}

let whitespace = [' ' '\t' '\n']+
let ident = ['A'-'Z' 'a'-'z' '0'-'9']+

rule token = parse
  | whitespace  { token lexbuf }
  | "-->"       { IMPLIES }
  | "<->"       { IFF }
  | "."         { DOT }
  | "~"         { NEG }
  | ","         { COMMA }
  | "("         { LPAREN }
  | ")"         { RPAREN }
  | "&"         { AND }
  | "|"         { OR }
  | "?"         { QUESTION }
  | "ALL"       { ALL }
  | "EXISTS"    { EXISTS }
  | ident as id { IDENT id }
  | eof         { EOF }
  | _           { raise Syntax_error }
