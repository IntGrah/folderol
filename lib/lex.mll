{
    open Parser
}

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | "ALL"               { ALL }
  | "EXISTS"            { EXISTS }
  | "-->"               { IMPL }
  | "<->"               { IFF }
  | "|"                 { OR }
  | "&"                 { AND }
  | "~"                 { NOT }
  | "."                 { DOT }
  | "("                 { LPAREN }
  | ")"                 { RPAREN }
  | ","                 { COMMA }
  | "?"                 { QUESTION }
  | ['A'-'Z' 'a'-'z' '_']+ as id { IDENT id }
  | "?"['A'-'Z' 'a'-'z' '_' '0'-'9']+ as v { IDENT v }  (* meta variables *)
  | eof                 { EOF }
  | _ as c              { failwith ("Unexpected character: " ^ String.make 1 c) }
