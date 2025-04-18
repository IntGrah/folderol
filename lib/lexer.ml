(* Scanning a list of characters into a list of tokens *)

type token =
  | ALL
  | EXISTS
  | NEG
  | DOT
  | COMMA
  | LPAREN
  | RPAREN
  | QUESTION
  | IMPLIES
  | IFF
  | AND
  | OR
  | IDENT of string

let is_alpha_num = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' -> true
  | _ -> false

(*Scanning of identifiers and keywords*)

let rec scan_ident front = function
  | c :: cs when is_alpha_num c -> scan_ident (c :: front) cs
  | rest -> (IDENT (front |> List.rev |> List.to_seq |> String.of_seq), rest)

(** Scanning, skipping blanks, etc. *)
let rec scan front_toks = function
  (* End of char list *)
  | [] -> List.rev front_toks
  | '-' :: '-' :: '>' :: cs -> scan (IMPLIES :: front_toks) cs
  | '<' :: '-' :: '>' :: cs ->
      scan (IFF :: front_toks) cs (*blanks, tabs, newlines*)
  | 'E' :: 'X' :: 'I' :: 'S' :: 'T' :: 'S' :: cs ->
      scan (EXISTS :: front_toks) cs
  | 'A' :: 'L' :: 'L' :: cs -> scan (ALL :: front_toks) cs
  | '.' :: cs -> scan (DOT :: front_toks) cs
  | '~' :: cs -> scan (NEG :: front_toks) cs
  | ',' :: cs -> scan (COMMA :: front_toks) cs
  | '(' :: cs -> scan (LPAREN :: front_toks) cs
  | ')' :: cs -> scan (RPAREN :: front_toks) cs
  | '&' :: cs -> scan (AND :: front_toks) cs
  | '|' :: cs -> scan (OR :: front_toks) cs
  | '?' :: cs -> scan (QUESTION :: front_toks) cs
  | (' ' | '\t' | '\n') :: cs -> scan front_toks cs
  | c :: cs when is_alpha_num c ->
      let tok, cs = scan_ident [ c ] cs in
      scan (tok :: front_toks) cs
  | _ -> failwith "Illegal character"
