open Ast
open Lexer

(** Parsing a comma separated list of tokens *)
let rec parse_list parsefn toks =
  let u, toks = parsefn toks in
  match toks with
  | COMMA :: toks ->
      let rep, toks = parse_list parsefn toks in
      (u :: rep, toks)
  | toks -> ([ u ], toks)

let rightparen = function
  | RPAREN :: toks -> toks
  | _ -> failwith "Symbol ) expected"

let rec parse_term = function
  | IDENT a :: LPAREN :: toks ->
      let x, toks = parse_list parse_term toks in
      (Fun (a, x), rightparen toks)
  | IDENT a :: toks -> (Fun (a, []), toks)
  | QUESTION :: IDENT a :: toks -> (Var a, toks)
  | _ -> failwith "Syntax of term"

(*Parsing of formulae;  prec is the precedence of the operator to the left;
    parsing stops at an operator with lower precedence*)
let rec parse_form =
  let makeQuant q b a = Quant (q, b, abstract (Fun (b, [])) a) in
  function
  | ALL :: IDENT a :: DOT :: toks ->
      let x, toks = parse_form toks in
      (makeQuant All a x, toks)
  | EXISTS :: IDENT a :: DOT :: toks ->
      let x, toks = parse_form toks in
      (makeQuant Exists a x, toks)
  | toks ->
      let a, toks = parse_atom toks in
      parse_fix 0 a toks

and parse_fix prec a = function
  | (IMPLIES as tok) :: toks
  | (IFF as tok) :: toks
  | (AND as tok) :: toks
  | (OR as tok) :: toks ->
      let conn =
        match tok with
        | IMPLIES -> Implies
        | IFF -> Iff
        | AND -> And
        | OR -> Or
        | _ -> failwith ""
      in
      let p = precedence_of conn in
      if p < prec then (a, tok :: toks)
      else
        let atom, toks = parse_atom toks in
        let b, toks = parse_fix p atom toks in
        parse_fix prec (Binop (a, conn, b)) toks
  | toks -> (a, toks)

and parse_atom = function
  | NEG :: toks ->
      let atom, toks = parse_atom toks in
      (Neg atom, toks)
  | LPAREN :: toks ->
      let x, toks = parse_form toks in
      (x, rightparen toks)
  | IDENT pr :: LPAREN :: toks ->
      let x, toks = parse_list parse_term toks in
      (Pred (pr, x), rightparen toks)
  | IDENT pr :: toks -> (Pred (pr, []), toks)
  | _ -> failwith "Syntax of formula"

let read a =
  let x, y = parse_form (scan [] (String.to_seq a |> List.of_seq)) in
  (*check that no tokens remain*)
  match y with
  | [] -> x
  | _ :: _ -> failwith "Extra characters in formula"
