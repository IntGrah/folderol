(* Just for fun, a recursive descent parser based on monadic parser combinators *)

module Combinators = struct
  type 'a t = Lexer.token list -> ('a * Lexer.token list) option
  (** Haskell: [newtype Parser a = StateT [Token] Maybe a] *)

  let return a = fun toks -> Some (a, toks)

  let ( let* ) (ma : 'a t) (f : 'a -> 'b t) : 'b t =
   fun toks -> Option.bind (ma toks) (fun (a, toks) -> f a toks)

  (** From Alternative / MonadPlus *)
  let ( <|> ) (ma : 'a t) (ma' : 'a t) : 'a t =
   fun toks -> match ma toks with Some a -> Some a | None -> ma' toks

  let fail : 'a t = fun _ -> None
  let one_of (parsers : 'a t list) : 'a t = List.fold_left ( <|> ) fail parsers
end

open Ast
open Combinators

let token (tok : Lexer.token) : unit t = function
  | tok' :: toks when tok = tok' -> Some ((), toks)
  | _ -> None

let parse_ident : string t = function
  | IDENT a :: toks -> return a toks
  | toks -> fail toks

(** Parsing a comma separated list of tokens *)
let rec parse_list parsefn =
  let* u = parsefn in
  one_of
    [
      (let* () = token COMMA in
       let* rep = parse_list parsefn in
       return (u :: rep));
      return [ u ];
    ]

let rec parse_term : term t =
 fun toks ->
  one_of
    [
      (let* f = parse_ident in
       let* () = token LPAREN in
       let* args = parse_list parse_term in
       let* () = token RPAREN in
       return (Fun (f, args)));
      (let* a = parse_ident in
       return (Fun (a, [])));
      (let* () = token QUESTION in
       let* a = parse_ident in
       return (Var a));
    ]
    toks

(** Parsing of formulae; prec is the precedence of the operator to the left;
    parsing stops at an operator with lower precedence*)
let rec parse_form toks =
  let makeQuant q b a = Quant (q, b, abstract (Fun (b, [])) a) in
  one_of
    [
      (let* () = token ALL in
       let* a = parse_ident in
       let* () = token DOT in
       let* x = parse_form in
       return (makeQuant All a x));
      (let* () = token EXISTS in
       let* a = parse_ident in
       let* () = token DOT in
       let* x = parse_form in
       return (makeQuant Exists a x));
      (let* atom = parse_atom in
       parsefix 0 atom);
    ]
    toks

and parsefix prec a toks =
  one_of
    [
      one_of
        (List.map
           (fun (tok, conn) ->
             let p = precedence_of conn in
             if p < prec then fail
             else
               let* () = token tok in
               let* atom = parse_atom in
               let* b = parsefix p atom in
               parsefix prec (Binop (a, conn, b)))
           [ (IMPLIES, Implies); (IFF, Iff); (AND, And); (OR, Or) ]);
      return a;
    ]
    toks

and parse_atom : formula t =
 fun toks ->
  one_of
    [
      (let* () = token NEG in
       let* a = parse_atom in
       return (Neg a));
      (let* () = token LPAREN in
       let* a = parse_form in
       let* () = token RPAREN in
       return a);
      (let* p = parse_ident in
       let* () = token LPAREN in
       let* args = parse_list parse_term in
       let* () = token RPAREN in
       return (Pred (p, args)));
      (let* p = parse_ident in
       return (Pred (p, [])));
    ]
    toks

let read a =
  match parse_form (Lexer.scan [] (String.to_seq a |> List.of_seq)) with
  | Some (x, []) -> x
  | Some (_, _ :: _) -> failwith "Extra characters in formula"
  | None -> failwith "Syntax of formula"

(*check that no tokens remain*)
