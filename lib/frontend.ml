open Parser

(** A really bad lexer written from scratch instead of using ocamllex *)
module Lex : sig
  val scan : token list -> char list -> token list
end = struct
  let is_alpha_num = function
    | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' -> true
    | _ -> false

  (** Scanning of identifiers or EXISTS / ALL *)
  let rec scan_ident front = function
    | c :: cs when is_alpha_num c -> scan_ident (c :: front) cs
    | rest -> (List.rev front |> List.to_seq |> String.of_seq, rest)

  (** Scanning, skipping blanks, etc. *)
  let rec scan front_toks = function
    (* End of char list *)
    | [] -> List.rev (EOF :: front_toks)
    | '-' :: '-' :: '>' :: cs -> scan (IMPLIES :: front_toks) cs
    | '<' :: '-' :: '>' :: cs -> scan (IFF :: front_toks) cs
    | '.' :: cs -> scan (DOT :: front_toks) cs
    | '~' :: cs -> scan (NEG :: front_toks) cs
    | ',' :: cs -> scan (COMMA :: front_toks) cs
    | '(' :: cs -> scan (LPAREN :: front_toks) cs
    | ')' :: cs -> scan (RPAREN :: front_toks) cs
    | '&' :: cs -> scan (AND :: front_toks) cs
    | '|' :: cs -> scan (OR :: front_toks) cs
    | '?' :: cs -> scan (QUESTION :: front_toks) cs
    | (' ' | '\t' | '\n') :: cs -> scan front_toks cs
    | cs ->
        let str, cs = scan_ident [] cs in
        let tok =
          match str with
          | "EXISTS" -> EXISTS
          | "ALL" -> ALL
          | "" -> invalid_arg "Illegal character"
          | s -> IDENT s
        in
        scan (tok :: front_toks) cs
end

module type S = sig
  val read : string -> Ast.formula
end

(** Generated from ocamllex and ocamlyacc *)
module Gen : S = struct
  let read str = Parser.main Lexer.token (Lexing.from_string str)
end

(** A really bad recursive descent parser based on combinators *)
module Comb : S = struct
  open struct
    type 'a t = token list -> ('a * token list) option
    (** Haskell: [newtype Parser a = StateT [Token] Maybe a] *)

    let return a = fun toks -> Some (a, toks)

    let ( let* ) (ma : 'a t) (f : 'a -> 'b t) : 'b t =
     fun toks -> Option.bind (ma toks) (fun (a, toks) -> f a toks)

    (** Alternative / MonadPlus *)
    let ( <|> ) (ma : 'a t) (ma' : 'a t) : 'a t =
     fun toks -> match ma toks with Some a -> Some a | None -> ma' toks

    let fail : 'a t = fun _ -> None

    let one_of (parsers : 'a t list) : 'a t =
      List.fold_left ( <|> ) fail parsers
  end

  open Ast

  let token (tok : token) : unit t = function
    | tok' :: toks when tok = tok' -> Some ((), toks)
    | _ -> None

  let parse_ident : string t = function
    | IDENT a :: toks -> return a toks
    | toks -> fail toks

  (** Parsing a comma separated list of tokens *)
  let rec parse_list parsefn =
    let* u = parsefn in
    let continue =
      let* () = token COMMA in
      let* rep = parse_list parsefn in
      return (u :: rep)
    in
    continue <|> return [ u ]

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
      parsing stops at an operator with lower precedence *)
  let rec parse_formula toks =
    let makeQuant q b a = Quant (q, b, abstract (Fun (b, [])) a) in
    one_of
      [
        (let* () = token ALL in
         let* a = parse_ident in
         let* () = token DOT in
         let* x = parse_formula in
         return (makeQuant All a x));
        (let* () = token EXISTS in
         let* a = parse_ident in
         let* () = token DOT in
         let* x = parse_formula in
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
         let* a = parse_formula in
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
    match parse_formula (Lex.scan [] (String.to_seq a |> List.of_seq)) with
    | Some (x, [ EOF ]) -> x
    | Some (_, _) -> failwith "Extra characters in formula"
    | None -> failwith "Syntax of formula"
end

(** A really bad recursive descent parser, free of monads *)
module Manual : S = struct
  open Ast

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

  (** Parsing of formulae; prec is the precedence of the operator to the left;
      parsing stops at an operator with lower precedence *)
  let rec parse_formula =
    let makeQuant q b a = Quant (q, b, abstract (Fun (b, [])) a) in
    function
    | ALL :: IDENT a :: DOT :: toks ->
        let x, toks = parse_formula toks in
        (makeQuant All a x, toks)
    | EXISTS :: IDENT a :: DOT :: toks ->
        let x, toks = parse_formula toks in
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
        let x, toks = parse_formula toks in
        (x, rightparen toks)
    | IDENT pr :: LPAREN :: toks ->
        let x, toks = parse_list parse_term toks in
        (Pred (pr, x), rightparen toks)
    | IDENT pr :: toks -> (Pred (pr, []), toks)
    | _ -> failwith "Syntax of formula"

  let read a =
    match parse_formula (Lex.scan [] (String.to_seq a |> List.of_seq)) with
    | x, [ EOF ] -> x
    | _, _ -> failwith "Extra characters in formula"
end
