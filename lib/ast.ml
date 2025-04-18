(* Terms and formulae *)

type term =
  | Var of string
  | Param of string * string list
  | Bound of int
  | Fun of string * term list

type connective = And | Or | Implies | Iff
type quantifier = All | Exists

type formula =
  | Pred of string * term list
  | Neg of formula
  | Binop of formula * connective * formula
  | Quant of quantifier * string * formula

(*variables
    a,b,c: string     q,r: string (quantifier names)
    i,j: int    (Bound indexes)
    t,u: term    A,B: form
    x,y: any     f,g: functions
*)

(** Precedence table *)
let precedence_of = function And -> 3 | Or -> 2 | Iff -> 1 | Implies -> 1

let map f =
  let rec abs i = function
    | Pred (a, ts) -> Pred (a, List.map (f i) ts)
    | Neg a -> Neg (abs i a)
    | Binop (l, conn, r) -> Binop (abs i l, conn, abs i r)
    | Quant (q, b, a) -> Quant (q, b, abs (i + 1) a)
  in
  abs 0

(*Replace the atomic term u by u' throughout a term*)
let rec replace_term u u' = function
  | t when t = u -> u'
  | Fun (a, ts) -> Fun (a, List.map (replace_term u u') ts)
  | t -> t

(*Abstraction of a formula over t (containing no bound vars).*)
let abstract t = map (fun i -> replace_term t (Bound i))

(*Replace (Bound 0) in formula with t (containing no bound vars).*)
let subst_bound t = map (fun i -> replace_term (Bound i) t)

(* Printing *)

let pp_quantifier ppf = function
  | All -> Format.pp_print_string ppf "ALL"
  | Exists -> Format.pp_print_string ppf "EXISTS"

let pp_connective ppf = function
  | And -> Format.pp_print_string ppf "&"
  | Or -> Format.pp_print_string ppf "|"
  | Implies -> Format.pp_print_string ppf "-->"
  | Iff -> Format.pp_print_string ppf "<->"

let pp_paren ppf = Format.fprintf ppf "(%a)"

let rec pp_term ppf = function
  | Param (a, _) -> Format.fprintf ppf "%s" a
  | Var a -> Format.fprintf ppf "?%s" a
  | Bound i -> Format.fprintf ppf "B.%d" i
  | Fun (a, ts) -> Format.fprintf ppf "%s%a" a pp_args ts

and pp_args ppf = function
  | [] -> Format.pp_print_nothing ppf ()
  | ts ->
      pp_paren ppf
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ",")
           pp_term)
        ts

let pp_formula =
  let rec aux prec ppf : formula -> unit = function
    | Pred (a, ts) -> Format.fprintf ppf "%s%a" a pp_args ts
    | Neg a -> Format.fprintf ppf "~%a" (aux 4) a
    | Binop (a, cf, b) ->
        let aux_prec = aux (max (precedence_of cf) prec) in
        let zf ppf () =
          Format.fprintf ppf "%a %a %a" aux_prec a pp_connective cf aux_prec b
        in
        if precedence_of cf <= prec then Format.fprintf ppf "(%a)" zf ()
        else zf ppf ()
    | Quant (q, b, af) ->
        let bf = subst_bound (Fun (b, [])) af in
        let zf ppf () =
          Format.fprintf ppf "%a %s. %a" pp_quantifier q b (aux 0) bf
        in
        if prec > 0 then pp_paren ppf zf () else zf ppf ()
  in
  aux 0
