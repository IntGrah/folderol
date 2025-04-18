(*TERMS AND FORMULAE*)
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

(*Precedence table*)
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
let string_of_quantifier = function All -> "ALL" | Exists -> "EXISTS"

(* Printing *)

let string_of_connective = function
  | And -> "&"
  | Or -> "|"
  | Implies -> "-->"
  | Iff -> "<->"

let parenthesise a = "(" ^ a ^ ")"

let rec stringof_term = function
  | Param (a, _) -> a
  | Var a -> "?" ^ a
  | Bound i -> "B." ^ Int.to_string i
  | Fun (a, ts) -> a ^ string_of_args ts

and string_of_args = function
  | [] -> ""
  | ts -> List.map stringof_term ts |> String.concat "," |> parenthesise

let string_of_formula =
  let rec aux prec = function
    | Pred (a, ts) -> a ^ string_of_args ts
    | Neg a -> "~" ^ aux 4 a
    | Binop (a, cf, b) ->
        let stringf = aux (max (precedence_of cf) prec) in
        let zf = stringf a ^ " " ^ string_of_connective cf ^ " " ^ stringf b in
        if precedence_of cf <= prec then parenthesise zf else zf
    | Quant (q, b, af) ->
        let bf = subst_bound (Fun (b, [])) af in
        let zf = string_of_quantifier q ^ " " ^ b ^ ". " ^ aux 0 bf in
        if prec > 0 then parenthesise zf else zf
  in
  aux 0
