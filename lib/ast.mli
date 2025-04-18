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

val precedence_of : connective -> int
val abstract : term -> formula -> formula
val subst_bound : term -> formula -> formula
val pp_quantifier : Format.formatter -> quantifier -> unit
val pp_connective : Format.formatter -> connective -> unit
val pp_term : Format.formatter -> term -> unit
val pp_args : Format.formatter -> term list -> unit
val pp_formula : Format.formatter -> formula -> unit
