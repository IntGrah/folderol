open Ast

(** Insertion into list if not already there *)
let ins x xs = if List.mem x xs then xs else x :: xs

(* UNIFICATION *)

exception Unify

(** Chase variable assignments *)
let rec chasevar env = function
  | Var a ->
      List.assoc_opt a env |> Option.fold ~none:(Var a) ~some:(chasevar env)
  | t -> t

(** Unification with var *)
let unify_var env a t =
  let rec occurs = function
    | Fun (_, ts) -> List.exists occurs ts
    | Param (_, bs) -> List.exists occurs (List.map (fun x -> Var x) bs)
    | Var b when a = b -> true
    | Var b -> List.assoc_opt b env |> Option.fold ~none:false ~some:occurs
    | _ -> false
  in
  if t = Var a then env else if occurs t then raise Unify else (a, t) :: env

let rec unify_term env t u =
  match (t, u) with
  | Var a, t -> unify_var env a t
  | t, Var a -> unify_var env a t
  | Param (a, _), Param (b, _) when a = b -> env
  | Fun (a, ts), Fun (b, us) when a = b && List.compare_lengths ts us = 0 ->
      unify_terms env ts us
  | _ -> raise Unify

(** Naive unification of terms containing no bound variables *)
and unify_terms env =
  List.fold_left2
    (fun env t u -> unify_term env (chasevar env t) (chasevar env u))
    env

(** Unification of atomic formulae *)
let unify af bf =
  match (af, bf) with
  | Pred (a, ts), Pred (b, us) when a = b && List.compare_lengths ts us = 0 ->
      unify_terms [] ts us
  | _ -> raise Unify

(** Accumulate all Vars in the term (not Vars attached to a Param). *)
let rec vars_in_term vars = function
  | Var a -> ins a vars
  | Fun (_, ts) -> List.fold_left vars_in_term vars ts
  | _ -> vars

(** Instantiate a term by an environment *)
let rec inst_term env = function
  | Fun (a, ts) -> Fun (a, List.map (inst_term env) ts)
  | Param (a, bs) ->
      Param
        ( a,
          List.map (fun x -> inst_term env (Var x)) bs
          |> List.fold_left vars_in_term [] )
  | Var a -> (
      match List.assoc_opt a env with
      | Some u -> inst_term env u
      | None -> Var a)
  | t -> t

(* INFERENCE: GOALS AND PROOF STATES: GOALS AND PROOF STATES *)

type side = Left | Right
type entry = int * (side * formula)
type goal = entry list
type goaltable = goal list

let rec inst_form env = function
  | Pred (a, ts) -> Pred (a, List.map (inst_term env) ts)
  | Neg afs -> Neg (inst_form env afs)
  | Binop (l, conn, r) -> Binop (inst_form env l, conn, inst_form env r)
  | Quant (q, b, af) -> Quant (q, b, inst_form env af)

let inst_goals (gfs : goaltable) = function
  | [] -> gfs
  | env ->
      List.map (List.map (fun (m, (si, af)) -> (m, (si, inst_form env af)))) gfs

(** Accumulate over all terms in a formula *)
let rec accum_form (f : 'a list -> term -> 'a list) (bs : 'a list) = function
  | Pred (_, ts) -> List.fold_left f bs ts
  | Neg a -> accum_form f bs a
  | Binop (l, _, r) -> List.fold_left (accum_form f) bs [ l; r ]
  | Quant (_, _, af) -> accum_form f bs af

(*Accumulate over all formulae in a goal*)
let accum_goal (f : 'a list -> formula -> 'a list) : 'a list -> goal -> 'a list
    =
  List.fold_left (fun acc (_, (_, af)) -> f acc af)

(*Accumulate all Params*)
let rec params_in_term pairs = function
  | Param (a, bs) -> ins (a, bs) pairs
  | Fun (_, ts) -> List.fold_left params_in_term pairs ts
  | _ -> pairs

(*Useful bindings, but beware free type variables*)
let vars_in_formula = accum_form vars_in_term
let vars_in_goal = accum_goal vars_in_formula
let params_in_goal = accum_goal (accum_form params_in_term)

(*Returns (As,Bs),preserving order of elements
  As = Left entries,  Bs = Right entries *)
let split_goal : goal -> formula list * formula list =
  List.partition_map (function
    | _, (Left, af) -> Left af
    | _, (Right, bf) -> Right bf)

let is_pred = function Pred _ -> true | _ -> false

(** Solve the goal [A |- A'] by unifying [A] with [A'], [Left] and [Right]
    atomic formulae. Returns list [Some (A, env)] if successful, otherwise
    [None]. *)
let solve_goal gf : (formula * (string * term) list) option =
  let rec findA afs bfs =
    match afs with
    | [] -> None (*failure*)
    | af :: afs ->
        let rec findB = function
          | [] -> findA afs bfs
          | bf :: bfs -> ( try Some (af, unify af bf) with Unify -> findB bfs)
        in
        findB bfs
  in
  let afs, bfs = split_goal gf in
  findA (List.filter is_pred afs) (List.filter is_pred bfs)

(** Insert goals into a goaltable. For each solved goal (A,env), accumulates the
    formula (in reverse) and instantiates all other goals. *)
let rec insert_goals (x : goaltable) (afs : formula list) (tab : goaltable) =
  match x with
  | [] -> (afs, tab)
  | gf :: gfs -> (
      match solve_goal gf with
      | Some (af, env) ->
          (* instantiate other goals *)
          insert_goals (inst_goals gfs env) (inst_form env af :: afs)
            (inst_goals tab env)
      | None -> insert_goals gfs afs (gf :: tab))

(** Generation of new variable names *)
let (gensym, init_gensym) : (unit -> string) * (unit -> unit) =
  let mk_var n =
    let rec aux acc n =
      let q, r = (n / 26, n mod 26) in
      let char = Char.chr (Char.code 'a' + r) in
      let acc = Seq.cons char acc in
      if q = 0 then acc else aux acc q
    in
    aux Seq.empty n |> String.of_seq
  in
  let varcount = ref 0 in
  ( (fun () ->
      let var = mk_var !varcount in
      varcount := !varcount + 1;
      var),
    fun () -> varcount := 0 )

(** The "cost" of reducing a connective *)
let cost = function
  | _, Neg _
  | Left, Binop (_, And, _)
  | Right, Binop (_, Or, _)
  | Right, Binop (_, Implies, _)
  | Right, Quant (All, _, _)
  | Left, Quant (Exists, _, _) ->
      1 (* a single subgoal *)
  | Right, Binop (_, And, _)
  | Left, Binop (_, Or, _)
  | Left, Binop (_, Implies, _)
  | _, Binop (_, Iff, _) ->
      2 (* case split: 2 subgoals *)
  | Left, Quant (All, _, _) | Right, Quant (Exists, _, _) ->
      3 (* quantifier expansion *)
  | _, Pred _ -> 1000 (* no reductions possible *)

let paircost sf : entry = (cost sf, sf)

(** Insertion into a list, ordered by sort keys. *)
let rec insert less (x : entry) : goal -> goal = function
  | [] -> [ x ]
  | y :: ys ->
      if less (fst y) (fst x) then y :: insert less x ys else x :: y :: ys

(** Extend the goal [goal] by inserting a list of (side,form) pairs *)
let new_goal goal pairs =
  List.fold_right (insert ( < )) (List.rev_map paircost pairs) goal

exception Reduce

(** Reduce the pair using the rest of the goal [goal] to make new goals *)
let reduce_goal (entry : entry) (goal : goal) : goal list =
  let goals = List.map (new_goal goal) in
  let vars_in af = vars_in_goal (vars_in_formula [] af) goal in
  let subparam af = subst_bound (Param (gensym (), vars_in af)) af in
  let subvar af = subst_bound (Var (gensym ())) af in
  let reduce : side * formula -> goaltable = function
    | Right, Neg af -> goals [ [ (Left, af) ] ]
    | Left, Neg af -> goals [ [ (Right, af) ] ]
    | Right, Binop (af, And, bf) -> goals [ [ (Right, af) ]; [ (Right, bf) ] ]
    | Left, Binop (af, And, bf) -> goals [ [ (Left, af); (Left, bf) ] ]
    | Right, Binop (af, Or, bf) -> goals [ [ (Right, af); (Right, bf) ] ]
    | Left, Binop (af, Or, bf) -> goals [ [ (Left, af) ]; [ (Left, bf) ] ]
    | Right, Binop (af, Implies, bf) -> goals [ [ (Left, af); (Right, bf) ] ]
    | Left, Binop (af, Implies, bf) -> goals [ [ (Right, af) ]; [ (Left, bf) ] ]
    | Right, Binop (af, Iff, bf) ->
        goals [ [ (Left, af); (Right, bf) ]; [ (Right, af); (Left, bf) ] ]
    | Left, Binop (af, Iff, bf) ->
        goals [ [ (Left, af); (Left, bf) ]; [ (Right, af); (Right, bf) ] ]
    | Right, Quant (All, _, af) -> goals [ [ (Right, subparam af) ] ]
    | Left, Quant (All, _, af) ->
        [
          insert ( <= ) entry goal |> insert ( < ) (paircost (Left, subvar af));
        ]
    | Right, Quant (Exists, _, af) ->
        [
          insert ( <= ) entry goal |> insert ( < ) (paircost (Right, subvar af));
        ]
    | Left, Quant (Exists, _, af) -> goals [ [ (Left, subparam af) ] ]
    | _ -> raise Reduce
  in
  reduce (snd entry)

(** Print the rule used, with each formula found by unification, indenting by
    number of goals left. *)
let print_step (_, (si, cf)) ngoals afs =
  let pp_symbol ppf = function
    | Pred (a, _) -> Format.pp_print_string ppf a
    | Neg _ -> Format.pp_print_string ppf "~"
    | Binop (_, a, _) -> pp_connective ppf a
    | Quant (q, _, _) -> pp_quantifier ppf q
  in
  let pp_side ppf = function
    | Right -> Format.pp_print_string ppf ":right"
    | Left -> Format.pp_print_string ppf ":left"
  in
  Format.printf "%*s%a%a%a@." ngoals "" pp_symbol cf pp_side si
    (Format.pp_print_list ~pp_sep:Format.pp_print_nothing (fun ppf ->
         Format.fprintf ppf "   %a" pp_formula))
    (List.rev afs)

(** A single inference in the goaltable *)
let proof_step : goaltable -> goaltable = function
  | [] -> []
  | [] :: _ -> failwith "Empty goal"
  | (entry :: gf) :: tab ->
      let afs, new_tab = insert_goals (reduce_goal entry gf) [] tab in
      print_step entry (List.length tab) afs;
      new_tab

(** Perform n proof steps, no limit if n < 0. Stops if impossible to continue.
*)
let rec proof_steps n = function
  | [] -> [] (* success -- no goals *)
  | tab when n = 0 -> tab
  | tab -> (
      try proof_steps (n - 1) (proof_step tab)
      with Reduce ->
        Format.printf "@.**No proof rules applicable**@.";
        tab)

(** Make a goal from lists of formulae: As |- Bs *)
let make_goal afs bfs : goal =
  let aes = List.map (fun af -> (Left, af)) afs in
  let bes = List.map (fun bf -> (Right, bf)) bfs in
  new_goal [] (aes @ bes)

(** Reading of goals: Astrs |- Bstrs *)
let read_tab afstrs bfstrs : goaltable =
  let read = Frontend.Comb.read in
  let afs = List.rev_map read afstrs in
  let bfs = List.rev_map read bfstrs in
  let gf = make_goal afs bfs in
  let _, tab = insert_goals [ gf ] [] [] in
  tab

let pp_tab ppf = function
  | [] -> Format.fprintf ppf "No more goals: proof finished@."
  | gfs ->
      let pp_sequent ppf = function
        | [] -> Format.pp_print_string ppf "empty"
        | afs ->
            Format.pp_print_list
              ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
              pp_formula ppf afs
      in
      let pp_goal ppf gf =
        let afs, bfs = split_goal gf in
        Format.fprintf ppf "%a  |-  %a@." pp_sequent afs pp_sequent bfs
      in
      let pp_count ppf = function
        | [ _ ] -> ()
        | gfs -> Format.fprintf ppf "%d goals@." (List.length gfs)
      in
      let pp_param ppf (a, ts) =
        Format.fprintf ppf "%s         %a" a pp_args
          (List.map (fun x -> Var x) ts)
      in
      let pp_params ppf = function
        | [] -> ()
        | pairs ->
            Format.fprintf ppf "Param     Not allowed in@.%a@.@."
              (Format.pp_print_list ~pp_sep:Format.pp_print_newline pp_param)
              pairs
      in
      Format.fprintf ppf "@.%a@.%a%a"
        (Format.pp_print_list ~pp_sep:Format.pp_print_newline pp_goal)
        gfs pp_count gfs pp_params
        (List.fold_left params_in_goal [] gfs)
