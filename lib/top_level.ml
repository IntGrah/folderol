open Solver

(* Top-level commands: interaction with proof state *)

let print tab =
  Format.printf "%a" pp_tab tab;
  tab

(** Read a goal: the sequent As |- Bs *)
let read_goalseq afstrs bfstrs =
  init_gensym ();
  read_tab afstrs bfstrs |> print

(** Read the goal |- B *)
let read_goal bfstr = read_goalseq [] [ bfstr ]

let step tab = proof_step tab |> print
let steps n tab = proof_steps (max n 0) tab |> print

let run_goalseq afstrs bfstrs =
  read_goalseq afstrs bfstrs |> proof_steps (-1) |> print

let run_goal b = run_goalseq [] [ b ]

(** Raises exception unless some goals are left unsolved after n proof steps *)
let fail_goal n g =
  read_goal g |> steps n |> function
  | [] -> failwith "This proof should have failed!"
  | _ :: _ -> print_endline "Failed, as expected"
