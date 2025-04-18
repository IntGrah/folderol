open Solver

val print : goaltable -> goaltable

val read_goalseq : string list -> string list -> goaltable
(** Read goal sequent *)

val read_goal : string -> goaltable
(** Read goal formula *)

val step : goaltable -> goaltable
(** One step *)

val steps : int -> goaltable -> goaltable
(** Many steps *)

val run_goalseq : string list -> string list -> goaltable
(** Read goal sequent and go *)

val run_goal : string -> goaltable

val fail_goal : int -> string -> unit
(** Bombs unless some goals left unsolved *)
