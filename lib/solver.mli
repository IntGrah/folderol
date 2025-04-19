type goal
type goaltable = goal list

val gensym : unit -> string
val init_gensym : unit -> unit
val proof_step : goaltable -> goaltable
val proof_steps : int -> goaltable -> goaltable
val read_tab : string list -> string list -> goaltable
val pp_tab : Format.formatter -> goaltable -> unit
