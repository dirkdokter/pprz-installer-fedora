(* $Id: netplex_mp.mli 896 2006-06-03 22:31:04Z gerd $ *)

(** Multi-processing provider *)

class mp : unit -> Netplex_types.parallelizer
  (** Uses [Unix.fork] to create new threads *)

val mp : unit -> Netplex_types.parallelizer
  (** Uses [Unix.fork] to create new threads *)
