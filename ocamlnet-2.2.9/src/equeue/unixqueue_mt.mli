(* $Id: unixqueue_mt.mli 459 2006-04-30 19:49:19Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

(** This module initializes Unixqueue for multi-threaded programs.
 * Make sure that this module is linked as object file (.cmo or .cmx)
 * into the final executable, because this module would be garbage-
 * collected if it were in an archive file (.cma or .cmxa).
 * If you use ocamlfind, this will be done automatically provided
 * that a -thread or -vmthread switch is on the command line.
 *)
