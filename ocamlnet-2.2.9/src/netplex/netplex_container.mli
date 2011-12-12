(* $Id: netplex_container.mli 903 2006-06-04 18:10:32Z gerd $ *)

(** Containers
  *
  * The container is the management object for the concurrently running
  * service processor.
 *)

open Netplex_types

val create_container : 
      parallelization_type -> socket_service -> container
  (** The container for normal services *)

val create_admin_container : 
      Unixqueue.unix_event_system -> parallelization_type -> socket_service -> container
  (** {b Internally used.} The container for the special admin service *)
