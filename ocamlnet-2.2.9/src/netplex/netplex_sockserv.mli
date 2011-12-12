(* $Id: netplex_sockserv.mli 906 2006-06-05 12:19:10Z gerd $ *)

(** Socket service creation
  *
  * A socket service object is an encapsulation of a user-defined processor
  * for a list of sockets.
 *)

open Netplex_types

val create_socket_service :
      processor ->
      socket_service_config ->
        socket_service
