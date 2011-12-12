(* $Id: netplex_sockserv.ml 976 2006-08-26 16:04:13Z gerd $ *)

open Netplex_types

let open_sockets prots =
  let fdlist = ref [] in
  let sockets = ref [] in
  try
    List.iter
      (fun proto ->
	 let fda =
	   Array.map
	     (fun addr ->
		let s =
		  Unix.socket
		    (Unix.domain_of_sockaddr addr) Unix.SOCK_STREAM 0 in
		fdlist := s :: !fdlist;
		Unix.setsockopt s Unix.SO_REUSEADDR proto#lstn_reuseaddr;
		Unix.setsockopt s Unix.SO_KEEPALIVE proto#so_keepalive;
		( match addr with
		    | Unix.ADDR_UNIX path ->
			( try Unix.unlink path with _ -> () )
		    | _ -> ()
		);
		Unix.bind s addr;
		Unix.set_nonblock s;
		Unix.set_close_on_exec s;
		Unix.listen s proto#lstn_backlog;
		s
	     )
	     proto#addresses in
	 sockets := (proto#name, fda) :: !sockets
      )
      prots;
    List.rev !sockets
  with
    | error ->
	List.iter (fun fd -> try Unix.close fd with _ -> ()) !fdlist;
	raise error
;;


class std_socket_service 
	proc
        config : socket_service =
  let sockets = open_sockets config#protocols in
object(self)
  method name = config#name
  method sockets = sockets
  method socket_service_config = config
  method processor = proc
  method create_container sockserv =
    Netplex_container.create_container sockserv

end


let create_socket_service
      proc
      config =
  new std_socket_service 
    proc config
;;
