(* $Id: qserver_auth_sys.ml 874 2006-05-04 14:07:27Z gerd $ *)

(* Configure qserver for system authentication (UNSAFE) *)

Qserver.pluggable_auth_module :=
  ( "auth_sys",
    (`Socket(Rpc.Tcp, Rpc_server.Portmapped, Rpc_server.default_socket_config)),
    (fun srv ->
       Rpc_server.set_auth_methods
	 srv
	 [ Rpc_auth_sys.server_auth_method
	      ~require_privileged_port:false 
	      ~user_name_as:`UID
	      () ]
    )
  )
;;