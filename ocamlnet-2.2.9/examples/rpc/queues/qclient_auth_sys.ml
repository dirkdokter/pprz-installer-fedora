(* $Id: qclient_auth_sys.ml 874 2006-05-04 14:07:27Z gerd $ *)

module C1 = Queues_clnt.QUEUESPROG.QUEUESVERS1 ;;

Qclient.pluggable_auth_module :=
  ( "auth_sys",
    (fun host ->
       let clnt = C1.create_portmapped_client host Rpc.Tcp in
       Rpc_client.set_auth_methods clnt 
	 [ Rpc_auth_sys.client_auth_method() ];
       clnt
    )
  )
;;
