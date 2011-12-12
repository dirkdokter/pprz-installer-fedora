(* $Id: rpc_auth_sys.ml 459 2006-04-30 19:49:19Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

open Xdr
open Rtypes
open Rpc

type identity =
    [ `Effective_user
    | `Real_user
    | `This_user of (int * int * int array * string)
    ]


let auth_params_type =
  X_struct [ "stamp",       X_uint;
	     "machinename", (X_string (uint4_of_int 255));
	     "uid",         X_uint;
	     "gid",         X_uint;
	     "gids",        X_array(X_uint,(uint4_of_int 16))
	   ]
;;


let val_auth_params_type = validate_xdr_type auth_params_type;;


type state =
    Init
  | Auth_sys_sent
  | Auth_short_sent
  | Auth_accepted of string  (* returned verifier *)


let max_uint4_as_int64 =
  Int64.of_string "0xffffffff";;

class client_auth_session identity : Rpc_client.auth_session =
let (uid, gid, gids, hostname) =
  match identity with
      `Effective_user -> (Unix.geteuid(), Unix.getegid(), Unix.getgroups(),
			  Unix.gethostname())
    | `Real_user      -> (Unix.getuid(),  Unix.getgid(),  Unix.getgroups(),
			  Unix.gethostname())
    | `This_user(u,g,gs,h) -> (u,g,gs,h) in
object
  val mutable state = Init


  method next_credentials _ =
    match state with
	Init
      | Auth_sys_sent             (* handle this case for robustness *)
      | Auth_short_sent ->        (* handle this case for robustness *)
	  (* Send AUTH_SYS credentials: *)
	  let xdr_value =
	    XV_struct
	      [ "stamp",       XV_uint (uint4_of_int64 (Int64.logand
							  (Int64.of_float
							     (Unix.time()))
							  max_uint4_as_int64));
		"machinename", XV_string hostname;
		"uid",         XV_uint (uint4_of_int uid);
		"gid",         XV_uint (uint4_of_int gid);
		"gids",        XV_array (Array.map
					   (fun g -> XV_uint (uint4_of_int g))
					   gids)
	      ]
	  in
	  let creds = pack_xdr_value_as_string
			xdr_value val_auth_params_type [] in
	  state <- Auth_sys_sent;
	  ("AUTH_SYS", creds, "AUTH_NONE", "")
      | Auth_accepted creds ->
	  (* Send AUTH_SHORT credentials: *)
	  state <- Auth_short_sent;
	  ("AUTH_SHORT", creds, "AUTH_NONE", "")

  method server_rejects err =
    match state with
	Auth_sys_sent ->
	  state <- Init;
	  raise (Rpc_server err)
      | Auth_short_sent ->
	  (* Retry: *)
	  state <- Init
      | _ ->
	  assert false

  method server_accepts flav data =
    match state with
	Auth_sys_sent
      | Auth_short_sent ->
	  ( match flav with
		"AUTH_SHORT" -> state <- Auth_accepted data
	      | _            -> state <- Init
	  )
      | _ ->
	  assert false
end


class client_auth_method ?(identity = `Real_user) () : Rpc_client.auth_method =
let _ = (identity : identity) in
object
  method name = "AUTH_SYS"
  method new_session() = new client_auth_session identity
end


let client_auth_method = new client_auth_method


type user_name_format =
    [ `Full
    | `UID
    | `Custom of int32 -> int32 -> int32 array -> string -> string
    ]


class server_auth_method
        ?(lookup_hostname = true)
        ?(require_privileged_port = true)
        ?(user_name_as = (`Full : user_name_format))
	()
	: Rpc_server.auth_method =
object
  method name = "AUTH_SYS"
  method flavors = [ "AUTH_SYS" ]              (* We don't reply AUTH_SHORT! *)
  method peek = `None
  method authenticate
           srv cnid sockname peername cred_flav cred_data verf_flav verf_data
	   pass =
    (* Unpack cred_data: *)
    let xdr = Xdr.unpack_xdr_value cred_data val_auth_params_type [] in
    match xdr with
	XV_struct
	  [ "stamp", _;
	    "machinename", XV_string hostname;
	    "uid",         XV_uint uid;
	    "gid",         XV_uint gid;
	    "gids",        XV_array xdr_gids;
	  ]
	->
	  let gids = Array.map
		       (function XV_uint g -> g | _ -> assert false)
		       xdr_gids in
	  if lookup_hostname then begin
	    match peername with
	      | Some (Unix.ADDR_INET(a,p)) ->
		  begin try
		    let entry = Unix.gethostbyname hostname in
		    let l = Array.to_list entry.Unix.h_addr_list in
		    if not(List.mem a l) then
		      raise Not_found
		  with
		      Not_found ->
			raise(Rpc_server Auth_bad_cred)
		  end
	      | _ ->
		  ()
	  end;
	  if require_privileged_port then begin
	    match peername with
	      | Some(Unix.ADDR_INET(a,p)) ->
		  if p >= 1024 then raise(Rpc_server Auth_bad_cred)
	      | _ ->
		  (* The Unix syscalls are missing. *)
		  raise(Rpc_server Auth_bad_cred)
	  end;
	  let uid_gid_str =
	    Int32.to_string(Rtypes.logical_int32_of_uint4 uid) ^ "." ^
	    Int32.to_string(Rtypes.logical_int32_of_uint4 gid) in
	  let gidlist_str =
	    String.concat "."
	      (Array.to_list
		 (Array.map
		    (fun u -> Int32.to_string(Rtypes.logical_int32_of_uint4 u))
		    gids
		 )
	      )
	  in
	  let username =
	    match user_name_as with
	      | `Full ->
		  uid_gid_str ^ 
		    (if gidlist_str <> "" then "." ^ gidlist_str else "") ^ 
		    "@" ^ hostname
	      | `UID ->
		  Int32.to_string(Rtypes.logical_int32_of_uint4 uid)
	      | `Custom f ->
		  f 
		    (Rtypes.logical_int32_of_uint4 uid)
		    (Rtypes.logical_int32_of_uint4 gid) 
		    (Array.map (fun u ->  Rtypes.logical_int32_of_uint4 u) gids)
		    hostname
	  in
	  pass (Rpc_server.Auth_positive(username, "AUTH_NONE", ""))

      | _ ->
	  assert false

end

let server_auth_method = new server_auth_method


let parse_user_name s =
  let rec parse pos ugs =
    try
      let pos' = String.index_from ugs pos '.' in  (* or Not_found *)
      let ds = String.sub ugs pos (pos' - pos) in
      int_of_string ds :: parse (pos'+1) ugs
    with
	Not_found ->
	  let ds = String.sub ugs pos (String.length ugs - pos) in
	  [ int_of_string ds ]
  in
  try
    let at_pos = String.index s '@' in  (* or Not_found *)
    let hostname = String.sub s (at_pos+1) (String.length s - 1 - at_pos) in
    match parse 0 (String.sub s 0 at_pos) with
	uid :: gid :: gidlist ->
	  (uid,gid,Array.of_list gidlist,hostname)
      | _ ->
	  raise Not_found
  with
      _ -> failwith "Rpc_auth_sys.parse_user_name"
;;
