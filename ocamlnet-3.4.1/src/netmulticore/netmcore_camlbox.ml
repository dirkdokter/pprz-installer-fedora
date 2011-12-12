(* $Id: netmcore_camlbox.ml 1496 2010-11-27 21:49:12Z gerd $ *)

open Netcamlbox
open Netmcore
open Printf

let create_camlbox prefix n size =
  let (fd, name) =
    Netsys_posix.shm_create ("/" ^ prefix) 0 in
  let fd_open = ref true in
  try
    let box =
      format_camlbox fd n size in
    Unix.close fd;
    fd_open := false;
    let res = manage_shm name in
    (box, res#id)
  with
    | error ->
	if !fd_open then Unix.close fd;
	raise error


let lookup_camlbox_address res_id =
  let name = get_shm res_id in
  assert(name.[0] = '/');
  String.sub name 1 (String.length name - 1)


let lookup_camlbox_sender res_id = 
  let addr = lookup_camlbox_address res_id in
  camlbox_sender addr

