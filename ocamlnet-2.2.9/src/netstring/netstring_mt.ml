(* $Id: netstring_mt.ml 1003 2006-09-24 15:17:15Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

(* Initialize multi-threading mode: *)

(* let str_mutex = Mutex.create();; *)
let mappings_mutex = Mutex.create();;

(*
Netstring_str.init_mt
  (fun () -> Mutex.lock str_mutex)
  (fun () -> Mutex.unlock str_mutex);
*)
Netmappings.init_mt
  (fun () -> Mutex.lock mappings_mutex)
  (fun () -> Mutex.unlock mappings_mutex)
;;
