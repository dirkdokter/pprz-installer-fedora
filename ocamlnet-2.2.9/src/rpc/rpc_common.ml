(* $Id: rpc_common.ml 459 2006-04-30 19:49:19Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

open Rtypes
open Xdr

(* auxiliary functions of general use *)

let rec unix_call (f:unit->'a) : 'a =
  try
    f()
  with
    Unix.Unix_error (Unix.EINTR, _, _) -> unix_call f
;;


(* TODO:
 * check if all system calls use unix_call
 *)
