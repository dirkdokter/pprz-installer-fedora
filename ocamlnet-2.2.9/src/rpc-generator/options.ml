(* $Id: options.ml 459 2006-04-30 19:49:19Z gerd $
 * ----------------------------------------------------------------------
 *
 *)


let default_int_variant = ref Syntax.Abstract;;
  (* The int variant chosen by default (i.e. int without
   * preceding _abstract, _int32, _int64, or _unboxed keyword)
   *)

let default_hyper_variant = ref Syntax.Abstract;;
