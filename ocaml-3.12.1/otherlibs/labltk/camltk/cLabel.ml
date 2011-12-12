(***********************************************************************)
(*                                                                     *)
(*                 MLTk, Tcl/Tk interface of Objective Caml            *)
(*                                                                     *)
(*    Francois Rouaix, Francois Pessaux, Jun Furuse and Pierre Weis    *)
(*               projet Cristal, INRIA Rocquencourt                    *)
(*            Jacques Garrigue, Kyoto University RIMS                  *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique and Kyoto University.  All rights reserved.         *)
(*  This file is distributed under the terms of the GNU Library        *)
(*  General Public License, with the special exception on linking      *)
(*  described in file LICENSE found in the Objective Caml source tree. *)
(*                                                                     *)
(***********************************************************************)
open CTk
open Tkintf
open Widget
open Textvariable

open Protocol
let create ?name parent options =
  let w = new_atom "label" ~parent ?name in
  tkCommand [|TkToken "label";
              TkToken (Widget.name w);
              TkTokenList (List.map (function x -> cCAMLtoTKoptions w options_label_table x) options)
             |];
      w

let create_named parent name options =
  let w = new_atom "label" ~parent ~name in
  tkCommand [|TkToken "label";
              TkToken (Widget.name w);
              TkTokenList (List.map (function x -> cCAMLtoTKoptions w options_label_table x) options)
             |];
      w

let configure v1 v2 =
tkCommand [|cCAMLtoTKwidget widget_label_table v1;
    TkToken "configure";
    TkTokenList (List.map (function x -> cCAMLtoTKoptions v1 options_label_table x) v2)|]

let configure_get v1 =
let res = tkEval [|cCAMLtoTKwidget widget_label_table v1;
    TkToken "configure"|] in 
res

