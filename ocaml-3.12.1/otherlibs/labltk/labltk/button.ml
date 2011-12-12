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
open StdLabels
open Tk
open Tkintf
open Widget
open Textvariable

open Protocol
let create ?name =
  button_options_optionals (fun opts parent ->
     let w = new_atom "button" ~parent ?name in
     tkCommand [|TkToken "button";
              TkToken (Widget.name w);
              TkTokenList opts |];
      w)


let configure ?activebackground:eta =
button_options_optionals ?activebackground:eta (fun opts v1 ->
tkCommand [|cCAMLtoTKwidget (v1 : button widget);
    TkToken "configure";
    TkTokenList opts|])

let configure_get v1 =
let res = tkEval [|cCAMLtoTKwidget (v1 : button widget);
    TkToken "configure"|] in 
res

let flash v1 =
tkCommand [|cCAMLtoTKwidget (v1 : button widget);
    TkToken "flash"|]

let invoke v1 =
tkCommand [|cCAMLtoTKwidget (v1 : button widget);
    TkToken "invoke"|]

