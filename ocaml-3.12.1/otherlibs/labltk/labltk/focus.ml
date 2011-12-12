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
let displayof v1 =
let res = tkEval [|TkToken "focus";
    TkToken "-displayof";
    cCAMLtoTKwidget v1|] in 
cTKtoCAMLwidget res

let follows_mouse () =
tkCommand [|TkToken "tk_focusFollowsMouse"|]

let force v1 =
tkCommand [|TkToken "focus";
    TkToken "-force";
    cCAMLtoTKwidget v1|]

let get ?displayof:v1 () =
let res = tkEval [|TkToken "focus";
    TkTokenList (match v1 with
 | Some v1 -> [TkToken "-displayof"; cCAMLtoTKwidget v1]
 | None -> [])|] in 
cTKtoCAMLwidget res

let lastfor v1 =
let res = tkEval [|TkToken "focus";
    TkToken "-lastfor";
    cCAMLtoTKwidget v1|] in 
cTKtoCAMLwidget res

let next v1 =
let res = tkEval [|TkToken "tk_focusNext";
    cCAMLtoTKwidget v1|] in 
cTKtoCAMLwidget res

let prev v1 =
let res = tkEval [|TkToken "tk_focusPrev";
    cCAMLtoTKwidget v1|] in 
cTKtoCAMLwidget res

let set v1 =
tkCommand [|TkToken "focus";
    cCAMLtoTKwidget v1|]

