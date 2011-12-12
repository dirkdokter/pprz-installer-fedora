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


open Protocol;;
(* Implementation of the tk_optionMenu *)

let create ?name parent variable values =
  let w = Widget.new_atom "menubutton" ~parent ?name in
  let mw = Widget.new_atom "menu" ~parent:w ~name:"menu" in
  let res =
    tkEval [|TkToken "tk_optionMenu";
             TkToken (Widget.name w);
             cCAMLtoTKtextVariable variable;
             TkTokenList (List.map (function x -> TkToken x) values)|] in
  if res <> Widget.name mw then
    raise (TkError "internal error in Optionmenu.create")
  else
    w,mw
;;

let create_named parent name variable values =
  let w = Widget.new_atom "menubutton" ~parent ~name in
  let mw = Widget.new_atom "menu" ~parent:w ~name: "menu" in
  let res =
    tkEval [|TkToken "tk_optionMenu";
             TkToken (Widget.name w);
             cCAMLtoTKtextVariable variable;
             TkTokenList (List.map (function x -> TkToken x) values)|] in
  if res <> Widget.name mw then
    raise (TkError "internal error in Optionmenu.create")
  else
    w,mw
;;


