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


let cTKtoCAMLimage s =
  let res = tkEval [|TkToken "image"; TkToken "type"; TkToken s|] in
  match res with
  | "bitmap" -> ImageBitmap (BitmapImage s)
  | "photo" -> ImagePhoto (PhotoImage s)
  | _ -> raise (TkError ("unknown image type \"" ^ res ^ "\""))
;;

let names () =
  let res = tkEval [|TkToken "image"; TkToken "names"|] in
  let names = splitlist res in
  List.map cTKtoCAMLimage names
;;


