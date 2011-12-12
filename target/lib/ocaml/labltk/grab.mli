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
(* The grab commands  *)
open StdLabels
open Tk
open Tkintf
open Widget
open Textvariable

(* unsafe *)
val current : ?displayof:'a widget -> unit -> any widget list 

(* /unsafe *)
val release : 'a widget -> unit 

val set : ?global:grabGlobal -> 'a widget -> unit 

val status : 'a widget -> grabStatus 

