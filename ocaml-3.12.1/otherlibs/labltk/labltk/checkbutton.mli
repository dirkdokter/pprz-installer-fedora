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
(* The checkbutton widget *)
open StdLabels
open Tk
open Tkintf
open Widget
open Textvariable

val create :
  ?name:string ->
  ?activebackground:color ->
  ?activeforeground:color ->
  ?anchor:anchor ->
  ?background:color ->
  ?bitmap:bitmap ->
  ?borderwidth:int ->
  ?command:(unit -> unit) ->
  ?cursor:cursor ->
  ?disabledforeground:color ->
  ?font:string ->
  ?foreground:color ->
  ?height:int ->
  ?highlightbackground:color ->
  ?highlightcolor:color ->
  ?highlightthickness:int ->
  ?image:[< image] ->
  ?indicatoron:bool ->
  ?justify:justification ->
  ?offvalue:string ->
  ?onvalue:string ->
  ?padx:int ->
  ?pady:int ->
  ?relief:relief ->
  ?selectcolor:color ->
  ?selectimage:[< image] ->
  ?state:state ->
  ?takefocus:bool ->
  ?text:string ->
  ?textvariable:textVariable ->
  ?underline:int ->
  ?variable:textVariable ->
  ?width:int ->
  ?wraplength:int ->
  'a widget -> checkbutton widget
(** [create ?name parent options...] creates a new widget with
    parent [parent] and new patch component [name], if specified. *)

val configure : ?activebackground:color   ->
?activeforeground:color   ->
?anchor:anchor   ->
?background:color   ->
?bitmap:bitmap   ->
?borderwidth:int   ->
?command:(unit -> unit)   ->
?cursor:cursor   ->
?disabledforeground:color   ->
?font:string   ->
?foreground:color   ->
?height:int   ->
?highlightbackground:color   ->
?highlightcolor:color   ->
?highlightthickness:int   ->
?image:[< image]   ->
?indicatoron:bool   ->
?justify:justification   ->
?offvalue:string   ->
?onvalue:string   ->
?padx:int   ->
?pady:int   ->
?relief:relief   ->
?selectcolor:color   ->
?selectimage:[< image]   ->
?state:state   ->
?takefocus:bool   ->
?text:string   ->
?textvariable:textVariable   ->
?underline:int   ->
?variable:textVariable   ->
?width:int   ->
?wraplength:int -> checkbutton widget -> unit 

val configure_get : checkbutton widget -> string 

val deselect : checkbutton widget -> unit 

val flash : checkbutton widget -> unit 

val invoke : checkbutton widget -> unit 

val select : checkbutton widget -> unit 

val toggle : checkbutton widget -> unit 

