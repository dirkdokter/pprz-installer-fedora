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
external rawget : string -> string
    = "camltk_getimgdata"
external rawset : string -> string -> int -> int -> int -> int -> unit
    = "camltk_setimgdata_bytecode"  (* all int parameters MUST be positive *)
      "camltk_setimgdata_native"

type t = {
  pixmap_width : int;
  pixmap_height: int;
  pixmap_data: string
}

type pixel = string  (* 3 chars *)

(* pixmap will be an abstract type *)
let width pix = pix.pixmap_width
let height pix = pix.pixmap_height


(* note: invalid size would have been caught by String.create, but we put
 * it here for documentation purpose *)
let create w h =
  if w < 0 || h < 0 then invalid_arg "invalid size"
  else {
    pixmap_width = w;
    pixmap_height = h;
    pixmap_data = String.create (w * h * 3);
  }

(*
 * operations on pixmaps
 *)
let unsafe_copy pix_from pix_to =
  String.unsafe_blit pix_from.pixmap_data 0
                     pix_to.pixmap_data 0
                     (String.length pix_from.pixmap_data)

(* We check only the length. w,h might be different... *)
let copy pix_from pix_to =
  let l = String.length pix_from.pixmap_data in
  if l <> String.length pix_to.pixmap_data then
    raise (Invalid_argument "copy: incompatible length")
  else unsafe_copy pix_from pix_to


(* Pixel operations *)
let unsafe_get_pixel pixmap x y =
  let pos = (y * pixmap.pixmap_width + x) * 3 in
  let r = String.create 3 in
  String.unsafe_blit pixmap.pixmap_data pos r 0 3;
  r

let unsafe_set_pixel pixmap x y pixel =
  let pos = (y * pixmap.pixmap_width + x) * 3 in
  String.unsafe_blit pixel 0 pixmap.pixmap_data pos 3

(* To get safe operations, we can either check x,y wrt [0,w[ and [0,h[
   or rely on blit checking. We choose the first for clarity.
 *)
let get_pixel pix x y =
  if x < 0 || y < 0 || x >= pix.pixmap_width || y >= pix.pixmap_height
  then invalid_arg "invalid pixel"
  else unsafe_get_pixel pix x y

(* same check (pixel being abstract, it must be of good size *)
let set_pixel pix x y pixel =
  if x < 0 || y < 0 || x >= pix.pixmap_width || y >= pix.pixmap_height
  then invalid_arg "invalid pixel"
  else unsafe_set_pixel pix x y pixel

(* black as default_color, if at all needed *)
let default_color = "\000\000\000"

(* Char.chr does range checking *)
let pixel r g b =
  let s = String.create 3 in
  s.[0] <- Char.chr r;
  s.[1] <- Char.chr g;
  s.[2] <- Char.chr b;
  s



(* create pixmap from an existing image *)
let get photo =
  match photo with
  | `Photo s -> {
      pixmap_width = Imagephoto.width photo;
      pixmap_height = Imagephoto.height photo;
      pixmap_data = rawget s;
    }

(* copy a full pixmap into an image *)
let set photo pix =
  match photo with
  | `Photo s -> rawset s pix.pixmap_data 0 0 pix.pixmap_width pix.pixmap_height

(* general blit of pixmap into image *)
let blit photo pix x y w h =
  if x < 0 || y < 0 || w < 0 || h < 0 then invalid_arg "negative argument"
  else match photo with
  | `Photo s -> rawset s pix.pixmap_data x y w h

(* get from a file *)
let from_file filename =
  let img = Imagephoto.create ~file: filename () in
  let pix = get img in
  Imagephoto.delete img;
  pix


