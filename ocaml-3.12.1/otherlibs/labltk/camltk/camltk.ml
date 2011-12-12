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
(** This module Camltk provides the module name spaces of the CamlTk API.

The users of the CamlTk API should open this module first to access
the types, functions and modules of the CamlTk API easier.
For the documentation of each sub modules such as [Button] and [Toplevel],
refer to its defintion file,  [cButton.mli], [cToplevel.mli], etc.
*)

include CTk
module Tk = CTk
module Place = CPlace;;
module Resource = CResource;;
module Wm = CWm;;
module Imagephoto = CImagephoto;;
module Canvas = CCanvas;;
module Button = CButton;;
module Text = CText;;
module Label = CLabel;;
module Scrollbar = CScrollbar;;
module Image = CImage;;
module Encoding = CEncoding;;
module Pixmap = CPixmap;;
module Palette = CPalette;;
module Font = CFont;;
module Message = CMessage;;
module Menu = CMenu;;
module Entry = CEntry;;
module Listbox = CListbox;;
module Focus = CFocus;;
module Menubutton = CMenubutton;;
module Pack = CPack;;
module Option = COption;;
module Toplevel = CToplevel;;
module Frame = CFrame;;
module Dialog = CDialog;;
module Imagebitmap = CImagebitmap;;
module Clipboard = CClipboard;;
module Radiobutton = CRadiobutton;;
module Tkwait = CTkwait;;
module Grab = CGrab;;
module Selection = CSelection;;
module Scale = CScale;;
module Optionmenu = COptionmenu;;
module Winfo = CWinfo;;
module Grid = CGrid;;
module Checkbutton = CCheckbutton;;
module Bell = CBell;;
module Tkvars = CTkvars;;
