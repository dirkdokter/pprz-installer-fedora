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
(** This module Labltk provides the module name spaces of the LablTk API,
useful to call LablTk functions inside CamlTk programs. 100% LablTk users
do not need to use this. *)

module Widget = Widget;;
module Protocol = Protocol;;
module Textvariable = Textvariable;;
module Fileevent = Fileevent;;
module Timer = Timer;;
module Place = Place;;
module Wm = Wm;;
module Imagephoto = Imagephoto;;
module Canvas = Canvas;;
module Button = Button;;
module Text = Text;;
module Label = Label;;
module Scrollbar = Scrollbar;;
module Image = Image;;
module Encoding = Encoding;;
module Pixmap = Pixmap;;
module Palette = Palette;;
module Font = Font;;
module Message = Message;;
module Menu = Menu;;
module Entry = Entry;;
module Listbox = Listbox;;
module Focus = Focus;;
module Menubutton = Menubutton;;
module Pack = Pack;;
module Option = Option;;
module Toplevel = Toplevel;;
module Frame = Frame;;
module Dialog = Dialog;;
module Imagebitmap = Imagebitmap;;
module Clipboard = Clipboard;;
module Radiobutton = Radiobutton;;
module Tkwait = Tkwait;;
module Grab = Grab;;
module Selection = Selection;;
module Scale = Scale;;
module Optionmenu = Optionmenu;;
module Winfo = Winfo;;
module Grid = Grid;;
module Checkbutton = Checkbutton;;
module Bell = Bell;;
module Tkvars = Tkvars;;

(** Widget typers *)

open Widget

let canvas (w : any widget) =
  Rawwidget.check_class w widget_canvas_table;
  (Obj.magic w : canvas widget);;

let button (w : any widget) =
  Rawwidget.check_class w widget_button_table;
  (Obj.magic w : button widget);;

let text (w : any widget) =
  Rawwidget.check_class w widget_text_table;
  (Obj.magic w : text widget);;

let label (w : any widget) =
  Rawwidget.check_class w widget_label_table;
  (Obj.magic w : label widget);;

let scrollbar (w : any widget) =
  Rawwidget.check_class w widget_scrollbar_table;
  (Obj.magic w : scrollbar widget);;

let message (w : any widget) =
  Rawwidget.check_class w widget_message_table;
  (Obj.magic w : message widget);;

let menu (w : any widget) =
  Rawwidget.check_class w widget_menu_table;
  (Obj.magic w : menu widget);;

let entry (w : any widget) =
  Rawwidget.check_class w widget_entry_table;
  (Obj.magic w : entry widget);;

let listbox (w : any widget) =
  Rawwidget.check_class w widget_listbox_table;
  (Obj.magic w : listbox widget);;

let menubutton (w : any widget) =
  Rawwidget.check_class w widget_menubutton_table;
  (Obj.magic w : menubutton widget);;

let toplevel (w : any widget) =
  Rawwidget.check_class w widget_toplevel_table;
  (Obj.magic w : toplevel widget);;

let frame (w : any widget) =
  Rawwidget.check_class w widget_frame_table;
  (Obj.magic w : frame widget);;

let radiobutton (w : any widget) =
  Rawwidget.check_class w widget_radiobutton_table;
  (Obj.magic w : radiobutton widget);;

let scale (w : any widget) =
  Rawwidget.check_class w widget_scale_table;
  (Obj.magic w : scale widget);;

let checkbutton (w : any widget) =
  Rawwidget.check_class w widget_checkbutton_table;
  (Obj.magic w : checkbutton widget);;

