(* $Id: num_top_printers.mli 49 2003-12-30 09:48:02Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

(**
  Printers for types defined in the "num" library. Meant to be used as printers
  in the ocaml toplevel. See num_top.mli.

  Copyright (C) 2003  Stefano Zacchiroli <zack@debian.org>

  This is free software! you can redistribute it and/or modify it under the
  terms of the GNU Lesser General Public License as published by the Free
  Software Foundation; either version 2.1 of the License, or (at your option)
  any later version.
*)

val nat_printer : Format.formatter -> Nat.nat -> unit
val big_int_printer : Format.formatter -> Big_int.big_int -> unit
val ratio_printer : Format.formatter -> Ratio.ratio -> unit
val num_printer: Format.formatter -> Num.num -> unit

