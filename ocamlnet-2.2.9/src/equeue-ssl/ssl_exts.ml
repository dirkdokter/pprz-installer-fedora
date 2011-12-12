(* $Id: ssl_exts.ml 919 2006-06-15 12:32:17Z gerd $ *)

exception Shutdown_error of Ssl.ssl_error

let _ =
  Callback.register_exception "ssl_exn_shutdown_error" 
    (Shutdown_error Ssl.Error_none)

external get_shutdown : Ssl.socket -> bool * bool = "ocaml_ssl_get_shutdown"

external get_rbio_eof : Ssl.socket -> bool = "ocaml_ssl_get_rbio_eof"

external single_shutdown : Ssl.socket -> unit = "ocaml_ssl_single_shutdown"

type ssl_mode =
    { enable_partial_write : bool;
      accept_moving_write_buffer : bool;
      auto_retry : bool;
    }

external get_mode : Ssl.socket -> ssl_mode = "ocaml_ssl_get_mode"

external set_mode : Ssl.socket -> ssl_mode -> unit = "ocaml_ssl_set_mode"

external single_read : Ssl.socket -> string -> int -> int -> int
  = "ocaml_ssl_read"

external single_write : Ssl.socket -> string -> int -> int -> int 
  = "ocaml_ssl_write"

