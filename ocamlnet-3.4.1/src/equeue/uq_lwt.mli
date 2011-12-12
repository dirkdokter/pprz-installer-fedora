(* $Id: uq_lwt.mli 1616 2011-06-10 15:08:57Z gerd $ *)

(** Compatibility with [Lwt] *)

(** Lwt is another library for event-driven programming. Here are some
    helpers for running Lwt code on top of Ocamlnet event queues.

    This is for Lwt-2.3 or better.
 *)

(** Adapter for turning an Ocamlnet [event_system] into an Lwt [Lwt_engine.t].

    Use it like:

    {[
       class lwt_engine esys =
       object
         inherit Lwt_engine.abstract
         inherit Uq_lwt.lwt_backend esys
       end
    ]}

    (We've intentionally left out {b this} definition to avoid any 
    build dependency on Lwt. Also note that [Lwt_engine] is in the
    package [lwt.unix].)

    Now, activate this Lwt engine (event loop):

    {[
      Lwt_engine.set (new lwt_engine esys)
    ]}

    Note that Lwt can only deal with one event loop at a time, and the
    new event loop will be used for all Lwt code.

    It is, unfortunately, necessary that you use the Lwt main loop
    ([Lwt_main.run] or [Lwt_unix.run]), because otherwise some hook
    functions are never executed (and execution will hang).

    For an example, see [tests/equeue/manual/relay.ml] in the distribution
    tarball.
 *)
class lwt_backend : Unixqueue.event_system ->
  object
      method iter : bool -> unit
      method private cleanup : unit
      method private register_readable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
      method private register_writable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
      method private register_timer : float -> bool -> (unit -> unit) -> unit Lazy.t
    end
 
