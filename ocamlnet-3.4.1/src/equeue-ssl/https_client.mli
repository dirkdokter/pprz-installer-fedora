(* $Id: https_client.mli 1614 2011-06-09 15:08:56Z gerd $ *)

(** HTTPS extension to {!Http_client} *)

type channel_binding_id = int
(** Same as {!Http_client.channel_binding_id} *)	  

class type transport_channel_type =
object
  method setup_e : Unix.file_descr -> channel_binding_id -> float -> exn -> 
                   string -> int -> Unixqueue.event_system ->
                   Uq_engines.multiplex_controller Uq_engines.engine
  method continue : Unix.file_descr -> channel_binding_id -> float -> exn ->
                   string -> int -> Unixqueue.event_system ->
                   Uq_engines.multiplex_controller
end
(** Same as {!Http_client.transport_channel_type} *)	  

val https_transport_channel_type : Ssl.context -> transport_channel_type
  (** Configures a TLS tunnel for this context *)

(** {2 How to configure a pipeline for TLS}

    Just follow this recipe:

    1. Create the [Ssl] context:

    {[ Ssl.init() ]}

    {[ let ctx = Ssl.create_context Ssl.TLSv1 Ssl.Client_context ]}

    2. Create the transport channel type:

    {[ let tct = Https_client.https_transport_channel_type ctx ]}

    3. Configure the transport:

    {[ pipeline # configure_transport Http_client.https_cb_id tct ]}

    Now all URLs starting with "https://" will use this transport.
    If you need more control about the type of SSL/TLS channel, you
    can create new channel binding IDs, and configure these in addition.
    For each message needing a specific context, just set the
    channel binding ID (method [set_channel_binding] of the message).
 *)

(** {2 How to configure the Convenience module}

    Just do once:

    {[
    Ssl.init();
    Http_client.Convenience.configure_pipeline
      (fun p ->
         let ctx = Ssl.create_context Ssl.TLSv1 Ssl.Client_context in
         let tct = Https_client.https_transport_channel_type ctx in
         p # configure_transport Http_client.https_cb_id tct
      )
    ]}

    This will enable "https" for the functions in {!Http_client.Convenience},
    e.g. {[ let data = Http_client.Convenience.http_get "https://url" ]}

 *)

(** {2 How to configure {!Http_fs}}

    Just do once:

    {[
    Ssl.init()
    ]}

    and create the [http_fs] object with

    {[
    Http_fs.http_fs 
      ~config_pipeline:(
        fun p ->
	  let ctx = Ssl.create_context Ssl.TLSv1 Ssl.Client_context in
	  let tct = Https_client.https_transport_channel_type ctx in
	  p # configure_transport Http_client.https_cb_id tct
      )
      "https://root-url"
    ]}

 *)


(** {2 Features and limitations} 

    We only implement RFC 2618, i.e. secure connections on a separate
    port (443 instead of 80). There is no support (yet) for RFC 2617,
    i.e. upgrading an existing insecure connection to a secure one.

    If an HTTP proxy server is configured, the TLS connection is established
    via the CONNECT method (documented in RFC 2617).

    Alternatively, it is also possible to connect via SOCKS version 5
    proxies.

    There is, so far, no support for reusing TLS sessions across connections.
    For every connection a new TLS session is created.
 *)
