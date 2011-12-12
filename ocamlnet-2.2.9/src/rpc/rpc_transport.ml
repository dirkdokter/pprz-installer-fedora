(* $Id: rpc_transport.ml 1123 2007-05-06 21:27:19Z gerd $
 * ----------------------------------------------------------------------
 *
 *)

open Rpc
open Rpc_packer


type 't result =
    [ `Ok of 't
    | `Error of exn
    ]

type 't result_eof =
    [ 't result
    | `End_of_file
    ]


type sockaddr =
    [ `Implied
    | `Sockaddr of Unix.sockaddr
    ]

exception Error of string

class type rpc_multiplex_controller =
object
  method alive : bool
  method event_system : Unixqueue.event_system
  method getsockname : sockaddr
  method getpeername : sockaddr
  method peer_user_name : string option
  method protocol : protocol
  method reading : bool
  method read_eof : bool
  method start_reading : 
    ?peek: (unit -> unit) ->
    ?before_record:( int -> sockaddr -> unit ) ->
    when_done:( (packed_value * sockaddr) result_eof -> unit) -> unit -> unit
  method cancel_rd_polling : unit -> unit
  method abort_rw : unit -> unit
  method skip_message : unit -> unit
  method writing : bool
  method start_writing :
    when_done:(unit result -> unit) -> packed_value -> sockaddr -> unit
  method start_shutting_down :
    when_done:(unit result -> unit) -> unit -> unit
  method cancel_shutting_down : unit -> unit
  method set_timeout : notify:(unit -> unit) -> float -> unit
  method inactivate : unit -> unit
end


class datagram_rpc_multiplex_controller sockname peername_opt peer_user_name_opt
        (mplex : Uq_engines.datagram_multiplex_controller) esys 
      : rpc_multiplex_controller =
object(self)
  val rd_buffer = String.create 16384
    (* Max. size of an Internet datagram is 64 K. See RFC 760. However,
     * the Unix library uses a buffer size of only 16 K. Longer messages
     * can neither be received nor sent without truncation.
     *)

  method alive = mplex # alive
  method event_system = esys
  method getsockname = sockname
  method getpeername = 
    match peername_opt with
      | None -> failwith "#getpeername: not connected"
      | Some a -> a
  method protocol = Udp
  method peer_user_name = peer_user_name_opt
  method reading = mplex # reading
  method read_eof = mplex # read_eof
  method writing = mplex # writing

  val mutable aborted = false
  val mutable skip_message = false

  method start_reading ?peek ?before_record ~when_done () =
    mplex # start_reading
      ?peek
      ~when_done:(fun exn_opt n ->
		    self # timer_event `Stop `R;
		    match exn_opt with
		      | None ->
			  let peer = `Sockaddr (mplex # received_from) in
			  if not skip_message then (
			    match before_record with
			      | None -> ()
			      | Some f -> 
				  f n peer
				    (* It can happen that reading is
                                     * aborted in the meantime!
                                     *)
			  );
			  if not aborted then (
			    if skip_message then
			      skip_message <- false
			    else
			      let pv = 
				packed_value_of_string 
				  (String.sub rd_buffer 0 n) in
			      when_done (`Ok(pv, peer))
			  )
		      | Some End_of_file ->
			  assert false
		      | Some Uq_engines.Cancelled ->
			  ()   (* Ignore *)
		      | Some error ->
			  when_done (`Error error)
		    )
      rd_buffer
      0
      (String.length rd_buffer);
    self # timer_event `Start `R
  
  method start_writing ~when_done pv addr =
    ( match addr with
	| `Implied ->
	    failwith "Rpc_transport.datagram_rpc_multiplex_controller: Cannot send datagram to implied address"
	| `Sockaddr a ->
	    mplex # send_to a
    );
    let s = string_of_packed_value pv in
    mplex # start_writing
      ~when_done:(fun exn_opt n ->
		    self # timer_event `Stop `W;
		    match exn_opt with
		      | None ->
			  if n = String.length s then
			    when_done (`Ok ())
			  else
			    when_done (`Error (Error "Datagram too large"))
		      | Some Uq_engines.Cancelled ->
			  ()  (* ignore *)
		      | Some error ->
			  when_done (`Error error)
		 )
      s
      0
      (String.length s);
    self # timer_event `Start `W

  method cancel_rd_polling () =
    if mplex#reading then
      mplex # cancel_reading()

  method skip_message () =
    skip_message <- true

  method abort_rw () =
    aborted <- true;
    mplex # cancel_reading();
    mplex # cancel_writing()
    
  method start_shutting_down ~when_done () =
    mplex # start_shutting_down
      ~when_done:(fun exn_opt ->
		    self # timer_event `Stop `D;
		    match exn_opt with
		      | None -> when_done (`Ok ())
		      | Some error -> when_done (`Error error)
		 )
      ();
    self # timer_event `Start `D

  method cancel_shutting_down () =
    self # timer_event `Stop `D;
    mplex # cancel_shutting_down()

  method inactivate () =
    self # stop_timer();
    mplex # inactivate()

  val mutable timer = None
  val mutable timer_r = `Stop
  val mutable timer_w = `Stop
  val mutable timer_d = `Stop
  val mutable timer_group = None

  method set_timeout ~notify tmo =
    timer <- Some(notify, tmo)

  method private timer_event start_stop which =
    ( match timer with
	| None -> ()
	| Some(notify, tmo) ->
	    ( match which with
		| `R -> timer_r <- start_stop
		| `W -> timer_w <- start_stop
		| `D -> timer_d <- start_stop
	    );
	    self # stop_timer();
	    if timer_r = `Start || timer_w = `Start || timer_d = `Start then (
	      let g = Unixqueue.new_group esys in
	      timer_group <- Some g;
	      Unixqueue.once esys g tmo
		(fun () -> 
		   timer_group <- None;
		   notify()
		)
	    );
    )


  method private stop_timer() =
    ( match timer_group with
	| None -> ()
	| Some g -> Unixqueue.clear esys g
    );
    timer_group <- None;
    timer_r <- `Stop;
    timer_w <- `Stop;
    timer_d <- `Stop


end



let datagram_rpc_multiplex_controller ?(close_inactive_descr=true) fd esys =
  let sockname = 
    try
      `Sockaddr(Unix.getsockname fd) 
    with
	(* The OCaml runtime sometimes returns EAFNOSUPPORT when asked
           for inaccessible socket names. EOPNOTSUPP is documented
           by SUS.
         *)
      | Unix.Unix_error((Unix.EAFNOSUPPORT|Unix.EOPNOTSUPP),_,_) -> `Implied in
  let peername_opt =
    try Some(`Sockaddr(Unix.getpeername fd))
    with
      | Unix.Unix_error((Unix.EAFNOSUPPORT|Unix.EOPNOTSUPP),_,_) -> 
	  Some `Implied
      | Unix.Unix_error(Unix.ENOTCONN,_,_) -> 
	  (* ENOTCONN is special because we allow to set the peer address
             per datagram in this case!
           *)
	  None in
  let mplex = 
    Uq_engines.create_multiplex_controller_for_datagram_socket
      ~close_inactive_descr
      fd esys in
  new datagram_rpc_multiplex_controller sockname peername_opt None mplex esys
;;


class stream_rpc_multiplex_controller sockname peername peer_user_name_opt
        (mplex : Uq_engines.multiplex_controller) esys 
      : rpc_multiplex_controller =
object(self)
  val mutable wr_buffer = None
  val mutable wr_buffer_pos = 0

  val mutable rd_buffer = String.create 16384

  val mutable rm_buffer = String.create 4
  val mutable rm_buffer_len = 0
  val mutable rm = 0
  val mutable rm_last = false

  val mutable rd_mode = `RM
  val mutable rd_fragment = ""
  val mutable rd_fragment_len = 0
  val mutable rd_queue = Queue.create()
  val mutable rd_queue_len = 0

  val mutable rd_continuation = None

  method alive = mplex # alive
  method event_system = esys
  method getsockname = sockname
  method getpeername = peername
  method protocol = Tcp
  method peer_user_name = peer_user_name_opt
  method reading = mplex # reading
  method read_eof = mplex # read_eof
  method writing = mplex # writing

  val mutable aborted = false
  val mutable skip_message = false

  method start_reading ?peek ?(before_record = fun _ _ -> ()) ~when_done () =
    let rec est_reading() =
      rd_continuation <- None;
      mplex # start_reading
	?peek
	~when_done:(fun exn_opt n ->
		      self # timer_event `Stop `R;
		      match exn_opt with
			| None ->
			    process 0 n
			| Some End_of_file ->
			    if rd_mode = `RM && rd_fragment_len = 0 then
			      return_eof()   (* EOF between messages *)
			    else
			      return_error (Error "EOF within message")
			| Some Uq_engines.Cancelled ->
			    ()   (* Ignore *)
			| Some error ->
			    return_error error
		   )
	rd_buffer
	0
	(String.length rd_buffer);
      self # timer_event `Start `R

    and process pos len =
      if len > 0 then (
	match rd_mode with
	  | `RM ->
	      (* Read the record marker *)
	      let m = min (4 - rm_buffer_len) len in
	      String.blit rd_buffer pos rm_buffer rm_buffer_len m;
	      rm_buffer_len <- rm_buffer_len + m;
	      if rm_buffer_len = 4 then (
		rm_last <- (Char.code rm_buffer.[0]) >= 128;
		let rm_0 = (Char.chr ((Char.code rm_buffer.[0]) land 0x7f)) in
		let ok =
		  try
		    rm <-
		      Rtypes.int_of_uint4
		      (Rtypes.mk_uint4 
			 (rm_0,rm_buffer.[1],rm_buffer.[2],rm_buffer.[3]));
		    if rm > Sys.max_string_length then
		      raise(Rtypes.Cannot_represent "");
		    if rd_queue_len + rm > Sys.max_string_length then
		      raise(Rtypes.Cannot_represent "");
		    true
		  with
		    | Rtypes.Cannot_represent _ -> false in
		rd_mode <- `Payload;
		rd_fragment <- String.create rm;
		rd_fragment_len <- 0;
		if ok then (
		  before_record (rd_queue_len + rm) `Implied;
		  process (pos+m) (len-m)
		)
		else
		  return_error (Error "Record too large")
	      )
	      else
		est_reading()
		
	  | `Payload ->
	      (* Read payload data *)
	      let m = min (rm - rd_fragment_len) len in
	      String.blit rd_buffer pos rd_fragment rd_fragment_len m;
	      rd_fragment_len <- rd_fragment_len + m;
	      if rd_fragment_len = rm then (
		let last = rm_last in
		if not skip_message then
		  Queue.push rd_fragment rd_queue;
		rd_queue_len <- rd_queue_len + rd_fragment_len;
		rd_fragment <- "";
		rd_fragment_len <- 0;
		rm_buffer_len <- 0;
		rd_mode <- `RM;
		if last then (
		  if skip_message then (
		    skip_message <- false;
		    process (pos+m) (len-m)
		  )
		  else (
		    let msg = String.create rd_queue_len in
		    let p = ref 0 in
		    Queue.iter
		      (fun s ->
			 String.blit s 0 msg !p (String.length s);
			 p := !p + String.length s)
		      rd_queue;
		    Queue.clear rd_queue;
		    rd_queue_len <- 0;
		    rd_continuation <- 
		      Some (fun () -> process (pos+m) (len-m));
		    return_msg msg
		  )
		)
		else
		  process (pos+m) (len-m)
	      )
	      else
		est_reading()
      )
      else
	est_reading()

    and return_msg msg =
      if not aborted then (
	let pv = packed_value_of_string msg in
	when_done (`Ok(pv, peername))
      )

    and return_error e =
      rd_continuation <- None;
      if not aborted then
	when_done (`Error e)

    and return_eof () =
      rd_continuation <- None;
      if not aborted then
	when_done `End_of_file 

    in
    match rd_continuation with
      | None ->
	  est_reading()
      | Some f ->
	  f()


  method start_writing ~when_done pv addr =
    let rec est_writing s pos =
      let len = String.length s - pos in
      mplex # start_writing
	~when_done:(fun exn_opt n ->
		      self # timer_event `Stop `W;
		      match exn_opt with
			| None ->
			    assert(n <= len);
			    if n = len then (
			      if not aborted then
				when_done (`Ok ())
			    )
			    else (
			      if not aborted then
				est_writing s (pos+n)
			    )
			| Some Uq_engines.Cancelled ->
			    ()  (* ignore *)
			| Some error ->
			    if not aborted then
			      when_done (`Error error)
		   )
	s
	pos
	(String.length s - pos);
      self # timer_event `Start `W
    in

    ( match addr with
	| `Implied -> ()
	| `Sockaddr a ->
	    if addr <> peername then
	      failwith "Rpc_transport.stream_rpc_multiplex_controller: cannot send to this address"
    );
    let s = rm_string_of_packed_value pv in
    (* Patch record marker at the beginning of [s] *)
    let rm = Rtypes.uint4_of_int (String.length s - 4) in
    Rtypes.write_uint4 s 0 rm;
    s.[0] <- Char.chr (Char.code s.[0] lor 0x80);
    est_writing s 0


  method cancel_rd_polling () =
    if mplex#reading then
      mplex # cancel_reading()

  method skip_message () =
    Queue.clear rd_queue;
    rd_queue_len <- 0;
    skip_message <- true

  method abort_rw () =
    aborted <- true;
    mplex # cancel_reading();
    mplex # cancel_writing()
    
  method start_shutting_down ~when_done () =
    mplex # start_shutting_down
      ~when_done:(fun exn_opt ->
		    self # timer_event `Stop `D;
		    match exn_opt with
		      | None -> when_done (`Ok ())
		      | Some error -> when_done (`Error error)
		 )
      ();
    self # timer_event `Start `D

  method cancel_shutting_down () =
    self # timer_event `Stop `D;
    mplex # cancel_shutting_down()

  method inactivate () =
    self # stop_timer();
    mplex # inactivate()

  val mutable timer = None
  val mutable timer_r = `Stop
  val mutable timer_w = `Stop
  val mutable timer_d = `Stop
  val mutable timer_group = None

  method set_timeout ~notify tmo =
    timer <- Some(notify, tmo)

  method private timer_event start_stop which =
    ( match timer with
	| None -> ()
	| Some(notify, tmo) ->
	    ( match which with
		| `R -> timer_r <- start_stop
		| `W -> timer_w <- start_stop
		| `D -> timer_d <- start_stop
	    );
	    self # stop_timer();
	    if timer_r = `Start || timer_w = `Start || timer_d = `Start then (
	      let g = Unixqueue.new_group esys in
	      timer_group <- Some g;
	      Unixqueue.once esys g tmo
		(fun () -> 
		   timer_group <- None;
		   notify()
		)
	    );
    )


  method private stop_timer() =
    ( match timer_group with
	| None -> ()
	| Some g -> Unixqueue.clear esys g
    );
    timer_group <- None;
    timer_r <- `Stop;
    timer_w <- `Stop;
    timer_d <- `Stop

end



let stream_rpc_multiplex_controller ?(close_inactive_descr=true) fd esys =
  let sockname = 
    try
      `Sockaddr(Unix.getsockname fd) 
    with
	(* The OCaml runtime sometimes returns EAFNOSUPPORT when asked
           for inaccessible socket names. EOPNOTSUPP is documented
           by SUS. We also catch ENOTSOCK to allow using RPC with
           bidirectional pipes that are not socket-based (i.e. SysV
           bidirectional pipes).
         *)
      | Unix.Unix_error((Unix.EAFNOSUPPORT|Unix.EOPNOTSUPP|Unix.ENOTSOCK),
			_,_) -> `Implied in
  let peername = 
    try
      `Sockaddr(Unix.getpeername fd)
    with
	(* also catching ENOTCONN - which might happen for strange socket
           implementations
         *)
      | Unix.Unix_error((Unix.EAFNOSUPPORT|Unix.EOPNOTSUPP|Unix.ENOTSOCK|Unix.ENOTCONN),
			_,_) -> `Implied in
  let mplex = 
    Uq_engines.create_multiplex_controller_for_connected_socket
      ~close_inactive_descr
      fd esys in
  new stream_rpc_multiplex_controller sockname peername None mplex esys
;;
