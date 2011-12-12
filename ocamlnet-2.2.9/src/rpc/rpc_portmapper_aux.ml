(************************************************************
 * WARNING!
 *
 * This file is generated by ocamlrpcgen from the source file
 * rpc_portmapper.x
 *
 ************************************************************)
type mapping = 
      { 
        mutable prog : Rtypes.uint4;
        mutable vers : Rtypes.uint4;
        mutable prot : Rtypes.uint4;
        mutable port : Rtypes.uint4;
      }
and pmaplist = 
      { 
        mutable map : mapping;
        mutable next : pmaplist option;
      }
and pmaplist_p = 
      pmaplist option
and call_args = 
      { 
        mutable call_prog : Rtypes.uint4;
        mutable call_vers : Rtypes.uint4;
        mutable call_proc : Rtypes.uint4;
        mutable call_args : string;
      }
and call_result = 
      { 
        mutable call_port : Rtypes.uint4;
        mutable call_res : string;
      }
and t_PMAP'V2'pmapproc_null'arg = 
      unit
and t_PMAP'V2'pmapproc_null'res = 
      unit
and t_PMAP'V2'pmapproc_set'arg = 
      mapping
and t_PMAP'V2'pmapproc_set'res = 
      bool
and t_PMAP'V2'pmapproc_unset'arg = 
      mapping
and t_PMAP'V2'pmapproc_unset'res = 
      bool
and t_PMAP'V2'pmapproc_getport'arg = 
      mapping
and t_PMAP'V2'pmapproc_getport'res = 
      Rtypes.uint4
and t_PMAP'V2'pmapproc_dump'arg = 
      unit
and t_PMAP'V2'pmapproc_dump'res = 
      pmaplist_p
and t_PMAP'V2'pmapproc_callit'arg = 
      call_args
and t_PMAP'V2'pmapproc_callit'res = 
      call_result
;;
let pmap_port = (Rtypes.mk_uint4('\000','\000','\000','\111'));;
let ipproto_tcp = (Rtypes.mk_uint4('\000','\000','\000','\006'));;
let ipproto_udp = (Rtypes.mk_uint4('\000','\000','\000','\017'));;
let rec _to_mapping (x:Xdr.xdr_value) : mapping =
  (let s = Xdr.dest_xv_struct_fast x in
     { prog = (fun x -> (Xdr.dest_xv_uint x)) s.(0); 
       vers = (fun x -> (Xdr.dest_xv_uint x)) s.(1); 
       prot = (fun x -> (Xdr.dest_xv_uint x)) s.(2); 
       port = (fun x -> (Xdr.dest_xv_uint x)) s.(3); 
     })
and _of_mapping (x:mapping) : Xdr.xdr_value =
  (Xdr.XV_struct_fast
     [|
       (let x = x.prog in (Xdr.XV_uint x));
       (let x = x.vers in (Xdr.XV_uint x));
       (let x = x.prot in (Xdr.XV_uint x));
       (let x = x.port in (Xdr.XV_uint x));
     |])
and _to_pmaplist (x:Xdr.xdr_value) : pmaplist =
  (let s = Xdr.dest_xv_struct_fast x in
     { map = (fun x -> (_to_mapping x)) s.(0); 
       next = (fun x -> (match Xdr.dest_xv_union_over_enum_fast x with
                        | (0, _) -> None
                        | (1, x) -> Some (_to_pmaplist x)
                        | _ -> assert false))
              s.(1); 
     })
and _of_pmaplist (x:pmaplist) : Xdr.xdr_value =
  (Xdr.XV_struct_fast
     [|
       (let x = x.map in (_of_mapping x));
       (let x = x.next in
         (match x with
         | None   -> Xdr.xv_none
         | Some x -> Xdr.xv_some (_of_pmaplist x)
         ));
     |])
and _to_pmaplist_p (x:Xdr.xdr_value) : pmaplist_p =
  (match Xdr.dest_xv_union_over_enum_fast x with
  | (0, _) -> None
  | (1, x) -> Some (_to_pmaplist x)
  | _ -> assert false)
and _of_pmaplist_p (x:pmaplist_p) : Xdr.xdr_value =
  (match x with
  | None   -> Xdr.xv_none
  | Some x -> Xdr.xv_some (_of_pmaplist x)
  )
and _to_call_args (x:Xdr.xdr_value) : call_args =
  (let s = Xdr.dest_xv_struct_fast x in
     { call_prog = (fun x -> (Xdr.dest_xv_uint x)) s.(0); 
       call_vers = (fun x -> (Xdr.dest_xv_uint x)) s.(1); 
       call_proc = (fun x -> (Xdr.dest_xv_uint x)) s.(2); 
       call_args = (fun x -> (Xdr.dest_xv_opaque x)) s.(3); 
     })
and _of_call_args (x:call_args) : Xdr.xdr_value =
  (Xdr.XV_struct_fast
     [|
       (let x = x.call_prog in (Xdr.XV_uint x));
       (let x = x.call_vers in (Xdr.XV_uint x));
       (let x = x.call_proc in (Xdr.XV_uint x));
       (let x = x.call_args in (Xdr.XV_opaque x));
     |])
and _to_call_result (x:Xdr.xdr_value) : call_result =
  (let s = Xdr.dest_xv_struct_fast x in
     { call_port = (fun x -> (Xdr.dest_xv_uint x)) s.(0); 
       call_res = (fun x -> (Xdr.dest_xv_opaque x)) s.(1); 
     })
and _of_call_result (x:call_result) : Xdr.xdr_value =
  (Xdr.XV_struct_fast
     [|
       (let x = x.call_port in (Xdr.XV_uint x));
       (let x = x.call_res in (Xdr.XV_opaque x));
     |])
and _to_PMAP'V2'pmapproc_null'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_null'arg =
  ()
and _of_PMAP'V2'pmapproc_null'arg (x:t_PMAP'V2'pmapproc_null'arg) : Xdr.xdr_value =
  Xdr.XV_void
and _to_PMAP'V2'pmapproc_null'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_null'res =
  ()
and _of_PMAP'V2'pmapproc_null'res (x:t_PMAP'V2'pmapproc_null'res) : Xdr.xdr_value =
  Xdr.XV_void
and _to_PMAP'V2'pmapproc_set'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_set'arg =
  (_to_mapping x)
and _of_PMAP'V2'pmapproc_set'arg (x:t_PMAP'V2'pmapproc_set'arg) : Xdr.xdr_value =
  (_of_mapping x)
and _to_PMAP'V2'pmapproc_set'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_set'res =
  (Xdr.dest_xv_enum_fast x = 1)
and _of_PMAP'V2'pmapproc_set'res (x:t_PMAP'V2'pmapproc_set'res) : Xdr.xdr_value =
  (if x then Xdr.xv_true else Xdr.xv_false)
and _to_PMAP'V2'pmapproc_unset'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_unset'arg =
  (_to_mapping x)
and _of_PMAP'V2'pmapproc_unset'arg (x:t_PMAP'V2'pmapproc_unset'arg) : Xdr.xdr_value =
  (_of_mapping x)
and _to_PMAP'V2'pmapproc_unset'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_unset'res =
  (Xdr.dest_xv_enum_fast x = 1)
and _of_PMAP'V2'pmapproc_unset'res (x:t_PMAP'V2'pmapproc_unset'res) : Xdr.xdr_value =
  (if x then Xdr.xv_true else Xdr.xv_false)
and _to_PMAP'V2'pmapproc_getport'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_getport'arg =
  (_to_mapping x)
and _of_PMAP'V2'pmapproc_getport'arg (x:t_PMAP'V2'pmapproc_getport'arg) : Xdr.xdr_value =
  (_of_mapping x)
and _to_PMAP'V2'pmapproc_getport'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_getport'res =
  (Xdr.dest_xv_uint x)
and _of_PMAP'V2'pmapproc_getport'res (x:t_PMAP'V2'pmapproc_getport'res) : Xdr.xdr_value =
  (Xdr.XV_uint x)
and _to_PMAP'V2'pmapproc_dump'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_dump'arg =
  ()
and _of_PMAP'V2'pmapproc_dump'arg (x:t_PMAP'V2'pmapproc_dump'arg) : Xdr.xdr_value =
  Xdr.XV_void
and _to_PMAP'V2'pmapproc_dump'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_dump'res =
  (_to_pmaplist_p x)
and _of_PMAP'V2'pmapproc_dump'res (x:t_PMAP'V2'pmapproc_dump'res) : Xdr.xdr_value =
  (_of_pmaplist_p x)
and _to_PMAP'V2'pmapproc_callit'arg (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_callit'arg =
  (_to_call_args x)
and _of_PMAP'V2'pmapproc_callit'arg (x:t_PMAP'V2'pmapproc_callit'arg) : Xdr.xdr_value =
  (_of_call_args x)
and _to_PMAP'V2'pmapproc_callit'res (x:Xdr.xdr_value) : t_PMAP'V2'pmapproc_callit'res =
  (_to_call_result x)
and _of_PMAP'V2'pmapproc_callit'res (x:t_PMAP'V2'pmapproc_callit'res) : Xdr.xdr_value =
  (_of_call_result x)
;;
let xdrt_mapping =
  Xdr.X_rec("mapping",
    Xdr.X_struct
      [
        ("prog", (Xdr.X_uint));
        ("vers", (Xdr.X_uint));
        ("prot", (Xdr.X_uint));
        ("port", (Xdr.X_uint));
      ])
;;
let xdrt_pmaplist =
  Xdr.X_rec("pmaplist",
    Xdr.X_struct
      [
        ("map", (xdrt_mapping));
        ("next", (Xdr.x_optional (Xdr.X_refer "pmaplist")));
      ])
;;
let xdrt_pmaplist_p = Xdr.X_rec("pmaplist_p", Xdr.x_optional (xdrt_pmaplist))
;;
let xdrt_call_args =
  Xdr.X_rec("call_args",
    Xdr.X_struct
      [
        ("call_prog", (Xdr.X_uint));
        ("call_vers", (Xdr.X_uint));
        ("call_proc", (Xdr.X_uint));
        ("call_args", (Xdr.x_opaque_max));
      ])
;;
let xdrt_call_result =
  Xdr.X_rec("call_result",
    Xdr.X_struct
      [   ("call_port", (Xdr.X_uint));   ("call_res", (Xdr.x_opaque_max)); ])
;;
let xdrt_PMAP'V2'pmapproc_null'arg = Xdr.X_void
;;
let xdrt_PMAP'V2'pmapproc_null'res = Xdr.X_void
;;
let xdrt_PMAP'V2'pmapproc_set'arg = xdrt_mapping
;;
let xdrt_PMAP'V2'pmapproc_set'res = Xdr.x_bool
;;
let xdrt_PMAP'V2'pmapproc_unset'arg = xdrt_mapping
;;
let xdrt_PMAP'V2'pmapproc_unset'res = Xdr.x_bool
;;
let xdrt_PMAP'V2'pmapproc_getport'arg = xdrt_mapping
;;
let xdrt_PMAP'V2'pmapproc_getport'res = Xdr.X_uint
;;
let xdrt_PMAP'V2'pmapproc_dump'arg = Xdr.X_void
;;
let xdrt_PMAP'V2'pmapproc_dump'res = xdrt_pmaplist_p
;;
let xdrt_PMAP'V2'pmapproc_callit'arg = xdrt_call_args
;;
let xdrt_PMAP'V2'pmapproc_callit'res = xdrt_call_result
;;
let program_PMAP'V2 =
  Rpc_program.create
    (Rtypes.mk_uint4('\000','\001','\134','\160'))
    (Rtypes.mk_uint4('\000','\000','\000','\002'))
    (Xdr.validate_xdr_type_system [])
    [
      "PMAPPROC_NULL",
        ((Rtypes.mk_uint4('\000','\000','\000','\000')),
        xdrt_PMAP'V2'pmapproc_null'arg,
        xdrt_PMAP'V2'pmapproc_null'res);
      "PMAPPROC_SET",
        ((Rtypes.mk_uint4('\000','\000','\000','\001')),
        xdrt_PMAP'V2'pmapproc_set'arg,
        xdrt_PMAP'V2'pmapproc_set'res);
      "PMAPPROC_UNSET",
        ((Rtypes.mk_uint4('\000','\000','\000','\002')),
        xdrt_PMAP'V2'pmapproc_unset'arg,
        xdrt_PMAP'V2'pmapproc_unset'res);
      "PMAPPROC_GETPORT",
        ((Rtypes.mk_uint4('\000','\000','\000','\003')),
        xdrt_PMAP'V2'pmapproc_getport'arg,
        xdrt_PMAP'V2'pmapproc_getport'res);
      "PMAPPROC_DUMP",
        ((Rtypes.mk_uint4('\000','\000','\000','\004')),
        xdrt_PMAP'V2'pmapproc_dump'arg,
        xdrt_PMAP'V2'pmapproc_dump'res);
      "PMAPPROC_CALLIT",
        ((Rtypes.mk_uint4('\000','\000','\000','\005')),
        xdrt_PMAP'V2'pmapproc_callit'arg,
        xdrt_PMAP'V2'pmapproc_callit'res);
    ]
;;
