(************************************************************
 * WARNING!
 *
 * This file is generated by ocamlrpcgen from the source file
 * netplex_ctrl.x
 *
 ************************************************************)
module Control = struct
  module V1 = struct
    open Netplex_ctrl_aux
    let _program = program_Control'V1
    
    let bind
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_poll
      ~proc_accepted
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Sync { Rpc_server.sync_name = "ping";
                                 Rpc_server.sync_proc = (fun x -> _of_Control'V1'ping'res (proc_ping (_to_Control'V1'ping'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "poll";
                                 Rpc_server.sync_proc = (fun x -> _of_Control'V1'poll'res (proc_poll (_to_Control'V1'poll'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "accepted";
                                 Rpc_server.sync_proc = (fun x -> _of_Control'V1'accepted'res (proc_accepted (_to_Control'V1'accepted'arg x)))});
            ]
            srv
    
    let bind_async
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_poll
      ~proc_accepted
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Async { Rpc_server.async_name = "ping";
                                  Rpc_server.async_invoke = (fun s x -> proc_ping s (_to_Control'V1'ping'arg x) (fun y -> Rpc_server.reply s (_of_Control'V1'ping'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "poll";
                                  Rpc_server.async_invoke = (fun s x -> proc_poll s (_to_Control'V1'poll'arg x) (fun y -> Rpc_server.reply s (_of_Control'V1'poll'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "accepted";
                                  Rpc_server.async_invoke = (fun s x -> proc_accepted s (_to_Control'V1'accepted'arg x) (fun y -> Rpc_server.reply s (_of_Control'V1'accepted'res y)))});
            ]
            srv
    
    end
  
end
module System = struct
  module V1 = struct
    open Netplex_ctrl_aux
    let _program = program_System'V1
    
    let bind
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_lookup
      ~proc_send_message
      ~proc_log
      ~proc_call_plugin
      ~proc_register_container_socket
      ~proc_lookup_container_sockets
      ~proc_activate_lever
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Sync { Rpc_server.sync_name = "ping";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'ping'res (proc_ping (_to_System'V1'ping'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "lookup";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'lookup'res (proc_lookup (_to_System'V1'lookup'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "send_message";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'send_message'res (proc_send_message (_to_System'V1'send_message'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "log";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'log'res (proc_log (_to_System'V1'log'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "call_plugin";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'call_plugin'res (proc_call_plugin (_to_System'V1'call_plugin'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "register_container_socket";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'register_container_socket'res (proc_register_container_socket (_to_System'V1'register_container_socket'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "lookup_container_sockets";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'lookup_container_sockets'res (proc_lookup_container_sockets (_to_System'V1'lookup_container_sockets'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "activate_lever";
                                 Rpc_server.sync_proc = (fun x -> _of_System'V1'activate_lever'res (proc_activate_lever (_to_System'V1'activate_lever'arg x)))});
            ]
            srv
    
    let bind_async
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_lookup
      ~proc_send_message
      ~proc_log
      ~proc_call_plugin
      ~proc_register_container_socket
      ~proc_lookup_container_sockets
      ~proc_activate_lever
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Async { Rpc_server.async_name = "ping";
                                  Rpc_server.async_invoke = (fun s x -> proc_ping s (_to_System'V1'ping'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'ping'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "lookup";
                                  Rpc_server.async_invoke = (fun s x -> proc_lookup s (_to_System'V1'lookup'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'lookup'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "send_message";
                                  Rpc_server.async_invoke = (fun s x -> proc_send_message s (_to_System'V1'send_message'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'send_message'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "log";
                                  Rpc_server.async_invoke = (fun s x -> proc_log s (_to_System'V1'log'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'log'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "call_plugin";
                                  Rpc_server.async_invoke = (fun s x -> proc_call_plugin s (_to_System'V1'call_plugin'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'call_plugin'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "register_container_socket";
                                  Rpc_server.async_invoke = (fun s x -> proc_register_container_socket s (_to_System'V1'register_container_socket'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'register_container_socket'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "lookup_container_sockets";
                                  Rpc_server.async_invoke = (fun s x -> proc_lookup_container_sockets s (_to_System'V1'lookup_container_sockets'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'lookup_container_sockets'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "activate_lever";
                                  Rpc_server.async_invoke = (fun s x -> proc_activate_lever s (_to_System'V1'activate_lever'arg x) (fun y -> Rpc_server.reply s (_of_System'V1'activate_lever'res y)))});
            ]
            srv
    
    end
  
end
module Admin = struct
  module V2 = struct
    open Netplex_ctrl_aux
    let _program = program_Admin'V2
    
    let bind
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_list
      ~proc_enable
      ~proc_disable
      ~proc_restart
      ~proc_restart_all
      ~proc_system_shutdown
      ~proc_reopen_logfiles
      ~proc_send_admin_message
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Sync { Rpc_server.sync_name = "ping";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'ping'res (proc_ping (_to_Admin'V2'ping'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "list";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'list'res (proc_list (_to_Admin'V2'list'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "enable";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'enable'res (proc_enable (_to_Admin'V2'enable'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "disable";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'disable'res (proc_disable (_to_Admin'V2'disable'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "restart";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'restart'res (proc_restart (_to_Admin'V2'restart'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "restart_all";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'restart_all'res (proc_restart_all (_to_Admin'V2'restart_all'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "system_shutdown";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'system_shutdown'res (proc_system_shutdown (_to_Admin'V2'system_shutdown'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "reopen_logfiles";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'reopen_logfiles'res (proc_reopen_logfiles (_to_Admin'V2'reopen_logfiles'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "send_admin_message";
                                 Rpc_server.sync_proc = (fun x -> _of_Admin'V2'send_admin_message'res (proc_send_admin_message (_to_Admin'V2'send_admin_message'arg x)))});
            ]
            srv
    
    let bind_async
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_list
      ~proc_enable
      ~proc_disable
      ~proc_restart
      ~proc_restart_all
      ~proc_system_shutdown
      ~proc_reopen_logfiles
      ~proc_send_admin_message
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Async { Rpc_server.async_name = "ping";
                                  Rpc_server.async_invoke = (fun s x -> proc_ping s (_to_Admin'V2'ping'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'ping'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "list";
                                  Rpc_server.async_invoke = (fun s x -> proc_list s (_to_Admin'V2'list'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'list'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "enable";
                                  Rpc_server.async_invoke = (fun s x -> proc_enable s (_to_Admin'V2'enable'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'enable'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "disable";
                                  Rpc_server.async_invoke = (fun s x -> proc_disable s (_to_Admin'V2'disable'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'disable'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "restart";
                                  Rpc_server.async_invoke = (fun s x -> proc_restart s (_to_Admin'V2'restart'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'restart'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "restart_all";
                                  Rpc_server.async_invoke = (fun s x -> proc_restart_all s (_to_Admin'V2'restart_all'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'restart_all'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "system_shutdown";
                                  Rpc_server.async_invoke = (fun s x -> proc_system_shutdown s (_to_Admin'V2'system_shutdown'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'system_shutdown'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "reopen_logfiles";
                                  Rpc_server.async_invoke = (fun s x -> proc_reopen_logfiles s (_to_Admin'V2'reopen_logfiles'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'reopen_logfiles'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "send_admin_message";
                                  Rpc_server.async_invoke = (fun s x -> proc_send_admin_message s (_to_Admin'V2'send_admin_message'arg x) (fun y -> Rpc_server.reply s (_of_Admin'V2'send_admin_message'res y)))});
            ]
            srv
    
    end
  
end
module Semaphore = struct
  module V1 = struct
    open Netplex_ctrl_aux
    let _program = program_Semaphore'V1
    
    let bind
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_increment
      ~proc_decrement
      ~proc_get
      ~proc_create
      ~proc_destroy
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Sync { Rpc_server.sync_name = "ping";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'ping'res (proc_ping (_to_Semaphore'V1'ping'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "increment";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'increment'res (proc_increment (_to_Semaphore'V1'increment'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "decrement";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'decrement'res (proc_decrement (_to_Semaphore'V1'decrement'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "get";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'get'res (proc_get (_to_Semaphore'V1'get'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "create";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'create'res (proc_create (_to_Semaphore'V1'create'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "destroy";
                                 Rpc_server.sync_proc = (fun x -> _of_Semaphore'V1'destroy'res (proc_destroy (_to_Semaphore'V1'destroy'arg x)))});
            ]
            srv
    
    let bind_async
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_increment
      ~proc_decrement
      ~proc_get
      ~proc_create
      ~proc_destroy
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Async { Rpc_server.async_name = "ping";
                                  Rpc_server.async_invoke = (fun s x -> proc_ping s (_to_Semaphore'V1'ping'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'ping'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "increment";
                                  Rpc_server.async_invoke = (fun s x -> proc_increment s (_to_Semaphore'V1'increment'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'increment'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "decrement";
                                  Rpc_server.async_invoke = (fun s x -> proc_decrement s (_to_Semaphore'V1'decrement'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'decrement'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "get";
                                  Rpc_server.async_invoke = (fun s x -> proc_get s (_to_Semaphore'V1'get'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'get'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "create";
                                  Rpc_server.async_invoke = (fun s x -> proc_create s (_to_Semaphore'V1'create'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'create'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "destroy";
                                  Rpc_server.async_invoke = (fun s x -> proc_destroy s (_to_Semaphore'V1'destroy'arg x) (fun y -> Rpc_server.reply s (_of_Semaphore'V1'destroy'res y)))});
            ]
            srv
    
    end
  
end
module Sharedvar = struct
  module V1 = struct
    open Netplex_ctrl_aux
    let _program = program_Sharedvar'V1
    
    let bind
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_create_var
      ~proc_set_value
      ~proc_get_value
      ~proc_delete_var
      ~proc_wait_for_value
      ~proc_dump
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Sync { Rpc_server.sync_name = "ping";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'ping'res (proc_ping (_to_Sharedvar'V1'ping'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "create_var";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'create_var'res (proc_create_var (_to_Sharedvar'V1'create_var'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "set_value";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'set_value'res (proc_set_value (_to_Sharedvar'V1'set_value'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "get_value";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'get_value'res (proc_get_value (_to_Sharedvar'V1'get_value'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "delete_var";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'delete_var'res (proc_delete_var (_to_Sharedvar'V1'delete_var'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "wait_for_value";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'wait_for_value'res (proc_wait_for_value (_to_Sharedvar'V1'wait_for_value'arg x)))});
              (Rpc_server.Sync { Rpc_server.sync_name = "dump";
                                 Rpc_server.sync_proc = (fun x -> _of_Sharedvar'V1'dump'res (proc_dump (_to_Sharedvar'V1'dump'arg x)))});
            ]
            srv
    
    let bind_async
      ?program_number
      ?version_number
      ~proc_ping
      ~proc_create_var
      ~proc_set_value
      ~proc_get_value
      ~proc_delete_var
      ~proc_wait_for_value
      ~proc_dump
      srv
      =
        Rpc_server.bind
            ?program_number ?version_number _program 
            [
              (Rpc_server.Async { Rpc_server.async_name = "ping";
                                  Rpc_server.async_invoke = (fun s x -> proc_ping s (_to_Sharedvar'V1'ping'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'ping'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "create_var";
                                  Rpc_server.async_invoke = (fun s x -> proc_create_var s (_to_Sharedvar'V1'create_var'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'create_var'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "set_value";
                                  Rpc_server.async_invoke = (fun s x -> proc_set_value s (_to_Sharedvar'V1'set_value'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'set_value'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "get_value";
                                  Rpc_server.async_invoke = (fun s x -> proc_get_value s (_to_Sharedvar'V1'get_value'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'get_value'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "delete_var";
                                  Rpc_server.async_invoke = (fun s x -> proc_delete_var s (_to_Sharedvar'V1'delete_var'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'delete_var'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "wait_for_value";
                                  Rpc_server.async_invoke = (fun s x -> proc_wait_for_value s (_to_Sharedvar'V1'wait_for_value'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'wait_for_value'res y)))});
              (Rpc_server.Async { Rpc_server.async_name = "dump";
                                  Rpc_server.async_invoke = (fun s x -> proc_dump s (_to_Sharedvar'V1'dump'arg x) (fun y -> Rpc_server.reply s (_of_Sharedvar'V1'dump'res y)))});
            ]
            srv
    
    end
  
end
