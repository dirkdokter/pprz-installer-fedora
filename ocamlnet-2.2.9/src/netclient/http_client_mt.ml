(* $Id: http_client_mt.ml 459 2006-04-30 19:49:19Z gerd $ *)

Http_client.init_mt
  ~create_lock_unlock_pair:
    (fun () ->
       let mutex = Mutex.create() in
       let lock() = Mutex.lock mutex in
       let unlock() = Mutex.unlock mutex in
       lock, unlock
    )
;;
