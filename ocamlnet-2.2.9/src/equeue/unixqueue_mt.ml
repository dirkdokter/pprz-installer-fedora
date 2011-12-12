(* $Id: unixqueue_mt.ml 871 2006-05-04 12:59:40Z gerd $
 * ----------------------------------------------------------------------
 *
 *)


let create_lock_unlock_pair() =
  let mutex = Mutex.create() in
  let lock() = Mutex.lock mutex in
  let unlock() = Mutex.unlock mutex in
  (lock, unlock)
;;

Unixqueue.init_mt create_lock_unlock_pair;;
