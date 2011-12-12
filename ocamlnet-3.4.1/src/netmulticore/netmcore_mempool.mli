(* $Id: netmcore_mempool.mli 1615 2011-06-09 23:33:05Z gerd $ *)

(** Memory pools

    A memory pool is a block of shared memory that is set aside for storing
    shared data structures. The pool needs to be created before the
    worker processes are forked off that are going to use the pool.
    The worker processes do not map the pool to some random address,
    but rather the processes inherit the pool from the common master
    process which ensures that all processes will see the pool at
    the same address.

    In order to allow inheritance, the function {!Netmcore.start}
    for starting workers needs to get an additional argument
    [~inherit_resources]. The resource ID of the pool must be put
    into this list - otherwise the worker does not get access to
    the pool.

    It is not possible to enlarge the pool later (because of the
    inheritance method for making the pool accessible). It is advised
    to make the pool large enough for all possible data cases, and
    to let the user configure this size.
 *)

exception Out_of_pool_memory

val create_mempool : int -> Netmcore.res_id
  (** Creates the memory pool as shared memory object of the passed size
      (rounded up to the next multiple of pages) and returns the resource ID.

      Note that the process calling this function cannot use the pool,
      but only worker processes that are forked later. It is possible
      to call [create_mempool] before running {!Netmcore.startup}.
   *)

val alloc_mem : Netmcore.res_id -> int -> Netsys_mem.memory
  (** Allocate memory in this pool. The passed int the size of the
      returned [memory] object. The size is rounded up to the next
      multiple of pages.

      Blocks are actually allocated in units of pages.

      Raises [Out_of_pool_memory] if there is not enough contiguous
      space in the pool.
   *)

(*
val realloc_mem : 
      Netmcore.res_id -> Netsys_mem.memory -> int -> Netsys_mem.memory
  (** Changes the size of the allocated block. It may be possible that
      the change in size if possible without relocating the block.
      In the general case, however, the block is moved to a new address.

      Raises [Out_of_pool_memory] if there is not enough contiguous
      space in the pool.
   *)
 *)

val size_mem : Netmcore.res_id -> Netsys_mem.memory -> int
  (** Returns the size of this block, or raises [Not_found] *)

val size_mem_at_addr : Netmcore.res_id -> nativeint -> int
  (** Returns the size of the block at this address, or raises [Not_found] *)

val free_mem : Netmcore.res_id -> Netsys_mem.memory -> unit
  (** Frees this allocated block *)

val stats : Netmcore.res_id -> int * int * int
  (** Returns [(total, free, contiguous)] where
      - [total] is the total size of the pool
      - [free] is the number of free bytes
      - [contiguous] is the size of the largest contiguous free block
   *)

val debug_info : Netmcore.res_id -> string
  (** Returns a string describing the allocations etc. *)

val shm_name : Netmcore.res_id -> string
  (** Returns the name of the shared memory object *)

module Debug : sig
  val enable : bool ref
    (** Enable debugging *)

  val enable_alloc : bool ref
    (** Trace allocation and deallocation *)

end
