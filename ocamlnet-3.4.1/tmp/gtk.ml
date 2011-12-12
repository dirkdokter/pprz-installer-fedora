open GMain.Io
let _ = (add_watch : cond:condition list -> callback:(condition list -> bool) -> ?prio:int -> channel -> id);;
exit 0
