external check : unit -> bool = "check";;

let () =
  exit (if check() then 0 else 1)
