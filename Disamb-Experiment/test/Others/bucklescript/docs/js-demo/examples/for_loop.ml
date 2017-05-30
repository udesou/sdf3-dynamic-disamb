
(** Imperative style *)
let sum n =
    let v  = ref 0 in
    for i = 0 to n do
       v := !v + i
    done;
    !v

let () = Js.log (sum 100)