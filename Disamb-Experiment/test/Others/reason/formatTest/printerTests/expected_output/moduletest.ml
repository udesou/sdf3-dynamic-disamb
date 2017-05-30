module Ppx_deriving_runtime =
  struct
    type nonrec int = int
    type nonrec char = char
    type nonrec string = string
    type nonrec float = float
    type nonrec bool = bool
    type nonrec unit = unit
    type nonrec exn = exn
    type nonrec 'a array = 'a array
    type nonrec 'a list = 'a list
    type nonrec 'a option = 'a option
    type nonrec nativeint = nativeint
    type nonrec int32 = int32
    type nonrec int64 = int64
    type nonrec 'a lazy_t = 'a lazy_t
    type nonrec bytes = bytes
    module Pervasives = Pervasives
    module Char = Char
    module String = String
    module Printexc = Printexc
    module Array = Array
    module List = List
    module Nativeint = Nativeint
    module Int32 = Int32
    module Int64 = Int64
    module Lazy = Lazy
    module Bytes = Bytes
    module Hashtbl = Hashtbl
    module Queue = Queue
    module Stack = Stack
    module Set = Set
    module Weak = Weak
    module Printf = Printf
    module Format = Format
    module Buffer = Buffer
    include Pervasives
  end
module TestModule =
  struct
    type twostrings = (string * string)
    let rec (pp_twostrings :
              Format.formatter -> twostrings -> Ppx_deriving_runtime.unit)
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt  ->
            fun (a0,a1)  ->
              Format.fprintf fmt "(@[";
              ((Format.fprintf fmt "%S") a0;
               Format.fprintf fmt ",@ ";
               (Format.fprintf fmt "%S") a1);
              Format.fprintf fmt "@])")
      [@ocaml.warning "-A"])
    
    and show_twostrings : twostrings -> Ppx_deriving_runtime.string =
      fun x  -> Format.asprintf "%a" pp_twostrings x
    
    let mkPair s = (s, s) 
  end
let twoStrings = TestModule.mkPair "hello" 
let () = print_endline (TestModule.show_twostrings twoStrings) 