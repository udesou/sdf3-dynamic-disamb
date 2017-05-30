open Migrate_parsetree
open Ast_404

type parse_itype = [ `ML | `Reason | `Binary | `BinaryReason | `Auto ]
type print_itype = [ `ML | `Reason | `Binary | `BinaryReason | `AST | `None ]

exception Invalid_config of string

module type PRINTER =
    sig
        type q
        type t = q list

        val parse : add_runtime:bool ->
                    use_stdin:bool ->
                    parse_itype ->
                    string ->
                    ((t * Reason_pprint_ast.commentWithCategory) * bool)

        val ppx_deriving_runtime : q

        val print : print_itype ->
                    string ->
                    bool ->
                    out_channel ->
                    Format.formatter ->
                    ((t * Reason_pprint_ast.commentWithCategory) -> unit)
    end

let err s = raise (Invalid_config s)

let prepare_output_file = function
    | Some name -> open_out_bin name
    | None -> set_binary_mode_out stdout true; stdout

let close_output_file output_file output_chan =
    match output_file with
    | Some _ -> close_out output_chan
    | None -> ()

let ocamlBinaryParser use_stdin filename =
  let chan =
    match use_stdin with
      | true -> stdin
      | false ->
          let file_chan = open_in filename in
          seek_in file_chan 0;
          file_chan
  in
  match Ast_io.from_channel chan with
  | Result.Error err -> assert false
  | Result.Ok (_, Ast_io.Impl ((module Version), ast)) ->
    let module Convert = Convert(Version)(OCaml_404) in
    ((Obj.magic (Convert.copy_structure ast), []), true, false)
  | Result.Ok (_, Ast_io.Intf ((module Version), ast)) ->
    let module Convert = Convert(Version)(OCaml_404) in
    ((Obj.magic (Convert.copy_signature ast), []), true, true)

let reasonBinaryParser use_stdin filename =
  let chan =
    match use_stdin with
      | true -> stdin
      | false ->
          let file_chan = open_in filename in
          seek_in file_chan 0;
          file_chan
  in
  let (magic_number, filename, ast, comments, parsedAsML, parsedAsInterface) = input_value chan in
  ((ast, comments), parsedAsML, parsedAsInterface)
