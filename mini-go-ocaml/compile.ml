(** Code generation for Mini Go programs (TODO) *)

open Format
open Ast
open Tast
open X86_64

let debug = ref false
let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in
  fun () ->
    incr r;
    "L_" ^ string_of_int !r
;;

let rec expr_description (e : expr) : string =
  let name, ofs =
    match e.expr_desc with
    | TEident v -> v.v_name, string_of_int v.v_ofs
    | _ -> " other ", "  ofs "
  in
  " '" ^ name ^ "' (ofs=" ^ ofs ^ ")"
;;

(* Iterate a list with a function to produce a tuple (code, data) and concatenate together the resulting codes and data.
  Optional start and finish element could be added
*)
let concat_code_data
      ?(start_code = nop)
      ?(start_data = nop)
      ?(finish_code = nop)
      ?(finish_data = nop)
      (f : 'a -> text * data)
      (ll : 'a list)
  : text * data
  =
  let code, data =
    List.fold_left
      (fun (code, data) e ->
         (* create a string with a block of all the code concatenated and another with all the data concatenated *)
         let argscode, argsdata = f e in
         code ++ argscode, data ++ argsdata)
      (start_code, start_data)
      ll
  in
  code ++ finish_code, data ++ finish_data
;;

(* Create label for each format string needed *)
let lbl_true = new_label ()
and lbl_false = new_label ()
and lbl_nil = new_label ()
and lbl_int = new_label ()
and lbl_string = new_label ()
and lbl_ptr = new_label ()

(* Print function : need to call printf for each argument with the good format *)
let rec compile_print (depth : int) (offset : int ref) (arg_list : expr list)
  : text (* code *) * data
  =
  (* to match go's Print behavior, we need to print a space between expressions when neither are of type string *)
  (* we accomplish this by inserting space string literals " " at the proper place in the list of arguments given to Print *)
  let insert_spaces_for_print (arg_list : expr list) : expr list =
    let space = { expr_desc = TEconstant (Cstring " "); expr_typ = Tstring } in
    let rec add_space (acc : expr list) (list : expr list) : expr list =
      match list with
      | [] -> List.rev acc
      | t :: [] -> List.rev (t :: acc)
      | t :: r :: q ->
        if t.expr_typ = Tstring
        then add_space (t :: acc) (r :: q)
        else if r.expr_typ = Tstring
        then add_space (r :: t :: acc) q
        else add_space (space :: t :: acc) (r :: q)
    in
    add_space [] arg_list
  in
  let compile_one_print (arg : expr) : text * data =
    (* generate code for printing a simple value *)
    let print_simple_value (ecode : text) (edata : data) (fmt_str : label) =
      ( ecode
        (* calling convention: second argument goes into %rsi *)
        ++ movq !%rdi !%rsi
        (* calling convention: first argument goes into %rdi *)
        ++ movq (ilab fmt_str) !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    in
    (* compile argument. after ecode, the argument value will be in %rdi *)
    let ecode, edata = compile_expr (depth + 1) offset arg in
    match arg.expr_typ with
    | Tbool ->
      ( ecode
        (* put the label for string "true" in %rax and the label for string "false" in %rbx *)
        ++ movq (ilab lbl_true) !%rax
        ++ movq (ilab lbl_false) !%rbx
        (* compare the boolean value with 0 (false) *)
        ++ cmpq (imm 0) !%rdi
        (* based on the comparison, move either %rax or %rbx in %rdi *)
        (* this way, the first argument of printf (%rdi) is either the label for string "true" or the label for string "false" *)
        (* according to the value of the boolean *)
        ++ cmovne !%rax !%rdi
        ++ cmove !%rbx !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    | Tint -> print_simple_value ecode edata lbl_int
    | Tstring -> print_simple_value ecode edata lbl_string
    | Tptr _ ->
      ( ecode
        (* put the label for string "<nil>" in %rax and the label for string "%p" (pointer) in %rbx *)
        ++ movq (ilab lbl_nil) !%rax
        ++ movq (ilab lbl_ptr) !%rbx
        (* compare the pointer value with 0 (nil) *)
        ++ cmpq (imm 0) !%rdi
        (* the first argument of printf (%rdi) is either the label for string "<nil>" or the format string "%p" for a pointer according to the value of the boolean *)
        ++ cmove !%rax !%rdi
        ++ cmovne !%rdi !%rsi
        ++ cmovne !%rbx !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    | Tstruct _ -> failwith "fmt.Print cannot print structures yet"
    | Tnil -> print_simple_value ecode edata lbl_nil
    | Tmany _ -> failwith "print tmany wip"
  in
  concat_code_data
    ~start_code:(comment (String.make depth '-' ^ "[begin] call to fmt.Print"))
    ~finish_code:(comment (String.make depth '-' ^ "[end] call to fmt.Print"))
    compile_one_print
    (insert_spaces_for_print arg_list)

and compile_binop
      (depth : int)
      (offset : int ref)
      (binop : binop)
      (expr1 : expr)
      (expr2 : expr)
  : text * data
  =
  (* specific code for each operation, at the beginning 
      - resulting value of expression 1 is in %r8
      - resulting value of expression 2 is in %rdi
  *)
  let op_name, op_code =
    match binop with
    | Badd -> "+", addq !%r8 !%rdi
    | Bsub ->
      ( "-"
      , (* need to invert registers to store the result in %rdi *)
        subq !%rdi !%r8 ++ movq !%r8 !%rdi )
    | Bmul -> "*", imulq !%r8 !%rdi
    | Bdiv ->
      ( "/"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax <- result
            - remainder: rdx
        *)
        xorq !%rdx !%rdx ++ movq !%r8 !%rax ++ idivq !%rdi ++ movq !%rax !%rdi )
    | Bmod ->
      ( "%"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax
            - remainder: rdx <- result
        *)
        xorq !%rdx !%rdx ++ movq !%r8 !%rax ++ idivq !%rdi ++ movq !%rdx !%rdi )
    | Beq -> "=", cmpq !%r8 !%rdi ++ sete !%dil
    | Bne -> "!=", cmpq !%r8 !%rdi ++ setne !%dil
    | Blt -> "<", cmpq !%r8 !%rdi ++ setl !%dil
    | Ble -> "<=", cmpq !%r8 !%rdi ++ setle !%dil
    | Bgt -> ">", cmpq !%r8 !%rdi ++ setg !%dil
    | Bge -> ">=", cmpq !%r8 !%rdi ++ setge !%dil
    | Band -> "&&", andq !%rdi !%r8 ++ setnz !%dil
    | Bor -> "||", orq !%rdi !%r8 ++ setnz !%dil
  in
  (* concatenate code of both expressions and of operation *)
  concat_code_data
    ~start_code:(comment (String.make depth '-' ^ "[begin] binary operation " ^ op_name))
    ~finish_code:(comment (String.make depth '-' ^ "[end] binary operation " ^ op_name))
    Fun.id
    [ (* compiled code of first expression, will store result in %rdi *)
      compile_expr (depth + 1) offset expr1
    ; (* need to push result on the stack to save result of first expression (otherwise overwritten by next expression) *)
      pushq !%rdi, inline ""
    ; (* compiled code of second expression, will store result in %rdi *)
      compile_expr (depth + 1) offset expr2
    ; (* restore the result of first expression in %r8 *)
      popq r8, inline ""
    ; (* now, %r8 contains the result of first expression, and %rdi the result of the second => we can use the binary operation code *)
      op_code, inline ""
    ]

and compile_unop (depth : int) (offset : int ref) (unop : unop) (expr : expr)
  : text * data
  =
  let op_name, op_code =
    match unop with
    | Uneg -> "-", negq !%rdi
    | Unot -> "!", notb !%dil ++ andb (imm 1) !%dil
    | Uamp -> "&", failwith "wip amp"
    | Ustar -> "*", failwith "wip star"
  in
  concat_code_data
    ~start_code:(comment (String.make depth '-' ^ "[begin] unary operation " ^ op_name))
    ~finish_code:(comment (String.make depth '-' ^ "[end] unary operation " ^ op_name))
    Fun.id
    [ compile_expr (depth + 1) offset expr; op_code, inline "" ]

(* Generate code for each expressions *)
and compile_expr (depth : int) (offset : int ref) (expr : expr) : text (* code *) * data =
  match expr.expr_desc with
  | TEskip -> nop, inline ""
  | TEconstant c ->
    (match c with
     (* if the expression has non-nil type, its value is stored in %rdi *)
     | Cbool b -> movq (imm (if b then 1 else 0)) !%rdi, inline ""
     | Cint i -> movq (imm64 i) !%rdi, inline ""
     | Cstring s ->
       let lbl = new_label () in
       movq (ilab lbl) !%rdi, label lbl ++ string s)
  | TEbinop (binop, expr1, expr2) -> compile_binop (depth + 1) offset binop expr1 expr2
  | TEunop (unop, expr) -> compile_unop (depth + 1) offset unop expr
  | TEnil -> xorq !%rdi !%rdi, inline ""
  | TEnew typ -> failwith "new wip"
  | TEcall (f, args) -> failwith "call wip"
  | TEident var -> movq (ind ~ofs:var.v_ofs rbp) !%rdi, inline ""
  | TEdot (expr, field) -> failwith "dot wip"
  | TEassign ([ var ], [ value ]) ->
    (* store value expressions on the stack at the variable's offset *)
    let ecode, edata =
      match value with
      | { expr_desc = TEcall (id, arg); _ } -> failwith "function assign wip"
      | values ->
        (* compute assignment expression and store it on the stack at the variable's offset  *)
        let compiled_expr = compile_expr (depth + 1) offset value in
        (match var.expr_desc with
         | TEident v ->
           let code = movq !%rdi (ind ~ofs:v.v_ofs rbp) in
           concat_code_data Fun.id [ compiled_expr; code, inline "" ]
         | _ -> failwith "struct assign wip")
    in
    concat_code_data
      ~start_code:
        (comment
           (String.make depth '-'
            ^ "[begin] variables assignment for "
            ^ expr_description var))
      ~finish_code:(comment (String.make depth '-' ^ "[end] variables assignment"))
      Fun.id
      [ ecode, edata ]
  (* multiple assignment are rewritten into single ones *)
  | TEassign (_, _) -> failwith "unreachable"
  | TEvars vars ->
    (* store each variable's offset and decrement stack pointer *)
    let vars_count = List.length vars in
    vars
    |> List.iter (fun var ->
      offset := !offset - 8;
      var.v_ofs <- !offset);
    ( comment " increment stack pointer to store variables"
      ++ subq (imm (8 * vars_count)) !%rsp
    , inline "" )
  | TEif (b, e1, e2) ->
    let compiled_condition = compile_expr (depth + 1) offset b in
    let lbl_end_if = new_label ()
    and lbl_else = new_label () in
    let ecode_if, edata_if = compile_expr (depth + 1) offset e1
    and ecode_else, edata_else = compile_expr (depth + 1) offset e2 in
    concat_code_data
      ~start_code:(comment (String.make depth '-' ^ "[begin] if statement"))
      ~finish_code:(comment (String.make depth '-' ^ "[end] if statement"))
      Fun.id
      [ compiled_condition
      ; ( (* compare condition result (in %rdi) with 0 *)
          cmpq (imm 0) !%rdi
          (* if false (equals 0), jump to else body *)
          ++ je lbl_else
          (* otherwise, run the if body, and jump to the end of the if statement *)
          ++ ecode_if
          ++ jmp lbl_end_if
          (* else body *)
          ++ label lbl_else
          ++ ecode_else
          ++ label lbl_end_if
        , edata_if ++ edata_else )
      ]
  | TEreturn el -> failwith "return wip"
  | TEblock el -> concat_code_data (compile_expr (depth + 1) offset) el
  | TEfor (b, e) -> failwith "for wip"
  | TEprint args -> compile_print (depth + 1) offset args
  | TEincdec (e, incdec) -> failwith "incdec wip"
;;

let compile_func tfunc tbody : text (* code *) * data =
  let offset = ref 0 in
  let body_code, body_data = compile_expr 0 offset tbody in
  let code =
    label tfunc.fn_name
    ++ pushq !%rbp
    ++ movq !%rsp !%rbp
    (* add generated code to the function call *)
    ++ body_code
    ++ movq !%rbp !%rsp
    ++ popq rbp
    ++ (if tfunc.fn_name = "main"
        then comment "main must return 0" ++ xorq !%rax !%rax
        else comment "")
    ++ ret
  in
  ( comment ("[begin] code of function " ^ tfunc.fn_name)
    ++ code
    ++ comment ("[end] code of function " ^ tfunc.fn_name)
  , comment ("[begin] data of function " ^ tfunc.fn_name)
    ++ body_data
    ++ comment ("[end] data of function " ^ tfunc.fn_name) )
;;

let file ?debug:(b = false) (dl : Tast.tfile) : X86_64.program =
  debug := b;
  let code, data =
    concat_code_data
      (function
        | TDfunction (tfunc, tbody) -> compile_func tfunc tbody
        | _ -> nop, nop)
      dl
  in
  { text =
      globl "main"
      ++ code
      (* TODO assembly code for the Go functions here *)
      ++ comment "TODO some auxiliary assembly functions, if needed"
      ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
      ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
      ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
  ; data =
      (* static data here, such as string constants *)
      comment "global data for all code"
      ++ label lbl_true
      ++ string "true"
      ++ label lbl_false
      ++ string "false"
      ++ label lbl_nil
      ++ string "<nil>"
      ++ label lbl_int
      ++ string "%lld"
      ++ label lbl_string
      ++ string "%s"
      ++ label lbl_ptr
      ++ string "%p"
      ++ data
  }
;;
