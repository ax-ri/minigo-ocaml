(** Code generation for Mini Go programs (TODO) *)

open Format
open Ast
open Tast
open X86_64
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

let lbl_true = new_label ()
and lbl_false = new_label ()

(* Print function : need to call printf for each argument with the good format *)
let rec compile_print (arg_list : expr list) : text (* code *) * data =
  let compile_one_print (arg : expr) : text * data =
    (* compile argument. after ecode, the argument value will be in %rdi *)
    let ecode, edata = compile_expr arg in
    if arg.expr_typ = Tbool
    then
      ( ecode
        (* put the label for string "true" in %rax and the label for string "false" in %rbx *)
        ++ movq (ilab lbl_true) !%rax
        ++ movq (ilab lbl_false) !%rbx
        (* compare the boolean value with 1 (true) *)
        ++ cmpq (imm 1) !%rdi
        (* based on the comparison, move either %rax or %rbx in %rdi *)
        (* this way, the first argument of printf (%rdi) is either the label for string "true" or the label for string "false" *)
        (* according to the value of the boolean *)
        ++ cmove !%rax !%rdi
        ++ cmovne !%rbx !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    else (
      (* get the format of the element to print *)
      let fmt_str =
        match arg.expr_typ with
        | Tbool -> failwith "unreachable"
        | Tint -> "%lld"
        | Tstring -> "%s"
        | Tptr _ -> "%p"
        | Tstruct _ -> failwith "fmt.Print cannot print structures"
        | Tnil -> failwith "fmt.Print cannot print nil"
        | Tmany _ -> failwith "print tmany wip"
      and lbl = new_label () in
      ( ecode
        (* calling convention: second argument goes into %rsi *)
        ++ movq !%rdi !%rsi
        (* calling convention: first argument goes into %rdi *)
        ++ movq (ilab lbl) !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata ++ label lbl ++ string fmt_str ))
  in
  concat_code_data
    ~start_code:(comment "[begin] call to fmt.Print")
    ~finish_code:(comment "[end] call to fmt.Print")
    compile_one_print
    arg_list

and compile_binop (binop : binop) (expr1 : expr) (expr2 : expr) : text * data =
  (* compiled code of first expression stored in %rdi *)
  let compiled_expr1 = compile_expr expr1 in
  (* compiled code of second expression stored in %rdi *)
  let compiled_expr2 = compile_expr expr2 in
  (* specific code for each operation, at the beginning 
        - compiled code of expression 1 is in %r8
        - compiled code of expression 2 is in %rdi
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
    ~start_code:(comment ("[begin] binary operation " ^ op_name))
    ~finish_code:(comment ("[end] binary operation " ^ op_name))
    Fun.id
    [ compiled_expr1
    ; (* need to push result on the stack to save result of first expression (otherwise overwritten by next expression) *)
      pushq !%rdi, inline ""
    ; compiled_expr2
    ; popq r8, inline ""
    ; op_code, inline ""
    ]

and compile_unop (unop : unop) (expr : expr) : text * data =
  let compiled_expr = compile_expr expr in
  let op_name, op_code =
    match unop with
    | Uneg -> "-", negq !%rdi
    | Unot -> "!", notb !%dil ++ andb (imm 1) !%dil
    | Uamp -> "&", failwith "wip amp"
    | Ustar -> "*", failwith "wip star"
  in
  concat_code_data
    ~start_code:(comment ("[begin] unary operation " ^ op_name))
    ~finish_code:(comment ("[end] unary operation " ^ op_name))
    Fun.id
    [ compiled_expr; op_code, inline "" ]

(* Generate code for each expressions *)
and compile_expr (expr : expr) : text (* code *) * data =
  match expr.expr_desc with
  | TEskip -> failwith "skip wip"
  | TEconstant c ->
    (match c with
     (* if the expression has non-nil type, its value is stored in %rdi *)
     | Cbool b -> movq (imm (if b then 1 else 0)) !%rdi, inline ""
     | Cint i -> movq (imm64 i) !%rdi, inline ""
     | Cstring s ->
       let lbl = new_label () in
       movq (ilab lbl) !%rdi, label lbl ++ string s)
  | TEbinop (binop, expr1, expr2) -> compile_binop binop expr1 expr2
  | TEunop (unop, expr) -> compile_unop unop expr
  | TEnil -> failwith "nil wip"
  | TEnew typ -> failwith "new wip"
  | TEcall (f, args) -> failwith "call wip"
  | TEident var -> failwith "var wip"
  | TEdot (expr, field) -> failwith "dot wip"
  | TEassign (arg, values) -> failwith "assign wip"
  | TEvars vars -> failwith "vars wip"
  | TEif (b, e1, e2) ->
    let compiled_condition = compile_expr b in
    let lbl_end_if = new_label ()
    and lbl_else = new_label () in
    let ecode_if, edata_if = compile_expr e1
    and ecode_else, edata_else = compile_expr e2 in
    concat_code_data
      ~start_code:(comment "[begin] if statement")
      ~finish_code:(comment "[end] if statement")
      Fun.id
      [ compiled_condition
      ; ( (* compare condition result (in %rdi) with 1 *)
          cmpq (imm 1) !%rdi
          (* if false, jump to else body *)
          ++ jne lbl_else
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
  | TEblock el -> concat_code_data compile_expr el
  | TEfor (b, e) -> failwith "for wip"
  | TEprint args -> compile_print args
  | TEincdec (e, incdec) -> failwith "incdec wip"
;;

let compile_func tfunc tbody : text (* code *) * data =
  let body_code, body_data = compile_expr tbody in
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
      ++ inline "\n# TODO some auxiliary assembly functions, if needed\n"
      ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
      ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
      ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
  ; data =
      (* TODO static data here, such as string constants *)
      label lbl_true ++ string "true" ++ label lbl_false ++ string "false" ++ data
  }
;;
