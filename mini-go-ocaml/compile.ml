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

let depth_comment (depth : int) (c : string) : [> ] asm =
  comment (String.make depth '-' ^ c)
;;

let rec expr_description (e : expr) : string =
  let name, ofs =
    match e.expr_desc with
    | TEident v -> v.v_name, string_of_int v.v_ofs
    | TEunop (Ustar, e) -> "*(" ^ expr_description e ^ ")", ""
    | _ -> "other", "ofs"
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

let rec sizeof_typ (typ : typ) : int =
  match typ with
  | Tint | Tbool | Tstring | Tptr _ | Tnil -> 8
  | Tstruct s ->
    if s.s_size = -1 then compute_struct_size_and_offsets s;
    s.s_size
  | Tmany _ -> failwith "unreachable (sizeof_typ)"

and compute_struct_size_and_offsets (s : structure) =
  let current_ofs = ref 0 in
  s.s_list
  |> List.iter (fun f ->
    f.f_ofs <- !current_ofs;
    let field_size = sizeof_typ f.f_typ in
    current_ofs := !current_ofs + field_size;
    ());
  s.s_size <- !current_ofs
;;

(* Create label for each format string needed *)
let lbl_true = new_label ()
and lbl_false = new_label ()
and lbl_nil = new_label ()
and lbl_int = new_label ()
and lbl_string = new_label ()
and lbl_ptr = new_label ()

(* Print function : need to call printf for each argument with the good format *)
let rec compile_print (depth : int) (arg_list : expr list) : text (* code *) * data =
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
        (* calling convention: second argument goes into rsi *)
        ++ movq !%rdi !%rsi
        (* calling convention: first argument goes into rdi *)
        ++ movq (ilab fmt_str) !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    in
    (* compile argument. after ecode, the argument value will be in rdi *)
    let ecode, edata = compile_expr (depth + 1) arg in
    match arg.expr_typ with
    | Tbool ->
      ( ecode
        (* put the label for string "true" in rax and the label for string "false" in rbx *)
        ++ movq (ilab lbl_true) !%rax
        ++ movq (ilab lbl_false) !%rbx
        (* compare the boolean value with 0 (false) *)
        ++ cmpq (imm 0) !%rdi
        (* based on the comparison, move either rax or rbx in rdi *)
        (* this way, the first argument of printf (rdi) is either the label for string "true" or the label for string "false" *)
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
        (* put the label for string "<nil>" in rax and the label for string "%p" (pointer) in rbx *)
        ++ movq (ilab lbl_nil) !%rax
        ++ movq (ilab lbl_ptr) !%rbx
        (* compare the pointer value with 0 (nil) *)
        ++ cmpq (imm 0) !%rdi
        (* the first argument of printf (rdi) is either the label for string "<nil>" or the format string "%p" for a pointer according to the value of the boolean *)
        ++ cmove !%rax !%rdi
        ++ cmovne !%rdi !%rsi
        ++ cmovne !%rbx !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , edata )
    | Tstruct s ->
      (* structures are printed in {}, with fields split by spaces *)
      failwith "print structures wip"
    | Tnil -> print_simple_value ecode edata lbl_nil
    | Tmany l -> failwith "unreachable (print Tmany)"
  in
  concat_code_data
    ~start_code:(depth_comment depth "[begin] call to fmt.Print")
    ~finish_code:(depth_comment depth "[end] call to fmt.Print")
    compile_one_print
    (insert_spaces_for_print arg_list)

and compile_binop (depth : int) (binop : binop) (expr1 : expr) (expr2 : expr)
  : text * data
  =
  (* specific code for each operation, at the beginning 
      - resulting value of expression 1 is in r8
      - resulting value of expression 2 is in rdi
  *)
  let op_name, op_code =
    match binop with
    | Badd -> "+", addq !%r8 !%rdi
    | Bsub ->
      ( "-"
      , (* need to invert registers to store the result in rdi *)
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
        movq !%r8 !%rax ++ cqto ++ idivq !%rdi ++ movq !%rax !%rdi )
    | Bmod ->
      ( "%"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax
            - remainder: rdx <- result
        *)
        movq !%r8 !%rax ++ cqto ++ idivq !%rdi ++ movq !%rdx !%rdi )
    | Beq -> "=", cmpq !%r8 !%rdi ++ sete !%dil ++ andq (imm 1) !%rdi
    | Bne -> "!=", cmpq !%r8 !%rdi ++ setne !%dil ++ andq (imm 1) !%rdi
    | Blt -> "<", cmpq !%rdi !%r8 ++ setl !%dil ++ andq (imm 1) !%rdi
    | Ble -> "<=", cmpq !%rdi !%r8 ++ setle !%dil ++ andq (imm 1) !%rdi
    | Bgt -> ">", cmpq !%rdi !%r8 ++ setg !%dil ++ andq (imm 1) !%rdi
    | Bge -> ">=", cmpq !%rdi !%r8 ++ setge !%dil ++ andq (imm 1) !%rdi
    | Band -> "&&", andq !%rdi !%r8 ++ setnz !%dil ++ andq (imm 1) !%rdi
    | Bor -> "||", orq !%rdi !%r8 ++ setnz !%dil ++ andq (imm 1) !%rdi
  in
  (* concatenate code of both expressions and of operation *)
  concat_code_data
    ~start_code:(depth_comment depth ("[begin] binary operation " ^ op_name))
    ~finish_code:(depth_comment depth ("[end] binary operation " ^ op_name))
    Fun.id
    [ (* compiled code of first expression, will store result in rdi *)
      compile_expr (depth + 1) expr1
    ; (* need to push result on the stack to save result of first expression (otherwise overwritten by next expression) *)
      pushq !%rdi, inline ""
    ; (* compiled code of second expression, will store result in rdi *)
      compile_expr (depth + 1) expr2
    ; (* restore the result of first expression in r8 *)
      popq r8, inline ""
    ; (* now, r8 contains the result of first expression, and rdi the result of the second => we can use the binary operation code *)
      op_code, inline ""
    ]

(* Generate code for each expressions *)
and compile_expr (depth : int) (expr : expr) : text * data =
  match expr.expr_desc with
  | TEskip -> nop, nop
  | TEconstant c ->
    (match c with
     (* if the expression has non-nil type, its value is stored in rdi *)
     | Cbool b -> movq (imm (if b then 1 else 0)) !%rdi, inline ""
     | Cint i -> movq (imm64 i) !%rdi, inline ""
     | Cstring s ->
       let lbl = new_label () in
       movq (ilab lbl) !%rdi, label lbl ++ string s)
  | TEbinop (binop, expr1, expr2) -> compile_binop (depth + 1) binop expr1 expr2
  | TEunop (Uneg, expr) ->
    let e_code, e_data = compile_expr (depth + 1) expr in
    e_code ++ negq !%rdi, e_data
  | TEunop (Unot, expr) ->
    let e_code, e_data = compile_expr (depth + 1) expr in
    e_code ++ notb !%dil ++ andb (imm 1) !%dil, e_data
  | TEunop (Ustar, _) ->
    let e_code, e_data = compile_left_value depth expr in
    e_code ++ movq (ind rdi) !%rdi, e_data
  | TEunop (Uamp, e) -> compile_left_value depth e
  | TEnil -> xorq !%rdi !%rdi, inline ""
  | TEnew typ ->
    let typ_size = sizeof_typ typ in
    ( depth_comment depth ("[begin] new (size " ^ string_of_int typ_size ^ ")")
      ++ movq (imm typ_size) !%rdi
      ++ call "malloc_"
      ++ movq !%rax !%rdi
      ++ depth_comment depth "[end] new"
    , inline "" )
  | TEcall (f, args) -> failwith "call wip"
  | TEident var -> movq (ind ~ofs:var.v_ofs rbp) !%rdi, inline ""
  | TEdot (expr, field) -> failwith "dot wip"
  | TEassign ([ left_expr ], [ value ]) ->
    (* store value expressions on the stack at the variable's offset *)
    let lv_code, lv_data = compile_left_value (depth + 1) left_expr in
    let value_code, value_data = compile_expr (depth + 1) value in
    ( depth_comment depth ("[begin] variable assignment for" ^ expr_description left_expr)
      ++ value_code
      (* store value result (rdi) on the stack *)
             ++ pushq !%rdi
      ++ lv_code
      (* recover value result in register r8*)
             ++ popq r8
             ++ movq !%r8 (ind rdi)
      ++ depth_comment depth "[end] variables assignment"
    , value_data ++ lv_data )
  (* multiple assignment are rewritten into single ones *)
  | TEassign _ -> failwith "unreachable (multiple TEassign)"
  (* all variables declarations are grouped at the top of the function *)
  | TEvars vars -> nop, nop
  | TEif (b, e1, e2) ->
    let compiled_condition = compile_expr (depth + 1) b in
    let lbl_end_if = new_label ()
    and lbl_else = new_label () in
    let ecode_if, edata_if = compile_expr (depth + 1) e1 in
    let ecode_else, edata_else = compile_expr (depth + 1) e2 in
    concat_code_data
      ~start_code:(depth_comment depth "[begin] if statement")
      ~finish_code:(depth_comment depth "[end] if statement")
      Fun.id
      [ compiled_condition
      ; ( (* compare condition result (in rdi) with 0 *)
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
  | TEblock el -> concat_code_data (compile_expr (depth + 1)) el
  | TEfor (c, b) ->
    let cond_lbl = new_label ()
    and body_lbl = new_label () in
    let compiled_condition = compile_expr (depth + 1) c in
    let compiled_body = compile_expr (depth + 1) b in
    concat_code_data
      Fun.id
      [ jmp cond_lbl ++ label body_lbl, inline ""
      ; compiled_body
      ; label cond_lbl, inline ""
      ; compiled_condition
      ; cmpb (imm 0) !%dil ++ jnz body_lbl, inline ""
      ]
  | TEprint args -> compile_print (depth + 1) args
  (* note: incdec is a statement, not an expression *)
  | TEincdec (e, incdec) ->
    let incdec =
      match incdec with
      | Inc -> incq
      | Dec -> decq
    in
    let lv_code, lv_data = compile_left_value (depth + 1) e in
    lv_code ++ incdec (ind rdi), lv_data

and compile_left_value (depth : int) (expr : expr) : text * data =
  (* put the address of the left value in rdi *)
  match expr.expr_desc with
  (* | TEident ({ v_typ = Tptr _; _ } as v) -> movq (ind ~ofs:v.v_ofs rbp) !%rdi, nop *)
  | TEident v -> movq !%rbp !%rdi ++ addq (imm v.v_ofs) !%rdi, nop
  | TEunop (Ustar, ({ expr_typ = Tptr _ } as e)) ->
    (* return the address referenced by the pointer ie its value *)
    (* put the value of expression e in rdi (which is the wanted address, because the expression is a pointer) *)
    compile_expr (depth + 1) e
  (* star can only be used on pointers *)
  | TEunop (Ustar, _) -> failwith "unreachable (compile_left_value - star on non-pointer)"
  | TEdot _ -> failwith "struct left_value dot wip"
  | _ -> failwith "unreachable (compile_left_value)"
;;

let find_all_vars (tbody : expr) : var list =
  let rec aux (acc : var list) (e : expr) : var list =
    match e.expr_desc with
    | TEskip
    | TEconstant _
    | TEbinop _
    | TEunop _
    | TEnil
    | TEnew _
    | TEcall _
    | TEident _
    | TEdot _
    | TEassign _
    | TEprint _
    | TEincdec _
    | TEreturn _ -> acc
    | TEvars v_list -> acc @ v_list
    | TEif (_, b1, b2) -> aux (aux acc b1 @ acc) b2
    | TEblock b -> b |> List.fold_left aux acc
    | TEfor (_, b) -> aux acc b
  in
  aux [] tbody
;;

let compile_func (tfunc : function_) (tbody : expr) : text (* code *) * data =
  (* for each variable declared somewhere in the function body, we compute its offset (from rbp) based on its size.
     we also compute the total size of all variables (sum of all variables size) to know how much stack frame we need to allocate. *)
  let total_var_size =
  let offset = ref 0 in
    find_all_vars tbody
    |> List.iter (fun var ->
      let size = sizeof_typ var.v_typ in
      offset := !offset - size;
      var.v_ofs <- !offset);
    (* offset starts at 0 and is subtracted the size of each variable, so the total variable size is just its opposite *)
    - !offset
  in
  let body_code, body_data = compile_expr (-2) tbody in
  let code =
    label tfunc.fn_name
    (* prepare stack frame *)
    ++ pushq !%rbp
    ++ movq !%rsp !%rbp
    (* allocate space for variables *)
    ++ comment "decrement stack pointer to store function variables"
    ++ subq (imm total_var_size) !%rsp
    (* function body code *)
    ++ comment ("code for body of function " ^ tfunc.fn_name)
    ++ body_code
    (* restore stack frame *)
    ++ movq !%rbp !%rsp
    ++ popq rbp
    (* set return code for main *)
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
