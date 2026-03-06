(** Code generation for Mini Go programs *)

open Format
open Ast
open Tast
open X86_64

let debug = ref false

let new_label =
  let r = ref 0 in
  fun () ->
    incr r;
    "L_" ^ string_of_int !r
;;

(* create a comment in asm code with a marker of the depth *)
let depth_comment (depth : int) (c : string) : [> ] asm =
  comment (String.make depth '-' ^ c)
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

(* get the size of a given type, in bytes. may trigger the computation of structure size (at most one time) *)
let rec sizeof_typ (typ : typ) : int =
  match typ with
  | Tint | Tbool | Tstring | Tptr _ | Tnil -> 8
  | Tstruct s ->
    if s.s_size = -1 then compute_struct_size_and_offsets s;
    s.s_size
  | Tmany _ -> failwith "unreachable (sizeof_typ)"

(* compute the total size of a structure (in bytes) as well as the offsets of each field *)
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

(* Create label for each recurring format string *)
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
    let print_simple_value (e_code : text) (e_data : data) (fmt_str : label) =
      ( e_code
        (* calling convention: second argument goes into rsi *)
        ++ movq !%rdi !%rsi
        (* calling convention: first argument goes into rdi *)
        ++ movq (ilab fmt_str) !%rdi
        (* call to printf (with alignment) *)
        ++ call "printf_"
      , e_data )
    in
    (* compile argument. after e_code, the argument value will be in rdi *)
    let e_code, e_data = compile_expr (depth + 1) arg in
    match arg.expr_typ with
    | Tbool ->
      ( e_code
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
      , e_data )
    | Tint -> print_simple_value e_code e_data lbl_int
    | Tstring -> print_simple_value e_code e_data lbl_string
    | Tptr _ ->
      ( e_code
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
      , e_data )
    | Tstruct s ->
      (* structures are printed in {}, with fields split by spaces *)
      failwith "print structures wip"
    | Tnil -> print_simple_value e_code e_data lbl_nil
    | Tmany _ -> failwith "unreachable (print Tmany)"
  in
  concat_code_data
    ~start_code:(depth_comment depth "[begin] call to fmt.Print")
    ~finish_code:(depth_comment depth "[end] call to fmt.Print")
    compile_one_print
    (insert_spaces_for_print arg_list)

and compile_binop (depth : int) (binop : binop) (expr1 : expr) (expr2 : expr)
  : text * data
  =
  match expr1.expr_desc, expr2.expr_desc with
  | TEconstant c1, TEconstant c2 -> compile_binop_cst_cst depth binop c1 c2
  | _, TEconstant c -> compile_binop_expr_cst depth binop expr1 c true
  | TEconstant c, _ -> compile_binop_expr_cst depth binop expr2 c false
  | _ -> compile_binop_expr_expr depth binop expr1 expr2

and compile_binop_cst_cst
      (depth : int)
      (binop : binop)
      (cst1 : constant)
      (cst2 : constant)
  =
  let op_name, op_code =
    match binop, cst1, cst2 with
    (* create an invalid operation *)
    | Bdiv, _, Cint 0L | Bmod, _, Cint 0L -> "/0", nop
    (* other specific cases when one of the two constant is zero *)
    | Badd, Cint 0L, Cint i | Badd, Cint i, Cint 0L | Bsub, Cint i, Cint 0L ->
      "", movq (imm64 i) !%rdi
    | Bsub, Cint 0L, Cint i -> "", movq (imm64 (Int64.neg i)) !%rdi
    | Bmul, Cint 0L, _ | Bmul, _, Cint 0L | Bdiv, Cint 0L, _ | Bmod, Cint 0L, _ ->
      "0", movq (imm 0) !%rdi
    (* generic cases *)
    | Badd, Cint i1, Cint i2 -> "+", movq (imm64 i1) !%rdi ++ addq (imm64 i2) !%rdi
    | Bsub, Cint i1, Cint i2 -> "-", movq (imm64 i1) !%rdi ++ subq (imm64 i2) !%rdi
    | Bmul, Cint i1, Cint i2 -> "*", movq (imm64 i1) !%rdi ++ imulq (imm64 i2) !%rdi
    | Bdiv, Cint i1, Cint i2 ->
      ( "/"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax <- result
            - remainder: rdx
        *)
        movq (imm64 i1) !%rax
        ++ movq (imm64 i2) !%rdi
        ++ cqto
        ++ idivq !%rdi
        ++ movq !%rax !%rdi )
    | Bmod, Cint i1, Cint i2 ->
      ( "%"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax
            - remainder: rdx <- result
        *)
        movq (imm64 i1) !%rax
        ++ movq (imm64 i2) !%rdi
        ++ cqto
        ++ idivq !%rdi
        ++ movq !%rdx !%rdi )
    (* for boolean operations, we need to `and` the result with 1 to ensure that rdi is set to exactly 0 or 1 (and not another non-zero value) *)
    | Beq, Cbool b1, Cbool b2 ->
      ( "="
      , movq (imm (if b1 then 1 else 0)) !%rdi
        ++ cmpq (imm (if b2 then 1 else 0)) !%rdi
        ++ sete !%dil
        ++ andq (imm 1) !%rdi )
    | Bne, Cbool b1, Cbool b2 ->
      ( "!="
      , movq (imm (if b1 then 1 else 0)) !%rdi
        ++ cmpq (imm (if b2 then 1 else 0)) !%rdi
        ++ setne !%dil
        ++ andq (imm 1) !%rdi )
    | Beq, Cint i1, Cint i2 ->
      ( "="
      , movq (imm64 i1) !%rdi ++ cmpq (imm64 i2) !%rdi ++ sete !%dil ++ andq (imm 1) !%rdi
      )
    | Bne, Cint i1, Cint i2 ->
      ( "!="
      , movq (imm64 i1) !%rdi
        ++ cmpq (imm64 i2) !%rdi
        ++ setne !%dil
        ++ andq (imm 1) !%rdi )
    | Blt, Cint i1, Cint i2 ->
      ( "<"
      , movq (imm64 i1) !%rdi ++ cmpq (imm64 i2) !%rdi ++ setl !%dil ++ andq (imm 1) !%rdi
      )
    | Ble, Cint i1, Cint i2 ->
      ( "<="
      , movq (imm64 i1) !%rdi
        ++ cmpq (imm64 i2) !%rdi
        ++ setle !%dil
        ++ andq (imm 1) !%rdi )
    | Bgt, Cint i1, Cint i2 ->
      ( ">"
      , movq (imm64 i1) !%rdi ++ cmpq (imm64 i2) !%rdi ++ setg !%dil ++ andq (imm 1) !%rdi
      )
    | Bge, Cint i1, Cint i2 ->
      ( ">="
      , movq (imm64 i1) !%rdi
        ++ cmpq (imm64 i2) !%rdi
        ++ setge !%dil
        ++ andq (imm 1) !%rdi )
    | Band, Cbool b1, Cbool b2 ->
      ( "&&"
      , movq (imm (if b1 then 1 else 0)) !%rdi
        ++ andq (imm (if b2 then 1 else 0)) !%rdi
        ++ setnz !%dil
        ++ andq (imm 1) !%rdi )
    | Bor, Cbool b1, Cbool b2 ->
      ( "||"
      , movq (imm (if b1 then 1 else 0)) !%rdi
        ++ orq (imm (if b2 then 1 else 0)) !%rdi
        ++ setnz !%dil
        ++ andq (imm 1) !%rdi )
    | _ -> failwith "unreachable (binary operation [cst - cst] with wrong types)"
  in
  (* concatenate code of both expressions and of operation *)
  match op_name with
  | "" -> nop, nop
  | "0" -> op_code, nop
  | "/0" -> failwith "invalid operation: division by zero"
  | _ ->
    concat_code_data
      ~start_code:(depth_comment depth ("[begin] binary operation " ^ op_name))
      ~finish_code:(depth_comment depth ("[end] binary operation " ^ op_name))
      Fun.id
      [ (* binary operation from constants: no expression compilation is needed *)
        op_code, nop
      ]

and compile_binop_expr_cst
      (depth : int)
      (binop : binop)
      (expr : expr)
      (cst : constant)
      (left : bool)
  =
  (* the boolean 'left' is here to say if the expression is the left or the right value *)
  (* value of expression will be stored in register rdi *)
  let op_name, op_code =
    match binop, cst with
    (* create an invalid operation *)
    | Bdiv, Cint 0L | Bmod, Cint 0L -> "/0", nop
    (* other specific cases when the constant is zero *)
    | Badd, Cint 0L | Bsub, Cint 0L -> "", nop
    | Bmul, Cint 0L -> "*0", movq (imm 0) !%rdi
    (* generic cases *)
    | Badd, Cint i -> "+", addq (imm64 i) !%rdi
    | Bsub, Cint i ->
      "-", if left then subq (imm64 i) !%rdi else subq (imm64 i) !%rdi ++ negq !%rdi
    | Bmul, Cint i -> "*", imulq (imm64 i) !%rdi
    | Bdiv, Cint i ->
      ( "/"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand (rdi)
            - quotient: rax <- result
            - remainder: rdx
        *)
        let init =
          if left then movq !%rdi !%rax ++ movq (imm64 i) !%rdi else movq (imm64 i) !%rax
        in
        init ++ cqto ++ idivq !%rdi ++ movq !%rax !%rdi )
    | Bmod, Cint i ->
      ( "%"
      , (* integer signed division 
            - dividend: rdx:rax
            - divisor: first operand 
            - quotient: rax
            - remainder: rdx <- result
        *)
        let init =
          if left then movq !%rdi !%rax ++ movq (imm64 i) !%rdi else movq (imm64 i) !%rax
        in
        init ++ cqto ++ idivq !%rdi ++ movq !%rdx !%rdi )
    (* for boolean operations, we need to `and` the result with 1 to ensure that rdi is set to exactly 0 or 1 (and not another non-zero value) *)
    | Beq, Cbool b ->
      "=", cmpq (imm (if b then 1 else 0)) !%rdi ++ sete !%dil ++ andq (imm 1) !%rdi
    | Bne, Cbool b ->
      "!=", cmpq (imm (if b then 1 else 0)) !%rdi ++ setne !%dil ++ andq (imm 1) !%rdi
    | Beq, Cint i -> "=", cmpq (imm64 i) !%rdi ++ sete !%dil ++ andq (imm 1) !%rdi
    | Bne, Cint i -> "!=", cmpq (imm64 i) !%rdi ++ setne !%dil ++ andq (imm 1) !%rdi
    | Blt, Cint i -> "<", cmpq (imm64 i) !%rdi ++ setl !%dil ++ andq (imm 1) !%rdi
    | Ble, Cint i -> "<=", cmpq (imm64 i) !%rdi ++ setle !%dil ++ andq (imm 1) !%rdi
    | Bgt, Cint i -> ">", cmpq (imm64 i) !%rdi ++ setg !%dil ++ andq (imm 1) !%rdi
    | Bge, Cint i -> ">=", cmpq (imm64 i) !%rdi ++ setge !%dil ++ andq (imm 1) !%rdi
    | Band, Cbool b ->
      "&&", andq (imm (if b then 1 else 0)) !%rdi ++ setnz !%dil ++ andq (imm 1) !%rdi
    | Bor, Cbool b ->
      "||", orq (imm (if b then 1 else 0)) !%rdi ++ setnz !%dil ++ andq (imm 1) !%rdi
    | _ ->
      Format.printf "%a %s %s\n" Pretty.expr expr (Pretty.binop binop) "cst";
      failwith "unreachable (binary operation [expr - cst] with wrong types)"
  in
  (* concatenate code of the expression and operation *)
  match op_name with
  | "" -> nop, nop
  | "*0" -> op_code, nop
  | "/0" -> failwith "invalid operation: division by zero"
  | _ ->
    concat_code_data
      ~start_code:(depth_comment depth ("[begin] binary operation " ^ op_name))
      ~finish_code:(depth_comment depth ("[end] binary operation " ^ op_name))
      Fun.id
      [ (* compiled code of first expression, will store result in rdi *)
        compile_expr (depth + 1) expr
      ; (* compiled binary operation with a constant *)
        op_code, nop
      ]

and compile_binop_expr_expr (depth : int) (binop : binop) (expr1 : expr) (expr2 : expr) =
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
    (* for boolean operations, we need to and the result with 1 to ensure that rdi is set to exactly 0 or 1 (and not another non-zero value) *)
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
      pushq !%rdi, nop
    ; (* compiled code of second expression, will store result in rdi *)
      compile_expr (depth + 1) expr2
    ; (* restore the result of first expression in r8 *)
      popq r8, nop
    ; (* now, r8 contains the result of first expression, and rdi the result of the second => we can use the binary operation code *)
      op_code, nop
    ]

(* generate code for each expressions *)
and compile_expr (depth : int) (expr : expr) : text * data =
  match expr.expr_desc with
  (**** expressions ****)
  (* expression code will leave the result of the expression in rdi *)
  | TEconstant (Cbool b) -> movq (imm (if b then 1 else 0)) !%rdi, nop
  | TEconstant (Cint i) -> movq (imm64 i) !%rdi, nop
  | TEconstant (Cstring s) ->
    let lbl = new_label () in
    movq (ilab lbl) !%rdi, label lbl ++ string s
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
  | TEnil -> xorq !%rdi !%rdi, nop
  | TEnew typ ->
    let typ_size = sizeof_typ typ in
    ( depth_comment depth "[begin] new heap allocation"
      ++ movq (imm typ_size) !%rdi
      ++ call "malloc_"
      ++ movq !%rax !%rdi
      ++ depth_comment depth "[end] new heap allocation"
    , nop )
  | TEident var -> movq (ind ~ofs:var.v_ofs rbp) !%rdi, nop
  | TEdot _ ->
    let e_code, e_data = compile_left_value (depth + 1) expr in
    e_code ++ movq (ind rdi) !%rdi, e_data
  (**** statements ****)
  | TEskip -> nop, nop
  | TEcall (f, args) ->
    (* push each parameters on the stack (in reverse order: n, n-1, ..., 2, 1) and then call the function *)
    (* for now, caller-saver registers are not used of them -> no save and restore  *)
    let args_code, args_data =
      args
      |> List.rev
      |> concat_code_data
           (fun arg ->
              let compiled_arg_code, compiled_arg_data = compile_expr (depth + 1) arg in
              compiled_arg_code ++ pushq !%rdi, compiled_arg_data)
           ~start_code:(depth_comment depth ("[begin] call of function " ^ f.fn_name))
    in
    ( args_code
      ++ call f.fn_name
      (* pop the stack with the right size to remove all the function call arguments at once *)
      ++ (let pop_size =
            args |> List.fold_left (fun acc a -> acc + sizeof_typ a.expr_typ) 0
          in
          addq (imm pop_size) !%rsp)
      ++ depth_comment depth ("[end] call of function " ^ f.fn_name)
    , args_data )
  | TEassign ([ left_expr ], [ value ]) ->
    (* store value expressions on the stack at the variable's offset *)
    let lv_code, lv_data = compile_left_value (depth + 1) left_expr in
    let value_code, value_data = compile_expr (depth + 1) value in
    ( depth_comment
        depth
        (Format.asprintf "[begin] variable assignment for '%a'" Pretty.expr left_expr)
      ++ comment "value code"
      ++ value_code
      (* store value result (rdi) on the stack *)
      ++ pushq !%rdi
      ++ comment "lv code"
      ++ lv_code
      (* recover value result in register r8 *)
      ++ popq r8
      ++ movq !%r8 (ind rdi)
      ++ depth_comment depth "[end] variables assignment"
    , value_data ++ lv_data )
  (* multiple assignment are rewritten into single ones *)
  | TEassign _ -> failwith "unreachable (multiple TEassign)"
  (* all variables declarations are grouped at the top of the function *)
  | TEvars _ -> nop, nop
  | TEif (b, e1, e2) ->
    let compiled_condition = compile_expr (depth + 1) b in
    let lbl_end_if = new_label ()
    and lbl_else = new_label () in
    let e_code_if, e_data_if = compile_expr (depth + 1) e1 in
    let e_code_else, e_data_else = compile_expr (depth + 1) e2 in
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
          ++ e_code_if
          ++ jmp lbl_end_if
          (* else body *)
          ++ label lbl_else
          ++ e_code_else
          ++ label lbl_end_if
        , e_data_if ++ e_data_else )
      ]
  | TEreturn l ->
    let e_code, e_data =
      match l with
      | [] -> nop, nop
      | [ e ] -> compile_expr depth e
      | _ -> failwith "unreachable (TEreturn)"
    in
    ( (* compute return value *)
      e_code
      ++
      (* restore stack frame *)
      movq !%rbp !%rsp
      ++ popq rbp
      (* return from function *)
      ++ ret
    , e_data )
  | TEblock el -> concat_code_data (compile_expr (depth + 1)) el
  | TEfor (c, b) ->
    let cond_lbl = new_label ()
    and body_lbl = new_label () in
    let compiled_condition = compile_expr (depth + 1) c in
    let compiled_body = compile_expr (depth + 1) b in
    concat_code_data
      Fun.id
      [ jmp cond_lbl ++ label body_lbl, nop
      ; compiled_body
      ; label cond_lbl, nop
      ; compiled_condition
      ; cmpb (imm 0) !%dil ++ jnz body_lbl, nop
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
  (* when executed, the generated code will leave the address of the left value in rdi *)
  match expr.expr_desc with
  (* since all the variables are stack-allocated, the adress of a variable is rbp + the variable offset *)
  | TEident v -> movq !%rbp !%rdi ++ addq (imm v.v_ofs) !%rdi, nop
  (* the address of *e is just the value of e (because e is a pointer) *)
  (* so we just need to get the value of e *)
  (* this way, we return the address referenced by the pointer (i.e. its value) *)
  | TEunop (Ustar, ({ expr_typ = Tptr _; _ } as e)) -> compile_expr (depth + 1) e
  (* star can only be used on pointers *)
  | TEunop (Ustar, _) -> failwith "unreachable (compile_left_value - star on non-pointer)"
  (* to get the address of e.f, we first need the address of e, and then we add the offset of the field f *)
  (* if e is a pointer, then we must also follow it *)
  | TEdot (e, f) ->
    let e_code, e_data = compile_left_value (depth + 1) e in
    ( e_code
      (* if the expression is a pointer, add a dereference *)
      ++ (match e.expr_typ with
        | Tptr _ -> movq (ind rdi) !%rdi
        | _ -> nop)
      ++ addq (imm f.f_ofs) !%rdi
    , e_data )
  | _ -> failwith "unreachable (compile_left_value)"
;;

(* find all the variables declared in a block (typically, the body of a function) *)
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
    | TEif (_, b1, b2) -> [ b1; b2 ] |> List.fold_left aux acc
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
      offset := !offset - sizeof_typ var.v_typ;
      var.v_ofs <- !offset);
    (* offset starts at 0 and is subtracted the size of each variable, so the total variable size is just its opposite *)
    - !offset
  in
  (* compute the offset of each parameter *)
  let _ =
    let offset = ref 8 in
    tfunc.fn_params
    |> List.iter (fun v ->
      offset := !offset + sizeof_typ v.v_typ;
      v.v_ofs <- !offset)
  in
  ();
  (* compile function body *)
  let body_code, body_data = compile_expr 0 tbody in
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
    ++ movq !%rbp !%rsp
    ++ popq rbp
    ++
    (* set return code for main *)
    (if tfunc.fn_name = "main"
     then comment "main must return 0" ++ xorq !%rax !%rax
     else nop)
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
    |> concat_code_data (function
      | TDstruct s ->
        compute_struct_size_and_offsets s;
        nop, nop
      | TDfunction (tfunc, tbody) -> compile_func tfunc tbody)
  in
  { text =
      globl "main"
      ++ code
      ++ comment "some auxiliary assembly functions"
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
