
(** Mini Go pretty-printer.

  Can be used to inspect the AST after the rewriting pass, just before
  code generation. Activated when command line flag `--debug` is passed.
*)

open Lib
open Format
open Tast

let binop = function
  | Ast.Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "+"
  | Bdiv -> "/"
  | Bmod -> "%"
  | Beq -> "=="
  | Bne -> "!="
  | Blt -> "<"
  | Ble -> "<="
  | Bgt -> ">"
  | Bge -> ">="
  | Band -> "&&"
  | Bor -> "||"
let unop = function
  | Ast.Uneg -> "-"
  | Unot -> "!"
  | Uamp -> "&"
  | Ustar -> "*"

let rec typ fmt = function
  | Tint -> fprintf fmt "int"
  | Tbool -> fprintf fmt "bool"
  | Tstring -> fprintf fmt "string"
  | Tstruct s -> fprintf fmt "%s" s.s_name
  | Tptr ty -> fprintf fmt "*%a" typ ty
  | Tnil -> fprintf fmt "<Tnil>"
  | Tmany tyl -> fprintf fmt "<%a>" (print_list comma typ) tyl

let rec expr fmt e = match e.expr_desc with
  | TEskip -> fprintf fmt ";"
  | TEnil -> fprintf fmt "ni"
  | TEconstant (Cint n) -> fprintf fmt "%Ld" n
  | TEconstant (Cbool b) -> fprintf fmt "%b" b
  | TEconstant (Cstring s) -> fprintf fmt "%S" s
  | TEbinop (op, e1, e2) ->
     fprintf fmt "@[(%a %s@ %a)@]" expr e1 (binop op) expr e2
  | TEunop (op, e1) ->
     fprintf fmt "@[(%s@ %a)@]" (unop op) expr e1
  | TEnew ty ->
     fprintf fmt "new(%a)" typ ty
  | TEcall (f, el) ->
     fprintf fmt "%s(%a)" f.fn_name list el
  | TEident v ->
     fprintf fmt "%s" v.v_name
  | TEdot (e1, f) ->
     fprintf fmt "%a.%s" expr e1 f.f_name
  | TEassign ([], _) | TEassign (_, []) ->
     assert false
  | TEassign ([lvl], [e]) ->
     fprintf fmt "%a = %a" expr lvl expr e
  | TEassign (lvl, el) ->
     fprintf fmt "%a = %a" list lvl list el
  | TEif (e1, e2, e3) ->
     fprintf fmt "if %a@ %a@ %a" expr e1 expr e2 expr e3
  | TEreturn el ->
     fprintf fmt "return %a" list el
  | TEblock bl ->
     block fmt bl
  | TEfor (e1, e2) ->
     fprintf fmt "for %a %a" expr e1 expr e2
  | TEprint el ->
     fprintf fmt "fmt.Print(%a)" list el
  | TEincdec (e1, op) ->
     fprintf fmt "%a%s" expr e1 (match op with Inc -> "++" | Dec -> "--")
  | TEvars vl ->
     fprintf fmt "var %a" (print_list comma var) vl

and var fmt v =
  fprintf fmt "%s" v.v_name

and block fmt bl =
  fprintf fmt "{@\n%a}" (print_list newline expr) bl

and list fmt el =
  print_list comma expr fmt el

let decl fmt = function
  | TDfunction (f, e) ->
     fprintf fmt "@[<hov 2>func %s(%a) %a@]@\n@\n"
       f.fn_name (print_list comma var) f.fn_params expr e
  | TDstruct s ->
     fprintf fmt "type %s struct { ... }@\n" s.s_name

let file fmt dl =
  fprintf fmt "---------@\n";
  List.iter (decl fmt) dl;
  fprintf fmt "---------@\n"

