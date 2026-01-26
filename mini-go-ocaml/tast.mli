
(** Typed syntax trees *)

type unop = Ast.unop

type binop = Ast.binop

type constant = Ast.constant

type incdec = Ast.incdec

type function_ = {
    fn_name: string;
  fn_params: var list;
     fn_typ: typ list;
}

and structure = {
          s_name: string;
        s_fields: (string, field) Hashtbl.t;
  mutable s_list: field list;
  mutable s_size: int; (** total size in bytes *)
}

and typ =
  | Tint | Tbool | Tstring
  | Tstruct of structure
  | Tptr of typ
  | Tnil (** to type nil *)
  | Tmany of typ list (** when 0 or >= 2 return types *)

and var = {
          v_name: string;
            v_id: int; (** unique *)
           v_loc: Ast.location;
           v_typ: typ;
  mutable v_used: bool;
  mutable v_addr: bool; (** means &x is used somewhere *)
  mutable  v_ofs: int; (** relative to %rbp *)
}

and field = {
         f_name: string;
          f_typ: typ;
  mutable f_ofs: int; (** relative to the start of the structure *)
}

and expr =
  { expr_desc: expr_desc;
    expr_typ : typ; }

and expr_desc =
  | TEskip
  | TEconstant of constant
  | TEbinop of binop * expr * expr
  | TEunop of unop * expr
  | TEnil
  | TEnew of typ
  | TEcall of function_ * expr list
  | TEident of var
  | TEdot of expr * field
  | TEassign of expr list * expr list
  | TEvars of var list
  | TEif of expr * expr * expr
  | TEreturn of expr list
  | TEblock of expr list
  | TEfor of expr * expr
  | TEprint of expr list
  | TEincdec of expr * incdec

type tdecl =
  | TDfunction of function_ * expr
  | TDstruct   of structure

type tfile = tdecl list
