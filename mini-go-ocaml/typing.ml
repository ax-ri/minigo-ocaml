(** Static type checking of Mini Go programs *)

open Lib
open Ast
open Tast

let debug : bool ref = ref false
let dummy_loc : location = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string

(** use this function to report errors; it is a printf-like function, eg.

    errorm ~loc "bad arity %d for function %s" n f

*)
let errorm ?(loc = dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")
;;

(** use this function to create variable, so that they all have a
    unique id if field `v_id` *)
let new_var : string -> Ast.location -> typ -> var =
  let id = ref 0 in
  fun x loc ty ->
    incr id;
    { v_name = x
    ; v_id = !id
    ; v_loc = loc
    ; v_typ = ty
    ; v_used = false
    ; v_addr = false
    ; v_ofs = -1
    }
;;

(* find the first duplicate element in a list, and returns it *)
let find_first_duplicate (mapper : 'a -> 'b) (l : 'a list) : 'a option =
  let rec check (acc : 'b list) (l : 'a list) : 'a option =
    match l with
    | [] -> None
    | t :: q ->
      let m = mapper t in
      if List.mem m acc then Some t else check (m :: acc) q
  in
  check [] l
;;

(* Represent the typing environment *)
module TypeEnv = struct
  type t =
    { functions : (string, function_) Hashtbl.t
    ; structures : (string, structure) Hashtbl.t
    ; variables : (string, var) Hashtbl.t
    ; import_fmt : import_fmt
    ; mutable fmt_used : bool
    }

  (* create a new typing environment *)
  let create (import_fmt : import_fmt) : t =
    { functions = Hashtbl.create 8
    ; structures = Hashtbl.create 8
    ; variables = Hashtbl.create 8
    ; import_fmt
    ; fmt_used = false
    }
  ;;

  (* create a new typing environment by copying an already existing one *)
  let clone (tenv : t) : t =
    { functions = Hashtbl.copy tenv.functions
    ; structures = Hashtbl.copy tenv.structures
    ; variables = Hashtbl.copy tenv.variables
    ; import_fmt = tenv.import_fmt
    ; fmt_used = tenv.fmt_used
    }
  ;;
end

(* Helpers functions to deal with types *)
module TypeHelpers = struct
  (* check that a ptyp is well formed, in the sense of the typing rules *)
  let rec is_ptyp_well_formed (tenv : TypeEnv.t) : ptyp -> bool = function
    | PTident { id; loc } ->
      (match id with
       | "bool" | "int" | "string" -> true
       | id -> Hashtbl.mem tenv.structures id)
    | PTptr t -> is_ptyp_well_formed tenv t
  ;;

  (* convert an AST type to a TAST type *)
  let rec typ_of_ptyp (tenv : TypeEnv.t) (ptyp : ptyp) : typ =
    match ptyp with
    | PTident ident ->
      (match ident with
       | { id = "bool"; _ } -> Tbool
       | { id = "string"; _ } -> Tstring
       | { id = "int"; _ } -> Tint
       | { id; loc } ->
         (match Hashtbl.find_opt tenv.structures id with
          | Some s -> Tstruct s
          | None -> errorm ~loc "unbound structure type '%s'" id))
    | PTptr t -> Tptr (typ_of_ptyp tenv t)
  ;;

  (* convert a TAST type list to a TAST type *)
  let typ_of_typ_list (types : typ list) : typ =
    match types with
    | [ hd ] -> hd
    | l -> Tmany l
  ;;

  let map_typ_to_typ_list (f : typ -> 'a) (typ : typ) : 'a list =
    match typ with
    | Tmany l -> l |> List.map f
    | t -> [ f t ]
  ;;

  (* convert a TAST type to a TAST type list *)
  let typ_list_of_typ (typ : typ) : typ list = map_typ_to_typ_list Fun.id typ

  (* equality operator for TAST types, because the structural operator (=) sometimes fails for recursive types *)
  let rec are_typ_equals (a : typ) (b : typ) : bool =
    match a, b with
    | Tint, Tint -> true
    | Tbool, Tbool -> true
    | Tstring, Tstring -> true
    | Tstruct s1, Tstruct s2 -> s1.s_name = s2.s_name
    | Tptr t1, Tptr t2 -> are_typ_equals t1 t2
    | Tptr _, Tnil | Tnil, Tptr _ -> true
    | Tnil, Tnil -> true
    | Tmany tl1, Tmany tl2 ->
      (try List.for_all2 are_typ_equals tl1 tl2 with
       | Invalid_argument _ -> false)
    | _ -> false
  ;;
end

(* Helpers functions for typing expressions *)
module Helpers = struct
  (* tell whether all the identifiers are unique in the list *)
  let check_identifiers_uniqueness (ids : ident list) : unit =
    (* check whether each identifier is unique *)
    match ids |> find_first_duplicate (fun { id; _ } -> id) with
    | Some { id; loc } -> errorm ~loc "duplicate identifier '%s' in identifier list" id
    | None -> ()
  ;;

  (* tell whether all the types are well-formed *)
  let check_types (tenv : TypeEnv.t) (loc : location) (types : ptyp list) =
    types
    |> List.iter (fun t ->
      if not (TypeHelpers.is_ptyp_well_formed tenv t) then errorm ~loc "invalid type")
  ;;

  (* tell whether all return statements in a block have the same type *)
  let are_returns_homogeneous (expected_ret_type : typ) (block : expr) : bool =
    let rec aux (e : expr) =
      match e.expr_desc, e.expr_typ with
      | TEreturn _, t -> TypeHelpers.are_typ_equals t expected_ret_type
      | TEif (_, e1, e2), _ -> aux e1 && aux e2
      | TEblock l, _ -> l |> List.fold_left (fun acc e -> acc && aux e) true
      | TEfor (_, e), _ -> aux e
      | _ -> true
    in
    aux block
  ;;

  (* check that all the branches in a block have a return statement *)
  let rec check_all_branches_reach_return (e : expr) : bool =
    match e.expr_desc with
    | TEreturn _ -> true
    | TEif (_, b1, b2) ->
      check_all_branches_reach_return b1 && check_all_branches_reach_return b2
    | TEblock b ->
      (match List.rev b with
       | [] -> false
       | e :: _ -> check_all_branches_reach_return e)
    | _ -> false
  ;;

  (* for a given struct, tell whether all the types of its fields have a valid type (no recursive reference to the same struct)  *)
  let check_struct_fields_types (s : structure) : unit =
    let struct_name = s.s_name in
    let rec check_fields (s : structure) : unit =
      s.s_list |> List.iter (fun field -> check_typ field.f_typ)
    and check_typ (typ : typ) : unit =
      match typ with
      | Tint | Tbool | Tstring | Tptr _ | Tnil -> ()
      | Tmany l -> l |> List.iter check_typ
      | Tstruct s' ->
        if s'.s_name = struct_name
        then errorm "structure '%s' uses itself recursively without pointer" struct_name
        else check_fields s'
    in
    check_fields s
  ;;
end

module PreRewrite = struct
  type gen_id =
    | Id of ident
    | Dot of (string * gen_id)

  (* default values based on types:
      - int:    0
      - bool:   false
      - string: ""
      - *tau:   nil 
  *)
  let default_type_value (pexpr_loc : location) (tau : typ) : pexpr =
    match tau with
    | Tint -> { pexpr_desc = PEconstant (Cint 0L); pexpr_loc }
    | Tbool -> { pexpr_desc = PEconstant (Cbool false); pexpr_loc }
    | Tstring -> { pexpr_desc = PEconstant (Cstring ""); pexpr_loc }
    | Tptr _ -> { pexpr_desc = PEnil; pexpr_loc }
    | _ -> failwith "unreachable"
  ;;

  let rec generate_initialization_data
            (pexpr_loc : location)
            (tau_opt : typ option)
            (ident_list : ident list)
            (pexpr_list : pexpr list)
    : gen_id list * pexpr list
    =
    let gen_simple_id_list () : gen_id list = ident_list |> List.map (fun id -> Id id) in
    let (ident_pexpr_list, init_values) : gen_id list * pexpr list =
      match tau_opt, pexpr_list with
      | Some (Tstruct s), [] ->
        let ident_pexpr_list, init_values =
          ident_list
          |> List.map (fun id ->
            s.s_list
            |> List.map (fun f ->
              let ident_pexpr_list, init_values =
                generate_initialization_data
                  pexpr_loc
                  (Some f.f_typ)
                  [ { id = f.f_name; loc = pexpr_loc } ]
                  []
              in
              let ident_pexpr_list =
                ident_pexpr_list |> List.map (fun gid -> Dot (id.id, gid))
              in
              ident_pexpr_list, init_values)
            |> List.split)
          |> List.split
        in
        ( ident_pexpr_list |> List.concat |> List.concat
        , init_values |> List.concat |> List.concat )
      | Some (Tstruct s), _ ->
        errorm ~loc:pexpr_loc "structure initialization is not supported"
      | Some tau, [] ->
        ( gen_simple_id_list ()
        , List.init (List.length ident_list) (fun _ -> default_type_value pexpr_loc tau) )
      | Some tau, pexpr_list -> gen_simple_id_list (), pexpr_list
      | None, [] ->
        errorm
          ~loc:pexpr_loc
          "need either type or initialization value for variable declaration"
      | None, pexpr_list -> gen_simple_id_list (), pexpr_list
    in
    ident_pexpr_list, init_values
  ;;

  let pexpr_of_gen_id (pexpr_loc : location) (gid : gen_id) : pexpr =
    let rec flatten_rev (acc : ident list) (gid : gen_id) : ident list =
      match gid with
      | Id id -> id :: acc
      | Dot (s, d) -> flatten_rev ({ id = s; loc = pexpr_loc } :: acc) d
    in
    let l = flatten_rev [] gid in
    List.fold_right
      (fun id (acc : pexpr) : pexpr ->
         match acc with
         | { pexpr_desc = PEnil; _ } -> { pexpr_desc = PEident id; pexpr_loc = id.loc }
         | _ -> { pexpr_desc = PEdot (acc, id); pexpr_loc = id.loc })
      l
      { pexpr_desc = PEnil; pexpr_loc }
  ;;

  let expand_vars_initialization (tenv : TypeEnv.t) (block_exprs : pexpr list)
    : pexpr list
    =
    let rec aux (acc : pexpr list) (pexpr_list : pexpr list) : pexpr list =
      match pexpr_list with
      | [] -> List.rev acc
      | ({ pexpr_desc = PEvars (ident_list, ptyp_opt, pexpr_list); pexpr_loc } as expr)
        :: q ->
        let tau_opt = Option.map (TypeHelpers.typ_of_ptyp tenv) ptyp_opt in
        let gen_id_list, init_values =
          generate_initialization_data pexpr_loc tau_opt ident_list pexpr_list
        in
        let pexpr_desc =
          PEassign (gen_id_list |> List.map (pexpr_of_gen_id pexpr_loc), init_values)
        in
        aux ({ pexpr_desc; pexpr_loc } :: expr :: acc) q
      | s :: q -> aux (s :: acc) q
    in
    block_exprs |> aux []
  ;;
end

(* expression typing function: convert an AST expression to a TAST expression *)
(* this function also handles statements as they are not separated from expressions *)
let rec expr (tenv : TypeEnv.t) (pexpr : Ast.pexpr) : Tast.expr =
  match pexpr.pexpr_desc with
  (**** expressions ****)
  | PEskip -> { expr_desc = TEskip; expr_typ = Tnil }
  | PEconstant c ->
    let expr_typ =
      match c with
      | Cbool _ -> Tbool
      | Cint _ -> Tint
      | Cstring _ -> Tstring
    in
    { expr_desc = TEconstant c; expr_typ }
  | PEbinop (binop, pe1, pe2) ->
    (match binop with
     | Badd | Bsub | Bmul | Bdiv | Bmod ->
       let te1 = expr tenv pe1 in
       let te2 = expr tenv pe2 in
       if te1.expr_typ <> Tint || te2.expr_typ <> Tint
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong types for binary operation '%s': expected 'int', found '%a' and '%a'"
           (Pretty.binop binop)
           Pretty.typ
           te1.expr_typ
           Pretty.typ
           te2.expr_typ;
       { expr_desc = TEbinop (binop, te1, te2); expr_typ = Tint }
     | Beq | Bne ->
       let te1 = expr tenv pe1 in
       let te2 = expr tenv pe2 in
       if not (TypeHelpers.are_typ_equals te1.expr_typ te2.expr_typ)
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong types for binary operation '%s': both expressions must have the same \
            type"
           (Pretty.binop binop);
       if te1.expr_typ = Tnil && te2.expr_typ = Tnil
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong types for binary operation '%s': both types are nil"
           (Pretty.binop binop);
       { expr_desc = TEbinop (binop, te1, te2); expr_typ = Tbool }
     | Blt | Ble | Bgt | Bge ->
       let te1 = expr tenv pe1 in
       let te2 = expr tenv pe2 in
       if te1.expr_typ <> Tint || te2.expr_typ <> Tint
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong types for binary operation '%s': expected 'int', found '%a' and '%a'"
           (Pretty.binop binop)
           Pretty.typ
           te1.expr_typ
           Pretty.typ
           te2.expr_typ;
       { expr_desc = TEbinop (binop, te1, te2); expr_typ = Tbool }
     | Band | Bor ->
       let te1 = expr tenv pe1 in
       let te2 = expr tenv pe2 in
       if te1.expr_typ <> Tbool || te2.expr_typ <> Tbool
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong types for binary operation '%s': expected 'bool', found '%a' and '%a'"
           (Pretty.binop binop)
           Pretty.typ
           te1.expr_typ
           Pretty.typ
           te2.expr_typ;
       { expr_desc = TEbinop (binop, te1, te2); expr_typ = Tbool })
  | PEunop (unop, pe) ->
    (match unop with
     | Uneg ->
       let te = expr tenv pe in
       if te.expr_typ <> Tint
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong type for unary operation '%s': expected 'int', found '%a'"
           (Pretty.unop unop)
           Pretty.typ
           te.expr_typ;
       { expr_desc = TEunop (unop, te); expr_typ = Tint }
     | Unot ->
       let te = expr tenv pe in
       if te.expr_typ <> Tbool
       then
         errorm
           ~loc:pexpr.pexpr_loc
           "wrong type for unary operation '%s': expected 'bool', found '%a'"
           (Pretty.unop unop)
           Pretty.typ
           te.expr_typ;
       { expr_desc = TEunop (unop, te); expr_typ = Tbool }
     | Uamp ->
       let te = expr_left_value tenv pe in
       (* if the operand is a variable v, retain the fact that &v is used *)
       (match te.expr_desc with
        | TEident v ->
          v.v_addr <- true;
          v.v_used <- true
        | _ -> ());
       { expr_desc = TEunop (unop, te); expr_typ = Tptr te.expr_typ }
     | Ustar -> expr_left_value tenv pexpr)
  | PEnil -> { expr_desc = TEnil; expr_typ = Tnil }
  | PEcall (id, pel) ->
    (match Hashtbl.find_opt tenv.functions id.id with
     (* function call fmt.Print *)
     | None when id.id = "fmt.Print" ->
       if not tenv.import_fmt
       then errorm ~loc:id.loc "import of module 'fmt' is required to use 'fmt.Print'";
       tenv.fmt_used <- true;
       { expr_desc = TEprint (pel |> List.map (expr tenv)); expr_typ = Tmany [] }
     (* function call new (for structure) *)
     | None when id.id = "new" ->
       (match pel with
        | [ e ] ->
          let te = expr tenv e in
          (match te.expr_typ with
           | Tstruct s ->
             let structure = Hashtbl.find_opt tenv.structures s.s_name in
             (match structure with
              | None -> errorm ~loc:pexpr.pexpr_loc "structure '%s' not found" s.s_name
              | Some str ->
                { expr_desc = TEnew (Tptr te.expr_typ); expr_typ = Tptr te.expr_typ })
           | _ -> errorm ~loc:pexpr.pexpr_loc "cannot call 'new' on a non-structure type")
        | _ -> errorm ~loc:pexpr.pexpr_loc "cannot call 'new' to multiple arguments")
     (* function is used but never declared *)
     | None -> errorm ~loc:pexpr.pexpr_loc "function '%s' not found" id.id
     (* function has been declared *)
     | Some f ->
       let arguments =
         match pel with
         (* actual parameters of function is another function -> need to get all the types of the second function first *)
         | [ ({ pexpr_desc = PEcall (id, params); pexpr_loc = loc } as pecall) ] ->
           if f.fn_params = []
           then errorm ~loc "too many arguments for function '%s'" f.fn_name;
           let g = expr tenv pecall in
           let g_returned_types = TypeHelpers.typ_list_of_typ g.expr_typ in
           List.iter2
             (fun param arg_typ ->
                if not (TypeHelpers.are_typ_equals param.v_typ arg_typ)
                then errorm ~loc "invalid argument type for function '%s'" f.fn_name)
             f.fn_params
             g_returned_types;
           [ g ]
         | pel ->
           (try
              List.iter2
                (fun pe param ->
                   let te = expr tenv pe in
                   let typ = param.v_typ in
                   if not (TypeHelpers.are_typ_equals te.expr_typ typ)
                   then
                     errorm
                       ~loc:pexpr.pexpr_loc
                       "invalid argument type for function '%s'"
                       f.fn_name)
                pel
                f.fn_params
            with
            | Invalid_argument _ ->
              errorm
                ~loc:pexpr.pexpr_loc
                "invalid argument count for function call '%s'"
                f.fn_name);
           pel |> List.map (expr tenv)
       in
       { expr_desc = TEcall (f, arguments)
       ; expr_typ = TypeHelpers.typ_of_typ_list f.fn_typ
       })
  | PEident id ->
    (match Hashtbl.find_opt tenv.structures id.id with
     | Some s -> { expr_desc = TEskip; expr_typ = Tstruct s }
     | None ->
       if id.id = "_" then errorm ~loc:pexpr.pexpr_loc "cannot use variable '_'";
       (match Hashtbl.find_opt tenv.variables id.id with
        | Some v -> v.v_used <- true
        | None -> ());
       expr_left_value tenv pexpr)
  | PEdot (pe, id) ->
    let te = expr tenv pe in
    (match te.expr_typ with
     | Tstruct s | Tptr (Tstruct s) ->
       (match Hashtbl.find_opt s.s_fields id.id with
        | None ->
          errorm
            ~loc:pexpr.pexpr_loc
            "structure '%s' has no field named '%s'"
            s.s_name
            id.id
        | Some field -> { expr_desc = TEdot (te, field); expr_typ = field.f_typ })
     | _ -> errorm ~loc:pexpr.pexpr_loc "accessing a field of a non-struct type")
  (**** statements ****)
  | PEassign (left_pexpr, right_pexpr) ->
    let left_expr = left_pexpr |> List.map (expr_left_value tenv)
    and right_expr_and_types : (expr * typ) list =
      match right_pexpr with
      | [ ({ pexpr_desc = PEcall (id, arg); _ } as pecall) ] ->
        let f = expr tenv pecall in
        TypeHelpers.map_typ_to_typ_list (fun x -> f, x) f.expr_typ
      | _ ->
        right_pexpr
        |> List.map (fun pe ->
          let te = expr tenv pe in
          te, te.expr_typ)
    in
    (try
       List.iter2
         (fun { expr_typ = t1; _ } (_, t2) ->
            if not (TypeHelpers.are_typ_equals t1 t2)
            then
              errorm
                ~loc:pexpr.pexpr_loc
                "cannot assign value of type '%a' to variable of type '%a'"
                Pretty.typ
                t2
                Pretty.typ
                t1)
         left_expr
         right_expr_and_types
     with
     | Invalid_argument _ ->
       errorm ~loc:pexpr.pexpr_loc "to few or to many values to assign to variables");
    { expr_desc = TEassign (left_expr, right_expr_and_types |> List.map fst)
    ; expr_typ = TypeHelpers.typ_of_typ_list (right_expr_and_types |> List.map snd)
    }
  | PEvars (ident_list, ptyp_opt, pexpr_list) ->
    let var_types : typ list =
      find_var_types tenv pexpr.pexpr_loc ptyp_opt ident_list pexpr_list
    in
    (* for each declared variable, create a variable and add it to the environment *)
    let var_list =
      try
        List.map2
          (fun id typ ->
             let v = new_var id.id id.loc typ in
             Hashtbl.add tenv.variables id.id v;
             v)
          ident_list
          var_types
      with
      | Invalid_argument _ ->
        errorm
          ~loc:pexpr.pexpr_loc
          "cannot assign '%d' values to '%d' variables (in single-value mode)"
          (List.length var_types)
          (List.length ident_list)
    in
    { expr_desc = TEvars var_list; expr_typ = Tnil }
  | PEif (pe, b1, b2) ->
    let te = expr tenv pe in
    (match te.expr_typ with
     | Tbool ->
       let tb1 = expr tenv b1 in
       let tb2 = expr tenv b2 in
       { expr_desc = TEif (te, tb1, tb2); expr_typ = Tnil }
     | t -> errorm ~loc:pexpr.pexpr_loc "conditional expression must be of boolean type")
  | PEreturn pel ->
    let tel = pel |> List.map (fun pe -> expr tenv pe) in
    { expr_desc = TEreturn tel
    ; expr_typ = TypeHelpers.typ_of_typ_list (tel |> List.map (fun e -> e.expr_typ))
    }
  | PEblock pel ->
    let rec aux
              (tenv : TypeEnv.t)
              (block_statements : Ast.pexpr list)
              (block_var_names : string list)
              (acc : expr list)
      : expr list
      =
      match block_statements with
      (* no more statements to process *)
      | [] ->
        (* for each variable that was introduced in this block, check that it is used and remove it from the typing environment *)
        block_var_names
        |> List.iter (fun id ->
          (*  check that any local variable introduced in block, other than _, is further used *)
          let var = Hashtbl.find tenv.variables id in
          if var.v_name <> "_" && not var.v_used
          then errorm ~loc:var.v_loc "unused variable '%s'" var.v_name;
          (* remove the variable from the environment *)
          Hashtbl.remove tenv.variables id);
        (* return the accumulator with the list of typed expressions in the block *)
        acc
      (* process the current statement *)
      | s :: q ->
        let te = expr tenv s in
        (* if the current statement contains variables declarations: *)
        let block_var_names =
          match s.pexpr_desc with
          | PEvars (ident_list, tau, pexpr_list) ->
            (* - update the list of block variables *)
            let new_var_names =
              ident_list
              |> List.map (fun { id; loc } ->
                if id <> "_" && List.mem id block_var_names
                then errorm ~loc "cannot redeclare a variable named '%s' in same block" id
                else id)
            in
            (* check for duplicates inside the identifier list *)
            (match find_first_duplicate Fun.id new_var_names with
             | Some id when id <> "_" ->
               errorm ~loc:pexpr.pexpr_loc "cannot redeclare a variable named '%s'" id
             | _ -> ());
            new_var_names @ block_var_names
          | _ -> block_var_names
        in
        aux tenv q block_var_names (te :: acc)
    in
    let pel = PreRewrite.expand_vars_initialization tenv pel in
    { expr_desc = TEblock (List.rev (aux tenv pel [] [])); expr_typ = Tnil }
  | PEfor (pe, b) ->
    let te = expr tenv pe in
    (match te.expr_typ with
     | Tbool ->
       let tb = expr tenv b in
       { expr_desc = TEfor (te, tb); expr_typ = Tnil }
     | _ -> errorm ~loc:pexpr.pexpr_loc "conditional expression must be of boolean type")
  | PEincdec (pe, incdec) ->
    let te = expr_left_value tenv pe in
    (match te.expr_desc with
     | TEident v -> v.v_used <- true
     | _ -> ());
    (match te.expr_typ with
     | Tint -> { expr_desc = TEincdec (te, incdec); expr_typ = Tint }
     | t ->
       errorm
         ~loc:pexpr.pexpr_loc
         "wrong type for increase/decrease operation: expected 'int', found '%a'"
         Pretty.typ
         t)

and
    (* same as the expression function, but also check that the expression is a left value *)
      expr_left_value
      (tenv : TypeEnv.t)
      (pe : Ast.pexpr)
  : Tast.expr
  =
  match pe.pexpr_desc with
  | PEunop (Ustar, x) ->
    let te = expr tenv x in
    (match te.expr_typ with
     | Tptr typ -> { expr_desc = TEunop (Ustar, te); expr_typ = typ }
     | _ ->
       errorm
         ~loc:pe.pexpr_loc
         "wrong type for unary operation '%s': expected 'ptr_', found '%a'"
         (Pretty.unop Ustar)
         Pretty.typ
         te.expr_typ)
  | PEident id ->
    (match Hashtbl.find_opt tenv.variables id.id with
     | None -> errorm ~loc:pe.pexpr_loc "unbound variable '%s'" id.id
     | Some v -> { expr_desc = TEident v; expr_typ = v.v_typ })
  | PEdot (e, f) ->
    let _ = expr_left_value tenv e in
    expr tenv pe
  | _ -> errorm ~loc:pe.pexpr_loc "cannot use this value as a left value"

and
    (* auxiliary function to deduce the types of a list of variables (used for PEVars) *)
      find_var_types
      (tenv : TypeEnv.t)
      (loc : location)
      (ptyp_opt : ptyp option)
      (ident_list : ident list)
      (pexpr_list : pexpr list)
  : typ list
  =
  match ptyp_opt with
  (* no type provided for declaration => need to deduce the type from initialization values *)
  | None ->
    (match pexpr_list with
     (* special case for initialization with a function call *)
     (* types list is the return type of the function *)
     | [ ({ pexpr_desc = PEcall (id, arg); pexpr_loc = _ } as pe) ] ->
       let f = expr tenv pe in
       f.expr_typ |> TypeHelpers.typ_list_of_typ
     (* otherwise, we need to type each expression to get their types *)
     | _ ->
       pexpr_list
       |> List.map (fun pe ->
         let te = expr tenv pe in
         if te.expr_typ = Tnil
         then errorm ~loc "use of untyped nil in variable declaration";
         te.expr_typ))
  (* a type is provided for the declaration; in that case, all the variables have this type. *)
  | Some ptyp ->
    if not (TypeHelpers.is_ptyp_well_formed tenv ptyp)
    then errorm ~loc "unbound type for this variable(s)";
    (* extract the specified type *)
    let tau = TypeHelpers.typ_of_ptyp tenv ptyp in
    (* build a verifying function from this reference type *)
    let value_type_checker =
      List.iter (fun typ ->
        if not (TypeHelpers.are_typ_equals typ tau)
        then
          errorm
            ~loc
            "cannot declare a variable of type '%a' with a value of type '%a'"
            Pretty.typ
            tau
            Pretty.typ
            typ)
    in
    (* apply this verifying function to the initialization expressions *)
    (match pexpr_list with
     (* no initialization values specified => nothing to do (will set reference type for each variable) *)
     | [] -> ()
     (* variables initialized with a function call *)
     | [ ({ pexpr_desc = PEcall (id, arg); pexpr_loc = _ } as pe) ] ->
       (* check that function f exists and only returns values of reference type *)
       let f = expr tenv pe in
       f.expr_typ |> TypeHelpers.typ_list_of_typ |> value_type_checker
     (* variables initialized with a list of expressions *)
     | _ ->
       pexpr_list
       |> List.map (fun pe ->
         let te = expr tenv pe in
         te.expr_typ)
       |> value_type_checker);
    (* the type of each variable is the reference type *)
    List.init (List.length ident_list) (fun _ -> tau)
;;

(* top-level typing rule: convert an AST file to a TAST file *)
let file ~debug:b ((imp, dl) : Ast.pfile) : Tast.tfile =
  debug := b;
  let tenv = TypeEnv.create imp in
  let function_bodies : (string, expr) Hashtbl.t = Hashtbl.create 8 in
  (**** 1 ****)
  dl
  |> List.iter (function
    (* We add all the structures (but not their fields) to the environment, checking the uniqueness of the structure names *)
    | PDstruct { ps_name; _ } ->
      if Hashtbl.mem tenv.structures ps_name.id
      then errorm ~loc:ps_name.loc "multiple definitions of structure '%s'" ps_name.id
      else
        Hashtbl.add
          tenv.structures
          ps_name.id
          { s_name = ps_name.id
          ; (* will be populated later *)
            s_fields = Hashtbl.create 8
          ; s_list = []
          ; s_size = 0
          }
    | _ -> ());
  (**** 2 ****)
  dl
  |> List.iter (function
    (* 2.a 
      We add all the functions to the environment, checking the uniqueness of the function names. For a function declaration of the form
        func f (x1 : τ1 , . . . , xn : τn) (τ1 ′ , . . . , τm′) {b}
      we check that the xi are pairwise distinct and that all types τi and τj′ are well-formed.
    *)
    | PDfunction { pf_name; pf_params; pf_typ; _ } ->
      if Hashtbl.mem tenv.functions pf_name.id
      then errorm ~loc:pf_name.loc "multiple definitions of function '%s'" pf_name.id;
      Helpers.check_identifiers_uniqueness (pf_params |> List.map fst);
      Helpers.check_types tenv pf_name.loc (pf_params |> List.map snd);
      Helpers.check_types tenv pf_name.loc pf_typ;
      (* construct a function *)
      let func : function_ =
        { fn_name = pf_name.id
        ; fn_params =
            pf_params
            |> List.map (fun ({ id; loc }, ptyp) ->
              new_var id loc (TypeHelpers.typ_of_ptyp tenv ptyp))
        ; fn_typ = pf_typ |> List.map (TypeHelpers.typ_of_ptyp tenv)
        }
      in
      (* add it to the environment *)
      Hashtbl.add tenv.functions pf_name.id func
    (* 2.b
      We check and add all the structure fields to the environment. For a structure declaration of the form
        type S struct { x1 : τ1 , . . . , xn : τn }
      we check that the xi are pairwise distinct and that all types τi are well-formed.
    *)
    | PDstruct { ps_name; ps_fields } ->
      Helpers.check_identifiers_uniqueness (ps_fields |> List.map fst);
      Helpers.check_types tenv ps_name.loc (ps_fields |> List.map snd);
      (* update the previously added structure in the environment *)
      let s = Hashtbl.find tenv.structures ps_name.id in
      ps_fields
      |> List.iter (fun ({ id; _ }, ptyp) ->
        (* construct a field *)
        let field : field =
          { f_name = id; f_typ = TypeHelpers.typ_of_ptyp tenv ptyp; f_ofs = 0 }
        in
        (* add it to the structure in the environment *)
        Hashtbl.add s.s_fields id field;
        s.s_list <- field :: s.s_list));
  (**** 3 ****)
  dl
  |> List.iter (function
    (* 3.a
      For each function declaration
        func f (x1 : τ1 , . . . , xn : τn) (τ1' , . . . , τm') {b}
      we construct a new environment Γ by adding all the variables xi : τi to the environment containing the structures and functions, 
      and we type the block b in Γ, i.e., we check Γ ⊢ b
    *)
    | PDfunction { pf_name; pf_body; _ } ->
      let f = Hashtbl.find tenv.functions pf_name.id in
      let f_env = TypeEnv.clone tenv in
      f.fn_params |> List.iter (fun v -> Hashtbl.add f_env.variables v.v_name v);
      let body = expr f_env pf_body in
      (* save the fact that fmt was seen during the typing of the body *)
      tenv.fmt_used <- tenv.fmt_used || f_env.fmt_used;
      (* Additionally, we check: *)
      (*  - that every return statement in b returns a list of m values of the expected types τ1′, ..., τm′ *)
      if not (Helpers.are_returns_homogeneous (TypeHelpers.typ_of_typ_list f.fn_typ) body)
      then
        errorm
          ~loc:pf_name.loc
          "in function '%s': different types are returned"
          pf_name.id;
      (*  - if m > 0, that any control-flow branch in b reaches a return statement; *)
      if f.fn_typ <> [] && not (Helpers.check_all_branches_reach_return body)
      then
        errorm
          ~loc:pf_name.loc
          "in function '%s': not all branches return a value"
          f.fn_name;
      (* store the function body for later use *)
      Hashtbl.add function_bodies pf_name.id body
    (* 3.b
      We check that there is no "recursive" structure, that is, no structure S with a field (which contains a field, which contains a field, etc.) of type S,
      without passing through a pointer.
    *)
    | PDstruct { ps_name; _ } ->
      let s = Hashtbl.find tenv.structures ps_name.id in
      Helpers.check_struct_fields_types s);
  (* 
    Finally, we check that there exists a function main without parameters and without return type 
    and that the file contains import "fmt" if and only if there is at least one fmt.Print
    instruction somewhere in the file. 
  *)
  (match Hashtbl.find_opt tenv.functions "main" with
   | None -> errorm "missing required 'main' function"
   | Some f ->
     (match f.fn_params, f.fn_typ with
      | [], [] -> ()
      | _ -> errorm "'main' function must have no parameter and no return type"));
  if tenv.import_fmt && not tenv.fmt_used then errorm "module 'fmt' imported but not used";
  (* build the final typed ast with the structures and functions *)
  Seq.append
    (tenv.structures |> Hashtbl.to_seq_values |> Seq.map (fun s -> TDstruct s))
    (tenv.functions
     |> Hashtbl.to_seq_values
     |> Seq.map (fun f -> TDfunction (f, Hashtbl.find function_bodies f.fn_name)))
  |> List.of_seq
;;
