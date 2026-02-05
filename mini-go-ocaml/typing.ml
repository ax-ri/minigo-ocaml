(** Static type checking of Mini Go programs (TODO) *)

open Format
open Lib
open Ast
open Tast

module TypeEnv = struct
  type t =
    { functions : (string, function_) Hashtbl.t
    ; structures : (string, structure) Hashtbl.t
    ; variables : (string, var) Hashtbl.t
    ; import_fmt : import_fmt
    ; mutable fmt_used : bool
    }

  let create (import_fmt : import_fmt) : t =
    { functions = Hashtbl.create 8
    ; structures = Hashtbl.create 8
    ; variables = Hashtbl.create 8
    ; import_fmt
    ; fmt_used = false
    }
  ;;

  let clone (tenv : t) : t =
    { functions = Hashtbl.copy tenv.functions
    ; structures = Hashtbl.copy tenv.structures
    ; variables = Hashtbl.copy tenv.variables
    ; import_fmt = tenv.import_fmt
    ; fmt_used = tenv.fmt_used
    }
  ;;
end

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

let rec is_type_well_formed (tenv : TypeEnv.t) : ptyp -> bool = function
  | PTident { id; loc } ->
    (match id with
     | "bool" | "int" | "string" -> true
     | id -> Hashtbl.mem tenv.structures id)
  | PTptr t -> is_type_well_formed tenv t
;;

let is_list_pairwise_unique (mapper : 'a -> 'b) (l : 'a list) : 'a option =
  let rec check (acc : 'b list) (l : 'a list) : 'a option =
    match l with
    | [] -> None
    | t :: q ->
      let m = mapper t in
      if List.mem m acc then Some t else check (m :: acc) q
  in
  check [] l
;;

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

let typ_of_ptyp_list (tenv : TypeEnv.t) (types : ptyp list) : typ =
  match types with
  | [ hd ] -> typ_of_ptyp tenv hd
  | l -> Tmany (l |> List.map (typ_of_ptyp tenv))
;;

let typ_of_typ_list (types : typ list) : typ =
  match types with
  | [ hd ] -> hd
  | l -> Tmany l
;;

module Helpers = struct
  (* tell whether all the identifiers are unique in the list *)
  let check_identifiers_uniqueness (ids : ident list) : unit =
    (* check whether each identifier is unique *)
    match ids |> is_list_pairwise_unique (fun { id; _ } -> id) with
    | Some { id; loc } -> errorm ~loc "duplicate identifier '%s' in identifier list" id
    | None -> ()
  ;;

  (* tell whether all the types are well-formed *)
  let check_types (tenv : TypeEnv.t) (loc : location) (types : ptyp list) =
    types
    |> List.iter (fun t ->
      if not (is_type_well_formed tenv t) then errorm ~loc "invalid type")
  ;;

  (* tell whether all return statements in a block have the same type *)
  let are_returns_homogeneous (expected_ret_type : typ) (block : expr) : bool =
    let rec aux (e : expr) =
      match e.expr_desc, e.expr_typ with
      | TEreturn _, t -> t = expected_ret_type
      | TEif (_, e1, e2), _ -> aux e1 && aux e2
      | TEblock l, _ -> l |> List.fold_left (fun acc e -> acc && aux e) true
      | TEfor (_, e), _ -> aux e
      | _ -> true
    in
    aux block
  ;;

  (* tell whether all the branches in a block have a return statement *)
  let rec are_returns_reached (block : expr) : bool =
    match block.expr_desc with
    | TEreturn _ -> true
    | TEif (_, e1, e2) -> are_returns_reached e1 && are_returns_reached e2
    | TEblock l -> l |> List.fold_left (fun acc e -> acc || are_returns_reached e) false
    | TEfor (_, e) -> are_returns_reached e
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

let rec file ~debug:b ((imp, dl) : Ast.pfile) : Tast.tfile =
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
              new_var id loc (typ_of_ptyp tenv ptyp))
        ; fn_typ = typ_of_ptyp_list tenv pf_typ
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
        let field : field = { f_name = id; f_typ = typ_of_ptyp tenv ptyp; f_ofs = 0 } in
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
      if not (Helpers.are_returns_homogeneous f.fn_typ body)
      then
        errorm
          ~loc:pf_name.loc
          "in function '%s': different types are returned"
          pf_name.id;
      (*  - if m > 0, that any control-flow branch in b reaches a return statement; *)
      (match f.fn_typ with
       | Tmany [] -> () (* ignores empty return type *)
       | _ ->
         if not (Helpers.are_returns_reached body)
         then
           errorm
             ~loc:pf_name.loc
             "in function '%s': not all branches return a value"
             f.fn_name);
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
      | [], Tmany [] -> ()
      | _ -> errorm "'main' function must have no parameter and no return type"));
  if tenv.import_fmt && not tenv.fmt_used then errorm "module 'fmt' imported but not used";
  (* build the final typed ast with the structures and functions *)
  Seq.append
    (tenv.structures |> Hashtbl.to_seq_values |> Seq.map (fun s -> TDstruct s))
    (tenv.functions
     |> Hashtbl.to_seq_values
     |> Seq.map (fun f -> TDfunction (f, Hashtbl.find function_bodies f.fn_name)))
  |> List.of_seq

and expr (tenv : TypeEnv.t) ({ pexpr_desc; pexpr_loc } : Ast.pexpr) : Tast.expr =
  match pexpr_desc with
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
           ~loc:pexpr_loc
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
       if te1.expr_typ <> te2.expr_typ
       then
         errorm
           ~loc:pexpr_loc
           "wrong types for binary operation '%s': both expressions must have the same \
            type"
           (Pretty.binop binop);
       if te1.expr_typ = Tnil && te2.expr_typ = Tnil
       then
         errorm
           ~loc:pexpr_loc
           "wrong types for binary operation '%s': both types are null"
           (Pretty.binop binop);
       { expr_desc = TEbinop (binop, te1, te2); expr_typ = Tbool }
     | Blt | Ble | Bgt | Bge ->
       let te1 = expr tenv pe1 in
       let te2 = expr tenv pe2 in
       if te1.expr_typ <> Tint || te2.expr_typ <> Tint
       then
         errorm
           ~loc:pexpr_loc
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
           ~loc:pexpr_loc
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
           ~loc:pexpr_loc
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
           ~loc:pexpr_loc
           "wrong type for unary operation '%s': expected 'bool', found '%a'"
           (Pretty.unop unop)
           Pretty.typ
           te.expr_typ;
       { expr_desc = TEunop (unop, te); expr_typ = Tbool }
     | Uamp ->
       let te = expr_left_value tenv pe in
       { expr_desc = TEunop (unop, te); expr_typ = Tptr te.expr_typ }
     | Ustar -> expr_left_value tenv { pexpr_desc; pexpr_loc })
  | PEnil -> { expr_desc = TEnil; expr_typ = Tnil }
  | PEcall (id, pel) ->
    (match Hashtbl.find_opt tenv.functions id.id with
     | None when id.id = "fmt.Print" ->
       if not tenv.import_fmt
       then errorm ~loc:id.loc "import of module 'fmt' is required to use 'fmt.Print'";
       tenv.fmt_used <- true;
       { expr_desc = TEprint (pel |> List.map (expr tenv)); expr_typ = Tmany [] }
     | None -> errorm ~loc:pexpr_loc "function '%s' not found" id.id
     | Some f ->
       (try
          List.iter2
            (fun pe param ->
               let te = expr tenv pe in
               let typ = param.v_typ in
               if te.expr_typ <> typ
               then
                 errorm ~loc:pexpr_loc "in function '%s': invalid argument type" f.fn_name)
            pel
            f.fn_params
        with
        | Invalid_argument _ ->
          errorm ~loc:pexpr_loc "invalid argument count for function call '%s'" f.fn_name);
       (* TODO cas spécial pour f(g()), par exemple pour gérer
            def f(x, y): print(x, y)
            def g(): 1, 2

             f(g()) === f((1, 2), _)
            on veut === f(1, 2)
        *)
       { expr_desc = TEcall (f, pel |> List.map (expr tenv)); expr_typ = f.fn_typ })
  | PEident id -> failwith "peident wip"
  | PEdot (pe, id) ->
    let te = expr tenv pe in
    (match te.expr_typ with
     | Tstruct s ->
       (match Hashtbl.find_opt s.s_fields id.id with
        | None ->
          errorm
            ~loc:pexpr_loc
            "structure '%a' has no field named '%s'"
            Pretty.expr
            te
            id.id
        | Some field -> { expr_desc = TEdot (te, field); expr_typ = field.f_typ })
     | Tptr (Tstruct s) ->
       (* TODO : comment on check si e!= nil ?? *)
       (match Hashtbl.find_opt s.s_fields id.id with
        | None ->
          errorm
            ~loc:pexpr_loc
            "structure '%a' has no field named '%s'"
            Pretty.expr
            te
            id.id
        | Some field -> { expr_desc = TEdot (te, field); expr_typ = field.f_typ })
     | _ -> errorm ~loc:pexpr_loc "accessing a field of a non-struct type")
  (**** statements ****)
  | PEassign (left_pexpr, right_pexpr) ->
    let left_expr = left_pexpr |> List.map (expr_left_value tenv)
    and right_expr_and_types : (expr * typ) list =
      match right_pexpr with
      | [ ({ pexpr_desc = PEcall (id, arg); _ } as pecall) ] ->
        let f = expr tenv pecall in
        (match f.expr_typ with
         | Tmany l -> l |> List.map (fun x -> f, x)
         | t -> [ f, t ])
      | _ ->
        right_pexpr
        |> List.map (fun pe ->
          let te = expr tenv pe in
          te, te.expr_typ)
    in
    (try
       List.iter2
         (fun { expr_typ = t1; _ } (_, t2) ->
            if t1 <> t2
            then
              errorm
                ~loc:pexpr_loc
                "cannot assign value of type '%a' to variable of type '%a'"
                Pretty.typ
                t2
                Pretty.typ
                t1)
         left_expr
         right_expr_and_types
     with
     | Invalid_argument _ ->
       errorm ~loc:pexpr_loc "to few or to many values to assign to variables");
    { expr_desc = TEassign (left_expr, right_expr_and_types |> List.map fst)
    ; expr_typ = typ_of_typ_list (right_expr_and_types |> List.map snd)
    }
  | PEvars (ident_list, ptyp, pexpr_list) ->
    let var_types : typ list =
      match ptyp with
      | None -> failwith "pevars wip"
      | Some ptyp ->
        if not (is_type_well_formed tenv ptyp)
        then errorm ~loc:pexpr_loc "unbound type for this variable(s)";
        (* extract the specified type *)
        let tau = typ_of_ptyp tenv ptyp in
        (match pexpr_list with
         (* no initialization values specified => set reference type for each variable *)
         | [] -> List.init (List.length ident_list) (fun _ -> tau)
         (* variables initialized with a function call *)
         | [ ({ pexpr_desc = PEcall (id, arg); pexpr_loc = _ } as pe) ] ->
           (* check that function f exists and only returns values of reference type *)
           let f = expr tenv pe in
           let returned_types =
             match f.expr_typ with
             | Tmany l -> l
             | t -> [ t ]
           in
           returned_types
           |> List.iter (fun typ ->
             if typ <> tau
             then
               errorm
                 ~loc:pexpr_loc
                 "cannot declare a variable of type '%a' with a value of type '%a'"
                 Pretty.typ
                 tau
                 Pretty.typ
                 typ);
           returned_types
         (* variables initialized with a list of expressions *)
         | pel ->
           let returned_types =
             pel
             |> List.map (fun pe ->
               let te = expr tenv pe in
               te.expr_typ)
           in
           returned_types
           |> List.iter (fun typ ->
             if typ <> tau
             then
               errorm
                 ~loc:pexpr_loc
                 "cannot declare a variable of type '%a' with a value of type '%a'"
                 Pretty.typ
                 tau
                 Pretty.typ
                 typ);
           returned_types)
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
          ~loc:pexpr_loc
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
     | t -> errorm ~loc:pexpr_loc "conditional expression must be of boolean type")
  | PEreturn pel ->
    let tel = pel |> List.map (fun pe -> expr tenv pe) in
    { expr_desc = TEreturn tel
    ; expr_typ = typ_of_typ_list (tel |> List.map (fun e -> e.expr_typ))
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
        (* if the current statement contains variables declarations, update the list of block variables *)
        let block_var_names =
          match s.pexpr_desc with
          | PEvars (ident_decls, _, _) ->
            let new_var_names =
              ident_decls
              |> List.map (fun { id; loc } ->
                if List.mem id block_var_names
                then errorm ~loc "cannot redeclare a variable named '%s' in same block" id
                else id)
            in
            new_var_names @ block_var_names
          | _ -> block_var_names
        in
        let te = expr tenv s in
        aux tenv q block_var_names (te :: acc)
    in
    { expr_desc = TEblock (List.rev (aux tenv pel [] [])); expr_typ = Tnil }
  | PEfor (pe, b) ->
    let te = expr tenv pe in
    (match te.expr_typ with
     | Tbool ->
       let tb = expr tenv b in
       { expr_desc = TEfor (te, tb); expr_typ = Tnil }
     | _ -> errorm ~loc:pexpr_loc "conditional expression must be of boolean type")
  | PEincdec (pe, incdec) ->
    let te = expr_left_value tenv pe in
    (match te.expr_typ with
     | Tint -> { expr_desc = TEincdec (te, incdec); expr_typ = Tint }
     | t ->
       errorm
         ~loc:pexpr_loc
         "wrong type for increase/decrease operation: expected 'int', found '%a'"
         Pretty.typ
         t)

and expr_left_value (tenv : TypeEnv.t) (pe : Ast.pexpr) : Tast.expr =
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
;;

(* 
The declarations in a file can appear in any order. In particular, functions and structures are mutually recursive. It is suggested to proceed in three steps:

- [x] We add all the structures (but not their fields) to the environment, checking the uniqueness of the structure names.
- [x]
  - [x] We add all the functions to the environment, checking the uniqueness of the function names. For a function declaration of the form
  func f (x1 : τ1, . . . , xn : τn) (τ′1, . . . , τ′m) {b} we check that the xi are pairwise distinct and that all types τi and τ′j are well-formed.
  - [x] We check and add all the structure fields to the environment. For a structure declaration of the form type S struct { x1 : τ1, . . . , xn : τn } we check that the xi are pairwise distinct and that all types τi are well-formed.
- [ ]
  - [x] For each function declaration func f (x1 : τ1, . . . , xn : τn) (τ′1, . . . , τ′m) {b} we construct a new environment Γ by adding all the variables xi : τi to the environment containing the structures and functions, and we type the block b in Γ, i.e., we check Γ ⊢ b. Additionally, we check that 
      - every return statement in b returns a list of m values of the expected types τ′1, . . . , τ′m
      - if m > 0, that any control-flow branch in b reaches a return statement;
      - that any local variable introduced in b, other than _, is further used.
  - [ ] We check that there is no “recursive” structure, that is, no structure S with a field (which contains a field, which contains a field, etc.) of type S, without passing through a pointer.
- [ ] Finally, we check that there exists a function main without parameters and without return type and that the file contains import "fmt" f and only if there is at least one `fmt.Print` instruction somewhere in the file
*)
