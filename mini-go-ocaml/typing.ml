(** Static type checking of Mini Go programs (TODO) *)

open Format
open Lib
open Ast
open Tast

(* Sub-environment hashtables of each type *)
type env =
  { functions : (string, function_) Hashtbl.t
  ; structures : (string, structure) Hashtbl.t
  }

let create_env () : env = { functions = Hashtbl.create 8; structures = Hashtbl.create 8 }
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

let rec is_type_well_formed (env : env) : ptyp -> bool = function
  | PTident { id; loc } ->
    (match id with
     | "bool" | "int" | "string" -> true
     | id -> Hashtbl.mem env.structures id)
  | PTptr t -> is_type_well_formed env t
;;

let is_list_pairwise_unique (l : string list) : bool =
  let rec check (acc : string list) (l : string list) : bool =
    match l with
    | [] -> true
    | t :: q -> if List.mem t acc then false else check (t :: acc) q
  in
  check [] l
;;

let are_idents_and_types_ok
      (env : env)
      (loc : location)
      (ids : ident list)
      (types : ptyp list)
  : bool
  =
  if is_list_pairwise_unique (ids |> List.map (fun { id; _ } -> id))
  then
    if types |> List.for_all (is_type_well_formed env)
    then true
    else errorm ~loc "invalid identifier type list"
  else errorm ~loc "duplicate name in identifier list"
;;

let rec typ_of_ptyp (env : env) (ptyp : ptyp) : typ =
  match ptyp with
  | PTident ident ->
    (match ident with
     | { id = "bool"; _ } -> Tbool
     | { id = "string"; _ } -> Tstring
     | { id = "int"; _ } -> Tint
     | { id; loc } ->
       (match Hashtbl.find_opt env.structures id with
        | Some s -> Tstruct s
        | None -> errorm ~loc "unable to find struct name '%s'" id))
  | PTptr t -> Tptr (typ_of_ptyp env t)
;;

let file ~debug:b ((imp, dl) : Ast.pfile) : Tast.tfile =
  debug := b;
  let tenv = create_env () in
  (* 1 - We add all the structures (but not their fields) to the environment, checking the uniqueness of the structure names *)
  dl
  |> List.iter (function
    | PDstruct { ps_name = { id; loc }; _ } ->
      if Hashtbl.mem tenv.structures id
      then errorm ~loc "structure name '%s' is already used" id
      else
        Hashtbl.add
          tenv.structures
          id
          { s_name = id; s_fields = Hashtbl.create 8; s_list = []; s_size = 0 }
    | _ -> ());
  (* 2 - We add all the functions/structures to the environment with checking on xi *)
  dl
  |> List.iter (function
    (* 2.a - checking the uniqueness of the function names, of theirs parameters and if types are well-formed *)
    | PDfunction { pf_name; pf_params; _ } ->
      if Hashtbl.mem tenv.functions pf_name.id
      then errorm ~loc:pf_name.loc "function name '%s' is already used" pf_name.id
      else if
        not
          (are_idents_and_types_ok
             tenv
             pf_name.loc
             (pf_params |> List.map fst)
             (pf_params |> List.map snd))
      then errorm ~loc:pf_name.loc "in function '%s'" pf_name.id
      else
        Hashtbl.add
          tenv.functions
          pf_name.id
          { fn_name = pf_name.id; fn_params = []; fn_typ = [] }
    (* 2.b - checking the uniqueness of the fields of a structure and if types are well-formed *)
    | PDstruct { ps_name; ps_fields } ->
      if
        not
          (are_idents_and_types_ok
             tenv
             ps_name.loc
             (ps_fields |> List.map fst)
             (ps_fields |> List.map snd))
      then errorm ~loc:ps_name.loc "in structure '%s'" ps_name.id
      else (
        let s = Hashtbl.find tenv.structures ps_name.id in
        ps_fields
        |> List.iter (fun ({ id; _ }, ptyp) ->
          let field = { f_name = id; f_typ = typ_of_ptyp tenv ptyp; f_ofs = 0 } in
          Hashtbl.add s.s_fields id field;
          s.s_list <- field :: s.s_list)));
  failwith "wip"
;;

(* 
The declarations in a file can appear in any order. In particular, functions and structures are mutually recursive. It is suggested to proceed in three steps:

- [x] We add all the structures (but not their fields) to the environment, checking the uniqueness of the structure names.
- [x]
  - [x] We add all the functions to the environment, checking the uniqueness of the function names. For a function declaration of the form
  func f (x1 : τ1, . . . , xn : τn) (τ′1, . . . , τ′m) {b} we check that the xi are pairwise distinct and that all types τi and τ′j are well-formed.
  - [x] We check and add all the structure fields to the environment. For a structure declaration of the form type S struct { x1 : τ1, . . . , xn : τn } we check that the xi are pairwise distinct and that all types τi are well-formed.
- [ ]
  - [ ] For each function declaration func f (x1 : τ1, . . . , xn : τn) (τ′1, . . . , τ′m) {b} we construct a new environment Γ by adding all the variables xi : τi to the environment containing the structures and functions, and we type the block b in Γ, i.e., we check Γ ⊢ b. Additionally, we check that 
      - every return statement in b returns a list of m values of the expected types τ′1, . . . , τ′m
      - if m > 0, that any control-flow branch in b reaches a return statement;
      - that any local variable introduced in b, other than _, is further used.
  - [ ] We check that there is no “recursive” structure, that is, no structure S with a field (which contains a field, which contains a field, etc.) of type S, without passing through a pointer.
- [ ] Finally, we check that there exists a function main without parameters and without return type and that the file contains import "fmt" f and only if there is at least one `fmt.Print` instruction somewhere in the file
*)
