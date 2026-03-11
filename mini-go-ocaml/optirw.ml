(* 
  Optimization stage, performed on the Typed AST
  This module uses e-graphs provided by the Ego library to perform boolean and integer expressions simplification and constant folding.
  Some code of this module was taken from the tutorial in the documentation page of the Ego library, available at https://ocaml.org/p/ego/0.0.6/doc/index.html.
 *)

open Ego.Generic

(* We need to add a couple of utility functions to the AST and Typed AST modules, so we redefine them to extend them  *)
module Ast = struct
  include Ast

  let equal_constant = Stdlib.( = )
  let equal_unop = Stdlib.( = )
  let equal_binop = Stdlib.( = )
  let compare_constant = Stdlib.compare
  let compare_unop = Stdlib.compare
  let compare_binop = Stdlib.compare

  let pp_constant fmt = function
    | Cbool b -> Format.pp_print_bool fmt b
    | Cint i -> Format.pp_print_string fmt (Int64.to_string i)
    | Cstring s -> Format.pp_print_string fmt s
  ;;

  let pp_unop fmt o = Format.fprintf fmt "%s" (Pretty.unop o)
  let pp_binop fmt o = Format.fprintf fmt "%s" (Pretty.binop o)
end

module Tast = struct
  include Tast

  let equal_var = Stdlib.( = )
  let equal_expr = Stdlib.( = )
  let compare_var = Stdlib.compare
  let compare_expr = Stdlib.compare
  let pp_var = Pretty.var
  let pp_expr = Pretty.expr

  let typ_of_constant (c : Ast.constant) : typ =
    match c with
    | Ast.Cbool _ -> Tbool
    | Ast.Cint _ -> Tint
    | Ast.Cstring _ -> Tstring
  ;;
end

(* The language of expressions to be optimized. It is composed of atomic operations (that cannot be optimized) of arity 0, and operators of arity greater than 0 (e.g. unary or binary operations) *)
module L = struct
  type 'a shape =
    (* for atomic operators, keep the value in the variant *)
    | LEconstant of Ast.constant
    | LEident of Tast.var
    | LEother of Tast.expr
    (* arity greater than 0 *)
    | LEunop of Ast.unop * 'a
    | LEbinop of Ast.binop * 'a * 'a
  [@@deriving ord, show]

  type t = Mk of t shape [@@unboxed]

  let rec pp_t (fmt : Format.formatter) (t : t) : unit =
    match t with
    | Mk t -> Format.fprintf fmt "%a" (pp_shape pp_t) t
  ;;

  (* convert a Typed AST expression into a language expression *)
  let rec of_expr (e : Tast.expr) : t =
    Mk
      (match e.expr_desc with
       | TEconstant c -> LEconstant c
       | TEident v -> LEident v
       | TEunop (((Ast.Unot | Ast.Uneg) as u), e) -> LEunop (u, of_expr e)
       | TEbinop
           ( ((Ast.Badd | Ast.Bsub | Ast.Bmul | Ast.Bdiv | Ast.Bmod | Ast.Band | Ast.Bor)
              as b)
           , e1
           , e2 ) -> LEbinop (b, of_expr e1, of_expr e2)
       | _ -> LEother e)
  ;;

  (* convert a language expression back to a Typed AST expression *)
  let rec to_expr (Mk t : t) : Tast.expr =
    match t with
    | LEconstant c -> { expr_desc = Tast.TEconstant c; expr_typ = Tast.typ_of_constant c }
    | LEident v -> { expr_desc = Tast.TEident v; expr_typ = v.v_typ }
    | LEunop ((Ast.Unot as u), e) ->
      { expr_desc = Tast.TEunop (u, to_expr e); expr_typ = Tast.Tbool }
    | LEunop ((Ast.Uneg as u), e) ->
      { expr_desc = Tast.TEunop (u, to_expr e); expr_typ = Tast.Tint }
    | LEbinop (((Ast.Band | Ast.Bor) as b), e1, e2) ->
      { expr_desc = Tast.TEbinop (b, to_expr e1, to_expr e2); expr_typ = Tast.Tbool }
    | LEbinop (((Ast.Badd | Ast.Bsub | Ast.Bmul | Ast.Bdiv | Ast.Bmod) as b), e1, e2) ->
      { expr_desc = Tast.TEbinop (b, to_expr e1, to_expr e2); expr_typ = Tast.Tint }
    | LEunop ((Ast.Uamp | Ast.Ustar), _)
    | LEbinop ((Ast.Beq | Ast.Bne | Ast.Blt | Ast.Ble | Ast.Bgt | Ast.Bge), _, _) ->
      failwith (Format.asprintf "unreachable (L.to_expr) %a" pp_t (Mk t))
    | LEother e -> e
  ;;

  (* | _ -> failwith (Format.asprintf "unreachable (L.of_expr) %a" pp_t (Mk t)) *)

  type op =
    | ConstOp of Ast.constant
    | IdentOp of Tast.var
    | OtherOp of Tast.expr
    | UnOp of Ast.unop
    | BinOp of Ast.binop
  [@@deriving eq]

  (* this function is used when defining rewriting rules, to map a symbol to the actual operator (or constant term) *)
  let op_of_string : Tast.typ -> string -> op =
    fun typ -> function
    (* booleans *)
    | "true" -> ConstOp (Ast.Cbool true)
    | "false" -> ConstOp (Ast.Cbool false)
    | "!" -> UnOp Ast.Unot
    | "&&" -> BinOp Ast.Band
    | "||" -> BinOp Ast.Bor
    (* integers *)
    | "--" -> UnOp Ast.Uneg
    | "+" -> BinOp Ast.Badd
    | "-" -> BinOp Ast.Bsub
    | "*" -> BinOp Ast.Bmul
    | "/" -> BinOp Ast.Bdiv
    | "%" -> BinOp Ast.Bdiv
    (* any other string is either an integer constant or a variable identifier *)
    | s ->
      (try ConstOp (Ast.Cint (Int64.of_string s)) with
       | Failure _ -> IdentOp (Typing.new_var s Typing.dummy_loc typ))
  ;;

  let op : 'a shape -> op = function
    | LEconstant c -> ConstOp c
    | LEident v -> IdentOp v
    | LEother e -> OtherOp e
    | LEunop (unop, _) -> UnOp unop
    | LEbinop (binop, _, _) -> BinOp binop
  ;;

  let make : op -> 'a list -> 'a shape =
    fun op ls ->
    match op, ls with
    | ConstOp c, [] -> LEconstant c
    | IdentOp v, [] -> LEident v
    | OtherOp e, [] -> LEother e
    | UnOp unop, [ s ] -> LEunop (unop, s)
    | BinOp binop, [ l; r ] -> LEbinop (binop, l, r)
    | _ -> failwith "unreachable (L.make)"
  ;;

  let children : 'a shape -> 'a list = function
    | LEconstant _ -> []
    | LEident _ -> []
    | LEother _ -> []
    | LEunop (_, e) -> [ e ]
    | LEbinop (_, e1, e2) -> [ e1; e2 ]
  ;;

  let map_children : 'a shape -> ('a -> 'b) -> 'b shape =
    fun term f ->
    match term with
    | LEconstant c -> LEconstant c
    | LEident v -> LEident v
    | LEother e -> LEother e
    | LEunop (u, e) -> LEunop (u, f e)
    | LEbinop (b, e1, e2) -> LEbinop (b, f e1, f e2)
  ;;
end

(* A type to extend Ego's analysis module type with some custom functions *)
module type Analysis = sig
  type d

  include ANALYSIS with type t = unit and type data = d option

  val t_of_d : d -> L.t
  val eval : data L.shape -> data
end

(* The two functors below are used to minimize the redundant code between boolean and integer rewriting *)

(* Make an analysis module (type-agnostic) *)
module MakeA (B : sig
    type d
    type data

    val equal_d : d -> d -> bool
    val equal_data : data -> data -> bool
    val pp_d : Format.formatter -> d -> unit
    val pp_data : Format.formatter -> data -> unit
    val t_of_d : d -> L.t
    val eval : d option L.shape -> d option
  end) : Analysis = struct
  type t = unit
  type d = B.d [@@deriving show, eq]
  type data = B.d option [@@deriving show, eq]

  let default = None
  let t_of_d = B.t_of_d
  let eval = B.eval
end

(* Make an analysis-maker module (type-agnostic) *)
module MakeMA
    (A : Analysis)
    (S :
       GRAPH_API
       with type 'p t = (Ego.Id.t L.shape, A.t, A.data, 'p) egraph
        and type analysis := A.t
        and type data := A.data
        and type 'a shape := 'a L.shape
        and type node := L.t) =
struct
  type 'p t = (Ego.Id.t L.shape, A.t, A.data, 'p) egraph

  let make : ro t -> Ego.Id.t L.shape -> A.data =
    fun graph term -> A.eval (L.map_children term (S.get_data graph))
  ;;

  let merge : A.t -> A.data -> A.data -> A.data * (bool * bool) =
    fun () l r ->
    let result =
      match l, r with
      | Some v, _ -> Some v
      | _, Some v -> Some v
      | None, None -> None
    in
    let changed_l = not (A.equal_data result l) in
    let changed_r = not (A.equal_data result r) in
    result, (changed_l, changed_r)
  ;;

  let modify : rw t -> Ego.Id.t -> unit =
    fun graph cls ->
    match S.get_data (S.freeze graph) cls with
    | None -> ()
    | Some n ->
      let nw_cls = S.add_node graph (A.t_of_d n) in
      S.merge graph nw_cls cls
  ;;
end

(* Cost of expressions *)
module C = struct
  type t = float [@@deriving ord]

  let cost f : Ego.Id.t L.shape -> t = function
    (* compute the cost of an operator based on its arity *)
    | LEconstant _ | LEident _ | LEother _ -> 1.0
    | LEunop (_, s) -> f s +. 1.0
    (* higher cost for mul and div as they are more CPU costly than others *)
    | LEbinop (Ast.Bmul, l, r) -> f l +. f r +. 1.5
    | LEbinop (Ast.Bdiv, l, r) -> f l +. f r +. 2.0
    | LEbinop (_, l, r) -> f l +. f r +. 1.0
  ;;
end

(* Common rewriting functions. It is meant to be used with the functions of the instantiated EGraph module *)
let rw init add_node run_until_saturation extract rules (expr : Tast.expr) : Tast.expr =
  (* create an e-graph *)
  let graph = init () in
  (* add the original expression (converted to the optimization language) *)
  let expr_id = add_node graph (L.of_expr expr) in
  (* generate all the possible rewrites *)
  if not (run_until_saturation graph rules)
  then Printf.eprintf "warning: run_until_saturation terminated early";
  (* extract the expression with the lowest cost *)
  expr_id |> extract graph |> L.to_expr
;;

(* Rewriting modules expose a single rewriting function, that converts an expression to its optimized version *)
module type Rw = sig
  val rw : Tast.expr -> Tast.expr
end

(* Rewriting of boolean arithmetic expressions *)
module RwBool : Rw = struct
  module A = MakeA (struct
      type d = bool [@@deriving show, eq]
      type data = d option [@@deriving show, eq]

      let t_of_d b = L.Mk (LEconstant (Ast.Cbool b))

      (* Boolean constant folding function *)
      let eval : d option L.shape -> d option = function
        | LEconstant (Ast.Cbool b) -> Some b
        | LEunop (Ast.Unot, Some b) -> Some (not b)
        | LEbinop (Ast.Band, Some l, Some r) -> Some (l && r)
        | LEbinop (Ast.Bor, Some l, Some r) -> Some (l || r)
        | _ -> None
      ;;
    end)

  module EGraph = Make (L) (A) (MakeMA (A))
  module Extractor = MakeExtractor (L) (C)

  (* Rewriting rules for boolean operators *)
  let rules =
    let op_of_string = L.op_of_string Tast.Tbool in
    let open Sexplib0.Sexp in
    [ (* !(!v) -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "!"; List [ Atom "!"; Atom "?v" ] ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v || true -> true *)
      ( Query.of_sexp op_of_string (List [ Atom "||"; Atom "?v"; Atom "true" ])
      , Query.of_sexp op_of_string (Atom "true") )
    ; (* v && true -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "&&"; Atom "?v"; Atom "true" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v || false -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "||"; Atom "?v"; Atom "false" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v && false -> false *)
      ( Query.of_sexp op_of_string (List [ Atom "&&"; Atom "?v"; Atom "false" ])
      , Query.of_sexp op_of_string (Atom "false") )
    ; (* !a && !b -> !(a || b) *)
      ( Query.of_sexp
          op_of_string
          (List [ Atom "&&"; List [ Atom "!"; Atom "?a" ]; List [ Atom "!"; Atom "?b" ] ])
      , Query.of_sexp
          op_of_string
          (List [ Atom "!"; List [ Atom "||"; Atom "?a"; Atom "?b" ] ]) )
    ; (* !a || !b -> !(a && b) *)
      ( Query.of_sexp
          op_of_string
          (List [ Atom "||"; List [ Atom "!"; Atom "?a" ]; List [ Atom "!"; Atom "?b" ] ])
      , Query.of_sexp
          op_of_string
          (List [ Atom "!"; List [ Atom "&&"; Atom "?a"; Atom "?b" ] ]) )
    ]
    |> List.map (fun (from, into) -> EGraph.Rule.make_constant ~from ~into)
  ;;

  let rw =
    rw EGraph.init EGraph.add_node EGraph.run_until_saturation Extractor.extract rules
  ;;
end

(* Rewriting of integer arithmetic expressions *)
module RwInt : Rw = struct
  module A = MakeA (struct
      type d = int64 [@@deriving show, eq]
      type data = d option [@@deriving show, eq]

      let t_of_d i = L.Mk (LEconstant (Ast.Cint i))

      (* Integer constant folding function *)
      let eval : d option L.shape -> d option = function
        | LEconstant (Ast.Cint i) -> Some i
        | LEunop (Ast.Uneg, Some i) -> Some (Int64.neg i)
        | LEbinop (Ast.Badd, Some l, Some r) -> Some (Int64.add l r)
        | LEbinop (Ast.Bsub, Some l, Some r) -> Some (Int64.sub l r)
        | LEbinop (Ast.Bmul, Some l, Some r) -> Some (Int64.mul l r)
        | LEbinop (Ast.Bdiv, Some l, Some r) ->
          if r <> 0L then Some (Int64.div l r) else raise Division_by_zero
        | LEbinop (Ast.Bmod, Some l, Some r) ->
          if r <> 0L then Some (Int64.rem l r) else raise Division_by_zero
        | _ -> None
      ;;
    end)

  module EGraph = Make (L) (A) (MakeMA (A))
  module Extractor = MakeExtractor (L) (C)

  (* Rewriting rules for integer operators *)
  let rules =
    let op_of_string = L.op_of_string Tast.Tint in
    let open Sexplib0.Sexp in
    [ (* -(-v) -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "--"; List [ Atom "--"; Atom "?v" ] ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v + 0 -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "+"; Atom "?v"; Atom "0" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v - 0 -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "-"; Atom "?v"; Atom "0" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v * 1 -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "*"; Atom "?v"; Atom "1" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v / 1 -> v *)
      ( Query.of_sexp op_of_string (List [ Atom "/"; Atom "?v"; Atom "1" ])
      , Query.of_sexp op_of_string (Atom "?v") )
    ; (* v * 0 -> 0 *)
      ( Query.of_sexp op_of_string (List [ Atom "*"; Atom "?v"; Atom "0" ])
      , Query.of_sexp op_of_string (Atom "0") )
    ; (* a + b -> b + a *)
      ( Query.of_sexp op_of_string (List [ Atom "+"; Atom "?a"; Atom "?b" ])
      , Query.of_sexp op_of_string (List [ Atom "+"; Atom "?b"; Atom "?a" ]) )
    ; (* (a + b) + c -> a + (b + c) *)
      ( Query.of_sexp
          op_of_string
          (List [ Atom "+"; List [ Atom "+"; Atom "?a"; Atom "?b" ]; Atom "?c" ])
      , Query.of_sexp
          op_of_string
          (List [ Atom "+"; Atom "?a"; List [ Atom "+"; Atom "?b"; Atom "?c" ] ]) )
    ; (* (k * a + k * b) -> k * (a + b) *)
      ( Query.of_sexp
          op_of_string
          (List
             [ Atom "+"
             ; List [ Atom "*"; Atom "?k"; Atom "?a" ]
             ; List [ Atom "*"; Atom "?k"; Atom "?b" ]
             ])
      , Query.of_sexp
          op_of_string
          (List [ Atom "*"; Atom "?k"; List [ Atom "+"; Atom "?a"; Atom "?b" ] ]) )
    ; (* k * (a + b) -> (k * a + k * b) *)
      ( Query.of_sexp
          op_of_string
          (List [ Atom "*"; Atom "?k"; List [ Atom "+"; Atom "?a"; Atom "?b" ] ])
      , Query.of_sexp
          op_of_string
          (List
             [ Atom "+"
             ; List [ Atom "*"; Atom "?k"; Atom "?a" ]
             ; List [ Atom "*"; Atom "?k"; Atom "?b" ]
             ]) )
    ]
    |> List.map (fun (from, into) -> EGraph.Rule.make_constant ~from ~into)
  ;;

  let rw =
    rw EGraph.init EGraph.add_node EGraph.run_until_saturation Extractor.extract rules
  ;;
end

(* rewrite an expression into an optimized one *)
let rec expr (e : Tast.expr) : Tast.expr =
  match e.expr_desc with
  | TEunop (Ast.Unot, _) -> RwBool.rw e
  | TEunop (Ast.Uneg, _) -> RwInt.rw e
  | TEunop _ -> e
  | TEbinop ((Ast.Band | Ast.Bor), _, _) -> RwBool.rw e
  | TEbinop ((Ast.Badd | Ast.Bsub | Ast.Bmul | Ast.Bdiv | Ast.Bmod), _, _) -> RwInt.rw e
  | TEbinop _ -> e
  (* for other expressions / statements, we just need to recursively rewrite the sub-expressions *)
  | TEcall (f, l) -> { e with expr_desc = TEcall (f, l |> List.map expr) }
  | TEassign (v, l) -> { e with expr_desc = TEassign (v, l |> List.map expr) }
  | TEif (c, e1, e2) -> { e with expr_desc = TEif (expr c, expr e1, expr e2) }
  | TEreturn l -> { e with expr_desc = TEreturn (l |> List.map expr) }
  | TEblock l -> { e with expr_desc = TEblock (l |> List.map expr) }
  | TEfor (c, e) -> { e with expr_desc = TEfor (expr c, expr e) }
  | TEprint l -> { e with expr_desc = TEprint (l |> List.map expr) }
  (* these expressions / statements cannot be optimized => do nothing *)
  | TEnil | TEdot _ | TEskip | TEconstant _ | TEnew _ | TEident _ | TEvars _ | TEincdec _
    -> e
;;

(* rewrite a file by applying optimizations *)
let file (file : Tast.tfile) : Tast.tfile =
  file
  |> List.map (function
    (* do nothing on structures *)
    | Tast.TDstruct _ as s -> s
    (* rewrite the functions bodies *)
    | Tast.TDfunction (f, body) -> Tast.TDfunction (f, expr body))
;;
