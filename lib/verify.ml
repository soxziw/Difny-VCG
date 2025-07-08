open Base

(** Substitutions *)
module Subst = struct
  open Lang

  (** [aexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec aexp (x : string) (e : aexp) (c : aexp) : aexp =
    match c with
    | Int i -> Int i
    | Aop (aop, aa, ab) -> Aop (aop, aexp x e aa, aexp x e ab)
    | Var s -> if String.equal x s then e else Var s
    | Select { arr; idx } -> Select { arr = (aexp x e arr); idx = (aexp x e idx)}
    | Store { arr; idx; value } -> Store { arr = (aexp x e arr); idx = (aexp x e idx); value = (aexp x e value)}

  (** [bexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec bexp (x : string) (e : aexp) (c : bexp) : bexp =
    match c with
    | Bool b -> Bool b
    | Comp (comp, aa, ab) -> Comp (comp, aexp x e aa, aexp x e ab)
    | Not (ba) -> Not (bexp x e ba)
    | And (ba, bb) -> And (bexp x e ba, bexp x e bb)
    | Or (ba, bb) -> Or (bexp x e ba, bexp x e bb)

  (** [formula x e f] substitutes all occurrences of [x] in [f] with [e] *)
  let rec formula (x : string) (e : aexp) (f : formula) : formula =
    match f with
    | FBool b -> FBool b
    | FComp (comp, aa, ab) -> FComp (comp, aexp x e aa, aexp x e ab)
    | FQ (q, s, fa) -> if String.equal x s then FQ (q, s, fa) else FQ (q, s, formula x e fa)
    | FNot (fa) -> FNot (formula x e fa)
    | FConn (conn, fa, fb) -> FConn (conn, formula x e fa, formula x e fb)
end

module MulSubst = struct
  open Lang

  (** [aexp m c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec aexp (m : (string * aexp) list) (c : aexp) : aexp =
    match c with
    | Int i -> Int i
    | Aop (aop, aa, ab) -> Aop (aop, aexp m aa, aexp m ab)
    | Var s -> (
      match List.find_map ~f:(fun (x, e) -> if String.equal x s then Some e else None) m with
      | Some e -> e
      | None -> Var s)
    | Select { arr; idx } -> Select { arr = (aexp m arr); idx = (aexp m idx)}
    | Store { arr; idx; value } -> Store { arr = (aexp m arr); idx = (aexp m idx); value = (aexp m value)}

  (** [bexp m c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec bexp (m : (string * aexp) list) (c : bexp) : bexp =
    match c with
    | Bool b -> Bool b
    | Comp (comp, aa, ab) -> Comp (comp, aexp m aa, aexp m ab)
    | Not (ba) -> Not (bexp m ba)
    | And (ba, bb) -> And (bexp m ba, bexp m bb)
    | Or (ba, bb) -> Or (bexp m ba, bexp m bb)

  (** [formula m f] substitutes all occurrences of [x] in [f] with [e] *)
  let rec formula (m : (string * aexp) list) (f : formula) : formula =
    match f with
    | FBool b -> FBool b
    | FComp (comp, aa, ab) -> FComp (comp, aexp m aa, aexp m ab)
    | FQ (q, s, fa) -> (
      let remain_map = List.filter ~f:(fun (x, _) -> not (String.equal x s)) m in
      FQ (q, s, formula remain_map fa))
    | FNot (fa) -> FNot (formula m fa)
    | FConn (conn, fa, fb) -> FConn (conn, formula m fa, formula m fb)
end

(** Lift a [bexp] into a [formula] *)
let rec bexp_to_formula (b : Lang.bexp) : Lang.formula =
  match b with
    | Bool b -> FBool b
    | Comp (comp, aa, ab) -> FComp (comp, aa, ab)
    | Not (ba) -> FNot (bexp_to_formula ba)
    | And (ba, bb) -> FConn (And, bexp_to_formula ba, bexp_to_formula bb)
    | Or (ba, bb) -> FConn (Or, bexp_to_formula ba, bexp_to_formula bb)

(** Make a verifier for a method in a difny program *)
module Make (S : sig
  val prog : Lang.prog
  (** ambient program *)

  val meth : Lang.meth
  (** method to verify *)
end) =
struct
  open Lang

  (** [INTERNAL] Mutable reference (i.e. pointer) to the current gamma *)
  let gamma_ref = ref (S.meth.locals @ S.meth.params)

  (** [INTERNAL] Retrieve the current gamma *)
  let gamma () = !gamma_ref

  (** Update gamma to map a new variable with its type *)
  let add_gamma (x : string) (t : ty) : unit = gamma_ref := (x, t) :: !gamma_ref

  (** [INTERNAL] Counter to generate fresh variables *)
  let counter = ref 0

  (** Generate a fresh variable using the hint, and record its type in gamma *)
  let fresh_var (t : ty) ~(hint : string) =
    let i = !counter in
    counter := !counter + 1;
    let x = Fmt.str "$%s_%d" hint i in
    add_gamma x t;
    x

  (** Compute the list of modified variables in a statement *)
  let rec modified (s : stmt) : string list =
    match s with
    | Assign { lhs; rhs = _ } -> [ lhs ]
    | If { cond = _; els; thn } -> (modified_block thn) @ (modified_block els)
    | While { cond = _; inv = _; body } -> modified_block body
    | Call { lhs; callee = _; args = _ } -> [ lhs ]
    | Havoc x -> [x]
    | Assume _ -> []
    | Assert _ -> []
    | Print _ -> []

  (** Compute the list of unique modified variables in a sequence of statements *)
  and modified_block (stmts : block) : string list =
    (* for each stmt, compute the list of modified variabls ("map"),
       and then concatenate all lists together ("concat") *)
    let xs = List.concat_map ~f:modified stmts in
    (* deduplicate and sort the list *)
    List.dedup_and_sort ~compare:String.compare xs

  (** Compile a statement into a sequence of guarded commands *)
  let rec compile (c : stmt) : gcom list =
    match c with
    | Assign { lhs; rhs } -> (
      let lhs_ty = Utils.ty_exn (gamma ()) ~of_:lhs in
      let tmp = fresh_var lhs_ty ~hint:lhs in
      [Assume (FComp (Eq, Var tmp, Var lhs));
      Havoc lhs;
      Assume (FComp(Eq, Var lhs, (Subst.aexp lhs (Var tmp) rhs)))])
    | If { cond; els; thn } -> (
      let thn_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] thn in
      let els_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] els in
      [Choose(
        Seq(Assume (bexp_to_formula cond)::thn_list),
        Seq(Assume (FNot (bexp_to_formula cond))::els_list)
      )])
    | While { cond; inv; body } -> (
      let body_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] body in
      let inv_assert_list = List.fold_left ~f:(fun acc s -> (Assert s)::acc) ~init:[] inv in
      let inv_assume_list = List.fold_left ~f:(fun acc s -> (Assume s)::acc) ~init:[] inv in
      let havoc_variables = List.fold_left ~f:(fun acc s -> (Havoc s)::acc) ~init:[] (modified_block body) in
      let continue = Seq ((Assume (bexp_to_formula cond)::body_list) @ inv_assert_list @ [Assume (FBool false)]) in
      let break = Seq [Assume (FNot (bexp_to_formula cond))] in
      inv_assert_list @ havoc_variables @ inv_assume_list @ [Choose (continue, break)])
    | Call { lhs; callee; args } -> (
      let callee_meth = 
        match List.find ~f:(fun m -> String.equal m.id callee) S.prog with
        | Some m -> m
        | None -> failwith (Fmt.str "Method %s not found" callee)
      in
      let param_vars = List.map2_exn ~f:(fun (x, _) arg -> (x, arg)) callee_meth.params args in
      let (ret_name, ret_ty) = callee_meth.returns in
      let ret_var = fresh_var ret_ty ~hint:ret_name in
      let pre_conds = List.map callee_meth.requires ~f:(fun f -> MulSubst.formula param_vars f) in
      let post_conds = List.map callee_meth.ensures ~f:(fun f -> Subst.formula ret_name (Var ret_var) (MulSubst.formula param_vars f)) in
      let pre_asserts = List.map pre_conds ~f:(fun pre -> Assert pre) in
      let post_assumes = List.map post_conds ~f:(fun post -> Assume post) in
      
      pre_asserts @ post_assumes @ (compile (Assign { lhs = lhs; rhs = Var ret_var }))
    )
    | Havoc x -> [ Havoc x ]
    | Assume f -> [ Assume f ]
    | Assert f -> [ Assert f ]
    | Print _ -> []

  (** For each statement in a block, compile it into a list of guarded 
      commands ("map"), and then concatenate the result ("concat") *)
  and compile_block : block -> gcom list = List.concat_map ~f:compile

  (** Compute weakest-pre given a guarded command and a post formula *)
  let rec wp (g : gcom) (f : formula) : formula =
    match g with
    | Assume f' -> FConn (Imply, f', f)
    | Assert f' -> FConn (And, f', f)
    | Havoc x -> (
      let x_ty = Utils.ty_exn (gamma ()) ~of_:x in
      let tmp = fresh_var x_ty ~hint:x in
      Subst.formula x (Var tmp) f)
    | Seq cs -> (
      match cs with
      | [] -> f
      | x::xs -> wp x (wp_seq xs f))
    | Choose (c1, c2) -> FConn (And, wp c1 f, wp c2 f)

  (** Propagate the post-condition backwards through a sequence of guarded
      commands using [wp] *)
  and wp_seq (gs : gcom list) (phi : formula) : formula =
    List.fold_right ~init:phi ~f:wp gs

  (** Verify the method passed in to this module *)
  let result : unit =
    (* print method id and content *)
    Logs.debug (fun m -> m "Verifying method %s:" S.meth.id);
    Logs.debug (fun m -> m "%a" Pretty.meth S.meth);

    (* compile method to guarded commands *)
    let pre_conds = List.map ~f:(fun s -> Assume s) S.meth.requires in
    let body_gs = compile_block (S.meth.body) in
    let (ret_name, _) = S.meth.returns in
    let post_conds = List.map ~f:(fun s -> Assert (Subst.formula ret_name S.meth.ret s)) S.meth.ensures in
    let gs = pre_conds @ body_gs @ post_conds in
    Logs.debug (fun m -> m "Guarded commands:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) gs);

    (* compute verification condition (VC) using weakest-precondition *)
    let vc = wp_seq gs (FBool true) in
    Logs.debug (fun m -> m "Verification condition:");
    Logs.debug (fun m -> m "%a" Pretty.formula vc);

    (* check if the VC is valid under the current gamma *)
    let status = Smt.check_validity (gamma ()) vc in
    match status with
    | Smt.Valid -> Logs.app (fun m -> m "%s: verified" S.meth.id)
    | Smt.Invalid cex ->
        Logs.app (fun m -> m "%s: not verified" S.meth.id);
        Logs.app (fun m -> m "Counterexample:");
        Logs.app (fun m -> m "%s" cex)
    | Smt.Unknown -> Logs.app (fun m -> m "%s: unknown" S.meth.id)
  (* this function doesn't return anything, so it implicitly
     returns the unit value "()" *)
end

(** Public function for verifying a difny method *)
let go (prog : Lang.prog) (meth : Lang.meth) : unit =
  (* construct a verifier module (verification happens during module construction) *)
  let module Verifier = Make (struct
    let prog = prog
    let meth = meth
  end) in
  (* retrieve the result, which is just a unit value *)
  Verifier.result
