open Base
open Lang

(** Convert a memory read of a [path] to a combination of [Var] and [Select] *)
let rec read_from_path (p : path) : aexp =
  match p with
  | { var; indices } ->
    match List.rev indices with
    | [] -> Var var
    | [i] -> Select { arr = Var var; idx = i }
    | i::is -> Select { arr = read_from_path { var; indices = List.rev is }; idx = i }

(** Convert an assignment to a [path] to a variable assignment
    using [Select] and [Store]. *)
let write_to_path (lhs : path) (rhs : aexp) : stmt =
  match lhs with
  | { var; indices } ->
    match List.rev indices with
    | [] -> Assign { lhs = var; rhs }
    | [i] -> Assign { lhs = var; rhs = Store { arr = Var var; idx = i; value = rhs } }
    | i::is -> Assign { lhs = var; rhs = Store { arr = read_from_path { var; indices = List.rev is }; idx = i; value = rhs } }
