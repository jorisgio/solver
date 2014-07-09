open Vector 

module type Variable = sig
  type t
  val empty : t
  val compare : t -> t -> int
end



module Make (Var : Variable) = struct 

  type value = Undef | True | False

  exception Undefined_value

  (**
	 State of a variable of the SAT problem
  *)
  type variable = {
	vs_id : Var.t;
	mutable vs_value : value; 
	vs_watch_true : watch VSet.t;
	(** Watched clauses when the variable is assigned [True] *)
	vs_watch_false : watch VSet.t;
	(** Watched clauses when the variable is assigned [False] *) 
	mutable vs_decision_level : int;
	(** The depth in the decision tree at which the variable has been assigned a value.
		[-1] when the variable is unassigned *)
	mutable vs_antecedant : clause option;
	(** The unit clause used for implying the variable value.
		When a variable is unassigned of is a decision variable, the antecedant is {i nil},
		*)
  }

  (** A literal is either a variable or the negation of a variable *)
  and literal = 
	| Pos of variable
	| Neg of variable

  (**
	 A clause is a list of literals.
	 The solver design allow for a literal to appear more than once, this is not a set.
	 This is useful for cost clauses
  *)
  and clause = {
	mutable cl_watch_end : int;
	(** Every watched literals are store in indexes stricly inferior to this value *)
	cl_literals : literal array;
  }

  (** Reference to a literal in a clause, using the index in the literals array *)
  and watch = clause * int


  (** The null variable, used to compare by reference. Dirty option type *)
  let null_var = {
	vs_id = Var.empty;
	vs_value = Undef;
	vs_watch_true = VSet.create () ;
	vs_watch_false = VSet.create () ;
	vs_decision_level = -1;
	vs_antecedant = None;
  }

  (** The null lit *)
  let null_lit = Pos null_var

  let empty_clause size const = {
	cl_watch_end = const;
	cl_literals = Array.make size null_lit;
  }

  type problem_state = 
	| SAT
	| UNSAT
	| Unresolved


  (**
	 Current state of the search tree and description of the sat problem
	 *)
  type pbo_state = {
	mutable pbo_propagation_stack : int;
	(**
	   List of the implied literals by the current decision tree
	   This list must be empty before making a new decision assignment.
	   *)
	mutable pbo_conflicts : int;
	(**
	   List of conflicting clauses.
	   This list must be empty before making a new decision assignment.
	   *)
	mutable pbo_learnt_clauses : clause list;
	pbo_clauses : clause list;
	(** Set of the clauses of the SAT problem *)
	mutable pbo_cost : clause list;
	(** Cost clauses to be minimized *)
	mutable pbo_cost_solved : clause list;
	mutable pbo_last_state : problem_state;
	mutable pbo_decision_level : int;
	(** Current depth in the decision tree *)
	pbo_trail : literal Vector.t;
	(** Stack of assignments *)
	pbo_trail_level : int Vector.t;
	(** Index in the trail of each d-level *)

 	(** branching heuristic *)
 	pbo_activity : variable Iheap.t;

  }

  let not_value = function
	| True -> False
	| False -> True
	| Undef -> Undef 

  let not_literal = function
	| Neg var -> Pos var
	| Pos var -> Neg var

  let eval_literal = function
	| Neg var -> var.vs_value
	| Pos var -> not_value var.vs_value

  let var_of_lit = function
	| Neg var | Pos var -> var

  type clause_state = 
	| Unit
	| Undef

  (** { 1 Clauses } *)

  let push_watch clause idx =
	match clause.cl_literals.(idx) with
	| Neg var -> VSet.push var.vs_watch_false (clause, idx)
	| Pos var -> VSet.push var.vs_watch_true (clause, idx)

  let conflict pbo clause = () 

  (**
	 Swap the two literals in the clause array
	 *)
  let swap_lit clause watch_idx new_idx =
	let old_watch =
	  clause.cl_literals.(watch_idx)
	in
	clause.cl_literals.(watch_idx) <- clause.cl_literals.(new_idx);
	clause.cl_literals.(new_idx) <- old_watch

  let eval_clause clause watch_idx = 
	let new_watch_lit idx = 
	  swap_lit clause watch_idx idx ;
	  push_watch clause watch_idx;
	  Undef
	in
	ArrayUtil.findi (fun lit -> eval_literal lit <> False) clause.cl_literals clause.cl_watch_end |>
	CCOpt.maybe new_watch_lit Unit 


  exception Conflict of clause

  let propagate_clause pbo clause =
	for idx = 0 to clause.cl_watch_end - 1 do
	  match eval_literal clause.cl_literals.(idx) with
	  | Undef -> 
		(* Add the current clause as antecedant for the variable *)
		(var_of_lit clause.cl_literals.(idx)).vs_antecedant <- Some clause;
		(* propagate the implication *)
		Vector.push pbo.pbo_trail (clause.cl_literals.(idx));
	  | True -> ()
	  | False -> raise (Conflict clause)
	done


  let propagate_watch pbo watch =
	let clause, literal = 
	  watch
	in
	match eval_clause clause literal with
	| Unit -> propagate_clause pbo clause; true 
	| Undef -> false

  let propagate_literal pbo d literal = 
	let watched, variable =
	  match literal with
	  | Pos variable -> variable.vs_watch_true, variable
	  | Neg variable -> variable.vs_watch_false, variable
	in
	variable.vs_decision_level <- d;
	if not (VSet.is_empty watched) then (
	  try
		VSet.filter (propagate_watch pbo) watched; None
	  with Conflict clause -> Some clause 
	) else 
	  None

  let branch pbo = 


(*
module type ClauseBuilderS = sig

type t

val empty : t
val add_lit : t -> literal -> t
val merge : t -> t -> t
val merge_clause : t -> clause -> t 
val to_clause : t -> int -> clause
val literal_with_d_level : t -> int -> unit
exception Found of variable

end 

module ClauseBuilder : ClauseBuilderS = struct

module VarMap = Map.Make(
struct
type t = variable
let compare v1 v2 = Var.compare v1.vs_id v2.vs_id
end)

type t = int VarMap.t

let empty = VarMap.empty

let merge_vars _ v1 v2 = 
match v1, v2 with
| Some v1, Some v2 -> Some (v1 + v2)
| Some v, _ | _, Some v -> Some v
| _,_ -> None

let merge t1 t2 = VarMap.merge merge_vars t1 t2

let add_lit t lit =
let incr, var = match lit with
| Neg var -> -1, var
| Pos var -> 1, var
in
let count =
try
VarMap.find var t
with Not_found -> 0
in
VarMap.add var (count + incr) t

let merge_clause t clause =
Array.fold_left (fun t lit -> add_lit t lit) t clause.cl_literals

let to_clause t const =
let size =
VarMap.fold (fun _ count size -> size + abs count) t 0
in
let clause = 
empty_clause size const
in
let build_lit_array var count idx =
let new_idx = 
idx + abs count - 1 
in
let lit = 
if count > 0 then
Pos var
else
Neg var
in
for i = idx to new_idx do 
clause.cl_literals.(i) <- lit
done;
new_idx
in
ignore (VarMap.fold build_lit_array t 0);
assert (clause.cl_watch_end < Array.length clause.cl_literals);
clause

exception Found of variable
(**
@param clause any clause
@param d a decision level in the decision tree
*)
let literal_with_d_level t d = 
let has_d_level var _ =  
if var.vs_decision_level = d && var.vs_antecedant <> None then
raise (Found var)
in
VarMap.iter has_d_level t 

end

(* XXX TODO *)
let decision_heuristic _ = null_lit

let learn_clause pbo conflict_clause =
let rec uip_fixpoint d clause_builder =
try
ClauseBuilder.literal_with_d_level clause_builder d;
ClauseBuilder.to_clause clause_builder 2
with ClauseBuilder.Found var ->
let clause = 
match var.vs_antecedant with
| None -> assert (false)
| Some clause -> clause 
in
uip_fixpoint d (ClauseBuilder.merge_clause clause_builder clause)
in
let start_clause =
ClauseBuilder.merge_clause ClauseBuilder.empty conflict_clause
in
let clause = 
uip_fixpoint pbo.pbo_decision_level start_clause
in
pbo.pbo_learnt_clauses <- clause :: pbo.pbo_learnt_clauses;
(* Compute the UIP *)
Array.fold_left (fun uip lit -> max uip (var_of_lit lit).vs_decision_level) (-1) clause.cl_literals



let eval_problem_state pbo = 
(* decide variable to be assigned *) 
let literal = 
decision_heuristic () 
in
assert (pbo.pbo_conflicts = []);
assert (pbo.pbo_propagation_stack = []);
(* Check if problem is SAT *)
if literal == null_lit then
SAT
else 
begin
(* Increase decision level *)
pbo.pbo_decision_level <- pbo.pbo_decision_level + 1;
(* apply decision *)
assign_literal pbo pbo.pbo_decision_level literal;
(* Simplify problem *)
List.iter (assign_literal pbo pbo.pbo_decision_level) pbo.pbo_propagation_stack;
pbo.pbo_propagation_stack <- [];
(* Learn from conflicts and backtrack *)
if pbo.pbo_conflicts <> [] then
begin
(* Make backtracking decision *)
let uip = 
List.map (learn_clause pbo) pbo.pbo_conflicts |>
List.fold_left (fun uip local_uip -> min local_uip uip) pbo.pbo_decision_level 
in
pbo.pbo_conflicts <- [];
(* Backtrack *)
let rec backtrack d = function
| [] -> []
| (curd, lit) :: q when curd < d ->
let var = 
(var_of_lit lit)
in 
var.vs_value <- Undef;
var.vs_decision_level <- -1;
var.vs_antecedant <- None;
backtrack d q 
| q -> q
in
pbo.pbo_decision_level <- pbo.pbo_decision_level - uip + 1;
pbo.pbo_trail <- backtrack  pbo.pbo_decision_level pbo.pbo_trail;
if pbo.pbo_trail = [] then
UNSAT
else
Unresolved
end
else
Unresolved
end

let update_cost_clause clause =
let cost = 
Array.fold_left (fun cost lit -> if eval_literal lit = True then cost + 1 else cost)
0 clause.cl_literals
in
let old_cost =
clause.cl_watch_end
in
assert (cost >= old_cost - 1);
let cost = 
if cost >= old_cost then
cost
else
old_cost + 1
in
clause.cl_watch_end <- cost;
for i = old_cost to cost - 1 do
push_watch clause i
done


let rec solve pbo = 
match eval_problem_state pbo with
| Unresolved -> solve pbo
| SAT -> 
begin
try
update_cost_clause (List.hd pbo.pbo_cost);
pbo.pbo_last_state <- SAT;
solve pbo
with Failure _ -> SAT
end

| UNSAT ->
begin
match pbo.pbo_cost with
| [] -> pbo.pbo_last_state
| a::q ->
begin
pbo.pbo_cost <- q;
pbo.pbo_cost_solved <- a :: pbo.pbo_cost_solved; 
solve pbo
end
end
 *)
end
