
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val sub : int -> int -> int

val divmod : int -> int -> int -> int -> int * int

val div : int -> int -> int

val modulo : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val pow : int -> int -> int
 end

val nth_error : 'a1 list -> int -> 'a1 option

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val string_dec : char list -> char list -> bool

val append : char list -> char list -> char list

val substring : int -> int -> char list -> char list

val beq_nat : int -> int -> bool

val beq_string : char list -> char list -> bool

val beq_string_list : char list list -> char list list -> bool

val insert_string : char list -> char list list -> char list list

val ret : 'a1 -> 'a1 option

val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

type term =
| Var of char list
| Param of char list * char list list
| Bound of int
| Fun of char list * term list

type formula =
| Pred of char list * term list
| Conn of char list * formula list
| Quant of char list * char list * formula

type goal = formula list * formula list
  (* singleton inductive, whose constructor was G *)

val beq_term : term -> term -> bool

val replace' : term -> term -> term -> term

val abstract' : int -> term -> formula -> formula

val subst' : int -> term -> formula -> formula

val term_vars : term -> char list list -> char list list

val term_params : term -> (char list * char list list) list -> (char list * char list list) list

val beq_term_list : term list -> term list -> bool

val beq_formula : formula -> formula -> bool

val accum_form : (term -> 'a1 -> 'a1) -> formula -> 'a1 -> 'a1

val accum_goal : (formula -> 'a1 -> 'a1) -> goal -> 'a1 -> 'a1

val goal_vars : goal -> char list list -> char list list

val goal_params : goal -> (char list * char list list) list -> (char list * char list list) list

type env = (char list * term) list

val env_update : env -> char list -> term -> (char list * term) list

val env_lookup : env -> char list -> term option

val chase : env -> term -> term option

val size : term -> int

val occurs_fuel : int -> env -> char list -> term -> bool

val occ : env -> char list -> term -> bool

val oc' : char list -> term -> bool

val chase' : env -> term -> term option

val get_env : (int * env) -> env

val unify_fuel : int -> env -> term -> term -> (int * env) option

val unifyl_fuel : int -> env -> term list -> term list -> (int * env) option

val unify_lists : term list -> term list -> env option

val atoms : formula -> formula -> env option

val inst_term_fuel : int -> env -> term -> term

val inst_term : env -> term -> term

val inst_form : env -> formula -> formula

val inst_goal : env -> goal -> goal

type state =
| State of goal list * formula * int

type tactic = state -> state list option

val main : state -> formula

val subgoals : state -> goal list

val initial : formula -> state

val final : state -> bool

val splice_goals : goal list -> goal list -> int -> goal list

val prop_rule : (goal -> goal list option) -> int -> state -> state list option

val basic : int -> tactic

val unifiable' : formula list -> formula list -> env list

val unifiable : goal -> env list

val inst : env -> goal list -> formula -> int -> state

val next : env -> goal list -> formula -> int -> int -> state

val unif : int -> state -> state list option

val getp : char list -> formula list -> formula list option

val delp : char list -> formula list -> formula list

val split_conn : char list -> formula list -> (formula list * formula list) option

val prop_l :
  char list -> (((formula list * formula list) * formula list) -> goal list option) -> int -> state -> state
  list option

val prop_r :
  char list -> ((formula list * (formula list * formula list)) -> goal list option) -> int -> state -> state
  list option

val conjL : int -> tactic

val conjR : int -> tactic

val disjL : int -> tactic

val disjR : int -> tactic

val impL : int -> tactic

val impR : int -> tactic

val negL : int -> tactic

val negR : int -> tactic

val iffL : int -> tactic

val iffR : int -> tactic

val getq : char list -> formula list -> formula option

val delq : char list -> formula list -> formula list

val split_quant : char list -> formula list -> (formula * formula list) option

val letter : int -> char list

val gensym' : int -> int -> char list

val gensym : int -> char list

val quant_rule : (goal -> char list -> goal list option) -> int -> state -> state list option

val allL : int -> tactic

val allR : int -> tactic

val exL : int -> tactic

val exR : int -> tactic

(** ADDED *)

val ctocs : char list -> string

val stocs : string -> char list

val makeForall : string -> formula -> formula

val makeExists : string -> formula -> formula

val makeConn : string -> formula -> formula -> formula

val makeNeg : formula -> formula                                      
                   
