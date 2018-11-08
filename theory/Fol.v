Set Warnings "-notation-overridden,-parsing".
Require Import Arith.
Require Import Ascii.
Require Import Strings.String.
Require Import VHal.theory.Util.
Open Scope string_scope. (* learn to use strings properly *)

Inductive term : Type :=
| Var : string -> term                           (* a name *)
| Param : string * list string -> term           (* list of forbidden names *)
| Bound : nat -> term                              (* an index *)
| Fun : string * list term -> term.              (* name and argument list *)

Inductive formula  : Type :=                   
| Pred : string * list term -> formula           (* predicate name; arg list *)
| Conn : string * list formula -> formula        (* connective; list of formulae *)
| Quant : string * string * formula -> formula.  (* quantifier; var name; body *)

Inductive goal : Type :=
| G : list formula * list formula -> goal.

