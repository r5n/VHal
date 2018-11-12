Set Warnings "-notation-overridden,-parsing".
Require Import Arith.
Require Import Ascii.
Require Import Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import VHal.theory.Util.
(* Open Scope string_scope. (* learn to use strings properly *) *)

Inductive term : Set :=
| Var : string -> term                           (* a name *)
| Param : string -> list string -> term           (* list of forbidden names *)
| Bound : nat -> term                              (* an index *)
| Fun : string -> list term -> term.              (* name and argument list *)

Inductive formula : Set :=                   
| Pred : string -> list term -> formula           (* predicate name; arg list *)
| Conn : string -> list formula -> formula        (* connective; list of formulae *)
| Quant : string -> string -> formula -> formula.  (* quantifier; var name; body *)

Inductive goal : Set :=
| G : list formula * list formula -> goal.

Section term_ind'.
  Variable P : term -> Prop.

  Hypothesis Var_case : forall s : string, P (Var s).
  Hypothesis Param_case : forall (s : string) (ls : list string), P (Param s ls).
  Hypothesis Bound_case : forall (n : nat), P (Bound n).
  Hypothesis Fun_case : forall (s : string) (ls : list term),
      Forall P ls -> P (Fun s ls).

  Fixpoint term_ind' (t : term) : P t :=
    match t with
    | Var s => Var_case s
    | Param s ls => Param_case s ls
    | Bound n => Bound_case n
    | Fun s ls => Fun_case s ls
      ((fix list_term_ind (ls : list term) : Forall P ls :=
          match ls with
          | [] => Forall_nil _
          | t :: ts => Forall_cons _ (term_ind' t) (list_term_ind ts)
          end) ls)
    end.
End term_ind'.

Section formula_ind'.
  Variable P : formula -> Prop.

  Hypothesis Pred_case : forall (s : string) (ls : list term), P (Pred s ls).
  Hypothesis Conn_case : forall (s : string) (ls : list formula),
      Forall P ls -> P (Conn s ls).
  Hypothesis Quant_case : forall (s s' : string) (f : formula),
      P f -> P (Quant s s' f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
    | Pred s ls => Pred_case s ls
    | Conn s ls => Conn_case s ls
      ((fix list_formula_ind (ls : list formula) : Forall P ls :=
          match ls with
          | [] => Forall_nil _
          | f :: fs => Forall_cons _ (formula_ind' f) (list_formula_ind fs)
          end) ls)
    | Quant s s' f => Quant_case s s' f (formula_ind' f)
    end.
End formula_ind'.

(* https://bit.ly/2D7M02y *)
Parameter term_eq_dec : forall (σ τ : term), { σ = τ } + { σ <> τ }.

Definition beq_term (s : term) (t : term) :=
  if term_eq_dec s t then true else false.

(* https://bit.ly/2RNCENB *)
Definition replace_one (u1 : term) (u2 : term) (t : term) :=
  if beq_term t u1 then u2 else
    let fix replace_one_aux (u1 : term) (u2 : term) (t : term) { struct t } : term :=
        match t with
        | Fun a args =>
          (Fun a
               ((fix replace_one_many_aux u1 u2 ts :=
                   match ts with
                   | [] => []
                   | t :: ts =>
                     (replace_one_aux u1 u2 t)
                       :: (replace_one_many_aux u1 u2 ts)
                   end) u1 u2 args))
        | _ => t
        end
    in replace_one_aux u1 u2 t.