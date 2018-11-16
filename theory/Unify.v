Require Import VHal.theory.Fol.
Require Import VHal.theory.Util.
Require Import VHal.theory.Maps.
Require Import Coq.Lists.List.
Import ListNotations.

(*+ Environments *)

(*! An attempt at using Dependent Types *)
Inductive envd : nat -> partial_map term -> Type :=
| EO : envd O empty
| ES : forall n m s t, envd n m -> envd (S n) (m & {s --> t}).

Definition envd_update {n} {m} e s t : envd (S n) (m & {s --> t}) :=
  ES n m s t e.

Definition envd_lookup {n} {m} (e : envd n m) (s : string) := m s.

Notation " e & {| a --> x |} " := (envd_update e a (Some x)) (at level 20).
Notation " e & {| a --> x ; b --> y |} " :=
  (envd_update (e & {| a --> x |}) b (Some y)) (at level 20).
Notation " e & {| a --> x ; b --> y ; c --> z |} " :=
  (envd_update (e & {| a --> x; b --> y|}) c (Some z)) (at level 20).
Notation " e % x " := (envd_lookup e x) (at level 20).

Compute EO % "x".
Compute (EO & {| "x" --> Var "z" |}).
Compute (EO & {| "x" --> Bound O ; "y" --> Bound 1 |}).
Compute (EO & {| "x" --> Bound O ; "y" --> Bound 1 ; "z" --> Bound 2 |}) % "z".

(*! List representation *)
Definition env := list (string * term).

Definition env_update (e : env) (s : string) (t : term) := (s,t) :: e.

Fixpoint env_lookup (e : env) (s : string) :=
  match e with
  | [] => None
  | (s',t) :: ts => if beq_string s s'
                   then Some t else env_lookup ts s
  end.

(*+ Unification *)

Definition chase (e : env) (t : term) :=
  match t with
  | Var x =>
    ((fix chase' (n : nat) (e : env) (s : string) { struct n } :=
        match n with
        | O => Some t
        | S n' => let v := env_lookup e s in
                 match v with
                 | Some (Var y) => chase' n' e y
                 | _ => v
                 end
        end) (length e) e x)
  | _ => Some t
  end.


Example chase_test1 : chase [("x", Var "y"); ("y", Bound 1)] (Var "x") = Some (Bound 1).
Proof. reflexivity. Qed.

Example chase_test2 :
  chase [("x", Var "y"); ("y", Var "z"); ("z", Bound 3)] (Var "x") = Some (Bound 3).
Proof. reflexivity. Qed.

Example chase_test3 :
  chase [("x", Var "y")] (Var "d") = None.
Proof. reflexivity. Qed.

Fixpoint b_exists {A : Type} (f : A -> bool) (ls : list A) : bool :=
  match ls with
  | [] => false
  | h :: t => f h || b_exists f t
  end.


(* Fixpoint occurs (e : env) (a : string) (t : term) := *)
(*   match t with *)
(*   | Fun _ ts => occsl e a ts *)
(*   | Param _ bs => occsl e a (List.map Var bs) *)
(*   | Var b => orb (beq_string a b) (match env_lookup e b with *)
(*                                   | Some t => occurs e a t *)
(*                                   | _ => false *)
(*                                   end) *)
(*   | _ => false *)
(*   end *)
(* with occsl e a := b_exists (occurs e a). *)
