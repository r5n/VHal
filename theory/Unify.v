Require Import VHal.theory.Fol.
Require Import VHal.theory.Util.
Require Import VHal.theory.Maps.
Require Import Coq.Lists.List.
Require Import Recdef.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
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

(* Use [existsb] from the Lists library instead of [b_exists] *)

Section OCCURS.
  Variable e : env.

  Inductive occurs : string -> term -> Prop :=
  | occF : forall s t ts, Exists (occurs s) ts -> occurs s (Fun t ts)
  | occP : forall s b bs, Exists (occurs s) (List.map Var bs) -> occurs s (Param b bs)
  | occVb : forall s b, beq_string s b = true -> occurs s (Var b)
  | occVr : forall s b t, env_lookup e s = Some t -> occurs s t -> occurs s (Var b).

  Definition occurs_dec : forall s t, { occurs s t } + { ~ occurs s t }.
  Proof.
    intros. destruct t eqn:T.
    - compute. destruct (beq_string s s0) eqn:H.
      + left. eapply occVb. assumption.
      + right. pose proof (occVb s s0).
        admit.
    - admit.
    - admit.
    - admit.
      all : fail.
  Admitted.
End OCCURS.

Print well_founded.
Print Acc.
Print Fix.

(** * Dealing with the Occurs Check *)
(** 1. Use an [Inductive] type and then show that the relation is decidable.
    2. Use the [Fix] combinator with a well founded ordering
    3. Use [Program Fixpoint] with a well founded ordering *)

(** Think about other ways of defining the occurs check.  Computing the free and bound
    variables can help *)

Fixpoint sizeT (t : term) : nat :=
  match t with
  | Var _ => 1
  | Fun _ ts => 1 +
    ((fix sizeT' (ts : list term) { struct ts } :=
        match ts with
        | [] => 0
        | t :: ts' => sizeT t + sizeT' ts'
        end) ts)
  | Param _ bs => length bs
  | Bound _ => 1
  end.

Definition sizeOrder (t t' : term) :=
  sizeT t < sizeT t'.

Program Fixpoint occurs' (e : env) (a : string) (t : term) {measure (sizeT t)} :=
  match t with
  | Fun _ ts => existsb (fun y => occurs' e a y) ts
  | Param _ bs => existsb (fun y => occurs' e a y) (List.map Var bs)
  | Var b => orb (beq_string a b) (match env_lookup  e b with
                                  | Some x => occurs' e a x
                                  | _ => false
                                  end)
  | _ => false
  end.
Obligation 1.
Proof.
  induction y using @term_ind'.
  - simpl.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.

Function occurs (e : env) (a : string) (t : term) { measure sizeT t } :=
  match t with
  | Fun _ ts => existsb (occurs e a) ts
  | Param _ bs => existsb (occurs e a) (List.map Var bs)
  | Var b => orb (beq_string a b) (match env_lookup e b with
                                  | Some x => occurs e a x
                                  | _ => false
                                  end)
  | _ => false
  end.

(* Function occurs (e : env) (a : string) (t : term) { measure term_size t } := *)
(*   match t with *)
(*   | Fun _ ts => b_exists (occurs e a) ts *)
(*   | Param _ bs => b_exists (occurs e a) (List.map Var bs) *)
(*   | Var b => orb (beq_string a b) (match env_lookup e b with *)
(*                                   | Some t => occurs e a t *)
(*                                   | _ => false *)
(*                                   end) *)
(*   | _ => false *)
(*   end. *)


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

