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

(* Program Fixpoint occurs (e : env) (a : string) (t : term) {measure (sizeT t)} := *)
(*   match t with *)
(*   | Fun _ ts => existsb (fun y => occurs e a y) ts *)
(*   | Param _ bs => existsb (fun y => occurs e a y) (List.map Var bs) *)
(*   | Var b => orb (beq_string a b) (match env_lookup  e b with *)
(*                                   | Some x => occurs e a x *)
(*                                   | _ => false *)
(*                                   end) *)
(*   | _ => false *)
(*   end. *)

Fixpoint occurs0 (a : string) (t : term) : bool :=
  match t with
  | Var b => beq_string a b
  | Param _ bs => existsb (beq_string a) bs
  | Fun _ ts =>
    ((fix occurs'_list (a : string) (ts : list term) { struct ts } :=
        match ts with
        | [] => false
        | t :: ts' => orb (occurs0 a t) (occurs'_list a ts')
        end) a ts)
  | _ => false
  end.

(** * Well-Formedness Conditions *)

Definition context := list string.

Fixpoint member (C : context) (s : string) : Prop :=
  match C with
  | [] => False
  | v :: vs => if string_dec s v then True else member vs s
  end.

Definition member_dec : forall C i, { member C i } + { ~ member C i }.
Proof.
  refine (fix member_dec (C : context) (i : string) : { member C i } + { ~ member C i } :=
            match C with
            | [] => right _ _
            | v :: vs =>
              match string_dec v i with
              | left _ => left _ _
              | right _ =>
                match member_dec vs i with
                | left _ => left _ _
                | right _ => right _ _
                end
              end
            end); auto.
  - unfold member. destruct (string_dec i v) eqn:H; auto.
    + unfold "~" in n; symmetry in e. pose proof (n e). inversion H0.
  - simpl. destruct (string_dec i v); auto.
  - simpl. destruct (string_dec i v); auto.
Defined.

Fixpoint wf_term (C : context) (t : term) : Prop :=
  match t with
  | Var x => member C x
  | Fun _ ts =>
    ((fix wf_termlist (ts : list term) : Prop :=
        match ts with
        | [] => True
        | t :: ts' => wf_term C t /\ wf_termlist ts'
        end) ts)
  | _ => True
  end.

Definition wf_term_dec : forall C t, { wf_term C t } + { ~ wf_term C t }.
Proof.
  refine (fix wf_term_dec (C : context) (t : term) : { wf_term C t } + { ~ wf_term C t } :=
            match t with
            | Var x => if member_dec C x then left _ _ else right _ _
            | Fun _ ts =>
              ((fix wf_termlist_dec (C : context) (ts : list term) :=
                  match ts with
                  | [] => left _ _
                  | t :: ts' => match wf_term_dec C t, wf_termlist_dec C ts' with
                               | left _, left _ => left _ _
                               | _, _ => right _ _
                               end
                  end) C ts)
            | _ => left _ _
            end); (simpl; try assumption; try auto); (unfold "~"; intros; firstorder).
Defined.

Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Definition constr := (term * term)%type.
Definition constraints := sigT (fun _ : context => list constr).
Definition get_list_constr (c : constraints) : list constr := let (_, l) := c in l.
Definition mk_constraints (C : context) (l : list constr) : constraints := existT _ C l.

Fixpoint size (t : term) : nat :=
  match t with
  | Var _ => 1
  | Fun _ ts => S
    ((fix sizelist (ts : list term) : nat :=
        match ts with
        | [] => O
        | t :: ts' => size t + sizelist ts'
        end) ts)
  | Param _ bs => S (length bs)
  | Bound _ => 1
  end.

Definition constr_size (c : constr) : nat :=
  match c with
    (t, t') => size t + size t'
  end.

Fixpoint list_measure (l : list constr) : nat :=
  match l with
  | [] => O
  | c :: cs => constr_size c + list_measure cs
  end.

Definition constraints_lt : constraints -> constraints -> Prop :=
  lexprod context (fun _ => list constr)
          (fun (x y : context) => length x < length y)
          (fun (x : context) (l l' : list constr) => list_measure l < list_measure l').

(*! NEED TO CHECK THIS CAREFULLY *)
Definition well_founded_contraints_lt : well_founded constraints_lt :=
  @wf_lexprod context (fun _ : context => list constr)
              (fun (x y : context) => length x < length y)
              (fun (x : context) (l l' : list constr) => list_measure l < list_measure l')
              (well_founded_ltof context (@length string))
              (fun _ => well_founded_ltof (list constr) list_measure).

(* Program Fixpoint some_occurs (e : env) (a : string) (t : term) { measure (size t) } := *)
(*   match t with *)
(*   | Fun _ ts => existsb (fun y => some_occurs e a y) ts *)
(*   | Param _ bs => existsb (fun y => some_occurs e a (Var y)) bs *)
(*   | Var b => orb (beq_string a b) (match env_lookup e b with *)
(*                                   | Some x => some_occurs e a x *)
(*                                   | _ => false *)
(*                                   end) *)
(*   | _ => false *)
(*   end. *)

(* Fixpoint occurs' (e : env) (a : string) (t : term) : Prop := *)
(*   match t with *)
(*   | Fun _ ts => *)
(*     ((fix occurs'_list (a : string) (ts : list term) { struct ts } := *)
(*         match ts with *)
(*         | [] => False *)
(*         | t :: ts' => occurs' e a t \/ occurs'_list a ts' *)
(*         end) a ts) *)
(*   | Param _ bs => *)
(*     ((fix occurs'_list (a : string) (bs : list string) { struct bs } := *)
(*         match bs with *)
(*         | [] => False *)
(*         | b :: bs' => occurs' e a (Var b) \/ occurs'_list a bs' *)
(*         end) a bs) *)
(*   | Var b => if string_dec a b then True else (match env_lookup e b with *)
(*                                            | Some x => occurs' e a x *)
(*                                            | _ => False *)
(*                                            end) *)
(*   | _ => False *)
(*   end. *)

(* Function occurs (e : env) (a : string) (t : term) { measure sizeT t } := *)
(*   match t with *)
(*   | Fun _ ts => existsb (occurs e a) ts *)
(*   | Param _ bs => existsb (occurs e a) (List.map Var bs) *)
(*   | Var b => orb (beq_string a b) (match env_lookup e b with *)
(*                                   | Some x => occurs e a x *)
(*                                   | _ => false *)
(*                                   end) *)
(*   | _ => false *)
(*   end. *)