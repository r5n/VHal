Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import VHal.theory.Util.
Import ListNotations.

(*+ Total Maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

Notation "{ --> d }" := (t_empty d) (at level 0).
Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
  (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).

Lemma t_apply_empty : forall (A : Type) (x : string) (v: A), { --> v } x = v.
Proof.
  intros. reflexivity.
Qed.

Lemma t_update_eq : forall A (m : total_map A) x v,
    (m & { x --> v }) x = v.
Proof.
  intros. unfold "m & { x --> v }".
  rewrite <- beq_string_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (X : Type) v x1 x2 (m : total_map X),
    x1 <> x2 -> (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite false_beq_string.
  reflexivity. assumption.
Qed.

Lemma t_update_shadow : forall A (m : total_map A) v1 v2 x,
    m & { x --> v1 ; x --> v2 } = m & { x --> v2 }.
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros. destruct (beq_string x x0); reflexivity.
Qed.

Lemma beq_stringP : forall x y, reflect (x = y) (beq_string x y).
Proof.
  intros. eapply iff_reflect. symmetry.
  apply beq_string_true_iff.
Qed.

Lemma t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros. destruct (beq_stringP x x0).
  - apply f_equal. assumption.
  - reflexivity.
Qed.

(*+ Partial Maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  m & { x --> (Some v) }.

Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
  (update (m & {{ a --> x ; b --> y ; c --> z }}) c z) (at level 20).

Lemma apply_empty : forall (A : Type) (x : string), @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m : partial_map A) x v,
    (m & {{ x --> v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X : Type) v x1 x2 (m : partial_map X),
    x2 <> x1 -> (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  assumption.
Qed.

Theorem update_shadow : forall X v x (m : partial_map X),
    m x = Some v -> m & {{ x --> v }} = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.
