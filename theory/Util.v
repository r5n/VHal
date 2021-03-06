Set Warnings "-notation,-overridden,-parsing".
Require Import Coq.Init.Nat.
Require Import Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Definition beq_nat := PeanoNat.Nat.eqb.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof.
  intros s. unfold beq_string. destruct (string_dec s s) as [| Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem beq_string_true_iff : forall x y : string,
    beq_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold beq_string.
  destruct (string_dec x y) as [|Hs].
  - subst. split; reflexivity.
  - split.
    + intros contra. inversion contra.
    + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_string_false_iff : forall x y : string,
    beq_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite Bool.not_true_iff_false. reflexivity.
Qed.

Theorem false_beq_string : forall x y : string,
    x <> y -> beq_string x y = false.
Proof.
  intros x y. rewrite beq_string_false_iff.
  intros H. assumption.
Qed.

Theorem beq_string_comm : forall s s', beq_string s s' = beq_string s' s.
Proof.
  intros s s'. destruct (beq_string s s') eqn:H1.
  - apply beq_string_true_iff in H1. symmetry. rewrite beq_string_true_iff. auto.
  - apply beq_string_false_iff in H1. symmetry. rewrite beq_string_false_iff. auto.
Qed.

Fixpoint beq_string_list (ss : list string) (ts : list string) :=
  match ss with
  | [] => match ts with
         | [] => true
         | _ => false
         end
  | x :: xs => match ts with
              | y :: ys => andb (beq_string x y) (beq_string_list xs ys)
              | _ => false
              end
  end.

Theorem beq_string_list_refl : forall (ss : list string),
    beq_string_list ss ss = true.
Proof.
  intros. induction ss.
  - reflexivity.
  - simpl. rewrite <- beq_string_refl. assumption.
Qed.

Fixpoint insert_string (s : string) (ls : list string) :=
  match ls with
  | [] => [s]
  | t :: ts => if string_dec s t then s :: ts else t :: (insert_string s ts)
  end.

Definition string_decP s1 s2 : Prop :=
  if string_dec s1 s2 then True else False.

Definition ret {A : Type} (x : A) := Some x.
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some x => f x
  | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Lemma M_id_l : forall (A B : Type) (a : A) (f : A -> option B), ret a >>= f = f a.
Proof. intros. reflexivity. Qed.

Lemma M_id_r : forall (A : Type) (a : option A), a >>= ret = a.
Proof. intros. induction a; reflexivity. Qed.

Lemma M_assoc : forall (A B C : Type) (a : option A) (f : A -> option B) (g : B -> option C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
Proof. intros. induction a; reflexivity. Qed.
