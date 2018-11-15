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
