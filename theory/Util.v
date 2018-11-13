Set Warnings "-notation,-overridden,-parsing".
Require Import Coq.Init.Nat.
Require Import Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.
Open Scope list_scope.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) .. ).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Fixpoint map {X Y : Type} (f: X->Y) (l: list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Definition beq_nat := PeanoNat.Nat.eqb.

Fixpoint beq_string (s1 : string) (s2 : string) :=
  match s1 with
  | "" => match s2 with
         | "" => true
         | _ => false
         end
  | String a s1' => match s2 with
                   | "" => false
                   | String b s2' =>
                     let a' := nat_of_ascii a in
                     let b' := nat_of_ascii b in
                     andb (beq_nat a' b') (beq_string s1' s2')
                   end
  end.

(* Definition beq_string (s1 : string) (s2 : string) := *)
(*   if string_dec s1 s2 then true else false. *)

Lemma beq_string_refl : forall (s : string),
    beq_string s s = true.
Proof.
  intros. induction s as [| a s]; try reflexivity.
  - simpl. rewrite <- EqNat.beq_nat_refl. assumption.
Qed.

Lemma beq_string_empty_r : forall (s : string),
    beq_string s "" = true -> s = "".
Proof.
  intros. induction s; (try reflexivity; inversion H).
Qed.

Lemma beq_string_empty_l : forall (s : string),
    beq_string "" s = true -> s = "".
Proof.
  intros. induction s; (try reflexivity; inversion H).
Qed.

Lemma beq_string_correct : forall (s : string) (t : string),
    beq_string s t = true -> s = t.
Proof.
  intro s. induction s.
  - intros. rewrite (beq_string_empty_l _ H). reflexivity.
  - destruct t.
    + discriminate.
    + admit.
Admitted.
  
Lemma beq_string_comm : forall (s : string) (t : string),
    beq_string s t = true -> beq_string t s = true.
Proof.
  intros. generalize dependent s. induction t.
  - intros. rewrite (beq_string_empty_r _ H). reflexivity.
  - admit.
Admitted.
      
Fixpoint beq_string_list (ss : list string) (ss': list string) :=
  match ss with
  | [] => match ss' with
         | [] => true
         | _ => false
         end
  | x :: xs => match ss' with
              | y :: ys => andb (beq_string x y) (beq_string_list xs ys)
              | _ => false
              end
  end.

Theorem beq_string_list_refl : forall (ss : list string),
    beq_string_list ss ss = true.
Proof.
  intros. induction ss.
  - reflexivity.
  - simpl. rewrite beq_string_refl. assumption.
Qed.
