Set Warnings "-notation,-overridden,-parsing".
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

Definition beq_string (s1 : string) (s2 : string) :=
  if string_dec s1 s2 then true else false.

Lemma beq_string_refl : forall (s : string),
    beq_string s s = true.
Proof.
  intros. induction s as [| a s].
  - reflexivity.
  - unfold beq_string. destruct (string_dec (String a s) (String a s)).
    + reflexivity.
    + destruct n. reflexivity.
Qed.

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

