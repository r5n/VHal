Set Warnings "-notation,-overridden,-parsing".
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

