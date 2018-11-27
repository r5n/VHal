Set Warnings "-notation-overridden,-parsing".
Require Import Arith.
Require Import Ascii.
Require Import Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import VHal.theory.Util.

Open Scope string_scope.

(*+ Terms and Formulae *)

Inductive term : Set :=
| Var : string -> term                           (* a name *)
| Param : string -> list string -> term           (* list of forbidden names *)
| Bound : nat -> term                              (* an index *)
| Fun : string -> list term -> term.              (* name and argument list *)

Inductive formula : Set :=                   
| Pred : string -> list term -> formula           (* predicate name; arg list *)
| Conn : string -> list formula -> formula        (* connective; list of formulae *)
| Quant : string -> string -> formula -> formula.  (* quantifier; var name; body *)

Check term_ind.

Inductive goal : Set :=
| G : list formula * list formula -> goal.

(*! Induction principle for [term] *)
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

(*! Induction principle for [formula] *)
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

Definition eq_term_dec : forall (t t' : term), { t = t' } + { t <> t' }.
Proof.
  pose eq_nat_dec. pose string_dec. pose list_eq_dec.
  pose term_eq_dec. decide equality.
Qed.

(* Definition beq_term (s : term) (t : term) := *)
(*   if term_eq_dec s t then true else false. *)

Fixpoint beq_term (t1 : term) (t2 : term) : bool :=
  match t1, t2 with
  | Var u, Var v => beq_string u v
  | Param s st, Param s' st' =>
    beq_string s s' && beq_string_list st st'
  | Bound n, Bound m => beq_nat n m
  | Fun u us, Fun v vs =>
    beq_string u v &&
    ((fix beq_term_list (us : list term) (vs : list term) : bool :=
        match us, vs with
        | [], [] => true
        | _, [] => false
        | [], _ => false
        | x :: xs, y :: ys => andb (beq_term x y) (beq_term_list xs ys)
        end) us vs)
  | _, _ => false
  end.


Theorem beq_term_refl : forall t : term,
    beq_term t t = true.
Proof.
  apply term_ind'; (try intros; simpl; symmetry).
  - apply beq_string_refl.
  - rewrite <- beq_string_refl. rewrite beq_string_list_refl.
    reflexivity.
  - apply beq_nat_refl.
  - induction ls as [| t' ls' IHls'].
    + rewrite <- beq_string_refl. reflexivity.
    + inversion H. apply IHls' in H3. rewrite H2. simpl.
      assumption.
Qed.

(*+ Functions on terms *)

(* look at https://bit.ly/2RNCENB for dealing with nested inductive types *)

(* [replace] : replace the term [u1] with [u2] throughout a term [t] *)
Fixpoint replace' (u1 : term) (u2 : term) (t : term) : term :=
  if beq_term u1 t then u2 else
    match t with
    | Fun a ts => Fun a
      ((fix replace'_list (u1 : term) (u2 : term) (ts : list term) { struct ts } :=
          match ts with
          | [] => []
          | s :: ss => (replace' u1 u2 s) :: (replace'_list u1 u2 ss)
          end) u1 u2 ts)
    | _ => t
    end.
      
Example replace_test1 : replace' (Var "x") (Var "y") (Var "x") = Var "y".
Proof. reflexivity. Qed.

Example replace_test2 : replace' (Var "x") (Var "y") (Fun "x" [Var "x"; Var "y"])
                        = Fun "x" [Var "y"; Var "y"].
Proof. reflexivity. Qed.

(* Abstraction of a formula over the atomic term t *)
Fixpoint abstract' (i : nat) (t : term) (f : formula) :=
  match f with
  | Pred a ts => Pred a (map (replace' t (Bound i)) ts)
  | Conn b ps => Conn b
    ((fix abstract'_list (i : nat) (t : term) (fs : list formula) { struct fs } :=
        match fs with
        | [] => []
        | f :: fs' => (abstract' i t f) :: (abstract'_list i t fs')
        end) i t ps)
  | Quant qnt b p => Quant qnt b (abstract' (S i) t p)
  end.

Compute abstract' O (Var "x") (Conn "/\" [(Pred "1" [Var "x"]); (Pred "2" [Var "y"])]).

Example abstract'_test1 :
  abstract' O (Var "x") (Conn "\/" [(Pred "H1" [Var "x"; Var "y"]);
                                      (Pred "H2" [Var "y"; Var "x"])])
  = Conn "\/" [(Pred "H1" [Bound 0; Var "y"]); (Pred "H2" [Var "y"; Bound 0])].
Proof. reflexivity. Qed.

Example abstract'_test2 :
  abstract' O (Var "x") (Quant "forall" "x" (Pred "P" [Var "x"]))
  = Quant "forall" "x" (Pred "P" [Bound (S O)]).
Proof. reflexivity. Qed.

(* Replace [Bound i] by [t] in [f].  [t] may contain no bound variables *)
Fixpoint subst' (i : nat) (t : term) (f : formula) : formula :=
  match f with
  | Pred a ts => Pred a (map (replace' (Bound i) t) ts)
  | Conn b ps => Conn b
    ((fix subst'_list (i : nat) (t : term) (fs : list formula) { struct fs } :=
        match fs with
        | [] => []
        | f :: fs' => (subst' i t f) :: (subst'_list i t fs')
        end) i t ps)
  | Quant qnt b p => Quant qnt b (subst' (S i) t p)
  end.

Example subst'_test1 :
  subst' (S O) (Var "x") (Conn "/\" [Quant "forall" "x" (Pred "P" [Bound (S (S O))]);
                                       Quant "exists" "y" (Pred "Q" [Var "y"])])
  = (Conn "/\" [Quant "forall" "x" (Pred "P" [Var "x"]);
                  Quant "exists" "y" (Pred "Q" [Var "y"])]).
Proof. reflexivity. Qed.

Example subst'_test2 :
  subst' O (Var "x") (Pred "x" [Bound O]) = Pred "x" [Var "x"].
Proof. reflexivity. Qed.

Example subst'_test3 :
  subst' O (Bound O) (Pred "x" [Bound O]) = Pred "x" [Bound O].
Proof. reflexivity. Qed.

Fixpoint term_vars (t : term) (ps : list string) : list string :=
  match t with
  | Var a => insert_string a ps
  | Fun _ ts => List.fold_right term_vars ps ts
  | _ => ps
  end.

Example term_vars_test1 :
  term_vars (Var "x") [] = ["x"].
Proof. reflexivity. Qed.

Example term_vars_test2 :
  term_vars (Fun "a" [Var "x"; Var "y"; Fun "a" [Var "c"; Var "d"]]) []
  = ["d"; "c"; "y"; "x"].
Proof. reflexivity. Qed.

Fixpoint term_params (t : term) (ps : list (string * list string)) :=
  match t with
  | Param a xs => (a, xs) :: ps
  | Fun _ ts => List.fold_right term_params ps ts
  | _ => ps
  end.



  