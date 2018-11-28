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

Definition occurs (a : string) (t : term) : bool :=
  orb (existsb (beq_string a) (term_vars t []))
      (existsb (beq_string a) (List.flat_map snd (term_params t []))).

Example occurs_test1 : occurs "x" (Var "x") = true.
Proof. reflexivity. Qed.

Example occurs_test2 : occurs "t" (Fun "P" [Var "t"; Var "b"; Var "t"]) = true.
Proof. reflexivity. Qed.

Example occurs_test3 : occurs "t" (Fun "t" [Var "z"; Var "y"; Var "x"]) = false.
Proof. reflexivity. Qed.

Example occurs_test4 : occurs "x" (Param "f" ["x"; "y"; "z"]) = true.
Proof. reflexivity. Qed.

Example occurs_test5 : occurs "x" (Fun "PRED" [Var "z"; Param "f" ["x"; "y"; "z"]]) = true.
Proof. reflexivity. Qed.

Example occurs_test6 :
  occurs "x" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = true.
Proof. reflexivity. Qed.

Example occurs_test7 :
  occurs "t" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = true.
Proof. reflexivity. Qed.

Example occurs_test8 :
  occurs "z" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = false.
Proof. reflexivity. Qed.

Theorem occurs_var : forall s s' : string, occurs s (Var s') = true -> s = s'.
Proof.
  intros s s' H. unfold occurs in H. simpl in *. apply Bool.orb_true_iff in H. destruct H.
  - apply Bool.orb_true_iff in H. destruct H.
    + apply beq_string_true_iff. assumption.
    + inversion H.
  - inversion H.
Qed.

Theorem occurs_env_inv : forall (es : list string) (ps : list (string * list string)) (t : term) (s : string),
    occurs s t = true -> In s (term_vars t es) \/ In s (List.flat_map snd (term_params t ps)).
Proof.
  intros es ps t s H. induction t using @term_ind'.
  - simpl in *. left. apply occurs_var in H. subst. induction es.
    + simpl. left. trivial.
    + simpl. destruct (string_dec s0 a) eqn:H.
      * simpl. left. trivial.
      * simpl. right. assumption.
  - unfold occurs in H. simpl in *. right. induction ps.
    + rewrite app_nil_r in *. apply existsb_exists in H.
      destruct H as [s' [H1 H2]]. apply beq_string_true_iff in H2. subst.
      assumption.
    + simpl in *. rewrite in_app_iff in *. destruct IHps eqn:H'.
      * left. assumption.
      * right. apply in_app_iff. right. assumption.
  - inversion H.
  - admit.
Admitted.

Section Occ.

  Fixpoint occurs_fuel (n : nat) (e : env) (s : string) (t : term) : bool :=
    match n with
    | O => false
    | S n' => match t with
             | Var x => orb (beq_string x s)
                           (let v := env_lookup e x in
                            match v with
                            | Some t => occurs_fuel n' e s t
                            | _ => false
                            end)
             | Fun _ ts =>
               ((fix occurs'_list (s : string) (ts : list term) :=
                   match ts with
                   | [] => false
                   | v :: vs => orb (occurs_fuel n' e s v)
                                   (occurs'_list s vs)
                   end) s ts)
             | Param _ bs =>
               ((fix occurs'_params (s : string) (ss : list string) :=
                   match ss with
                   | [] => false
                   | v :: vs => orb (occurs_fuel n' e s (Var v))
                                   (occurs'_params s vs)
                   end) s bs)
             | _ => false
             end
    end.

  Definition occ (e : env) (s : string) (t : term) : bool :=
    occurs_fuel (Nat.max (length e) (size t)) e s t.

  Definition oc' (s : string) (t : term) := occ [] s t.

  Example oc'_test1 : oc' "x" (Var "x") = true.
  Proof. reflexivity. Qed.
  Example oc'_test2 : oc' "t" (Fun "P" [Var "t"; Var "b"; Var "t"]) = true.
  Proof. reflexivity. Qed.
  Example oc'_test3 : oc' "t" (Fun "t" [Var "z"; Var "y"; Var "x"]) = false.
  Proof. reflexivity. Qed.
  Example oc'_test4 : oc' "x" (Param "f" ["x"; "y"; "z"]) = true.
  Proof. reflexivity. Qed.
  Example oc'_test5 : oc' "x" (Fun "PRED" [Var "z"; Param "f" ["x"; "y"; "z"]]) = true.
  Proof. reflexivity. Qed.
  Example oc'_test6 :
    oc' "x" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = true.
  Proof. reflexivity. Qed.
  Example oc'_test7 :
    oc' "t" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = true.
  Proof. reflexivity. Qed.
  Example oc'_test8 :
    oc' "z" (Fun "PRED" [Var "t"; Fun "-1" [Param "f" ["x"]]; Fun "O" [Param "x" ["f"]]]) = false.
  Proof. reflexivity. Qed.

  Theorem oc'_var_eq : forall s s', oc' s (Var s') = true -> s = s'.
  Proof.
    intros s s' H. unfold oc' in H. unfold occ in H. simpl in *.
    destruct (beq_string s' s) eqn:H'.
    - apply beq_string_true_iff. rewrite beq_string_comm. assumption.
    - inversion H.
  Qed.

  (* Theorem oc'_occurs_equiv : forall s t, oc' s t = occurs s t. *)
  (* Proof. *)
  (*   intros s t. induction t using @term_ind'. *)
  (*   - unfold occurs, oc', occ. simpl in *. rewrite beq_string_comm. *)
  (*     destruct (beq_string s s0); simpl; trivial. *)
  (*   - induction ls. *)
  (*     + trivial. *)
  (*     + unfold occurs, oc', occ. simpl in *. destruct (beq_string a s) eqn:H. *)
  (*       * simpl. unfold "||". rewrite beq_string_comm, H. trivial. *)
  (*       * edestruct (_ s ls). *)
  (*         ++ rewrite app_nil_r, beq_string_comm, H. simpl. *)
  (*            destruct (oc' s (Param s0 ls)). *)
  (*            ** unfold occurs in IHls. simpl in IHls. rewrite app_nil_r in IHls. *)
  (*               assumption. *)
  (*            ** unfold occurs in IHls. simpl in IHls. rewrite app_nil_r in IHls. *)
  (*               rewrite <- IHls.  *)
End Occ.
               
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

Definition well_founded_contraints_lt : well_founded constraints_lt :=
  @wf_lexprod context (fun _ : context => list constr)
              (fun (x y : context) => length x < length y)
              (fun (x : context) (l l' : list constr) => list_measure l < list_measure l')
              (well_founded_ltof context (@length string))
              (fun _ => well_founded_ltof (list constr) list_measure).
