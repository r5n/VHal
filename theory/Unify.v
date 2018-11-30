Require Import VHal.theory.Fol.
Require Import VHal.theory.Util.
Require Import VHal.theory.Maps.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
Import ListNotations.

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

Definition chase' (e : env) (t : term) : option term :=
  let v := chase e t in
  match v with
  | None => Some t
  | _ => v
  end.

Definition get_env (e' : nat * env) : env := let (_, v) := e' in v.

Fixpoint unify_fuel (n : nat) (e : env) (s : term) (t : term) : option (nat * env) :=
  match n with
  | S m => match s, t with
          | Var a as s', _ => if beq_term t s' then ret (m, e)
                             else if oc' a t then None
                                  else ret (m, (env_update e a t))
          | _, Var a => unify_fuel m e (Var a) s
          | Param a _, Param b _ => if beq_string a b then ret (m, e) else None
          | Fun a ts, Fun b us => if beq_string a b then unifyl_fuel m e ts us else None
          | _, _ => None
          end
  | O => None
  end
with unifyl_fuel (n : nat) (e : env) (ts : list term) (us : list term) : option (nat * env) :=
       match n with
       | S m => match ts, us with
               | [], [] => ret (m, e)
               | t :: ts', u :: us' => (chase' e t) >>= (fun t' =>
                                      (chase' e u) >>= (fun u' =>
                                      (unify_fuel m e t' u') >>= (fun e' =>
                                      (unifyl_fuel m (get_env e') ts' us'))))
               | _, _ => None
               end
       | O => None
       end.

Definition unify (s : term) (t : term) :=
  (unify_fuel (2 ^ (size s) * (size t)) [] s t) >>= (fun e => ret (get_env e)).

Definition unify_lists (ts : list term) (us : list term) :=
  if beq_nat (length ts) (length us) then
    (unifyl_fuel (2 ^ (List.fold_right plus O (List.map size ts))) [] ts us) >>= (fun e => ret (get_env e))
  else None.

Example ul_test1 : unify_lists [Var "c"; Var "x"] [Var "x"; Var "c"] = Some [("x", Var "c"); ("c", Var "x")].
Proof. reflexivity. Qed.

Theorem ul_nil : forall e, unify_lists [] [] = Some e -> e = [].
Proof.
  intros e H. compute in H. inversion H. reflexivity.
Qed.

Theorem ul_nil_l_some : forall ts e, unify_lists [] ts = Some e -> ts = [].
Proof.
  intros ts e H. induction ts.
  - reflexivity.
  - discriminate.
Qed.

Theorem ul_nil_r_some : forall ts e, unify_lists ts [] = Some e -> ts = [].
Proof.
  intros ts e H. induction ts.
  - reflexivity.
  - compute in H. inversion H.
Qed.

(*! Need to prove more theorems about unify_lists *)


Definition atoms (f : formula) (g : formula) :=
  match f, g with
  | Pred a ts, Pred b us => if beq_string a b then unify_lists ts us else None
  | _, _ => None
  end.


Fixpoint inst_term_fuel (n : nat) (e : env) (t : term) :=
  match n with
  | S m => match t with
          | Fun a ts => Fun a (List.map (inst_term_fuel m e) ts)
          | Param a bs => Param a (List.fold_right term_vars [] (List.map (fun x => inst_term_fuel m e (Var x)) bs))
          | Var a => match env_lookup e a with
                    | Some t' => inst_term_fuel m e t'
                    | None => Var a
                    end
          | _ => t
          end
  | O => t
  end.

Definition inst_term (e : env) (t : term) :=
  inst_term_fuel (2 ^ (length e)) e t.


Fixpoint inst_form (e : env) (f : formula) :=
  match f with
  | Pred a ts => Pred a (List.map (inst_term e) ts)
  | Conn b ps => Conn b (List.map (inst_form e) ps)
  | Quant qnt b p => Quant qnt b (inst_form e p)
  end.

Definition inst_goal (e : env) (g : goal) :=
  match g with
    | G (ps, qs) => (List.map (inst_form e) ps, List.map (inst_form e) qs)
  end.

