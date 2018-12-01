Require Import
        VHal.theory.Fol
        VHal.theory.Util
        VHal.theory.Unify
        Coq.Lists.List
        Ascii
        Strings.String.
Import ListNotations.

Inductive state : Set :=
| State : list goal -> formula -> nat -> state.

Definition tactic := state -> option (list state).

Definition main (s : state) :=
  match s with
  | State _ p _ => p
  end.

Definition subgoals (s : state) :=
  match s with
  | State gs _ _ => gs
  end.

Definition initial (p : formula) := State [G ([], [p])] p O.

Definition final (s : state) :=
  match s with
  | State [] _ _ => true
  | _ => false
  end.

Definition splice_goals (gs : list goal) (newgs : list goal) (i : nat) :=
  List.firstn i gs ++ newgs ++ List.skipn i gs.


Definition prop_rule (gF : goal -> option (list goal)) (i : nat) (s : state) :=
  match s with
  | State gs p n =>
    (List.nth_error gs (i-1)) >>=
    (fun gi => gF gi >>=
    (fun gs' => ret (splice_goals gs gs' i) >>=
    (fun g2 => ret [State g2 p n])))
  end.

Definition prop_rule' (gF : goal -> option (list goal)) (i : nat) (s : state) :=
  match prop_rule gF i s with
  | Some s' => s'
  | None => []
  end.

(*! Tactics for basic sequents *)

Definition basic : nat -> tactic :=
  prop_rule
    (fun g => match g with
           | G (ps, qs) => if existsb (fun p => existsb (fun q => beq_formula p q) qs) ps
                       then Some [] else None
           end).

(* Solves goal [P |- Q] by unifying [P] with [Q].  Returns a list of successful environments *)
Fixpoint unifiable' (ts : list formula) (us : list formula) : list env :=
  match ts, us with
  | [], _ => []
  | p :: ps, qs =>
    ((fix ufind (qs : list formula) : list env :=
        match qs with
        | [] => unifiable' ps qs
        | q :: qs' => match atoms p q with
                     | Some e => e :: ufind qs'
                     | None => ufind qs'
                     end
        end) qs)
  end.

Fixpoint unifiable (g : goal) :=
  match g with
  | G (ps, qs) => unifiable' ps qs
  end.

Definition inst (e : env) (gs : list goal) (p : formula) (n : nat) :=
  State (List.map (inst_goal e) gs) p n.

Definition next (e : env) (gs : list goal) (p : formula) (i : nat) (n : nat) :=
  inst e (splice_goals gs [] i) p n.

(* For solvable goals with unfiable formulae on opposite sides *)
Fixpoint unif (i : nat) (s : state) : option (list state) :=
  match s with
  | State gs p n => (List.nth_error gs (i-1)) >>=
                   (fun g => ret (List.map (fun e => next e gs p i n) (unifiable g)))
  end.

(*! Propositional tactics *)

Fixpoint getp (a : string) (ls : list formula) :=
  match ls with
  | [] => None
  | (Conn b ps) :: qs => if beq_string a b then Some ps else getp a qs
  | q :: qs => getp a qs
  end.

Fixpoint delp (a : string) (ls : list formula) :=
  match ls with
  | [] => []
  | Conn b _ as q :: qs => if beq_string a b then qs else q :: delp a qs
  | q :: qs => q :: delp a qs
  end.

Definition split_conn (a : string) (qs : list formula) :=
  (getp a qs) >>= (fun ps => ret (ps, delp a qs)).

Definition prop_l (a : string) leftF :=
  prop_rule
    (fun g => match g with
           | G (ps, qs) => (split_conn a ps) >>= (fun ps' => leftF (ps', qs))
           end).

Definition prop_r (a : string) rightF :=
  prop_rule
    (fun g => match g with
           | G (ps, qs) => (split_conn a qs) >>= (fun qs' => rightF (ps, qs'))
           end).

Definition conjL : nat -> tactic :=
  prop_l "&" (fun x => match x with
                    | (([p1; p2], ps), qs) => ret [G (p1 :: p2 :: ps, qs)]
                    | _ => None
                    end).

Definition conjR : nat -> tactic :=
  prop_r "&" (fun x => match x with
                    | (ps, ([q1; q2], qs)) => ret [G (ps, q1 :: qs); G (ps, q2 :: qs)]
                    | _ => None
                    end).

Definition disjL : nat -> tactic :=
  prop_l "|" (fun x => match x with
                    | (([p1; p2], ps), qs) => ret [G (p1 :: ps, qs); G (p2 :: ps, qs)]
                    | _ => None
                    end).

Definition disjR : nat -> tactic :=
  prop_r "|" (fun x => match x with
                    | (ps, ([q1; q2], qs)) => ret [G (ps, q1 :: q2 :: qs)]
                    | _ => None
                    end).

Definition impL : nat -> tactic :=
  prop_l "-->" (fun x => match x with
                      | (([p1; p2], ps), qs) => ret [G (p2 :: ps, qs); G (ps, p1 :: qs)]
                      | _ => None
                      end).

Definition impR : nat -> tactic :=
  prop_r "-->" (fun x => match x with
                      | (ps, ([q1; q2], qs)) => ret [G (q1 :: ps, q2 :: qs)]
                      | _ => None
                      end).

Definition negL : nat -> tactic :=
  prop_l "~" (fun x => match x with
                    | (([p], ps), qs) => ret [G (ps, p :: qs)]
                    | _ => None
                    end).

Definition negR : nat -> tactic :=
  prop_r "~" (fun x => match x with
                    | (ps, ([q], qs)) => ret [G (q :: ps, qs)]
                    | _ => None
                    end).

Definition iffL : nat -> tactic :=
  prop_l "<->" (fun x => match x with
                      | (([p1; p2], ps), qs) => ret [G (p1 :: p2 :: ps, qs); G (ps, p1 :: p2 :: qs)]
                      | _ => None
                      end).

Definition iffR : nat -> tactic :=
  prop_r "<->" (fun x => match x with
                      | (ps, ([q1; q2], qs)) => ret [G (q1 :: ps, q2 :: qs); G (q2 :: ps, q1 :: qs)]
                      | _ => None
                      end).

(*! Quantifier tactics *)

Fixpoint getq (qnt : string) (ls : list formula) :=
  match ls with
  | [] => None
  | ((Quant qnt2 _ p) as q) :: qs => if beq_string qnt qnt2 then ret q
                                    else getq qnt qs
  | q :: qs => getq qnt qs
  end.

Fixpoint delq (qnt : string) (ls : list formula) :=
  match ls with
  | [] => []
  | ((Quant qnt2 _ p) as q) :: qs => if beq_string qnt qnt2 then qs
                                    else q :: delq qnt qs
  | q :: qs => q :: delq qnt qs
  end.

Fixpoint split_quant (qnt : string) (qs : list formula) :=
  (getq qnt qs) >>= (fun ps => ret (ps, delq qnt qs)).

Definition letter (n : nat) := String.substring n 1 "abcdefghijklmnopqrstuvwxyz".

Fixpoint gensym' (n : nat) (m : nat) :=
  match n with
  | S n' => if PeanoNat.Nat.ltb m 26 then append "_" (letter m)
           else append (gensym' n' (Nat.div m 26)) (letter (Nat.modulo m 26))
  | O => ""
  end.

Definition gensym (n : nat) := gensym' ((Nat.div n 26) + 1) n.

Theorem gensym_eq : forall n m, n = m -> beq_string (gensym n) (gensym m) = true.
Proof.
  intros n m H. apply beq_string_true_iff. now apply f_equal.
Qed.

Fixpoint quant_rule (gF : goal -> string -> option (list goal)) (i : nat) (s : state) :=
  match s with
  | State gs p n =>
    (List.nth_error gs (i-1)) >>=
    (fun g__i => gF g__i (gensym n) >>=
    (fun gs' => ret (splice_goals gs gs' i) >>=
    (fun g2 => ret [State g2 p (n + 1)])))
  end.

Definition allL : nat -> tactic :=
  quant_rule
    (fun x b =>
       match x with
       | G (ps, qs) =>
         (split_quant "ALL" ps) >>=
         (fun qntForm => match qntForm with
                      | ((Quant _ _ p) as q, ps') =>
                        let px := subst' O (Var b) p
                        in ret [G (px :: ps' ++ [q], qs)]
                      | _ => None
                      end)
       end).

Definition allR : nat -> tactic :=
  quant_rule
    (fun x b =>
       match x with
       | G (ps, qs) as g =>
         (split_quant "ALL" qs) >>=
         (fun qntForm => match qntForm with
                      | (Quant _ _ q, qs') =>
                        let vars := goal_vars g [] in
                        let qx := subst' O (Param b vars) q in
                        ret [G (ps, qx :: qs')]
                      | _ => None
                      end)
       end).

Definition exL : nat -> tactic :=
  quant_rule
    (fun x b =>
       match x with
       | G (ps, qs) as g =>
         (split_quant "EX" ps) >>=
         (fun qntForm => match qntForm with
                      | (Quant _ _ p, ps') =>
                        let vars := goal_vars g [] in
                        let px := subst' O (Param b vars) p in
                        ret [G (px :: ps', qs)]
                      | _ => None
                      end)
       end).

Definition exR : nat -> tactic :=
  quant_rule
    (fun x b =>
       match x with
       | G (ps, qs) =>
         (split_quant "EX" ps) >>=
         (fun qntForm => match qntForm with
                      | ((Quant _ _ q) as q', qs') =>
                        let qx := subst' O (Var b) q in
                        ret [G (ps, qx :: qs' ++ [q'])]
                      | _ => None
                      end)
       end).
