Require Import
        VHal.theory.Fol
        VHal.theory.Util
        VHal.theory.Unify
        Coq.Lists.List
        Coq.Lists.Streams.
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

