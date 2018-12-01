Require Import
        VHal.theory.Util
        VHal.theory.Fol
        VHal.theory.Unify
        VHal.theory.Rule.


Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "./ml/vhal.ml"
           (* from Util.v *)
           beq_string beq_string_list ret bind
           (* from Fol.v  *)
           term formula goal abstract' subst' term_vars goal_vars goal_params
           (* from Unify.v *)
           atoms inst_term inst_form inst_goal
           (* from Rule.v *)
           state tactic main subgoals initial final basic unif
           conjL conjR disjL disjR impL impR negL negR iffL iffR
           allL allR exL exR.

