  From mathcomp Require Import all_ssreflect .
  From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
  From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
  From mathcomp Require Import cardinality fsbigop.
  Require Reals Interval.Tactic.
  From AUChain Require Import GlobalState  CG Rstruct_topology.
  From AUChain Require Import Schedule.
  From mathcomp Require Import (canonicals) Rstruct.
  From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
  From mathcomp Require Import reals ereal interval_inference topology normedtype.
  From mathcomp Require Import sequences realfun convex real_interval.
  From mathcomp Require Import derive esum measure exp numfun lebesgue_measure measurable_realfun.
  From mathcomp Require Import lebesgue_integral kernel probability.
  From mathcomp Require Import hoelder unstable.
  From mathcomp Require Import archimedean.
  From HB Require Import structures.
  From AUChain Require Import sampling.
  From AUChain Require Import
     Network
     Protocol
     GlobalState
     Blocks
     Messages
     MessageTuple
     Parameters
     BlockTree
     Schedule
     LocalState
     MemEq
     SsrFacts
     TreeChain
     CG.

  Import Order.TTheory GRing.Theory Num.Def Num.Theory.
  Import numFieldTopology.Exports numFieldNormedType.Exports.
  Import hoelder ess_sup_inf.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.


  Set Printing Notations.
  Unset Printing Implicit.
  Unset Printing Coercions.
  Unset Printing Universes.
  Unset Printing All.
  Local Open Scope ereal_scope.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope schedule_scope.
  Section set_lemmas.
    Variable (I : Type).
    Variable (R : realType).
    Lemma ST_Set :  forall (s : set I) , setT `&` s = s.
    Proof.
        move => s.
        apply /seteqP.
        split;move => i Hi.
        apply Hi.
        rewrite //=.
    Qed.
    
    Lemma setT_def : ([set _ | true] : set I) = setT.
    Proof.
        apply/seteqP.
        split.
        rewrite //=.
        rewrite //=.
    Qed.


    Lemma set0_def : ([set _ | false] : set I) = set0.
    Proof.
        apply/seteqP.
        split.
        rewrite //=.
        rewrite //=.
    Qed.

    Lemma set_lt_eq_neg_le : 
    forall (A B : R),
    [set r : I | (B < A)%R] = ~` [set r : I | (A <= B)%R].
    Proof.
        move => A B.
        apply/seteqP.
        split.
        - move => r.
          rewrite //=.
          rewrite ltNge.
          move /negP => H.
          apply H.
        move => r.
        rewrite //=.
        rewrite ltNge.
        move /negP => H.
        apply H.
    Qed.

End set_lemmas.

