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
     CG
     additional_lemmas.

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




Section pos_proof.
    Local Open Scope ereal_scope.

    Local Open Scope classical_set_scope.
    Local Open Scope ring_scope.
    Local Open Scope schedule_scope.
    Let R := Rdefinitions.R.
    Context {d} (T : measurableType d)  (P : probability T R). 

    Variable pLs pSs pAs : R.
    Variable nbre_de_slots : nat.
    Hypothesis n_sup_O: (0 < nbre_de_slots)%nat. 
    Hypothesis pLs01 : (0 <= pLs <= 1)%R.
    Hypothesis pSs01 : (0 <= pSs <= 1)%R.
    Hypothesis pAs01 : (0 <= pAs <= 1)%R.
    Variable LS : nbre_de_slots.-tuple (bernoulliRV P pLs).
    Variable SS : nbre_de_slots.-tuple (bernoulliRV P pSs).
    Variable AS : nbre_de_slots.-tuple (bernoulliRV P pAs).
    Variable deltaLs deltaSs deltaAs : R.
    Hypothesis delta_range_Ls : (0 < deltaLs < 1)%R.
    Hypothesis delta_range_Ss : (0 < deltaSs < 1)%R.
    Hypothesis delta_range_As : (0 < deltaAs < 1)%R.
    Hypothesis lottery_assumption_CP : exists epsilon , (epsilon > 0) -> pSs >= (pAs *+ 2) + epsilon .
    Hypothesis lottery_assumption_CQ : exists epsilon , (epsilon > 0) -> pLs >= pAs + epsilon.
    Definition LS_r := bool_trial_value LS.
    Definition SS_r := bool_trial_value SS.
    Definition AS_r := bool_trial_value AS.
    Variables (N N' : GlobalState).
    Hypothesis N_from_initial : N0 ⇓ N .
    Hypothesis N_is_ready : N @ Ready.
    Hypothesis N'_from_N :  N ⇓^+ N'.
    Variables (p1 p2 : Party).
    Hypothesis p1_honest : is_honest p1.
    Hypothesis p2_honest : is_honest p2.
    Variable (l1 l2 : LocalState).
    Hypothesis l1_p1_state : has_state p1 N l1.
    Hypothesis l2_p2_state : has_state p2 N' l2.
    Locate "||".
    Hypothesis LS_r_eq_slotrange : forall r,  (LS_r r  = | lucky_slots_range (t_now N) (t_now N' - 1) |%:R)%N.
    
    
    
    
    Check (sampling_ineq3 pLs01 LS delta_range_Ls).
    Check (sampling_ineq3 pSs01 SS  delta_range_Ss).
    Check (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).

      
    Lemma complementary_specialized_LS : 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (\X_nbre_de_slots P) [set i | ~~ (X' i <= (1 - deltaLs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value LS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E - 
      (\X_nbre_de_slots P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
    Proof.
      rewrite /= .
      set X' := bool_trial_value LS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      set B :=  (1 - deltaLs) * fine mu.
      set A := [set i | X' i <= B ].
      set Pr := (\X_nbre_de_slots P).
      have  Hsame :
      [set i | ~~ (X' i <= B )] = ~` A.
      {
      apply/seteqP.
      split.
      - move => i Hi.
        rewrite /A /= .
        rewrite /= in Hi.
        move /negP in Hi.
        apply Hi.
      move => i Hi.
      rewrite /A /= in Hi.
      rewrite /=.
      apply /negP.
      apply Hi.
      }
      rewrite Hsame.
      apply probability_setC.
      rewrite -(ST_Set A).
      apply: (measurable_fun_le (D := setT) (f := X') (g := fun _ => B)) .
      - apply: measurableT.
      - by rewrite //=.
      by rewrite //=.
    Qed.
      



    Lemma complementary_Ls_Bound :
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (\X_nbre_de_slots P) [set i | (1 - deltaLs) * fine mu <  X' i ]%R
    = 
      let X' := bool_trial_value LS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E - 
      (\X_nbre_de_slots P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
    Proof.
    rewrite -complementary_specialized_LS /=.
    set X' := bool_trial_value LS.
    set mu := 'E_(\X_nbre_de_slots P)[X'].
    set B := ((1 - deltaLs) * fine mu)%R.
    have Hset :
    [set i | B < X' i]%R =
    [set i | ~~ (X' i <= B)%R].
    {
      rewrite seteqP.
      split.
      - move  => i Hn /=.
        rewrite -ltNge.
        apply Hn.
      move => i Hn /=.
      rewrite /= -ltNge in Hn.
      apply Hn.
    }
    by rewrite Hset.
  Qed.




  Theorem chain_growth_bound : 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E -
      (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
    <=
    (\X_nbre_de_slots P)
      [set i | (1 - deltaLs) * fine mu < X' i]%R)%E.
    Proof.
      rewrite /=.
      
      have H1:= (sampling_ineq3 pLs01 LS delta_range_Ls).
      rewrite complementary_Ls_Bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value LS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.

  Definition Chain_growth_ls_Good_event :=
    let X' := bool_trial_value LS in 
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    [set r | ((1 - deltaLs) * fine mu < X' r)%R].

  Definition chain_growth_parties_event (w : nat)  :=
  let X' := bool_trial_value LS in 
  [set r : nbre_de_slots.-tuple T | ((|bestChain (t_now N - 1)%N (tree l1)| + w)%N <= |bestChain (t_now N' - 1)%N (tree l2)|)%N].
  

  Lemma Good_Ls_implies_chain_growth w :
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  w%:R <= (1 - deltaLs) * fine mu
  -> 
  (forall r , Chain_growth_ls_Good_event r-> chain_growth_parties_event w r).
  Proof.
    move => X' mu H1 r H2.
    rewrite /chain_growth_parties_event //=.
    apply chain_growth_parties with (p1 := p1) (p2 := p2) ; try easy.
    rewrite /Chain_growth_ls_Good_event in H2.
    rewrite -(ler_nat R).
    rewrite -(LS_r_eq_slotrange r).
    rewrite //=  in H2.
    rewrite -/mu in H2.
    rewrite -/LS_r in H2.
    apply ltW in H2.
    apply (le_trans H1).
    apply H2.
  Qed.
  
    

  Lemma probability_implication (w : nat) :
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  w%:R <= (1 - deltaLs) * fine mu
  ->
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  ((\X_nbre_de_slots P) Chain_growth_ls_Good_event<= (\X_nbre_de_slots P) (chain_growth_parties_event w))%E .
  Proof.
  move => X' mu H1.
  set B := ((1 - deltaLs) * fine mu)%R.
  apply: le_measure.
  - 
    rewrite /Chain_growth_ls_Good_event -/X'.
    rewrite -/B.
    have Hinvertedle:
    [set r | (B < X' r)%R] = ~` [set r | (X' r <= B)%R].
    {
      apply /seteqP.
      split.
      - move => r .
        rewrite //=.
        rewrite ltNge.
        move /negP  => H.
        apply H.
      - move => r.
        rewrite //=.
        rewrite ltNge.
        move /negP => H.
        apply H.
    }
    rewrite Hinvertedle.
    
    have Hle :
    (measurable_structure.measure_tuple_display d).-measurable [set r | (X' r <= B)%R] .
    {
      rewrite -(ST_Set [set r | X' r <= B]).
      apply (measurable_fun_le (D := setT) (f := X') (g := fun _ => B)); rewrite //=.
    }
    rewrite //=.
    rewrite inE.
    apply : measurableC.
    apply Hle.
  
  - rewrite /chain_growth_parties_event.
    case Hcmp : (((|bestChain (t_now N - 1)%N (tree l1)| + w)%N <= |bestChain (t_now N' - 1)%N (tree l2)|)%N).

    + rewrite //=.
      rewrite inE //=.
      rewrite setT_def.
      apply /measurableT.
    +  rewrite set0_def inE.
      apply /measurable0.
      
  move =>r.
  apply Good_Ls_implies_chain_growth.
  apply H1.
  Qed.

  Theorem Chernoff_bound_chain_growth_parties_even (w:nat): 
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  w%:R <= (1 - deltaLs) * fine mu 
  ->
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  (
  ((1%R)%:E - (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
  <= 
  ((\X_nbre_de_slots P) (chain_growth_parties_event w))%E
  )%E.
  Proof.
    move => X' mu H.
    apply (le_trans chain_growth_bound).
    apply (probability_implication H).
  Qed.  
     




      Lemma complementary_specialized_SS : 
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (\X_nbre_de_slots P) [set i | ~~ (X' i <= (1 - deltaSs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value SS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E - 
      (\X_nbre_de_slots P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
    Proof.
      rewrite /= .
      set X' := bool_trial_value SS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      set B :=  (1 - deltaSs) * fine mu.
      set A := [set i | X' i <= B ].
      set Pr := (\X_nbre_de_slots P).
      have  Hsame :
      [set i | ~~ (X' i <= B )] = ~` A.
      {
      apply/seteqP.
      split.
      - move => i Hi.
        rewrite /A /= .
        rewrite /= in Hi.
        move /negP in Hi.
        apply Hi.
      move => i Hi.
      rewrite /A /= in Hi.
      rewrite /=.
      apply /negP.
      apply Hi.
      }
      rewrite Hsame.
      apply probability_setC.
      rewrite -(ST_Set A).
      apply: (measurable_fun_le (D := setT) (f := X') (g := fun _ => B)) .
      - apply: measurableT.
      - by rewrite //=.
      by rewrite //=.
    Qed.

    Lemma complementary_SS_bound:
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (\X_nbre_de_slots P) [set i | (1 - deltaSs) * fine mu <  X' i ]%R
    = 
      let X' := bool_trial_value SS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E - 
      (\X_nbre_de_slots P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
    Proof.
    rewrite -complementary_specialized_SS /=.
    set X' := bool_trial_value SS.
    set mu := 'E_(\X_nbre_de_slots P)[X'].
    set B := ((1 - deltaSs) * fine mu)%R.
    have Hset :
    [set i | B < X' i]%R =
    [set i | ~~ (X' i <= B)%R].
    {
      rewrite seteqP.
      split.
      - move  => i Hn /=.
        rewrite -ltNge.
        apply Hn.
      move => i Hn /=.
      rewrite /= -ltNge in Hn.
      apply Hn.
    }
    by rewrite Hset.
  Qed.

      


  Theorem complementary_SS_event : 
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E -
      (expR (-(fine mu * deltaSs ^+ 2) / 2)%R)%:E)%E
    <=
    (\X_nbre_de_slots P)
      [set i | (1 - deltaSs) * fine mu < X' i]%R)%E.
    Proof.
      rewrite /=.
      
      have H1:= (sampling_ineq3 pSs01 SS delta_range_Ss).
      rewrite complementary_SS_bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value SS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.


  Lemma complementary_specialized_AS : 
    let X' := bool_trial_value AS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (\X_nbre_de_slots P) [set i | ~~ (X' i >= (1 + deltaAs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value AS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E - 
      (\X_nbre_de_slots P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
    Proof.
      rewrite /= .
      set X' := bool_trial_value AS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      set B :=  (1 + deltaAs) * fine mu.
      set A := [set i | X' i >= B ].
      set Pr := (\X_nbre_de_slots P).
      have  Hsame :
      [set i | ~~ (X' i >= B )] = ~` A.
      {
      apply/seteqP.
      split.
      - move => i Hi.
        rewrite /A /= .
        rewrite /= in Hi.
        move /negP in Hi.
        apply Hi.
      move => i Hi.
      rewrite /A /= in Hi.
      rewrite /=.
      apply /negP.
      apply Hi.
      }
      rewrite Hsame.
      apply probability_setC.
      rewrite -(ST_Set A).
      apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g :=X' )) .
      - apply: measurableT.
      - by rewrite //=.
      by rewrite //=.
    Qed.


Lemma complementary_AS_bound:
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  (\X_nbre_de_slots P) [set i |  X' i   < (1 + deltaAs) * fine mu ]%R
  = 
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_nbre_de_slots P)[X'] in
  (((1%R)%:E - 
  (\X_nbre_de_slots P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
  Proof.
    rewrite -complementary_specialized_AS /=.
    set X' := bool_trial_value AS.
    set mu := 'E_(\X_nbre_de_slots P)[X'].
    set B := ((1 + deltaAs) * fine mu)%R.
    have Hset :
    [set i | X' i  < B]%R =
    [set i | ~~ (X' i >= B)%R].
    {
      rewrite seteqP.
      split.
      - move  => i Hn /=.
        rewrite -ltNge.
        apply Hn.
      move => i Hn /=.
      rewrite /= -ltNge in Hn.
      apply Hn.
    }
    by rewrite Hset.
  Qed.



  Theorem complementary_AS_event : 
    let X' := bool_trial_value AS in
    let mu := 'E_(\X_nbre_de_slots P)[X'] in
    (((1%R)%:E -
      (expR (-(fine mu * deltaAs ^+ 2) / 3)%R)%:E)%E
    <=
    (\X_nbre_de_slots P)
      [set i | X' i < (1 + deltaAs) * fine mu]%R)%E.
    Proof.
      rewrite /=.
      
      have H1:= (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
      rewrite complementary_AS_bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value AS.
      set mu := 'E_(\X_nbre_de_slots P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.



Lemma SS_gt_2AS : 
    let XSS := bool_trial_value SS in
    let XAS := bool_trial_value AS in
    let muSS := 'E_(\X_nbre_de_slots P)[XSS] in
    let muAS := 'E_(\X_nbre_de_slots P)[XAS] in
    ( ((1+deltaAs) * fine muAS) *+ 2) < (1 - deltaSs) * fine muSS
    ->
    forall r,
    (1+deltaAs) * fine muAS > AS_r r  ->
    ((1-deltaSs) * fine muSS) < SS_r r->
    (SS_r r> (AS_r r) *+ 2).
    Proof.
      move => XSS XAS muSS muAS H1 r H11 H12.
      have H112T :
      AS_r r *+ 2< ((1 + deltaAs) * fine muAS) *+ 2.
      {
        Search "ltr_pmul2l".
        rewrite  ltr_wpMn2r.
        - rewrite //=.
        - rewrite //=.
        apply H11.
      }
      Print lt_trans.
      apply: (lt_trans H112T).
      apply: (lt_trans H1).
      apply H12.
    Qed.


Variables  (epsilon:R).


Lemma epsilon_condition_CP :
  (1 - deltaSs) * ((pAs *+ 2) + epsilon) >
  (1 + deltaAs) * (pAs *+ 2) ->
  epsilon > (((1 + deltaAs) / (1 - deltaSs)) - 1) * (pAs *+ 2).
  
  Proof.
    move => H.
    rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon) ) in H.

    rewrite -(ltr_pdivrMr (pAs *+ 2 + epsilon)) in H.
    rewrite mulrBl.
    rewrite (mulrC (1 + deltaAs)) in H.
    rewrite (mulrC (pAs *+ 2)) in H.
    rewrite mulrC.
    rewrite mulrC.
    rewrite ltrBlDr.
    About mul1r.
    rewrite mul1r.
    rewrite (addrC epsilon). 
    rewrite -mulrA.
    rewrite (mulrC ((1 - deltaSs)^-1)).
    rewrite mulrA.
    apply H.
    rewrite subr_gt0.
    move/andP : delta_range_Ss => [H1 H2].
    apply H2.
  Qed.
    

End pos_proof.


      













    
     
    


  




