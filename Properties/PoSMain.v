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
     CP
     CQ
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




    Definition tuple_interval_index {T : Type} (a b n : nat) (t : n.-tuple T) :=
    drop a (take b t).
    
    
    Compute tuple_interval_index 3 6  [:: 1;2;3;4;5;6;7;8;9;10].
  
    Local Open Scope ereal_scope.

    Local Open Scope classical_set_scope.
    Local Open Scope ring_scope.
    Local Open Scope schedule_scope.
    Let R := Rdefinitions.R.
    Context {d} (T : measurableType d)  (P : probability T R). 

    Variable Sc : nat.
    Hypothesis n_sup_O: (0 < Sc)%nat. 
    
    
    (* Probabilities for LuckySlot, SuperSlot and AversarialSlot*)
    Variable pLs pSs pAs : R.
    Hypothesis pLs01 : (0 <= pLs <= 1)%R.
    Hypothesis pSs01 : (0 <= pSs <= 1)%R.
    Hypothesis pAs01 : (0 <= pAs <= 1)%R.
    
    (*tuple of boolean values to model a multiple bernoulli draw*)
    Variable LS : Sc.-tuple (bernoulliRV P pLs).
    Variable SS : Sc.-tuple (bernoulliRV P pSs).
    Variable AS : Sc.-tuple (bernoulliRV P pAs).
    
    Definition LS_r := bool_trial_value LS.
    Definition SS_r := bool_trial_value SS.
    Definition AS_r := bool_trial_value AS.

    (*Delta assumptions*)
    Variable deltaLs deltaSs deltaAs : R.
    Hypothesis delta_range_Ls : (0 < deltaLs < 1)%R.
    Hypothesis delta_range_Ss : (0 < deltaSs < 1)%R.
    Hypothesis delta_range_As : (0 < deltaAs < 1)%R.

    (*lottery assumption for CP and CQ bounds*)
    Hypothesis lottery_assumption_CP : exists epsilon , (epsilon > 0) /\ pSs >= (pAs *+ 2) + epsilon .
    Hypothesis lottery_assumption_CQ : exists epsilon , (epsilon > 0) /\ pLs >= pAs + epsilon.
    
    Variable (epsilon : R).
    
    
    
    Check (sampling_ineq3 pLs01 LS delta_range_Ls).
    Check (sampling_ineq3 pSs01 SS  delta_range_Ss).
    Check (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
    
    
    Search (honest_advantage_ranges_gt _ _).
    
    Section ChainGrowth.
    
    (*GlobalStates assumptions*)
    Variables (N N' : GlobalState).
    Hypothesis N_from_initial : N0 ⇓ N .
    Hypothesis N_is_ready : N @ Ready.
    Hypothesis N'_from_N :  N ⇓^+ N'.

    (*party assumptions corresponding to CG assumptions for now*)
    Variables (p1 p2 : Party).
    Hypothesis p1_honest : is_honest p1.
    Hypothesis p2_honest : is_honest p2.

    (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
    Variable (l1 l2 : LocalState).
    Hypothesis l1_p1_state : has_state p1 N l1.
    Hypothesis l2_p2_state : has_state p2 N' l2.
    
    (*Assumption to link the bool_trial_value LS to the amount of lucky slots between N and N'*)
    Hypothesis LS_r_eq_slotrange : forall r, (LS_r r  = | lucky_slots_range (t_now N) (t_now N' - 1) |%:R)%N.	
 
    Lemma Sc_pos_R : (0 < (Sc%:R : R))%R.
    Proof.
      by rewrite ltr0n.
    Qed.
    Lemma complementary_specialized_LS : 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (\X_Sc P) [set i | ~~ (X' i <= (1 - deltaLs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - 
      (\X_Sc P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
    Proof.
      move => X' mu.
      by rewrite complementary_specialized_le.
    Qed.
      



    Lemma complementary_Ls_Bound :
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (\X_Sc P) [set i | (1 - deltaLs) * fine mu <  X' i ]%R
    = 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - (\X_Sc P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
   
    Proof.
      move => X' mu.
      rewrite -complementary_specialized_LS .
      by rewrite set_gt_as_compl_le.
    Qed.




    Theorem chain_growth_bound : 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
    <=
    (\X_Sc P) [set i | (1 - deltaLs) * fine mu < X' i]%R)%E.
    Proof.
      rewrite /=.
      have H1:= (sampling_ineq3 pLs01 LS delta_range_Ls).
      rewrite complementary_Ls_Bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value LS.
      set mu := 'E_(\X_Sc P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.

    Definition Chain_growth_ls_Good_event :=
    let X' := bool_trial_value LS in 
    let mu := 'E_(\X_Sc P)[X'] in
    [set r | ((1 - deltaLs) * fine mu < X' r)%R].

    Definition chain_growth_parties_event (w : nat)  :=
    let X' := bool_trial_value LS in 
    [set r : Sc.-tuple T | ((|bestChain (t_now N - 1)%N (tree l1)| + w)%N <= |bestChain (t_now N' - 1)%N (tree l2)|)%N].
    

    Lemma Good_Ls_implies_chain_growth w :
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
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
    let mu := 'E_(\X_Sc P)[X'] in
    w%:R <= (1 - deltaLs) * fine mu
    ->
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    ((\X_Sc P) Chain_growth_ls_Good_event<= (\X_Sc P) (chain_growth_parties_event w))%E .
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
      rewrite set_lt_eq_neg_le.
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
      + rewrite set0_def inE.
        apply /measurable0.
        
    move =>r.
    apply Good_Ls_implies_chain_growth.
    apply H1.
    Qed.

    Theorem Chernoff_bound_chain_growth_parties_even (w:nat): 
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    w%:R <= (1 - deltaLs) * fine mu 
    ->
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (
    ((1%R)%:E - (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
    <= 
    ((\X_Sc P) (chain_growth_parties_event w))%E
    )%E.
    Proof.
      move => X' mu H.
      apply (le_trans chain_growth_bound).
      apply (probability_implication  H).
    Qed.
  
  End ChainGrowth.


  Lemma complementary_specialized_SS : 
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (\X_Sc P) [set i | ~~ (X' i <= (1 - deltaSs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - 
      (\X_Sc P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
    Proof.
      move => X' mu. 
      by rewrite complementary_specialized_le.
    Qed.

    Lemma complementary_SS_bound:
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (\X_Sc P) [set i | (1 - deltaSs) * fine mu <  X' i ]%R
    = 
      let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - 
      (\X_Sc P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
    Proof.
    move => X' mu.
    rewrite -complementary_specialized_SS.
    by rewrite -(set_gt_as_compl_le).
  Qed.

      


  Theorem complementary_SS_event : 
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (expR (-(fine mu * deltaSs ^+ 2) / 2)%R)%:E)%E
    <=
    (\X_Sc P)
      [set i | (1 - deltaSs) * fine mu < X' i]%R)%E.
    Proof.
      rewrite /=.
      
      have H1:= (sampling_ineq3 pSs01 SS delta_range_Ss).
      rewrite complementary_SS_bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value SS.
      set mu := 'E_(\X_Sc P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.


  Lemma complementary_specialized_AS : 
    let X' := bool_trial_value AS in
    let mu := 'E_(\X_Sc P)[X'] in
    (\X_Sc P) [set i | ~~ (X' i >= (1 + deltaAs) * fine mu)%R ]%R
    = 
      let X' := bool_trial_value AS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - 
      (\X_Sc P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
    Proof.
      rewrite /= .
      set X' := bool_trial_value AS.
      set mu := 'E_(\X_Sc P)[X'].
      set B :=  (1 + deltaAs) * fine mu.
      set A := [set i | X' i >= B ].
      set Pr := (\X_Sc P).
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
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i |  X' i   < (1 + deltaAs) * fine mu ]%R
  = 
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_Sc P)[X'] in
  (((1%R)%:E - 
  (\X_Sc P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
  Proof.
    rewrite -complementary_specialized_AS /=.
    set X' := bool_trial_value AS.
    set mu := 'E_(\X_Sc P)[X'].
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
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (expR (-(fine mu * deltaAs ^+ 2) / 3)%R)%:E)%E
    <=
    (\X_Sc P)
      [set i | X' i < (1 + deltaAs) * fine mu]%R)%E.
    Proof.
      rewrite /=.
      
      have H1:= (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
      rewrite complementary_AS_bound /=.
      rewrite /= in H1.
      set X' := bool_trial_value AS.
      set mu := 'E_(\X_Sc P)[X'].
      rewrite /mu -leeN2 in H1.
      rewrite /mu.
      by apply : leeD2l H1.
    Qed.
    
    
  Section ChainQuality.
  
    Variable (N : GlobalState).
    Hypothesis N_from_initial : N0 ⇓ N.
    Hypothesis N_forging_free : forging_free N.
    Hypothesis N_collision_free : collision_free N.
    
    Variable (p : Party).
    Hypothesis p_is_honest : is_honest p.
    
    Variable (l : LocalState).
    
    Hypothesis p_has_state_l: has_state p N l.
   
   
    Variable (b_i b_j : Block).
    Variable (c : Chain).
    Hypothesis interval_is_fragment_of_best :
    fragment ([:: b_j] ++ c ++ [:: b_i]) (bestChain ((t_now N)-1)%N (tree l)).
    
    
    Lemma tuple_sub_size {X : Type} (a b : nat) (t : Sc.-tuple X) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    size (take (b - a)%N (drop a (tval t))) == (b - a)%N.
    Proof.
      apply/eqP.
      rewrite size_take size_drop size_tuple.
      apply: minn_idPl.
      rewrite leq_sub2r //=.
    Qed.



    Lemma tuple_interval_index_try {X : Type} (a b n : nat) (t : n.-tuple X) (Hab : (a<b)%N) (Hb : (b <= n)%N) :
    size (drop a (take b (tval t))) == (b-a)%N.
    Proof.
      apply/eqP.
      rewrite size_drop size_take size_tuple.
      rewrite -/(minn b n). 
      by rewrite (minn_idPl Hb).
    Qed.
    
    Definition tuple_interval_index_fun ( a b n : nat) (t : n.-tuple T)
    (Hab : (a<b)%N) (Hb : (b <= n)%N) : ((b-a)%N).-tuple T :=
    Tuple (tuple_interval_index_try t Hab Hb).
     
    
    Definition LS_sub (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) : ((b-a)%N).-tuple (bernoulliRV P pLs) :=
    Tuple (tuple_sub_size  LS Hab Hb).
    
    Hypothesis Ls_r_range_link : forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N ) (r : Sc.-tuple T),
    bool_trial_value (LS_sub Hab Hb) (@tuple_interval_index_fun a b Sc r Hab Hb ) = (| lucky_slots_range a b |%:R )%N.
    

    Definition AS_sub (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) : ((b-a)%N).-tuple (bernoulliRV P pAs) :=
    Tuple (tuple_sub_size AS Hab Hb).

    Hypothesis As_r_range_link : forall a b (Hab : (a<b)%N) (Hb : (b <= Sc)%N) (r : Sc.-tuple T),
    bool_trial_value (AS_sub Hab Hb) (@tuple_interval_index_fun a b Sc r Hab Hb) = (| adv_slots_range a b |%:R)%N.
 
    About minn_idPl.
    Print honest_advantage_ranges_gt.
    

    Hypothesis delta_choice : (1 + deltaAs) * pAs < (1 - deltaLs) * pLs.
  

    Definition LS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
    let X' := bool_trial_value (LS_sub Hab Hb) in
    let muLS := 'E_(\X_(b-a)%N P)[X'] in
    [set r | (1 - deltaLs) * fine muLS < X' r].
    
    Definition AS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
    let X' := bool_trial_value (AS_sub Hab Hb) in
    let muAS := 'E_(\X_(b-a)%N P)[X'] in
    [set r | (1 + deltaAs) * fine muAS > X' r].
    
    
    Definition CQ_good_event (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
    (LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ  Hab Hb).
    
    Definition CQ_try_good w d := 
    [set r : Sc.-tuple T | honest_advantage_ranges_gt w d].
    
    
    Definition TCQ_good_event  w := ((w - 1)%N <= | honest_blocks ([:: b_j] ++ c ++ [:: b_i])|%N)%N.
    
    Definition TCQ_good_event_set w := 
    [set r : Sc.-tuple T | ((w - 1)%N <= | honest_blocks ([:: b_j] ++ c ++ [:: b_i])|%N)%N].
    
    Print honest_advantage_ranges_gt.
    
    
    

    Definition CQ_all_intervals_good w d :=
    [set i : Sc.-tuple T | forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
     (d <= (b - a))%N 
     ->( | adv_slots_range a b | + w <= | lucky_slots_range a b | )%N ].
     

    
      
      
      
               

    Lemma LS_measurable_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) : 
    measurable (LS_good_event_CQ Hab Hb).
    Proof.
      rewrite /LS_good_event_CQ.
      set X' := bool_trial_value (LS_sub Hab Hb).
      set muLS := 'E_(\X_(b - a) P)[X'].
      set B := (1 - deltaLs) * fine muLS.
      rewrite set_lt_eq_neg_le.
      apply : measurableC.
      rewrite -(ST_Set [set r |  X' r <= B]).
      apply: (measurable_fun_le (D := setT) (f := X' ) (g := fun _ => B)).
      - apply : measurableT.
      - rewrite //=.
      rewrite //=.
    Qed.


    
    
    Lemma AS_measurable_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N): 
    measurable (AS_good_event_CQ Hab Hb).
    Proof.
      rewrite /AS_good_event_CQ.
      set X' := bool_trial_value (AS_sub Hab Hb).
      set muAS := 'E_(\X_(b - a) P)[X']. 
      set B := (1 + deltaAs) * fine muAS.
      have Hcomp : 
      [set r | X' r < B] = [set r | ~~ (B <= X' r)].
      {
        apply /seteqP.
        split.
        - move => r //= Hr ; by rewrite -ltNge.
        move => r //= Hr. by rewrite -ltNge in Hr.
      } 
      rewrite Hcomp.
      have HsetNcomp :
      [set r | ~~ (B <= X' r)] = ~` [set r | B <= X' r].
      {
        apply /seteqP.
        split.
        - move => r Hr.
          rewrite //=.
          rewrite //= in Hr.
          move /negP in Hr.
          apply : Hr.
         - move => r Hr.
           rewrite //=.
           rewrite //= in Hr.
           move /negP in Hr.
           apply Hr.
        }
          
        rewrite  HsetNcomp.
        apply measurableC.
        rewrite -(ST_Set ([set r | B <= X' r])). 
      apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := X')).
    -  by apply: measurableT.
    - rewrite  //=.
    rewrite //=.
Qed.
    



    
    Lemma LS_gt_AS (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N): 
    let XLS := bool_trial_value (LS_sub Hab Hb) in
    let XAS := bool_trial_value (AS_sub Hab Hb) in
    let muLS := 'E_(\X_(b-a) P)[XLS] in
    let muAS := 'E_(\X_(b-a) P)[XAS] in
    (1+deltaAs) * fine muAS < (1 - deltaLs) * fine muLS
    ->
    forall r,
    (1+deltaAs) * fine muAS > AS_r r  ->
    ((1-deltaLs) * fine muLS) < LS_r r->
    (LS_r r > AS_r r).
    Proof.
      cbv zeta.
      move => H r HAS HLS.
      apply: (lt_trans HAS).
      apply: (lt_trans H).
      apply HLS.
    Qed.
    
    Lemma epsilon_condition_CQ :
    (1 - deltaLs) * (pAs + epsilon) >
    (1 + deltaAs) * pAs <->
    epsilon > (((1 + deltaAs) / (1 - deltaLs)) - 1) * pAs.
    Proof.
      split.
        - move => H.
          rewrite (mulrC (1 - deltaLs) (pAs + epsilon) ) in H.
          rewrite -(ltr_pdivrMr (pAs + epsilon)) in H.
          rewrite (mulrC (1 + deltaAs)) in H.
          rewrite (mulrC pAs) in H.
          rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaLs)^-1))  mulrA.
          apply : H.
          rewrite subr_gt0.
          move/andP : delta_range_Ls => [H1 H2].
          apply H2.
      move => H.
      rewrite (mulrC (1 - deltaLs) (pAs + epsilon) ).
      rewrite -(ltr_pdivrMr (pAs + epsilon)) .
      rewrite (mulrC (1 + deltaAs)).
      rewrite (mulrC pAs).
      rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaLs)^-1))  mulrA in H.
      apply : H.
      rewrite subr_gt0.
      move/andP : delta_range_Ls => [H1 H2].
      apply H2.
    Qed.
    
    
    Lemma union_bound_LS_AS_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
    (\X_(b-a) P) ((LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ Hab Hb))
    =
    (1%R%:E - (\X_(b-a) P) ((~` (LS_good_event_CQ Hab Hb)) `|` (~` (AS_good_event_CQ Hab Hb))))%E.
    Proof.
    rewrite -probability_setC.
    - congr ((\X_(b-a) P) _).
      apply /seteqP.
      split.
      + move => r [Hl Hr].
        move => [Hll | Hrr].
        + rewrite //=.
        rewrite //=.
      + move => r H.
        split.
        * apply : Classical_Prop.NNPP => HLS.
          apply : H.
          by left.
        apply : Classical_Prop.NNPP => HAS.
        apply : H.
        by right.
    - apply : measurableU.
      + apply measurableC.
        apply LS_measurable_good_event_CQ.
       apply measurableC.
       apply AS_measurable_good_event_CQ.
    Qed.


    Lemma E_LS_gt_E_AS (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) : 
    let XLS' := bool_trial_value (LS_sub Hab Hb) in
    let muLS := 'E_(\X_(b - a) P)[XLS'] in
    let XAS' := bool_trial_value (AS_sub Hab Hb) in
    let muAS := 'E_(\X_(b - a) P)[XAS'] in
    (1 + deltaAs) * fine muAS < (1 - deltaLs) * fine muLS.
    Proof.
      cbv zeta.
      repeat rewrite expectation_bernoulli_trial.
      rewrite /=.
      repeat rewrite mulrA.
      rewrite mulrC.
      rewrite mulrA.
      rewrite (mulrC ((1 - deltaLs) * (b-a)%:R) pLs).
      rewrite mulrA.
      rewrite ltr_pM2r.
      rewrite mulrC.
      by rewrite (mulrC pLs).
      Search "sub2r".
      apply ltn_sub2r with (p := a) in Hab.
      rewrite /= in Hab.
      rewrite subnn in Hab.
      Search ((_ < _)%N -> (_ < _)%R).
      rewrite ltr0n.
      apply Hab.
      apply Hab.
      apply pLs01.
      apply pAs01.
    Qed.
      
      
      
      
    Lemma bad_event_union_bound_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) : 
    ((\X_(b - a)%N P) ((~` LS_good_event_CQ Hab Hb) `|` (~` AS_good_event_CQ Hab Hb))%E
    <=
    ((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) + ((\X_(b - a)%N P) (~` AS_good_event_CQ Hab Hb)))%E.
    Proof.
      apply : measureU2 ; apply : measurableC.
      - apply : LS_measurable_good_event_CQ.
      apply : AS_measurable_good_event_CQ.
    Qed.

    Lemma bad_event_chernoff_bound (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :
    let XLS' := bool_trial_value (LS_sub Hab Hb)  in
    let muLS := 'E_(\X_(b-a)%N P)[XLS'] in
    let XAS' := bool_trial_value (AS_sub Hab Hb) in
    let muAS := 'E_(\X_(b-a)%N P)[XAS'] in
     
    (((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) +
     ((\X_(b - a)%N P) (~` AS_good_event_CQ Hab Hb))
    <=
    (((expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E) +
     ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E)%E.
    Proof.
      cbv zeta.
      set XLS' := (bool_trial_value (LS_sub Hab Hb)).
      set muLS := 'E_(\X_(b-a)%N P)[XLS'].
      set XAS' := (bool_trial_value (AS_sub Hab Hb)).
      set muAS := 'E_(\X_(b-a)%N P)[XAS'].
      
      have HLS :
      (((\X_(b - a) P) (~` LS_good_event_CQ Hab Hb))%E
      <=
      (expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E)%E.
      {
        rewrite /LS_good_event_CQ.
        rewrite -try3.
        apply  (sampling_ineq3 pLs01 (LS_sub Hab Hb) delta_range_Ls).
      }

      have HAS :
      (((\X_(b - a) P) (~` AS_good_event_CQ Hab Hb))%E
      <=
      (expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E)%E.
      {
        rewrite /AS_good_event_CQ.
        rewrite -try2.
        have Hab' : (a < b)%N. {
          easy.
        }
        apply ltn_sub2r with (p := a) in Hab'.
        rewrite subnn in Hab'.
        rewrite /muAS.
        rewrite /XAS'.
        apply  (sampling_ineq2 pAs01 (AS_sub Hab Hb) Hab' delta_range_As).
        apply Hab'.
      }
      
      Search ((?a <= ?b)%E -> (?c<=?d)%E ->_).
      apply (leeD HLS HAS).
    Qed.
      
      
      
      
      
    Theorem CQ_good_event_lower_bound (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
    let XLS' := bool_trial_value (LS_sub Hab Hb)  in
    let muLS := 'E_(\X_(b-a)%N P)[XLS'] in
    let XAS' := bool_trial_value (AS_sub Hab Hb) in
    let muAS := 'E_(\X_(b-a)%N P)[XAS'] in
    ((1%R%:E - 
    ((expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E) -
    ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E
    <=
    (\X_(b-a)%N P) (CQ_good_event Hab Hb))%E.
    Proof.
      rewrite union_bound_LS_AS_CQ.
      About sube_eq.
      set U := (\X_(b-a)%N P) (~` LS_good_event_CQ Hab Hb `|` ~` AS_good_event_CQ Hab Hb).
      cbv zeta.
      rewrite -addeA.
      rewrite leeD2l.
      - by []. 
      rewrite /U.
      rewrite -oppeD.
      - rewrite leeN2.
        apply (le_trans (bad_event_union_bound_CQ Hab Hb)).
        rewrite leeD.
           + by [].
          rewrite /LS_good_event_CQ.
          apply: (le_trans _ (sampling_ineq3 pLs01 (LS_sub Hab Hb) delta_range_Ls)).
          apply : le_measure.
          * rewrite inE.
            rewrite -try3.
            rewrite -(ST_Set ([set r | bool_trial_value (LS_sub Hab Hb) r <= (1 - deltaLs) * fine 'E_(\X_(b-a)%N P)[(bool_trial_value (LS_sub Hab Hb)) ] ] ) ).
            apply: (measurable_fun_le (D := setT)).
            -- apply : measurableT.
            -- rewrite //=.
            rewrite //=.
          * rewrite inE.
            rewrite -(ST_Set ([set i | bool_trial_value (LS_sub Hab Hb) i <= (1 - deltaLs) * fine 'E_(\X_(b-a)%N P)[(bool_trial_value (LS_sub Hab Hb))] ] ) ).
            apply: (measurable_fun_le (D := setT)).
            -- apply : measurableT.
            -- rewrite //=.
            rewrite //=.
          move => r Hr.
          rewrite -try3 in Hr.
          exact: Hr.
      rewrite /AS_good_event_CQ.
      rewrite -try2.
      have Haltb : (a < b  )%N.
      { 
        apply Hab. 
      }
      have H0ltab : (0 < b - a)%N.
      {
        Search "ltn_sub2r".
        apply ltn_sub2r with (p:=a) in Haltb.
        rewrite subnn in Haltb.
        apply Haltb.
        apply Hab.
      }
      apply (sampling_ineq2 pAs01 (AS_sub Hab Hb) H0ltab delta_range_As).
      rewrite //=.
    Qed.
    
    
    Lemma CQ_bound_on_all_intervalls_implies_CQ_all_intervals_good w ds :
    forall (r : Sc.-tuple T) ,((forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N) ,  (CQ_good_event Hab Hb) (tuple_interval_index_fun r Hab Hb)) ->
               (CQ_all_intervals_good w ds) r).
    Proof.
      move => r H a b Hab Hb HCQINTERVAL.
      rewrite /CQ_good_event in H.
      rewrite /LS_good_event_CQ /AS_good_event_CQ  in  H.
      specialize (H a b Hab Hb).
      set XLS := bool_trial_value (LS_sub Hab Hb).
      set XAS := bool_trial_value (AS_sub Hab Hb).
      set muLS := 'E_(\X_(b-a) P)[XLS].
      set muAS := 'E_(\X_(b-a) P)[XAS].
      destruct H as [HLS HAS].
      rewrite -/XLS in HLS.
      rewrite -/muLS in HLS.
      rewrite //= in HLS.
      rewrite -/XLS.
      have XLSSIMP : (\sum_(i < b - a) Tnth (real_of_bool (LS_sub Hab Hb)) i) = bool_trial_value (LS_sub Hab Hb).
      {
        rewrite //=.
      }
      rewrite XLSSIMP in HLS.
      rewrite Ls_r_range_link in HLS.
      rewrite -/XAS in HAS.
      rewrite -/muAS in HAS.
      rewrite //= in HAS.
      rewrite -/XAS.
      have XASSIMP : (\sum_(i < b - a) Tnth (real_of_bool (AS_sub Hab Hb)) i) = bool_trial_value (AS_sub Hab Hb).
      {
        rewrite //=.
      }
      rewrite XASSIMP in HAS.
      rewrite As_r_range_link in HAS.
      have HT1: (((| adv_slots_range a b |)%:R) : R) < (| lucky_slots_range a b |)%:R.
      {
        About lt_trans.
        have HT2 : (1 + deltaAs) * fine muAS < (| lucky_slots_range a b |)%:R.
        {
          apply (lt_trans (E_LS_gt_E_AS Hab Hb) HLS).
        }
        
        apply  (lt_trans HAS HT2 ).
      }
      
    Lemma CQ_on_all_intervalls_implies 
    
(*   
    Nombre de tuples entre 
    (0,1,1) (0,1,2,3) (0,1,2,3,4) (0,1,2,3,4,5) (0,1,2,3,4,5,6)
1-t 3       4         5           6             7
    
2-t 2       3         4           5             6
    
3-t 1       2         3           4             5                    n-2
    
4-t 0       1         2           3             4                    n3
    
5-t 0       0         1           2             3                    n-4
                                                
                                                2
                                                
                                                1


Nombre de tuples de taille (x <= taille du tuple de base)

(n - (n - 1) = 1
+
(n - (n - 2) = 2
+
(n - (n - 3) = 3
+
(n - (n - 4) = 4
+
.
.
.
+
(n - (n - n)) = n


n(n-1) / 2 
*)



    
    
    
    
    
    (*
    
    Lemma CQ_good_event_implies_honest_advantage_bi_bj :
    forall r , CQ_good_event r -> honest_advantage_range 1 (sl b_j) ((sl b_i) + 1).
    Proof.
      move => r HCQ.
      rewrite /CQ_good_event /LS_good_event_CQ /AS_good_event_CQ in HCQ.
      set muLs := 'E_(\X_Sc P)[(bool_trial_value LS)].
      set muAs := 'E_(\X_Sc P)[(bool_trial_value AS)].
      rewrite -/muLs in HCQ.
      rewrite -/muAs in HCQ.
      rewrite /= in HCQ.
      rewrite /honest_advantage_range.
      case : HCQ => HLS HAS.
      rewrite LS_r_link_Bi_Bj_interval in HLS.
      rewrite AS_r_link_Bi_Bj_interval in HAS.
      apply (lt_trans E_LS_gt_E_AS) in HLS.
      apply (lt_trans HAS) in HLS.
      rewrite addn1. 
      by rewrite -(ltr_nat R).
    Qed.
    
    Theorem CQ_good_event_implies_TCQ :
    forall w r, CQ_good_event r -> TCQ_good_event_set w r.
    Proof.
      move => w r H.
      rewrite /TCQ_good_event_set.
      rewrite //=.
      apply (chain_quality 
               N_from_initial 
               N_forging_free 
               N_collision_free 
               p_has_state_l 
               p_is_honest 
               interval_is_fragment_of_best).
      rewrite /CQ_good_event  in H.
      rewrite //= in H.
      rewrite /LS_good_event_CQ /AS_good_event_CQ in H.
      set muLs := 'E_(\X_Sc P)[(bool_trial_value LS)].
      set muAs := 'E_(\X_Sc P)[(bool_trial_value AS)].
      rewrite -/muLs in H.
      rewrite -/muAs in H.
      rewrite //= in H.
      rewrite LS_r_link_Bi_Bj_interval in H.
      rewrite AS_r_link_Bi_Bj_interval in H.
      case : H => HLS HAS.
      rewrite /honest_advantage_ranges_gt.
      move => /(_ (sl b_j)).
      move => a b Hab.
      rewrite /honest_advantage_range.
      
      Abort.
       
    *)
    End ChainQuality.
    
    
    
   
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
  
  Section CommonPrefix.
    

    Lemma SS_gt_2AS : 
    let XSS := bool_trial_value SS in
    let XAS := bool_trial_value AS in
    let muSS := 'E_(\X_Sc P)[XSS] in
    let muAS := 'E_(\X_Sc P)[XAS] in
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
        rewrite  ltr_wpMn2r.
        - rewrite //=.
        - rewrite //=.
        apply H11.
      }
      apply: (lt_trans H112T).
      apply: (lt_trans H1).
      apply H12.
    Qed.




    Lemma epsilon_condition_CP :
    (1 - deltaSs) * ((pAs *+ 2) + epsilon) >
    (1 + deltaAs) * (pAs *+ 2) <->
    epsilon > (((1 + deltaAs) / (1 - deltaSs)) - 1) * (pAs *+ 2).
    Proof.
      split.
      - move => H.
        rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon) ) in H.
        rewrite -(ltr_pdivrMr (pAs *+ 2 + epsilon)) in H.
        rewrite (mulrC (1 + deltaAs)) in H.
        rewrite (mulrC (pAs *+ 2)) in H.
        rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaSs)^-1))  mulrA.
        apply H.
        rewrite subr_gt0.
        move/andP : delta_range_Ss => [H1 H2].
        apply H2.
      move => H.
      rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon) ).
      rewrite -(ltr_pdivrMr (pAs *+ 2 + epsilon)).
      rewrite (mulrC (1 + deltaAs)).
      rewrite (mulrC (pAs *+ 2)).
      rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaSs)^-1))  mulrA in H.
      apply H.
      rewrite subr_gt0.
      move/andP : delta_range_Ss => [H1 H2].
      apply H2.
    Qed.
    
  Definition SS_good_event := 
  let X' := bool_trial_value SS in
  let muSS := 'E_(\X_Sc P)[X'] in
  [set r | (1 - deltaSs) * fine muSS < X' r].
   
   
  Lemma SS_measurable_good_event_CP : 
  measurable SS_good_event.
  Proof.
    set X' := bool_trial_value SS.
    set muSS := 'E_(\X_Sc P)[X'].
    rewrite /SS_good_event. 
    rewrite -/X'.
    rewrite -/muSS.
    set B := (1 - deltaSs) * fine muSS.
    rewrite set_lt_eq_neg_le.
    apply : measurableC.
    rewrite -(ST_Set [set r |  X' r <= B]).
    apply: (measurable_fun_le (D := setT) (f := X' ) (g := fun _ => B)).
    - apply : measurableT.
    - rewrite //=.
    rewrite //=.
Qed.
  

  Definition AS_good_event_CP := 
  let X' := bool_trial_value AS in
  let muAS := 'E_(\X_Sc P)[X'] in
  [set r | (1 + deltaAs) * fine muAS > X' r].

  Lemma AS_measurable_good_event_CP : 
    measurable AS_good_event_CP.
    Proof.
      set X' := bool_trial_value AS.
      set muAS := 'E_(\X_Sc P)[X'].
      rewrite /AS_good_event_CP. 
      rewrite -/X'.
      rewrite -/muAS.
      set B := (1 + deltaAs) * fine muAS.
      have Hcomp : 
      [set r | X' r < B] = [set r | ~~ (B <= X' r)].
      {
        apply /seteqP.
        split.
        - move => r //= Hr ; by rewrite -ltNge.
        move => r //= Hr. by rewrite -ltNge in Hr.
      } 
      rewrite Hcomp.
      have HsetNcomp :
      [set r | ~~ (B <= X' r)] = ~` [set r | B <= X' r].
      {
        apply /seteqP.
        split.
        - move => r Hr.
          rewrite //=.
          rewrite //= in Hr.
          move /negP in Hr.
          apply : Hr.
         - move => r Hr.
           rewrite //=.
           rewrite //= in Hr.
           move /negP in Hr.
           apply Hr.
        }
          
        rewrite  HsetNcomp.
        apply measurableC.
        rewrite -(ST_Set ([set r | B <= X' r])). 
      apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := X')).
    -  by apply: measurableT.
    - rewrite  //=.
    rewrite //=.
Qed.
    
  
  Definition CP_good_event := 
  SS_good_event `&` AS_good_event_CP.

  Lemma union_bound_SS_AS_CP :
  (\X_Sc P) (SS_good_event `&` AS_good_event_CP)
  =
  (1%R%:E - (\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP)))%E.
  Proof.
  rewrite -probability_setC.
  - congr ((\X_Sc P) _).
    apply /seteqP.
    split.
    + move => r [Hl Hr].
      move => [Hll | Hrr].
      + rewrite //=.
      rewrite //=.
    + move => r H.
      split.
      * apply : Classical_Prop.NNPP => HSS.
        apply : H.
        by left.
      apply : Classical_Prop.NNPP => HAS.
      apply : H.
      by right.
  - apply : measurableU.
    + apply measurableC.
      apply SS_measurable_good_event_CP.
     apply measurableC.
     apply AS_measurable_good_event_CP.
  Qed. 
  
  Variables (N N' : GlobalState).
  Hypothesis N_from_initial : N0 ⇓ N .
  Hypothesis N'_from_N :  N ⇓^+ N'.
  Hypothesis N'_is_forgin_free : forging_free N'.
  Hypothesis N'_is_collision_free : collision_free N'.
    

  (*party assumptions corresponding to CG assumptions for now*)
  Variables (p1 p2 : Party).
  Hypothesis p1_honest : is_honest p1.
  Hypothesis p2_honest : is_honest p2.

  (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
  Variable (l1 l2 : LocalState).
  Hypothesis l1_p1_state : has_state p1 N l1.
  Hypothesis l2_p2_state : has_state p2 N' l2.
  
  
  Variables (k : nat).
  Variables (N1 N2 : GlobalState).
  Variables (t1 t2 : nat).

  Hypothesis Ht1 : (t1 <= k)%N.
  Hypothesis Ht2 : (t_now N1 <= t2 <= t_now N2)%N.
  
  Hypothesis SS_slots_fixed_interval : forall r,  (SS_r r = |super_slots_range (t1 + 1)%N (t2 - 1)%N|%:R)%N.
   Hypothesis AS_slots_fixed_interval : forall r,  (AS_r r = |adv_slots_range (t1 + 1)%N (t2 - 1)%N|%:R)%N.
  
  Definition TCP_Good_event k : Prop:=  
  prune_time k (bestChain (t_now N - 1)%N (tree l1)) ⪯ bestChain (t_now N' - 1 )%N (tree l2).
  
  
  
  Lemma bad_event_union_bound_CP : 
  ((\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP))%E
   <=
  ((\X_Sc P) (~` SS_good_event)) + ((\X_Sc P) (~` AS_good_event_CP)))%E.
  Proof.
    apply : measureU2 ; apply : measurableC.
    - apply : SS_measurable_good_event_CP.
    apply : AS_measurable_good_event_CP.
  Qed.
  
  
  
  Theorem CP_good_event_lower_bound :
  let XSS' := bool_trial_value SS in
  let muSS := 'E_(\X_Sc P)[XSS'] in
  let XAS' := bool_trial_value AS in
  let muAS := 'E_(\X_Sc P)[XAS'] in
  ((1%R%:E - 
  ((expR (-(fine muSS * deltaSs ^+ 2) / 2)%R)%:E) -
  ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E
  <=
  (\X_Sc P) CP_good_event)%E.
  Proof.
  rewrite union_bound_SS_AS_CP.
  About sube_eq.
  set U := (\X_Sc P) (~` SS_good_event `|` ~` AS_good_event_CP).
  cbv zeta.
  rewrite -addeA.
  rewrite leeD2l.
  - by []. 
  rewrite /U.
  rewrite -oppeD.
  - rewrite leeN2.
    apply (le_trans bad_event_union_bound_CP).
    rewrite leeD.
       + by [].
      rewrite /SS_good_event.
      apply: (le_trans _ (sampling_ineq3 pSs01 SS delta_range_Ss)).
      apply : le_measure.
      * rewrite inE.
        rewrite -try3.
        rewrite -(ST_Set ([set r | bool_trial_value SS r <= (1 - deltaSs) * fine 'E_(\X_Sc P)[(bool_trial_value SS) ] ] ) ).
        apply: (measurable_fun_le (D := setT)).
        -- apply : measurableT.
        -- rewrite //=.
        rewrite //=.
      * rewrite inE.
        rewrite -(ST_Set ([set i | bool_trial_value SS i <= (1 - deltaSs) * fine 'E_(\X_Sc P)[(bool_trial_value SS)] ] ) ).
        apply: (measurable_fun_le (D := setT)).
        -- apply : measurableT.
        -- rewrite //=.
        rewrite //=.
      move => r Hr.
      rewrite -try3 in Hr.
      exact: Hr.
  rewrite /AS_good_event_CP.
  rewrite -try2.
  apply (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
  rewrite //=.
  Qed.
   
  Lemma CP_good_event_implies_TCP_good_event :
   CP_good_event -> TCP_Good_event k .
  Proof. 
    move => H.
    rewrite /TCP_Good_event.
    rewrite /CP_good_event in H.
    apply timed_common_prefix' with (p1 := p1) (p2 := p2) ; try easy.
    move => t1' t2'.
    move => Ht1k HNt2N'.
    
    Abort.

    
  
  
  
  End CommonPrefix.
End pos_proof.  














    
     
    


  




