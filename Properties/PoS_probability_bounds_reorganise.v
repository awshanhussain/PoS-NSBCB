From mathcomp Require Import
  all_ssreflect ssralg poly ssrnum ssrint interval finmap
  mathcomp_extra boolp classical_sets functions cardinality fsbigop.

From mathcomp Require Import (canonicals) Rstruct.
From mathcomp Require Import
  reals ereal interval_inference topology normedtype sequences realfun
  convex real_interval derive esum measure exp numfun lebesgue_measure
  measurable_realfun lebesgue_integral kernel probability hoelder unstable
  archimedean.

Require Reals Interval.Tactic.
From HB Require Import structures.

From AUChain Require Import
  sampling Rstruct_topology Network Protocol GlobalState Blocks Messages
  MessageTuple Parameters BlockTree Schedule LocalState MemEq SsrFacts
  TreeChain CG CP CQ additional_lemmas.

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

Section PoSProbabilityBounds.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope schedule_scope.

Let R := Rdefinitions.R.
Context {d} (T : measurableType d) (P : probability T R).

(* -------------------------------------------------------------------- *)
(* Shared probabilistic model                                            *)
(* -------------------------------------------------------------------- *)

Variable Sc : nat.
Hypothesis n_sup_O : (0 < Sc)%N.

Variable pLs pSs pAs : R.
Hypothesis pLs01 : (0 <= pLs <= 1)%R.
Hypothesis pSs01 : (0 <= pSs <= 1)%R.
Hypothesis pAs01 : (0 <= pAs <= 1)%R.

Variable LS : Sc.-tuple (bernoulliRV P pLs).
Variable SS : Sc.-tuple (bernoulliRV P pSs).
Variable AS : Sc.-tuple (bernoulliRV P pAs).

Definition LS_r := bool_trial_value LS.
Definition SS_r := bool_trial_value SS.
Definition AS_r := bool_trial_value AS.

Variable deltaLs deltaSs deltaAs : R.
Hypothesis delta_range_Ls : (0 < deltaLs < 1)%R.
Hypothesis delta_range_Ss : (0 < deltaSs < 1)%R.
Hypothesis delta_range_As : (0 < deltaAs < 1)%R.

(* -------------------------------------------------------------------- *)
(* Tuple utilities                                                       *)
(* -------------------------------------------------------------------- *)

Definition tuple_interval_index {T : Type} (a b n : nat) (t : n.-tuple T) :=
      drop a (take b t).

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

Lemma Sc_pos_R : (0 < (Sc%:R : R))%R.
Proof.
        by rewrite ltr0n.
Qed.

(* -------------------------------------------------------------------- *)
(* Shared interval tuples                                               *)
(* -------------------------------------------------------------------- *)

Definition LS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pLs) :=
  Tuple (tuple_sub_size LS Hab Hb).

Definition SS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pSs) :=
  Tuple (tuple_sub_size SS Hab Hb).

Definition AS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pAs) :=
  Tuple (tuple_sub_size AS Hab Hb).

(* -------------------------------------------------------------------- *)
(* Shared Chernoff/complement bounds                                     *)
(* -------------------------------------------------------------------- *)

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

(* ==================================================================== *)
(* Chain Growth                                                         *)
(* ==================================================================== *)

      Section ChainGrowth.

      (* Protocol assumptions specific to Chain Growth. *)

      (*GlobalStates assumptions*)
        Variables (N_from_r N'_from_r : Sc.-tuple T -> GlobalState).
      Hypothesis N_from_initial : forall r, N0 ⇓ N_from_r r .
      Hypothesis N_is_ready : forall r, N_from_r r @ Ready.
      Hypothesis N'_from_N :  forall r, N_from_r r  ⇓^+ N'_from_r r.
     
      Search "measurable_fun_le". 



      (*party assumptions corresponding to CG assumptions for now*)
      Variables (p1 p2 : Party).
      Hypothesis p1_honest : is_honest p1.
      Hypothesis p2_honest : is_honest p2.

      (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
      Variable (l1_from_r l2_from_r : Sc.-tuple T -> LocalState).
      Hypothesis l1_p1_state : forall r, has_state p1 (N_from_r r) (l1_from_r r).
      Hypothesis l2_p2_state : forall r, has_state p2 (N'_from_r r)  (l2_from_r r).

      (*Assumption to link the bool_trial_value LS to the amount of lucky slots between N and N'*)
      Hypothesis LS_r_eq_slotrange : forall r, (LS_r r  = | lucky_slots_range (t_now (N_from_r r)) ((t_now (N'_from_r r)) - 1) |%:R)%N.
      Definition Chain_growth_ls_Good_event :=
      let X' := bool_trial_value LS in
      let mu := 'E_(\X_Sc P)[X'] in
      [set r | ((1 - deltaLs) * fine mu < X' r)%R].

      Definition chain_growth_parties_event (w : nat)  :=
      let X' := bool_trial_value LS in
      [set r : Sc.-tuple T | ((|bestChain (t_now (N_from_r r) - 1)%N (tree (l1_from_r r))| + w)%N <= |bestChain (t_now (N'_from_r r) - 1)%N (tree (l2_from_r r))|)%N].

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
      


      (*if you want to make a chain growth event that takes in condiseration a given r, you are in the obligation
      to define functions on Global state and LocalState that depends on a given r, those functions are abstract
      , meaning that no mater what we won't be apple to prove they are measurable*)
      Hypothesis chain_growth_parties_event_measurable :
      forall w : nat,
      measurable (chain_growth_parties_event w).

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
        rewrite  //=. 
        rewrite inE.
        apply chain_growth_parties_event_measurable.
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

(* ==================================================================== *)
(* Chain Quality                                                        *)
(* ==================================================================== *)

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

      Variable (w_cq : nat) (r_cq : Sc.-tuple T).

      (* Links between the probabilistic samples and protocol slot counts. *)
      Hypothesis Ls_r_range_link :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          bool_trial_value (LS_sub Hab Hb)
            (tuple_interval_index_fun r_cq Hab Hb)
          = | lucky_slots_range a b |%:R.

      Hypothesis As_r_range_link :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          bool_trial_value (AS_sub Hab Hb)
            (tuple_interval_index_fun r_cq Hab Hb)
          = | adv_slots_range a b |%:R.

      Variable epsilon : R.

      Variable (ds : nat).
      Hypothesis w_cq_bound :
      forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
      (ds <= b - a)%N ->
      ((1 + deltaAs) * fine 'E_(\X_(b-a) P)[bool_trial_value (AS_sub Hab Hb)] + w_cq%:R
      <=
      (1 - deltaLs) * fine 'E_(\X_(b-a) P)[bool_trial_value (LS_sub Hab Hb)])%R.

      Hypotheses w_cq_gt_0 : (w_cq > 0)%N.
      

      (*there is enough lucky slots*)
      Definition LS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
      let X' := bool_trial_value (LS_sub Hab Hb) in
      let muLS := 'E_(\X_(b-a)%N P)[X'] in
      [set r | (1 - deltaLs) * fine muLS < X' r].
     

      (* there is a satisfying number of adversarial slots*)
      Definition AS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
      let X' := bool_trial_value (AS_sub Hab Hb) in
      let muAS := 'E_(\X_(b-a)%N P)[X'] in
      [set r | (1 + deltaAs) * fine muAS > X' r].
      

      
      Definition CQ_good_event (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
      (LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ  Hab Hb).
      

      (*there a number of lucky slot greater than expected and a number of adversarial slots 
      lower than expected probabilisticly on every interval [a,b] of slots greater than ds*)
    
      Definition CQ_interval_event (ds a b : nat) :=
      match boolP (a <b)%N with
      | AltTrue Hab =>
        match boolP (b <= Sc)%N with
        | AltTrue Hb =>
          if (ds <= (b - a)%N)%N then [set r | CQ_good_event Hab Hb (@tuple_interval_index_fun a b Sc r Hab Hb)]
          else setT
        | _ => setT
        end
      | _ => setT
      end.

       
      (* same as CQ_good_event_on_all_subset but under the form of a set which makes us able to apply 
         probabilities to it *) 
      Definition CQ_all_intervals_good (d : nat) (a b : nat) : set (Sc.-tuple T) :=
        match boolP (a < b)%N with
          | AltTrue Hab => match boolP (b <= Sc)%N  with
                             | AltTrue Hb => match boolP (d <= b - a)%N with
                                               | AltTrue Hdba => [set r : Sc.-tuple T | CQ_good_event Hab Hb (tuple_interval_index_fun r Hab Hb)]
                                               | _ => setT
                                              end
                             | _ => setT
                             end
          | _ => setT
          end.

      Definition CQ_slot_advantage (w d : nat) : Prop :=
      forall (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
      (d <= b - a)%N
      -> ((| adv_slots_range  a b| + w) <= | lucky_slots_range a b |)%N.





        Lemma CQ_good_interval_implies_advantage (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) (Hsize : (ds <= b - a)%N) :
        CQ_good_event Hab Hb (@tuple_interval_index_fun a b Sc r_cq Hab Hb)
        -> ((| adv_slots_range  a b| + w_cq) <= | lucky_slots_range a b |)%N.
        Proof.
          move => HGE.
          
          rewrite /CQ_good_event /LS_good_event_CQ /AS_good_event_CQ //= As_r_range_link Ls_r_range_link in HGE.
          move : HGE => [HLS HAS].

          have Hw := w_cq_bound Hab Hb Hsize.

          rewrite -(ler_nat R) natrD.

          rewrite //= in Hw.
          
          set muAS := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool (AS_sub Hab Hb)) i)].
          set muLS := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool (LS_sub Hab Hb)) i)].
          rewrite -/muAS -/muLS in Hw.
          rewrite -/muAS in HAS.
          rewrite -/muLS in HLS. 
          have Htrans1 := le_lt_trans Hw HLS.
          have HASw : (| adv_slots_range a b |)%:R + w_cq%:R < (1 + deltaAs) * muAS + w_cq%:R.
          {
            by rewrite ltrD2r.
          }

          

          have htrans3 := lt_trans HASw Htrans1.
          Search  "ltW".
          by apply ltW in htrans3.
          
        Qed.  

        Lemma CQ_all_intervals_good_implies_advantage : 
        (forall a b, CQ_all_intervals_good ds a b r_cq) -> CQ_slot_advantage w_cq ds.
        Proof.
          move => HAIG.
          rewrite /CQ_slot_advantage.
          move => a0 b0 Hab Hb Hds.
          rewrite /CQ_all_intervals_good in HAIG.
          specialize (HAIG a0 b0).
          destruct (boolP (a0 < b0)%N) as [Hab' | Hnab'].
            - destruct (boolP (b0 <= Sc)%N) as [Hb' | Hnb'].
              + destruct (boolP (ds <= b0 - a0)%N) as [Hds' | Hnds']. 
                * rewrite /= in HAIG.
                  have Habs : Hab = Hab'.
                  {
                    rewrite //=.
                  }
                  have Hbs : Hb = Hb'.
                  {
                    rewrite //=.
                  }
                  apply (@CQ_good_interval_implies_advantage a0 b0 Hab Hb Hds).
                  by rewrite Habs Hbs.
                
                * by rewrite /negb Hds in Hnds'.
              + by rewrite /negb Hb in Hnb'.
            - by rewrite /negb Hab in Hnab'.
          Qed.

        Lemma measurable_tuple_interval_index_fun
            (a b : nat)
            (Hab : (a < b)%N)
            (Hb : (b <= Sc)%N) :
          measurable_fun [set: Sc.-tuple T]
            (fun r : Sc.-tuple T =>
              tuple_interval_index_fun r Hab Hb).
        Proof.
          apply/measurable_fun_tnthP => i.
          destruct i. 
          
          have ty : (a + m < b)%N. {
           Check ltn_subRL.  
           by rewrite -ltn_subRL.
          }
          

          have HSc_ai := ltn_leq_trans ty Hb.
          rewrite /comp /=.
          
          pose j : 'I_Sc := @Ordinal Sc (a + m) HSc_ai.
          
          rewrite /tuple_interval_index_fun /=.

          have Hcoord (x : Sc.-tuple T) :
          tnth (Tuple (tuple_interval_index_try x Hab Hb)) (Ordinal i)
          =
          tnth x j.
          {
            rewrite [LHS](tnth_nth (tnth x j)) /=. 
            rewrite nth_drop.
            rewrite nth_take.
            change (nth (tnth x j) (tval x) (val j) = tnth x j).
            

            exact: esym (tnth_nth (tnth x j) x j).
            exact : ty.
          }


                    

          have Hfun :
              (fun x : Sc.-tuple T =>
                tnth (Tuple (tuple_interval_index_try x Hab Hb)) (Ordinal i))
              =
              (fun x : Sc.-tuple T => tnth x j).
          {
            apply/funext => x.
            exact: Hcoord x.
          }

          rewrite Hfun. 
        



        

          exact: measurable_tnth.
        Qed.
              
          




           
      






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

      Lemma CQ_good_event_measurable (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
      measurable (CQ_good_event Hab Hb).
      Proof.
        apply measurableI.
        - apply LS_measurable_good_event_CQ.
        apply AS_measurable_good_event_CQ.
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

  (*
      Lemma E_LS_gt_E_AS (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :
      let XLS' := bool_trial_value (LS_sub Hab Hb) in
      let muLS := 'E_(\X_(b - a) P)[XLS'] in
      let XAS' := bool_trial_value (AS_sub Hab Hb) in
      let muAS := 'E_(\X_(b - a) P)[XAS'] in
      (1 + deltaAs) * fine muAS < (1 - deltaLs) * fine muLS.
      Proof.
        cbv zeta.
        repeat rewrite expectation_bernoulli_trial.
        specialize (w_cq_bound Hab Hb).
        have w_cq_bound' :
        (1 + deltaAs) * fine 'E_(\X_(b - a) P)[(bool_trial_value (AS_sub Hab Hb))] + w_cq%:R <=
            (1 - deltaLs) * fine 'E_(\X_(b - a) P)[(bool_trial_value (LS_sub Hab Hb))]. {
              easy.
            }

        repeat rewrite expectation_bernoulli_trial in w_cq_bound'.
        rewrite /=.
        repeat rewrite mulrA.
        rewrite mulrC.
        rewrite mulrA.
        rewrite (mulrC ((1 - deltaLs) * (b-a)%:R) pLs).
        rewrite mulrA.
        rewrite ltr_pM2r.
        rewrite mulrC.
        rewrite (mulrC pLs).
        have Hab' : (a<b)%N.
        {
          easy.
        }
        apply ltn_sub2r with (p := a) in Hab'.
        rewrite /= in Hab'.
        rewrite subnn in Hab'.
        rewrite ltr0n.
        apply Hab.
        apply Hab.
        apply pLs01.
        apply pAs01.
      Qed.
    *)

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
        have Haltb : (a < b)%N.
        {
          apply Hab.
        }
        have H0ltab : (0 < b - a)%N.
        {
          apply ltn_sub2r with (p:=a) in Haltb.
          rewrite subnn in Haltb.
          apply Haltb.
          apply Hab.
        }
        apply (sampling_ineq2 pAs01 (AS_sub Hab Hb) H0ltab delta_range_As).
        rewrite //=.
      Qed.
      (*
      Lemma CQ_bound_on_all_intervalls_implies_CQ_all_intervals :
      ((forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N) ,  (CQ_good_event Hab Hb) (tuple_interval_index_fun r_cq Hab Hb)) ->
                 (CQ_all_intervals_good w_cq ds) r_cq).
      Proof.
        move =>  H a b Hab Hb HCQINTERVAL.
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
        have Hw := w_cq_bound (a := a) (b := b) Hab Hb.
        have Hw' := Hw HCQINTERVAL.
        rewrite -/muAS -/muLS in Hw'.
        rewrite -(ler_nat R) natrD.
        have HASw :
        ((| adv_slots_range a b |)%:R + w_cq%:R
        <=
        (1 + deltaAs) * fine muAS + w_cq%:R)%R.
        {
          rewrite lerD2r.
          exact : ltW HAS.
        }
        apply (le_trans HASw).
        apply (le_trans Hw').
        exact (ltW HLS).
      Qed.
       *)
      Fixpoint number_of_sub_tuples (n : nat) :nat :=
      match n with
      | 0 => 0
      | n'.+1 => (number_of_sub_tuples n') + n'.+1
      end.

      Lemma number_of_sub_tuples_is_sum :
      forall n , number_of_sub_tuples n = \sum_(0<= i < n.+1 ) i.
      Proof.
        move => n.
        elim  n => [|n' IHn'].
        - rewrite //= big_nat1 //=.
        rewrite big_nat_recr //=.
        rewrite IHn' //=.
      Qed.

       

        Lemma measurable_all_intervals_good (d' : nat) : 
        forall a b , measurable (CQ_all_intervals_good d' a b).
        Proof.
          move => a b.
          rewrite /CQ_all_intervals_good.
          destruct (boolP (a < b)%N) as [Hab' | Hnab'].
            - destruct (boolP (b <= Sc)%N) as [Hb' | Hnb'].
              + destruct (boolP (d' <= b - a)%N) as [Hdab' | Hndab'].
                * Search "measurable" .
                  Search (measurable [set _ | ?D ?i]).
                  have Hfun := measurable_tuple_interval_index_fun Hab' Hb'.
                  have Hgood_event := CQ_good_event_measurable Hab' Hb'.
                  have Hpre := Hfun measurableT (CQ_good_event Hab' Hb') Hgood_event.
                  rewrite setTI  in Hpre.
                  apply Hpre. 
                * exact : measurableT.
              + exact : measurableT.
            - exact : measurableT.
        Qed.
 
      Lemma measurable_CQ_good_event_all_subset (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
      forall d , measurable (CQ_good_event_on_all_subset d a b).
      Proof.
        move => d0.
        rewrite /CQ_good_event_on_all_subset.
        destruct (boolP ( a < b)%N) as [HabT | HabF].
        - destruct (boolP (b <= Sc)%N) as [HbT | HbF].
          + destruct (d0 <= b - a)%N .
            * have : (  measurable_fun [set: Sc.-tuple T] (fun r => tuple_interval_index_fun r HabT HbT)).
                {
                  apply/measurable_fun_tnthP => i.

                  Admitted.

      Lemma Probability_CQ_on_all_intervall_gt_than_CQ_good_event :
      forall  a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N) , ((\X_Sc P) (CQ_good_event_on_all_subset ds)
      <=
      (\X_Sc P) ((CQ_all_intervals_good w_cq ds)))%E.
      Proof.
        move => a b Hab Hb.

         
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

(* ==================================================================== *)
(* Common Prefix                                                        *)
(* ==================================================================== *)

    Section CommonPrefix.

      Variable epsilon : R.

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
        have Hcomp :
        [set r | X' r < B] = [set r | ~~ (B <= X' r)].
        {
          apply /seteqP.
          split.
          - move => r //= Hr ; by rewrite -ltNge.
          move => r //= Hr. by rewrite -ltNge in Hr.
        }
        rewrite //=.
       
  Qed.
    
    Definition AS_good_event_CP :=
    let X' := bool_trial_value AS in
    let muAS := 'E_(\X_Sc P)[X'] in
    [set r | (1 + deltaAs) * fine  muAS > X' r].


    Lemma AS_measurable_good_event_CP :
    measurable AS_good_event_CP.
     
         Proof.
        rewrite /AS_good_event_CP.
        set X' := bool_trial_value AS.
        set muAS := 'E_(\X_Sc P)[X'].
        set B := (1 + deltaAs) * fine muAS.
        rewrite -/B.
        have Hcomp :
        [set r | X' r < B] = [set r | ~~ (B <= X' r)].
        {
          apply /seteqP.
          split.
          - move => r //= Hr ; by rewrite -ltNge.
          move => r //= Hr. by rewrite -ltNge in Hr.
        }
        rewrite -/B.
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
    Hypothesis N'_now_is_Sc : (t_now N' = Sc)%N.
    (*party assumptions corresponding to CG assumptions for now*)
    Variables (p1 p2 : Party).
    Hypothesis p1_honest : is_honest p1.
    Hypothesis p2_honest : is_honest p2.

    (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
    Variable (l1 l2 : LocalState).
    Hypothesis l1_p1_state : has_state p1 N l1.
    Hypothesis l2_p2_state : has_state p2 N' l2.
     
    Variables (k : nat).

    (* ------------------------------------------------------------------ *)
    (* Interval model used by timed common prefix                          *)
    (* ------------------------------------------------------------------ *)
    
    Lemma b_le_t_now_N2_implies_b_le_SC (b : nat): 
      (b <= t_now N')%N -> (b <= Sc)%N.
    Proof.
      move => HTN.
      by rewrite N'_now_is_Sc in HTN.
    Qed.

    Search ((?a <= ?b)%N -> (?a - 1 <= ?b)%N).

    Lemma sub1_leq (a b : nat):
      (a <= b)%N -> ((a - 1) <= b)%N.
    Proof.
      move => H. 
      have Ha : ((a - 1) <= a)%N.
      {
        apply  (leq_subr 1 (a)).
      }
      apply (leq_trans Ha H).
    Qed.
      

    
    Hypothesis Ss_r_range_link :
      forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
             (r : Sc.-tuple T),
        bool_trial_value (SS_sub Hab Hb)
          (tuple_interval_index_fun r Hab Hb)
        = | super_slots_range a b |%:R.

    Hypothesis As_r_range_link_CP :
      forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
             (r : Sc.-tuple T),
        bool_trial_value (AS_sub Hab Hb)
          (tuple_interval_index_fun r Hab Hb)
        = | adv_slots_range a b |%:R.

    Definition CP_good_event_interval
       (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :=
      [set r : Sc.-tuple T |
        ((bool_trial_value (AS_sub Hab Hb)
            (tuple_interval_index_fun r Hab Hb)) *+ 2
         < bool_trial_value (SS_sub Hab Hb)
            (tuple_interval_index_fun r Hab Hb))%R].
    


    Definition CP_good_event_interval' (a b : nat)  :=
    match boolP (a < b)%N with
    | AltTrue Hab => match boolP (b <= Sc)%N with
                     | AltTrue Hb => CP_good_event_interval Hab Hb 
                     | _ => setT
                     end
    | _ => setT
    end.



    Definition interval_advantage_CP (a b : nat) : Prop :=
      ((((| adv_slots_range a b |)%:R : R) *+ 2
          < ((| super_slots_range a b |)%:R : R)))%R.
    

    Definition CP_good_event_set : set (Sc.-tuple T) :=
      [set r : Sc.-tuple T |
        forall (t1 t2 : nat) 
               (Htk : (t1 <= k)%N) 
               (Ht2 : (t_now N <= t2 <= t_now N')%N) 
               (Ht1t2 : ((t1 + 1) < (t2 - 1))%N)
               (Ht2Sc : ((t2 - 1) <= Sc)%N) , 
          
               CP_good_event_interval Ht1t2 Ht2Sc   r
          ].
    Lemma CP_good_interval_implies_advantage (a b : nat) (r : Sc.-tuple T) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    CP_good_event_interval Hab Hb r -> interval_advantage_CP a b.
    Proof. 
      move => H.
      rewrite /interval_advantage_CP.
      rewrite -(Ss_r_range_link Hab Hb r) -(As_r_range_link_CP Hab Hb r).  
      rewrite /CP_good_event_interval //= in H.
    Qed. 

    
    
    Definition TCP_Good_event k : Prop:=
    prune_time k (bestChain (t_now N - 1)%N (tree l1)) ⪯ bestChain (t_now N' - 1 )%N (tree l2).
    
    Lemma CP_good_event_implies_TCP (r : Sc.-tuple T) :
    CP_good_event_set r -> TCP_Good_event k.
    Proof.
      move => H.
      apply  timed_common_prefix' with (p1 := p1) (p2 := p2) ; try easy.
      rewrite /CP_good_event_set //= in H.
      move => t0 t3 Ht0 Ht3.
     
      

      have Ht0t3 : ((t0 - 1) < (t3 - 1))%N.
      {
         
      }
      
      have Ht3sc : ((t3 - 1) <= Sc)%N.
      {
        case /andP : Ht3 =>  Ht31 Hr32.
        rewrite N'_now_is_Sc in Hr32.
        have Ht3't3 : (t3 - 1 <= t3)%N.        
        {
          by rewrite sub1_leq.
        }
        apply (leq_trans  Ht3't3 Hr32).
      }
      
      eapply H.
    



    
    Lemma bad_event_union_bound_CP :
    ((\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP))%E
     <=
    ((\X_Sc P) (~` SS_good_event)) + ((\X_Sc P) (~` AS_good_event_CP)))%E.
    Proof.
      apply : measureU2 ; apply : measurableC.
      - apply : SS_measurable_good_event_CP.
      apply : AS_measurable_good_event_CP.
    Qed.
    

    Search ((?a + ?b)%N). 

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

    End CommonPrefix.

End PoSProbabilityBounds.

(* --------------------------------------------------------------------
   Scratch commands belong in a separate temporary file, not in the proof:

   Compute tuple_interval_index 3 6 [:: 1;2;3;4;5;6;7;8;9;10].
   Check (sampling_ineq3 pLs01 LS delta_range_Ls).
   Search (honest_advantage_ranges_gt _ _).
   -------------------------------------------------------------------- *)
