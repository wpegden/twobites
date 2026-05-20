import Tablet.ClosedPairsBound
import Tablet.FixedSetClosedPredicateBoundary
import Tablet.FixedSetHugeOppositeWitnessTouched
import Tablet.FixedSetStagedOpenOppositeWitnessLMS
import Tablet.FixedSetRedFinalGraphOppositeWitness
import Tablet.FixedSetBlueFinalGraphOppositeWitness
import Tablet.LargeClosedPairsBound
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteXPlus
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteX
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetExceptionalWitnessClassification]

theorem FixedSetExceptionalWitnessClassification :
    ∀ {n m k : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n)),
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) →
      I.card = k →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
      let T := TwoBiteStagedOpenPairs ω ε I
      let present : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
        fun e =>
          match e with
          | Sum.inl q => (TwoBiteRedGraph ω).Adj q.1 q.2
          | Sum.inr q => (TwoBiteBlueGraph ω).Adj q.1 q.2
      let lms : TwoBiteBaseVertex m → Prop :=
        fun x =>
          TwoBiteLargeClass ω ε I x ∨
            TwoBiteMediumClass ω ε I x ∨
              TwoBiteSmallClass ω ε I x
      let redExceptional : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
        fun e =>
          match e with
          | Sum.inl q =>
              ∃ b : Fin m,
                lms (Sum.inr b) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inr b)).image
                        (TwoBiteRedProjection ω))
          | Sum.inr _ => False
      let blueExceptional : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
        fun e =>
          match e with
          | Sum.inl _ => False
          | Sum.inr q =>
              ∃ r : Fin m,
                lms (Sum.inl r) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inl r)).image
                        (TwoBiteBlueProjection ω))
      ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        (∀ e, e ∈ ER ↔ e ∈ T ∧ redExceptional e) ∧
        (∀ e, e ∈ EB ↔ e ∈ T ∧ blueExceptional e) ∧
        (∀ e, e ∈ T → present e →
          (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) →
            redExceptional e ∨ blueExceptional e) ∧
        ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
        ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) := by
-- BODY
  classical
  intro n m k p ε ε1 ε2 n0 ω I hε1_nonneg hComparisons hn hm hp hIcard hk hRegularity
  let T := TwoBiteStagedOpenPairs ω ε I
  let present : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl q => (TwoBiteRedGraph ω).Adj q.1 q.2
      | Sum.inr q => (TwoBiteBlueGraph ω).Adj q.1 q.2
  let lms : TwoBiteBaseVertex m → Prop :=
    fun x =>
      TwoBiteLargeClass ω ε I x ∨
        TwoBiteMediumClass ω ε I x ∨
          TwoBiteSmallClass ω ε I x
  let redExceptional : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl q =>
          ∃ b : Fin m,
            lms (Sum.inr b) ∧
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inr b)).image
                    (TwoBiteRedProjection ω))
      | Sum.inr _ => False
  let blueExceptional : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl _ => False
      | Sum.inr q =>
          ∃ r : Fin m,
            lms (Sum.inl r) ∧
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inl r)).image
                    (TwoBiteBlueProjection ω))
  let ER : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter redExceptional
  let EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter blueExceptional
  have hER_mem :
      ∀ e, e ∈ ER ↔ e ∈ T ∧ redExceptional e := by
    intro e
    simp [ER]
  have hEB_mem :
      ∀ e, e ∈ EB ↔ e ∈ T ∧ blueExceptional e := by
    intro e
    simp [EB]
  have hFiber : FiberAndDegreeEvent ω ε2 := by
    simpa [TwoBiteRegularityEvent] using hRegularity.1
  have hMediumEvent :
      TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω := by
    simpa [TwoBiteRegularityEvent] using hRegularity.2.1
  have hSmallEvent :
      TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω := by
    simpa [TwoBiteRegularityEvent] using hRegularity.2.2
  have hI_scale :
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n := by
    rw [hIcard, hk]
  have hLargeClosed :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) := by
    have h :=
      LargeClosedPairsBound ω I hComparisons hn hI_scale hFiber
    simpa [hIcard] using h
  have hMediumClosed :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) :=
    hMediumEvent I hIcard
  have hSmallClosed :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) :=
    hSmallEvent I hIcard
  have hTripleClosedBound :
      ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
            ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
        ≤ (3 * ε1) * (k : ℝ) ^ 2 := by
    dsimp [ClosedPairsBound] at hLargeClosed hMediumClosed hSmallClosed
    nlinarith
  let redClassExceptional (cls : TwoBiteBaseVertex m → Prop) :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl q =>
          ∃ b : Fin m,
            cls (Sum.inr b) ∧
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inr b)).image
                    (TwoBiteRedProjection ω))
      | Sum.inr _ => False
  let blueClassExceptional (cls : TwoBiteBaseVertex m → Prop) :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl _ => False
      | Sum.inr q =>
          ∃ r : Fin m,
            cls (Sum.inl r) ∧
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inl r)).image
                    (TwoBiteBlueProjection ω))
  let ERLarge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (redClassExceptional (TwoBiteLargeClass ω ε I))
  let ERMedium : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (redClassExceptional (TwoBiteMediumClass ω ε I))
  let ERSmall : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (redClassExceptional (TwoBiteSmallClass ω ε I))
  let EBLarge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (blueClassExceptional (TwoBiteLargeClass ω ε I))
  let EBMedium : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (blueClassExceptional (TwoBiteMediumClass ω ε I))
  let EBSmall : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    T.filter (blueClassExceptional (TwoBiteSmallClass ω ε I))
  have hRedExceptional_cases :
      ∀ e, redExceptional e →
        redClassExceptional (TwoBiteLargeClass ω ε I) e ∨
          redClassExceptional (TwoBiteMediumClass ω ε I) e ∨
            redClassExceptional (TwoBiteSmallClass ω ε I) e := by
    intro e he
    cases e with
    | inl q =>
        dsimp [redExceptional, lms] at he
        rcases he with ⟨b, hbClass, hq⟩
        rcases hbClass with hbLarge | hbRest
        · exact Or.inl ⟨b, hbLarge, hq⟩
        · rcases hbRest with hbMedium | hbSmall
          · exact Or.inr (Or.inl ⟨b, hbMedium, hq⟩)
          · exact Or.inr (Or.inr ⟨b, hbSmall, hq⟩)
    | inr q =>
        dsimp [redExceptional] at he
  have hBlueExceptional_cases :
      ∀ e, blueExceptional e →
        blueClassExceptional (TwoBiteLargeClass ω ε I) e ∨
          blueClassExceptional (TwoBiteMediumClass ω ε I) e ∨
            blueClassExceptional (TwoBiteSmallClass ω ε I) e := by
    intro e he
    cases e with
    | inl q =>
        dsimp [blueExceptional] at he
    | inr q =>
        dsimp [blueExceptional, lms] at he
        rcases he with ⟨r, hrClass, hq⟩
        rcases hrClass with hrLarge | hrRest
        · exact Or.inl ⟨r, hrLarge, hq⟩
        · rcases hrRest with hrMedium | hrSmall
          · exact Or.inr (Or.inl ⟨r, hrMedium, hq⟩)
          · exact Or.inr (Or.inr ⟨r, hrSmall, hq⟩)
  have hER_subset_class_union :
      ER ⊆ ERLarge ∪ ERMedium ∪ ERSmall := by
    intro e he
    have hpack := (hER_mem e).1 he
    have ht : e ∈ T := hpack.1
    have hred : redExceptional e := hpack.2
    rcases hRedExceptional_cases e hred with hlarge | hrest
    · simp [ERLarge, ht, hlarge]
    · rcases hrest with hmedium | hsmall
      · simp [ERMedium, ht, hmedium]
      · simp [ERSmall, ht, hsmall]
  have hEB_subset_class_union :
      EB ⊆ EBLarge ∪ EBMedium ∪ EBSmall := by
    intro e he
    have hpack := (hEB_mem e).1 he
    have ht : e ∈ T := hpack.1
    have hblue : blueExceptional e := hpack.2
    rcases hBlueExceptional_cases e hblue with hlarge | hrest
    · simp [EBLarge, ht, hlarge]
    · rcases hrest with hmedium | hsmall
      · simp [EBMedium, ht, hmedium]
      · simp [EBSmall, ht, hsmall]
  have hER_card_le_class_union :
      ER.card ≤ ERLarge.card + ERMedium.card + ERSmall.card := by
    have hsub :
        ER.card ≤ (ERLarge ∪ ERMedium ∪ ERSmall).card :=
      Finset.card_le_card hER_subset_class_union
    have hunion₁ :
        (ERLarge ∪ ERMedium ∪ ERSmall).card ≤
          (ERLarge ∪ ERMedium).card + ERSmall.card :=
      Finset.card_union_le (ERLarge ∪ ERMedium) ERSmall
    have hunion₂ :
        (ERLarge ∪ ERMedium).card ≤ ERLarge.card + ERMedium.card :=
      Finset.card_union_le ERLarge ERMedium
    omega
  have hEB_card_le_class_union :
      EB.card ≤ EBLarge.card + EBMedium.card + EBSmall.card := by
    have hsub :
        EB.card ≤ (EBLarge ∪ EBMedium ∪ EBSmall).card :=
      Finset.card_le_card hEB_subset_class_union
    have hunion₁ :
        (EBLarge ∪ EBMedium ∪ EBSmall).card ≤
          (EBLarge ∪ EBMedium).card + EBSmall.card :=
      Finset.card_union_le (EBLarge ∪ EBMedium) EBSmall
    have hunion₂ :
        (EBLarge ∪ EBMedium).card ≤ EBLarge.card + EBMedium.card :=
      Finset.card_union_le EBLarge EBMedium
    omega
  have hProjectedPair_has_final_pair :
      ∀ (proj : Fin n → Fin m) (X : Finset (Fin n)) (q : Fin m × Fin m),
        q ∈ TwoBiteBasePairs (X.image proj) →
          ∃ a : Fin n × Fin n,
            a ∈ TwoBiteFinalPairs X ∧
              ((proj a.1 = q.1 ∧ proj a.2 = q.2) ∨
                (proj a.1 = q.2 ∧ proj a.2 = q.1)) := by
    intro proj X q hq
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq
    rcases hq with ⟨⟨hq1, hq2⟩, hqrank⟩
    rcases hq1 with ⟨u, huX, huproj⟩
    rcases hq2 with ⟨v, hvX, hvproj⟩
    have huv_ne : u ≠ v := by
      intro huv
      have hqeq : q.1 = q.2 := by
        calc
          q.1 = proj u := huproj.symm
          _ = proj v := by rw [huv]
          _ = q.2 := hvproj
      rw [hqeq] at hqrank
      exact (lt_irrefl q.2) hqrank
    by_cases huv_rank : u.val < v.val
    · refine ⟨(u, v), ?_, Or.inl ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, huX, hvX] using huv_rank
      · exact ⟨huproj, hvproj⟩
    · have hval_ne : u.val ≠ v.val := by
        intro hval
        exact huv_ne (Fin.ext hval)
      have hvu_rank : v.val < u.val := by
        have hle : v.val ≤ u.val := Nat.le_of_not_gt huv_rank
        exact lt_of_le_of_ne hle (Ne.symm hval_ne)
      refine ⟨(v, u), ?_, Or.inr ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, hvX, huX] using hvu_rank
      · exact ⟨hvproj, huproj⟩
  have hRedClass_card_le_closed :
      ∀ cls : TwoBiteBaseVertex m → Prop,
        (T.filter (redClassExceptional cls)).card ≤
          (TwoBiteClosedPairsInClass ω I cls).card := by
    intro cls
    let S : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      T.filter (redClassExceptional cls)
    let Fcls : Finset (Fin n × Fin n) :=
      TwoBiteClosedPairsInClass ω I cls
    let redPairOfFinal : Fin n × Fin n →
        Sum (Fin m × Fin m) (Fin m × Fin m) :=
      fun a =>
        if (TwoBiteRedProjection ω a.1).val <
            (TwoBiteRedProjection ω a.2).val then
          Sum.inl (TwoBiteRedProjection ω a.1, TwoBiteRedProjection ω a.2)
        else
          Sum.inl (TwoBiteRedProjection ω a.2, TwoBiteRedProjection ω a.1)
    have hsubset : S ⊆ Fcls.image redPairOfFinal := by
      intro e he
      have hpred : redClassExceptional cls e := (Finset.mem_filter.mp he).2
      cases e with
      | inl q =>
          dsimp [redClassExceptional] at hpred
          rcases hpred with ⟨b, hbcls, hq⟩
          rcases hProjectedPair_has_final_pair (TwoBiteRedProjection ω)
              (TwoBiteX ω I (Sum.inr b)) q hq with
            ⟨a, haFinal, hproj⟩
          have haClosed : a ∈ Fcls := by
            dsimp [Fcls, TwoBiteClosedPairsInClass]
            rw [Finset.mem_biUnion]
            exact ⟨Sum.inr b, by simp [hbcls], haFinal⟩
          rw [Finset.mem_image]
          refine ⟨a, haClosed, ?_⟩
          have hqrank : q.1.val < q.2.val := by
            have hq' := hq
            simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq'
            exact hq'.2
          rcases hproj with hdir | hrev
          · have hif :
                (TwoBiteRedProjection ω a.1).val <
                  (TwoBiteRedProjection ω a.2).val := by
              simpa [hdir.1, hdir.2] using hqrank
            change
              (if (TwoBiteRedProjection ω a.1).val <
                    (TwoBiteRedProjection ω a.2).val then
                  Sum.inl (TwoBiteRedProjection ω a.1,
                    TwoBiteRedProjection ω a.2)
                else
                  Sum.inl (TwoBiteRedProjection ω a.2,
                    TwoBiteRedProjection ω a.1)) = Sum.inl q
            rw [if_pos hif]
            simp [hdir.1, hdir.2]
          · have hif :
                ¬ (TwoBiteRedProjection ω a.1).val <
                  (TwoBiteRedProjection ω a.2).val := by
              have hnot : ¬ q.2.val < q.1.val :=
                not_lt.mpr (le_of_lt hqrank)
              simpa [hrev.1, hrev.2] using hnot
            change
              (if (TwoBiteRedProjection ω a.1).val <
                    (TwoBiteRedProjection ω a.2).val then
                  Sum.inl (TwoBiteRedProjection ω a.1,
                    TwoBiteRedProjection ω a.2)
                else
                  Sum.inl (TwoBiteRedProjection ω a.2,
                    TwoBiteRedProjection ω a.1)) = Sum.inl q
            rw [if_neg hif]
            simp [hrev.1, hrev.2]
      | inr q =>
          dsimp [redClassExceptional] at hpred
    have hcard_subset : S.card ≤ (Fcls.image redPairOfFinal).card :=
      Finset.card_le_card hsubset
    have himage_card : (Fcls.image redPairOfFinal).card ≤ Fcls.card :=
      Finset.card_image_le
    simpa [S, Fcls] using le_trans hcard_subset himage_card
  have hBlueClass_card_le_closed :
      ∀ cls : TwoBiteBaseVertex m → Prop,
        (T.filter (blueClassExceptional cls)).card ≤
          (TwoBiteClosedPairsInClass ω I cls).card := by
    intro cls
    let S : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      T.filter (blueClassExceptional cls)
    let Fcls : Finset (Fin n × Fin n) :=
      TwoBiteClosedPairsInClass ω I cls
    let bluePairOfFinal : Fin n × Fin n →
        Sum (Fin m × Fin m) (Fin m × Fin m) :=
      fun a =>
        if (TwoBiteBlueProjection ω a.1).val <
            (TwoBiteBlueProjection ω a.2).val then
          Sum.inr (TwoBiteBlueProjection ω a.1, TwoBiteBlueProjection ω a.2)
        else
          Sum.inr (TwoBiteBlueProjection ω a.2, TwoBiteBlueProjection ω a.1)
    have hsubset : S ⊆ Fcls.image bluePairOfFinal := by
      intro e he
      have hpred : blueClassExceptional cls e := (Finset.mem_filter.mp he).2
      cases e with
      | inl q =>
          dsimp [blueClassExceptional] at hpred
      | inr q =>
          dsimp [blueClassExceptional] at hpred
          rcases hpred with ⟨r, hrcls, hq⟩
          rcases hProjectedPair_has_final_pair (TwoBiteBlueProjection ω)
              (TwoBiteX ω I (Sum.inl r)) q hq with
            ⟨a, haFinal, hproj⟩
          have haClosed : a ∈ Fcls := by
            dsimp [Fcls, TwoBiteClosedPairsInClass]
            rw [Finset.mem_biUnion]
            exact ⟨Sum.inl r, by simp [hrcls], haFinal⟩
          rw [Finset.mem_image]
          refine ⟨a, haClosed, ?_⟩
          have hqrank : q.1.val < q.2.val := by
            have hq' := hq
            simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq'
            exact hq'.2
          rcases hproj with hdir | hrev
          · have hif :
                (TwoBiteBlueProjection ω a.1).val <
                  (TwoBiteBlueProjection ω a.2).val := by
              simpa [hdir.1, hdir.2] using hqrank
            change
              (if (TwoBiteBlueProjection ω a.1).val <
                    (TwoBiteBlueProjection ω a.2).val then
                  Sum.inr (TwoBiteBlueProjection ω a.1,
                    TwoBiteBlueProjection ω a.2)
                else
                  Sum.inr (TwoBiteBlueProjection ω a.2,
                    TwoBiteBlueProjection ω a.1)) = Sum.inr q
            rw [if_pos hif]
            simp [hdir.1, hdir.2]
          · have hif :
                ¬ (TwoBiteBlueProjection ω a.1).val <
                  (TwoBiteBlueProjection ω a.2).val := by
              have hnot : ¬ q.2.val < q.1.val :=
                not_lt.mpr (le_of_lt hqrank)
              simpa [hrev.1, hrev.2] using hnot
            change
              (if (TwoBiteBlueProjection ω a.1).val <
                    (TwoBiteBlueProjection ω a.2).val then
                  Sum.inr (TwoBiteBlueProjection ω a.1,
                    TwoBiteBlueProjection ω a.2)
                else
                  Sum.inr (TwoBiteBlueProjection ω a.2,
                    TwoBiteBlueProjection ω a.1)) = Sum.inr q
            rw [if_neg hif]
            simp [hrev.1, hrev.2]
    have hcard_subset : S.card ≤ (Fcls.image bluePairOfFinal).card :=
      Finset.card_le_card hsubset
    have himage_card : (Fcls.image bluePairOfFinal).card ≤ Fcls.card :=
      Finset.card_image_le
    simpa [S, Fcls] using le_trans hcard_subset himage_card
  have hER_count_by_classes :
      (ER.card : ℝ) ≤
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
            ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) := by
    have hclassCover :
        (ER.card : ℝ) ≤
          (ERLarge.card : ℝ) + (ERMedium.card : ℝ) + (ERSmall.card : ℝ) := by
      exact_mod_cast hER_card_le_class_union
    have hLarge :
        (ERLarge.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [ERLarge] using
            hRedClass_card_le_closed (TwoBiteLargeClass ω ε I))
    have hMedium :
        (ERMedium.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [ERMedium] using
            hRedClass_card_le_closed (TwoBiteMediumClass ω ε I))
    have hSmall :
        (ERSmall.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [ERSmall] using
            hRedClass_card_le_closed (TwoBiteSmallClass ω ε I))
    nlinarith
  have hEB_count_by_classes :
      (EB.card : ℝ) ≤
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
            ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) := by
    have hclassCover :
        (EB.card : ℝ) ≤
          (EBLarge.card : ℝ) + (EBMedium.card : ℝ) + (EBSmall.card : ℝ) := by
      exact_mod_cast hEB_card_le_class_union
    have hLarge :
        (EBLarge.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [EBLarge] using
            hBlueClass_card_le_closed (TwoBiteLargeClass ω ε I))
    have hMedium :
        (EBMedium.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [EBMedium] using
            hBlueClass_card_le_closed (TwoBiteMediumClass ω ε I))
    have hSmall :
        (EBSmall.card : ℝ) ≤
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) := by
      exact_mod_cast
        (by
          simpa [EBSmall] using
            hBlueClass_card_le_closed (TwoBiteSmallClass ω ε I))
    nlinarith
  refine ⟨ER, EB, hER_mem, hEB_mem, ?classification, ?redBound, ?blueBound⟩
  · intro e heT hpresent hIndep
    have hOppLMS :=
      FixedSetStagedOpenOppositeWitnessLMS (n := n) (m := m) (p := p)
        (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0)
        ω I hComparisons hn hm hp hI_scale hFiber
    cases e with
    | inl q =>
        left
        have hOppWitness :
            ∃ b : Fin m,
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inr b)).image
                    (TwoBiteRedProjection ω)) := by
          exact FixedSetRedFinalGraphOppositeWitness ω I q heT hpresent hIndep
        simpa [redExceptional, lms] using hOppLMS.1 q heT hOppWitness
    | inr q =>
        right
        have hOppWitness :
            ∃ r : Fin m,
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ω I (Sum.inl r)).image
                    (TwoBiteBlueProjection ω)) := by
          exact FixedSetBlueFinalGraphOppositeWitness ω I q heT hpresent hIndep
        simpa [blueExceptional, lms] using hOppLMS.2 q heT hOppWitness
  · dsimp [ClosedPairsBound]
    exact le_trans hER_count_by_classes hTripleClosedBound
  · dsimp [ClosedPairsBound]
    exact le_trans hEB_count_by_classes hTripleClosedBound
