import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.ProjectionOpenPairFunction
import Tablet.LargeClosedPairsBound
import Tablet.HugeProjectionClosedPairsBound
import Tablet.ProjectedPairsInClassMultiplicityBound
import Tablet.TwoBiteProjectedPairSum
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent

-- [TABLET NODE: ProjectionClosedPairCountBound]

set_option maxHeartbeats 1000000 in
theorem ProjectionClosedPairCountBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      TwoBiteMediumClosedPairsEvent (k := I.card) ε ε1 ω →
      TwoBiteSmallClosedPairsEvent (k := I.card) ε ε1 ω →
      ((@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
          (fun e => TwoBiteProjectionPairClosed ω I e)
          (Classical.decPred (fun e => TwoBiteProjectionPairClosed ω I e))
          (TwoBiteProjectionPairSet ω I)).card : ℝ) ≤
        ((TwoBiteProjectionPairSet ω I).card : ℝ) -
          ProjectionOpenPairFunction
            (((I.image (TwoBiteRedProjection ω)).card : ℝ))
            (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
            (I.card : ℝ) p (n : ℝ) +
          9 * ε1 * (I.card : ℝ) ^ 2 := by
-- BODY
  classical
  intro n m p ω I ε ε1 ε2 n0 hε1 hParams hn hm hp hI hFiber hMedium hSmall
  let hugeRed : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
  let hugeBlue : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
  let closedSet : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    @Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
      (fun e => TwoBiteProjectionPairClosed ω I e)
      (Classical.decPred (fun e => TwoBiteProjectionPairClosed ω I e))
      (TwoBiteProjectionPairSet ω I)
  let qSmall : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteProjectedPairsClosedInClass ω I (TwoBiteSmallClass ω ε I)
  let qMedium : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteProjectedPairsClosedInClass ω I (TwoBiteMediumClass ω ε I)
  let qLarge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteProjectedPairsClosedInClass ω I (TwoBiteLargeClass ω ε I)
  let qHuge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteProjectedPairsClosedInClass ω I (TwoBiteHugeClass ω I)
  let redOppTarget : ℝ :=
    min
      (RealChooseTwo ((I.card : ℝ) -
        ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
      (RealChooseTwo (p * (n : ℝ)) +
        RealChooseTwo
          ((I.card : ℝ) -
            ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
              p * (n : ℝ)))
  let blueOppTarget : ℝ :=
    min
      (RealChooseTwo ((I.card : ℝ) -
        ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
      (RealChooseTwo (p * (n : ℝ)) +
        RealChooseTwo
          ((I.card : ℝ) -
            ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
              p * (n : ℝ)))
  have hLarge :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ)
        ε1 (I.card : ℝ) :=
    LargeClosedPairsBound (n := n) (m := m) (p := p) ω
      (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0) I
      hParams hn hI hFiber
  have hHuge :=
    HugeProjectionClosedPairsBound (n := n) (m := m) (k := I.card) (p := p)
      ω I ε ε1 ε2 (n0 := n0)
      hε1 hParams hn hm hp hI rfl hFiber
  have hHugeSame :
      ClosedPairsBound
        (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
        ε1 (I.card : ℝ) := by
    dsimp [hugeRed, hugeBlue] at hHuge ⊢
    exact hHuge.2.2.1
  have hControlled :
      ClosedPairsBound
        (((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)))
        (4 * ε1) (I.card : ℝ) := by
    have hMediumBound :
        ClosedPairsBound
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
          ε1 (I.card : ℝ) :=
      hMedium I rfl
    have hSmallBound :
        ClosedPairsBound
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
          ε1 (I.card : ℝ) :=
      hSmall I rfl
    unfold ClosedPairsBound at hLarge hMediumBound hSmallBound hHugeSame ⊢
    nlinarith
  have hControlled_num :
      (((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)))
        ≤ (4 * ε1) * (I.card : ℝ) ^ 2 := by
    simpa [ClosedPairsBound] using hControlled
  have hHugeExpanded := hHuge
  dsimp [hugeRed, hugeBlue] at hHugeExpanded
  have hHugeOppRed :
      TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) ≤
        (1 + ε1) *
          min
            (RealChooseTwo ((I.card : ℝ) -
              ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
            (RealChooseTwo (p * (n : ℝ)) +
              RealChooseTwo
                ((I.card : ℝ) -
                  ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
                    p * (n : ℝ))) := by
    exact hHugeExpanded.2.2.2.1
  have hHugeOppBlue :
      TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω) ≤
        (1 + ε1) *
          min
            (RealChooseTwo ((I.card : ℝ) -
              ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
            (RealChooseTwo (p * (n : ℝ)) +
              RealChooseTwo
                ((I.card : ℝ) -
                  ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
                    p * (n : ℝ))) := by
    exact hHugeExpanded.2.2.2.2
  have hHugeOppTotal :
      TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω) ≤
        (1 + ε1) * (redOppTarget + blueOppTarget) := by
    dsimp [redOppTarget, blueOppTarget]
    calc
      TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω)
          ≤ (1 + ε1) *
                min
                  (RealChooseTwo ((I.card : ℝ) -
                    ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
                  (RealChooseTwo (p * (n : ℝ)) +
                    RealChooseTwo
                      ((I.card : ℝ) -
                        ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
                          p * (n : ℝ))) +
              (1 + ε1) *
                min
                  (RealChooseTwo ((I.card : ℝ) -
                    ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
                  (RealChooseTwo (p * (n : ℝ)) +
                    RealChooseTwo
                      ((I.card : ℝ) -
                        ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
                          p * (n : ℝ))) := by
            exact add_le_add hHugeOppRed hHugeOppBlue
      _ = (1 + ε1) *
            (min
                (RealChooseTwo ((I.card : ℝ) -
                  ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((I.card : ℝ) -
                      ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
                        p * (n : ℝ))) +
              min
                (RealChooseTwo ((I.card : ℝ) -
                  ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((I.card : ℝ) -
                      ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
                        p * (n : ℝ)))) := by
            ring
  have hOpenPair_algebra :
      RealChooseTwo (((I.image (TwoBiteRedProjection ω)).card : ℝ)) +
          RealChooseTwo (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) -
            ProjectionOpenPairFunction
              (((I.image (TwoBiteRedProjection ω)).card : ℝ))
              (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
              (I.card : ℝ) p (n : ℝ)
        = redOppTarget + blueOppTarget := by
    dsimp [ProjectionOpenPairFunction, redOppTarget, blueOppTarget]
    ring
  have hLargeMultiplicity :
      ((TwoBiteProjectedPairsClosedInClass ω I
          (TwoBiteLargeClass ω ε I)).card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteLargeClass ω ε I)).card : ℝ) :=
    ProjectedPairsInClassMultiplicityBound ω I (TwoBiteLargeClass ω ε I)
  have hMediumMultiplicity :
      ((TwoBiteProjectedPairsClosedInClass ω I
          (TwoBiteMediumClass ω ε I)).card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteMediumClass ω ε I)).card : ℝ) :=
    ProjectedPairsInClassMultiplicityBound ω I (TwoBiteMediumClass ω ε I)
  have hSmallMultiplicity :
      ((TwoBiteProjectedPairsClosedInClass ω I
          (TwoBiteSmallClass ω ε I)).card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteSmallClass ω ε I)).card : ℝ) :=
    ProjectedPairsInClassMultiplicityBound ω I (TwoBiteSmallClass ω ε I)
  have hLargeMultiplicity_q :
      (qLarge.card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteLargeClass ω ε I)).card : ℝ) := by
    simpa [qLarge] using hLargeMultiplicity
  have hMediumMultiplicity_q :
      (qMedium.card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteMediumClass ω ε I)).card : ℝ) := by
    simpa [qMedium] using hMediumMultiplicity
  have hSmallMultiplicity_q :
      (qSmall.card : ℝ) ≤
        2 *
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteSmallClass ω ε I)).card : ℝ) := by
    simpa [qSmall] using hSmallMultiplicity
  have hClassControlled_num :
      (qLarge.card : ℝ) + (qMedium.card : ℝ) + (qSmall.card : ℝ) +
          2 *
            (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
              TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
        ≤ 8 * ε1 * (I.card : ℝ) ^ 2 := by
    nlinarith [hLargeMultiplicity_q, hMediumMultiplicity_q,
      hSmallMultiplicity_q, hControlled_num]
  have hX_subset_I : ∀ x : TwoBiteBaseVertex m, TwoBiteX ω I x ⊆ I := by
    intro x v hv
    simpa [TwoBiteX] using (Finset.mem_filter.mp hv).1
  have hWitnessClass :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteSmallClass ω ε I x ∨
          TwoBiteMediumClass ω ε I x ∨
            TwoBiteLargeClass ω ε I x ∨ TwoBiteHugeClass ω I x := by
    intro x
    have hx_nonneg : 0 ≤ ((TwoBiteX ω I x).card : ℝ) := by
      exact_mod_cast Nat.zero_le (TwoBiteX ω I x).card
    have hx_le_I : ((TwoBiteX ω I x).card : ℝ) ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hX_subset_I x)
    by_cases hsmall : ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteSmallCutoff ε n
    · exact Or.inl ⟨hx_nonneg, hsmall⟩
    · have hsmall_lt :
          TwoBiteSmallCutoff ε n < ((TwoBiteX ω I x).card : ℝ) :=
        lt_of_not_ge hsmall
      by_cases hmedium :
          ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteLargeCutoff ε n
      · exact Or.inr (Or.inl ⟨hsmall_lt, hmedium⟩)
      · have hlarge_lt :
            TwoBiteLargeCutoff ε n < ((TwoBiteX ω I x).card : ℝ) :=
          lt_of_not_ge hmedium
        by_cases hlarge :
            ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteHugeCutoff n
        · exact Or.inr (Or.inr (Or.inl ⟨hlarge_lt, hlarge⟩))
        · have hhuge_lt :
              TwoBiteHugeCutoff n < ((TwoBiteX ω I x).card : ℝ) :=
            lt_of_not_ge hlarge
          exact Or.inr (Or.inr (Or.inr ⟨hhuge_lt, hx_le_I⟩))
  have hClosed_subset_class_union :
      closedSet ⊆ (((qSmall ∪ qMedium) ∪ qLarge) ∪ qHuge) := by
    intro e he
    have heFilter :
        e ∈ @Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
          (fun e => TwoBiteProjectionPairClosed ω I e)
          (Classical.decPred (fun e => TwoBiteProjectionPairClosed ω I e))
          (TwoBiteProjectionPairSet ω I) := by
      simpa [closedSet] using he
    have hePair : e ∈ TwoBiteProjectionPairSet ω I ∧
        TwoBiteProjectionPairClosed ω I e :=
      Finset.mem_filter.mp heFilter
    cases e with
    | inl q =>
        rcases hePair.2 with ⟨x, hxq⟩
        rcases hWitnessClass x with hcls | hcls | hcls | hcls
        · have hmem : Sum.inl q ∈ qSmall := by
            dsimp [qSmall, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl hmem)))))
        · have hmem : Sum.inl q ∈ qMedium := by
            dsimp [qMedium, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))))
        · have hmem : Sum.inl q ∈ qLarge := by
            dsimp [qLarge, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
        · have hmem : Sum.inl q ∈ qHuge := by
            dsimp [qHuge, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr (Or.inr hmem)
    | inr q =>
        rcases hePair.2 with ⟨x, hxq⟩
        rcases hWitnessClass x with hcls | hcls | hcls | hcls
        · have hmem : Sum.inr q ∈ qSmall := by
            dsimp [qSmall, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl hmem)))))
        · have hmem : Sum.inr q ∈ qMedium := by
            dsimp [qMedium, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))))
        · have hmem : Sum.inr q ∈ qLarge := by
            dsimp [qLarge, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
        · have hmem : Sum.inr q ∈ qHuge := by
            dsimp [qHuge, TwoBiteProjectedPairsClosedInClass]
            exact Finset.mem_filter.mpr ⟨hePair.1, ⟨x, hcls, hxq⟩⟩
          exact Finset.mem_union.mpr (Or.inr hmem)
  have hClosed_card_le_class_union :
      (closedSet.card : ℝ) ≤
        (qSmall.card : ℝ) + (qMedium.card : ℝ) +
          (qLarge.card : ℝ) + (qHuge.card : ℝ) := by
    have hclosed_union :
        (closedSet.card : ℝ) ≤
          ((((qSmall ∪ qMedium) ∪ qLarge) ∪ qHuge).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hClosed_subset_class_union
    have h_union_huge :
        (((((qSmall ∪ qMedium) ∪ qLarge) ∪ qHuge).card : ℝ) ≤
          (((qSmall ∪ qMedium) ∪ qLarge).card : ℝ) + (qHuge.card : ℝ)) := by
      exact_mod_cast Finset.card_union_le ((qSmall ∪ qMedium) ∪ qLarge) qHuge
    have h_union_large :
        ((((qSmall ∪ qMedium) ∪ qLarge).card : ℝ) ≤
          ((qSmall ∪ qMedium).card : ℝ) + (qLarge.card : ℝ)) := by
      exact_mod_cast Finset.card_union_le (qSmall ∪ qMedium) qLarge
    have h_union_medium :
        (((qSmall ∪ qMedium).card : ℝ) ≤
          (qSmall.card : ℝ) + (qMedium.card : ℝ)) := by
      exact_mod_cast Finset.card_union_le qSmall qMedium
    linarith
  have hClosed_subset_projection :
      closedSet ⊆ TwoBiteProjectionPairSet ω I :=
    Finset.filter_subset _ _
  have hClosed_le_projection :
      (closedSet.card : ℝ) ≤
        ((TwoBiteProjectionPairSet ω I).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hClosed_subset_projection
  have hBasePairs_choose_bound :
      ∀ {r : ℕ} (X : Finset (Fin r)),
        ((TwoBiteBasePairs X).card : ℝ) ≤ RealChooseTwo (X.card : ℝ) := by
    intro r X
    refine Finset.induction_on X ?base_card_eq ?step_card_eq
    · simp [TwoBiteBasePairs, TwoBitePairsInSet, RealChooseTwo]
    · intro a s ha ih
      let newPairs : Finset (Fin r × Fin r) :=
        (s.filter (fun y => a.val < y.val ∨ y.val < a.val)).image
          (fun y => if a.val < y.val then (a, y) else (y, a))
      have hinsert_subset :
          TwoBiteBasePairs (insert a s) ⊆ TwoBiteBasePairs s ∪ newPairs := by
        intro e he
        rcases e with ⟨u, v⟩
        dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at he ⊢
        simp only [Finset.mem_filter, Finset.mem_product] at he
        rcases he with ⟨⟨hu, hv⟩, huv⟩
        simp only [Finset.mem_union]
        rw [Finset.mem_insert] at hu hv
        rcases hu with rfl | hu_s
        · rcases hv with rfl | hv_s
          · exact False.elim ((Nat.lt_irrefl _) huv)
          · right
            dsimp [newPairs]
            rw [Finset.mem_image]
            refine ⟨v, ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨hv_s, Or.inl huv⟩
            · simp [huv]
        · rcases hv with rfl | hv_s
          · right
            dsimp [newPairs]
            rw [Finset.mem_image]
            refine ⟨u, ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨hu_s, Or.inr huv⟩
            · have hnot : ¬ v.val < u.val :=
                fun hvu => (Nat.lt_asymm hvu) huv
              simp [hnot]
          · left
            dsimp [TwoBiteBasePairs, TwoBitePairsInSet]
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hu_s, hv_s⟩, huv⟩
      have hnew_card_le :
          newPairs.card ≤ s.card := by
        have himage :
            newPairs.card ≤
              (s.filter (fun y => a.val < y.val ∨ y.val < a.val)).card := by
          dsimp [newPairs]
          exact Finset.card_image_le
        exact le_trans himage (Finset.card_le_card (Finset.filter_subset _ _))
      have hcard_step_nat :
          (TwoBiteBasePairs (insert a s)).card ≤
            (TwoBiteBasePairs s).card + s.card := by
        exact le_trans (Finset.card_le_card hinsert_subset)
          (le_trans (Finset.card_union_le (TwoBiteBasePairs s) newPairs)
            (Nat.add_le_add_left hnew_card_le (TwoBiteBasePairs s).card))
      have hcard_step_real :
          ((TwoBiteBasePairs (insert a s)).card : ℝ) ≤
            ((TwoBiteBasePairs s).card : ℝ) + (s.card : ℝ) := by
        exact_mod_cast hcard_step_nat
      have hchoose_insert :
          RealChooseTwo ((insert a s).card : ℝ) =
            RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
        simp [ha, RealChooseTwo]
        ring
      calc
        ((TwoBiteBasePairs (insert a s)).card : ℝ)
            ≤ ((TwoBiteBasePairs s).card : ℝ) + (s.card : ℝ) := hcard_step_real
        _ ≤ RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
          linarith only [ih]
        _ = RealChooseTwo ((insert a s).card : ℝ) := hchoose_insert.symm
  let hugeRedSet : Finset (TwoBiteBaseVertex m) :=
    @Finset.filter (TwoBiteBaseVertex m) hugeRed
      (Classical.decPred hugeRed) (Finset.univ : Finset (TwoBiteBaseVertex m))
  let hugeBlueSet : Finset (TwoBiteBaseVertex m) :=
    @Finset.filter (TwoBiteBaseVertex m) hugeBlue
      (Classical.decPred hugeBlue) (Finset.univ : Finset (TwoBiteBaseVertex m))
  let redSamePairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    hugeRedSet.biUnion (fun x =>
      (TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))).image
        (fun q => (Sum.inl q : Sum (Fin m × Fin m) (Fin m × Fin m))))
  let redOppPairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    hugeRedSet.biUnion (fun x =>
      (TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω))).image
        (fun q => (Sum.inr q : Sum (Fin m × Fin m) (Fin m × Fin m))))
  let blueOppPairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    hugeBlueSet.biUnion (fun x =>
      (TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))).image
        (fun q => (Sum.inl q : Sum (Fin m × Fin m) (Fin m × Fin m))))
  let blueSamePairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    hugeBlueSet.biUnion (fun x =>
      (TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω))).image
        (fun q => (Sum.inr q : Sum (Fin m × Fin m) (Fin m × Fin m))))
  have hQHuge_subset :
      qHuge ⊆ (((redSamePairs ∪ redOppPairs) ∪ blueOppPairs) ∪ blueSamePairs) := by
    intro e he
    have heFilter :
        e ∈ TwoBiteProjectedPairsClosedInClass ω I (TwoBiteHugeClass ω I) := by
      simpa [qHuge] using he
    dsimp [TwoBiteProjectedPairsClosedInClass] at heFilter
    rw [Finset.mem_filter] at heFilter
    rcases heFilter with ⟨_heProjection, heWitness⟩
    cases e with
    | inl q =>
        rcases heWitness with ⟨x, hxHuge, hxq⟩
        cases x with
        | inl r =>
            have hxRed : (Sum.inl r : TwoBiteBaseVertex m) ∈ hugeRedSet := by
              simp [hugeRedSet, hugeRed, hxHuge]
            have hmem : Sum.inl q ∈ redSamePairs := by
              dsimp [redSamePairs]
              rw [Finset.mem_biUnion]
              refine ⟨Sum.inl r, hxRed, ?_⟩
              rw [Finset.mem_image]
              exact ⟨q, hxq, rfl⟩
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr
                (Or.inl (Finset.mem_union.mpr (Or.inl hmem)))))
        | inr b =>
            have hxBlue : (Sum.inr b : TwoBiteBaseVertex m) ∈ hugeBlueSet := by
              simp [hugeBlueSet, hugeBlue, hxHuge]
            have hmem : Sum.inl q ∈ blueOppPairs := by
              dsimp [blueOppPairs]
              rw [Finset.mem_biUnion]
              refine ⟨Sum.inr b, hxBlue, ?_⟩
              rw [Finset.mem_image]
              exact ⟨q, hxq, rfl⟩
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
    | inr q =>
        rcases heWitness with ⟨x, hxHuge, hxq⟩
        cases x with
        | inl r =>
            have hxRed : (Sum.inl r : TwoBiteBaseVertex m) ∈ hugeRedSet := by
              simp [hugeRedSet, hugeRed, hxHuge]
            have hmem : Sum.inr q ∈ redOppPairs := by
              dsimp [redOppPairs]
              rw [Finset.mem_biUnion]
              refine ⟨Sum.inl r, hxRed, ?_⟩
              rw [Finset.mem_image]
              exact ⟨q, hxq, rfl⟩
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr
                (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))))
        | inr b =>
            have hxBlue : (Sum.inr b : TwoBiteBaseVertex m) ∈ hugeBlueSet := by
              simp [hugeBlueSet, hugeBlue, hxHuge]
            have hmem : Sum.inr q ∈ blueSamePairs := by
              dsimp [blueSamePairs]
              rw [Finset.mem_biUnion]
              refine ⟨Sum.inr b, hxBlue, ?_⟩
              rw [Finset.mem_image]
              exact ⟨q, hxq, rfl⟩
            exact Finset.mem_union.mpr (Or.inr hmem)
  have hGenerated_card_le :
      ∀ (A : Finset (TwoBiteBaseVertex m)) (proj : Fin n → Fin m)
        (tag : Fin m × Fin m → Sum (Fin m × Fin m) (Fin m × Fin m)),
        (((A.biUnion (fun x =>
            (TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag)).card : ℝ) ≤
          A.sum (fun x =>
            RealChooseTwo (((TwoBiteX ω I x).image proj).card : ℝ))) := by
    intro A proj tag
    have hbi_nat :
        (A.biUnion (fun x =>
            (TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag)).card ≤
          A.sum (fun x =>
            ((TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag).card) := by
      simpa using
        (Finset.card_biUnion_le (s := A)
          (t := fun x =>
            (TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag))
    have hbi_real :
        (((A.biUnion (fun x =>
            (TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag)).card : ℝ) ≤
          A.sum (fun x =>
            (((TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag).card : ℝ))) := by
      exact_mod_cast hbi_nat
    have hsum_image :
        A.sum (fun x =>
            (((TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).image tag).card : ℝ)) ≤
          A.sum (fun x =>
            ((TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).card : ℝ)) := by
      exact Finset.sum_le_sum (fun x _hx => by
        exact_mod_cast
          (Finset.card_image_le
            (s := TwoBiteBasePairs ((TwoBiteX ω I x).image proj))
            (f := tag)))
    have hsum_choose :
        A.sum (fun x =>
            ((TwoBiteBasePairs ((TwoBiteX ω I x).image proj)).card : ℝ)) ≤
          A.sum (fun x =>
            RealChooseTwo (((TwoBiteX ω I x).image proj).card : ℝ)) := by
      exact Finset.sum_le_sum (fun x _hx =>
        hBasePairs_choose_bound ((TwoBiteX ω I x).image proj))
    exact le_trans hbi_real (le_trans hsum_image hsum_choose)
  have hRedSame_card :
      (redSamePairs.card : ℝ) ≤
        TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) := by
    simpa [redSamePairs, hugeRedSet, TwoBiteProjectedPairSum] using
      hGenerated_card_le hugeRedSet (TwoBiteRedProjection ω)
        (fun q => (Sum.inl q : Sum (Fin m × Fin m) (Fin m × Fin m)))
  have hRedOpp_card :
      (redOppPairs.card : ℝ) ≤
        TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) := by
    simpa [redOppPairs, hugeRedSet, TwoBiteProjectedPairSum] using
      hGenerated_card_le hugeRedSet (TwoBiteBlueProjection ω)
        (fun q => (Sum.inr q : Sum (Fin m × Fin m) (Fin m × Fin m)))
  have hBlueOpp_card :
      (blueOppPairs.card : ℝ) ≤
        TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω) := by
    simpa [blueOppPairs, hugeBlueSet, TwoBiteProjectedPairSum] using
      hGenerated_card_le hugeBlueSet (TwoBiteRedProjection ω)
        (fun q => (Sum.inl q : Sum (Fin m × Fin m) (Fin m × Fin m)))
  have hBlueSame_card :
      (blueSamePairs.card : ℝ) ≤
        TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω) := by
    simpa [blueSamePairs, hugeBlueSet, TwoBiteProjectedPairSum] using
      hGenerated_card_le hugeBlueSet (TwoBiteBlueProjection ω)
        (fun q => (Sum.inr q : Sum (Fin m × Fin m) (Fin m × Fin m)))
  have hQHuge_card_le_union :
      (qHuge.card : ℝ) ≤
        ((((redSamePairs ∪ redOppPairs) ∪ blueOppPairs) ∪ blueSamePairs).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hQHuge_subset
  have hHuge_union_card :
      (((((redSamePairs ∪ redOppPairs) ∪ blueOppPairs) ∪ blueSamePairs).card : ℝ) ≤
        (redSamePairs.card : ℝ) + (redOppPairs.card : ℝ) +
          (blueOppPairs.card : ℝ) + (blueSamePairs.card : ℝ)) := by
    have h_union_blueSame :
        (((((redSamePairs ∪ redOppPairs) ∪ blueOppPairs) ∪ blueSamePairs).card : ℝ) ≤
          (((redSamePairs ∪ redOppPairs) ∪ blueOppPairs).card : ℝ) +
            (blueSamePairs.card : ℝ)) := by
      exact_mod_cast
        Finset.card_union_le ((redSamePairs ∪ redOppPairs) ∪ blueOppPairs)
          blueSamePairs
    have h_union_blueOpp :
        ((((redSamePairs ∪ redOppPairs) ∪ blueOppPairs).card : ℝ) ≤
          ((redSamePairs ∪ redOppPairs).card : ℝ) +
            (blueOppPairs.card : ℝ)) := by
      exact_mod_cast Finset.card_union_le (redSamePairs ∪ redOppPairs)
        blueOppPairs
    have h_union_redOpp :
        (((redSamePairs ∪ redOppPairs).card : ℝ) ≤
          (redSamePairs.card : ℝ) + (redOppPairs.card : ℝ)) := by
      exact_mod_cast Finset.card_union_le redSamePairs redOppPairs
    linarith
  have hQHuge_bound :
      (qHuge.card : ℝ) ≤
        (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)) +
        (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω)) := by
    calc
      (qHuge.card : ℝ)
          ≤ (((((redSamePairs ∪ redOppPairs) ∪ blueOppPairs) ∪ blueSamePairs).card : ℝ)) :=
        hQHuge_card_le_union
      _ ≤ (redSamePairs.card : ℝ) + (redOppPairs.card : ℝ) +
            (blueOppPairs.card : ℝ) + (blueSamePairs.card : ℝ) :=
        hHuge_union_card
      _ ≤ (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω)) := by
        linarith [hRedSame_card, hRedOpp_card, hBlueOpp_card, hBlueSame_card]
  have hBasePairs_card_eq :
      ∀ {r : ℕ} (X : Finset (Fin r)),
        ((TwoBiteBasePairs X).card : ℝ) = RealChooseTwo (X.card : ℝ) := by
    intro r X
    refine Finset.induction_on X ?base ?step
    · simp [TwoBiteBasePairs, TwoBitePairsInSet, RealChooseTwo]
    · intro a s ha ih
      let pairOf : Fin r → Fin r × Fin r :=
        fun y => if a.val < y.val then (a, y) else (y, a)
      let newPairs : Finset (Fin r × Fin r) :=
        (s.filter (fun y => a.val < y.val ∨ y.val < a.val)).image pairOf
      have hpairOf_inj : Function.Injective pairOf := by
        intro y z hyz
        dsimp [pairOf] at hyz
        by_cases hy : a.val < y.val <;> by_cases hz : a.val < z.val
        · have hsnd := congrArg Prod.snd hyz
          simpa [hy, hz] using hsnd
        · have hsnd := congrArg Prod.snd hyz
          have hfst := congrArg Prod.fst hyz
          have hya : y = a := by
            simpa [hy, hz] using hsnd
          have haz : a = z := by
            simpa [hy, hz] using hfst
          exact hya.trans haz
        · have hfst := congrArg Prod.fst hyz
          have hsnd := congrArg Prod.snd hyz
          have hya : y = a := by
            simpa [hy, hz] using hfst
          have haz : a = z := by
            simpa [hy, hz] using hsnd
          exact hya.trans haz
        · have hfst := congrArg Prod.fst hyz
          simpa [hy, hz] using hfst
      have hfilter_eq :
          s.filter (fun y => a.val < y.val ∨ y.val < a.val) = s := by
        ext y
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).1
        · intro hy
          rw [Finset.mem_filter]
          have hne_val : a.val ≠ y.val := by
            intro hval
            have hay : a = y := Fin.ext hval
            exact ha (by simpa [hay] using hy)
          exact ⟨hy, lt_or_gt_of_ne hne_val⟩
      have hnew_card : newPairs.card = s.card := by
        dsimp [newPairs]
        rw [Finset.card_image_of_injective _ hpairOf_inj, hfilter_eq]
      have hinsert_eq :
          TwoBiteBasePairs (insert a s) = TwoBiteBasePairs s ∪ newPairs := by
        ext e
        constructor
        · intro he
          rcases e with ⟨u, v⟩
          dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at he ⊢
          simp only [Finset.mem_filter, Finset.mem_product] at he
          rcases he with ⟨⟨hu, hv⟩, huv⟩
          simp only [Finset.mem_union]
          rw [Finset.mem_insert] at hu hv
          rcases hu with rfl | hu_s
          · rcases hv with rfl | hv_s
            · exact False.elim ((Nat.lt_irrefl _) huv)
            · right
              dsimp [newPairs, pairOf]
              rw [Finset.mem_image]
              refine ⟨v, ?_, ?_⟩
              · rw [Finset.mem_filter]
                exact ⟨hv_s, Or.inl huv⟩
              · simp [huv]
          · rcases hv with rfl | hv_s
            · right
              dsimp [newPairs, pairOf]
              rw [Finset.mem_image]
              refine ⟨u, ?_, ?_⟩
              · rw [Finset.mem_filter]
                exact ⟨hu_s, Or.inr huv⟩
              · have hnot : ¬ v.val < u.val := fun hvu => (Nat.lt_asymm hvu) huv
                simp [hnot]
            · left
              dsimp [TwoBiteBasePairs, TwoBitePairsInSet]
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hu_s, hv_s⟩, huv⟩
        · intro he
          rcases e with ⟨u, v⟩
          rw [Finset.mem_union] at he
          rcases he with hold | hnew
          · dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at hold ⊢
            simp only [Finset.mem_filter, Finset.mem_product] at hold ⊢
            rcases hold with ⟨⟨hu, hv⟩, huv⟩
            exact ⟨⟨Finset.mem_insert.mpr (Or.inr hu),
              Finset.mem_insert.mpr (Or.inr hv)⟩, huv⟩
          · dsimp [newPairs, pairOf] at hnew
            rw [Finset.mem_image] at hnew
            rcases hnew with ⟨y, hyfilter, hye⟩
            rw [Finset.mem_filter] at hyfilter
            rcases hyfilter with ⟨hy_s, hycomp⟩
            by_cases hay : a.val < y.val
            · simp [hay] at hye
              rcases hye with ⟨rfl, rfl⟩
              dsimp [TwoBiteBasePairs, TwoBitePairsInSet]
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨Finset.mem_insert_self _ _,
                Finset.mem_insert.mpr (Or.inr hy_s)⟩, hay⟩
            · simp [hay] at hye
              rcases hye with ⟨rfl, rfl⟩
              have hya : y.val < a.val := by
                rcases hycomp with hlt | hlt
                · exact False.elim (hay hlt)
                · exact hlt
              dsimp [TwoBiteBasePairs, TwoBitePairsInSet]
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨Finset.mem_insert.mpr (Or.inr hy_s),
                Finset.mem_insert_self _ _⟩, hya⟩
      have hdisjoint :
          Disjoint (TwoBiteBasePairs s) newPairs := by
        rw [Finset.disjoint_left]
        intro e hold hnew
        rcases e with ⟨u, v⟩
        dsimp [newPairs, pairOf] at hnew
        rw [Finset.mem_image] at hnew
        rcases hnew with ⟨y, hyfilter, hye⟩
        rw [Finset.mem_filter] at hyfilter
        rcases hyfilter with ⟨_hy_s, _hycomp⟩
        by_cases hay : a.val < y.val
        · simp [hay] at hye
          rcases hye with ⟨rfl, rfl⟩
          dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at hold
          rw [Finset.mem_filter, Finset.mem_product] at hold
          exact ha hold.1.1
        · simp [hay] at hye
          rcases hye with ⟨rfl, rfl⟩
          dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at hold
          rw [Finset.mem_filter, Finset.mem_product] at hold
          exact ha hold.1.2
      have hcard_insert_nat :
          (TwoBiteBasePairs (insert a s)).card =
            (TwoBiteBasePairs s).card + s.card := by
        rw [hinsert_eq, Finset.card_union_of_disjoint hdisjoint, hnew_card]
      have hcard_insert_real :
          ((TwoBiteBasePairs (insert a s)).card : ℝ) =
            ((TwoBiteBasePairs s).card : ℝ) + (s.card : ℝ) := by
        exact_mod_cast hcard_insert_nat
      have hchoose_insert :
          RealChooseTwo ((insert a s).card : ℝ) =
            RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
        simp [ha, RealChooseTwo]
        ring
      calc
        ((TwoBiteBasePairs (insert a s)).card : ℝ)
            = ((TwoBiteBasePairs s).card : ℝ) + (s.card : ℝ) := hcard_insert_real
        _ = RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
          rw [ih]
        _ = RealChooseTwo ((insert a s).card : ℝ) := hchoose_insert.symm
  have hProjectionPairSet_card :
      (((TwoBiteProjectionPairSet ω I).card : ℝ) =
        RealChooseTwo (((I.image (TwoBiteRedProjection ω)).card : ℝ)) +
          RealChooseTwo (((I.image (TwoBiteBlueProjection ω)).card : ℝ))) := by
    let redPairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).image
        (fun q => (Sum.inl q : Sum (Fin m × Fin m) (Fin m × Fin m)))
    let bluePairs : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).image
        (fun q => (Sum.inr q : Sum (Fin m × Fin m) (Fin m × Fin m)))
    have hred_card :
        (redPairs.card : ℝ) =
          RealChooseTwo (((I.image (TwoBiteRedProjection ω)).card : ℝ)) := by
      have himage :
          redPairs.card =
            (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).card := by
        dsimp [redPairs]
        exact Finset.card_image_of_injective _
          (by
            intro a b h
            exact Sum.inl.inj h)
      exact_mod_cast (by
        rw [himage]
        exact hBasePairs_card_eq (I.image (TwoBiteRedProjection ω)))
    have hblue_card :
        (bluePairs.card : ℝ) =
          RealChooseTwo (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) := by
      have himage :
          bluePairs.card =
            (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).card := by
        dsimp [bluePairs]
        exact Finset.card_image_of_injective _
          (by
            intro a b h
            exact Sum.inr.inj h)
      exact_mod_cast (by
        rw [himage]
        exact hBasePairs_card_eq (I.image (TwoBiteBlueProjection ω)))
    have hdisjoint : Disjoint redPairs bluePairs := by
      rw [Finset.disjoint_left]
      intro e hred hblue
      dsimp [redPairs] at hred
      dsimp [bluePairs] at hblue
      rw [Finset.mem_image] at hred hblue
      rcases hred with ⟨r, _hr, hre⟩
      rcases hblue with ⟨b, _hb, hbe⟩
      rw [← hre] at hbe
      cases hbe
    have hset_eq : TwoBiteProjectionPairSet ω I = redPairs ∪ bluePairs := by
      rfl
    calc
      ((TwoBiteProjectionPairSet ω I).card : ℝ)
          = ((redPairs ∪ bluePairs).card : ℝ) := by rw [hset_eq]
      _ = (redPairs.card : ℝ) + (bluePairs.card : ℝ) := by
        exact_mod_cast Finset.card_union_of_disjoint hdisjoint
      _ = RealChooseTwo (((I.image (TwoBiteRedProjection ω)).card : ℝ)) +
          RealChooseTwo (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) := by
        rw [hred_card, hblue_card]
  have hChoose_nat_nonneg : ∀ a : ℕ, 0 ≤ RealChooseTwo (a : ℝ) := by
    intro a
    by_cases ha0 : a = 0
    · simp [ha0, RealChooseTwo]
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
      have ha_one : (1 : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt ha_pos)
      have ha_nonneg : 0 ≤ (a : ℝ) := by exact_mod_cast Nat.zero_le a
      unfold RealChooseTwo
      nlinarith
  have hProjectedPairSum_nonneg :
      ∀ (cls : TwoBiteBaseVertex m → Prop) (proj : Fin n → Fin m),
        0 ≤ TwoBiteProjectedPairSum ω I cls proj := by
    intro cls proj
    dsimp [TwoBiteProjectedPairSum]
    exact Finset.sum_nonneg (fun x _hx =>
      hChoose_nat_nonneg (((TwoBiteX ω I x).image proj).card))
  have hSameHuge_nonneg :
      0 ≤
        TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω) := by
    exact add_nonneg
      (hProjectedPairSum_nonneg hugeRed (TwoBiteRedProjection ω))
      (hProjectedPairSum_nonneg hugeBlue (TwoBiteBlueProjection ω))
  have hClassSame_le :
      (qSmall.card : ℝ) + (qMedium.card : ℝ) + (qLarge.card : ℝ) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
        ≤ 8 * ε1 * (I.card : ℝ) ^ 2 := by
    linarith only [hClassControlled_num, hSameHuge_nonneg]
  have hClosed_le_class_same_opp :
      (closedSet.card : ℝ) ≤
        (qSmall.card : ℝ) + (qMedium.card : ℝ) + (qLarge.card : ℝ) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)) +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω)) := by
    linarith only [hClosed_card_le_class_union, hQHuge_bound]
  have hClosed_le_error_opp :
      (closedSet.card : ℝ) ≤
        8 * ε1 * (I.card : ℝ) ^ 2 +
          (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω)) := by
    linarith only [hClosed_le_class_same_opp, hClassSame_le]
  have hClosed_le_error_targets :
      (closedSet.card : ℝ) ≤
        8 * ε1 * (I.card : ℝ) ^ 2 +
          (1 + ε1) * (redOppTarget + blueOppTarget) := by
    linarith only [hClosed_le_error_opp, hHugeOppTotal]
  have hChoose_half_bound :
      ∀ {x K : ℝ}, 0 ≤ x → x ≤ K → RealChooseTwo x ≤ K ^ 2 / 2 := by
    intro x K hx_nonneg hx_le
    have hx_sq_le : x ^ 2 ≤ K ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hx_nonneg hx_le
    have hx_sub_le : x - 1 ≤ x := by
      linarith
    have hprod_le_xsq : x * (x - 1) ≤ x * x :=
      mul_le_mul_of_nonneg_left hx_sub_le hx_nonneg
    have hdiv_le : x * (x - 1) / 2 ≤ x * x / 2 :=
      div_le_div_of_nonneg_right hprod_le_xsq (by norm_num : (0 : ℝ) ≤ 2)
    have hx_sq_half_le : x * x / 2 ≤ K ^ 2 / 2 := by
      exact div_le_div_of_nonneg_right (by simpa [pow_two] using hx_sq_le)
        (by norm_num : (0 : ℝ) ≤ 2)
    unfold RealChooseTwo
    exact le_trans hdiv_le hx_sq_half_le
  have hRedImage_le_I :
      (((I.image (TwoBiteRedProjection ω)).card : ℝ) ≤ (I.card : ℝ)) := by
    exact_mod_cast Finset.card_image_le
  have hBlueImage_le_I :
      (((I.image (TwoBiteBlueProjection ω)).card : ℝ) ≤ (I.card : ℝ)) := by
    exact_mod_cast Finset.card_image_le
  have hRedImage_nonneg :
      0 ≤ (((I.image (TwoBiteRedProjection ω)).card : ℝ)) := by
    exact_mod_cast Nat.zero_le (I.image (TwoBiteRedProjection ω)).card
  have hBlueImage_nonneg :
      0 ≤ (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) := by
    exact_mod_cast Nat.zero_le (I.image (TwoBiteBlueProjection ω)).card
  have hRedDef_nonneg :
      0 ≤ (I.card : ℝ) -
        (((I.image (TwoBiteRedProjection ω)).card : ℝ)) := by
    linarith
  have hBlueDef_nonneg :
      0 ≤ (I.card : ℝ) -
        (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) := by
    linarith
  have hRedDef_le :
      (I.card : ℝ) - (((I.image (TwoBiteRedProjection ω)).card : ℝ)) ≤
        (I.card : ℝ) := by
    linarith
  have hBlueDef_le :
      (I.card : ℝ) - (((I.image (TwoBiteBlueProjection ω)).card : ℝ)) ≤
        (I.card : ℝ) := by
    linarith
  have hRedTarget_le :
      redOppTarget ≤ (I.card : ℝ) ^ 2 / 2 := by
    dsimp [redOppTarget]
    exact le_trans (min_le_left _ _)
      (hChoose_half_bound hRedDef_nonneg hRedDef_le)
  have hBlueTarget_le :
      blueOppTarget ≤ (I.card : ℝ) ^ 2 / 2 := by
    dsimp [blueOppTarget]
    exact le_trans (min_le_left _ _)
      (hChoose_half_bound hBlueDef_nonneg hBlueDef_le)
  have hTargets_le_sq :
      redOppTarget + blueOppTarget ≤ (I.card : ℝ) ^ 2 := by
    linarith [hRedTarget_le, hBlueTarget_le]
  have hEpsilon_targets_le :
      ε1 * (redOppTarget + blueOppTarget) ≤
        ε1 * (I.card : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hTargets_le_sq hε1
  let targetSum : ℝ := redOppTarget + blueOppTarget
  let epsilonError : ℝ := ε1 * (I.card : ℝ) ^ 2
  have hClosed_le_error_targets_compact :
      (closedSet.card : ℝ) ≤ 8 * epsilonError + (1 + ε1) * targetSum := by
    dsimp [targetSum, epsilonError]
    simpa [mul_assoc] using hClosed_le_error_targets
  have hEpsilon_targets_le_compact :
      ε1 * targetSum ≤ epsilonError := by
    simpa [targetSum, epsilonError] using hEpsilon_targets_le
  have hClosed_le_targets_error_compact :
      (closedSet.card : ℝ) ≤ targetSum + 9 * epsilonError := by
    calc
      (closedSet.card : ℝ)
          ≤ 8 * epsilonError + (1 + ε1) * targetSum :=
        hClosed_le_error_targets_compact
      _ = targetSum + (8 * epsilonError + ε1 * targetSum) := by
        ring
      _ ≤ targetSum + (8 * epsilonError + epsilonError) := by
        have hinner : 8 * epsilonError + ε1 * targetSum ≤
            8 * epsilonError + epsilonError := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hEpsilon_targets_le_compact (8 * epsilonError)
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hinner targetSum
      _ = targetSum + 9 * epsilonError := by
        ring
  have hClosed_le_targets_error :
      (closedSet.card : ℝ) ≤
        redOppTarget + blueOppTarget + 9 * ε1 * (I.card : ℝ) ^ 2 := by
    simpa [targetSum, epsilonError, mul_assoc] using hClosed_le_targets_error_compact
  have hProjectionOpen_rewrite :
      ((TwoBiteProjectionPairSet ω I).card : ℝ) -
          ProjectionOpenPairFunction
            (((I.image (TwoBiteRedProjection ω)).card : ℝ))
            (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
            (I.card : ℝ) p (n : ℝ)
        = redOppTarget + blueOppTarget := by
    rw [hProjectionPairSet_card]
    exact hOpenPair_algebra
  calc
    ((@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
        (fun e => TwoBiteProjectionPairClosed ω I e)
        (Classical.decPred (fun e => TwoBiteProjectionPairClosed ω I e))
        (TwoBiteProjectionPairSet ω I)).card : ℝ)
        = (closedSet.card : ℝ) := by rfl
    _ ≤ redOppTarget + blueOppTarget + 9 * ε1 * (I.card : ℝ) ^ 2 :=
      hClosed_le_targets_error
    _ =
        ((TwoBiteProjectionPairSet ω I).card : ℝ) -
          ProjectionOpenPairFunction
            (((I.image (TwoBiteRedProjection ω)).card : ℝ))
            (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
            (I.card : ℝ) p (n : ℝ) +
          9 * ε1 * (I.card : ℝ) ^ 2 := by
      rw [hProjectionOpen_rewrite]
