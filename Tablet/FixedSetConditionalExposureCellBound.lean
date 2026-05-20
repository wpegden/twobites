import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.ProjectionOpenPairFunction
import Tablet.ClosedPairsBound
import Tablet.LargeClosedPairsBound
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.FixedSetExposureCellProductLaw
import Tablet.FixedSetExceptionalWitnessClassification
import Tablet.FixedSetOppositeColorTerminalCoverage
import Tablet.FixedSetAdaptiveExceptionalCandidates
import Tablet.FixedSetHistoryCellAdaptiveProductBound
import Tablet.FixedSetCellAnalyticSummationBound

-- [TABLET NODE: FixedSetConditionalExposureCellBound]

theorem FixedSetConditionalExposureCellBound :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (I : Finset (Fin n)),
      0 ≤ ε1 →
      ε1 ≤ 1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = k →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      (∀ ω : TwoBiteSample n m p,
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I →
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
            (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
          ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      TwoBiteConditionalProbability n m p
          (fun ω =>
            (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
          (fun ω =>
            TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
        ≤
          Real.exp
            (-(p *
              ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                (k : ℝ) p (n : ℝ)) +
              8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 +
              10 * ε1 * p * (k : ℝ) ^ 2 +
              4 * Real.log (k : ℝ)) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε ε1 ε2 n0 I hε1_nonneg hε1_le_one
    hComparisons hn hm hp hIcard hk hOpenLower
  let event : TwoBiteSample n m p → Prop :=
    fun ω =>
      (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω
  let condition : TwoBiteSample n m p → Prop :=
    fun ω =>
      TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I
  let B : ℝ :=
    Real.exp
      (-(p *
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
          (k : ℝ) p (n : ℝ)) +
        8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 +
        10 * ε1 * p * (k : ℝ) ^ 2 +
        4 * Real.log (k : ℝ))
  have hB_nonneg : 0 ≤ B := (Real.exp_pos _).le
  by_cases hcondition_zero :
      TwoBiteEventProbability n m p condition = 0
  · simpa [event, condition, B, TwoBiteConditionalProbability,
      hcondition_zero] using hB_nonneg
  · have hCompn := hComparisons n hn
    have hp_base_nonneg :
        0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
      simpa [TwoBiteEdgeProbability] using hCompn.2.1
    have hp_nonneg : 0 ≤ p := by
      simpa [hp] using hp_base_nonneg
    have hp_base_le_half :
        TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := by
      simpa [TwoBiteEdgeProbability] using hCompn.2.2.1
    have hp_le_half : p ≤ (1 / 2 : ℝ) := by
      simpa [hp] using hp_base_le_half
    have hm_pos_base :
        0 < (TwoBiteNaturalReducedVertexCount n : ℝ) := by
      simpa using hCompn.1
    have hm_pos : 0 < (m : ℝ) := by
      simpa [hm] using hm_pos_base
    have hp_prod_ge_base :
        1 ≤
          2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n *
            (TwoBiteNaturalReducedVertexCount n : ℝ) := by
      simpa [TwoBiteEdgeProbability] using hCompn.2.2.2.1
    have hp_prod_ge : 1 ≤ 2 * p * (m : ℝ) := by
      simpa [hp, hm] using hp_prod_ge_base
    have hp_ne_zero : p ≠ 0 := by
      intro hp_zero
      have hle_zero : (2 : ℝ) * p * (m : ℝ) ≤ 0 := by
        nlinarith
      nlinarith
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne_zero)
    have hp_lt_one : p < 1 := by
      nlinarith
    rcases
        FixedSetExposureCellProductLaw
          (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
          (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2) I
          hp_pos hp_lt_one with
      ⟨ι, instι, hist, hCover, hDisjoint, hCellData, hLift⟩
    letI := instι
    have hcellBound :
        ∀ i : ι,
          TwoBiteConditionalProbability n m p event (hist i) ≤ B := by
      intro i
      rcases hCellData i with
        ⟨recorded, terminal, order, rep, hRepHist, hHistCylinder,
          hRecorded, hRecordedOriented, hOrderNodup, hOrderFinset,
          hTerminal, hTerminalUnrecorded, hTerminalOriented,
          hStagedTerminal, hProductLaw, hPrefixSafe⟩
      have hBranchCandidates :
          ∀ branch : TwoBiteSample n m p,
            hist i branch →
              ∃ ER EB :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
                ER ⊆ terminal ∧
                EB ⊆ terminal ∧
                (∀ ω : TwoBiteSample n m p,
                  hist i ω →
                  (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
                  (∀ e,
                    e ∈ recorded →
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
                  (∀ e,
                    e ∈ terminal →
                      match e with
                      | Sum.inl _ => True
                      | Sum.inr _ =>
                          (TwoBiteEdgeCoordinateValue ω e ↔
                            TwoBiteEdgeCoordinateValue branch e)) →
                  TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                    ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                    (∀ e,
                      e ∈ TwoBiteStagedOpenPairs ω ε I →
                      TwoBiteEdgeCoordinateValue ω e →
                      (match e with
                      | Sum.inl _ => True
                      | Sum.inr _ => False) →
                      (TwoBiteFinalGraph ω).2.2.IsIndepSet
                        (↑I : Set (Fin n)) →
                        e ∈ ER)) ∧
                (∀ ω : TwoBiteSample n m p,
                  hist i ω →
                  (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
                  (∀ e,
                    e ∈ recorded →
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
                  (∀ e,
                    e ∈ terminal →
                      match e with
                      | Sum.inl _ =>
                          (TwoBiteEdgeCoordinateValue ω e ↔
                            TwoBiteEdgeCoordinateValue branch e)
                      | Sum.inr _ => True) →
                  TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                    ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                    (∀ e,
                      e ∈ TwoBiteStagedOpenPairs ω ε I →
                      TwoBiteEdgeCoordinateValue ω e →
                      (match e with
                      | Sum.inl _ => False
                      | Sum.inr _ => True) →
                      (TwoBiteFinalGraph ω).2.2.IsIndepSet
                        (↑I : Set (Fin n)) →
                        e ∈ EB)) := by
        intro branch hBranch
        rcases
            FixedSetAdaptiveExceptionalCandidates
              (n := n) (m := m) (k := k) (p := p) (ε := ε)
              (ε1 := ε1) (ε2 := ε2) (n0 := n0)
              I (hist i) recorded terminal branch
              hε1_nonneg hComparisons hn hm hp hIcard hk hBranch
              hRecorded hTerminal hStagedTerminal with
          ⟨ER, EB, hER_mem, hEB_mem, hRedCandidates, hBlueCandidates⟩
        refine ⟨ER, EB, ?_, ?_, hRedCandidates, hBlueCandidates⟩
        · intro e he
          exact ((hER_mem e).1 he).1
        · intro e he
          exact ((hEB_mem e).1 he).1
      have hHistProjection :
          ∀ ω : TwoBiteSample n m p,
            hist i ω →
              TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                (ℓB := ℓB) ω I := by
        intro ω hω
        exact (hCover ω).2 ⟨i, hω⟩
      have hProductBound :
          TwoBiteConditionalProbability n m p event (hist i) ≤
            max (1 : ℝ) ((k : ℝ) ^ 4) *
              Real.exp
                (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 -
                  p *
                    (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                      (k : ℝ) p (n : ℝ) -
                      10 * ε1 * (k : ℝ) ^ 2)) :=
        FixedSetHistoryCellAdaptiveProductBound
          (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
          (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2)
          I (hist i) recorded terminal order rep
          hε1_nonneg hε1_le_one hp_nonneg hp_le_half hIcard
          hRepHist hHistProjection hHistCylinder hRecorded hTerminal
          hOrderNodup hOrderFinset hTerminalUnrecorded hStagedTerminal
          hProductLaw hPrefixSafe hOpenLower hBranchCandidates
      have hAnalytic :
          max (1 : ℝ) ((k : ℝ) ^ 4) *
              Real.exp
                (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 -
                  p *
                    (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                      (k : ℝ) p (n : ℝ) -
                      10 * ε1 * (k : ℝ) ^ 2))
            ≤ B := by
        by_cases hk_zero : (k : ℝ) = 0
        · have hmax :
              max (1 : ℝ) ((k : ℝ) ^ 4) = 1 := by
            simp [hk_zero]
          rw [hmax]
          simp [B, hk_zero]
        · have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
          have hk_pos : 0 < (k : ℝ) :=
            lt_of_le_of_ne hk_nonneg (Ne.symm hk_zero)
          have hk_nat_pos : 0 < k := by
            exact_mod_cast hk_pos
          have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast hk_nat_pos
          have hk_sq_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
            nlinarith [sq_nonneg ((k : ℝ) - 1)]
          have hk_pow_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 4 := by
            nlinarith [sq_nonneg ((k : ℝ) ^ 2 - 1)]
          have hmax :
              max (1 : ℝ) ((k : ℝ) ^ 4) = (k : ℝ) ^ 4 :=
            max_eq_right hk_pow_ge_one
          rw [hmax]
          simpa [B] using
            (FixedSetCellAnalyticSummationBound
              (k := k) (p := p) (ε1 := ε1)
              (f := ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                (k : ℝ) p (n : ℝ)))
      exact le_trans hProductBound hAnalytic
    have hGlobal := hLift B hB_nonneg hcellBound
    simpa [event, condition, B] using hGlobal
