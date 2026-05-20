import Tablet.FixedSetConditionalIndependenceBound
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.ParameterHierarchy
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteProjectionCellEmpty
import Tablet.TwoBiteConditionalIntersectionBound
import Tablet.TwoBiteProjectionSizePartition

-- [TABLET NODE: FixedSetProjectionCellReduction]

theorem FixedSetProjectionCellReduction :
    ∀ {n m k : ℕ} {p ε ε1 ε2 η δ : ℝ} {n0 : ℕ}
      (I : Finset (Fin n)),
      ParameterHierarchy ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = k →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      (∀ ℓR ℓB : ℕ,
        ℓR * ℓB ≥ k →
        TwoBiteEventProbability n m p
            (fun ω =>
              TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
          ≤
          Real.exp
            ((η - (2 - (ℓR : ℝ) / (k : ℝ) -
                (ℓB : ℝ) / (k : ℝ)) / 2) *
              (k : ℝ) * Real.log (n : ℝ))) →
      (Finset.range (k + 1)).sum (fun ℓR =>
        (Finset.range (k + 1)).sum (fun ℓB =>
          if ℓR * ℓB < k then
            0
          else
            Real.exp
              ((η - (2 - (ℓR : ℝ) / (k : ℝ) -
                  (ℓB : ℝ) / (k : ℝ)) / 2) *
                (k : ℝ) * Real.log (n : ℝ)) *
              min (1 : ℝ)
                (Real.exp
                  (-(p *
                    (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                      (k : ℝ) p (n : ℝ) -
                      ε ^ 3 * (k : ℝ) ^ 2)))))) ≤
        δ * ((Nat.choose n k : ℝ)⁻¹) →
      TwoBiteEventProbability n m p
          (fun ω =>
            (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
        ≤ δ * ((Nat.choose n k : ℝ)⁻¹) := by
-- BODY
  intro n m k p ε ε1 ε2 η δ n0 I hParams hn hm hp hI hScale hCell hSum
  unfold ParameterHierarchy at hParams
  rcases hParams with
    ⟨hε2_pos, hε2_lt_ε1, hε1_lt_ε, hε_lt_one, hε_lt_1_16,
      hthree, height, hn0large, hComparisons⟩
  have hε1_nonneg : 0 ≤ ε1 := le_of_lt (lt_trans hε2_pos hε2_lt_ε1)
  have hε1_le_one : ε1 ≤ 1 :=
    le_of_lt (lt_trans hε1_lt_ε hε_lt_one)
  have hCompn := hComparisons n hn
  have hp_nonneg_base : 0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
    simpa [TwoBiteEdgeProbability] using hCompn.2.1
  have hp_le_half_base : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := by
    simpa [TwoBiteEdgeProbability] using hCompn.2.2.1
  have hp_nonneg : 0 ≤ p := by
    simpa [hp] using hp_nonneg_base
  have hp_le_one : p ≤ 1 := by
    have hp_le_half : p ≤ (1 / 2 : ℝ) := by
      simpa [hp] using hp_le_half_base
    linarith
  let event : TwoBiteSample n m p → Prop :=
    fun ω =>
      (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω
  have hweight : ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp_nonneg hp_le_one
  have hpartition :
      TwoBiteEventProbability n m p event =
        (Finset.range (k + 1)).sum (fun ℓR =>
          (Finset.range (k + 1)).sum (fun ℓB =>
            TwoBiteEventProbability n m p
              (fun ω =>
                event ω ∧
                  TwoBiteProjectionSizeEvent
                    (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I))) := by
    exact TwoBiteProjectionSizePartition I event hI
  rw [hpartition]
  refine le_trans ?_ hSum
  refine Finset.sum_le_sum ?_
  intro ℓR hℓR
  refine Finset.sum_le_sum ?_
  intro ℓB hℓB
  by_cases hlt : ℓR * ℓB < k
  · have hzero :
        TwoBiteEventProbability n m p
          (fun ω =>
            event ω ∧
              TwoBiteProjectionSizeEvent
                (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I) = 0 := by
      classical
      unfold TwoBiteEventProbability
      apply Finset.sum_eq_zero
      intro ω hω
      have hcell :
          TwoBiteProjectionSizeEvent
            (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I := by
        have hmem :
            event ω ∧
              TwoBiteProjectionSizeEvent
                (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hω
        exact hmem.2
      exact False.elim ((TwoBiteProjectionCellEmpty ω I hlt) hcell)
    rw [hzero]
    simp [hlt]
  · have hge : ℓR * ℓB ≥ k := le_of_not_gt hlt
    have hcond :
        TwoBiteConditionalProbability n m p event
            (fun ω =>
              TwoBiteProjectionSizeEvent
                (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
          ≤
          Real.exp
            (-(p *
              (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                (k : ℝ) p (n : ℝ) - ε ^ 3 * (k : ℝ) ^ 2))) := by
      exact FixedSetConditionalIndependenceBound (n := n) (m := m) (k := k)
        (ℓR := ℓR) (ℓB := ℓB) (p := p) (ε := ε) (ε1 := ε1)
        (ε2 := ε2) (n0 := n0) I hε1_nonneg hε1_le_one hComparisons
        hn hm hp hI hScale
    have hle :=
      TwoBiteConditionalIntersectionBound
        (n := n) (m := m) (p := p)
        (cellBound :=
          Real.exp
            ((η - (2 - (ℓR : ℝ) / (k : ℝ) -
                (ℓB : ℝ) / (k : ℝ)) / 2) *
              (k : ℝ) * Real.log (n : ℝ)))
        (condBound :=
          Real.exp
            (-(p *
              (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                (k : ℝ) p (n : ℝ) - ε ^ 3 * (k : ℝ) ^ 2))))
        (event := event)
        (condition := fun ω =>
          TwoBiteProjectionSizeEvent
            (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
        hweight (by positivity) (by positivity) (hCell ℓR ℓB hge) hcond
    simpa [hlt] using hle
