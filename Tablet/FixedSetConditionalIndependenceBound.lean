import Tablet.FixedSetOpenPairsAfterConditioning
import Tablet.FixedSetExposureExceptionalChoices
import Tablet.ProjectionSizeProbabilityBound
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteConditionalProbability
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetConditionalIndependenceBound]

theorem FixedSetConditionalIndependenceBound :
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
      TwoBiteConditionalProbability n m p
          (fun ω =>
            (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
          (fun ω =>
            TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
        ≤
        Real.exp
          (-(p *
            (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
              (k : ℝ) p (n : ℝ) - ε ^ 3 * (k : ℝ) ^ 2))) := by
-- BODY
  intro n m k ℓR ℓB p ε ε1 ε2 n0 I hε1 hε1_le hParams hn hm hp hI hScale
  apply FixedSetExposureExceptionalChoices (n := n) (m := m) (k := k)
    (ℓR := ℓR) (ℓB := ℓB) (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2)
    (n0 := n0) I hε1 hε1_le hParams hn hm hp hI hScale
  intro ω hRegular hProjection
  exact FixedSetOpenPairsAfterConditioning (n := n) (m := m) (k := k)
    (ℓR := ℓR) (ℓB := ℓB) (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2)
    (n0 := n0) ω I hε1 hParams hn hm hp hI hScale hRegular hProjection
