import Tablet.RevealingLeavesOpenPairs
import Tablet.TwoBiteRegularityEvent
import Tablet.FiberAndDegreeEvent
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.ProjectionOpenPairFunction
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetOpenPairsAfterConditioning]

theorem FixedSetOpenPairsAfterConditioning :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n)),
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = k →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
      TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I →
      ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
          (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
        ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
-- BODY
  intro n m k ℓR ℓB p ε ε1 ε2 n0 ω I hε1 hParams hn hm hp hI hScale
    hRegular hProjection
  rcases hRegular with ⟨hFiber, hMedium, hSmall⟩
  rcases hProjection with ⟨hIProjection, hRed, hBlue⟩
  have hIScale : I.card = TwoBiteNaturalIndependenceScale (1 + ε) n :=
    hIProjection.trans hScale
  have hMediumI : TwoBiteMediumClosedPairsEvent (k := I.card) ε ε1 ω := by
    simpa [hIProjection] using hMedium
  have hSmallI : TwoBiteSmallClosedPairsEvent (k := I.card) ε ε1 ω := by
    simpa [hIProjection] using hSmall
  have hOpen :=
    RevealingLeavesOpenPairs (n := n) (m := m) (p := p) ω I ε ε1 ε2
      (n0 := n0) hε1 hParams hn hm hp hIScale hFiber hMediumI hSmallI
  simpa [hIProjection, hRed, hBlue] using hOpen
