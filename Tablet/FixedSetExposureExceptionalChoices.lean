import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.FixedSetConditionalExposureCellBound
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.ProjectionOpenPairFunction
import Tablet.LargeClosedPairsBound
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetExposureExceptionalChoices]

theorem FixedSetExposureExceptionalChoices :
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
            (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
              (k : ℝ) p (n : ℝ) - ε ^ 3 * (k : ℝ) ^ 2))) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε ε1 ε2 n0 I hε1_nonneg hε1_le_one
    hComparisons hn hm hp hIcard hk hOpenLower
  let f :=
    ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (k : ℝ) p (n : ℝ)
  have hCell :=
    FixedSetConditionalExposureCellBound
      (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
      (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0)
      I hε1_nonneg hε1_le_one hComparisons hn hm hp hIcard hk
      hOpenLower
  have hAbsorb :
      8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 +
          10 * ε1 * p * (k : ℝ) ^ 2 +
          4 * Real.log (k : ℝ) ≤
        ε ^ 3 * p * (k : ℝ) ^ 2 := by
    have hCompn := hComparisons n hn
    rcases hCompn with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, hAbsorbBase, _, _⟩
    simpa [TwoBiteEdgeProbability, hk, hp] using hAbsorbBase
  have hExponent :
      -(p * f) +
            8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 +
            10 * ε1 * p * (k : ℝ) ^ 2 +
            4 * Real.log (k : ℝ) ≤
        -(p * (f - ε ^ 3 * (k : ℝ) ^ 2)) := by
    nlinarith [hAbsorb]
  exact hCell.trans (Real.exp_le_exp.mpr (by simpa [f] using hExponent))
