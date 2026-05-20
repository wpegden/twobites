import Tablet.ProjectionClosedPairLossBound
import Tablet.StagedTouchedPairsBound
import Tablet.StagedOpenPairsFromUnclosedAndTouched
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteSameColorClosedImpliesClosed
import Tablet.TwoBiteXPlus
import Tablet.TwoBiteX
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteUnclosedProjectedPairs
import Tablet.TwoBiteTouchedProjectedPairs
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: RevealingLeavesOpenPairs]

theorem RevealingLeavesOpenPairs :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) (I : Finset (Fin n))
      (ε ε1 ε2 : ℝ) {n0 : ℕ},
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      TwoBiteMediumClosedPairsEvent (k := I.card) ε ε1 ω →
      TwoBiteSmallClosedPairsEvent (k := I.card) ε ε1 ω →
      ProjectionOpenPairFunction
          ((I.image (TwoBiteRedProjection ω)).card : ℝ)
          ((I.image (TwoBiteBlueProjection ω)).card : ℝ)
          (I.card : ℝ) p (n : ℝ) -
          10 * ε1 * (I.card : ℝ) ^ 2
        ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
-- BODY
  intro n m p ω I ε ε1 ε2 n0 hε1 hParams hn hm hp hI hFiber hMedium hSmall
  exact
    StagedOpenPairsFromUnclosedAndTouched ω I ε ε1
      (ProjectionOpenPairFunction
        (((I.image (TwoBiteRedProjection ω)).card : ℝ))
        (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
        (I.card : ℝ) p (n : ℝ))
      (ProjectionClosedPairLossBound ω I ε ε1 ε2
        hε1 hParams hn hm hp hI hFiber hMedium hSmall)
      (StagedTouchedPairsBound ω I ε ε1 ε2
        hε1 hParams hn hI hFiber)
