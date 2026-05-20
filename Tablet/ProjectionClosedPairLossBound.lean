import Tablet.TwoBiteUnclosedProjectedPairs
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.ProjectionOpenPairFunction
import Tablet.ClosedPairsBound
import Tablet.ClosedPairsControlled
import Tablet.LargeClosedPairsBound
import Tablet.HugeProjectionClosedPairsBound
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteProjectedPairSum
import Tablet.TwoBiteProjectedPairsClosedInClass
import Tablet.ProjectedPairsInClassMultiplicityBound
import Tablet.ProjectionClosedPairCountBound
import Tablet.ProjectionUnclosedFromClosedCount
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteX
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteSmallClosedPairsEvent

-- [TABLET NODE: ProjectionClosedPairLossBound]

theorem ProjectionClosedPairLossBound :
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
      ProjectionOpenPairFunction
          ((I.image (TwoBiteRedProjection ω)).card : ℝ)
          ((I.image (TwoBiteBlueProjection ω)).card : ℝ)
          (I.card : ℝ) p (n : ℝ) -
          9 * ε1 * (I.card : ℝ) ^ 2
        ≤ ((TwoBiteUnclosedProjectedPairs ω I).card : ℝ) := by
-- BODY
  intro n m p ω I ε ε1 ε2 n0 hε1 hParams hn hm hp hI hFiber hMedium hSmall
  exact
    ProjectionUnclosedFromClosedCount ω I
      (ProjectionOpenPairFunction
        (((I.image (TwoBiteRedProjection ω)).card : ℝ))
        (((I.image (TwoBiteBlueProjection ω)).card : ℝ))
        (I.card : ℝ) p (n : ℝ))
      (9 * ε1 * (I.card : ℝ) ^ 2)
      (ProjectionClosedPairCountBound ω I ε ε1 ε2
        hε1 hParams hn hm hp hI hFiber hMedium hSmall)
