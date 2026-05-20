import Tablet.FixedSetPreTerminalHistoryCells
import Tablet.FixedSetPreTerminalStagedOpenTerminalUnrecorded
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteStageRevealedVertex
import Tablet.TwoBiteStageF1
import Tablet.TwoBiteStageF2
import Tablet.TwoBiteProjectionContains
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteBaseFiber
import Tablet.TwoBiteBaseAdj
import Tablet.TwoBiteBasePairs
import Tablet.TwoBitePairsInSet
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.FixedSetClosedPredicateBoundary
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteX
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: FixedSetPreTerminalHistoryPartition]

theorem FixedSetPreTerminalHistoryPartition :
    ∀ {n m k ℓR ℓB : ℕ} {p ε : ℝ} (I : Finset (Fin n)),
      ∃ ι : Type, ∃ _ : Fintype ι,
        ∃ hist : ι → TwoBiteSample n m p → Prop,
          ∃ recorded :
            ι → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
          ∃ rep : ι → TwoBiteSample n m p,
            (∀ ω : TwoBiteSample n m p,
              TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                (ℓB := ℓB) ω I ↔ ∃ i : ι, hist i ω) ∧
            (∀ i j : ι, i ≠ j → ∀ ω : TwoBiteSample n m p,
              ¬ (hist i ω ∧ hist j ω)) ∧
            (∀ i : ι, hist i (rep i)) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω ↔
                (∀ x : Fin n, ω.2.2 x = (rep i).2.2 x) ∧
                (∀ e,
                  e ∈ recorded i →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue (rep i) e))) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ recorded i) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                  (ℓB := ℓB) ω I) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ ω' : TwoBiteSample n m p,
                  (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                  (∀ c,
                    c ∈ recorded i →
                      (TwoBiteEdgeCoordinateValue ω c ↔
                        TwoBiteEdgeCoordinateValue ω' c)) →
                    (∀ x,
                      TwoBiteStageRevealedVertex ω ε I x ↔
                        TwoBiteStageRevealedVertex ω' ε I x) ∧
                    (∀ e,
                      TwoBiteProjectionPairTouched ω ε I e ↔
                        TwoBiteProjectionPairTouched ω' ε I e)) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                    e ∈ TwoBiteTerminalCoordinateUniverse m ∧
                      e ∉ recorded i) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε I
  rcases FixedSetPreTerminalHistoryCells
      (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
      (p := p) (ε := ε) I with
    ⟨ι, instι, hist, recorded, rep, hcover, hdisjoint, hrep,
      hcylinder, hrecorded, hevent, hreplay⟩
  refine
    ⟨ι, instι, hist, recorded, rep, hcover, hdisjoint, hrep,
      hcylinder, hrecorded, hevent, hreplay, ?_⟩
  intro i ω hhist e hopen
  exact
    FixedSetPreTerminalStagedOpenTerminalUnrecorded
      I (recorded i) ω (hrecorded i ω hhist) e hopen
