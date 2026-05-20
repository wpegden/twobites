import Tablet.FixedSetPreTerminalRecordedPairsReplayEquality
import Tablet.FixedSetPreTerminalF2QueriesRecorded
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetPreTerminalReplayTranscriptConstruction]

theorem FixedSetPreTerminalReplayTranscriptConstruction :
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
                TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                  (ℓB := ℓB) ω I) := by
-- BODY
  intro n m k ℓR ℓB p ε I
  rcases
      FixedSetPreTerminalRecordedPairsReplayEquality
        (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
        (p := p) (ε := ε) I with
    ⟨ι, instι, hist, recorded, rep, hCover, hDisjoint, hRepHist,
      hCylinder, hEvent, _hRecorded⟩
  exact
    ⟨ι, instι, hist, recorded, rep, hCover, hDisjoint, hRepHist,
      hCylinder, hEvent⟩
