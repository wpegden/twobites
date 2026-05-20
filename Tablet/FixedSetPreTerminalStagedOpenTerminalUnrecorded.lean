import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetPreTerminalStagedOpenTerminalUnrecorded]

theorem FixedSetPreTerminalStagedOpenTerminalUnrecorded :
    ∀ {n m : ℕ} {p ε : ℝ} (I : Finset (Fin n))
      (recorded : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω : TwoBiteSample n m p),
      (∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔ e ∈ recorded) →
      ∀ e,
        e ∈ TwoBiteStagedOpenPairs ω ε I →
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded := by
-- BODY
  classical
  intro n m p ε I recorded ω hrecorded e hopen
  have hopen' :
      e ∈ TwoBiteProjectionPairSet ω I ∧
        ¬ TwoBiteProjectionPairSameColorClosed ω I e ∧
          ¬ TwoBiteProjectionPairTouched ω ε I e ∧
            e ∉ TwoBitePreTerminalRecordedPairs ω ε I := by
    simpa [TwoBiteStagedOpenPairs] using hopen
  refine ⟨?_, ?_⟩
  · cases e with
    | inl q =>
        have hset :
            ((∃ a ∈ I, TwoBiteRedProjection ω a = q.1) ∧
                ∃ a ∈ I, TwoBiteRedProjection ω a = q.2) ∧
              q.1.val < q.2.val := by
          simpa [TwoBiteProjectionPairSet, TwoBiteBasePairs,
            TwoBitePairsInSet] using hopen'.1
        simpa [TwoBiteTerminalCoordinateUniverse] using hset.2
    | inr q =>
        have hset :
            ((∃ a ∈ I, TwoBiteBlueProjection ω a = q.1) ∧
                ∃ a ∈ I, TwoBiteBlueProjection ω a = q.2) ∧
              q.1.val < q.2.val := by
          simpa [TwoBiteProjectionPairSet, TwoBiteBasePairs,
            TwoBitePairsInSet] using hopen'.1
        simpa [TwoBiteTerminalCoordinateUniverse] using hset.2
  · intro hrec
    exact hopen'.2.2.2 ((hrecorded e).2 hrec)
