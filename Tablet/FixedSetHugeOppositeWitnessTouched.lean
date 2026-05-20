import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteX
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.FixedSetHugeWitnessStageRevealed
import Tablet.FiberAndDegreeEvent
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetHugeOppositeWitnessTouched]

theorem FixedSetHugeOppositeWitnessTouched :
    ∀ {n m : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n)),
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      (∀ q : Fin m × Fin m,
        (∃ b : Fin m,
          TwoBiteHugeClass ω I (Sum.inr b) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ω I (Sum.inr b)).image
                  (TwoBiteRedProjection ω))) →
          Sum.inl q ∈ TwoBitePreTerminalRecordedPairs ω ε I ∧
            Sum.inl q ∉ TwoBiteStagedOpenPairs ω ε I) ∧
      (∀ q : Fin m × Fin m,
        (∃ r : Fin m,
          TwoBiteHugeClass ω I (Sum.inl r) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ω I (Sum.inl r)).image
                  (TwoBiteBlueProjection ω))) →
          Sum.inr q ∈ TwoBitePreTerminalRecordedPairs ω ε I ∧
            Sum.inr q ∉ TwoBiteStagedOpenPairs ω ε I) := by
-- BODY
  classical
  intro n m p ε ε1 ε2 n0 ω I hComparisons hn hm hp hI hFiber
  constructor
  · intro q hq
    rcases hq with ⟨b, hHuge, hPair⟩
    have hStage :
        TwoBiteStageRevealedVertex ω ε I (Sum.inr b) :=
      FixedSetHugeWitnessStageRevealed ω I (Sum.inr b)
        hComparisons hn hm hp hI hFiber hHuge
    have hlt : q.1.val < q.2.val := by
      have hPair' := hPair
      simp [TwoBiteBasePairs, TwoBitePairsInSet] at hPair'
      exact hPair'.2
    have hRecorded :
        Sum.inl q ∈ TwoBitePreTerminalRecordedPairs ω ε I := by
      simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
      exact ⟨hlt, Or.inr (Or.inr ⟨b, hStage, hPair⟩)⟩
    have hNotOpen :
        Sum.inl q ∉ TwoBiteStagedOpenPairs ω ε I := by
      intro hOpen
      unfold TwoBiteStagedOpenPairs at hOpen
      exact (Finset.mem_filter.mp hOpen).2.2.2 hRecorded
    exact ⟨hRecorded, hNotOpen⟩
  · intro q hq
    rcases hq with ⟨r, hHuge, hPair⟩
    have hStage :
        TwoBiteStageRevealedVertex ω ε I (Sum.inl r) :=
      FixedSetHugeWitnessStageRevealed ω I (Sum.inl r)
        hComparisons hn hm hp hI hFiber hHuge
    have hlt : q.1.val < q.2.val := by
      have hPair' := hPair
      simp [TwoBiteBasePairs, TwoBitePairsInSet] at hPair'
      exact hPair'.2
    have hRecorded :
        Sum.inr q ∈ TwoBitePreTerminalRecordedPairs ω ε I := by
      simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
      exact ⟨hlt, Or.inr (Or.inl ⟨r, hStage, hPair⟩)⟩
    have hNotOpen :
        Sum.inr q ∉ TwoBiteStagedOpenPairs ω ε I := by
      intro hOpen
      unfold TwoBiteStagedOpenPairs at hOpen
      exact (Finset.mem_filter.mp hOpen).2.2.2 hRecorded
    exact ⟨hRecorded, hNotOpen⟩
