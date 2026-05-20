import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteStageF1
import Tablet.TwoBiteProjectionContains

-- [TABLET NODE: FixedSetPreTerminalF2QueriesRecorded]

theorem FixedSetPreTerminalF2QueriesRecorded :
    ∀ {n m : ℕ} {p ε : ℝ} (I : Finset (Fin n))
      (ω : TwoBiteSample n m p),
      (∀ r s : Fin m, ∀ q : Fin m × Fin m,
        (q = (r, s) ∨ q = (s, r)) →
        q.1.val < q.2.val →
        TwoBiteStageF1 ω I (Sum.inl s) →
        TwoBiteProjectionContains ω I (Sum.inl r) →
          Sum.inl q ∈ TwoBitePreTerminalRecordedPairs ω ε I) ∧
      (∀ b c : Fin m, ∀ q : Fin m × Fin m,
        (q = (b, c) ∨ q = (c, b)) →
        q.1.val < q.2.val →
        TwoBiteStageF1 ω I (Sum.inr c) →
        TwoBiteProjectionContains ω I (Sum.inr b) →
          Sum.inr q ∈ TwoBitePreTerminalRecordedPairs ω ε I) := by
-- BODY
  intro n m p ε I ω
  constructor
  · intro r s q hq hlt hF1 hproj
    classical
    simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse,
      TwoBiteStageRevealedVertex]
    constructor
    · exact hlt
    · left
      refine ⟨r, s, hq, ?_⟩
      right
      exact ⟨Or.inr (Or.inl hF1), hproj⟩
  · intro b c q hq hlt hF1 hproj
    classical
    simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse,
      TwoBiteStageRevealedVertex]
    constructor
    · exact hlt
    · left
      refine ⟨b, c, hq, ?_⟩
      right
      exact ⟨Or.inr (Or.inl hF1), hproj⟩
