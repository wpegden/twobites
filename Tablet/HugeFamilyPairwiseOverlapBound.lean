import Tablet.FiberAndDegreeEvent
import Tablet.TwoBiteX

-- [TABLET NODE: HugeFamilyPairwiseOverlapBound]

theorem HugeFamilyPairwiseOverlapBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε2 : ℝ),
      FiberAndDegreeEvent ω ε2 →
      ∀ {x y : TwoBiteBaseVertex m}, x ≠ y →
        (((TwoBiteX ω I x ∩ TwoBiteX ω I y).card : ℝ)
          ≤ 100 * (Real.log (n : ℝ)) ^ 3) := by
-- BODY
  classical
  intro n m p ω I ε2 hfiber x y hxy
  dsimp [FiberAndDegreeEvent] at hfiber
  rcases hfiber with
    ⟨_, _, _, _, _, _, _, hred, hblue, hmixed, _, _⟩
  rcases x with r | b <;> rcases y with s | c
  · have hne : r ≠ s := by
      intro hrs
      apply hxy
      simp [hrs]
    have hsubset :
        TwoBiteX ω I (Sum.inl r) ∩ TwoBiteX ω I (Sum.inl s) ⊆
          TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inl s) := by
      intro v hv
      simp [TwoBiteX] at hv ⊢
      exact ⟨hv.1.2, hv.2.2⟩
    have hcard :
        (((TwoBiteX ω I (Sum.inl r) ∩ TwoBiteX ω I (Sum.inl s)).card : ℝ) ≤
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact le_trans hcard (by simpa using hred r s hne)
  · have hsubset :
        TwoBiteX ω I (Sum.inl r) ∩ TwoBiteX ω I (Sum.inr c) ⊆
          TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inr c) := by
      intro v hv
      simp [TwoBiteX] at hv ⊢
      exact ⟨hv.1.2, hv.2.2⟩
    have hcard :
        (((TwoBiteX ω I (Sum.inl r) ∩ TwoBiteX ω I (Sum.inr c)).card : ℝ) ≤
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact le_trans hcard (by simpa using hmixed r c)
  · have hsubset :
        TwoBiteX ω I (Sum.inr b) ∩ TwoBiteX ω I (Sum.inl s) ⊆
          TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inl s) := by
      intro v hv
      simp [TwoBiteX] at hv ⊢
      exact ⟨hv.1.2, hv.2.2⟩
    have hcard :
        (((TwoBiteX ω I (Sum.inr b) ∩ TwoBiteX ω I (Sum.inl s)).card : ℝ) ≤
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hmixed' :
        (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
          ≤ 100 * (Real.log (n : ℝ)) ^ 3) := by
      simpa [Finset.inter_comm] using hmixed s b
    exact le_trans hcard hmixed'
  · have hne : b ≠ c := by
      intro hbc
      apply hxy
      simp [hbc]
    have hsubset :
        TwoBiteX ω I (Sum.inr b) ∩ TwoBiteX ω I (Sum.inr c) ⊆
          TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inr c) := by
      intro v hv
      simp [TwoBiteX] at hv ⊢
      exact ⟨hv.1.2, hv.2.2⟩
    have hcard :
        (((TwoBiteX ω I (Sum.inr b) ∩ TwoBiteX ω I (Sum.inr c)).card : ℝ) ≤
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact le_trans hcard (by simpa using hblue b c hne)
