import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteHugeClass

-- [TABLET NODE: TwoBiteClassSmallMediumLargeOrHuge]

theorem TwoBiteClassSmallMediumLargeOrHuge :
    ∀ {n m : ℕ} {p ε : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (x : TwoBiteBaseVertex m),
      TwoBiteSmallClass ω ε I x ∨
        TwoBiteMediumClass ω ε I x ∨
          TwoBiteLargeClass ω ε I x ∨
            TwoBiteHugeClass ω I x := by
-- BODY
  classical
  intro n m p ε ω I x
  let c : ℝ := ((TwoBiteX ω I x).card : ℝ)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le (TwoBiteX ω I x).card
  have hX_subset : TwoBiteX ω I x ⊆ I := by
    intro v hv
    change v ∈ I.filter (fun v => v ∈ TwoBiteLiftedNeighborhood ω x) at hv
    exact (Finset.mem_filter.mp hv).1
  have hc_le_I : c ≤ (I.card : ℝ) := by
    dsimp [c]
    exact_mod_cast Finset.card_le_card hX_subset
  by_cases hHuge : TwoBiteHugeCutoff n < c
  · right
    right
    right
    dsimp [TwoBiteHugeClass]
    exact ⟨by simpa [c] using hHuge, by simpa [c] using hc_le_I⟩
  · have hc_le_huge : c ≤ TwoBiteHugeCutoff n := le_of_not_gt hHuge
    by_cases hLarge : TwoBiteLargeCutoff ε n < c
    · right
      right
      left
      dsimp [TwoBiteLargeClass]
      exact ⟨by simpa [c] using hLarge, by simpa [c] using hc_le_huge⟩
    · have hc_le_large : c ≤ TwoBiteLargeCutoff ε n := le_of_not_gt hLarge
      by_cases hMedium : TwoBiteSmallCutoff ε n < c
      · right
        left
        dsimp [TwoBiteMediumClass]
        exact ⟨by simpa [c] using hMedium, by simpa [c] using hc_le_large⟩
      · have hc_le_small : c ≤ TwoBiteSmallCutoff ε n := le_of_not_gt hMedium
        left
        dsimp [TwoBiteSmallClass]
        exact ⟨by simpa [c] using hc_nonneg, by simpa [c] using hc_le_small⟩
