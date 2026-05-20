import Tablet.TwoBiteProjectionSizeEvent

-- [TABLET NODE: TwoBiteProjectionCellEmpty]

theorem TwoBiteProjectionCellEmpty :
    ∀ {n m k ℓR ℓB : ℕ} {p : ℝ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n)),
      ℓR * ℓB < k →
      ¬ TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I := by
-- BODY
  intro n m k ℓR ℓB p ω I hlt hcell
  rcases hcell with ⟨hIcard, hRcard, hBcard⟩
  let embSet : Finset (Fin m × Fin m) := I.image (TwoBiteEmbedding ω)
  let redSet : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
  let blueSet : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
  have hcardEmb : embSet.card = k := by
    have hinj : Set.InjOn (TwoBiteEmbedding ω) (↑I : Set (Fin n)) := by
      intro x hx y hy hxy
      exact (TwoBiteEmbedding ω).injective hxy
    simpa [embSet, hIcard] using
      (Finset.card_image_of_injOn (s := I) (f := TwoBiteEmbedding ω) hinj)
  have hsubset : embSet ⊆ redSet ×ˢ blueSet := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    rw [Finset.mem_product]
    constructor
    · exact Finset.mem_image.mpr ⟨v, hv, by simp [TwoBiteRedProjection]⟩
    · exact Finset.mem_image.mpr ⟨v, hv, by simp [TwoBiteBlueProjection]⟩
  have hle : k ≤ ℓR * ℓB := by
    calc
      k = embSet.card := hcardEmb.symm
      _ ≤ (redSet ×ˢ blueSet).card := Finset.card_le_card hsubset
      _ = redSet.card * blueSet.card := Finset.card_product redSet blueSet
      _ = ℓR * ℓB := by simp [redSet, blueSet, hRcard, hBcard]
  exact not_lt_of_ge hle hlt
