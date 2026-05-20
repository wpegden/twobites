import Tablet.Preamble

-- [TABLET NODE: ProjectionDeficitFromSubset]

theorem ProjectionDeficitFromSubset :
    ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      (I W : Finset α) (f : α → β) (k : ℕ),
      I.card = k →
      W ⊆ I →
        (W.card : ℝ) - ((W.image f).card : ℝ) ≤
          (k : ℝ) - ((I.image f).card : ℝ) := by
-- BODY
  classical
  intro α β _ _ I W f k hI hWI
  have himage_subset :
      I.image f ⊆ W.image f ∪ ((I \ W).image f) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxI, rfl⟩
    by_cases hxW : x ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hxW, rfl⟩)
    · have hxDiff : x ∈ I \ W := by
        simp [hxI, hxW]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hxDiff, rfl⟩)
  have hcard_image_le :
      (I.image f).card ≤ (W.image f ∪ ((I \ W).image f)).card :=
    Finset.card_le_card himage_subset
  have hcard_union_le :
      (W.image f ∪ ((I \ W).image f)).card ≤
        (W.image f).card + ((I \ W).image f).card :=
    Finset.card_union_le _ _
  have hdiff_image_le :
      ((I \ W).image f).card ≤ (I \ W).card :=
    Finset.card_image_le
  have hWI_inter : W ∩ I = W := Finset.inter_eq_left.mpr hWI
  have hdiff_card : (I \ W).card = I.card - W.card := by
    rw [Finset.card_sdiff, hWI_inter]
  have hW_card_le_I : W.card ≤ I.card := Finset.card_le_card hWI
  have himage_card_bound :
      (I.image f).card ≤ (W.image f).card + (I.card - W.card) := by
    omega
  have hreal_image_bound :
      ((I.image f).card : ℝ) ≤
        ((W.image f).card : ℝ) + ((I.card - W.card : ℕ) : ℝ) := by
    exact_mod_cast himage_card_bound
  have hcast_diff :
      ((I.card - W.card : ℕ) : ℝ) = (I.card : ℝ) - (W.card : ℝ) := by
    exact Nat.cast_sub hW_card_le_I
  have hI_real : (I.card : ℝ) = (k : ℝ) := by
    exact_mod_cast hI
  nlinarith only [hreal_image_bound, hcast_diff, hI_real]
