import Tablet.Preamble
import Tablet.TwoBiteFinalPairs

-- [TABLET NODE: FinalPairsCardLeHalfSq]

lemma FinalPairsCardLeHalfSq {n : ℕ} (X : Finset (Fin n)) :
    ((TwoBiteFinalPairs X).card : ℝ) ≤ (X.card : ℝ) ^ 2 / 2 := by
-- BODY
  have h_disj : Disjoint (TwoBiteFinalPairs X) ((TwoBiteFinalPairs X).image (fun e => (e.2, e.1))) := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨y, hy, hy_eq⟩
    rw [TwoBiteFinalPairs, TwoBitePairsInSet, Finset.mem_filter] at hx1 hy
    have hx_eq : x = (y.2, y.1) := hy_eq.symm
    rw [hx_eq] at hx1
    have h1 := hx1.2
    have h2 := hy.2
    linarith
  have h_sub : (TwoBiteFinalPairs X) ∪ ((TwoBiteFinalPairs X).image (fun e => (e.2, e.1))) ⊆ X ×ˢ X := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with h1 | h2
    · rw [TwoBiteFinalPairs, TwoBitePairsInSet, Finset.mem_filter] at h1
      exact h1.1
    · rw [Finset.mem_image] at h2
      rcases h2 with ⟨y, hy, hy_eq⟩
      rw [TwoBiteFinalPairs, TwoBitePairsInSet, Finset.mem_filter] at hy
      rw [← hy_eq]
      have hy_prod := Finset.mem_product.mp hy.1
      exact Finset.mem_product.mpr ⟨hy_prod.2, hy_prod.1⟩
  have h_card_eq : (((TwoBiteFinalPairs X).image (fun e => (e.2, e.1))).card : ℝ) = ((TwoBiteFinalPairs X).card : ℝ) := by
    have h_inj : Set.InjOn (fun e : Fin n × Fin n => (e.2, e.1)) (TwoBiteFinalPairs X) := by
      intro x _ y _ hxy
      have h1 : x.2 = y.2 := congrArg Prod.fst hxy
      have h2 : x.1 = y.1 := congrArg Prod.snd hxy
      exact Prod.ext h2 h1
    exact_mod_cast Finset.card_image_of_injOn h_inj
  have h_card_prod : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
    rw [Finset.card_product, sq]
    push_cast
    rfl
  have h_union : (((TwoBiteFinalPairs X) ∪ ((TwoBiteFinalPairs X).image (fun e => (e.2, e.1)))).card : ℝ) = ((TwoBiteFinalPairs X).card : ℝ) + (((TwoBiteFinalPairs X).image (fun e => (e.2, e.1))).card : ℝ) := by
    exact_mod_cast Finset.card_union_of_disjoint h_disj
  have h_le : (((TwoBiteFinalPairs X) ∪ ((TwoBiteFinalPairs X).image (fun e => (e.2, e.1)))).card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub
  calc
    ((TwoBiteFinalPairs X).card : ℝ) = (1 / 2 : ℝ) * (2 * ((TwoBiteFinalPairs X).card : ℝ)) := by ring
    _ = (1 / 2 : ℝ) * (((TwoBiteFinalPairs X).card : ℝ) + ((TwoBiteFinalPairs X).card : ℝ)) := by ring
    _ = (1 / 2 : ℝ) * (((TwoBiteFinalPairs X).card : ℝ) + (((TwoBiteFinalPairs X).image (fun e => (e.2, e.1))).card : ℝ)) := by rw [h_card_eq]
    _ = (1 / 2 : ℝ) * (((TwoBiteFinalPairs X) ∪ ((TwoBiteFinalPairs X).image (fun e => (e.2, e.1)))).card : ℝ) := by rw [h_union]
    _ ≤ (1 / 2 : ℝ) * ((X ×ˢ X).card : ℝ) := mul_le_mul_of_nonneg_left h_le (by norm_num)
    _ = (X.card : ℝ) ^ 2 / 2 := by rw [h_card_prod]; ring
