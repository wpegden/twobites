import Tablet.Preamble
import Tablet.TwoBitePairsInSet

-- [TABLET NODE: PairsInSetLeHalfProduct]

lemma PairsInSetLeHalfProduct {α : Type} [DecidableEq α] (rank : α → ℕ) (I : Finset α)
    (p : α × α → Prop) [DecidablePred p]
    (hp_symm : ∀ a b, p (a, b) → p (b, a)) :
    2 * (((TwoBitePairsInSet rank I).filter p).card : ℝ) ≤ (((I.product I).filter p).card : ℝ) := by
-- BODY
  have h_disj : Disjoint ((TwoBitePairsInSet rank I).filter p) (((TwoBitePairsInSet rank I).filter p).image (fun e => (e.2, e.1))) := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    rw [Finset.mem_filter, TwoBitePairsInSet, Finset.mem_filter] at hx1
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨y, hy, hy_eq⟩
    rw [Finset.mem_filter, TwoBitePairsInSet, Finset.mem_filter] at hy
    have hx_eq : x = (y.2, y.1) := hy_eq.symm
    rw [hx_eq] at hx1
    have h1 := hx1.1.2
    have h2 := hy.1.2
    linarith
  have h_sub : ((TwoBitePairsInSet rank I).filter p) ∪ (((TwoBitePairsInSet rank I).filter p).image (fun e => (e.2, e.1))) ⊆ (I.product I).filter p := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with h1 | h2
    · rw [Finset.mem_filter, TwoBitePairsInSet, Finset.mem_filter] at h1
      exact Finset.mem_filter.mpr ⟨h1.1.1, h1.2⟩
    · rw [Finset.mem_image] at h2
      rcases h2 with ⟨y, hy, hy_eq⟩
      rw [Finset.mem_filter, TwoBitePairsInSet, Finset.mem_filter] at hy
      rw [← hy_eq]
      have hy_prod := Finset.mem_product.mp hy.1.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy_prod.2, hy_prod.1⟩, hp_symm _ _ hy.2⟩
  have h_card_eq : ((((TwoBitePairsInSet rank I).filter p).image (fun e => (e.2, e.1))).card : ℝ) = (((TwoBitePairsInSet rank I).filter p).card : ℝ) := by
    have h_inj : Set.InjOn (fun e : α × α => (e.2, e.1)) ((TwoBitePairsInSet rank I).filter p) := by
      intro x _ y _ hxy
      ext
      · exact congrArg Prod.snd hxy
      · exact congrArg Prod.fst hxy
    exact_mod_cast Finset.card_image_of_injOn h_inj
  calc
    2 * (((TwoBitePairsInSet rank I).filter p).card : ℝ) = (((TwoBitePairsInSet rank I).filter p).card : ℝ) + (((TwoBitePairsInSet rank I).filter p).card : ℝ) := by ring
    _ = (((TwoBitePairsInSet rank I).filter p).card : ℝ) + ((((TwoBitePairsInSet rank I).filter p).image (fun e => (e.2, e.1))).card : ℝ) := by rw [h_card_eq]
    _ = (((((TwoBitePairsInSet rank I).filter p) ∪ (((TwoBitePairsInSet rank I).filter p).image (fun e => (e.2, e.1))))).card : ℝ) := by exact_mod_cast (Finset.card_union_of_disjoint h_disj).symm
    _ ≤ (((I.product I).filter p).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
