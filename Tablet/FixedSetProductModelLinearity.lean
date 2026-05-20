import Tablet.FixedSetProductModelVar
import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelMass
import Tablet.RealChooseTwo
import Tablet.FixedSetFakeGraph
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteX
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteBaseVertex
import Tablet.FinsetCardFilterLt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

open scoped Classical
open scoped BigOperators

-- [TABLET NODE: FixedSetProductModelLinearity]

theorem FixedSetProductModelLinearity {n : ℕ} (I : Finset (Fin n)) (ε : ℝ)
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1)
    (C : ℝ) (hC : C = RealChooseTwo I.card) (B : ℝ)
    (hB : 0 ≤ B)
    (h_pair_bound : ∀ u w : Fin n, u ∈ I → w ∈ I → (π u).1 ≠ (π w).1 → (π u).2 ≠ (π w).2 →
      let r_prod := 2 * m_sub
      let P_R := I.image (fun u => (π u).1)
      let P_B := I.image (fun u => (π u).2)
      let q := FixedSetProductModelMassFn p_sub P_R P_B
      Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
        if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
            (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2)
        then Finset.univ.prod (fun i => q (v i)) else 0) ≤ B) :
    let r_prod := 2 * m_sub
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      (Finset.univ.prod (fun i => q (v i))) * Z_prod v) ≤ C * B := by
-- BODY
  intro r_prod P_R P_B q Z_prod
  -- 1. Mass nonnegativity
  have hq_nonneg : ∀ v_val, 0 ≤ q v_val := by
    intro v_val
    exact (FixedSetProductModelMass p_sub hp0 hp1 P_R P_B).1 v_val
  have hW_nonneg : ∀ (v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub)), 0 ≤ Finset.univ.prod (fun i => q (v i)) := by
    intro v
    apply Finset.prod_nonneg
    intro i _
    apply hq_nonneg

  -- 2. Pointwise bound for Z_prod
  let Pairs := (I.product I).filter (fun e => (e.1.val < e.2.val))
  let PairEvent (e : Fin n × Fin n) (v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub)) : Prop :=
      (∃ x : Fin r_prod, x.val < m_sub ∧ (π e.1).1 ∈ (v x).1 ∧ (π e.2).1 ∈ (v x).1) ∨
      (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π e.1).2 ∈ (v x).2 ∧ (π e.2).2 ∈ (v x).2)
  let DistinctProj (e : Fin n × Fin n) : Prop :=
      (π e.1).1 ≠ (π e.2).1 ∧ (π e.1).2 ≠ (π e.2).2

  have hZ_bound : ∀ v, Z_prod v ≤ (Pairs.filter (fun e => DistinctProj e ∧ PairEvent e v)).card := by
    intro v
    subst Z_prod
    unfold FixedSetProductModelVar
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro e he
    have he_mem := Finset.mem_filter.mp he
    obtain ⟨x, hx_mem, he_final⟩ := Finset.mem_biUnion.mp he_mem.1
    have he_distinct := he_mem.2
    apply Finset.mem_filter.mpr
    constructor
    · -- e ∈ Pairs
      unfold TwoBiteFinalPairs TwoBitePairsInSet at he_final
      have he_final_mem := Finset.mem_filter.mp he_final
      let ⟨he_prod, he_rank⟩ := he_final_mem
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        have he_prod_mem := Finset.mem_product.mp he_prod
        have he1_in_X := he_prod_mem.1
        have he2_in_X := he_prod_mem.2
        simp only [TwoBiteX, Finset.mem_filter] at he1_in_X he2_in_X
        exact ⟨he1_in_X.1, he2_in_X.1⟩
      · exact he_rank
    · -- DistinctProj e ∧ PairEvent e v
      constructor
      · exact he_distinct
      · -- PairEvent e v
        dsimp [PairEvent]
        have he_final_mem := Finset.mem_filter.mp he_final
        have he_prod := he_final_mem.1
        have he_prod_mem := Finset.mem_product.mp he_prod
        have he1_in_X := he_prod_mem.1
        have he2_in_X := he_prod_mem.2
        cases x with
        | inl r =>
          left
          have hr_lt : r.val < 2 * m_sub := by have := r.isLt; omega
          use ⟨r.val, hr_lt⟩
          constructor
          · have hr_lt_m : r.val < m_sub := r.isLt
            exact hr_lt_m
          · have hr_not_in : r ∉ I.image (fun u => (π u).1) := by
              have h_not_in := (Finset.mem_sdiff.mp hx_mem).2
              intro hr_mem
              apply h_not_in
              apply Finset.mem_union_left
              apply Finset.mem_image_of_mem
              exact hr_mem
            simp only [TwoBiteX, TwoBiteLiftedNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at he1_in_X he2_in_X
            have he1_adj := he1_in_X.2
            have he2_adj := he2_in_X.2
            simp only [FixedSetFakeGraph, TwoBiteRedGraph, TwoBiteRedProjection, TwoBiteEmbedding] at he1_adj he2_adj
            -- Manual destruction of Adj
            have h1 : (π e.1).1 ∈ (v ⟨r.val, hr_lt⟩).1 := by
              cases he1_adj with
              | inl h => exact False.elim (hr_not_in h.1)
              | inr h => exact h.2.2
            have h2 : (π e.2).1 ∈ (v ⟨r.val, hr_lt⟩).1 := by
              cases he2_adj with
              | inl h => exact False.elim (hr_not_in h.1)
              | inr h => exact h.2.2
            exact ⟨h1, h2⟩
        | inr b =>
          right
          have hb_lt : b.val + m_sub < 2 * m_sub := by have := b.isLt; omega
          use ⟨b.val + m_sub, hb_lt⟩
          constructor
          · have hb_m : m_sub ≤ b.val + m_sub := by omega
            exact hb_m
          · have hb_not_in : b ∉ I.image (fun u => (π u).2) := by
              have h_not_in := (Finset.mem_sdiff.mp hx_mem).2
              intro hb_mem
              apply h_not_in
              apply Finset.mem_union_right
              apply Finset.mem_image_of_mem
              exact hb_mem
            simp only [TwoBiteX, TwoBiteLiftedNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at he1_in_X he2_in_X
            have he1_adj := he1_in_X.2
            have he2_adj := he2_in_X.2
            simp only [FixedSetFakeGraph, TwoBiteBlueGraph, TwoBiteBlueProjection, TwoBiteEmbedding] at he1_adj he2_adj
            have h1 : (π e.1).2 ∈ (v ⟨b.val + m_sub, hb_lt⟩).2 := by
              cases he1_adj with
              | inl h => exact False.elim (hb_not_in h.1)
              | inr h => exact h.2.2
            have h2 : (π e.2).2 ∈ (v ⟨b.val + m_sub, hb_lt⟩).2 := by
              cases he2_adj with
              | inl h => exact False.elim (hb_not_in h.1)
              | inr h => exact h.2.2
            exact ⟨h1, h2⟩

  -- 3. Summation exchange
  let W (v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub)) := Finset.univ.prod (fun i => q (v i))
  have h_total : ∑ v, W v * Z_prod v ≤ ∑ e ∈ Pairs, ∑ v, if DistinctProj e ∧ PairEvent e v then W v else 0 := by
    apply (Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hZ_bound v) (hW_nonneg v))).trans
    simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro v _
    by_cases h_cond : DistinctProj e ∧ PairEvent e v
    · simp [h_cond]
      change (Finset.univ.prod fun i => q (v i)) = W v
      rfl
    · simp [h_cond]

  -- 4. Apply pair bound
  have h_pair_sum : ∀ e ∈ Pairs, (∑ v, if DistinctProj e ∧ PairEvent e v then W v else 0) ≤ B := by
    intro e he
    have he1 : e.1 ∈ I := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    have he2 : e.2 ∈ I := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
    by_cases h_proj : DistinctProj e
    · have h_eq : (∑ v, if DistinctProj e ∧ PairEvent e v then W v else 0) = ∑ v, if PairEvent e v then W v else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h_ev : PairEvent e v
        · simp [h_proj, h_ev]
        · simp [h_ev]
      rw [h_eq]
      apply h_pair_bound e.1 e.2 he1 he2 h_proj.1 h_proj.2
    · have h_eq : (∑ v, if DistinctProj e ∧ PairEvent e v then W v else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [h_proj]
      rw [h_eq]
      exact hB

  -- 5. Final summation
  have h_card_pairs : (Pairs.card : ℝ) = I.card.choose 2 := by
    have h_nat : Pairs.card = I.card.choose 2 := by
      show ((I.product I).filter (fun e => (e.1.val < e.2.val))).card = I.card.choose 2
      apply FinsetCardFilterLt
    rw [h_nat]

  apply h_total.trans
  apply (Finset.sum_le_sum (fun e he => h_pair_sum e he)).trans
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hC, RealChooseTwo, h_card_pairs]
  apply le_of_eq
  rw [Nat.cast_choose_two]
