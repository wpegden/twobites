import Tablet.FixedSetProductModelCoordinateMarginal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped Classical
open scoped BigOperators

-- [TABLET NODE: FixedSetProductModelPairUnionBound]

theorem FixedSetProductModelPairUnionBound {n : ℕ} (I : Finset (Fin n))
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1) (u w : Fin n) (hu : u ∈ I) (hw : w ∈ I)
    (h_distinct : (π u).1 ≠ (π w).1 ∧ (π u).2 ≠ (π w).2) :
    let r_prod := 2 * m_sub
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
          (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2)
      then Finset.univ.prod (fun i => q (v i)) else 0) ≤ 2 * m_sub * p_sub ^ 2 := by
-- BODY
  intro r_prod P_R P_B q
  have h_bound : ∀ v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub),
      (if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
          (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2) then 1 else (0 : ℝ)) ≤
      (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then 1 else (0 : ℝ)) +
      (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then 1 else (0 : ℝ)) := by
    intro v
    split_ifs with h
    · rcases h with ⟨x, hx1, hx2, hx3⟩ | ⟨x, hx1, hx2, hx3⟩
      · have h_le_1 : (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0 := by
          let f := fun y : Fin r_prod => if (π u).1 ∈ (v y).1 ∧ (π w).1 ∈ (v y).1 then (1 : ℝ) else 0
          change f x ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin r_prod => y.val < m_sub), f y
          apply Finset.single_le_sum
          · intro y _
            dsimp [f]
            split_ifs <;> norm_num
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx1⟩
        have h_pos : (0 : ℝ) ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0 := by
          apply Finset.sum_nonneg
          intro y _
          split_ifs <;> norm_num
        have h_eq_1 : (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) = 1 := if_pos ⟨hx2, hx3⟩
        linarith
      · have h_le_1 : (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0 := by
          let f := fun y : Fin r_prod => if (π u).2 ∈ (v y).2 ∧ (π w).2 ∈ (v y).2 then (1 : ℝ) else 0
          change f x ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin r_prod => m_sub ≤ y.val), f y
          apply Finset.single_le_sum
          · intro y _
            dsimp [f]
            split_ifs <;> norm_num
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx1⟩
        have h_pos : (0 : ℝ) ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0 := by
          apply Finset.sum_nonneg
          intro y _
          split_ifs <;> norm_num
        have h_eq_1 : (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) = 1 := if_pos ⟨hx2, hx3⟩
        linarith
    · apply add_nonneg <;> apply Finset.sum_nonneg <;> intro y _ <;> split_ifs <;> norm_num

  have h_prob_nonneg : ∀ v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub), (0 : ℝ) ≤ Finset.univ.prod (fun i => q (v i)) := by
    intro v
    apply Finset.prod_nonneg
    intro i _
    change 0 ≤ FixedSetProductModelMassFn p_sub P_R P_B (v i)
    unfold FixedSetProductModelMassFn
    split_ifs
    · apply mul_nonneg <;> apply mul_nonneg <;> apply pow_nonneg <;> linarith
    · exact le_refl 0

  have h_main_le : Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
          (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2) then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))
      ≤ Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => ((∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then 1 else (0 : ℝ)) +
                                   (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then 1 else (0 : ℝ))) *
                                  Finset.univ.prod (fun i => q (v i))) := by
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_right (h_bound v) (h_prob_nonneg v)

  have h_rewrite_sum : Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => ((∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then 1 else (0 : ℝ)) +
                                   (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then 1 else (0 : ℝ))) *
                                  Finset.univ.prod (fun i => q (v i))) =
      (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) +
      (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) := by
    have h_step1 : Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => ((∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then 1 else (0 : ℝ)) +
                                   (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then 1 else (0 : ℝ))) *
                                  Finset.univ.prod (fun i => q (v i))) =
      Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i))) +
                                   (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [h_step1, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_comm (s := Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val))]

  have h_inner_R : ∀ x, Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i))) =
      if {(π u).1, (π w).1} ⊆ P_R ∧ (∅ : Finset (Fin m_sub)) ⊆ P_B then p_sub ^ (({(π u).1, (π w).1} : Finset (Fin m_sub)).card + (∅ : Finset (Fin m_sub)).card) else 0 := by
    intro x
    have h_rewrite : ∀ v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub), (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)) =
      if {(π u).1, (π w).1} ⊆ (v x).1 ∧ (∅ : Finset (Fin m_sub)) ⊆ (v x).2 then Finset.univ.prod (fun i => q (v i)) else 0 := by
      intro v
      have h_eq : ((π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ↔ (({(π u).1, (π w).1} : Finset (Fin m_sub)) ⊆ (v x).1 ∧ (∅ : Finset (Fin m_sub)) ⊆ (v x).2) := by
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      by_cases h : ((π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1)
      · rw [if_pos h, if_pos (h_eq.mp h), one_mul]
      · rw [if_neg h, if_neg (h_eq.not.mp h), zero_mul]
    rw [Finset.sum_congr rfl (fun v _ => h_rewrite v)]
    exact FixedSetProductModelCoordinateMarginal p_sub P_R P_B hp0 hp1 x {(π u).1, (π w).1} ∅

  have h_inner_B : ∀ x, Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i))) =
      if (∅ : Finset (Fin m_sub)) ⊆ P_R ∧ {(π u).2, (π w).2} ⊆ P_B then p_sub ^ (((∅ : Finset (Fin m_sub)).card : ℕ) + ({(π u).2, (π w).2} : Finset (Fin m_sub)).card) else 0 := by
    intro x
    have h_rewrite : ∀ v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub), (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)) =
      if (∅ : Finset (Fin m_sub)) ⊆ (v x).1 ∧ {(π u).2, (π w).2} ⊆ (v x).2 then Finset.univ.prod (fun i => q (v i)) else 0 := by
      intro v
      have h_eq : ((π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2) ↔ ((∅ : Finset (Fin m_sub)) ⊆ (v x).1 ∧ ({(π u).2, (π w).2} : Finset (Fin m_sub)) ⊆ (v x).2) := by
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      by_cases h : ((π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2)
      · rw [if_pos h, if_pos (h_eq.mp h), one_mul]
      · rw [if_neg h, if_neg (h_eq.not.mp h), zero_mul]
    rw [Finset.sum_congr rfl (fun v _ => h_rewrite v)]
    exact FixedSetProductModelCoordinateMarginal p_sub P_R P_B hp0 hp1 x ∅ {(π u).2, (π w).2}

  have h_card_R : (({(π u).1, (π w).1} : Finset (Fin m_sub)).card + (∅ : Finset (Fin m_sub)).card) = 2 := by
    simp
    apply Finset.card_pair
    exact h_distinct.1

  have h_card_B : (((∅ : Finset (Fin m_sub)).card : ℕ) + ({(π u).2, (π w).2} : Finset (Fin m_sub)).card) = 2 := by
    simp
    apply Finset.card_pair
    exact h_distinct.2

  have h_val_R : (if {(π u).1, (π w).1} ⊆ P_R ∧ (∅ : Finset (Fin m_sub)) ⊆ P_B then p_sub ^ (({(π u).1, (π w).1} : Finset (Fin m_sub)).card + (∅ : Finset (Fin m_sub)).card) else 0) ≤ p_sub ^ 2 := by
    rw [h_card_R]
    split_ifs
    · exact le_refl (p_sub ^ 2)
    · apply pow_nonneg hp0

  have h_val_B : (if (∅ : Finset (Fin m_sub)) ⊆ P_R ∧ {(π u).2, (π w).2} ⊆ P_B then p_sub ^ (((∅ : Finset (Fin m_sub)).card : ℕ) + ({(π u).2, (π w).2} : Finset (Fin m_sub)).card) else 0) ≤ p_sub ^ 2 := by
    rw [h_card_B]
    split_ifs
    · exact le_refl (p_sub ^ 2)
    · apply pow_nonneg hp0

  have h_card_R_set : (Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub)).card = m_sub := by
    have hr : r_prod = 2 * m_sub := rfl
    have h_lt : ∀ i : Fin m_sub, i.val < 2 * m_sub := fun i => by linarith [i.isLt, hr]
    let f : Fin m_sub ↪ Fin r_prod := ⟨fun i => ⟨i.val, h_lt i⟩, fun i j hij => Fin.ext (Fin.mk.inj hij)⟩
    have h_im : Finset.univ.image f = Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, rfl⟩
        exact y.isLt
      · rintro hx
        exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    rw [← h_im, Finset.card_image_of_injective Finset.univ f.injective, Finset.card_univ, Fintype.card_fin]

  have h_card_B_set : (Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val)).card = m_sub := by
    have hr : r_prod = 2 * m_sub := rfl
    have h_lt : ∀ i : Fin m_sub, i.val + m_sub < 2 * m_sub := fun i => by linarith [i.isLt, hr]
    let f : Fin m_sub ↪ Fin r_prod := ⟨fun i => ⟨i.val + m_sub, h_lt i⟩, fun i j hij => by
      have h_inj : i.val + m_sub = j.val + m_sub := Fin.mk.inj hij
      exact Fin.ext (Nat.add_right_cancel h_inj)⟩
    have h_im : Finset.univ.image f = Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, h_eq⟩
        have h_val_eq : y.val + m_sub = x.val := congrArg Fin.val h_eq
        omega
      · rintro hx
        have h_bound1 : x.val < 2 * m_sub := by linarith [x.isLt, hr]
        have h_bound2 : x.val - m_sub < m_sub := by omega
        use ⟨x.val - m_sub, h_bound2⟩
        apply Fin.ext
        dsimp
        exact Nat.sub_add_cancel hx
    rw [← h_im, Finset.card_image_of_injective Finset.univ f.injective, Finset.card_univ, Fintype.card_fin]

  have h_le_R : (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) ≤ m_sub * p_sub ^ 2 := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), (if {(π u).1, (π w).1} ⊆ P_R ∧ (∅ : Finset (Fin m_sub)) ⊆ P_B then p_sub ^ (({(π u).1, (π w).1} : Finset (Fin m_sub)).card + (∅ : Finset (Fin m_sub)).card) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact h_inner_R x
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), p_sub ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact h_val_R
      _ = (Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub)).card * p_sub ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = m_sub * p_sub ^ 2 := by
        rw [h_card_R_set]

  have h_le_B : (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) ≤ m_sub * p_sub ^ 2 := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), (if (∅ : Finset (Fin m_sub)) ⊆ P_R ∧ {(π u).2, (π w).2} ⊆ P_B then p_sub ^ (((∅ : Finset (Fin m_sub)).card : ℕ) + ({(π u).2, (π w).2} : Finset (Fin m_sub)).card) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact h_inner_B x
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), p_sub ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact h_val_B
      _ = (Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val)).card * p_sub ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = m_sub * p_sub ^ 2 := by
        rw [h_card_B_set]

  have h_final : (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => x.val < m_sub), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) +
      (∑ x ∈ Finset.univ.filter (fun x : Fin r_prod => m_sub ≤ x.val), Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2 then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i)))) ≤
      2 * m_sub * p_sub ^ 2 := by
    calc
      _ ≤ m_sub * p_sub ^ 2 + m_sub * p_sub ^ 2 := add_le_add h_le_R h_le_B
      _ = 2 * m_sub * p_sub ^ 2 := by ring

  have h_goal_eq : Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
          (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2)
      then Finset.univ.prod (fun i => q (v i)) else 0) =
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) => (if (∃ x : Fin r_prod, x.val < m_sub ∧ (π u).1 ∈ (v x).1 ∧ (π w).1 ∈ (v x).1) ∨
          (∃ x : Fin r_prod, m_sub ≤ x.val ∧ (π u).2 ∈ (v x).2 ∧ (π w).2 ∈ (v x).2) then (1 : ℝ) else 0) * Finset.univ.prod (fun i => q (v i))) := by
    apply Finset.sum_congr rfl
    intro v _
    split_ifs
    · rw [one_mul]
    · rw [zero_mul]

  rw [h_goal_eq]
  linarith
