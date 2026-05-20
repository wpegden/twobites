import Tablet.FixedSetProductModelMass
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

open scoped Classical
open scoped BigOperators
open Finset

-- [TABLET NODE: FixedSetProductModelCoordinateMarginal]

theorem FixedSetProductModelCoordinateMarginal {m_sub : ℕ} (p_sub : ℝ) (P_R P_B : Finset (Fin m_sub))
    (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1) (x : Fin (2 * m_sub))
    (A_R A_B : Finset (Fin m_sub)) :
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let r_prod := 2 * m_sub
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      if A_R ⊆ (v x).1 ∧ A_B ⊆ (v x).2 then Finset.univ.prod (fun i => q (v i)) else 0) =
      if A_R ⊆ P_R ∧ A_B ⊆ P_B then p_sub ^ (A_R.card + A_B.card) else 0 := by
-- BODY
  intro q r_prod
  let f : Fin r_prod → (Finset (Fin m_sub) × Finset (Fin m_sub)) → ℝ :=
    fun i a => if i = x then (if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0) else q a

  have h1 : ∀ v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub),
      (if A_R ⊆ (v x).1 ∧ A_B ⊆ (v x).2 then ∏ i, q (v i) else 0) = ∏ i, f i (v i) := by
    intro v
    by_cases h : A_R ⊆ (v x).1 ∧ A_B ⊆ (v x).2
    · rw [if_pos h]
      have : (∏ i, if i = x then (if A_R ⊆ (v i).1 ∧ A_B ⊆ (v i).2 then q (v i) else 0) else q (v i)) = ∏ i, q (v i) := by
        apply prod_congr rfl
        intro i hi
        by_cases hix : i = x
        · rw [if_pos hix, hix]
          rw [if_pos h]
        · rw [if_neg hix]
      exact this.symm
    · rw [if_neg h]
      have : (∏ i, if i = x then (if A_R ⊆ (v i).1 ∧ A_B ⊆ (v i).2 then q (v i) else 0) else q (v i)) = 0 := by
        apply prod_eq_zero (mem_univ x)
        rw [if_pos rfl, if_neg h]
      exact this.symm

  rw [sum_congr rfl (fun v _ => h1 v)]
  rw [← Fintype.prod_sum]
  have h2 : (∏ i, ∑ a, f i a) = (∑ a, f x a) * ∏ i ∈ univ.erase x, ∑ a, f i a := by
    rw [← mul_prod_erase univ _ (mem_univ x)]
  rw [h2]

  have h_sum_q : ∑ a, q a = 1 := (FixedSetProductModelMass p_sub hp0 hp1 P_R P_B).2

  have h_sum_f_other : ∀ i ∈ univ.erase x, ∑ a, f i a = 1 := by
    intro i hi
    have : i ≠ x := by
      intro h_eq
      subst h_eq
      simp at hi
    have h_eq_q : ∀ a, f i a = q a := by
      intro a
      simp [f, this]
    rw [sum_congr rfl (fun a _ => h_eq_q a)]
    exact h_sum_q

  have h_prod_one : (∏ i ∈ univ.erase x, ∑ a, f i a) = 1 := by
    rw [prod_congr rfl (fun i hi => h_sum_f_other i hi)]
    exact prod_const_one

  rw [h_prod_one, mul_one]

  have h_fx : ∀ a, f x a = if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0 := by
    intro a
    simp [f]
  rw [sum_congr rfl (fun a _ => h_fx a)]

  -- Now we just need to evaluate `∑ a, if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0`
  -- We restrict the sum to the support of q
  have h_support : ∀ a, a ∉ (P_R.powerset ×ˢ P_B.powerset) → q a = 0 := by
    intro a ha
    change FixedSetProductModelMassFn p_sub P_R P_B a = 0
    unfold FixedSetProductModelMassFn
    split_ifs with h
    · exfalso
      apply ha
      simp [h]
    · rfl

  have h_sum_restrict : (∑ a, if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0) =
      ∑ a ∈ P_R.powerset ×ˢ P_B.powerset, if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0 := by
    rw [← sum_subset (subset_univ (P_R.powerset ×ˢ P_B.powerset))]
    intro a _ ha
    have : q a = 0 := h_support a ha
    simp [this]
  rw [h_sum_restrict]

  have h_q_on : ∀ a ∈ P_R.powerset ×ˢ P_B.powerset, q a =
      (p_sub ^ a.1.card * (1 - p_sub) ^ (P_R.card - a.1.card)) *
      (p_sub ^ a.2.card * (1 - p_sub) ^ (P_B.card - a.2.card)) := by
    intro a ha
    simp at ha
    change FixedSetProductModelMassFn p_sub P_R P_B a = _
    unfold FixedSetProductModelMassFn
    rw [if_pos ha]

  have h_sum_factor : (∑ a ∈ P_R.powerset ×ˢ P_B.powerset, if A_R ⊆ a.1 ∧ A_B ⊆ a.2 then q a else 0) =
      (∑ a1 ∈ P_R.powerset, if A_R ⊆ a1 then p_sub ^ a1.card * (1 - p_sub) ^ (P_R.card - a1.card) else 0) *
      (∑ a2 ∈ P_B.powerset, if A_B ⊆ a2 then p_sub ^ a2.card * (1 - p_sub) ^ (P_B.card - a2.card) else 0) := by
    rw [sum_product]
    have h_inner : ∀ a1 ∈ P_R.powerset, (∑ a2 ∈ P_B.powerset, if A_R ⊆ a1 ∧ A_B ⊆ a2 then q (a1, a2) else 0) =
        (if A_R ⊆ a1 then p_sub ^ a1.card * (1 - p_sub) ^ (P_R.card - a1.card) else 0) *
        (∑ a2 ∈ P_B.powerset, if A_B ⊆ a2 then p_sub ^ a2.card * (1 - p_sub) ^ (P_B.card - a2.card) else 0) := by
      intro a1 ha1
      by_cases hAR : A_R ⊆ a1
      · rw [if_pos hAR]
        rw [mul_sum]
        apply sum_congr rfl
        intro a2 ha2
        by_cases hAB : A_B ⊆ a2
        · rw [if_pos hAB, if_pos ⟨hAR, hAB⟩]
          have h_in : (a1, a2) ∈ P_R.powerset ×ˢ P_B.powerset := by
            simp [ha1, ha2]
          exact h_q_on (a1, a2) h_in
        · rw [if_neg hAB, if_neg (fun h : A_R ⊆ a1 ∧ A_B ⊆ a2 => hAB h.2)]
          simp
      · rw [if_neg hAR]
        simp
        apply sum_eq_zero
        intro a2 _
        have : ¬ (A_R ⊆ a1 ∧ A_B ⊆ a2) := fun h => hAR h.1
        rw [if_neg this]
    rw [sum_congr rfl h_inner, ← sum_mul]

  rw [h_sum_factor]

  have one_coord_sum : ∀ P A : Finset (Fin m_sub),
      (∑ a ∈ P.powerset, if A ⊆ a then p_sub ^ a.card * (1 - p_sub) ^ (P.card - a.card) else 0) =
      if A ⊆ P then p_sub ^ A.card else 0 := by
    intro P A
    by_cases h : A ⊆ P
    · rw [if_pos h]
      have h_eq : (∑ a ∈ P.powerset, if A ⊆ a then p_sub ^ a.card * (1 - p_sub) ^ (P.card - a.card) else 0) =
        ∑ a ∈ P.powerset.filter (A ⊆ ·), p_sub ^ a.card * (1 - p_sub) ^ (P.card - a.card) := by
        rw [sum_filter]
      rw [h_eq]
      have h_bij : (∑ T ∈ (P \ A).powerset, p_sub ^ (A.card + T.card) * (1 - p_sub) ^ ((P \ A).card - T.card)) =
        ∑ a ∈ P.powerset.filter (A ⊆ ·), p_sub ^ a.card * (1 - p_sub) ^ (P.card - a.card) := by
        apply sum_bij (fun T _ => A ∪ T)
        · intro T hT
          rw [mem_filter, mem_powerset]
          rw [mem_powerset] at hT
          refine ⟨union_subset h (Subset.trans hT sdiff_subset), subset_union_left⟩
        · intro T1 hT1 T2 hT2 h_eq_union
          rw [mem_powerset] at hT1 hT2
          have h_disj1 : Disjoint A T1 := disjoint_sdiff.mono_right hT1
          have h_disj2 : Disjoint A T2 := disjoint_sdiff.mono_right hT2
          have h1 : (A ∪ T1) \ A = T1 := by rw [union_sdiff_left, sdiff_eq_self_of_disjoint h_disj1.symm]
          have h2 : (A ∪ T2) \ A = T2 := by rw [union_sdiff_left, sdiff_eq_self_of_disjoint h_disj2.symm]
          rw [← h1, h_eq_union, h2]
        · intro a ha
          rw [mem_filter, mem_powerset] at ha
          use a \ A
          refine ⟨?_, ?_⟩
          · rw [mem_powerset]
            exact sdiff_subset_sdiff ha.1 (Subset.refl A)
          · rw [union_sdiff_of_subset ha.2]
        · intro T hT
          rw [mem_powerset] at hT
          have h_disj : Disjoint A T := disjoint_sdiff.mono_right hT
          have h_card : (A ∪ T).card = A.card + T.card := card_union_of_disjoint h_disj
          rw [h_card]
          congr 2
          have h_sub_eq : P.card - (A.card + T.card) = (P \ A).card - T.card := by
            rw [card_sdiff_of_subset h]
            omega
          rw [h_sub_eq]
      rw [← h_bij]
      have h_pull : (∑ T ∈ (P \ A).powerset, p_sub ^ (A.card + T.card) * (1 - p_sub) ^ ((P \ A).card - T.card)) =
        p_sub ^ A.card * ∑ T ∈ (P \ A).powerset, p_sub ^ T.card * (1 - p_sub) ^ ((P \ A).card - T.card) := by
        simp_rw [pow_add, mul_assoc, ← mul_sum]
      rw [h_pull]
      have h_binom : (∑ T ∈ (P \ A).powerset, p_sub ^ T.card * (1 - p_sub) ^ ((P \ A).card - T.card)) = 1 := by
        let P' := P \ A
        have h_sum_inner : (∑ T ∈ P'.powerset, p_sub ^ T.card * (1 - p_sub) ^ (P'.card - T.card)) = 1 := by
          rw [sum_powerset]
          have h_inner (j : ℕ) : ∑ T ∈ P'.powersetCard j, p_sub ^ T.card * (1 - p_sub) ^ (P'.card - T.card) =
            (P'.card.choose j : ℝ) * (p_sub ^ j * (1 - p_sub) ^ (P'.card - j)) := by
            have h_body : ∀ T ∈ P'.powersetCard j, p_sub ^ T.card * (1 - p_sub) ^ (P'.card - T.card) = p_sub ^ j * (1 - p_sub) ^ (P'.card - j) := by
              intro T hT
              rw [mem_powersetCard] at hT
              simp [hT.2]
            rw [sum_congr rfl h_body]
            rw [sum_const, card_powersetCard, nsmul_eq_mul]
          simp_rw [h_inner]
          have h_match : (∑ j ∈ range (P'.card + 1), (P'.card.choose j : ℝ) * (p_sub ^ j * (1 - p_sub) ^ (P'.card - j))) =
                         (∑ j ∈ range (P'.card + 1), p_sub ^ j * (1 - p_sub) ^ (P'.card - j) * (P'.card.choose j : ℝ)) := by
            apply sum_congr rfl
            intro j _
            rw [mul_comm]
          rw [h_match]
          rw [← add_pow p_sub (1 - p_sub) P'.card]
          simp
        exact h_sum_inner
      rw [h_binom, mul_one]
    · rw [if_neg h]
      apply sum_eq_zero
      intro a ha
      by_cases hA : A ⊆ a
      · rw [if_pos hA]
        rw [mem_powerset] at ha
        exfalso
        exact h (Subset.trans hA ha)
      · rw [if_neg hA]

  rw [one_coord_sum P_R A_R, one_coord_sum P_B A_B]
  by_cases h_all : A_R ⊆ P_R ∧ A_B ⊆ P_B
  · rw [if_pos h_all, if_pos h_all.1, if_pos h_all.2]
    rw [pow_add]
  · rw [if_neg h_all]
    by_cases hR : A_R ⊆ P_R
    · rw [if_pos hR, if_neg (fun h => h_all ⟨hR, h⟩)]
      simp
    · rw [if_neg hR]
      simp
