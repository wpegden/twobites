import Tablet.FixedSetProductModelMassFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

-- [TABLET NODE: FixedSetProductModelMass]

open scoped BigOperators
open Finset

theorem FixedSetProductModelMass {m_sub : ℕ} (p_sub : ℝ) (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1)
    (P_R P_B : Finset (Fin m_sub)) :
    (∀ a, 0 ≤ FixedSetProductModelMassFn p_sub P_R P_B a) ∧
    Finset.univ.sum (FixedSetProductModelMassFn p_sub P_R P_B) = 1 := by
-- BODY
  constructor
  · intro a
    unfold FixedSetProductModelMassFn
    split_ifs with h
    · rcases h with ⟨hR, hB⟩
      apply mul_nonneg
      · apply mul_nonneg
        · apply pow_nonneg hp0
        · apply pow_nonneg
          linarith
      · apply mul_nonneg
        · apply pow_nonneg hp0
        · apply pow_nonneg
          linarith
    · linarith
  · -- Total mass
    have h_support : ∀ a, a ∉ (P_R.powerset ×ˢ P_B.powerset) → FixedSetProductModelMassFn p_sub P_R P_B a = 0 := by
      intro a ha
      unfold FixedSetProductModelMassFn
      split_ifs with h
      · exfalso
        apply ha
        simp at h
        simp [h]
      · rfl
    rw [← sum_subset (subset_univ (P_R.powerset ×ˢ P_B.powerset)) (fun a _ ha => h_support a ha)]
    unfold FixedSetProductModelMassFn
    have h_in : ∀ a ∈ (P_R.powerset ×ˢ P_B.powerset), a.1 ⊆ P_R ∧ a.2 ⊆ P_B := by
      intro a ha
      simp at ha
      exact ha
    rw [sum_congr rfl (fun a ha => if_pos (h_in a ha))]
    -- Sum factors
    rw [sum_product]
    dsimp
    rw [← sum_mul_sum]
    -- Both sums are 1
    let f (P : Finset (Fin m_sub)) (A : Finset (Fin m_sub)) := p_sub ^ A.card * (1 - p_sub) ^ (P.card - A.card)
    have h_sum (P : Finset (Fin m_sub)) : ∑ A ∈ P.powerset, f P A = 1 := by
      rw [sum_powerset]
      have h_inner (j : ℕ) : ∑ A ∈ P.powersetCard j, f P A = (P.card.choose j : ℝ) * (p_sub ^ j * (1 - p_sub) ^ (P.card - j)) := by
        have h_body : ∀ A ∈ P.powersetCard j, f P A = p_sub ^ j * (1 - p_sub) ^ (P.card - j) := by
          intro A hA
          rw [mem_powersetCard] at hA
          simp [f, hA.2]
        rw [sum_congr rfl h_body]
        rw [sum_const, card_powersetCard, nsmul_eq_mul]
      simp_rw [h_inner]
      -- Reorder terms to match add_pow
      have h_match : (∑ j ∈ range (P.card + 1), (P.card.choose j : ℝ) * (p_sub ^ j * (1 - p_sub) ^ (P.card - j))) =
                     (∑ j ∈ range (P.card + 1), p_sub ^ j * (1 - p_sub) ^ (P.card - j) * (P.card.choose j : ℝ)) := by
        apply sum_congr rfl
        intro j hj
        rw [mul_comm]
      rw [h_match]
      rw [← add_pow p_sub (1 - p_sub) P.card]
      simp
    rw [h_sum P_R, h_sum P_B]
    simp
