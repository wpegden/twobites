import Tablet.Preamble
import Tablet.OppositeProjectionFallingFactorialBound
import Tablet.OppositeProjectionRowFavorableRatio
import Tablet.OppositeProjectionRowFavorableZero
import Tablet.OppositeProjectionRowInjectionAllCounting
import Tablet.OppositeProjectionRowInjectionGoodCounting

-- [TABLET NODE: OppositeProjectionRowInjectionCounting]

open scoped Classical
open Finset

theorem OppositeProjectionRowInjectionCounting (n m : ℕ) (ρ : Fin n → Fin m)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ;
    let X_good := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v ∈ T, (ϕ v).2 ∈ S) X_all;
    (X_all.card : ℝ) ≠ 0 →
    (X_good.card : ℝ) / (X_all.card : ℝ) ≤ ((S.card : ℝ) / (m : ℝ)) ^ T.card := by
-- BODY
  intro X_all X_good h_all_ne_zero
  let R (i : Fin m) := Finset.filter (fun v => ρ v = i) Finset.univ
  let q (i : Fin m) := (R i).card
  let T_i (i : Fin m) := T ∩ R i
  let h (i : Fin m) := (T_i i).card

  have h_all_card : (X_all.card : ℝ) = ∏ i : Fin m, (Nat.descFactorial m (q i) : ℝ) := OppositeProjectionRowInjectionAllCounting n m ρ

  have hq_le_m : ∀ i, q i ≤ m := by
    intro i
    have h1 : ∏ j : Fin m, (Nat.descFactorial m (q j) : ℝ) ≠ 0 := by
      rw [← h_all_card]
      exact h_all_ne_zero
    have h2 : (Nat.descFactorial m (q i) : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.mp h1 i (Finset.mem_univ i)
    have h3 : Nat.descFactorial m (q i) ≠ 0 := by
      intro hc
      rw [hc] at h2
      simp at h2
    have h4 : ¬ (m < q i) := by
      intro hc
      have h5 : Nat.descFactorial m (q i) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hc
      exact h3 h5
    omega

  have h_good_card : (X_good.card : ℝ) = ∏ i : Fin m, ((Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ)) := OppositeProjectionRowInjectionGoodCounting n m ρ S T

  have h_all_ne_zero_i : ∀ i, (Nat.descFactorial m (q i) : ℝ) ≠ 0 := by
    intro i
    have h1 : ∏ i : Fin m, (Nat.descFactorial m (q i) : ℝ) ≠ 0 := by
      rw [← h_all_card]
      exact h_all_ne_zero
    exact Finset.prod_ne_zero_iff.mp h1 i (Finset.mem_univ i)

  have row_bound : ∀ i, ((Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ)) / (Nat.descFactorial m (q i) : ℝ) ≤ ((S.card : ℝ) / (m : ℝ)) ^ (h i) := by
    intro i
    have h_le_q : h i ≤ q i := by exact Finset.card_le_card Finset.inter_subset_right
    have q_le_m : q i ≤ m := hq_le_m i
    by_cases h_cases : h i ≤ S.card
    · have hr := OppositeProjectionRowFavorableRatio m S.card (h i) (q i) h_le_q q_le_m h_cases
      have hs_le_m : S.card ≤ m := by
        calc S.card ≤ Fintype.card (Fin m) := Finset.card_le_univ S
             _ = m := Fintype.card_fin m
      have hb := OppositeProjectionFallingFactorialBound S.card m (h i) hs_le_m h_cases
      rw [hr]
      exact hb
    · push Not at h_cases
      have hz := OppositeProjectionRowFavorableZero S.card (h i) h_cases
      rw [hz]
      simp
      positivity

  have prod_ratio : (X_good.card : ℝ) / (X_all.card : ℝ) = ∏ i : Fin m, (((Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ)) / (Nat.descFactorial m (q i) : ℝ)) := by
    rw [h_good_card, h_all_card, ← Finset.prod_div_distrib]

  have h_sum : ∑ i : Fin m, h i = T.card := by
    have h1 : ∀ i, T_i i = Finset.filter (fun v => ρ v = i) T := by
      intro i
      dsimp [T_i, R]
      ext x
      simp only [mem_inter, mem_filter, mem_univ, true_and]
    have h_sum_h : ∑ i : Fin m, h i = ∑ i : Fin m, (T_i i).card := rfl
    rw [h_sum_h]
    simp_rw [h1]
    have h2 := Finset.sum_card_fiberwise_eq_card_filter T Finset.univ ρ
    have h3 : Finset.filter (fun (i : Fin n) => ρ i ∈ Finset.univ) T = T := by
      ext x
      simp only [mem_filter, mem_univ, and_true]
    rw [h3] at h2
    exact h2

  have h_bound : (∏ i : Fin m, (((Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ)) / (Nat.descFactorial m (q i) : ℝ))) ≤ ∏ i : Fin m, (((S.card : ℝ) / (m : ℝ)) ^ (h i)) := by
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      exact row_bound i

  have h_pow : ∏ i : Fin m, (((S.card : ℝ) / (m : ℝ)) ^ (h i)) = ((S.card : ℝ) / (m : ℝ)) ^ (∑ i : Fin m, h i) := by
    exact Finset.prod_pow_eq_pow_sum Finset.univ h ((S.card : ℝ) / (m : ℝ))

  rw [prod_ratio]
  rw [h_pow] at h_bound
  rw [h_sum] at h_bound
  exact h_bound
