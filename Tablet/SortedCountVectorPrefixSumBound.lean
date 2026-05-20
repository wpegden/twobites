import Tablet.Preamble

open Finset Real BigOperators

-- [TABLET NODE: SortedCountVectorPrefixSumBound]

theorem SortedCountVectorPrefixSumBound :
    ∀ N n : ℕ,
    ∀ x : Fin N → ℝ, (∑ i, x i) = n →
    (∀ i : Fin N, ∃ k : ℕ, x i = k) →
    (∀ i j : Fin N, i.val ≤ j.val → x j ≤ x i) →
    ∀ r : ℕ, r ≤ N →
    min r n ≤ ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), x i := by
-- BODY
  intro N n x hsum hnat hmono r hr
  have hnonneg : ∀ i, 0 ≤ x i := by
    intro i
    rcases hnat i with ⟨k, hk⟩
    rw [hk]
    exact Nat.cast_nonneg k
  have hcard : (univ.filter (fun (i : Fin N) => i.val < r)).card = r := by
    have h_eq : univ.filter (fun (i : Fin N) => i.val < r) = (univ : Finset (Fin r)).image (Fin.castLE hr) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro h
        use ⟨y.val, h⟩
        simp
      · rintro ⟨z, hz⟩
        subst hz
        exact z.isLt
    rw [h_eq, card_image_of_injective _ (Fin.castLE_injective hr), card_univ, Fintype.card_fin]
  rcases eq_or_lt_of_le (Nat.zero_le r) with rfl | hrpos
  · simp
  rcases le_total r n with hrn | hnr
  · have hmin : min r n = r := Nat.min_eq_left hrn
    rw [hmin]
    by_contra hlt
    rw [not_le] at hlt
    have hrn_real : (r : ℝ) ≤ n := Nat.cast_le.mpr hrn
    let r_minus_1 : Fin N := ⟨r - 1, by omega⟩
    have xr0 : x r_minus_1 = 0 := by
      by_contra hxr
      have hxr1 : 1 ≤ x r_minus_1 := by
        rcases hnat r_minus_1 with ⟨k, hk⟩
        have hk0 : k ≠ 0 := by
          intro hk0
          subst hk0
          simp only [Nat.cast_zero] at hk
          exact hxr hk
        have : 1 ≤ k := Nat.pos_of_ne_zero hk0
        rw [hk]
        exact_mod_cast this
      have hsum_ge : (r : ℝ) ≤ ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), x i := by
        calc (r : ℝ) = ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), (1 : ℝ) := by
              simp only [sum_const, nsmul_eq_mul, mul_one]
              congr 1
              exact hcard.symm
             _ ≤ ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), x i := by
              apply sum_le_sum
              intro i hi
              simp only [mem_filter, mem_univ, true_and] at hi
              have himono : i.val ≤ r_minus_1.val := by
                change i.val ≤ r - 1
                omega
              exact le_trans hxr1 (hmono i r_minus_1 himono)
      linarith
    have hsum_eq : ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), x i = ∑ i, x i := by
      rw [← sum_filter_add_sum_filter_not univ (fun (i : Fin N) => i.val < r)]
      have : ∑ i ∈ univ.filter (fun (i : Fin N) => ¬ i.val < r), x i = 0 := by
        apply sum_eq_zero
        intro i hi
        simp only [mem_filter, mem_univ, true_and, not_lt] at hi
        have himono : r_minus_1.val ≤ i.val := by
          change r - 1 ≤ i.val
          omega
        have hxi : x i ≤ x r_minus_1 := hmono r_minus_1 i himono
        rw [xr0] at hxi
        exact le_antisymm hxi (hnonneg i)
      linarith
    linarith
  · have hmin : min r n = n := Nat.min_eq_right hnr
    rw [hmin]
    by_contra hlt
    rw [not_le] at hlt
    have hnr_real : (n : ℝ) ≤ r := Nat.cast_le.mpr hnr
    have h_not_all_zero : ∃ i ∈ univ.filter (fun (i : Fin N) => ¬ i.val < r), x i > 0 := by
      by_contra hzero
      simp only [not_exists, not_and] at hzero
      have hzero' : ∀ i ∈ univ.filter (fun (i : Fin N) => ¬ i.val < r), x i ≤ 0 := by
        intro i hi
        exact not_lt.mp (hzero i hi)
      have hsum_eq : ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), x i = ∑ i, x i := by
        rw [← sum_filter_add_sum_filter_not univ (fun (i : Fin N) => i.val < r)]
        have : ∑ i ∈ univ.filter (fun (i : Fin N) => ¬ i.val < r), x i = 0 := by
          apply sum_eq_zero
          intro i hi
          exact le_antisymm (hzero' i hi) (hnonneg i)
        linarith
      linarith
    rcases h_not_all_zero with ⟨i, hi, hxi⟩
    simp only [mem_filter, mem_univ, true_and, not_lt] at hi
    have hxi1 : 1 ≤ x i := by
      rcases hnat i with ⟨k, hk⟩
      have hk0 : k ≠ 0 := by
        intro hk0
        subst hk0
        simp only [Nat.cast_zero] at hk
        rw [hk] at hxi
        exact lt_irrefl 0 hxi
      have : 1 ≤ k := Nat.pos_of_ne_zero hk0
      rw [hk]
      exact_mod_cast this
    have hsum_ge : (r : ℝ) ≤ ∑ j ∈ univ.filter (fun (j : Fin N) => j.val < r), x j := by
      calc (r : ℝ) = ∑ j ∈ univ.filter (fun (j : Fin N) => j.val < r), (1 : ℝ) := by
            simp only [sum_const, nsmul_eq_mul, mul_one]
            congr 1
            exact hcard.symm
           _ ≤ ∑ j ∈ univ.filter (fun (j : Fin N) => j.val < r), x j := by
            apply sum_le_sum
            intro j hj
            simp only [mem_filter, mem_univ, true_and] at hj
            have hjmono : j.val ≤ i.val := by omega
            exact le_trans hxi1 (hmono j i hjmono)
    linarith
