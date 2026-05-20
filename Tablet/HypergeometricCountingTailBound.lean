import Tablet.HypergeometricMgfComparison

open Real Finset

-- [TABLET NODE: HypergeometricCountingTailBound]

theorem HypergeometricCountingTailBound :
    ∀ N n m : ℕ, n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ T : ℝ, T > 0 →
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let μ : ℝ := (n : ℝ) * q
    ((Finset.powersetCard n (Finset.univ : Finset (Fin N))).filter (fun S => ((S ∩ M).card : ℝ) ≥ T)).card /
      ((Nat.choose N n : ℝ)) ≤ (Real.exp 1 * μ / T) ^ T := by
-- BODY
  intro N n m hn hm M hM T hT
  let q : ℝ := (m : ℝ) / (N : ℝ)
  let μ : ℝ := (n : ℝ) * q
  let S_n := powersetCard n (univ : Finset (Fin N))
  let E := S_n.filter (fun S => ((S ∩ M).card : ℝ) ≥ T)
  have hμ_nonneg : 0 ≤ μ := by
    apply mul_nonneg (Nat.cast_nonneg n)
    apply div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg N)
  have h_choose_pos : (0 : ℝ) < Nat.choose N n := by
    norm_cast
    exact Nat.choose_pos hn
  by_cases hμ0 : μ = 0
  · have h_card_zero : ∀ S ∈ S_n, (S ∩ M).card = 0 := by
      intro S hS
      by_cases hN0 : N = 0
      · subst N
        simp
        apply Finset.eq_empty_of_isEmpty
      · have hN_pos : (0 : ℝ) < N := by norm_cast; exact Nat.pos_of_ne_zero hN0
        have h_mu_zero : (n : ℝ) * ((m : ℝ) / (N : ℝ)) = 0 := hμ0
        rcases mul_eq_zero.mp h_mu_zero with h | h
        · have hn0 : n = 0 := by norm_cast at h
          subst n
          simp [S_n] at hS
          subst S; simp
        · have hm0 : m = 0 := by
            rw [div_eq_zero_iff] at h
            rcases h with h1 | h2
            · norm_cast at h1
            · exfalso; exact hN_pos.ne.symm h2
          have : M = ∅ := by
            apply card_eq_zero.mp
            rw [hM, hm0]
          subst M; simp
    have h_E_empty : E = ∅ := by
      ext S
      constructor
      · intro h_mem
        simp [E] at h_mem
        have h_card := h_card_zero S h_mem.1
        have h_T_le := h_mem.2
        rw [h_card] at h_T_le
        norm_cast at h_T_le
        linarith
      · intro h; exfalso; exact notMem_empty S h
    show ↑(#E) / ↑(N.choose n) ≤ (rexp 1 * μ / T) ^ T
    rw [h_E_empty]
    simp [hμ0]
    rw [Real.zero_rpow hT.ne.symm]
  have hμ_pos : 0 < μ := hμ_nonneg.lt_of_ne (Ne.symm hμ0)
  by_cases hTμ : T ≤ μ
  · have h_lhs_le_one : (E.card : ℝ) / (Nat.choose N n : ℝ) ≤ 1 := by
      rw [div_le_one h_choose_pos]
      norm_cast
      apply (card_filter_le S_n _).trans
      simp [S_n]
    apply h_lhs_le_one.trans
    have h_base_ge_one : 1 ≤ exp 1 * μ / T := by
      have h_base_ge_exp : exp 1 ≤ exp 1 * (μ / T) := by
        apply le_mul_of_one_le_right (exp_pos 1).le
        rw [one_le_div hT]
        exact hTμ
      rw [mul_div_assoc]
      apply h_base_ge_exp.trans'
      apply (one_lt_exp_iff.mpr zero_lt_one).le
    apply (Real.one_rpow T).symm.le.trans
    apply Real.rpow_le_rpow zero_le_one h_base_ge_one hT.le
  have hTμ_gt : μ < T := not_le.mp hTμ
  let L := log (T / μ)
  have hL_pos : 0 < L := log_pos ((one_lt_div hμ_pos).mpr hTμ_gt)
  have h_markov : (E.card : ℝ) / (Nat.choose N n : ℝ) ≤
    ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * (S ∩ M).card)) * exp (-L * T) := by
    rw [div_le_iff₀ h_choose_pos]
    have h_choose_cancel : ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * (S ∩ M).card)) * exp (-L * T) * (Nat.choose N n : ℝ) =
      (∑ S ∈ S_n, exp (L * (S ∩ M).card)) * exp (-L * T) := by
      field_simp [h_choose_pos.ne.symm]
    rw [h_choose_cancel]
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    have h1 : ∑ S ∈ E, exp (L * T) ≤ ∑ S ∈ E, exp (L * (S ∩ M).card) := by
      apply sum_le_sum
      intro S hS
      simp [E] at hS
      apply exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left hS.2 hL_pos.le
    have h2 : ∑ S ∈ E, exp (L * (S ∩ M).card) ≤ ∑ S ∈ S_n, exp (L * (S ∩ M).card) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro S hS hS_not_E
      apply (exp_pos _).le
    calc
      (E.card : ℝ) * exp (L * T) = ∑ S ∈ E, exp (L * T) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ E, exp (L * (S ∩ M).card) := h1
      _ ≤ ∑ S ∈ S_n, exp (L * (S ∩ M).card) := h2
  apply h_markov.trans
  let Y_mgf := (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * (S ∩ M).card)
  have h_mgf : Y_mgf ≤ exp (μ * (exp L - 1)) := by
    have h := HypergeometricMgfComparison N n m hn hm M hM L
    exact h.1.trans h.2
  apply (mul_le_mul_of_nonneg_right h_mgf (exp_pos (-L * T)).le).trans
  rw [← Real.exp_add]
  have h_exp_rpow : (rexp 1 * μ / T) ^ T = rexp (T * log (rexp 1 * μ / T)) := by
    rw [Real.rpow_def_of_pos]
    · rw [mul_comm]
    · apply div_pos (mul_pos (exp_pos 1) hμ_pos) hT
  rw [h_exp_rpow]
  have h_target_expr : μ * (exp L - 1) + -L * T = T - μ - T * log (T / μ) := by
    have h_expL : exp L = T / μ := exp_log (div_pos hT hμ_pos)
    rw [h_expL]
    rw [mul_sub, mul_div_cancel₀ _ hμ_pos.ne.symm]
    ring
  rw [h_target_expr]
  have h_target : T - μ - T * log (T / μ) ≤ T * log (rexp 1 * μ / T) := by
    have h_target_le : T - μ - T * log (T / μ) ≤ T * (1 - log (T / μ)) := by
      rw [mul_sub, mul_one]
      linarith
    apply h_target_le.trans
    have h_log_eq : 1 - log (T / μ) = log (exp 1 * μ / T) := by
      rw [log_div (mul_pos (exp_pos 1) hμ_pos).ne.symm hT.ne.symm]
      rw [log_mul (exp_pos 1).ne.symm hμ_pos.ne.symm]
      rw [Real.log_exp, log_div hT.ne.symm hμ_pos.ne.symm]
      ring_nf
    rw [h_log_eq]
  exact exp_le_exp.mpr h_target
