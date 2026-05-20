import Tablet.HypergeometricMgfComparison

open Real Finset

-- [TABLET NODE: HypergeometricCountingLowerTailBound]

theorem HypergeometricCountingLowerTailBound :
    ∀ N n m : ℕ, n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let μ : ℝ := (n : ℝ) * q
    ((Finset.powersetCard n (Finset.univ : Finset (Fin N))).filter
      (fun S => ((S ∩ M).card : ℝ) < (1 - δ) * μ)).card /
      ((Nat.choose N n : ℝ)) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
-- BODY
  intro N n m hn hm M hM δ hδ_pos hδ_lt_one
  let q : ℝ := (m : ℝ) / (N : ℝ)
  let μ : ℝ := (n : ℝ) * q
  let S_n := powersetCard n (univ : Finset (Fin N))
  let threshold : ℝ := (1 - δ) * μ
  let E := S_n.filter (fun S => ((S ∩ M).card : ℝ) < threshold)
  let L : ℝ := log (1 - δ)
  have h_choose_pos : (0 : ℝ) < Nat.choose N n := by
    norm_cast
    exact Nat.choose_pos hn
  have h_one_minus_pos : 0 < 1 - δ := by
    linarith
  have hL_neg : L < 0 := by
    have hlt_one : 1 - δ < 1 := by linarith
    dsimp [L]
    simpa using Real.log_lt_log h_one_minus_pos hlt_one
  have h_markov :
      (E.card : ℝ) / (Nat.choose N n : ℝ) ≤
        ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ))) *
          exp (-L * threshold) := by
    rw [div_le_iff₀ h_choose_pos]
    have h_choose_cancel :
        ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ))) *
            exp (-L * threshold) * (Nat.choose N n : ℝ)
          =
        (∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ))) * exp (-L * threshold) := by
      field_simp [h_choose_pos.ne.symm]
    rw [h_choose_cancel]
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    have h1 : ∑ S ∈ E, exp (L * threshold) ≤
        ∑ S ∈ E, exp (L * ((S ∩ M).card : ℝ)) := by
      apply sum_le_sum
      intro S hS
      simp [E] at hS
      exact exp_le_exp.mpr (le_of_lt (mul_lt_mul_of_neg_left hS.2 hL_neg))
    have h2 : ∑ S ∈ E, exp (L * ((S ∩ M).card : ℝ)) ≤
        ∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro S hS hS_not_E
      exact (exp_pos _).le
    calc
      (E.card : ℝ) * exp (L * threshold) = ∑ S ∈ E, exp (L * threshold) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ E, exp (L * ((S ∩ M).card : ℝ)) := h1
      _ ≤ ∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ)) := h2
  apply h_markov.trans
  let Y_mgf := (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n, exp (L * ((S ∩ M).card : ℝ))
  have h_mgf : Y_mgf ≤ exp (μ * (exp L - 1)) := by
    have h := HypergeometricMgfComparison N n m hn hm M hM L
    exact h.1.trans h.2
  refine (mul_le_mul_of_nonneg_right h_mgf (exp_pos (-L * threshold)).le).trans ?_
  have h_expL : exp L = 1 - δ := by
    dsimp [L]
    exact exp_log h_one_minus_pos
  rw [← Real.exp_add]
  have h_arg :
      μ * (exp L - 1) + -L * threshold =
        -(δ + (1 - δ) * log (1 - δ)) * μ := by
    dsimp [threshold, L]
    rw [h_expL]
    ring
  rw [h_arg]
