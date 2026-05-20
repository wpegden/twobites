import Tablet.HypergeometricMgfComparison

open Real Finset

-- [TABLET NODE: HypergeometricCountingUpperChernoffBound]

/-- Chernoff upper tail for the number of marked elements in a uniformly chosen
`n`-subset of a finite population. -/
theorem HypergeometricCountingUpperChernoffBound :
    ∀ N n m : ℕ, n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ δ : ℝ, 0 < δ →
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let μ : ℝ := (n : ℝ) * q
    ((Finset.powersetCard n (Finset.univ : Finset (Fin N))).filter
        (fun S => (1 + δ) * μ < (((S ∩ M).card : ℕ) : ℝ))).card /
      (Nat.choose N n : ℝ)
      ≤ Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) := by
-- BODY
  intro N n m hnN hmN M hM δ hδ
  let q : ℝ := (m : ℝ) / (N : ℝ)
  let μ : ℝ := (n : ℝ) * q
  let S_n := powersetCard n (univ : Finset (Fin N))
  let threshold : ℝ := (1 + δ) * μ
  let E := S_n.filter (fun S => threshold < (((S ∩ M).card : ℕ) : ℝ))
  let L : ℝ := Real.log (1 + δ)
  have h_choose_pos : 0 < (Nat.choose N n : ℝ) := by
    norm_cast
    exact Nat.choose_pos hnN
  have h_one_plus_pos : 0 < (1 + δ : ℝ) := by linarith
  have h_one_lt : (1 : ℝ) < 1 + δ := by linarith
  have hL_nonneg : 0 ≤ L := le_of_lt (Real.log_pos h_one_lt)
  have h_markov :
      (E.card : ℝ) / (Nat.choose N n : ℝ)
        ≤
        ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n,
            Real.exp (L * (((S ∩ M).card : ℕ) : ℝ))) *
          Real.exp (-L * threshold) := by
    rw [div_le_iff₀ h_choose_pos]
    have h_choose_cancel :
        ((Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n,
            Real.exp (L * (((S ∩ M).card : ℕ) : ℝ))) *
            Real.exp (-L * threshold) * (Nat.choose N n : ℝ)
          =
        (∑ S ∈ S_n, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ))) *
          Real.exp (-L * threshold) := by
      field_simp [h_choose_pos.ne.symm]
    rw [h_choose_cancel]
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    have h1 : ∑ S ∈ E, Real.exp (L * threshold) ≤
        ∑ S ∈ E, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro S hS
      simp [E] at hS
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_of_lt hS.2) hL_nonneg)
    have h2 : ∑ S ∈ E, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ)) ≤
        ∑ S ∈ S_n, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S hS hSnot
      exact (Real.exp_pos _).le
    calc
      (E.card : ℝ) * Real.exp (L * threshold) =
          ∑ S ∈ E, Real.exp (L * threshold) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ E, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ)) := h1
      _ ≤ ∑ S ∈ S_n, Real.exp (L * (((S ∩ M).card : ℕ) : ℝ)) := h2
  apply h_markov.trans
  let Y_mgf : ℝ :=
    (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ S_n,
      Real.exp (L * (((S ∩ M).card : ℕ) : ℝ))
  have h_mgf : Y_mgf ≤ Real.exp (μ * (Real.exp L - 1)) := by
    have h := HypergeometricMgfComparison N n m hnN hmN M hM L
    exact h.1.trans h.2
  refine (mul_le_mul_of_nonneg_right h_mgf (Real.exp_pos (-L * threshold)).le).trans ?_
  have h_expL : Real.exp L = 1 + δ := by
    dsimp [L]
    exact Real.exp_log h_one_plus_pos
  rw [← Real.exp_add]
  have h_arg :
      μ * (Real.exp L - 1) + -L * threshold =
        -(((1 + δ) * Real.log (1 + δ) - δ) * μ) := by
    dsimp [L, threshold]
    rw [h_expL]
    ring
  rw [h_arg]
