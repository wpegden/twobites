import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT28Algebra]

theorem ParameterHierarchyT28Algebra :
    ∀ η ε1 k : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      0 < (n : ℝ) →
      0 ≤ L →
      k < 2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L →
      2 * (1 + η) * Real.sqrt L * L /
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) ≤ (1 / 4 : ℝ) →
      4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
        (1 / 4 : ℝ) →
      Real.exp (-(1 / 2 : ℝ) * Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤
        ε1 →
      Real.exp
        (k * L +
          2 * k * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * η) * L -
          Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
-- BODY
  intro η ε1 k n
  dsimp
  let L := Real.log (n : ℝ)
  let A := Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)
  let e₁ := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η)
  let e₂ := Real.rpow (n : ℝ) η
  let r := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * η)
  intro hn_pos hL_nonneg hk_upper hfirst hsecond hfinal
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hsqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtL_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos hn_pos _
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have he₁_pos : 0 < e₁ := by
    dsimp [e₁]
    exact Real.rpow_pos_of_pos hn_pos _
  have he₂_pos : 0 < e₂ := by
    dsimp [e₂]
    exact Real.rpow_pos_of_pos hn_pos _
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hn_pos _
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hA_eq_sqrt_e₁ :
      A = Real.sqrt (n : ℝ) * e₁ := by
    dsimp [A, e₁]
    calc
      Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η) =
          Real.rpow (n : ℝ) ((1 / 2 : ℝ) + ((1 / 4 : ℝ) - 2 * η)) := by
        congr 1
        ring
      _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) := by
        exact Real.rpow_add hn_pos (1 / 2 : ℝ) ((1 / 4 : ℝ) - 2 * η)
      _ = Real.sqrt (n : ℝ) *
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) :=
        congrArg (fun x : ℝ => x * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η))
          (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hsqrt_mul_e₁ :
      Real.sqrt (n : ℝ) * e₁ = A := hA_eq_sqrt_e₁.symm
  have hr_mul_e₂ :
      r * e₂ = e₁ := by
    dsimp [r, e₂, e₁]
    calc
      Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * η) * Real.rpow (n : ℝ) η =
          Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 3 * η) + η) := by
        exact (Real.rpow_add hn_pos ((1 / 4 : ℝ) - 3 * η) η).symm
      _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) := by
        congr 1
        ring
  have hsqrt_mul_r_e₂ :
      Real.sqrt (n : ℝ) * r * e₂ = A := by
    calc
      Real.sqrt (n : ℝ) * r * e₂ =
          Real.sqrt (n : ℝ) * (r * e₂) := by ring
      _ = Real.sqrt (n : ℝ) * e₁ := by rw [hr_mul_e₂]
      _ = A := hsqrt_mul_e₁
  have hterm₁_upper :
      k * L ≤ 2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by
    have hmul :=
      mul_le_mul_of_nonneg_right (le_of_lt hk_upper) hL_nonneg
    calc
      k * L ≤ (2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L) * L := hmul
      _ = 2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by ring
  have hterm₁_quarter :
      k * L ≤ (1 / 4 : ℝ) * A := by
    have hscale :=
      mul_le_mul_of_nonneg_right hfirst hA_nonneg
    have hupper_quarter :
        2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * L ≤
          (1 / 4 : ℝ) * A := by
      calc
        2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * L =
            (2 * (1 + η) * Real.sqrt L * L / e₁) * A := by
          rw [← hsqrt_mul_e₁]
          field_simp [ne_of_gt he₁_pos]
        _ ≤ (1 / 4 : ℝ) * A := by
          simpa [e₁] using hscale
    exact le_trans hterm₁_upper hupper_quarter
  have hsecond_factor_nonneg :
      0 ≤ 2 * r * L := by
    positivity
  have hterm₂_upper :
      2 * k * r * L ≤ 4 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L := by
    have hmul :=
      mul_le_mul_of_nonneg_right (le_of_lt hk_upper) hsecond_factor_nonneg
    calc
      2 * k * r * L = k * (2 * r * L) := by ring
      _ ≤ (2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L) *
          (2 * r * L) := hmul
      _ = 4 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L := by ring
  have hterm₂_quarter :
      2 * k * r * L ≤ (1 / 4 : ℝ) * A := by
    have hscale :=
      mul_le_mul_of_nonneg_right hsecond hA_nonneg
    have hupper_quarter :
        4 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L ≤
          (1 / 4 : ℝ) * A := by
      calc
        4 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L =
            (4 * (1 + η) * Real.sqrt L * L / e₂) * A := by
          rw [← hsqrt_mul_r_e₂]
          field_simp [ne_of_gt he₂_pos]
        _ ≤ (1 / 4 : ℝ) * A := by
          simpa [e₂] using hscale
    exact le_trans hterm₂_upper hupper_quarter
  have hexponent_le :
      k * L + 2 * k * r * L - A ≤ -(1 / 2 : ℝ) * A := by
    calc
      k * L + 2 * k * r * L - A ≤
          (1 / 4 : ℝ) * A + (1 / 4 : ℝ) * A - A :=
        sub_le_sub_right (add_le_add hterm₁_quarter hterm₂_quarter) A
      _ = -(1 / 2 : ℝ) * A := by ring
  exact le_trans (Real.exp_le_exp.2 (by simpa [A, r] using hexponent_le)) hfinal
