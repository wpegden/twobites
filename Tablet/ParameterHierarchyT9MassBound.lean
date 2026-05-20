import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT9MassBound]

theorem ParameterHierarchyT9MassBound :
    ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let mReal := (n : ℝ) / L ^ 2
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      0 < (n : ℝ) →
      0 < L →
      m ≤ mReal →
      2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := by
-- BODY
  intro n
  dsimp
  let L := Real.log (n : ℝ)
  let mReal := (n : ℝ) / L ^ 2
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  intro hn_pos hL_pos hm_le_mReal
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have htwo_p_nonneg : 0 ≤ 2 * p := by positivity
  have hfirst :
      2 * p * m ≤ 2 * p * mReal :=
    mul_le_mul_of_nonneg_left hm_le_mReal htwo_p_nonneg
  have hsqrt_div :
      Real.sqrt (L / (n : ℝ)) = Real.sqrt L / Real.sqrt (n : ℝ) := by
    rw [div_eq_mul_inv]
    rw [Real.sqrt_mul hL_nonneg ((n : ℝ)⁻¹)]
    rw [Real.sqrt_inv]
    ring
  have hsqrt_n_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    rw [← sq]
    exact Real.sq_sqrt hn_nonneg
  have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    calc
      L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
      _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcalc :
      2 * p * mReal = Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := by
    have hsqrtL_sq : Real.sqrt L * Real.sqrt L = L := by
      rw [← sq]
      exact Real.sq_sqrt hL_nonneg
    have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
    have htarget : Real.sqrt L / L ^ 2 = 1 / (Real.sqrt L * L) := by
      have hden : L ^ 2 = (Real.sqrt L * L) * Real.sqrt L := by
        calc
          L ^ 2 = L * L := by ring
          _ = (Real.sqrt L * Real.sqrt L) * L := by rw [hsqrtL_sq]
          _ = (Real.sqrt L * L) * Real.sqrt L := by ring
      rw [hden]
      field_simp [ne_of_gt hsqrtL_pos]
    calc
      2 * p * mReal =
          (Real.sqrt L / Real.sqrt (n : ℝ)) * ((n : ℝ) / L ^ 2) := by
        dsimp [p, mReal]
        rw [hsqrt_div]
        ring
      _ = Real.sqrt (n : ℝ) * (Real.sqrt L / L ^ 2) := by
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos)]
        nth_rewrite 1 [show (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) by
          exact hsqrt_n_sq.symm]
        ring
      _ = Real.sqrt (n : ℝ) * (1 / (Real.sqrt L * L)) := by rw [htarget]
      _ = Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := by
        rw [hL_rpow]
        ring
  exact le_trans hfirst (le_of_eq hcalc)

