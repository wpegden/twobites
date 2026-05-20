import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT16Algebra]

theorem ParameterHierarchyT16Algebra :
    ∀ ε2 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < (n : ℝ) →
      0 < L →
      0 < Real.log L →
      2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
      Real.log L / L ^ 2 ≤ ε2 / 100 →
      2 * p * m ≤ (ε2 / 100) * t1 := by
-- BODY
  intro ε2 n
  dsimp
  let L := Real.log (n : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hn_pos hL_pos hlogL_pos hmass hthreshold
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have ht1_pos : 0 < t1 := by
    dsimp [t1]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos hn_pos hL_pos)) hlogL_pos
  have hsqrt_nL :
      Real.sqrt ((n : ℝ) * L) = Real.sqrt (n : ℝ) * Real.sqrt L := by
    rw [Real.sqrt_mul hn_nonneg L]
  have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    calc
      L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
      _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hmass_eq :
      Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) =
        t1 * (Real.log L / L ^ 2) := by
    have hsqrtL_sq : Real.sqrt L * Real.sqrt L = L := by
      rw [← sq]
      exact Real.sq_sqrt hL_nonneg
    have htarget : Real.sqrt L / L ^ 2 = 1 / (Real.sqrt L * L) := by
      have hden : L ^ 2 = (Real.sqrt L * L) * Real.sqrt L := by
        calc
          L ^ 2 = L * L := by ring
          _ = (Real.sqrt L * Real.sqrt L) * L := by rw [hsqrtL_sq]
          _ = (Real.sqrt L * L) * Real.sqrt L := by ring
      rw [hden]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hL_pos)]
    calc
      Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) =
          Real.sqrt (n : ℝ) * (1 / (Real.sqrt L * L)) := by
        rw [hL_rpow]
        ring
      _ = Real.sqrt (n : ℝ) * (Real.sqrt L / L ^ 2) := by rw [htarget]
      _ = Real.sqrt ((n : ℝ) * L) / L ^ 2 := by rw [hsqrt_nL]; ring
      _ = t1 * (Real.log L / L ^ 2) := by
        dsimp [t1]
        have hlog_ne : Real.log L ≠ 0 := ne_of_gt hlogL_pos
        have hL2_ne : L ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hL_pos)
        field_simp [hlog_ne, hL2_ne, mul_ne_zero hL2_ne hlog_ne]
  calc
    2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := hmass
    _ = t1 * (Real.log L / L ^ 2) := hmass_eq
    _ ≤ t1 * (ε2 / 100) :=
      mul_le_mul_of_nonneg_left hthreshold (le_of_lt ht1_pos)
    _ = (ε2 / 100) * t1 := by ring
