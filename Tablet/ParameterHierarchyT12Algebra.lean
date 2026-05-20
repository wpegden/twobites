import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT12Algebra]

theorem ParameterHierarchyT12Algebra :
    ∀ η ε1 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < η →
      0 < ε1 →
      0 < (n : ℝ) →
      0 < L →
      1 ≤ L →
      0 < Real.log L →
      0 ≤ k →
      kReal ≤ k →
      0 < t1 →
      2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L →
      400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 /
          (ε1 * ((1 + η) ^ 2 * (n : ℝ))) ≤ 1 →
      RealChooseTwo (2 * k / t1 + 1) * RealChooseTwo (200 * L ^ 3) ≤
        (ε1 / 10) * k ^ 2 := by
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hη hε1 hn_pos hL_pos hL_ge_one _hlogL_pos hk_nonneg hkReal_le_k ht1_pos hD hthreshold
  let x : ℝ := 2 * k / t1 + 1
  let y : ℝ := 200 * L ^ 3
  let A : ℝ := 5 * (1 + η) * Real.log L
  have hnL_nonneg : 0 ≤ (n : ℝ) * L := le_of_lt (mul_pos hn_pos hL_pos)
  have hden_pos : 0 < ε1 * ((1 + η) ^ 2 * (n : ℝ)) := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    have hfrac_nonneg : 0 ≤ 2 * k / t1 := by
      exact div_nonneg (mul_nonneg (by norm_num) hk_nonneg) (le_of_lt ht1_pos)
    linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_ge_two : (2 : ℝ) ≤ y := by
    dsimp [y]
    calc
      (2 : ℝ) ≤ 200 * 1 := by norm_num
      _ ≤ 200 * L ^ 3 := by
        have hL3_ge_one : (1 : ℝ) ≤ L ^ 3 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one 3
        exact mul_le_mul_of_nonneg_left hL3_ge_one (by norm_num)
  have hchoose_x_le_xsq : RealChooseTwo x ≤ x ^ 2 :=
    (RealChooseTwoQuadraticBounds x hx_nonneg).2
  have hx_sq_le_A_sq : x ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hx_nonneg (by simpa [x, A, L, k, t1] using hD) 2
  have hchoose_x_le_A_sq : RealChooseTwo x ≤ A ^ 2 :=
    le_trans hchoose_x_le_xsq hx_sq_le_A_sq
  have hchoose_y_bounds := RealChooseTwoQuadraticBounds y hy_nonneg
  have hchoose_y_nonneg : 0 ≤ RealChooseTwo y := by
    have hlower := (hchoose_y_bounds.1 hy_ge_two).1
    exact le_trans (by positivity : 0 ≤ y ^ 2 / 4) hlower
  have hchoose_y_le_ysq : RealChooseTwo y ≤ y ^ 2 := hchoose_y_bounds.2
  have hA_sq_nonneg : 0 ≤ A ^ 2 := sq_nonneg A
  have hproduct_le :
      RealChooseTwo x * RealChooseTwo y ≤ A ^ 2 * y ^ 2 := by
    calc
      RealChooseTwo x * RealChooseTwo y ≤ A ^ 2 * RealChooseTwo y :=
        mul_le_mul_of_nonneg_right hchoose_x_le_A_sq hchoose_y_nonneg
      _ ≤ A ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_left hchoose_y_le_ysq hA_sq_nonneg
  have hthreshold_mul :
      400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 ≤
        ε1 * ((1 + η) ^ 2 * (n : ℝ)) := by
    simpa [L] using (div_le_iff₀ hden_pos).1 hthreshold
  have hA_sq_eq : A ^ 2 = (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 := by
    dsimp [A]
    ring
  have hy_sq_eq : y ^ 2 = 40000 * L ^ 6 := by
    dsimp [y]
    ring
  have hA_y_eq :
      A ^ 2 * y ^ 2 =
        40000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 6 := by
    rw [hA_sq_eq, hy_sq_eq]
    ring
  have hkReal_sq_eq :
      kReal ^ 2 = (1 + η) ^ 2 * ((n : ℝ) * L) := by
    dsimp [kReal]
    rw [mul_pow, Real.sq_sqrt hnL_nonneg]
  have hA_y_le_kReal :
      A ^ 2 * y ^ 2 ≤ (ε1 / 10 : ℝ) * kReal ^ 2 := by
    rw [hA_y_eq, hkReal_sq_eq]
    have hscaled :=
      mul_le_mul_of_nonneg_right hthreshold_mul (le_of_lt hL_pos)
    nlinarith [hscaled]
  have hkReal_nonneg : 0 ≤ kReal := by
    dsimp [kReal]
    positivity
  have hkReal_sq_le_k_sq : kReal ^ 2 ≤ k ^ 2 :=
    pow_le_pow_left₀ hkReal_nonneg hkReal_le_k 2
  have hscaled_k :
      (ε1 / 10 : ℝ) * kReal ^ 2 ≤ (ε1 / 10) * k ^ 2 :=
    mul_le_mul_of_nonneg_left hkReal_sq_le_k_sq (by positivity)
  calc
    RealChooseTwo (2 * k / t1 + 1) * RealChooseTwo (200 * L ^ 3)
        = RealChooseTwo x * RealChooseTwo y := by simp [x, y]
    _ ≤ A ^ 2 * y ^ 2 := hproduct_le
    _ ≤ (ε1 / 10) * kReal ^ 2 := hA_y_le_kReal
    _ ≤ (ε1 / 10) * k ^ 2 := hscaled_k
