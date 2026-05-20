import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT3ChooseComparison]

theorem ParameterHierarchyT3ChooseComparison :
    ∀ η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      1 < L →
      kReal ≤ k →
      16 * L ^ 2 * Real.sqrt L ≤ kReal →
      (1 / (2 * L)) * RealChooseTwo k + 2 * k * L ^ 2 +
          (1 / Real.sqrt L) * RealChooseTwo k ≤
        (2 / Real.sqrt L) * RealChooseTwo k := by
-- BODY
  intro η n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  intro hL_gt_one hkReal_le_k hT3scale
  have hL_pos : 0 < L := by linarith
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact Nat.cast_nonneg K
  have hscale_k : 16 * L ^ 2 * Real.sqrt L ≤ k := le_trans hT3scale hkReal_le_k
  have hsqrt_ge_one : 1 ≤ Real.sqrt L := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ L by linarith)
  have hL_sq_ge_one : 1 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have hprod_ge_one : 1 ≤ L ^ 2 * Real.sqrt L := by
    have := mul_le_mul hL_sq_ge_one hsqrt_ge_one (by norm_num : (0 : ℝ) ≤ 1)
      (by nlinarith [hL_sq_ge_one])
    simpa using this
  have htwo_le_scale : (2 : ℝ) ≤ 16 * L ^ 2 * Real.sqrt L := by nlinarith
  have htwo_le_k : (2 : ℝ) ≤ k := le_trans htwo_le_scale hscale_k
  have hchoose_bounds := RealChooseTwoQuadraticBounds k hk_nonneg
  have hchoose_lower : k ^ 2 / 4 ≤ RealChooseTwo k := (hchoose_bounds.1 htwo_le_k).1
  have hchoose_nonneg : 0 ≤ RealChooseTwo k := by
    have hk_sq_nonneg : 0 ≤ k ^ 2 / 4 := by positivity
    exact le_trans hk_sq_nonneg hchoose_lower
  have hsqrt_le_L : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hL_nonneg
    · nlinarith [sq_nonneg (L - 1)]
  have hcoef_A : 1 / (2 * L) ≤ 1 / (2 * Real.sqrt L) := by
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity : 0 < 2 * Real.sqrt L)
      (by nlinarith)
  have hA :
      (1 / (2 * L)) * RealChooseTwo k ≤
        (1 / (2 * Real.sqrt L)) * RealChooseTwo k :=
    mul_le_mul_of_nonneg_right hcoef_A hchoose_nonneg
  have hB_core : 16 * k * L ^ 2 * Real.sqrt L ≤ k ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hscale_k hk_nonneg
    nlinarith
  have hB :
      2 * k * L ^ 2 ≤ (1 / (2 * Real.sqrt L)) * RealChooseTwo k := by
    have hlower_scaled :
        (1 / (2 * Real.sqrt L)) * (k ^ 2 / 4) ≤
          (1 / (2 * Real.sqrt L)) * RealChooseTwo k :=
      mul_le_mul_of_nonneg_left hchoose_lower (by positivity)
    have hmain :
        2 * k * L ^ 2 ≤ (1 / (2 * Real.sqrt L)) * (k ^ 2 / 4) := by
      rw [one_div]
      field_simp [hsqrt_pos.ne']
      nlinarith
    exact le_trans hmain hlower_scaled
  calc
    (1 / (2 * L)) * RealChooseTwo k + 2 * k * L ^ 2 +
        (1 / Real.sqrt L) * RealChooseTwo k
        ≤ (1 / (2 * Real.sqrt L)) * RealChooseTwo k +
            (1 / (2 * Real.sqrt L)) * RealChooseTwo k +
          (1 / Real.sqrt L) * RealChooseTwo k := by
          nlinarith
    _ = (2 / Real.sqrt L) * RealChooseTwo k := by
      field_simp [hsqrt_pos.ne']
      ring
