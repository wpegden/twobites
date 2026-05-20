import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT10Algebra]

theorem ParameterHierarchyT10Algebra :
    ∀ η ε1 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < η →
      0 < ε1 →
      0 < (n : ℝ) →
      0 < L →
      0 < Real.log L →
      0 ≤ k →
      kReal ≤ k →
      0 ≤ 2 * p * m →
      2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
      2 * Real.log L / ((1 + η) * L ^ 4) ≤ ε1 →
      (2 * k / t1) * RealChooseTwo (2 * p * m) ≤ ε1 * k ^ 2 := by
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hη hε1 hn_pos hL_pos hlogL_pos hk_nonneg hkReal_le_k hx_nonneg hmass hthreshold
  let x : ℝ := 2 * p * m
  have hκ_pos : 0 < 1 + η := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hnL_pos : 0 < (n : ℝ) * L := mul_pos hn_pos hL_pos
  have ht1_pos : 0 < t1 := by
    dsimp [t1]
    exact div_pos (Real.sqrt_pos.mpr hnL_pos) hlogL_pos
  have hfactor_nonneg : 0 ≤ 2 * k / t1 := by
    exact div_nonneg (mul_nonneg (by norm_num) hk_nonneg) (le_of_lt ht1_pos)
  have hx_nonneg_for_x : 0 ≤ x := by
    dsimp [x]
    exact hx_nonneg
  have hmass_for_x : x ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := by
    dsimp [x]
    exact hmass
  have hchoose_le_xsq : RealChooseTwo x ≤ x ^ 2 :=
    (RealChooseTwoQuadraticBounds x hx_nonneg_for_x).2
  have hmass_sq : x ^ 2 ≤ (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hx_nonneg_for_x hmass_for_x 2
  have hsqrt_nL :
      Real.sqrt ((n : ℝ) * L) = Real.sqrt (n : ℝ) * Real.sqrt L := by
    rw [Real.sqrt_mul hn_nonneg L]
  have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    calc
      L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
      _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hfactor_eq :
      (2 * k / t1) * (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) ^ 2 =
        k * (2 * Real.log L / ((1 + η) * L ^ 4)) * kReal := by
    dsimp [t1, kReal]
    rw [hsqrt_nL, hL_rpow]
    field_simp [ne_of_gt hlogL_pos, ne_of_gt hκ_pos,
      ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt (Real.sqrt_pos.mpr hL_pos),
      ne_of_gt hL_pos]
    rw [show L = Real.sqrt L ^ 2 by exact (Real.sq_sqrt hL_nonneg).symm]
    rw [Real.sqrt_sq_eq_abs (Real.sqrt L), abs_of_nonneg (Real.sqrt_nonneg L)]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hL_pos)]
  have hkReal_nonneg : 0 ≤ kReal := by
    dsimp [kReal]
    positivity
  have hthreshold_scaled :
      k * (2 * Real.log L / ((1 + η) * L ^ 4)) * kReal ≤
        k * ε1 * kReal := by
    calc
      k * (2 * Real.log L / ((1 + η) * L ^ 4)) * kReal
          = k * ((2 * Real.log L / ((1 + η) * L ^ 4)) * kReal) := by ring
      _ ≤ k * (ε1 * kReal) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hthreshold hkReal_nonneg) hk_nonneg
      _ = k * ε1 * kReal := by ring
  have hkReal_scaled :
      k * ε1 * kReal ≤ k * ε1 * k := by
    exact mul_le_mul_of_nonneg_left hkReal_le_k (mul_nonneg hk_nonneg (le_of_lt hε1))
  calc
    (2 * k / t1) * RealChooseTwo (2 * p * m)
        = (2 * k / t1) * RealChooseTwo x := by simp [x]
    _ ≤ (2 * k / t1) * x ^ 2 :=
      mul_le_mul_of_nonneg_left hchoose_le_xsq hfactor_nonneg
    _ ≤ (2 * k / t1) * (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hmass_sq hfactor_nonneg
    _ = k * (2 * Real.log L / ((1 + η) * L ^ 4)) * kReal := hfactor_eq
    _ ≤ k * ε1 * kReal := hthreshold_scaled
    _ ≤ k * ε1 * k := hkReal_scaled
    _ = ε1 * k ^ 2 := by ring

