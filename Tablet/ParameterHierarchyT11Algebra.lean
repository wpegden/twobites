import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT11Algebra]

theorem ParameterHierarchyT11Algebra :
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
      0 < Real.log L →
      0 ≤ k →
      kReal ≤ k →
      0 < t1 →
      2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L →
      2000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 /
          (ε1 * ((1 + η) * Real.sqrt ((n : ℝ) * L))) ≤ 1 →
      RealChooseTwo (2 * k / t1 + 1) * (200 * L ^ 3) ≤ (ε1 / 10) * k := by
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hη hε1 hn_pos hL_pos _hlogL_pos hk_nonneg hkReal_le_k ht1_pos hD hthreshold
  let x : ℝ := 2 * k / t1 + 1
  let A : ℝ := 5 * (1 + η) * Real.log L
  have hκ_pos : 0 < 1 + η := by linarith
  have hnL_pos : 0 < (n : ℝ) * L := mul_pos hn_pos hL_pos
  have hden_pos : 0 < ε1 * ((1 + η) * Real.sqrt ((n : ℝ) * L)) := by
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) * L) := Real.sqrt_pos.mpr hnL_pos
    positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    have hfrac_nonneg : 0 ≤ 2 * k / t1 := by
      exact div_nonneg (mul_nonneg (by norm_num) hk_nonneg) (le_of_lt ht1_pos)
    linarith
  have hchoose_le_xsq : RealChooseTwo x ≤ x ^ 2 :=
    (RealChooseTwoQuadraticBounds x hx_nonneg).2
  have hx_sq_le_A_sq : x ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hx_nonneg (by simpa [x, A, L, k, t1] using hD) 2
  have hchoose_le_A_sq : RealChooseTwo x ≤ A ^ 2 :=
    le_trans hchoose_le_xsq hx_sq_le_A_sq
  have hscale_nonneg : 0 ≤ 200 * L ^ 3 := by positivity
  have hchoose_scaled :
      RealChooseTwo x * (200 * L ^ 3) ≤ A ^ 2 * (200 * L ^ 3) :=
    mul_le_mul_of_nonneg_right hchoose_le_A_sq hscale_nonneg
  have hthreshold_mul :
      2000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 ≤
        ε1 * kReal := by
    have hmul := (div_le_iff₀ hden_pos).1 hthreshold
    simpa [kReal, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hA_sq_eq : A ^ 2 = (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 := by
    dsimp [A]
    ring
  have hA_scaled_eq :
      A ^ 2 * (200 * L ^ 3) =
        200 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 := by
    rw [hA_sq_eq]
    ring
  have htenth_kReal :
      A ^ 2 * (200 * L ^ 3) ≤ (ε1 / 10 : ℝ) * kReal := by
    rw [hA_scaled_eq]
    nlinarith [hthreshold_mul]
  have htenth_kReal_le_k : (ε1 / 10 : ℝ) * kReal ≤ (ε1 / 10) * k :=
    mul_le_mul_of_nonneg_left hkReal_le_k (by positivity)
  exact le_trans hchoose_scaled (le_trans htenth_kReal htenth_kReal_le_k)
