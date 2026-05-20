import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT9Algebra]

theorem ParameterHierarchyT9Algebra :
    ∀ η ε1 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < ε1 →
      0 < (n : ℝ) →
      0 < L →
      0 < Real.log L →
      0 ≤ k →
      2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
      2 * Real.log L / L ^ 2 ≤ ε1 / 10 →
      (2 * k / t1) * (2 * p * m) ≤ (ε1 / 10) * k := by
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro _hε1 hn_pos hL_pos hlogL_pos hk_nonneg hmass hthreshold
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have ht1_pos : 0 < t1 := by
    dsimp [t1]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos hn_pos hL_pos)) hlogL_pos
  have hfactor_nonneg : 0 ≤ 2 * k / t1 := by
    exact div_nonneg (mul_nonneg (by norm_num) hk_nonneg) (le_of_lt ht1_pos)
  have hsqrt_nL :
      Real.sqrt ((n : ℝ) * L) = Real.sqrt (n : ℝ) * Real.sqrt L := by
    rw [Real.sqrt_mul hn_nonneg L]
  have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    calc
      L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
      _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hfactor_eq :
      (2 * k / t1) * (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) =
        k * (2 * Real.log L / L ^ 2) := by
    dsimp [t1]
    rw [hsqrt_nL, hL_rpow]
    field_simp [ne_of_gt hlogL_pos, ne_of_gt (Real.sqrt_pos.mpr hn_pos),
      ne_of_gt (Real.sqrt_pos.mpr hL_pos), ne_of_gt hL_pos]
    rw [show Real.sqrt L ^ 2 = L by exact Real.sq_sqrt hL_nonneg]
    ring
  calc
    (2 * k / t1) * (2 * p * m)
        ≤ (2 * k / t1) * (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass hfactor_nonneg
    _ = k * (2 * Real.log L / L ^ 2) := hfactor_eq
    _ ≤ k * (ε1 / 10) :=
      mul_le_mul_of_nonneg_left hthreshold hk_nonneg
    _ = (ε1 / 10) * k := by ring

