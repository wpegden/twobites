import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT6LogAlgebra]

open scoped Topology

theorem ParameterHierarchyT6LogAlgebra :
    ∀ η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      0 < η →
      0 < (n : ℝ) →
      0 < L →
      kReal ≤ k →
      k < 2 * kReal →
      8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) /
          ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) ≤ η ^ 3 / 2 →
      4 * Real.log k ≤ (η ^ 3 / 2) * p * k ^ 2 := by
-- BODY
  intro η n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  intro hη hn_pos hL_pos hkReal_le_k hk_lt_two hthreshold
  have hκ_pos : 0 < 1 + η := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hnL_pos : 0 < (n : ℝ) * L := mul_pos hn_pos hL_pos
  have hkReal_pos : 0 < kReal := by
    dsimp [kReal]
    positivity
  have hk_pos : 0 < k := lt_of_lt_of_le hkReal_pos hkReal_le_k
  have hlog_le :
      Real.log k ≤ Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) := by
    have hk_le_arg : k ≤ 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := by
      linarith
    exact Real.log_le_log hk_pos hk_le_arg
  have hden_pos :
      0 < (1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ) := by
    have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hLpow_pos : 0 < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL_pos _
    positivity
  have hthreshold_mul :
      8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
        (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) := by
    exact (div_le_iff₀ hden_pos).1 hthreshold
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hkReal_sq_le_k_sq : kReal ^ 2 ≤ k ^ 2 := by
    nlinarith [sq_nonneg (k - kReal), le_of_lt hkReal_pos, hkReal_le_k]
  have hp_kReal_sq_le_hp_k_sq :
      p * kReal ^ 2 ≤ p * k ^ 2 :=
    mul_le_mul_of_nonneg_left hkReal_sq_le_k_sq hp_nonneg
  have hpkReal_eq :
      p * kReal ^ 2 =
        ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) / 2 := by
    dsimp [p, kReal]
    have hsqrt_div :
        Real.sqrt (L / (n : ℝ)) = Real.sqrt L / Real.sqrt (n : ℝ) := by
      rw [div_eq_mul_inv]
      rw [Real.sqrt_mul hL_nonneg ((n : ℝ)⁻¹)]
      rw [Real.sqrt_inv]
      ring
    have hsqrt_n_mul :
        Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt hn_nonneg
    have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
      calc
        L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
        _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
        _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hsqrt_div]
    rw [show ((1 + η) * Real.sqrt ((n : ℝ) * L)) ^ 2 =
        (1 + η) ^ 2 * ((n : ℝ) * L) by
      rw [mul_pow]
      rw [show Real.sqrt ((n : ℝ) * L) ^ 2 = (n : ℝ) * L by
        exact Real.sq_sqrt (le_of_lt hnL_pos)]]
    rw [hL_rpow]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos)]
    nth_rewrite 1 [show (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) by
      exact hsqrt_n_mul.symm]
    ring
  have hlog_arg_bound :
      4 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
        (η ^ 3 / 2) * (p * kReal ^ 2) := by
    calc
      4 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L))
          = (8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L))) / 2 := by ring
      _ ≤ ((η ^ 3 / 2) *
          ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ))) / 2 :=
            div_le_div_of_nonneg_right hthreshold_mul (by norm_num)
      _ = (η ^ 3 / 2) * (p * kReal ^ 2) := by rw [hpkReal_eq]; ring
  have hcoef_nonneg : 0 ≤ η ^ 3 / 2 := by positivity
  calc
    4 * Real.log k
        ≤ 4 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) :=
          mul_le_mul_of_nonneg_left hlog_le (by norm_num)
    _ ≤ (η ^ 3 / 2) * (p * kReal ^ 2) := hlog_arg_bound
    _ ≤ (η ^ 3 / 2) * (p * k ^ 2) :=
      mul_le_mul_of_nonneg_left hp_kReal_sq_le_hp_k_sq hcoef_nonneg
    _ = (η ^ 3 / 2) * p * k ^ 2 := by ring
