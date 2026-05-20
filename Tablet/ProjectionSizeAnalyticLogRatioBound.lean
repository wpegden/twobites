import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.Preamble

-- [TABLET NODE: ProjectionSizeAnalyticLogRatioBound]

theorem ProjectionSizeAnalyticLogRatioBound {n m k : ℕ} {ε L : ℝ} (hL : L = Real.log (n : ℝ))
    (hm : (n : ℝ) / (2 * L ^ 2) ≤ m)
    (hk : (k : ℝ) ≤ 2 * (1 + ε) * Real.sqrt ((n : ℝ) * L))
    (hk_pos : 1 ≤ k)
    (heps : 0 < ε)
    (hL_ge_1 : 1 ≤ L) :
    (1/2 : ℝ) * L - (5/2 : ℝ) * Real.log L - Real.log (4 * (1 + ε)) ≤ Real.log ((m : ℝ) / (k : ℝ)) := by
-- BODY
  have hk_pos_real : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk_pos
  have hn_pos_real : (0 : ℝ) < n := by
    by_contra! h
    have hn0 : (n : ℝ) = 0 := le_antisymm h (by exact_mod_cast Nat.zero_le n)
    rw [hL, hn0, Real.log_zero] at hL_ge_1
    norm_num at hL_ge_1
  have L_pos : 0 < L := by linarith
  have hm_pos : (0 : ℝ) < m := by
    calc (0:ℝ) < (n:ℝ) / (2 * L^2) := div_pos hn_pos_real (mul_pos zero_lt_two (by positivity))
      _ ≤ (m:ℝ) := hm
  
  have hl1 : Real.log ((n:ℝ) / (2 * L^2)) ≤ Real.log (m:ℝ) :=
    Real.log_le_log (div_pos hn_pos_real (by positivity)) hm
  
  have h_num : Real.log ((n:ℝ) / (2 * L^2)) = L - Real.log 2 - 2 * Real.log L := by
    have hz2 : (0 : ℝ) < 2 := zero_lt_two
    have hzL : (0 : ℝ) < L ^ 2 := by positivity
    rw [Real.log_div hn_pos_real.ne' (mul_pos hz2 hzL).ne']
    rw [Real.log_mul hz2.ne' hzL.ne']
    have : Real.log (L ^ 2) = 2 * Real.log L := by
      have : L ^ 2 = L ^ (2 : ℕ) := by norm_cast
      rw [this, Real.log_pow]
      norm_cast
    rw [this, ← hL]
    ring

  have hk_upper_pos : (0 : ℝ) < 2 * (1 + ε) * Real.sqrt ((n : ℝ) * L) := by
    apply mul_pos (mul_pos zero_lt_two (by linarith)) (Real.sqrt_pos.mpr (by positivity))

  have hl2 : Real.log (k:ℝ) ≤ Real.log (2 * (1 + ε) * Real.sqrt ((n:ℝ) * L)) :=
    Real.log_le_log hk_pos_real hk

  have h_den : Real.log (2 * (1 + ε) * Real.sqrt ((n:ℝ) * L)) = Real.log 2 + Real.log (1 + ε) + (1/2:ℝ) * L + (1/2:ℝ) * Real.log L := by
    have hz2 : (0:ℝ) < 2 := zero_lt_two
    have hze : (0:ℝ) < 1 + ε := by linarith
    have hzsq : (0:ℝ) < Real.sqrt ((n:ℝ) * L) := Real.sqrt_pos.mpr (by positivity)
    rw [Real.log_mul (by positivity) hzsq.ne']
    rw [Real.log_mul hz2.ne' hze.ne']
    have : Real.log (Real.sqrt ((n:ℝ) * L)) = (1/2:ℝ) * Real.log ((n:ℝ) * L) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
    rw [this, Real.log_mul hn_pos_real.ne' L_pos.ne', ← hL]
    ring
  
  have hl3 : Real.log ((m:ℝ) / (k:ℝ)) = Real.log (m:ℝ) - Real.log (k:ℝ) :=
    Real.log_div hm_pos.ne' hk_pos_real.ne'
  
  rw [hl3]
  have h_log4 : Real.log (4 * (1 + ε)) = 2 * Real.log 2 + Real.log (1 + ε) := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by positivity)]
    have : Real.log ((2:ℝ) ^ 2) = 2 * Real.log 2 := by
      have : (2:ℝ) ^ 2 = (2:ℝ) ^ (2 : ℕ) := by norm_cast
      rw [this, Real.log_pow]
      norm_cast
    rw [this]

  rw [h_log4]
  linarith
