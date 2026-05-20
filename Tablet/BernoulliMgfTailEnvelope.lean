import Tablet.Preamble
import Mathlib.Tactic

open Classical

-- [TABLET NODE: BernoulliMgfTailEnvelope]

theorem BernoulliMgfTailEnvelope (m : ℕ) (p ε t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (m : ℝ) *
      (Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          (1 - p + p * Real.exp t) ^ (m - 1) +
        Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          (1 - p + p * Real.exp (-t)) ^ (m - 1)) ≤
    (m : ℝ) *
      (Real.exp (-(t * ((1 + ε) * p * (m : ℝ))) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) +
        Real.exp (t * ((1 - ε) * p * (m : ℝ)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1)))) := by
-- BODY
  have hbase_nonneg :
      ∀ u : ℝ, 0 ≤ 1 - p + p * Real.exp u := by
    intro u
    have hp_exp_nonneg : 0 ≤ p * Real.exp u :=
      mul_nonneg hp0 (Real.exp_pos u).le
    nlinarith
  have hpow_bound :
      ∀ u : ℝ,
        (1 - p + p * Real.exp u) ^ (m - 1) ≤
        Real.exp (((m - 1 : ℕ) : ℝ) * (p * (Real.exp u - 1))) := by
    intro u
    have hbase_eq : 1 - p + p * Real.exp u = p * (Real.exp u - 1) + 1 := by
      ring
    have hbase_le_exp :
        1 - p + p * Real.exp u ≤ Real.exp (p * (Real.exp u - 1)) := by
      rw [hbase_eq]
      exact Real.add_one_le_exp _
    have hpow :=
      pow_le_pow_left₀ (hbase_nonneg u) hbase_le_exp (m - 1)
    have hexp_pow :
        Real.exp (p * (Real.exp u - 1)) ^ (m - 1) =
        Real.exp (((m - 1 : ℕ) : ℝ) * (p * (Real.exp u - 1))) := by
      rw [← Real.exp_nat_mul]
    exact le_trans hpow (le_of_eq hexp_pow)
  have hupper :
      Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          (1 - p + p * Real.exp t) ^ (m - 1) ≤
        Real.exp (-(t * ((1 + ε) * p * (m : ℝ))) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) := by
    calc
      Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          (1 - p + p * Real.exp t) ^ (m - 1)
        ≤ Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          Real.exp (((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) := by
            exact mul_le_mul_of_nonneg_left (hpow_bound t) (Real.exp_pos _).le
      _ = Real.exp (-(t * ((1 + ε) * p * (m : ℝ))) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) := by
            rw [Real.exp_add]
  have hlower :
      Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          (1 - p + p * Real.exp (-t)) ^ (m - 1) ≤
        Real.exp (t * ((1 - ε) * p * (m : ℝ)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))) := by
    calc
      Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          (1 - p + p * Real.exp (-t)) ^ (m - 1)
        ≤ Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          Real.exp (((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))) := by
            exact mul_le_mul_of_nonneg_left (hpow_bound (-t)) (Real.exp_pos _).le
      _ = Real.exp (t * ((1 - ε) * p * (m : ℝ)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))) := by
            rw [Real.exp_add]
  exact mul_le_mul_of_nonneg_left (add_le_add hupper hlower) (Nat.cast_nonneg m)
