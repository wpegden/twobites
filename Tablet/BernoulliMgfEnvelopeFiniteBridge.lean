import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Tablet.Preamble

open Filter

-- [TABLET NODE: BernoulliMgfEnvelopeFiniteBridge]

theorem BernoulliMgfEnvelopeFiniteBridge (m : ℕ) (p ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlarge : 100 / ε ≤ p * (m : ℝ)) :
    let t := Real.log (1 + ε / 2)
    0 < t ∧
    (m : ℝ) *
      (Real.exp (-(t * ((1 + ε) * p * (m : ℝ))) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) +
        Real.exp (t * ((1 - ε) * p * (m : ℝ)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1)))) ≤
    (m : ℝ) *
      (Real.exp (-((ε ^ 2 / 100) * p * (m : ℝ))) +
        Real.exp (-((ε ^ 2 / 100) * p * (m : ℝ)))) := by
-- BODY
  let M : ℝ := (m : ℝ)
  let q : ℝ := p * M
  let c : ℝ := ε ^ 2 / 100
  let t : ℝ := Real.log (1 + ε / 2)
  have hε_nonneg : 0 ≤ ε := hε0.le
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg m
  have hq_nonneg : 0 ≤ q := mul_nonneg hp0 hM_nonneg
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have harg_pos : 0 < 1 + ε / 2 := by positivity
  have harg_gt_one : 1 < 1 + ε / 2 := by linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact Real.log_pos harg_gt_one
  have ht_exp : Real.exp t = 1 + ε / 2 := by
    dsimp [t]
    rw [Real.exp_log harg_pos]
  have ht_exp_sub : Real.exp t - 1 = ε / 2 := by
    rw [ht_exp]
    ring
  have ht_exp_neg_sub : Real.exp (-t) - 1 = -(ε / (ε + 2)) := by
    rw [Real.exp_neg, ht_exp]
    field_simp [show ε + 2 ≠ 0 by linarith]
    ring
  have ht_le : t ≤ ε / 2 := by
    have h := Real.log_le_sub_one_of_pos harg_pos
    dsimp [t] at h ⊢
    linarith
  have ht_lower_raw :
      2 * (ε / 2) / (ε / 2 + 2) ≤ t := by
    dsimp [t]
    exact Real.le_log_one_add_of_nonneg (by positivity : 0 ≤ ε / 2)
  have ht_lower : 2 * ε / (ε + 4) ≤ t := by
    have heq : 2 * (ε / 2) / (ε / 2 + 2) = 2 * ε / (ε + 4) := by
      field_simp [show ε + 4 ≠ 0 by linarith]
      ring
    simpa [heq] using ht_lower_raw
  have hupper_gain :
      c ≤ (1 + ε) * t - ε / 2 := by
    have honeps_nonneg : 0 ≤ 1 + ε := by positivity
    have hmul := mul_le_mul_of_nonneg_left ht_lower honeps_nonneg
    have hcoef :
        c ≤ (1 + ε) * (2 * ε / (ε + 4)) - ε / 2 := by
      dsimp [c]
      field_simp [show ε + 4 ≠ 0 by linarith]
      nlinarith [hε0, hε1, sq_nonneg ε]
    nlinarith
  have hupper_exp_le :
      -(t * ((1 + ε) * p * M)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1)) ≤
        -(c * q) := by
    have hpred_le : ((m - 1 : ℕ) : ℝ) ≤ M := by
      dsimp [M]
      exact_mod_cast Nat.sub_le m 1
    have hfactor_nonneg : 0 ≤ p * (Real.exp t - 1) := by
      rw [ht_exp_sub]
      positivity
    have hpred_term_le :
        ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1)) ≤
          M * (p * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_right hpred_le hfactor_nonneg
    have hlinear :
        -(t * ((1 + ε) * p * M)) + M * (p * (Real.exp t - 1)) =
          (-((1 + ε) * t) + (Real.exp t - 1)) * q := by
      dsimp [q]
      ring
    have hcoef : -((1 + ε) * t) + (Real.exp t - 1) ≤ -c := by
      rw [ht_exp_sub]
      nlinarith
    have hcoef_mul := mul_le_mul_of_nonneg_right hcoef hq_nonneg
    calc
      -(t * ((1 + ε) * p * M)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))
          ≤ -(t * ((1 + ε) * p * M)) + M * (p * (Real.exp t - 1)) := by
            linarith
      _ = (-((1 + ε) * t) + (Real.exp t - 1)) * q := hlinear
      _ ≤ (-c) * q := hcoef_mul
      _ = -(c * q) := by ring
  have hq_pos : 0 < q := by
    have hlarge_pos : 0 < 100 / ε := by positivity
    exact lt_of_lt_of_le hlarge_pos (by simpa [q] using hlarge)
  have hM_pos : 0 < M := by
    by_contra hnot
    have hM_le_zero : M ≤ 0 := le_of_not_gt hnot
    have hM_zero : M = 0 := le_antisymm hM_le_zero hM_nonneg
    have hq_zero : q = 0 := by simp [q, hM_zero]
    linarith
  have hm_pos : 0 < m := by
    by_contra hnot
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hnot
    simp [M, hm_zero] at hM_pos
  have hp_le_small_q : p ≤ (ε / 100) * q := by
    have hscale_nonneg : 0 ≤ ε / 100 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlarge hscale_nonneg
    have hone_le : (1 : ℝ) ≤ (ε / 100) * q := by
      have heq : (ε / 100) * (100 / ε) = 1 := by
        field_simp [hε0.ne']
      calc
        (1 : ℝ) = (ε / 100) * (100 / ε) := heq.symm
        _ ≤ (ε / 100) * q := by simpa [q] using hmul
    exact le_trans hp1 hone_le
  have hpred_mul_eq : ((m - 1 : ℕ) : ℝ) * p = q - p := by
    rw [Nat.cast_pred hm_pos]
    dsimp [q, M]
    ring
  have hpred_p_lower :
      (1 - ε / 100) * q ≤ ((m - 1 : ℕ) : ℝ) * p := by
    rw [hpred_mul_eq]
    nlinarith
  have hneg_factor : Real.exp (-t) - 1 ≤ 0 := by
    rw [ht_exp_neg_sub]
    have hfrac_nonneg : 0 ≤ ε / (ε + 2) := by positivity
    linarith
  have hlower_coeff :
      (ε / 2) * (1 - ε) - (1 - ε / 100) * (ε / (ε + 2)) ≤ -c := by
    dsimp [c]
    field_simp [show ε + 2 ≠ 0 by linarith]
    nlinarith [hε0, hε1, sq_nonneg ε]
  have hlower_exp_le :
      t * ((1 - ε) * p * M) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1)) ≤
        -(c * q) := by
    have hone_minus_nonneg : 0 ≤ 1 - ε := by linarith
    have ht_term_le :
        t * ((1 - ε) * p * M) ≤ (ε / 2) * ((1 - ε) * q) := by
      have hmul := mul_le_mul_of_nonneg_right ht_le (mul_nonneg hone_minus_nonneg hq_nonneg)
      simpa [q, mul_assoc] using hmul
    have hpred_neg_le :
        ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1)) ≤
          ((1 - ε / 100) * q) * (Real.exp (-t) - 1) := by
      have hmul := mul_le_mul_of_nonpos_right hpred_p_lower hneg_factor
      simpa [mul_assoc] using hmul
    have hcoef_mul := mul_le_mul_of_nonneg_right hlower_coeff hq_nonneg
    calc
      t * ((1 - ε) * p * M) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))
          ≤ (ε / 2) * ((1 - ε) * q) +
              ((1 - ε / 100) * q) * (Real.exp (-t) - 1) := by
            linarith
      _ = ((ε / 2) * (1 - ε) - (1 - ε / 100) * (ε / (ε + 2))) * q := by
            rw [ht_exp_neg_sub]
            ring
      _ ≤ (-c) * q := hcoef_mul
      _ = -(c * q) := by ring
  have hupper_tail :
      Real.exp (-(t * ((1 + ε) * p * M)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) ≤
        Real.exp (-(c * q)) :=
    Real.exp_le_exp.mpr hupper_exp_le
  have hlower_tail :
      Real.exp (t * ((1 - ε) * p * M) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))) ≤
        Real.exp (-(c * q)) :=
    Real.exp_le_exp.mpr hlower_exp_le
  have hsum :
      Real.exp (-(t * ((1 + ε) * p * M)) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) +
        Real.exp (t * ((1 - ε) * p * M) +
          ((m - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1))) ≤
      Real.exp (-(c * q)) + Real.exp (-(c * q)) :=
    add_le_add hupper_tail hlower_tail
  have hmul := mul_le_mul_of_nonneg_left hsum hM_nonneg
  exact by
    simpa [M, q, c, t, mul_assoc] using (And.intro ht_pos hmul)
