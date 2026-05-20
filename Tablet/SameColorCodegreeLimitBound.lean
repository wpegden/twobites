import Tablet.NegligibleProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteEdgeProbability
import Tablet.OppositeProjectionChooseExponentialBound

open Filter Topology Classical

-- [TABLET NODE: SameColorCodegreeLimitBound]

theorem SameColorCodegreeLimitBound (m : ℕ → ℕ)
      (hm : ∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) :
      NegligibleProbability (fun n =>
        2 * (m n : ℝ)^2 * ((Nat.choose (m n) ⌈Real.log (n : ℝ)⌉₊ : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ ⌈Real.log (n : ℝ)⌉₊)) := by
-- BODY
  unfold NegligibleProbability
  have h_log_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_two_div_n :
      Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h_base_small :
      ∀ᶠ n : ℕ in atTop,
        Real.exp 1 / (4 * (Real.log (n : ℝ)) ^ 2) ≤ Real.exp (-3 : ℝ) := by
    have hL2_atTop :
        Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2) atTop atTop := by
      exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp h_log_atTop
    have hden_atTop :
        Tendsto (fun n : ℕ => 4 * (Real.log (n : ℝ)) ^ 2) atTop atTop := by
      exact hL2_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    have hsmall :
        Tendsto (fun n : ℕ => Real.exp 1 / (4 * (Real.log (n : ℝ)) ^ 2))
          atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop hden_atTop
    exact hsmall.eventually (Iic_mem_nhds (Real.exp_pos (-3)))
  have h_bound :
      ∀ᶠ n : ℕ in atTop,
        2 * (m n : ℝ)^2 * ((Nat.choose (m n) ⌈Real.log (n : ℝ)⌉₊ : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ ⌈Real.log (n : ℝ)⌉₊) ≤
            (2 : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ),
      h_log_atTop.eventually_ge_atTop (1 : ℝ), h_base_small] with n hn3 hL_ge_one hbase_small
    let L : ℝ := Real.log (n : ℝ)
    let T : ℕ := ⌈Real.log (n : ℝ)⌉₊
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn3)
    have hL_pos : 0 < L := by
      have : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le this (by simpa [L] using hL_ge_one)
    have hL_nonneg : 0 ≤ L := hL_pos.le
    have hT_ge_L : L ≤ (T : ℝ) := by
      simpa [T, L] using (Nat.le_ceil (Real.log (n : ℝ)))
    have hT_pos : 0 < (T : ℝ) := lt_of_lt_of_le hL_pos hT_ge_L
    have hM_nonneg : 0 ≤ (m n : ℝ) := by positivity
    have hM_le : (m n : ℝ) ≤ (n : ℝ) / L ^ 2 := by
      rw [hm n, TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount, TwoBiteStretch]
      have hred_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by positivity
      exact Nat.floor_le hred_nonneg
    have hp_sq :
        (TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2 = (1 / 4 : ℝ) * (L / (n : ℝ)) := by
      unfold TwoBiteEdgeProbability
      have hsqrt_sq : (Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) ^ 2 =
          Real.log (n : ℝ) / (n : ℝ) := by
        exact Real.sq_sqrt (div_nonneg (by simpa [L] using hL_nonneg) hn_pos.le)
      calc
        ((1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) ^ 2
            = (1 / 4 : ℝ) * (Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) ^ 2 := by ring
        _ = (1 / 4 : ℝ) * (L / (n : ℝ)) := by
          rw [hsqrt_sq]
    have htail_nonneg :
        0 ≤ ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T := by positivity
    have hchoose_bound := OppositeProjectionChooseExponentialBound (m n) T
    have hbase_le :
        ((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) *
            ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ≤
          Real.exp (-3 : ℝ) := by
      have hden_le :
          (Real.exp 1 * (m n : ℝ)) / (T : ℝ) ≤
            (Real.exp 1 * ((n : ℝ) / L ^ 2)) / L := by
        apply div_le_div₀
        · positivity
        · gcongr
        · exact hL_pos
        · exact hT_ge_L
      have hp2_nonneg : 0 ≤ (1 / 4 : ℝ) * (L / (n : ℝ)) := by positivity
      calc
        ((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) *
            ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2)
            = ((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) *
                ((1 / 4 : ℝ) * (L / (n : ℝ))) := by rw [hp_sq]
        _ ≤ ((Real.exp 1 * ((n : ℝ) / L ^ 2)) / L) *
                ((1 / 4 : ℝ) * (L / (n : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hden_le hp2_nonneg
        _ = Real.exp 1 / (4 * L ^ 2) := by
              field_simp [hn_pos.ne', hL_pos.ne']
        _ ≤ Real.exp (-3 : ℝ) := by
              simpa [L] using hbase_small
    have hbase_nonneg :
        0 ≤ ((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) *
            ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) := by
      positivity
    have htail_le :
        (Nat.choose (m n) T : ℝ) *
            ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T ≤
          Real.exp (-3 * L) := by
      calc
        (Nat.choose (m n) T : ℝ) *
            ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T
            ≤ ((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) ^ T *
                ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T := by
              exact mul_le_mul_of_nonneg_right hchoose_bound htail_nonneg
        _ = (((Real.exp 1 * (m n : ℝ)) / (T : ℝ)) *
                ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2)) ^ T := by
              rw [mul_pow]
        _ ≤ (Real.exp (-3 : ℝ)) ^ T := by
              exact pow_le_pow_left₀ hbase_nonneg hbase_le T
        _ = Real.exp (-3 * (T : ℝ)) := by
              rw [← Real.exp_nat_mul]
              ring_nf
        _ ≤ Real.exp (-3 * L) := by
              exact Real.exp_le_exp.mpr (by nlinarith)
    have hL_sq_ge_one : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have hM_le_n : (m n : ℝ) ≤ (n : ℝ) := by
      calc
        (m n : ℝ) ≤ (n : ℝ) / L ^ 2 := hM_le
        _ ≤ (n : ℝ) := by exact div_le_self hn_pos.le hL_sq_ge_one
    have hM_sq_le_n_sq : (m n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - (m n : ℝ))]
    have htail_prod_nonneg :
        0 ≤ (Nat.choose (m n) T : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T := by
      positivity
    calc
      2 * (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ T)
          ≤ 2 * (n : ℝ)^2 * Real.exp (-3 * L) := by
            gcongr
      _ = (2 : ℝ) / (n : ℝ) := by
            have h_expL : Real.exp L = (n : ℝ) := by
              simpa [L] using Real.exp_log hn_pos
            have h_exp_neg :
                Real.exp (-3 * L) = ((n : ℝ) ^ 3)⁻¹ := by
              calc
                Real.exp (-3 * L) = (Real.exp (3 * L))⁻¹ := by
                  rw [show -3 * L = -(3 * L) by ring, Real.exp_neg]
                _ = ((Real.exp L) ^ 3)⁻¹ := by
                  congr 1
                  rw [← Real.exp_nat_mul]
                  ring_nf
                _ = ((n : ℝ) ^ 3)⁻¹ := by rw [h_expL]
            rw [h_exp_neg]
            field_simp [hn_pos.ne']
  have h_nonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ 2 * (m n : ℝ)^2 * ((Nat.choose (m n) ⌈Real.log (n : ℝ)⌉₊ : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ ⌈Real.log (n : ℝ)⌉₊) := by
    filter_upwards with n
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_two_div_n h_nonneg h_bound
