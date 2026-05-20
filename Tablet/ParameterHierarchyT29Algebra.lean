import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT29Algebra]

theorem ParameterHierarchyT29Algebra :
    ∀ η ε1 k : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      0 < η →
      0 < (n : ℝ) →
      0 < L →
      (1 + η) * Real.sqrt ((n : ℝ) * L) ≤ k →
      Real.exp
          (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
            Real.sqrt L * L) ≤ ε1 →
      Real.exp (-(η / 4) * k * L) ≤ ε1 := by
-- BODY
  intro η ε1 k n
  dsimp
  let L := Real.log (n : ℝ)
  intro hη_pos hn_pos hL_pos hkReal_le_k hthreshold
  have hL_pos_local : 0 < L := by
    simpa [L] using hL_pos
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hη_quarter_nonneg : 0 ≤ η / 4 := by positivity
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos_local
  have hthreshold_local :
      Real.exp
          (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
            Real.sqrt L * L) ≤ ε1 := by
    simpa [L] using hthreshold
  have hscaled_k :
      (η / 4) * ((1 + η) * Real.sqrt ((n : ℝ) * L)) * L ≤
        (η / 4) * k * L := by
    have hleft :=
      mul_le_mul_of_nonneg_left hkReal_le_k hη_quarter_nonneg
    exact mul_le_mul_of_nonneg_right hleft hL_nonneg
  have hlower :
      (η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L ≤
        (η / 4) * k * L := by
    have hscaled_rewritten :
        (η / 4) * ((1 + η) * (Real.sqrt (n : ℝ) * Real.sqrt L)) * L ≤
          (η / 4) * k * L := by
      simpa [Real.sqrt_mul hn_nonneg] using hscaled_k
    calc
      (η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L =
          (η / 4) * ((1 + η) * (Real.sqrt (n : ℝ) * Real.sqrt L)) * L := by
        ring
      _ ≤ (η / 4) * k * L := hscaled_rewritten
  have hexponent_le :
      -(η / 4) * k * L ≤
        -(η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by
    calc
      -(η / 4) * k * L = -((η / 4) * k * L) := by ring
      _ ≤ -((η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
          Real.sqrt L * L) := neg_le_neg hlower
      _ = -(η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by
        ring
  exact le_trans (Real.exp_le_exp.2 hexponent_le) hthreshold_local
