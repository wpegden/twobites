import Tablet.Preamble

-- [TABLET NODE: ProjectionMassBoundFromEstimates]

theorem ProjectionMassBoundFromEstimates :
    ∀ {ε2 δ D T S : ℝ},
      0 ≤ ε2 →
      ε2 ≤ 1 →
      δ = ε2 / 100 →
      0 ≤ T →
      (1 - δ) * T ≤ S →
      (1 - 2 * δ) * S ≤ D →
      T ≤ (1 + ε2) * D := by
-- BODY
  intro ε2 δ D T S hε2 hε2_le hδ hT hcompress hdef
  subst δ
  have hfac2_nonneg : 0 ≤ 1 - 2 * (ε2 / 100) := by nlinarith
  have hfac_prod_T :
      ((1 - ε2 / 100) * (1 - 2 * (ε2 / 100))) * T ≤ D := by
    have hmul := mul_le_mul_of_nonneg_left hcompress hfac2_nonneg
    nlinarith only [hmul, hdef]
  have hnumeric :
      1 ≤ (1 + ε2) * ((1 - ε2 / 100) * (1 - 2 * (ε2 / 100))) := by
    have hcoef_nonneg :
        0 ≤ (97 / 100 : ℝ) - (149 / 5000 : ℝ) * ε2 +
          (1 / 5000 : ℝ) * ε2 ^ 2 := by
      nlinarith [sq_nonneg ε2]
    have hgap_nonneg :
        0 ≤ ε2 *
          ((97 / 100 : ℝ) - (149 / 5000 : ℝ) * ε2 +
            (1 / 5000 : ℝ) * ε2 ^ 2) :=
      mul_nonneg hε2 hcoef_nonneg
    nlinarith [hgap_nonneg]
  have hT_le_scaled :
      T ≤ (1 + ε2) * (((1 - ε2 / 100) * (1 - 2 * (ε2 / 100))) * T) := by
    nlinarith [hT, hnumeric]
  have hscale_nonneg : 0 ≤ 1 + ε2 := by nlinarith
  exact le_trans hT_le_scaled (mul_le_mul_of_nonneg_left hfac_prod_T hscale_nonneg)
