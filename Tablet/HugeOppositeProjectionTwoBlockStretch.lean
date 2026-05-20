import Tablet.RealChooseTwo

-- [TABLET NODE: HugeOppositeProjectionTwoBlockStretch]

theorem HugeOppositeProjectionTwoBlockStretch :
    ∀ {ε D b u : ℝ},
      0 ≤ ε →
      ε ≤ 1 →
      98 ≤ D →
      0 ≤ b →
      0 ≤ u →
      b + u = D →
        RealChooseTwo ((1 + ε) * b) + RealChooseTwo ((1 + ε) * u) ≤
          (1 + 10 * ε) * (RealChooseTwo b + RealChooseTwo u) := by
-- BODY
  intro ε D b u hε hε_le_one hD hb hu hsum
  have hsq : 0 ≤ (b - u) ^ 2 := sq_nonneg (b - u)
  have hsumsq : D ^ 2 ≤ 2 * (b ^ 2 + u ^ 2) := by
    nlinarith [hsq, hsum]
  have hcoef_nonneg : 0 ≤ (8 - ε) * (b ^ 2 + u ^ 2) - 9 * D := by
    nlinarith [hsumsq]
  have hgap_nonneg :
      0 ≤ ε * ((8 - ε) * (b ^ 2 + u ^ 2) - 9 * D) :=
    mul_nonneg hε hcoef_nonneg
  unfold RealChooseTwo
  nlinarith [hgap_nonneg, hsum]
