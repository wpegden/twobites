import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT4ExponentAlgebra]

theorem ParameterHierarchyT4ExponentAlgebra :
    ∀ η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let mReal := (n : ℝ) / L ^ 2
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      0 < (n : ℝ) →
      0 < L →
      0 < m →
      0 ≤ kReal →
      2 ≤ k →
      kReal ≤ k →
      m ≤ mReal →
      (2 * k * L + L) *
          (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤ kReal ^ 4 →
      2 * k * L + L ≤
        RealChooseTwo k ^ 2 /
          (L * m * Real.rpow (n : ℝ) (8 * η)) := by
-- BODY
  intro η n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let mReal := (n : ℝ) / L ^ 2
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  intro hn_pos hL hm hkReal_nonneg htwo_le_k hkReal_le_k hm_le_mReal hthreshold
  have hnPow : 0 < Real.rpow (n : ℝ) (8 * η) :=
    Real.rpow_pos_of_pos hn_pos (8 * η)
  have hk_nonneg : 0 ≤ k := le_trans (by norm_num : (0 : ℝ) ≤ 2) htwo_le_k
  have hA_nonneg : 0 ≤ 2 * k * L + L := by nlinarith [hL, hk_nonneg]
  have hden_pos : 0 < L * m * Real.rpow (n : ℝ) (8 * η) := by positivity
  have hchoose_bounds := RealChooseTwoQuadraticBounds k hk_nonneg
  have hchoose_lower : k ^ 2 / 4 ≤ RealChooseTwo k :=
    (hchoose_bounds.1 htwo_le_k).1
  have hchoose_nonneg : 0 ≤ RealChooseTwo k := by
    have hk_sq_quarter_nonneg : 0 ≤ k ^ 2 / 4 := by positivity
    exact le_trans hk_sq_quarter_nonneg hchoose_lower
  have hkReal_sq_le_k_sq : kReal ^ 2 ≤ k ^ 2 := by
    nlinarith [sq_nonneg (k - kReal), hkReal_nonneg, hkReal_le_k]
  have hkReal_four_le_k_four : kReal ^ 4 ≤ k ^ 4 := by
    nlinarith [sq_nonneg (k ^ 2 - kReal ^ 2), hkReal_sq_le_k_sq]
  have hk_four_le_choose : k ^ 4 ≤ 16 * RealChooseTwo k ^ 2 := by
    nlinarith [sq_nonneg (RealChooseTwo k - k ^ 2 / 4), hchoose_lower]
  have hden_le :
      16 * L * m * Real.rpow (n : ℝ) (8 * η) ≤
        16 * L * mReal * Real.rpow (n : ℝ) (8 * η) := by
    nlinarith [hL, hm, hnPow, hm_le_mReal]
  have hthreshold_m :
      (2 * k * L + L) * (16 * L * m * Real.rpow (n : ℝ) (8 * η)) ≤
        kReal ^ 4 := by
    calc
      (2 * k * L + L) * (16 * L * m * Real.rpow (n : ℝ) (8 * η))
          ≤ (2 * k * L + L) *
              (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) :=
            mul_le_mul_of_nonneg_left hden_le hA_nonneg
      _ ≤ kReal ^ 4 := hthreshold
  have hscaled :
      (2 * k * L + L) * (16 * L * m * Real.rpow (n : ℝ) (8 * η)) ≤
        16 * RealChooseTwo k ^ 2 := by
    exact le_trans hthreshold_m (le_trans hkReal_four_le_k_four hk_four_le_choose)
  have hmain :
      (2 * k * L + L) * (L * m * Real.rpow (n : ℝ) (8 * η)) ≤
        RealChooseTwo k ^ 2 := by
    nlinarith
  exact (le_div_iff₀ hden_pos).2 hmain
