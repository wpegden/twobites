import Tablet.RealChooseTwoQuadraticBounds
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT5ChooseBound]

theorem ParameterHierarchyT5ChooseBound :
    ∀ ε1 η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      0 ≤ k →
      2 ≤ k →
      0 < Real.sqrt L →
      1 / Real.sqrt L ≤ ε1 / 2 →
      (2 / Real.sqrt L) * RealChooseTwo k ≤ (ε1 / 2) * k ^ 2 := by
-- BODY
  intro ε1 η n
  dsimp
  let L := Real.log (n : ℝ)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  intro hk_nonneg htwo_le_k hsqrt_pos hthreshold
  have hchoose_upper : RealChooseTwo k ≤ k ^ 2 / 2 :=
    ((RealChooseTwoQuadraticBounds k hk_nonneg).1 htwo_le_k).2
  have hcoef_nonneg : 0 ≤ 2 / Real.sqrt L := by positivity
  have hfirst :
      (2 / Real.sqrt L) * RealChooseTwo k ≤
        (2 / Real.sqrt L) * (k ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hchoose_upper hcoef_nonneg
  have hsquare_nonneg : 0 ≤ k ^ 2 := sq_nonneg k
  calc
    (2 / Real.sqrt L) * RealChooseTwo k
        ≤ (2 / Real.sqrt L) * (k ^ 2 / 2) := hfirst
    _ = (1 / Real.sqrt L) * k ^ 2 := by ring
    _ ≤ (ε1 / 2) * k ^ 2 :=
      mul_le_mul_of_nonneg_right hthreshold hsquare_nonneg
