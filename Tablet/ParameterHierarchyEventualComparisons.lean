import Tablet.RealChooseTwo
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff

-- [TABLET NODE: ParameterHierarchyEventualComparisons]

noncomputable def ParameterHierarchyEventualComparisons
    (ε ε1 ε2 : ℝ) (n0 : ℕ) : Prop :=
-- BODY
  ∀ n : ℕ, n0 < n →
    let kReal := (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
    let K := TwoBiteNaturalIndependenceScale (1 + ε) n
    let k := (K : ℝ)
    let mReal := (n : ℝ) / (Real.log (n : ℝ)) ^ 2
    let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
    let p := (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
    let t1 := Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) /
      Real.log (Real.log (n : ℝ))
    let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε)
    let t3 := Real.rpow (n : ℝ) (2 * ε)
    0 < m ∧
      0 ≤ p ∧
      p ≤ (1 / 2 : ℝ) ∧
      1 ≤ 2 * p * m ∧
      kReal ≤ k ∧
      k < kReal + 1 ∧
      m ≤ mReal ∧
      mReal < m + 1 ∧
    Real.rpow (n : ℝ) (4 * ε) * k ≤ (ε1 / 2) * k ^ 2 ∧
      2 * k * (Real.log (n : ℝ)) ^ 2 ≤ (ε1 / 8) * k ^ 2 ∧
      (1 / (2 * Real.log (n : ℝ))) * RealChooseTwo k +
            2 * k * (Real.log (n : ℝ)) ^ 2 +
          (1 / Real.sqrt (Real.log (n : ℝ))) * RealChooseTwo k ≤
        (2 / Real.sqrt (Real.log (n : ℝ))) * RealChooseTwo k ∧
      Real.exp
          (-(RealChooseTwo k ^ 2 /
              (Real.log (n : ℝ) *
                m *
                  Real.rpow (n : ℝ) (8 * ε)))) *
        (Nat.choose n K : ℝ) ≤ (n : ℝ)⁻¹ ∧
      (2 / Real.sqrt (Real.log (n : ℝ))) * RealChooseTwo k ≤
        (ε1 / 2) * k ^ 2 ∧
      4 * Real.log k ≤ (ε ^ 3 / 2) * p * k ^ 2 ∧
      t1 * k ≤ ε1 * k ^ 2 ∧
      RealChooseTwo (2 * k / t1 + 1) *
          (100 * (Real.log (n : ℝ)) ^ 3) ≤ (1 / 2 : ℝ) * k ∧
      (2 * k / t1) * (2 * p * m) ≤ (ε1 / 10) * k ∧
      (2 * k / t1) * RealChooseTwo (2 * p * m) ≤ ε1 * k ^ 2 ∧
      RealChooseTwo (2 * k / t1 + 1) *
          (2 * 100 * (Real.log (n : ℝ)) ^ 3) ≤ (ε1 / 10) * k ∧
      RealChooseTwo (2 * k / t1 + 1) *
          RealChooseTwo (2 * 100 * (Real.log (n : ℝ)) ^ 3) ≤
        (ε1 / 10) * k ^ 2 ∧
      3 * ε2 ≤ ε1 / 10 ∧
      0 ≤ ε2 ∧ ε2 ≤ 1 ∧
      2 * p * m ≤ (ε2 / 100) * t1 ∧
      (2 * k / t1 + 1) * (100 * (Real.log (n : ℝ)) ^ 3) ≤
        (ε2 / 100) * t1 ∧
      (2 * k / t1 + 1) * (2 * 100 * (Real.log (n : ℝ)) ^ 3) ≤
        (ε2 / 100) * t1 ∧
      (2 * k / t1 + 1) * (400 * (Real.log (n : ℝ)) ^ 5) ≤
        (ε2 / 100) * t1 ∧
      t2 * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) ≤ ε1 * k ∧
      TwoBiteLargeCutoff ε n < TwoBiteHugeCutoff n ∧
      (1 + ε2) * (Real.log (n : ℝ)) ^ 2 *
            (t2 / Real.log (n : ℝ)) +
          Real.log (n : ℝ) * (1 + ε2) * p * m <
        TwoBiteHugeCutoff n ∧
      100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) *
          (Real.log (n : ℝ)) ^ 3 ≤ TwoBiteLargeCutoff ε n ∧
      k < Real.rpow (n : ℝ) (1 / 4 : ℝ) * t2 -
        RealChooseTwo (Real.rpow (n : ℝ) (1 / 4 : ℝ)) *
          (100 * (Real.log (n : ℝ)) ^ 3) ∧
      t3 ^ 2 * k ≤ (ε1 / 2) * k ^ 2 ∧
      k * (2 * k / Real.log (n : ℝ) + Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
        ε1 * k ^ 2 ∧
      8 * Real.sqrt ε1 * p * k ^ 2 + 10 * ε1 * p * k ^ 2 +
          4 * Real.log k ≤ ε ^ 3 * p * k ^ 2 ∧
      Real.exp
        (k * Real.log (n : ℝ) +
          2 * k * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
            Real.log (n : ℝ) -
          Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) ≤ ε1 ∧
      Real.exp
        (-(ε / 4) * k * Real.log (n : ℝ)) ≤ ε1
