import Tablet.NaturalParameterApproximation
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.ParameterHierarchyBaseThreshold
import Tablet.ParameterHierarchyInitialPowerComparisons
import Tablet.ParameterHierarchyInitialPowerRatioThreshold
import Tablet.ParameterHierarchyT3ChooseComparison
import Tablet.ParameterHierarchyT3Threshold
import Tablet.ParameterHierarchyT4ChooseExpBound
import Tablet.ParameterHierarchyT4ExponentAlgebra
import Tablet.ParameterHierarchyT4ExponentThreshold
import Tablet.ParameterHierarchyT4ExponentialConclusion
import Tablet.ParameterHierarchyT5ChooseBound
import Tablet.ParameterHierarchyT5SqrtLogThreshold
import Tablet.ParameterHierarchyT6LogAlgebra
import Tablet.ParameterHierarchyT6LogThreshold
import Tablet.ParameterHierarchyT7Algebra
import Tablet.ParameterHierarchyT7LogLogThreshold
import Tablet.ParameterHierarchyT8Algebra
import Tablet.ParameterHierarchyT8Threshold
import Tablet.ParameterHierarchyT9Algebra
import Tablet.ParameterHierarchyT9LogThreshold
import Tablet.ParameterHierarchyT9MassBound
import Tablet.ParameterHierarchyT10Algebra
import Tablet.ParameterHierarchyT10LogThreshold
import Tablet.ParameterHierarchyT11Algebra
import Tablet.ParameterHierarchyT11Threshold
import Tablet.ParameterHierarchyT12Algebra
import Tablet.ParameterHierarchyT12Threshold
import Tablet.ParameterHierarchyT16LogThreshold
import Tablet.ParameterHierarchyT17T19Threshold
import Tablet.ParameterHierarchyT21Threshold
import Tablet.ParameterHierarchyT22Algebra
import Tablet.ParameterHierarchyT22Threshold
import Tablet.ParameterHierarchyT23Algebra
import Tablet.ParameterHierarchyT23Threshold
import Tablet.ParameterHierarchyT24Algebra
import Tablet.ParameterHierarchyT24Threshold
import Tablet.ParameterHierarchyT26Algebra
import Tablet.ParameterHierarchyT26Threshold
import Tablet.ParameterHierarchyT28Algebra
import Tablet.ParameterHierarchyT28Threshold
import Tablet.ParameterHierarchyT29Algebra
import Tablet.ParameterHierarchyT29Threshold
import Tablet.RealChooseTwoQuadraticBounds

-- [TABLET NODE: ParameterHierarchyEventualComparisonsFromBounds]

theorem ParameterHierarchyEventualComparisonsFromBounds :
    ∀ η ε1 ε2 : ℝ,
      0 < η →
      0 < ε2 →
      ε2 < ε1 →
      ε1 < η →
      η < 1 →
      η < (1 / 16 : ℝ) →
      3 * ε2 ≤ ε1 / 10 →
      8 * Real.sqrt ε1 + 10 * ε1 ≤ η ^ 3 / 2 →
      ∃ n0 : ℕ,
        ε2⁻¹ ^ 2 ≤ (n0 : ℝ) ∧
        ParameterHierarchyEventualComparisons η ε1 ε2 n0 := by
-- BODY
  intro η ε1 ε2 hη_pos hε2_pos hε2_lt_ε1 hε1_lt_η hη_lt_one
    hη_lt_sixteen hthree hsqrt
  have hε1_pos : 0 < ε1 := lt_trans hε2_pos hε2_lt_ε1
  have hε2_nonneg : 0 ≤ ε2 := le_of_lt hε2_pos
  have hε2_le_one : ε2 ≤ 1 := by
    linarith [hε2_lt_ε1, hε1_lt_η, hη_lt_one]
  have hε1_le_one : ε1 ≤ 1 := by
    linarith [hε1_lt_η, hη_lt_one]
  let nBase : ℕ := Nat.ceil (ε2⁻¹ ^ 2)
  have hnBase : ε2⁻¹ ^ 2 ≤ (nBase : ℝ) := by
    dsimp [nBase]
    exact Nat.le_ceil (ε2⁻¹ ^ 2)
  have hchoose_bounds :
      ∀ x : ℝ, 0 ≤ x →
        (2 ≤ x → x ^ 2 / 4 ≤ RealChooseTwo x ∧
          RealChooseTwo x ≤ x ^ 2 / 2) ∧
          RealChooseTwo x ≤ x ^ 2 :=
    RealChooseTwoQuadraticBounds
  obtain ⟨nBaseThreshold, hBaseThreshold⟩ :=
    ParameterHierarchyBaseThreshold η hη_pos
  obtain ⟨nRatioThreshold, hRatioThreshold⟩ :=
    ParameterHierarchyInitialPowerRatioThreshold η ε1 hη_pos hε1_pos hη_lt_sixteen
  obtain ⟨nT3Threshold, hT3Threshold⟩ :=
    ParameterHierarchyT3Threshold η hη_pos
  obtain ⟨nT4ExponentThreshold, hT4ExponentThreshold⟩ :=
    ParameterHierarchyT4ExponentThreshold η hη_pos hη_lt_sixteen
  obtain ⟨nT5SqrtLogThreshold, hT5SqrtLogThreshold⟩ :=
    ParameterHierarchyT5SqrtLogThreshold ε1 hε1_pos
  obtain ⟨nT6LogThreshold, hT6LogThreshold⟩ :=
    ParameterHierarchyT6LogThreshold η hη_pos
  obtain ⟨nT7LogLogThreshold, hT7LogLogThreshold⟩ :=
    ParameterHierarchyT7LogLogThreshold η ε1 hη_pos hε1_pos
  obtain ⟨nT8Threshold, hT8Threshold⟩ :=
    ParameterHierarchyT8Threshold η hη_pos
  obtain ⟨nT9LogThreshold, hT9LogThreshold⟩ :=
    ParameterHierarchyT9LogThreshold ε1 hε1_pos
  obtain ⟨nT10LogThreshold, hT10LogThreshold⟩ :=
    ParameterHierarchyT10LogThreshold η ε1 hη_pos hε1_pos
  obtain ⟨nT11Threshold, hT11Threshold⟩ :=
    ParameterHierarchyT11Threshold η ε1 hη_pos hε1_pos hε1_le_one
  obtain ⟨nT12Threshold, hT12Threshold⟩ :=
    ParameterHierarchyT12Threshold η ε1 hη_pos hε1_pos hε1_le_one
  obtain ⟨nT16LogThreshold, hT16LogThreshold⟩ :=
    ParameterHierarchyT16LogThreshold ε2 hε2_pos
  obtain ⟨nT17T19Threshold, hT17T19Threshold⟩ :=
    ParameterHierarchyT17T19Threshold η ε2 hη_pos hε2_pos
  obtain ⟨nT21Threshold, hT21Threshold⟩ :=
    ParameterHierarchyT21Threshold η hη_pos hη_lt_sixteen
  obtain ⟨nT22Threshold, hT22Threshold⟩ :=
    ParameterHierarchyT22Threshold η hη_pos hη_lt_sixteen
  obtain ⟨nT23Threshold, hT23Threshold⟩ :=
    ParameterHierarchyT23Threshold η hη_pos
  obtain ⟨nT24Threshold, hT24Threshold⟩ :=
    ParameterHierarchyT24Threshold η hη_pos
  obtain ⟨nT26Threshold, hT26Threshold⟩ :=
    ParameterHierarchyT26Threshold η ε1 hη_pos hε1_pos
  obtain ⟨nT28Threshold, hT28Threshold⟩ :=
    ParameterHierarchyT28Threshold η ε1 hη_pos hε1_pos hη_lt_sixteen
  obtain ⟨nT29Threshold, hT29Threshold⟩ :=
    ParameterHierarchyT29Threshold η ε1 hη_pos hε1_pos
  let nPreT6 : ℕ :=
    max
      (max (max (max (max nBase nBaseThreshold) nRatioThreshold) nT3Threshold)
        nT4ExponentThreshold)
      nT5SqrtLogThreshold
  let nPreT7 : ℕ := max nPreT6 nT6LogThreshold
  let nPreT8 : ℕ := max nPreT7 nT7LogLogThreshold
  let nPreT9 : ℕ := max nPreT8 nT8Threshold
  let nPreT10 : ℕ := max nPreT9 nT9LogThreshold
  let nPreT11 : ℕ := max nPreT10 nT10LogThreshold
  let nPreT12 : ℕ := max nPreT11 nT11Threshold
  let nPreT16 : ℕ := max nPreT12 nT12Threshold
  let nPreT22 : ℕ :=
    max (max (max nPreT16 nT16LogThreshold) nT17T19Threshold) nT21Threshold
  let n0 : ℕ :=
    max
      (max
        (max (max (max (max nPreT22 nT22Threshold) nT23Threshold)
          nT24Threshold) nT26Threshold)
        nT28Threshold)
      nT29Threshold
  have hnPreT6_le_nPreT7 : nPreT6 ≤ nPreT7 := Nat.le_max_left _ _
  have hnPreT7_le_nPreT8 : nPreT7 ≤ nPreT8 := Nat.le_max_left _ _
  have hnPreT8_le_nPreT9 : nPreT8 ≤ nPreT9 := Nat.le_max_left _ _
  have hnPreT9_le_nPreT10 : nPreT9 ≤ nPreT10 := Nat.le_max_left _ _
  have hnPreT10_le_nPreT11 : nPreT10 ≤ nPreT11 := Nat.le_max_left _ _
  have hnPreT11_le_nPreT12 : nPreT11 ≤ nPreT12 := Nat.le_max_left _ _
  have hnPreT12_le_nPreT16 : nPreT12 ≤ nPreT16 := Nat.le_max_left _ _
  have hnPreT22_le_n0 : nPreT22 ≤ n0 := by
    exact le_trans
      (le_trans
        (le_trans
          (le_trans (Nat.le_max_left nPreT22 nT22Threshold)
            (Nat.le_max_left (max nPreT22 nT22Threshold) nT23Threshold))
          (Nat.le_max_left _ nT24Threshold))
        (Nat.le_max_left _ nT26Threshold))
      (le_trans (Nat.le_max_left _ nT28Threshold) (Nat.le_max_left _ nT29Threshold))
  have hnPreT16_le_n0 : nPreT16 ≤ n0 := by
    exact le_trans
      (by
        dsimp [nPreT22]
        exact le_trans
          (le_trans (Nat.le_max_left nPreT16 nT16LogThreshold)
            (Nat.le_max_left (max nPreT16 nT16LogThreshold) nT17T19Threshold))
          (Nat.le_max_left _ nT21Threshold))
      hnPreT22_le_n0
  have hnPreT12_le_n0 : nPreT12 ≤ n0 :=
    le_trans hnPreT12_le_nPreT16 hnPreT16_le_n0
  have hnPreT11_le_n0 : nPreT11 ≤ n0 :=
    le_trans hnPreT11_le_nPreT12 hnPreT12_le_n0
  have hnPreT10_le_n0 : nPreT10 ≤ n0 :=
    le_trans hnPreT10_le_nPreT11 hnPreT11_le_n0
  have hnPreT6_le_n0 : nPreT6 ≤ n0 :=
    le_trans hnPreT6_le_nPreT7
      (le_trans hnPreT7_le_nPreT8
        (le_trans hnPreT8_le_nPreT9
          (le_trans hnPreT9_le_nPreT10 hnPreT10_le_n0)))
  have hnBase_le_nPreT6 : nBase ≤ nPreT6 := by
    dsimp [nPreT6]
    exact le_trans (Nat.le_max_left nBase nBaseThreshold)
      (le_trans (Nat.le_max_left (max nBase nBaseThreshold) nRatioThreshold)
        (le_trans
          (Nat.le_max_left (max (max nBase nBaseThreshold) nRatioThreshold)
            nT3Threshold)
          (le_trans
            (Nat.le_max_left
              (max (max (max nBase nBaseThreshold) nRatioThreshold)
                nT3Threshold)
              nT4ExponentThreshold)
            (Nat.le_max_left
              (max
                (max (max (max nBase nBaseThreshold) nRatioThreshold)
                  nT3Threshold)
                nT4ExponentThreshold)
              nT5SqrtLogThreshold))))
  have hnBaseThreshold_le_nPreT6 : nBaseThreshold ≤ nPreT6 := by
    dsimp [nPreT6]
    exact le_trans (Nat.le_max_right nBase nBaseThreshold)
      (le_trans (Nat.le_max_left (max nBase nBaseThreshold) nRatioThreshold)
        (le_trans
          (Nat.le_max_left (max (max nBase nBaseThreshold) nRatioThreshold)
            nT3Threshold)
          (le_trans
            (Nat.le_max_left
              (max (max (max nBase nBaseThreshold) nRatioThreshold)
                nT3Threshold)
              nT4ExponentThreshold)
            (Nat.le_max_left
              (max
                (max (max (max nBase nBaseThreshold) nRatioThreshold)
                  nT3Threshold)
                nT4ExponentThreshold)
              nT5SqrtLogThreshold))))
  have hnRatioThreshold_le_nPreT6 : nRatioThreshold ≤ nPreT6 := by
    dsimp [nPreT6]
    exact le_trans
      (Nat.le_max_right (max nBase nBaseThreshold) nRatioThreshold)
      (le_trans
        (Nat.le_max_left (max (max nBase nBaseThreshold) nRatioThreshold)
          nT3Threshold)
        (le_trans
          (Nat.le_max_left
            (max (max (max nBase nBaseThreshold) nRatioThreshold)
              nT3Threshold)
            nT4ExponentThreshold)
          (Nat.le_max_left
            (max
              (max (max (max nBase nBaseThreshold) nRatioThreshold)
                nT3Threshold)
              nT4ExponentThreshold)
            nT5SqrtLogThreshold)))
  have hnT3Threshold_le_nPreT6 : nT3Threshold ≤ nPreT6 := by
    dsimp [nPreT6]
    exact le_trans
      (Nat.le_max_right
        (max (max nBase nBaseThreshold) nRatioThreshold) nT3Threshold)
      (le_trans
        (Nat.le_max_left
          (max (max (max nBase nBaseThreshold) nRatioThreshold)
            nT3Threshold)
          nT4ExponentThreshold)
        (Nat.le_max_left
          (max
            (max (max (max nBase nBaseThreshold) nRatioThreshold)
              nT3Threshold)
            nT4ExponentThreshold)
          nT5SqrtLogThreshold))
  have hnT4ExponentThreshold_le_nPreT6 : nT4ExponentThreshold ≤ nPreT6 := by
    dsimp [nPreT6]
    exact le_trans
      (Nat.le_max_right
        (max (max (max nBase nBaseThreshold) nRatioThreshold)
          nT3Threshold)
        nT4ExponentThreshold)
      (Nat.le_max_left
        (max
          (max (max (max nBase nBaseThreshold) nRatioThreshold)
            nT3Threshold)
          nT4ExponentThreshold)
        nT5SqrtLogThreshold)
  have hnT5SqrtLogThreshold_le_nPreT6 : nT5SqrtLogThreshold ≤ nPreT6 := by
    dsimp [nPreT6]
    exact Nat.le_max_right _ _
  have hnBaseThreshold_le_n0 : nBaseThreshold ≤ n0 :=
    le_trans hnBaseThreshold_le_nPreT6 hnPreT6_le_n0
  have hnRatioThreshold_le_n0 : nRatioThreshold ≤ n0 :=
    le_trans hnRatioThreshold_le_nPreT6 hnPreT6_le_n0
  have hnT3Threshold_le_n0 : nT3Threshold ≤ n0 :=
    le_trans hnT3Threshold_le_nPreT6 hnPreT6_le_n0
  have hnT4ExponentThreshold_le_n0 : nT4ExponentThreshold ≤ n0 :=
    le_trans hnT4ExponentThreshold_le_nPreT6 hnPreT6_le_n0
  have hnT5SqrtLogThreshold_le_n0 : nT5SqrtLogThreshold ≤ n0 :=
    le_trans hnT5SqrtLogThreshold_le_nPreT6 hnPreT6_le_n0
  have hnT6LogThreshold_le_n0 : nT6LogThreshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT6 nT6LogThreshold)
      (le_trans hnPreT7_le_nPreT8
        (le_trans hnPreT8_le_nPreT9
          (le_trans hnPreT9_le_nPreT10 hnPreT10_le_n0)))
  have hnT7LogLogThreshold_le_n0 : nT7LogLogThreshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT7 nT7LogLogThreshold)
      (le_trans hnPreT8_le_nPreT9
        (le_trans hnPreT9_le_nPreT10 hnPreT10_le_n0))
  have hnT8Threshold_le_n0 : nT8Threshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT8 nT8Threshold)
      (le_trans hnPreT9_le_nPreT10 hnPreT10_le_n0)
  have hnT9LogThreshold_le_n0 : nT9LogThreshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT9 nT9LogThreshold) hnPreT10_le_n0
  have hnT10LogThreshold_le_n0 : nT10LogThreshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT10 nT10LogThreshold) hnPreT11_le_n0
  have hnT11Threshold_le_n0 : nT11Threshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT11 nT11Threshold) hnPreT12_le_n0
  have hnT12Threshold_le_n0 : nT12Threshold ≤ n0 := by
    exact le_trans (Nat.le_max_right nPreT12 nT12Threshold) hnPreT16_le_n0
  have hnT16LogThreshold_le_n0 : nT16LogThreshold ≤ n0 := by
    exact le_trans
      (by
        dsimp [nPreT22]
        exact le_trans
          (le_trans (Nat.le_max_right nPreT16 nT16LogThreshold)
            (Nat.le_max_left (max nPreT16 nT16LogThreshold) nT17T19Threshold))
          (Nat.le_max_left _ nT21Threshold))
      hnPreT22_le_n0
  have hnT17T19Threshold_le_n0 : nT17T19Threshold ≤ n0 := by
    exact le_trans
      (by
        dsimp [nPreT22]
        exact le_trans
          (Nat.le_max_right (max nPreT16 nT16LogThreshold) nT17T19Threshold)
          (Nat.le_max_left _ nT21Threshold))
      hnPreT22_le_n0
  have hnT21Threshold_le_n0 : nT21Threshold ≤ n0 := by
    exact le_trans
      (by
        dsimp [nPreT22]
        exact Nat.le_max_right _ _)
      hnPreT22_le_n0
  have hnT22Threshold_le_n0 : nT22Threshold ≤ n0 := by
    exact le_trans
      (le_trans
        (le_trans (Nat.le_max_right nPreT22 nT22Threshold)
          (Nat.le_max_left (max nPreT22 nT22Threshold) nT23Threshold))
        (Nat.le_max_left _ nT24Threshold))
      (le_trans (le_trans (Nat.le_max_left _ nT26Threshold)
        (Nat.le_max_left _ nT28Threshold)) (Nat.le_max_left _ nT29Threshold))
  have hnT23Threshold_le_n0 : nT23Threshold ≤ n0 := by
    exact le_trans
      (le_trans (Nat.le_max_right (max nPreT22 nT22Threshold) nT23Threshold)
        (Nat.le_max_left _ nT24Threshold))
      (le_trans (le_trans (Nat.le_max_left _ nT26Threshold)
        (Nat.le_max_left _ nT28Threshold)) (Nat.le_max_left _ nT29Threshold))
  have hnT24Threshold_le_n0 : nT24Threshold ≤ n0 := by
    exact le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ nT26Threshold))
      (le_trans (Nat.le_max_left _ nT28Threshold) (Nat.le_max_left _ nT29Threshold))
  have hnT26Threshold_le_n0 : nT26Threshold ≤ n0 := by
    exact le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ nT28Threshold))
      (Nat.le_max_left _ nT29Threshold)
  have hnT28Threshold_le_n0 : nT28Threshold ≤ n0 := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ nT29Threshold)
  have hnT29Threshold_le_n0 : nT29Threshold ≤ n0 := by
    exact Nat.le_max_right _ _
  have hnBase_le_n0 : (nBase : ℝ) ≤ (n0 : ℝ) := by
    exact (Nat.cast_le).2 (le_trans hnBase_le_nPreT6 hnPreT6_le_n0)
  have hn0 : ε2⁻¹ ^ 2 ≤ (n0 : ℝ) := le_trans hnBase hnBase_le_n0
  have hBaseForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        let K := TwoBiteNaturalIndependenceScale (1 + η) n
        let k := (K : ℝ)
        let mReal := (n : ℝ) / L ^ 2
        let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
        let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
        let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
        0 < m ∧
          0 ≤ p ∧
          p ≤ (1 / 2 : ℝ) ∧
          1 ≤ 2 * p * m ∧
          kReal ≤ k ∧
          k < kReal + 1 ∧
          m ≤ mReal ∧
          mReal < m + 1 ∧
          K ≤ n ∧
          k < 2 * kReal ∧
          0 < Real.log L ∧
          2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L := by
    intro n hn
    exact hBaseThreshold n
      (lt_of_le_of_lt hnBaseThreshold_le_n0 hn)
  have hRatiosForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal ∧
          2 * L ^ 2 ≤ (ε1 / 8) * kReal := by
    intro n hn
    exact hRatioThreshold n
      (lt_of_le_of_lt hnRatioThreshold_le_n0 hn)
  have hT3ForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        1 < L ∧ 16 * L ^ 2 * Real.sqrt L ≤ kReal := by
    intro n hn
    exact hT3Threshold n
      (lt_of_le_of_lt hnT3Threshold_le_n0 hn)
  have hT4ExponentThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        let K := TwoBiteNaturalIndependenceScale (1 + η) n
        let k := (K : ℝ)
        let mReal := (n : ℝ) / L ^ 2
        (2 * k * L + L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤ kReal ^ 4 := by
    intro n hn
    exact hT4ExponentThreshold n
      (lt_of_le_of_lt hnT4ExponentThreshold_le_n0 hn)
  have hT5SqrtLogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        1 / Real.sqrt L ≤ ε1 / 2 := by
    intro n hn
    exact hT5SqrtLogThreshold n
      (lt_of_le_of_lt hnT5SqrtLogThreshold_le_n0 hn)
  have hT6LogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) /
            ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) ≤
          η ^ 3 / 2 := by
    intro n hn
    exact hT6LogThreshold n
      (lt_of_le_of_lt hnT6LogThreshold_le_n0
        hn)
  have hT7LogLogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        1 / ((1 + η) * Real.log L) ≤ ε1 := by
    intro n hn
    exact hT7LogLogThreshold n
      (lt_of_le_of_lt hnT7LogLogThreshold_le_n0
        hn)
  have hT8ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        200 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 /
            ((1 + η) * Real.sqrt ((n : ℝ) * L)) ≤ 1 := by
    intro n hn
    exact hT8Threshold n
      (lt_of_le_of_lt hnT8Threshold_le_n0 hn)
  have hT9LogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L / L ^ 2 ≤ ε1 / 10 := by
    intro n hn
    exact hT9LogThreshold n
      (lt_of_le_of_lt hnT9LogThreshold_le_n0 hn)
  have hT10LogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L / ((1 + η) * L ^ 4) ≤ ε1 := by
    intro n hn
    exact hT10LogThreshold n
      (lt_of_le_of_lt hnT10LogThreshold_le_n0 hn)
  have hT11ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 /
            (ε1 * ((1 + η) * Real.sqrt ((n : ℝ) * L))) ≤ 1 := by
    intro n hn
    exact hT11Threshold n
      (lt_of_le_of_lt hnT11Threshold_le_n0 hn)
  have hT12ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 /
            (ε1 * ((1 + η) ^ 2 * (n : ℝ))) ≤ 1 := by
    intro n hn
    exact hT12Threshold n
      (lt_of_le_of_lt hnT12Threshold_le_n0 hn)
  have hT16LogThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
        let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
        let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
        0 < (n : ℝ) →
        0 < L →
        0 < Real.log L →
        2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
        2 * p * m ≤ (ε2 / 100) * t1 := by
    intro n hn
    exact hT16LogThreshold n
      (lt_of_le_of_lt hnT16LogThreshold_le_n0 hn)
  have hT17T19ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
          200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
              Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
            400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
                Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 := by
    intro n hn
    exact hT17T19Threshold n
      (lt_of_le_of_lt hnT17T19Threshold_le_n0 hn)
  have hT21ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        Real.log L /
            (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L) < 1 := by
    intro n hn
    exact hT21Threshold n
      (lt_of_le_of_lt hnT21Threshold_le_n0 hn)
  have hT22ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L * Real.sqrt L /
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) ∧
          Real.log L / L < (1 / 2 : ℝ) := by
    intro n hn
    exact hT22Threshold n
      (lt_of_le_of_lt hnT22Threshold_le_n0 hn)
  have hT23ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 := by
    intro n hn
    exact hT23Threshold n
      (lt_of_le_of_lt hnT23Threshold_le_n0 hn)
  have hT24ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L / Real.rpow (n : ℝ) η < (1 / 2 : ℝ) := by
    intro n hn
    exact hT24Threshold n
      (lt_of_le_of_lt hnT24Threshold_le_n0 hn)
  have hT26ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 / L ≤ ε1 / 2 ∧
          1 /
              ((1 + η) * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.sqrt L) ≤
            ε1 / 2 := by
    intro n hn
    exact hT26Threshold n
      (lt_of_le_of_lt hnT26Threshold_le_n0 hn)
  have hT28ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L * L /
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) ≤ (1 / 4 : ℝ) ∧
          4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
              (1 / 4 : ℝ) ∧
            Real.exp
                (-(1 / 2 : ℝ) *
                  Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
    intro n hn
    exact hT28Threshold n
      (lt_of_le_of_lt hnT28Threshold_le_n0 hn)
  have hT29ThresholdForN :
      ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        Real.exp
            (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
              Real.sqrt L * L) ≤ ε1 := by
    intro n hn
    exact hT29Threshold n
      (lt_of_le_of_lt hnT29Threshold_le_n0 hn)
  exact ⟨n0, hn0, by
    intro n hn
    let L := Real.log (n : ℝ)
    let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
    let K := TwoBiteNaturalIndependenceScale (1 + η) n
    let k := (K : ℝ)
    let mReal := (n : ℝ) / L ^ 2
    let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
    let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
    let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
    let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η)
    let t3 := Real.rpow (n : ℝ) (2 * η)
    have hbase := hBaseForN n hn
    have hratios := hRatiosForN n hn
    have hT3data := hT3ForN n hn
    have hT1_ratio :
        Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal := by
      simpa [L, kReal] using hratios.1
    have hT2_ratio : 2 * L ^ 2 ≤ (ε1 / 8) * kReal := by
      simpa [L, kReal] using hratios.2
    have hInitialPower :
        0 < m ∧
          0 ≤ p ∧
          p ≤ (1 / 2 : ℝ) ∧
          1 ≤ 2 * p * m ∧
          kReal ≤ k ∧
          k < kReal + 1 ∧
          m ≤ mReal ∧
          mReal < m + 1 ∧
          Real.rpow (n : ℝ) (4 * η) * k ≤ (ε1 / 2) * k ^ 2 ∧
          2 * k * L ^ 2 ≤ (ε1 / 8) * k ^ 2 := by
      simpa [L, kReal, K, k, mReal, m, p, t1] using
        ParameterHierarchyInitialPowerComparisons η ε1 n hε1_pos
          (by simpa [L, kReal, K, k, mReal, m, p, t1] using hbase)
          (by simpa [L, kReal] using hT1_ratio)
          (by simpa [L, kReal] using hT2_ratio)
    have hkReal_le_k_from_base : kReal ≤ k := by
      rcases hbase with
        ⟨_, _, _, _, hkReal_le_k, _, _, _, _, _, _, _⟩
      exact hkReal_le_k
    have hk_lt_two_kReal_from_base : k < 2 * kReal := by
      rcases hbase with
        ⟨_, _, _, _, _, _, _, _, _, hk_lt_two_kReal, _, _⟩
      exact hk_lt_two_kReal
    have hlogL_pos_from_base : 0 < Real.log L := by
      rcases hbase with
        ⟨_, _, _, _, _, _, _, _, _, _, hlogL_pos, _⟩
      exact hlogL_pos
    have hD_from_base :
        2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L := by
      rcases hbase with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hD⟩
      exact hD
    have hT3Comparison :
        (1 / (2 * L)) * RealChooseTwo k + 2 * k * L ^ 2 +
            (1 / Real.sqrt L) * RealChooseTwo k ≤
          (2 / Real.sqrt L) * RealChooseTwo k := by
      simpa [L, kReal, K, k] using
        ParameterHierarchyT3ChooseComparison η n
          (by simpa [L] using hT3data.1)
          (by simpa [L, kReal, K, k] using hkReal_le_k_from_base)
          (by simpa [L, kReal] using hT3data.2)
    have hn_pos_real : 0 < (n : ℝ) := by
      have hn_ne_zero : n ≠ 0 := by
        intro hn_zero
        have hL_zero : L = 0 := by
          simp [L, hn_zero, Real.log_zero]
        linarith [hT3data.1, hL_zero]
      exact_mod_cast Nat.pos_of_ne_zero hn_ne_zero
    have hT4ChooseExp :
        (Nat.choose n K : ℝ) ≤ Real.exp (k * L) := by
      simpa [L, K, k] using ParameterHierarchyT4ChooseExpBound n K hn_pos_real
    have hm_pos_from_base : 0 < m := by
      rcases hbase with ⟨hm_pos, _, _, _, _, _, _, _, _, _, _, _⟩
      exact hm_pos
    have hp_nonneg_from_base : 0 ≤ p := by
      rcases hbase with ⟨_, hp_nonneg, _, _, _, _, _, _, _, _, _, _⟩
      exact hp_nonneg
    have hm_le_mReal_from_base : m ≤ mReal := by
      rcases hbase with ⟨_, _, _, _, _, _, hm_le_mReal, _, _, _, _, _⟩
      exact hm_le_mReal
    have hL_pos : 0 < L := by linarith [hT3data.1]
    have hL_ge_one : (1 : ℝ) ≤ L := by linarith [hT3data.1]
    have hkReal_nonneg : 0 ≤ kReal := by
      have hscale_nonneg : 0 ≤ 16 * L ^ 2 * Real.sqrt L := by positivity
      exact le_trans hscale_nonneg hT3data.2
    have hscale_k : 16 * L ^ 2 * Real.sqrt L ≤ k :=
      le_trans hT3data.2 hkReal_le_k_from_base
    have hsqrt_ge_one : 1 ≤ Real.sqrt L := by
      simpa using Real.sqrt_le_sqrt hL_ge_one
    have hL_sq_ge_one : 1 ≤ L ^ 2 := by
      have hL_nonneg : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one
      have hmul := mul_le_mul hL_ge_one hL_ge_one
        (by norm_num : (0 : ℝ) ≤ 1) hL_nonneg
      simpa [pow_two] using hmul
    have hprod_ge_one : 1 ≤ L ^ 2 * Real.sqrt L := by
      have := mul_le_mul hL_sq_ge_one hsqrt_ge_one
        (by norm_num : (0 : ℝ) ≤ 1) (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL_sq_ge_one)
      simpa using this
    have htwo_le_scale : (2 : ℝ) ≤ 16 * L ^ 2 * Real.sqrt L := by
      calc
        (2 : ℝ) ≤ 16 * 1 := by norm_num
        _ ≤ 16 * (L ^ 2 * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hprod_ge_one (by norm_num)
        _ = 16 * L ^ 2 * Real.sqrt L := by ring
    have htwo_le_k : (2 : ℝ) ≤ k := le_trans htwo_le_scale hscale_k
    have hT4ExponentThresholdData :
        (2 * k * L + L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤ kReal ^ 4 := by
      simpa only [L, kReal, K, k, mReal] using hT4ExponentThresholdForN n hn
    have hT4ExponentLower :
        2 * k * L + L ≤
          RealChooseTwo k ^ 2 /
            (L * m * Real.rpow (n : ℝ) (8 * η)) := by
      simpa only [L, kReal, K, k, mReal, m] using
        ParameterHierarchyT4ExponentAlgebra η n hn_pos_real hL_pos hm_pos_from_base
          hkReal_nonneg htwo_le_k hkReal_le_k_from_base hm_le_mReal_from_base
          hT4ExponentThresholdData
    have hkL_nonneg : 0 ≤ k * L := by
      exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 2) htwo_le_k)
        (le_of_lt hL_pos)
    have hT4Exponential :
        Real.exp
            (-(RealChooseTwo k ^ 2 /
                (L * m * Real.rpow (n : ℝ) (8 * η)))) *
          (Nat.choose n K : ℝ) ≤ (n : ℝ)⁻¹ := by
      simpa only [L, K, k, m] using
        ParameterHierarchyT4ExponentialConclusion η n hn_pos_real hkL_nonneg
          hT4ChooseExp hT4ExponentLower
    have hT5Threshold :
        1 / Real.sqrt L ≤ ε1 / 2 := by
      simpa [L] using hT5SqrtLogThresholdForN n hn
    have hk_nonneg : 0 ≤ k :=
      le_trans (by norm_num : (0 : ℝ) ≤ 2) htwo_le_k
    have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
    have hT5Choose :
        (2 / Real.sqrt L) * RealChooseTwo k ≤ (ε1 / 2) * k ^ 2 := by
      simpa only [L, K, k] using
        ParameterHierarchyT5ChooseBound ε1 η n hk_nonneg htwo_le_k hsqrt_pos
          hT5Threshold
    have hT6Threshold :
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) /
            ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) ≤
          η ^ 3 / 2 := by
      simpa [L] using hT6LogThresholdForN n hn
    have hT6Log :
        4 * Real.log k ≤ (η ^ 3 / 2) * p * k ^ 2 := by
      simpa only [L, kReal, K, k, p] using
        ParameterHierarchyT6LogAlgebra η n hη_pos hn_pos_real hL_pos
          hkReal_le_k_from_base hk_lt_two_kReal_from_base hT6Threshold
    have hT7Threshold :
        1 / ((1 + η) * Real.log L) ≤ ε1 := by
      simpa [L] using hT7LogLogThresholdForN n hn
    have hT7 :
        t1 * k ≤ ε1 * k ^ 2 := by
      simpa only [L, kReal, K, k, t1] using
        ParameterHierarchyT7Algebra η ε1 n hη_pos hε1_pos hn_pos_real hL_pos
          hlogL_pos_from_base hkReal_le_k_from_base hT7Threshold
    have hT8ThresholdData :
        200 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 /
            ((1 + η) * Real.sqrt ((n : ℝ) * L)) ≤ 1 := by
      simpa [L] using hT8ThresholdForN n hn
    have ht1_pos : 0 < t1 := by
      dsimp [t1]
      exact div_pos (Real.sqrt_pos.mpr (mul_pos hn_pos_real hL_pos))
        hlogL_pos_from_base
    have hT8 :
        RealChooseTwo (2 * k / t1 + 1) * (100 * L ^ 3) ≤ (1 / 2 : ℝ) * k := by
      simpa only [L, kReal, K, k, t1] using
        ParameterHierarchyT8Algebra η n hη_pos hn_pos_real hL_pos hlogL_pos_from_base
          hk_nonneg hkReal_le_k_from_base ht1_pos hD_from_base hT8ThresholdData
    have hT9Mass :
        2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) := by
      simpa only [L, mReal, m, p] using
        ParameterHierarchyT9MassBound n hn_pos_real hL_pos hm_le_mReal_from_base
    have hT9LogThresholdData :
        2 * Real.log L / L ^ 2 ≤ ε1 / 10 := by
      simpa [L] using hT9LogThresholdForN n hn
    have hT9 :
        (2 * k / t1) * (2 * p * m) ≤ (ε1 / 10) * k := by
      simpa only [L, K, k, m, p, t1] using
        ParameterHierarchyT9Algebra η ε1 n hε1_pos hn_pos_real hL_pos
          hlogL_pos_from_base hk_nonneg hT9Mass hT9LogThresholdData
    have hT10LogThresholdData :
        2 * Real.log L / ((1 + η) * L ^ 4) ≤ ε1 := by
      simpa [L] using hT10LogThresholdForN n hn
    have htwo_pm_nonneg : 0 ≤ 2 * p * m := by
      have hm_nonneg : 0 ≤ m := le_of_lt hm_pos_from_base
      exact mul_nonneg (mul_nonneg (by norm_num) hp_nonneg_from_base) hm_nonneg
    have hT10 :
        (2 * k / t1) * RealChooseTwo (2 * p * m) ≤ ε1 * k ^ 2 := by
      simpa only [L, kReal, K, k, m, p, t1] using
        ParameterHierarchyT10Algebra η ε1 n hη_pos hε1_pos hn_pos_real hL_pos
          hlogL_pos_from_base hk_nonneg hkReal_le_k_from_base htwo_pm_nonneg
          hT9Mass hT10LogThresholdData
    have hT11ThresholdData :
        2000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 3 /
            (ε1 * ((1 + η) * Real.sqrt ((n : ℝ) * L))) ≤ 1 := by
      simpa [L] using hT11ThresholdForN n hn
    have hT11 :
        RealChooseTwo (2 * k / t1 + 1) * (200 * L ^ 3) ≤ (ε1 / 10) * k := by
      simpa only [L, kReal, K, k, t1] using
        ParameterHierarchyT11Algebra η ε1 n hη_pos hε1_pos hn_pos_real hL_pos
          hlogL_pos_from_base hk_nonneg hkReal_le_k_from_base ht1_pos hD_from_base
          hT11ThresholdData
    have hT12ThresholdData :
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 /
            (ε1 * ((1 + η) ^ 2 * (n : ℝ))) ≤ 1 := by
      simpa [L] using hT12ThresholdForN n hn
    have hT12 :
        RealChooseTwo (2 * k / t1 + 1) * RealChooseTwo (200 * L ^ 3) ≤
          (ε1 / 10) * k ^ 2 := by
      simpa only [L, kReal, K, k, t1] using
        ParameterHierarchyT12Algebra η ε1 n hη_pos hε1_pos hn_pos_real hL_pos
          hL_ge_one hlogL_pos_from_base hk_nonneg hkReal_le_k_from_base ht1_pos
          hD_from_base hT12ThresholdData
    have hConstThreeEps : 3 * ε2 ≤ ε1 / 10 := hthree
    have hConstEpsNonneg : 0 ≤ ε2 := hε2_nonneg
    have hConstEpsLeOne : ε2 ≤ 1 := hε2_le_one
    have hT16 : 2 * p * m ≤ (ε2 / 100) * t1 := by
      simpa only [L, m, p, t1] using
        hT16LogThresholdForN n hn hn_pos_real hL_pos hlogL_pos_from_base hT9Mass
    have hT17T19ThresholdData :
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
              Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
          200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
                Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
            400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
                  Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 := by
      simpa [L] using hT17T19ThresholdForN n hn
    have hsqrt_nL_pos : 0 < Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_pos.mpr (mul_pos hn_pos_real hL_pos)
    have hT17Scaled :
        (5 * (1 + η) * Real.log L) * (100 * L ^ 3) ≤ (ε2 / 100) * t1 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hT17T19ThresholdData.1 (le_of_lt ht1_pos)
      calc
        (5 * (1 + η) * Real.log L) * (100 * L ^ 3) =
            (100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
                Real.sqrt ((n : ℝ) * L)) * t1 := by
          dsimp [t1]
          field_simp [ne_of_gt hsqrt_nL_pos, ne_of_gt hlogL_pos_from_base]
        _ ≤ (ε2 / 100) * t1 := hmul
    have hT17 :
        (2 * k / t1 + 1) * (100 * L ^ 3) ≤ (ε2 / 100) * t1 := by
      have hD_scaled :
          (2 * k / t1 + 1) * (100 * L ^ 3) ≤
            (5 * (1 + η) * Real.log L) * (100 * L ^ 3) :=
        mul_le_mul_of_nonneg_right hD_from_base (by positivity)
      exact le_trans hD_scaled hT17Scaled
    have hT18Scaled :
        (5 * (1 + η) * Real.log L) * (200 * L ^ 3) ≤ (ε2 / 100) * t1 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hT17T19ThresholdData.2.1 (le_of_lt ht1_pos)
      calc
        (5 * (1 + η) * Real.log L) * (200 * L ^ 3) =
            (200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
                Real.sqrt ((n : ℝ) * L)) * t1 := by
          dsimp [t1]
          field_simp [ne_of_gt hsqrt_nL_pos, ne_of_gt hlogL_pos_from_base]
        _ ≤ (ε2 / 100) * t1 := hmul
    have hT18 :
        (2 * k / t1 + 1) * (200 * L ^ 3) ≤ (ε2 / 100) * t1 := by
      have hD_scaled :
          (2 * k / t1 + 1) * (200 * L ^ 3) ≤
            (5 * (1 + η) * Real.log L) * (200 * L ^ 3) :=
        mul_le_mul_of_nonneg_right hD_from_base (by positivity)
      exact le_trans hD_scaled hT18Scaled
    have hT19Scaled :
        (5 * (1 + η) * Real.log L) * (400 * L ^ 5) ≤ (ε2 / 100) * t1 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hT17T19ThresholdData.2.2 (le_of_lt ht1_pos)
      calc
        (5 * (1 + η) * Real.log L) * (400 * L ^ 5) =
            (400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
                Real.sqrt ((n : ℝ) * L)) * t1 := by
          dsimp [t1]
          field_simp [ne_of_gt hsqrt_nL_pos, ne_of_gt hlogL_pos_from_base]
        _ ≤ (ε2 / 100) * t1 := hmul
    have hT19 :
        (2 * k / t1 + 1) * (400 * L ^ 5) ≤ (ε2 / 100) * t1 := by
      have hD_scaled :
          (2 * k / t1 + 1) * (400 * L ^ 5) ≤
            (5 * (1 + η) * Real.log L) * (400 * L ^ 5) :=
        mul_le_mul_of_nonneg_right hD_from_base (by positivity)
      exact le_trans hD_scaled hT19Scaled
    have hT20 :
        t2 * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) ≤ ε1 * k := by
      have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
      have hsqrtL_nonneg : 0 ≤ Real.sqrt L := le_of_lt hsqrtL_pos
      have hT5_mul :=
        mul_le_mul_of_nonneg_right hT5Threshold hsqrtL_nonneg
      have hone_le_half : (1 : ℝ) ≤ (ε1 / 2) * Real.sqrt L := by
        calc
          (1 : ℝ) = (1 / Real.sqrt L) * Real.sqrt L := by
            field_simp [ne_of_gt hsqrtL_pos]
          _ ≤ (ε1 / 2) * Real.sqrt L := hT5_mul
      have hhalf_le_full :
          (ε1 / 2) * Real.sqrt L ≤ ε1 * (1 + η) * Real.sqrt L := by
        have hhalf_le_one_eta : (1 / 2 : ℝ) ≤ 1 + η := by
          linarith
        have hcoeff : ε1 / 2 ≤ ε1 * (1 + η) := by
          calc
            ε1 / 2 = ε1 * (1 / 2 : ℝ) := by ring
            _ ≤ ε1 * (1 + η) :=
              mul_le_mul_of_nonneg_left hhalf_le_one_eta hε1_pos.le
        exact mul_le_mul_of_nonneg_right hcoeff hsqrtL_nonneg
      have hone_le_full : (1 : ℝ) ≤ ε1 * (1 + η) * Real.sqrt L :=
        le_trans hone_le_half hhalf_le_full
      have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hsqrtn_le_eps_kReal :
          Real.sqrt (n : ℝ) ≤ ε1 * kReal := by
        calc
          Real.sqrt (n : ℝ) = (1 : ℝ) * Real.sqrt (n : ℝ) := by ring
          _ ≤ (ε1 * (1 + η) * Real.sqrt L) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_right hone_le_full hsqrtn_nonneg
          _ = ε1 * kReal := by
            dsimp [kReal]
            rw [Real.sqrt_mul (Nat.cast_nonneg n)]
            ring
      have hsqrtn_le_eps_k : Real.sqrt (n : ℝ) ≤ ε1 * k :=
        le_trans hsqrtn_le_eps_kReal
          (mul_le_mul_of_nonneg_left hkReal_le_k_from_base hε1_pos.le)
      have hrpow_product :
          t2 * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
            Real.sqrt (n : ℝ) := by
        dsimp [t2]
        calc
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
              Real.rpow (n : ℝ)
                (((1 / 4 : ℝ) + η) + ((1 / 4 : ℝ) - η)) := by
            simpa using
              (Real.rpow_add hn_pos_real ((1 / 4 : ℝ) + η)
                ((1 / 4 : ℝ) - η)).symm
          _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
            congr 1
            ring
          _ = Real.sqrt (n : ℝ) := by
            exact (Real.sqrt_eq_rpow (n : ℝ)).symm
      calc
        t2 * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
            Real.sqrt (n : ℝ) := hrpow_product
        _ ≤ ε1 * k := hsqrtn_le_eps_k
    have hT21ThresholdData :
        Real.log L /
            (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L) < 1 := by
      simpa [L] using hT21ThresholdForN n hn
    have hT21 :
        TwoBiteLargeCutoff η n < TwoBiteHugeCutoff n := by
      have hpower_small_pos :
          0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) :=
        Real.rpow_pos_of_pos hn_pos_real _
      have hpower_large_pos :
          0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) :=
        Real.rpow_pos_of_pos hn_pos_real _
      have hsqrtL_pos_local : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
      have hden_pos :
          0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L :=
        mul_pos hpower_small_pos hsqrtL_pos_local
      have hlogL_lt :
          Real.log L <
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L := by
        rw [div_lt_iff₀ hden_pos] at hT21ThresholdData
        simpa [one_mul] using hT21ThresholdData
      have hrpow_product :
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
            Real.sqrt (n : ℝ) := by
        calc
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
              Real.rpow (n : ℝ)
                (((1 / 4 : ℝ) + η) + ((1 / 4 : ℝ) - η)) := by
            simpa using
              (Real.rpow_add hn_pos_real ((1 / 4 : ℝ) + η)
                ((1 / 4 : ℝ) - η)).symm
          _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
            congr 1
            ring
          _ = Real.sqrt (n : ℝ) := by
            exact (Real.sqrt_eq_rpow (n : ℝ)).symm
      have hmul_lt :
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) * Real.log L <
            Real.sqrt (n : ℝ) * Real.sqrt L := by
        have hmul :=
          mul_lt_mul_of_pos_left hlogL_lt hpower_large_pos
        calc
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) * Real.log L <
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) *
                (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L) := hmul
          _ = Real.sqrt (n : ℝ) * Real.sqrt L := by
            rw [← mul_assoc, hrpow_product]
      have hlarge_lt_core :
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) <
            (Real.sqrt (n : ℝ) * Real.sqrt L) / Real.log L := by
        rw [lt_div_iff₀ hlogL_pos_from_base]
        exact hmul_lt
      calc
        TwoBiteLargeCutoff η n =
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) := by
          rfl
        _ < (Real.sqrt (n : ℝ) * Real.sqrt L) / Real.log L := hlarge_lt_core
        _ = TwoBiteHugeCutoff n := by
          dsimp [TwoBiteHugeCutoff, L]
          rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    have hT22ThresholdData :
        2 * Real.log L * Real.sqrt L /
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) ∧
          Real.log L / L < (1 / 2 : ℝ) := by
      simpa [L] using hT22ThresholdForN n hn
    have hT22 :
        (1 + ε2) * L ^ 2 * (t2 / L) +
            L * (1 + ε2) * p * m <
          TwoBiteHugeCutoff n := by
      simpa only [L, m, p, t2] using
        ParameterHierarchyT22Algebra η ε2 n hε2_nonneg hε2_le_one
          hn_pos_real hL_pos hlogL_pos_from_base hp_nonneg_from_base
          (le_of_lt hm_pos_from_base)
          (by simpa only [L, m, p] using hT9Mass)
          (by simpa only [L] using hT22ThresholdData.1)
          (by simpa only [L] using hT22ThresholdData.2)
    have hT23ThresholdData :
        200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 := by
      simpa [L] using hT23ThresholdForN n hn
    have hT23 :
        100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) * L ^ 3 ≤
          TwoBiteLargeCutoff η n := by
      simpa only [L] using
        ParameterHierarchyT23Algebra η n hn_pos_real (le_of_lt hL_pos)
          (by simpa only [L] using hT23ThresholdData)
    have hT24LossThresholdData :
        100 * L ^ 3 / Real.rpow (n : ℝ) η ≤ (1 / 2 : ℝ) := by
      calc
        100 * L ^ 3 / Real.rpow (n : ℝ) η =
            (1 / 2 : ℝ) * (200 * L ^ 3 / Real.rpow (n : ℝ) η) := by ring
        _ ≤ (1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hT23ThresholdData (by norm_num)
        _ = (1 / 2 : ℝ) := by ring
    have hT24SqrtThresholdData :
        2 * (1 + η) * Real.sqrt L / Real.rpow (n : ℝ) η < (1 / 2 : ℝ) := by
      simpa [L] using hT24ThresholdForN n hn
    have hchooseQuarter_le_sq :
        RealChooseTwo (Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
          Real.rpow (n : ℝ) (1 / 4 : ℝ) ^ 2 := by
      exact (hchoose_bounds (Real.rpow (n : ℝ) (1 / 4 : ℝ))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)).2
    have hT24KUpper :
        k < 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := by
      calc
        k < 2 * kReal := hk_lt_two_kReal_from_base
        _ = 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := by
          dsimp [kReal]
          ring
    have hT24 :
        k < Real.rpow (n : ℝ) (1 / 4 : ℝ) * t2 -
          RealChooseTwo (Real.rpow (n : ℝ) (1 / 4 : ℝ)) * (100 * L ^ 3) := by
      simpa only [L, t2] using
        ParameterHierarchyT24Algebra η k n hn_pos_real (le_of_lt hL_pos)
          (by simpa only [L] using hT24KUpper)
          hchooseQuarter_le_sq
          (by simpa only [L] using hT24LossThresholdData)
          (by simpa only [L] using hT24SqrtThresholdData)
    rcases hInitialPower with
      ⟨hm_pos_initial, hp_nonneg_initial, hp_le_half_initial,
        hpm_ge_one_initial, hkReal_le_k_initial, hk_lt_kReal_add_initial,
        hm_le_mReal_initial, hmReal_lt_m_add_initial, hT1, hT2⟩
    have hT25 :
        t3 ^ 2 * k ≤ (ε1 / 2) * k ^ 2 := by
      have ht3_sq : t3 ^ 2 = Real.rpow (n : ℝ) (4 * η) := by
        dsimp [t3]
        calc
          (Real.rpow (n : ℝ) (2 * η)) ^ 2 =
              Real.rpow (n : ℝ) (2 * η) *
                Real.rpow (n : ℝ) (2 * η) := by ring
          _ = Real.rpow (n : ℝ) ((2 * η) + (2 * η)) := by
            exact (Real.rpow_add hn_pos_real (2 * η) (2 * η)).symm
          _ = Real.rpow (n : ℝ) (4 * η) := by
            congr 1
            ring
      rw [ht3_sq]
      exact hT1
    have hT26ThresholdData :
        2 / L ≤ ε1 / 2 ∧
          1 /
              ((1 + η) * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.sqrt L) ≤
            ε1 / 2 := by
      simpa [L] using hT26ThresholdForN n hn
    have hT26 :
        k * (2 * k / L + Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
          ε1 * k ^ 2 := by
      simpa only [L, kReal] using
        ParameterHierarchyT26Algebra η ε1 k n hη_pos hε1_pos hn_pos_real hL_pos
          hk_nonneg hkReal_le_k_from_base
          (by simpa only [L] using hT26ThresholdData.1)
          (by simpa only [L] using hT26ThresholdData.2)
    have hp_k_sq_nonneg : 0 ≤ p * k ^ 2 :=
      mul_nonneg hp_nonneg_from_base (sq_nonneg k)
    have hT27Coefficient :
        8 * Real.sqrt ε1 * p * k ^ 2 + 10 * ε1 * p * k ^ 2 ≤
          (η ^ 3 / 2) * p * k ^ 2 := by
      have hscaled :
          (8 * Real.sqrt ε1 + 10 * ε1) * (p * k ^ 2) ≤
            (η ^ 3 / 2) * (p * k ^ 2) :=
        mul_le_mul_of_nonneg_right hsqrt hp_k_sq_nonneg
      calc
        8 * Real.sqrt ε1 * p * k ^ 2 + 10 * ε1 * p * k ^ 2 =
            (8 * Real.sqrt ε1 + 10 * ε1) * (p * k ^ 2) := by ring
        _ ≤ (η ^ 3 / 2) * (p * k ^ 2) := hscaled
        _ = (η ^ 3 / 2) * p * k ^ 2 := by ring
    have hT27 :
        8 * Real.sqrt ε1 * p * k ^ 2 + 10 * ε1 * p * k ^ 2 +
            4 * Real.log k ≤ η ^ 3 * p * k ^ 2 := by
      calc
        8 * Real.sqrt ε1 * p * k ^ 2 + 10 * ε1 * p * k ^ 2 +
              4 * Real.log k ≤
            (η ^ 3 / 2) * p * k ^ 2 + (η ^ 3 / 2) * p * k ^ 2 :=
          add_le_add hT27Coefficient hT6Log
        _ = η ^ 3 * p * k ^ 2 := by ring
    have hT28ThresholdData :
        2 * (1 + η) * Real.sqrt L * L /
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) ≤ (1 / 4 : ℝ) ∧
          4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
              (1 / 4 : ℝ) ∧
            Real.exp
                (-(1 / 2 : ℝ) *
                  Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
      simpa [L] using hT28ThresholdForN n hn
    have hT28KUpper :
        k < 2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L := by
      calc
        k < 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := hT24KUpper
        _ = 2 * (1 + η) * Real.sqrt (n : ℝ) * Real.sqrt L := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n)]
          ring
    have hT28 :
        Real.exp
          (k * L +
            2 * k * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * η) * L -
            Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
      simpa only [L] using
        ParameterHierarchyT28Algebra η ε1 k n hn_pos_real (le_of_lt hL_pos)
          (by simpa only [L] using hT28KUpper)
          (by simpa only [L] using hT28ThresholdData.1)
          (by simpa only [L] using hT28ThresholdData.2.1)
          (by simpa only [L] using hT28ThresholdData.2.2)
    have hT29ThresholdData :
        Real.exp
            (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
              Real.sqrt L * L) ≤ ε1 := by
      simpa [L] using hT29ThresholdForN n hn
    have hT29 :
        Real.exp (-(η / 4) * k * L) ≤ ε1 := by
      simpa only [L, kReal] using
        ParameterHierarchyT29Algebra η ε1 k n hη_pos hn_pos_real hL_pos
          hkReal_le_k_from_base
          (by simpa only [L] using hT29ThresholdData)
    exact ⟨hm_pos_initial, hp_nonneg_initial, hp_le_half_initial,
      hpm_ge_one_initial, hkReal_le_k_initial, hk_lt_kReal_add_initial,
      hm_le_mReal_initial, hmReal_lt_m_add_initial, hT1, hT2, hT3Comparison,
      hT4Exponential, hT5Choose, hT6Log, hT7, hT8, hT9, hT10,
      (by
        simpa only [L, K, k, t1, Real.sqrt_mul (Nat.cast_nonneg n),
          show (2 : ℝ) * 100 = 200 by norm_num] using hT11),
      (by
        simpa only [L, K, k, t1, Real.sqrt_mul (Nat.cast_nonneg n),
          show (2 : ℝ) * 100 = 200 by norm_num] using hT12),
      hConstThreeEps, hConstEpsNonneg, hConstEpsLeOne, hT16, hT17,
      (by
        simpa only [L, K, k, t1, Real.sqrt_mul (Nat.cast_nonneg n),
          show (2 : ℝ) * 100 = 200 by norm_num] using hT18), hT19,
      hT20, hT21, hT22, hT23, hT24, hT25, hT26, hT27, hT28,
      hT29⟩⟩
