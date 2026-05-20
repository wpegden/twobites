import Tablet.ParameterHierarchyBaseThreshold

-- [TABLET NODE: ParameterHierarchyInitialPowerComparisons]

theorem ParameterHierarchyInitialPowerComparisons :
    ∀ η ε1 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let mReal := (n : ℝ) / L ^ 2
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < ε1 →
      (0 < m ∧
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
        2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L) →
      Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal →
      2 * L ^ 2 ≤ (ε1 / 8) * kReal →
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
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let mReal := (n : ℝ) / L ^ 2
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hε1 hbase hT1_ratio hT2_ratio
  rcases hbase with
    ⟨hm_pos, hp_nonneg, hp_le_half, hpm, hkReal_le_k, hk_lt_kReal_add,
      hm_le_mReal, hmReal_lt_m_add, hK_le_n, hk_lt_two_kReal, hlogL_pos, hD⟩
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact Nat.cast_nonneg K
  have hkReal_le_k' : kReal ≤ k := by
    simpa [kReal, k, K, L] using hkReal_le_k
  have hε1_half_nonneg : 0 ≤ ε1 / 2 := by positivity
  have hε1_eighth_nonneg : 0 ≤ ε1 / 8 := by positivity
  have hT1_mul :
      Real.rpow (n : ℝ) (4 * η) * k ≤ ((ε1 / 2) * kReal) * k :=
    mul_le_mul_of_nonneg_right hT1_ratio hk_nonneg
  have hT1 :
      Real.rpow (n : ℝ) (4 * η) * k ≤ (ε1 / 2) * k ^ 2 := by
    calc
      Real.rpow (n : ℝ) (4 * η) * k ≤ ((ε1 / 2) * kReal) * k := hT1_mul
      _ ≤ ((ε1 / 2) * k) * k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkReal_le_k' hε1_half_nonneg) hk_nonneg
      _ = (ε1 / 2) * k ^ 2 := by ring
  have hT2_mul : (2 * L ^ 2) * k ≤ ((ε1 / 8) * kReal) * k :=
    mul_le_mul_of_nonneg_right hT2_ratio hk_nonneg
  have hT2 : 2 * k * L ^ 2 ≤ (ε1 / 8) * k ^ 2 := by
    calc
      2 * k * L ^ 2 = (2 * L ^ 2) * k := by ring
      _ ≤ ((ε1 / 8) * kReal) * k := hT2_mul
      _ ≤ ((ε1 / 8) * k) * k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkReal_le_k' hε1_eighth_nonneg) hk_nonneg
      _ = (ε1 / 8) * k ^ 2 := by ring
  exact ⟨hm_pos, hp_nonneg, hp_le_half, hpm, hkReal_le_k, hk_lt_kReal_add,
    hm_le_mReal, hmReal_lt_m_add, hT1, hT2⟩
