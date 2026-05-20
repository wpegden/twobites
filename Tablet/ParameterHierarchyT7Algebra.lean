import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT7Algebra]

theorem ParameterHierarchyT7Algebra :
    ∀ η ε1 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
      0 < η →
      0 < ε1 →
      0 < (n : ℝ) →
      0 < L →
      0 < Real.log L →
      kReal ≤ k →
      1 / ((1 + η) * Real.log L) ≤ ε1 →
      t1 * k ≤ ε1 * k ^ 2 := by
-- BODY
  intro η ε1 n
  dsimp
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  intro hη hε1 hn_pos hL_pos hlogL_pos hkReal_le_k hthreshold
  have hκ_pos : 0 < 1 + η := by linarith
  have hkReal_pos : 0 < kReal := by
    dsimp [kReal]
    positivity
  have hk_pos : 0 < k := lt_of_lt_of_le hkReal_pos hkReal_le_k
  have hk_nonneg : 0 ≤ k := le_of_lt hk_pos
  have ht1_eq : t1 = kReal * (1 / ((1 + η) * Real.log L)) := by
    dsimp [t1, kReal]
    field_simp [hκ_pos.ne', hlogL_pos.ne']
  have ht1_le : t1 ≤ ε1 * kReal := by
    calc
      t1 = kReal * (1 / ((1 + η) * Real.log L)) := ht1_eq
      _ ≤ kReal * ε1 :=
        mul_le_mul_of_nonneg_left hthreshold (le_of_lt hkReal_pos)
      _ = ε1 * kReal := by ring
  have hkReal_mul_le : kReal * k ≤ k * k :=
    mul_le_mul_of_nonneg_right hkReal_le_k hk_nonneg
  calc
    t1 * k ≤ (ε1 * kReal) * k :=
      mul_le_mul_of_nonneg_right ht1_le hk_nonneg
    _ = ε1 * (kReal * k) := by ring
    _ ≤ ε1 * (k * k) :=
      mul_le_mul_of_nonneg_left hkReal_mul_le (le_of_lt hε1)
    _ = ε1 * k ^ 2 := by ring
