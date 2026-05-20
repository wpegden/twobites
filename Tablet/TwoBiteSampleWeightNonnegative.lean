import Tablet.TwoBiteSampleWeight

-- [TABLET NODE: TwoBiteSampleWeightNonnegative]

theorem TwoBiteSampleWeightNonnegative :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p),
      0 ≤ p →
      p ≤ 1 →
      0 ≤ TwoBiteSampleWeight ω := by
-- BODY
  intro n m p ω hp0 hp1
  have hG1 : 0 ≤ GnpGraphWeight p ω.1 := by
    classical
    unfold GnpGraphWeight
    exact Finset.prod_nonneg (by
      intro e he
      by_cases hAdj : SimpleGraph.Adj ω.1 e.1 e.2
      · simp [hAdj, hp0]
      · have h : 0 ≤ 1 - p := sub_nonneg.mpr hp1
        simp [hAdj, h])
  have hG2 : 0 ≤ GnpGraphWeight p ω.2.1 := by
    classical
    unfold GnpGraphWeight
    exact Finset.prod_nonneg (by
      intro e he
      by_cases hAdj : SimpleGraph.Adj ω.2.1 e.1 e.2
      · simp [hAdj, hp0]
      · have h : 0 ≤ 1 - p := sub_nonneg.mpr hp1
        simp [hAdj, h])
  have hU : 0 ≤ UniformInjectionWeight n m := by
    unfold UniformInjectionWeight
    split_ifs <;> positivity
  unfold TwoBiteSampleWeight
  positivity
