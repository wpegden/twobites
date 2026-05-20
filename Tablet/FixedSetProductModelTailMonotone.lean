import Tablet.FixedSetProductModelMass

-- [TABLET NODE: FixedSetProductModelTailMonotone]

open scoped BigOperators

theorem FixedSetProductModelTailMonotone {m_sub : ℕ} (p_sub : ℝ) (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1) (P_R P_B : Finset (Fin m_sub))
    (S T : Finset (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub))) (h_sub : S ⊆ T) :
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    S.sum (fun v => Finset.univ.prod (fun i => q (v i))) ≤ T.sum (fun v => Finset.univ.prod (fun i => q (v i))) := by
-- BODY
  intro q
  apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
  intro v _ _
  apply Finset.prod_nonneg
  intro i _
  exact (FixedSetProductModelMass p_sub hp0 hp1 P_R P_B).1 (v i)
