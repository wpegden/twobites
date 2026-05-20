import Tablet.RamseyWitness
import Tablet.RamseyScale

-- [TABLET NODE: MainToRamseyWitnessLargeEta]

theorem MainToRamseyWitnessLargeEta :
    ∀ η : ℝ, 0 < η → (1 / 2 : ℝ) ≤ η →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ N : ℕ, RamseyWitness N k ∧
          ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) := by
-- BODY
  intro η hη hLarge
  refine ⟨2, ?_⟩
  intro k hk
  refine ⟨0, ?_, ?_⟩
  · unfold RamseyWitness
    classical
    refine ⟨⊥, ?_, ?_⟩
    · exact SimpleGraph.cliqueFree_of_card_lt (by simp)
    · intro I hIcard hIndep
      have hIempty : I = ∅ := by
        ext x
        exact Fin.elim0 x
      have hcard : I.card = 0 := by
        simp [hIempty]
      have hkpos : 0 < k := by
        omega
      omega
  · have hcoef : ((1 : ℝ) / 2 - η) ≤ 0 := by
      linarith
    have hk_gt_one_real : (1 : ℝ) < (k : ℝ) := by
      norm_num
      exact_mod_cast hk
    have hlog_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos hk_gt_one_real
    have hscale_nonneg : 0 ≤ RamseyScale k := by
      unfold RamseyScale
      exact div_nonneg (by positivity) hlog_pos.le
    have hprod : ((1 : ℝ) / 2 - η) * RamseyScale k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hscale_nonneg
    simpa using hprod
