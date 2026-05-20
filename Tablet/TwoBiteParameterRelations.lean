import Tablet.TwoBiteStretch
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteIndependenceScale

-- [TABLET NODE: TwoBiteParameterRelations]

theorem TwoBiteParameterRelations :
    ∀ ε β κ : ℝ, 0 < ε → β = (1 : ℝ) / 2 → κ = 1 + ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        0 < TwoBiteStretch n ∧
          0 < TwoBiteEdgeProbability β n ∧
          TwoBiteIndependenceScale κ n =
            κ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
-- BODY
  intro ε β κ hε hβ hκ
  refine ⟨2, ?_⟩
  intro n hn
  have hn_gt_one_nat : 1 < n := Nat.lt_of_succ_le hn
  have hn_gt_one_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_gt_one_nat
  have hn_pos_real : 0 < (n : ℝ) := lt_trans zero_lt_one hn_gt_one_real
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one_real
  have hstretch_pos : 0 < TwoBiteStretch n := by
    unfold TwoBiteStretch
    exact pow_pos hlog_pos 2
  have hbeta_pos : 0 < β := by
    rw [hβ]
    norm_num
  have hquot_pos : 0 < Real.log (n : ℝ) / (n : ℝ) :=
    div_pos hlog_pos hn_pos_real
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) :=
    Real.sqrt_pos.mpr hquot_pos
  have hedge_pos : 0 < TwoBiteEdgeProbability β n := by
    unfold TwoBiteEdgeProbability
    exact mul_pos hbeta_pos hsqrt_pos
  exact ⟨hstretch_pos, hedge_pos, rfl⟩
