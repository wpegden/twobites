import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyLogPositivity]

lemma ParameterHierarchyLogPositivity {n : ℕ} {ε ε1 ε2 : ℝ} {n0 : ℕ}
    (h_hier : ParameterHierarchyEventualComparisons ε ε1 ε2 n0)
    (hn : n0 < n) :
    0 < Real.log (n : ℝ) := by
-- BODY
  have h1 := h_hier n hn
  rcases h1 with ⟨hm_pos, _, _, h_pm, _⟩
  -- hm_pos: 0 < m
  -- h_pm: 1 ≤ 2 * p * m
  have h2 : 0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
    by_contra h3
    push Not at h3
    have h4 : Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) = 0 := le_antisymm h3 (Real.sqrt_nonneg _)
    rw [h4] at h_pm
    norm_num at h_pm
  have h3 : 0 < Real.log (n : ℝ) / (n : ℝ) := by
    apply Real.sqrt_pos.mp h2
  have hn_pos : (0 : ℝ) < n := by
    by_contra h4
    push Not at h4
    have h5 : (n : ℝ) = 0 := le_antisymm h4 (Nat.cast_nonneg _)
    rw [h5] at h3
    have h6 : Real.log (0 : ℝ) / 0 = 0 := by simp
    rw [h6] at h3
    exact lt_irrefl _ h3
  exact (div_pos_iff_of_pos_right hn_pos).mp h3
