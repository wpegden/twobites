import Tablet.Preamble

-- [TABLET NODE: OppositeProjectionFallingFactorialBound]

open scoped BigOperators Classical

theorem OppositeProjectionFallingFactorialBound (S m h : ℕ) (hSm : S ≤ m) (hhS : h ≤ S) :
    (∏ l ∈ Finset.range h, ((S - l : ℝ) / (m - l : ℝ))) ≤ ((S : ℝ) / (m : ℝ)) ^ h := by
-- BODY
  have H_elem : ∀ (l : ℝ), 0 ≤ l → l < m → (S - l) / (m - l) ≤ S / m := by
    intro l hl0 hlm
    have hm : 0 < (m : ℝ) := by linarith
    have hml : 0 < (m : ℝ) - l := by linarith
    rw [div_le_div_iff₀ hml hm]
    have H : (S - l) * m = S * m - l * m := by ring
    have H2 : S * (m - l) = S * m - S * l := by ring
    rw [H, H2]
    have H3 : l * S ≤ l * m := by
      apply mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hSm) hl0
    linarith
  have H : ∀ l ∈ Finset.range h, 0 ≤ (S - l : ℝ) / (m - l : ℝ) ∧ (S - l : ℝ) / (m - l : ℝ) ≤ (S : ℝ) / (m : ℝ) := by
    intro l hl
    rw [Finset.mem_range] at hl
    have hlS : (l : ℝ) ≤ S := by exact Nat.cast_le.mpr (le_trans (le_of_lt hl) hhS)
    have hlm : (l : ℝ) < m := by exact Nat.cast_lt.mpr (lt_of_lt_of_le (lt_of_lt_of_le hl hhS) hSm)
    have hz : 0 ≤ S - (l : ℝ) := by linarith
    have hmd : 0 < m - (l : ℝ) := by linarith
    have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    constructor
    · exact div_nonneg hz (le_of_lt hmd)
    · exact H_elem l hl0 hlm
  have h_le := Finset.prod_le_prod (fun i hi => (H i hi).1) (fun i hi => (H i hi).2)
  rw [Finset.prod_const, Finset.card_range] at h_le
  exact h_le
