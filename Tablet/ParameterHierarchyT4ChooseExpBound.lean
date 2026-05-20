import Mathlib.Data.Nat.Choose.Bounds
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT4ChooseExpBound]

theorem ParameterHierarchyT4ChooseExpBound :
    ∀ n K : ℕ, 0 < (n : ℝ) →
      (Nat.choose n K : ℝ) ≤ Real.exp ((K : ℝ) * Real.log (n : ℝ)) := by
-- BODY
  intro n K hn_pos
  have hchoose_nat : Nat.choose n K ≤ n ^ K := Nat.choose_le_pow n K
  calc
    (Nat.choose n K : ℝ) ≤ ((n ^ K : ℕ) : ℝ) := by
      exact_mod_cast hchoose_nat
    _ = (n : ℝ) ^ K := by
      norm_num
    _ = (n : ℝ) ^ (K : ℝ) := by
      rw [Real.rpow_natCast]
    _ = Real.exp (Real.log (n : ℝ) * (K : ℝ)) := by
      rw [Real.rpow_def_of_pos hn_pos]
    _ = Real.exp ((K : ℝ) * Real.log (n : ℝ)) := by ring_nf
