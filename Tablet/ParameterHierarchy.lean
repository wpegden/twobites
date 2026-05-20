import Tablet.ParameterHierarchyEventualComparisons

-- [TABLET NODE: ParameterHierarchy]

def ParameterHierarchy (ε ε1 ε2 : ℝ) (n0 : ℕ) : Prop :=
-- BODY
  0 < ε2 ∧ ε2 < ε1 ∧ ε1 < ε ∧ ε < 1 ∧
    ε < (1 / 16 : ℝ) ∧
    3 * ε2 ≤ ε1 / 10 ∧
    8 * Real.sqrt ε1 + 10 * ε1 ≤ ε ^ 3 / 2 ∧
    ε2⁻¹ ^ 2 ≤ (n0 : ℝ) ∧
    ParameterHierarchyEventualComparisons ε ε1 ε2 n0
