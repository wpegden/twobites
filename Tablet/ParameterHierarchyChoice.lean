import Tablet.ParameterHierarchyConstantBounds
import Tablet.ParameterHierarchyEventualThreshold
import Tablet.ParameterHierarchy
import Tablet.NaturalParameterApproximation
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff

-- [TABLET NODE: ParameterHierarchyChoice]

theorem ParameterHierarchyChoice :
    ∀ ε : ℝ, 0 < ε →
      ∃ ε' ε1 ε2 : ℝ, ∃ n0 : ℕ,
        0 < ε' ∧ ε' < ε ∧ ε' ≤ ε ∧
          ParameterHierarchy ε' ε1 ε2 n0 := by
-- BODY
  intro ε hε
  let eps := min (ε / 2) (1 / 32 : ℝ)
  let eps1 := (1 / 2 : ℝ) *
    min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40))
  let eps2 := (1 / 2 : ℝ) * min eps1 (min (eps1 / 30) (1 : ℝ))
  have hconst :
      0 < eps ∧ eps < ε ∧ eps ≤ ε ∧
        0 < eps2 ∧ eps2 < eps1 ∧ eps1 < eps ∧ eps < 1 ∧
          eps < (1 / 16 : ℝ) ∧
        3 * eps2 ≤ eps1 / 10 ∧
        8 * Real.sqrt eps1 + 10 * eps1 ≤ eps ^ 3 / 2 := by
    simpa [eps, eps1, eps2] using ParameterHierarchyConstantBounds ε hε
  obtain ⟨n0, hn0, hcomparisons⟩ :
      ∃ n0 : ℕ,
        eps2⁻¹ ^ 2 ≤ (n0 : ℝ) ∧
        ParameterHierarchyEventualComparisons eps eps1 eps2 n0 := by
    simpa [eps, eps1, eps2] using ParameterHierarchyEventualThreshold ε hε
  rcases hconst with
    ⟨heps_pos, heps_lt, heps_le, heps2_pos, heps2_lt, heps1_lt,
      heps_lt_one, heps_lt_sixteen, hthree, hsqrt⟩
  refine ⟨eps, eps1, eps2, n0, heps_pos, heps_lt, heps_le, ?_⟩
  unfold ParameterHierarchy
  exact ⟨heps2_pos, heps2_lt, heps1_lt, heps_lt_one, heps_lt_sixteen,
    hthree, hsqrt, hn0, hcomparisons⟩
