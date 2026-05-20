import Tablet.MainIndependence
import Tablet.MainToRamseyWitness
import Tablet.RamseyScaleConversion
import Tablet.RamseyWitness
import Tablet.RamseyScale

-- [TABLET NODE: MainRamseyLowerBound]

theorem MainRamseyLowerBound :
    ∀ η : ℝ, 0 < η →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ N : ℕ, RamseyWitness N k ∧
          ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) := by
-- BODY
  exact MainToRamseyWitness MainIndependence
