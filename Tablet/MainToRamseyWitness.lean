import Tablet.MainIndependence
import Tablet.RamseyWitness
import Tablet.RamseyScale
import Tablet.IndependenceNumberLess
import Tablet.MainToRamseyWitnessLargeEta
import Tablet.MainToRamseyWitnessSmallEta

-- [TABLET NODE: MainToRamseyWitness]

theorem MainToRamseyWitness
    (hmain :
      ∀ ε : ℝ, 0 < ε →
        ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
          ∃ G : SimpleGraph (Fin n),
            G.CliqueFree 3 ∧
              IndependenceNumberLess G
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) :
    ∀ η : ℝ, 0 < η →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ N : ℕ, RamseyWitness N k ∧
          ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) := by
-- BODY
  intro η hη
  by_cases hLarge : (1 / 2 : ℝ) ≤ η
  · exact MainToRamseyWitnessLargeEta η hη hLarge
  · exact MainToRamseyWitnessSmallEta hmain η hη (lt_of_not_ge hLarge)
