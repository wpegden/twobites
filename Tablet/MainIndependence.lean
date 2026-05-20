import Tablet.TwoBitePositiveExistence
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteDeletionTriangleFree
import Tablet.IndependenceNumberLess
import Tablet.NoDistinctTriangleCliqueFree

-- [TABLET NODE: MainIndependence]

theorem MainIndependence :
    ∀ ε : ℝ, 0 < ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ G : SimpleGraph (Fin n),
          G.CliqueFree 3 ∧
            IndependenceNumberLess G
              ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
-- BODY
  intro ε hε
  obtain ⟨n0, hn0⟩ := TwoBitePositiveExistence ε hε
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨_, _, ω, _, _, _, hNoTriangle, hIndependent⟩ := hn0 n hn
  refine ⟨(TwoBiteFinalGraph ω).2.2, ?_, hIndependent⟩
  exact NoDistinctTriangleCliqueFree (TwoBiteFinalGraph ω).2.2 hNoTriangle
