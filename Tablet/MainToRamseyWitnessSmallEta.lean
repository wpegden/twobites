import Tablet.RamseyWitness
import Tablet.RamseyScale
import Tablet.IndependenceNumberLess
import Tablet.SmallEtaRamseyArithmeticWindow

-- [TABLET NODE: MainToRamseyWitnessSmallEta]

theorem MainToRamseyWitnessSmallEta
    (hmain :
      ∀ ε : ℝ, 0 < ε →
        ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
          ∃ G : SimpleGraph (Fin n),
            G.CliqueFree 3 ∧
              IndependenceNumberLess G
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) :
    ∀ η : ℝ, 0 < η → η < (1 / 2 : ℝ) →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ N : ℕ, RamseyWitness N k ∧
          ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) := by
-- BODY
  intro η hη hηsmall
  obtain ⟨ε, hεpos, hwindow⟩ := SmallEtaRamseyArithmeticWindow η hη hηsmall
  obtain ⟨n0, hn0⟩ := hmain ε hεpos
  obtain ⟨k0, hk0⟩ := hwindow n0
  refine ⟨k0, ?_⟩
  intro k hk
  obtain ⟨N, hNlarge, hscale, hthreshold⟩ := hk0 k hk
  obtain ⟨G, hclique, hind⟩ := hn0 N hNlarge
  refine ⟨N, ?_, hscale⟩
  unfold RamseyWitness
  refine ⟨G, hclique, ?_⟩
  intro I hIcard hIindep
  unfold IndependenceNumberLess at hind
  have hIlt := hind I hIindep
  have hklt :
      (k : ℝ) < (1 + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
    simpa [hIcard] using hIlt
  exact (lt_irrefl (k : ℝ)) (lt_trans hklt hthreshold)
