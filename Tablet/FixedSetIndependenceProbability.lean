import Tablet.FixedSetConditionalIndependenceBound
import Tablet.FixedSetProjectionCellSummationBound
import Tablet.FixedSetProjectionCellReduction
import Tablet.ProjectionSizeProbabilityBound
import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteRegularityEvent
import Tablet.ParameterHierarchy
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: FixedSetIndependenceProbability]

theorem FixedSetIndependenceProbability :
    ∀ δ : ℝ, 0 < δ →
      ∀ {ε ε1 ε2 : ℝ} {n0 : ℕ},
        ParameterHierarchy ε ε1 ε2 n0 →
        ∃ N : ℕ,
          n0 ≤ N ∧
            ∀ {n m : ℕ} {p : ℝ} (I : Finset (Fin n)),
              N < n →
              m = TwoBiteNaturalReducedVertexCount n →
              p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
              I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
              TwoBiteEventProbability n m p
                  (fun ω =>
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                      TwoBiteRegularityEvent (k := I.card) ε ε1 ε2 ω)
                ≤ δ * ((Nat.choose n I.card : ℝ)⁻¹) := by
-- BODY
  intro δ hδ ε ε1 ε2 n0 hHierarchy
  obtain ⟨η, hη, Nsum, hNsum_ge, hSum⟩ :=
    FixedSetProjectionCellSummationBound (ε := ε) (ε1 := ε1) (ε2 := ε2)
      (n0 := n0) δ hδ hHierarchy
  have hεpos : 0 < ε :=
    lt_trans (lt_trans hHierarchy.1 hHierarchy.2.1) hHierarchy.2.2.1
  obtain ⟨Nproj, hProj⟩ := ProjectionSizeProbabilityBound η ε hη hεpos
  refine ⟨max Nsum Nproj, ?_, ?_⟩
  · exact le_trans hNsum_ge (Nat.le_max_left Nsum Nproj)
  · intro n m p I hn hm hp hI
    have hNsum_lt : Nsum < n := lt_of_le_of_lt (Nat.le_max_left Nsum Nproj) hn
    have hNproj_le : Nproj ≤ n :=
      le_of_lt (lt_of_le_of_lt (Nat.le_max_right Nsum Nproj) hn)
    have hn0_lt : n0 < n := lt_of_le_of_lt hNsum_ge hNsum_lt
    have hCell :
        ∀ ℓR ℓB : ℕ,
          ℓR * ℓB ≥ I.card →
          TwoBiteEventProbability n m p
              (fun ω =>
                TwoBiteProjectionSizeEvent
                  (k := I.card) (ℓR := ℓR) (ℓB := ℓB) ω I)
            ≤
            Real.exp
              ((η - (2 - (ℓR : ℝ) / (I.card : ℝ) -
                  (ℓB : ℝ) / (I.card : ℝ)) / 2) *
                (I.card : ℝ) * Real.log (n : ℝ)) := by
      intro ℓR ℓB hNonempty
      exact hProj (n := n) (m := m) (k := I.card)
        (ℓR := ℓR) (ℓB := ℓB) (p := p)
        I hNproj_le hm rfl hI hNonempty
    have hSumI :
        (Finset.range (I.card + 1)).sum (fun ℓR =>
          (Finset.range (I.card + 1)).sum (fun ℓB =>
            if ℓR * ℓB < I.card then
              0
            else
              Real.exp
                ((η - (2 - (ℓR : ℝ) / (I.card : ℝ) -
                    (ℓB : ℝ) / (I.card : ℝ)) / 2) *
                  (I.card : ℝ) * Real.log (n : ℝ)) *
                min (1 : ℝ)
                  (Real.exp
                    (-(p *
                      (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                        (I.card : ℝ) p (n : ℝ) -
                        ε ^ 3 * (I.card : ℝ) ^ 2)))))) ≤
          δ * ((Nat.choose n I.card : ℝ)⁻¹) := by
      simpa [hI, hp] using hSum n hNsum_lt
    exact FixedSetProjectionCellReduction (n := n) (m := m) (k := I.card)
      (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2) (η := η) (δ := δ)
      (n0 := n0) I hHierarchy hn0_lt hm hp rfl hI hCell hSumI
