import Tablet.FixedSetHugeOppositeWitnessTouched
import Tablet.TwoBiteClassSmallMediumLargeOrHuge

-- [TABLET NODE: FixedSetStagedOpenOppositeWitnessLMS]

theorem FixedSetStagedOpenOppositeWitnessLMS :
    ∀ {n m : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n)),
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      (∀ q : Fin m × Fin m,
        Sum.inl q ∈ TwoBiteStagedOpenPairs ω ε I →
        (∃ b : Fin m,
          q ∈
            TwoBiteBasePairs
              ((TwoBiteX ω I (Sum.inr b)).image
                (TwoBiteRedProjection ω))) →
        ∃ b : Fin m,
          (TwoBiteLargeClass ω ε I (Sum.inr b) ∨
            TwoBiteMediumClass ω ε I (Sum.inr b) ∨
              TwoBiteSmallClass ω ε I (Sum.inr b)) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ω I (Sum.inr b)).image
                  (TwoBiteRedProjection ω))) ∧
      (∀ q : Fin m × Fin m,
        Sum.inr q ∈ TwoBiteStagedOpenPairs ω ε I →
        (∃ r : Fin m,
          q ∈
            TwoBiteBasePairs
              ((TwoBiteX ω I (Sum.inl r)).image
                (TwoBiteBlueProjection ω))) →
        ∃ r : Fin m,
          (TwoBiteLargeClass ω ε I (Sum.inl r) ∨
            TwoBiteMediumClass ω ε I (Sum.inl r) ∨
              TwoBiteSmallClass ω ε I (Sum.inl r)) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ω I (Sum.inl r)).image
                  (TwoBiteBlueProjection ω))) := by
-- BODY
  classical
  intro n m p ε ε1 ε2 n0 ω I hComparisons hn hm hp hI hFiber
  have hHuge :=
    FixedSetHugeOppositeWitnessTouched (n := n) (m := m) (p := p)
      (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0)
      ω I hComparisons hn hm hp hI hFiber
  constructor
  · intro q hOpen hWitness
    rcases hWitness with ⟨b, hq⟩
    have hClass :=
      TwoBiteClassSmallMediumLargeOrHuge (n := n) (m := m)
        (p := p) (ε := ε) ω I (Sum.inr b)
    rcases hClass with hSmall | hMedium | hLarge | hHugeClass
    · exact ⟨b, Or.inr (Or.inr hSmall), hq⟩
    · exact ⟨b, Or.inr (Or.inl hMedium), hq⟩
    · exact ⟨b, Or.inl hLarge, hq⟩
    · exfalso
      exact (hHuge.1 q ⟨b, hHugeClass, hq⟩).2 hOpen
  · intro q hOpen hWitness
    rcases hWitness with ⟨r, hq⟩
    have hClass :=
      TwoBiteClassSmallMediumLargeOrHuge (n := n) (m := m)
        (p := p) (ε := ε) ω I (Sum.inl r)
    rcases hClass with hSmall | hMedium | hLarge | hHugeClass
    · exact ⟨r, Or.inr (Or.inr hSmall), hq⟩
    · exact ⟨r, Or.inr (Or.inl hMedium), hq⟩
    · exact ⟨r, Or.inl hLarge, hq⟩
    · exfalso
      exact (hHuge.2 q ⟨r, hHugeClass, hq⟩).2 hOpen
