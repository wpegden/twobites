import Tablet.FixedSetIndependenceProbability
import Tablet.FiberAndDegreeConcentration
import Tablet.MediumClosedPairsBound
import Tablet.SmallClosedPairsBound
import Tablet.WithHighProbability
import Tablet.IndependenceNumberLess
import Tablet.ParameterHierarchy
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.NaturalParameterApproximation
import Tablet.NaturalIndependenceScaleFitsTarget
import Tablet.NoLargeIndependentSetRegularityWhp
import Tablet.NoLargeIndependentSetFromFixedSetBound

-- [TABLET NODE: NoLargeIndependentSetWhp]

theorem NoLargeIndependentSetWhp :
    ∀ (ε η ε1 ε2 β : ℝ) {n0 : ℕ},
      0 < ε →
      0 < η →
      η < ε →
      β = (1 / 2 : ℝ) →
      ParameterHierarchy η ε1 ε2 n0 →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))))) := by
-- BODY
  intro ε η ε1 ε2 β n0 hε hη hη_lt hβ hHierarchy
  have hRegular :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              TwoBiteRegularityEvent
                (k := TwoBiteNaturalIndependenceScale (1 + η) n)
                η ε1 ε2 ω)) := by
    exact NoLargeIndependentSetRegularityWhp η ε1 ε2 β hβ hHierarchy
  have hFixed :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ,
          n0 ≤ N ∧
            ∀ {n m : ℕ} {p : ℝ} (I : Finset (Fin n)),
              N < n →
              m = TwoBiteNaturalReducedVertexCount n →
              p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
              I.card = TwoBiteNaturalIndependenceScale (1 + η) n →
              TwoBiteEventProbability n m p
                  (fun ω =>
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                      TwoBiteRegularityEvent (k := I.card) η ε1 ε2 ω)
                ≤ δ * ((Nat.choose n I.card : ℝ)⁻¹) := by
    intro δ hδ
    exact FixedSetIndependenceProbability δ hδ hHierarchy
  exact NoLargeIndependentSetFromFixedSetBound ε η ε1 ε2 β hε hη hη_lt
    hβ hHierarchy hRegular hFixed
