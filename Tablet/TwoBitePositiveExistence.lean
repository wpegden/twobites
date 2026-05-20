import Tablet.NoLargeIndependentSetWhp
import Tablet.TwoBiteFinalGraph
import Tablet.IndependenceNumberLess
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.NaturalIndependenceScaleFitsTarget
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyChoice
import Tablet.TwoBiteDeletionTriangleFree
import Tablet.TwoBiteParameterRelations
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteSampleWeight
import Tablet.WithHighProbability
import Tablet.TwoBiteEventProbabilityPositiveWitness

-- [TABLET NODE: TwoBitePositiveExistence]

theorem TwoBitePositiveExistence :
    ∀ ε : ℝ, 0 < ε →
        ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ m : ℕ, ∃ p : ℝ, ∃ ω : TwoBiteSample n m p,
          m = TwoBiteNaturalReducedVertexCount n ∧
          p = TwoBiteEdgeProbability (1 / 2 : ℝ) n ∧
          0 < TwoBiteSampleWeight ω ∧
            (¬ ∃ u v w : Fin n,
              u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
                (TwoBiteFinalGraph ω).2.2.Adj u v ∧
                  (TwoBiteFinalGraph ω).2.2.Adj u w ∧
                    (TwoBiteFinalGraph ω).2.2.Adj v w) ∧
            IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
              ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
-- BODY
  intro ε hε
  obtain ⟨η, ε1, ε2, nh, hη_pos, hη_lt, hη_le, hHierarchy⟩ :=
    ParameterHierarchyChoice ε hε
  let β : ℝ := (1 / 2 : ℝ)
  have hWhp :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))))) := by
    exact NoLargeIndependentSetWhp ε η ε1 ε2 β hε hη_pos hη_lt rfl hHierarchy
  unfold WithHighProbability at hWhp
  have hPositiveEventually :
      ∀ᶠ n in Filter.atTop,
        0 <
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) := by
    exact (tendsto_order.mp hWhp).1 (0 : ℝ) zero_lt_one
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hPositiveEventually
  refine ⟨n0, ?_⟩
  intro n hn
  have hProbPos :
      0 <
        TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
          (TwoBiteEdgeProbability β n)
          (fun ω =>
            IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
              ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) :=
    hn0 n hn
  obtain ⟨ω, hIndep, hWeightPos⟩ :=
    TwoBiteEventProbabilityPositiveWitness hProbPos
  refine ⟨TwoBiteNaturalReducedVertexCount n, TwoBiteEdgeProbability (1 / 2 : ℝ) n,
    ω, rfl, ?_, ?_⟩
  · rfl
  · refine ⟨?_, ?_⟩
    · simpa [β] using hWeightPos
    · refine ⟨?_, ?_⟩
      · simpa using (TwoBiteDeletionTriangleFree ω).2.2.2.2
      · simpa [β] using hIndep
