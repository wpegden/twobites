import Tablet.WithHighProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.GraphDegreeCount
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.WithinRelativeError
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.TwoBiteRedMarginal
import Tablet.TwoBiteBlueMarginal
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.GnpGraphWeightNaturalDegreeConcentration

open Filter

-- [TABLET NODE: FiberAndDegreeBaseDegreeConcentration]

theorem FiberAndDegreeBaseDegreeConcentration :
    ∀ ε2 β : ℝ, 0 < ε2 → β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              (∀ r : Fin (m n),
                WithinRelativeError ε2
                  (TwoBiteEdgeProbability β n * (m n : ℝ))
                  (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
              (∀ b : Fin (m n),
                WithinRelativeError ε2
                  (TwoBiteEdgeProbability β n * (m n : ℝ))
                  (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)))) := by
-- BODY
  intro ε2 β hε2 hβ m hm
  classical
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  have hsupport : ∀ᶠ n in Filter.atTop, n ≤ m n * m n := by
    filter_upwards [TwoBiteNaturalTotalMassOneEventually β hβ m hm] with n hn
    exact hn.1
  have hpBounds : ∀ᶠ n in Filter.atTop, 0 ≤ p n ∧ p n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hn
    simpa [p, hβ] using hn
  have hRedDegreeFailureMarginal :
      ∀ᶠ n in Filter.atTop,
        TwoBiteEventProbability n (m n) (p n)
          (fun ω =>
            ¬ ∀ r : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) =
        ∑ G : SimpleGraph (Fin (m n)),
          if ¬ ∀ r : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount G r : ℝ)
          then GnpGraphWeight (p n) G else 0 := by
    filter_upwards [hsupport] with n hn
    let E : SimpleGraph (Fin (m n)) → Prop :=
      fun G =>
        ¬ ∀ r : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount G r : ℝ)
    simpa [E, p] using
      (TwoBiteRedMarginal n (m n) (p n) hn E)
  have hBlueDegreeFailureMarginal :
      ∀ᶠ n in Filter.atTop,
        TwoBiteEventProbability n (m n) (p n)
          (fun ω =>
            ¬ ∀ b : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)) =
        ∑ G : SimpleGraph (Fin (m n)),
          if ¬ ∀ b : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount G b : ℝ)
          then GnpGraphWeight (p n) G else 0 := by
    filter_upwards [hsupport] with n hn
    let E : SimpleGraph (Fin (m n)) → Prop :=
      fun G =>
        ¬ ∀ b : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount G b : ℝ)
    simpa [E, p] using
      (TwoBiteBlueMarginal n (m n) (p n) hn E)
  have hDegreeFailureUnionBound :
      ∀ᶠ n in Filter.atTop,
        TwoBiteEventProbability n (m n) (p n)
          (fun ω =>
            ¬ ((∀ r : Fin (m n),
                  WithinRelativeError ε2 (p n * (m n : ℝ))
                    (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
                (∀ b : Fin (m n),
                  WithinRelativeError ε2 (p n * (m n : ℝ))
                    (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)))) ≤
        TwoBiteEventProbability n (m n) (p n)
          (fun ω =>
            ¬ ∀ r : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) +
        TwoBiteEventProbability n (m n) (p n)
          (fun ω =>
            ¬ ∀ b : Fin (m n),
              WithinRelativeError ε2 (p n * (m n : ℝ))
                (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)) := by
    filter_upwards [hpBounds] with n hp
    unfold TwoBiteEventProbability
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro ω hω
    have hweight_nonneg : 0 ≤ TwoBiteSampleWeight ω :=
      TwoBiteSampleWeightNonnegative ω hp.1 hp.2
    by_cases hRed :
        ∀ r : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)
    · by_cases hBlue :
        ∀ b : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)
      · simp [hRed, hBlue]
      · simp [hRed, hBlue]
    · by_cases hBlue :
        ∀ b : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)
      · simp [hRed, hBlue]
      · have hle :
            TwoBiteSampleWeight ω ≤
              TwoBiteSampleWeight ω + TwoBiteSampleWeight ω := by
          linarith
        simpa [hRed, hBlue] using hle
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      (∀ r : Fin (m n),
        WithinRelativeError ε2 (p n * (m n : ℝ))
          (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
      (∀ b : Fin (m n),
        WithinRelativeError ε2 (p n * (m n : ℝ))
          (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ))
  let badProb : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Good n ω)
  let degreeFailureSum : ℕ → ℝ := fun n =>
    ∑ G : SimpleGraph (Fin (m n)),
      if ¬ ∀ v : Fin (m n),
          WithinRelativeError ε2 (p n * (m n : ℝ))
            (GraphDegreeCount G v : ℝ)
      then GnpGraphWeight (p n) G else 0
  have hDegreeSumNegligible :
      NegligibleProbability degreeFailureSum := by
    simpa [degreeFailureSum, p] using
      (GnpGraphWeightNaturalDegreeConcentration ε2 β hε2 hβ m hm)
  have hDegreeSumTendsto :
      Filter.Tendsto degreeFailureSum Filter.atTop (nhds (0 : ℝ)) := by
    simpa [NegligibleProbability] using hDegreeSumNegligible
  have hUpperTendsto :
      Filter.Tendsto (fun n => degreeFailureSum n + degreeFailureSum n)
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hDegreeSumTendsto.add hDegreeSumTendsto
  have hBadLower :
      ∀ᶠ n in Filter.atTop, (fun _ : ℕ => (0 : ℝ)) n ≤ badProb n := by
    filter_upwards [hpBounds] with n hp
    dsimp [badProb]
    unfold TwoBiteEventProbability
    apply Finset.sum_nonneg
    intro ω hω
    exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  have hBadUpper :
      ∀ᶠ n in Filter.atTop,
        badProb n ≤ degreeFailureSum n + degreeFailureSum n := by
    filter_upwards [hDegreeFailureUnionBound, hRedDegreeFailureMarginal,
      hBlueDegreeFailureMarginal] with n hUnion hRed hBlue
    dsimp [badProb, degreeFailureSum, Good] at hUnion hRed hBlue ⊢
    rw [hRed, hBlue] at hUnion
    exact hUnion
  have hBadTendsto :
      Filter.Tendsto badProb Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpperTendsto hBadLower hBadUpper
  have hTrue :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (fun _ => True)) := by
    unfold WithHighProbability
    have htotal := TwoBiteNaturalTotalMassOneEventually β hβ m hm
    have hEq :
        (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop]
          (fun n =>
            TwoBiteEventProbability n (m n) (p n) (fun _ => True)) := by
      filter_upwards [htotal] with n hn
      simpa [p] using hn.2.symm
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hBad :
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ True)) := by
    unfold NegligibleProbability
    simpa [badProb] using hBadTendsto
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [hpBounds] with n hp ω
    exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  have hGood :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    WithHighProbabilityOfNegligibleBadOnRegular
      m p Good (fun _ _ => True) hTrue hBad hweight
  simpa [Good, p] using hGood
