import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.UniformInjectionWeight
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
import Tablet.FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible
import Tablet.FiberAndDegreeSameColorLiftedIntersectionSharpBaseNegligible

open Classical

-- [TABLET NODE: FiberAndDegreeSameColorLiftedIntersectionNegligible]

theorem FiberAndDegreeSameColorLiftedIntersectionNegligible :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                ( (∃ r s : Fin (m n), r ≠ s ∧
                    ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
                      > 100 * (Real.log (n : ℝ)) ^ 3) ∨
                  (∃ b c : Fin (m n), b ≠ c ∧
                    ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
                      > 100 * (Real.log (n : ℝ)) ^ 3) ) ∧
                (∀ r s : Fin (m n), r ≠ s →
                  ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)))) := by
-- BODY
  intro β hβ m hm
  classical
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Bad : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      ( (∃ r s : Fin (m n), r ≠ s ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3) ∨
        (∃ b c : Fin (m n), b ≠ c ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3) )
  let Sharp : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))
  let Weak : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ 100 * Real.log (n : ℝ))
  have hSharp :
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => Bad n ω ∧ Sharp n ω)) := by
    simpa [p, Bad, Sharp] using
      FiberAndDegreeSameColorLiftedIntersectionSharpBaseNegligible β hβ m hm
  have hFail :
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => ¬ Sharp n ω)) := by
    simpa [p, Sharp] using
      FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible β hβ m hm
  unfold NegligibleProbability at hSharp hFail ⊢
  have hUpperTendsto :
      Filter.Tendsto
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (fun ω => Bad n ω ∧ Sharp n ω) +
          TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Sharp n ω))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hsum := hSharp.add hFail
    simpa using hsum
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hp_bounds ω
    have hp_bounds' :
        0 ≤ TwoBiteEdgeProbability β n ∧ TwoBiteEdgeProbability β n ≤ 1 := by
      rwa [← hβ] at hp_bounds
    exact TwoBiteSampleWeightNonnegative ω hp_bounds'.1 hp_bounds'.2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hUpperTendsto ?_ ?_
  · filter_upwards [hweight] with n hnw
    unfold TwoBiteEventProbability
    apply Finset.sum_nonneg
    intro ω _
    exact hnw ω
  · filter_upwards [hweight] with n hnw
    let Ω := TwoBiteSample n (m n) (p n)
    let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
    have hpoint : ∀ ω : Ω,
        (if Bad n ω ∧ Weak n ω then w ω else 0) ≤
          (if Bad n ω ∧ Sharp n ω then w ω else 0) +
            (if ¬ Sharp n ω then w ω else 0) := by
      intro ω
      by_cases hBad : Bad n ω <;>
        by_cases hSharpω : Sharp n ω <;>
        by_cases hWeak : Weak n ω <;>
        simp [hBad, hSharpω, hWeak, w, hnw ω]
    calc
      TwoBiteEventProbability n (m n) (p n) (fun ω => Bad n ω ∧ Weak n ω)
          = ∑ ω : Ω, (if Bad n ω ∧ Weak n ω then w ω else 0) := by
            unfold TwoBiteEventProbability
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro ω _
            simp [Ω, w]
      _ ≤ ∑ ω : Ω,
            ((if Bad n ω ∧ Sharp n ω then w ω else 0) +
              (if ¬ Sharp n ω then w ω else 0)) := by
            apply Finset.sum_le_sum
            intro ω _
            exact hpoint ω
      _ =
          (∑ ω : Ω, (if Bad n ω ∧ Sharp n ω then w ω else 0)) +
            ∑ ω : Ω, (if ¬ Sharp n ω then w ω else 0) := by
            rw [Finset.sum_add_distrib]
      _ =
          TwoBiteEventProbability n (m n) (p n) (fun ω => Bad n ω ∧ Sharp n ω) +
            TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Sharp n ω) := by
            unfold TwoBiteEventProbability
            rw [Finset.sum_filter, Finset.sum_filter]
            congr 1
            · apply Finset.sum_congr rfl
              intro ω _
              simp [Ω, w]
            · apply Finset.sum_congr rfl
              intro ω _
              simp [Ω, w]
