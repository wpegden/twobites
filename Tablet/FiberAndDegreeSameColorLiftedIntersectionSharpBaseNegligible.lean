import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalReducedVertexRatioEventually
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
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
import Tablet.FiberAndDegreeSameColorLiftedIntersectionUniformBound
import Tablet.FiberAndDegreeMixedLiftedIntersectionConditioning

open Classical
open Filter Topology

-- [TABLET NODE: FiberAndDegreeSameColorLiftedIntersectionSharpBaseNegligible]

theorem FiberAndDegreeSameColorLiftedIntersectionSharpBaseNegligible :
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
                  ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ)))) := by
-- BODY
  intro β hβ m hm
  classical
  unfold NegligibleProbability
  have h_asymp :
      Filter.Tendsto
        (fun n : ℕ =>
          (2 : ℝ) *
            ((m n : ℝ)^2 * Real.exp (-2 * (Real.log (n : ℝ))^3)))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa using
      (OppositeProjectionAsymptoticBound 2 (by norm_num) m hm).const_mul (2 : ℝ)
  have h_log_eventual :
      ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) h_asymp ?_ ?_
  · filter_upwards [OppositeProjectionEdgeProbBounds] with n hp_bounds
    have hp_bounds' :
        0 ≤ TwoBiteEdgeProbability β n ∧ TwoBiteEdgeProbability β n ≤ 1 := by
      rwa [← hβ] at hp_bounds
    exact TwoBiteEventProbabilityNonnegative hp_bounds'.1 hp_bounds'.2 _
  · filter_upwards [TwoBiteNaturalTotalMassOneEventually β hβ m hm,
      TwoBiteNaturalReducedVertexRatioEventually m hm, h_log_eventual,
      OppositeProjectionEdgeProbBounds]
      with n h_mass h_ratio h_log hp_bounds
    let p_n := TwoBiteEdgeProbability β n
    let M := m n
    let Bad : TwoBiteSample n M p_n → Prop :=
      fun ω =>
        (∃ r s : Fin M, r ≠ s ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3) ∨
        (∃ b c : Fin M, b ≠ c ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3)
    let Sharp : TwoBiteSample n M p_n → Prop :=
      fun ω =>
        (∀ r s : Fin M, r ≠ s →
          ((Finset.univ.filter
            (fun t => (TwoBiteRedGraph ω).Adj r t ∧
              (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
        (∀ b c : Fin M, b ≠ c →
          ((Finset.univ.filter
            (fun t => (TwoBiteBlueGraph ω).Adj b t ∧
              (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))
    let E_n : TwoBiteSample n M p_n → Prop := fun ω => Bad ω ∧ Sharp ω
    let C_n : ℝ :=
      (2 : ℝ) * (M : ℝ)^2 * Real.exp (-2 * (Real.log (n : ℝ))^3)
    have hp_bounds' : 0 ≤ p_n ∧ p_n ≤ 1 := by
      simpa [p_n, hβ] using hp_bounds
    have hC_nonneg : 0 ≤ C_n := by
      dsimp [C_n]
      positivity
    have hweight : ∀ ω : TwoBiteSample n M p_n, 0 ≤ TwoBiteSampleWeight ω := by
      intro ω
      exact TwoBiteSampleWeightNonnegative ω hp_bounds'.1 hp_bounds'.2
    have h_cond_bound : ∀ G_R G_B : SimpleGraph (Fin M),
        TwoBiteConditionalProbability n M p_n E_n
          (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) ≤ C_n := by
      intro G_R G_B
      unfold TwoBiteConditionalProbability
      by_cases h_den :
          TwoBiteEventProbability n M p_n
            (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) = 0
      · rw [if_pos h_den]
        exact hC_nonneg
      · rw [if_neg h_den]
        by_cases hsharpGB :
            (∀ r s : Fin M, r ≠ s →
              ((Finset.univ.filter
                (fun t => G_R.Adj r t ∧ G_R.Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
            (∀ b c : Fin M, b ≠ c →
              ((Finset.univ.filter
                (fun t => G_B.Adj b t ∧ G_B.Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))
        · have h_prob_pos :
              0 < TwoBiteEventProbability n M p_n
                (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) := by
            have h_nonneg :
                0 ≤ TwoBiteEventProbability n M p_n
                  (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) := by
              unfold TwoBiteEventProbability
              apply Finset.sum_nonneg
              intro ω _
              exact hweight ω
            exact lt_of_le_of_ne h_nonneg (Ne.symm h_den)
          have h_num_le :
              TwoBiteEventProbability n M p_n
                (fun ω => E_n ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) ≤
              TwoBiteEventProbability n M p_n
                (fun ω => Bad ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) := by
            unfold TwoBiteEventProbability
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro ω hω
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
                exact ⟨hω.1.1, hω.2⟩)
              (by
                intro ω _ _
                exact hweight ω)
          have hunif :=
            FiberAndDegreeSameColorLiftedIntersectionUniformBound
              n M p_n (hm n) (by simp [p_n, hβ]) h_mass.1 h_log h_ratio
              G_R G_B hsharpGB
          unfold TwoBiteConditionalProbability at hunif
          rw [if_neg h_den] at hunif
          exact le_trans
            (div_le_div_of_nonneg_right h_num_le h_prob_pos.le) hunif
        · have h_num :
              TwoBiteEventProbability n M p_n
                (fun ω => E_n ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) = 0 := by
            unfold TwoBiteEventProbability
            apply Finset.sum_eq_zero
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            rcases hω with ⟨⟨_, hsharpω⟩, ⟨hRω, hBω⟩⟩
            exfalso
            apply hsharpGB
            constructor
            · intro r s hrs
              simpa [Sharp, TwoBiteRedGraph, hRω] using hsharpω.1 r s hrs
            · intro b c hbc
              simpa [Sharp, TwoBiteBlueGraph, hBω] using hsharpω.2 b c hbc
          rw [h_num, zero_div]
          exact hC_nonneg
    have h_final :=
      FiberAndDegreeMixedLiftedIntersectionConditioning
        n M p_n E_n C_n hC_nonneg hweight h_cond_bound
    show
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
            ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧
              (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
          (∀ b c : Fin (m n), b ≠ c →
            ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧
              (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ)))
        ≤ (2 : ℝ) *
          ((m n : ℝ)^2 * Real.exp (-2 * (Real.log (n : ℝ))^3))
    simpa [p_n, M, Bad, Sharp, E_n, C_n, mul_assoc] using h_final
