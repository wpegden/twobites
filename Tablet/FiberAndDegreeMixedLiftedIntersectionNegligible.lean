import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSample
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.GraphDegreeCount
import Tablet.FiberAndDegreeMixedLiftedIntersectionConditioning
import Tablet.FiberAndDegreeMixedLiftedIntersectionHypergeometricBound
import Tablet.FiberAndDegreeMixedLiftedIntersectionUniformBound
import Tablet.FiberAndDegreeMixedLiftedIntersectionUnionBound
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.OppositeProjectionEdgeProbBounds

open Filter Topology

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionNegligible]

theorem FiberAndDegreeMixedLiftedIntersectionNegligible :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                (∃ r b : Fin (m n), ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > 100 * (Real.log (n : ℝ)) ^ 3) ∧
                ((∀ r : Fin (m n), (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (m n : ℝ)) ∧
                 (∀ b : Fin (m n), (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (m n : ℝ))))) := by
-- BODY
  intro β hβ m hm
  unfold NegligibleProbability
  
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := 0)) (OppositeProjectionAsymptoticBound 2 (by norm_num) m hm)
  · filter_upwards [OppositeProjectionEdgeProbBounds] with n hp_bounds
    have hp_bounds' : 0 ≤ TwoBiteEdgeProbability β n ∧ TwoBiteEdgeProbability β n ≤ 1 := by rwa [← hβ] at hp_bounds
    apply Finset.sum_nonneg
    intro ω _
    apply TwoBiteSampleWeightNonnegative ω hp_bounds'.1 hp_bounds'.2
  · filter_upwards [TwoBiteNaturalTotalMassOneEventually β hβ m hm, Filter.eventually_ge_atTop 3, OppositeProjectionEdgeProbBounds] with n h_mass hn_ge_three hp_bounds
    let p_n := TwoBiteEdgeProbability β n
    let M := m n
    let E_n := fun ω : TwoBiteSample n M p_n =>
                (∃ r b : Fin M, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > 100 * (Real.log (n : ℝ)) ^ 3) ∧
                ((∀ r : Fin M, (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * p_n * (M : ℝ)) ∧
                 (∀ b : Fin M, (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * p_n * (M : ℝ)))
    let C_n := (M : ℝ)^2 * Real.exp (- 2 * (Real.log n)^3)
    
    have hp_bounds' : 0 ≤ p_n ∧ p_n ≤ 1 := by rwa [← hβ] at hp_bounds
    have hp_n_nonneg : 0 ≤ p_n := hp_bounds'.1
    have hp_n_le_one : p_n ≤ 1 := hp_bounds'.2
    
    have hC_nonneg : 0 ≤ C_n := by
      apply mul_nonneg
      · positivity
      · exact (Real.exp_pos _).le
    
    have h_cond_bound : ∀ G_R G_B : SimpleGraph (Fin M),
      TwoBiteConditionalProbability n M p_n E_n (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) ≤ C_n := by
      intro G_R G_B
      classical
      unfold TwoBiteConditionalProbability
      by_cases h_den : TwoBiteEventProbability n M p_n (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) = 0
      · rw [if_pos h_den]
        exact hC_nonneg
      · rw [if_neg h_den]
        let bad_event := fun ω : TwoBiteSample n M p_n => ∃ r b : Fin M, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > 100 * (Real.log (n : ℝ)) ^ 3
        
        by_cases h_deg : (∀ r : Fin M, (GraphDegreeCount G_R r : ℝ) ≤ 2 * p_n * (M : ℝ)) ∧ (∀ b : Fin M, (GraphDegreeCount G_B b : ℝ) ≤ 2 * p_n * (M : ℝ))
        · -- Degree good case: use FiberAndDegreeMixedLiftedIntersectionUniformBound
          have h_prob_pos : 0 < TwoBiteEventProbability n M p_n (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) := by
            have h_nonneg : 0 ≤ TwoBiteEventProbability n M p_n (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) := by
              unfold TwoBiteEventProbability; apply Finset.sum_nonneg; intro ω _; apply TwoBiteSampleWeightNonnegative ω hp_n_nonneg hp_n_le_one
            exact lt_of_le_of_ne h_nonneg (Ne.symm h_den)
            
          have h_num_le : TwoBiteEventProbability n M p_n (fun ω => E_n ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) ≤
                          TwoBiteEventProbability n M p_n (fun ω => bad_event ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro ω hω
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
              rcases hω with ⟨⟨h_bad, h_deg_ω⟩, h_G⟩
              exact ⟨h_bad, h_G⟩
            · intro ω _ _
              apply TwoBiteSampleWeightNonnegative ω hp_n_nonneg hp_n_le_one
          
          have h_unif := FiberAndDegreeMixedLiftedIntersectionUniformBound n M p_n (hm n) (by rw [← hβ]) h_mass.1 (by
              have h3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
              have hn : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_three
              rw [← Real.log_exp 1]
              apply Real.log_le_log (Real.exp_pos 1)
              exact h3.le.trans hn) G_R G_B (fun r b => ⟨h_deg.1 r, h_deg.2 b⟩)
          unfold TwoBiteConditionalProbability at h_unif
          rw [if_neg h_den] at h_unif
          
          exact le_trans (div_le_div_of_nonneg_right h_num_le h_prob_pos.le) h_unif
        · -- Degree bad case: conditional probability is 0
          have h_num : TwoBiteEventProbability n M p_n (fun ω => E_n ω ∧ ω.1 = G_R ∧ ω.2.1 = G_B) = 0 := by
            apply Finset.sum_eq_zero
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            rcases hω with ⟨⟨_, hdeg_ω⟩, ⟨hR_ω, hB_ω⟩⟩
            exfalso
            apply h_deg
            rw [← hR_ω, ← hB_ω]
            exact hdeg_ω
          rw [h_num, zero_div]
          exact hC_nonneg
          
    have hweight : ∀ ω : TwoBiteSample n M p_n, 0 ≤ TwoBiteSampleWeight ω := fun ω => TwoBiteSampleWeightNonnegative ω hp_n_nonneg hp_n_le_one
    have h_final := FiberAndDegreeMixedLiftedIntersectionConditioning n M p_n E_n C_n hC_nonneg hweight h_cond_bound
    show TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) _ ≤ (m n : ℝ)^2 * Real.exp (- 2 * (Real.log n)^3)
    have h_p_eq : p_n = TwoBiteEdgeProbability β n := rfl
    have h_M_eq : M = m n := rfl
    have h_E_eq : E_n = fun ω : TwoBiteSample n M p_n =>
                (∃ r b : Fin M, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > 100 * (Real.log (n : ℝ)) ^ 3) ∧
                ((∀ r : Fin M, (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * p_n * (M : ℝ)) ∧
                 (∀ b : Fin M, (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * p_n * (M : ℝ))) := rfl
    rw [← h_p_eq, ← h_M_eq, ← h_E_eq]
    exact h_final
