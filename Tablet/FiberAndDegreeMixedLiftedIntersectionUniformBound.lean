import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.UniformInjectionWeight
import Tablet.FiberAndDegreeMixedLiftedIntersectionHypergeometricBound
import Tablet.TwoBiteFixedGraphsConditionalInjectionBridge
import Tablet.UniformInjectionImage
import Tablet.FiberAndDegreeMixedLiftedIntersectionFixedPairInjectionTail

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionUniformBound]

theorem FiberAndDegreeMixedLiftedIntersectionUniformBound (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ))
    (G_R G_B : SimpleGraph (Fin m))
    [DecidableRel G_R.Adj] [DecidableRel G_B.Adj]
    (h_deg : ∀ r b, ((Finset.univ.filter (G_R.Adj r)).card : ℝ) ≤ 2 * p * (m : ℝ) ∧ ((Finset.univ.filter (G_B.Adj b)).card : ℝ) ≤ 2 * p * (m : ℝ)) :
    TwoBiteConditionalProbability n m p
      (fun ω => ∃ r b : Fin m, 
        ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > 100 * (Real.log (n : ℝ)) ^ 3)
      (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) ≤ m^2 * Real.exp (- 2 * (Real.log n)^3) := by
-- BODY
  let T_val : ℝ := 100 * (log n)^3
  let cond := fun ω : TwoBiteSample n m p => ω.1 = G_R ∧ ω.2.1 = G_B
  
  let P_rb : Fin m → Fin m → (Fin n ↪ Fin m × Fin m) → Prop := fun r b ϕ =>
    ((((univ : Finset (Fin n)).image ϕ) ∩ ((univ.filter (G_R.Adj r)) ×ˢ (univ.filter (G_B.Adj b)))).card : ℝ) > T_val
  
  let P_event : (Fin n ↪ Fin m × Fin m) → Prop := fun ϕ => ∃ r b : Fin m, P_rb r b ϕ
  
  unfold TwoBiteConditionalProbability
  by_cases hd : TwoBiteEventProbability n m p cond = 0
  · rw [if_pos hd]
    have h_pos : 0 ≤ (m^2 : ℝ) * Real.exp (- 2 * (Real.log n)^3) := mul_nonneg (by positivity) (exp_pos _).le
    exact h_pos
  · rw [if_neg hd]
    have h_num_eq : TwoBiteEventProbability n m p (fun ω => (∃ r b : Fin m, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > T_val) ∧ cond ω) =
      TwoBiteEventProbability n m p (fun ω => P_event ω.2.2 ∧ cond ω) := by
      apply congr_arg
      ext ω
      by_cases hc : cond ω
      · simp only [hc, and_true]
        rcases hc with ⟨hR, hB⟩
        have h_inter : ∀ r b, TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b) =
          (univ : Finset (Fin n)).filter (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_B.Adj b (ω.2.2 v).2) := by
          intro r b
          ext v
          simp only [mem_inter, mem_filter, mem_univ, true_and]
          unfold TwoBiteLiftedNeighborhood
          unfold TwoBiteRedGraph TwoBiteBlueGraph TwoBiteRedProjection TwoBiteBlueProjection TwoBiteEmbedding
          rw [hR, hB]
          simp
        have h_equiv : (∃ r b : Fin m, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > T_val) ↔ P_event ω.2.2 := by
          dsimp [P_event, P_rb]
          apply exists_congr; intro r
          apply exists_congr; intro b
          rw [h_inter r b]
          have h_inter_img : ((univ : Finset (Fin n)).filter (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_B.Adj b (ω.2.2 v).2)).card =
                             (((univ : Finset (Fin n)).image ω.2.2) ∩ ((univ.filter (G_R.Adj r)) ×ˢ (univ.filter (G_B.Adj b)))).card := by
            have h_eq : (((univ : Finset (Fin n)).image ω.2.2).filter (fun x => G_R.Adj r x.1 ∧ G_B.Adj b x.2)) =
                        (((univ : Finset (Fin n)).image ω.2.2) ∩ ((univ.filter (G_R.Adj r)) ×ˢ (univ.filter (G_B.Adj b)))) := by
              ext x
              simp only [mem_filter, mem_inter, mem_product, mem_univ, true_and]
            rw [← h_eq]
            have h_filter_image_size : ((univ : Finset (Fin n)).filter (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_B.Adj b (ω.2.2 v).2)).card = (((univ : Finset (Fin n)).image ω.2.2).filter (fun x => G_R.Adj r x.1 ∧ G_B.Adj b x.2)).card := by
              have h_img : (((univ : Finset (Fin n)).image ω.2.2).filter (fun x => G_R.Adj r x.1 ∧ G_B.Adj b x.2)) = ((univ : Finset (Fin n)).filter (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_B.Adj b (ω.2.2 v).2)).image ω.2.2 := by
                ext x
                simp only [mem_filter, mem_image, mem_univ, true_and]
                constructor
                · rintro ⟨⟨v, rfl⟩, hP⟩; exact ⟨v, hP, rfl⟩
                · rintro ⟨v, hP, rfl⟩; exact ⟨⟨v, rfl⟩, hP⟩
              rw [h_img, card_image_of_injective _ ω.2.2.injective]
            exact h_filter_image_size
          rw [h_inter_img]
        exact h_equiv
      · simp [hc]
    
    have h_frac_eq : TwoBiteEventProbability n m p (fun ω => (∃ r b : Fin m, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) > T_val) ∧ cond ω) / TwoBiteEventProbability n m p cond =
                     (↑((filter P_event univ).card) : ℝ) / ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by
      rw [h_num_eq]
      have h_bridges := TwoBiteFixedGraphsConditionalInjectionBridge n m p G_R G_B P_event
      rcases h_bridges with ⟨h_den, h_num2⟩
      rw [h_den, h_num2]
      have hd2 : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) ≠ 0 := by
        rw [← h_den]
        exact hd
      have hd_inner : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m ≠ 0 := by
        intro H
        rw [H, zero_mul] at hd2
        exact hd2 rfl
      have h_mul := mul_div_mul_left (↑(#(filter P_event univ)) : ℝ) (↑(Fintype.card (Fin n ↪ Fin m × Fin m)) : ℝ) hd_inner
      convert h_mul
    
    rw [h_frac_eq]
    
    have hB_ne_0 : (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) ≠ 0 := by
      have h_den : TwoBiteEventProbability n m p cond = GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := (TwoBiteFixedGraphsConditionalInjectionBridge n m p G_R G_B P_event).1
      intro H
      have : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) = 0 := by rw [H, mul_zero]
      rw [← h_den] at this
      exact hd this
    have hB_nonneg : (0 : ℝ) ≤ ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by positivity
    have hB_pos : (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) > 0 := lt_of_le_of_ne hB_nonneg hB_ne_0.symm
    
    rw [div_le_iff₀ hB_pos]
    
    have h_union : (filter P_event univ).card ≤ ∑ p_pair : Fin m × Fin m, (filter (fun ϕ => P_rb p_pair.1 p_pair.2 ϕ) univ).card := by
      have h_subset : filter P_event univ ⊆ univ.biUnion (fun p_pair : Fin m × Fin m => filter (fun ϕ => P_rb p_pair.1 p_pair.2 ϕ) univ) := by
        intro ϕ hϕ
        simp only [mem_filter, mem_univ, true_and] at hϕ
        rcases hϕ with ⟨r, b, hr⟩
        simp only [mem_biUnion, mem_univ, mem_filter, true_and]
        use ⟨r, b⟩
      have h_card_le := card_le_card h_subset
      have h_card_biUnion : (univ.biUnion (fun p_pair : Fin m × Fin m => filter (fun ϕ => P_rb p_pair.1 p_pair.2 ϕ) univ)).card ≤ ∑ p_pair : Fin m × Fin m, (filter (fun ϕ => P_rb p_pair.1 p_pair.2 ϕ) univ).card := card_biUnion_le
      exact h_card_le.trans h_card_biUnion
      
    have h_union_real : (↑((filter P_event univ).card) : ℝ) ≤ ∑ p_pair : Fin m × Fin m, ↑((filter (fun ϕ => P_rb p_pair.1 p_pair.2 ϕ) univ).card) := by
      push_cast
      exact_mod_cast h_union
      
    apply le_trans h_union_real
    
    have h_m2 : (∑ p_pair : Fin m × Fin m, Real.exp (- 2 * (Real.log n)^3) * ↑(Fintype.card (Fin n ↪ Fin m × Fin m))) =
                m ^ 2 * Real.exp (- 2 * (Real.log n)^3) * ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by
      rw [sum_const]
      simp
      ring
    rw [← h_m2]
    
    apply sum_le_sum
    intro p_pair _
    dsimp [P_rb, T_val]
    exact FiberAndDegreeMixedLiftedIntersectionFixedPairInjectionTail
      n m p hm hp h_support h_log G_R G_B p_pair.1 p_pair.2
      (h_deg p_pair.1 p_pair.2).1 (h_deg p_pair.1 p_pair.2).2
