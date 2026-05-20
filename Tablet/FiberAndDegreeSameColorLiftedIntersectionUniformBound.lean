import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteFixedGraphsConditionalInjectionBridge
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
import Tablet.FiberAndDegreeSameColorLiftedIntersectionSecondCoordinateTail

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeSameColorLiftedIntersectionUniformBound]

theorem FiberAndDegreeSameColorLiftedIntersectionUniformBound
    (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ))
    (h_ratio : (n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 * (m : ℝ))
    (G_R G_B : SimpleGraph (Fin m))
    [DecidableRel G_R.Adj] [DecidableRel G_B.Adj]
    (h_codeg :
      (∀ r s : Fin m, r ≠ s →
        ((Finset.univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
      (∀ b c : Fin m, b ≠ c →
        ((Finset.univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))) :
    TwoBiteConditionalProbability n m p
      (fun ω =>
        (∃ r s : Fin m, r ≠ s ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3) ∨
        (∃ b c : Fin m, b ≠ c ∧
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
            > 100 * (Real.log (n : ℝ)) ^ 3))
      (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B)
      ≤ (2 : ℝ) * (m : ℝ)^2 * Real.exp (-2 * (Real.log (n : ℝ))^3) := by
-- BODY
  classical
  let T_val : ℝ := 100 * (log n)^3
  let cond := fun ω : TwoBiteSample n m p => ω.1 = G_R ∧ ω.2.1 = G_B
  let RedP : Fin m → Fin m → (Fin n ↪ Fin m × Fin m) → Prop := fun r s ϕ =>
    r ≠ s ∧
      ((((univ : Finset (Fin n)).image ϕ) ∩
        ((univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
          (univ : Finset (Fin m)))).card : ℝ) > T_val
  let BlueP : Fin m → Fin m → (Fin n ↪ Fin m × Fin m) → Prop := fun b c ϕ =>
    b ≠ c ∧
      ((((univ : Finset (Fin n)).image ϕ) ∩
        ((univ : Finset (Fin m)) ×ˢ
          (univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))).card : ℝ) > T_val
  let P_event : (Fin n ↪ Fin m × Fin m) → Prop := fun ϕ =>
    (∃ r s : Fin m, RedP r s ϕ) ∨
    (∃ b c : Fin m, BlueP b c ϕ)
  unfold TwoBiteConditionalProbability
  by_cases hd : TwoBiteEventProbability n m p cond = 0
  · rw [if_pos hd]
    positivity
  · rw [if_neg hd]
    have h_num_eq :
        TwoBiteEventProbability n m p
          (fun ω =>
            (((∃ r s : Fin m, r ≠ s ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
                > 100 * (Real.log (n : ℝ)) ^ 3) ∨
            (∃ b c : Fin m, b ≠ c ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
                > 100 * (Real.log (n : ℝ)) ^ 3)) ∧ cond ω)) =
        TwoBiteEventProbability n m p (fun ω => P_event ω.2.2 ∧ cond ω) := by
      apply congr_arg
      ext ω
      by_cases hc : cond ω
      · simp only [hc, and_true]
        rcases hc with ⟨hRω, hBω⟩
        have h_red_equiv :
            (∃ r s : Fin m, r ≠ s ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) > T_val)
            ↔ ∃ r s : Fin m, RedP r s ω.2.2 := by
          dsimp [RedP, T_val]
          apply exists_congr; intro r
          apply exists_congr; intro s
          constructor
          · rintro ⟨hrs, hbad⟩
            refine ⟨hrs, ?_⟩
            have h_inter :
                TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s) =
                (univ : Finset (Fin n)).filter
                  (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1) := by
              ext v
              simp only [mem_inter, mem_filter, mem_univ, true_and]
              unfold TwoBiteLiftedNeighborhood
              unfold TwoBiteRedGraph TwoBiteRedProjection TwoBiteEmbedding
              rw [hRω]
              simp
            have h_inter_img :
                ((univ : Finset (Fin n)).filter
                  (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1)).card =
                (((univ : Finset (Fin n)).image ω.2.2) ∩
                  ((univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
                    (univ : Finset (Fin m)))).card := by
              have h_eq :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_R.Adj r x.1 ∧ G_R.Adj s x.1)) =
                  (((univ : Finset (Fin n)).image ω.2.2) ∩
                    ((univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
                      (univ : Finset (Fin m)))) := by
                ext x
                simp
              rw [← h_eq]
              have h_img :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_R.Adj r x.1 ∧ G_R.Adj s x.1)) =
                  ((univ : Finset (Fin n)).filter
                    (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1)).image ω.2.2 := by
                ext x
                simp only [mem_filter, mem_image, mem_univ, true_and]
                constructor
                · rintro ⟨⟨v, rfl⟩, hP⟩
                  exact ⟨v, hP, rfl⟩
                · rintro ⟨v, hP, rfl⟩
                  exact ⟨⟨v, rfl⟩, hP⟩
              rw [h_img, card_image_of_injective _ ω.2.2.injective]
            simpa [h_inter, h_inter_img] using hbad
          · rintro ⟨hrs, hbad⟩
            refine ⟨hrs, ?_⟩
            have h_inter :
                TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s) =
                (univ : Finset (Fin n)).filter
                  (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1) := by
              ext v
              simp only [mem_inter, mem_filter, mem_univ, true_and]
              unfold TwoBiteLiftedNeighborhood
              unfold TwoBiteRedGraph TwoBiteRedProjection TwoBiteEmbedding
              rw [hRω]
              simp
            have h_inter_img :
                ((univ : Finset (Fin n)).filter
                  (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1)).card =
                (((univ : Finset (Fin n)).image ω.2.2) ∩
                  ((univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
                    (univ : Finset (Fin m)))).card := by
              have h_eq :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_R.Adj r x.1 ∧ G_R.Adj s x.1)) =
                  (((univ : Finset (Fin n)).image ω.2.2) ∩
                    ((univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
                      (univ : Finset (Fin m)))) := by
                ext x
                simp
              rw [← h_eq]
              have h_img :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_R.Adj r x.1 ∧ G_R.Adj s x.1)) =
                  ((univ : Finset (Fin n)).filter
                    (fun v => G_R.Adj r (ω.2.2 v).1 ∧ G_R.Adj s (ω.2.2 v).1)).image ω.2.2 := by
                ext x
                simp only [mem_filter, mem_image, mem_univ, true_and]
                constructor
                · rintro ⟨⟨v, rfl⟩, hP⟩
                  exact ⟨v, hP, rfl⟩
                · rintro ⟨v, hP, rfl⟩
                  exact ⟨⟨v, rfl⟩, hP⟩
              rw [h_img, card_image_of_injective _ ω.2.2.injective]
            simpa [h_inter, h_inter_img] using hbad
        have h_blue_equiv :
            (∃ b c : Fin m, b ≠ c ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) > T_val)
            ↔ ∃ b c : Fin m, BlueP b c ω.2.2 := by
          dsimp [BlueP, T_val]
          apply exists_congr; intro b
          apply exists_congr; intro c
          constructor
          · rintro ⟨hbc, hbad⟩
            refine ⟨hbc, ?_⟩
            have h_inter :
                TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c) =
                (univ : Finset (Fin n)).filter
                  (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2) := by
              ext v
              simp only [mem_inter, mem_filter, mem_univ, true_and]
              unfold TwoBiteLiftedNeighborhood
              unfold TwoBiteBlueGraph TwoBiteBlueProjection TwoBiteEmbedding
              rw [hBω]
              simp
            have h_inter_img :
                ((univ : Finset (Fin n)).filter
                  (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2)).card =
                (((univ : Finset (Fin n)).image ω.2.2) ∩
                  ((univ : Finset (Fin m)) ×ˢ
                    (univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))).card := by
              have h_eq :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_B.Adj b x.2 ∧ G_B.Adj c x.2)) =
                  (((univ : Finset (Fin n)).image ω.2.2) ∩
                    ((univ : Finset (Fin m)) ×ˢ
                      (univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))) := by
                ext x
                simp
              rw [← h_eq]
              have h_img :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_B.Adj b x.2 ∧ G_B.Adj c x.2)) =
                  ((univ : Finset (Fin n)).filter
                    (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2)).image ω.2.2 := by
                ext x
                simp only [mem_filter, mem_image, mem_univ, true_and]
                constructor
                · rintro ⟨⟨v, rfl⟩, hP⟩
                  exact ⟨v, hP, rfl⟩
                · rintro ⟨v, hP, rfl⟩
                  exact ⟨⟨v, rfl⟩, hP⟩
              rw [h_img, card_image_of_injective _ ω.2.2.injective]
            simpa [h_inter, h_inter_img] using hbad
          · rintro ⟨hbc, hbad⟩
            refine ⟨hbc, ?_⟩
            have h_inter :
                TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c) =
                (univ : Finset (Fin n)).filter
                  (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2) := by
              ext v
              simp only [mem_inter, mem_filter, mem_univ, true_and]
              unfold TwoBiteLiftedNeighborhood
              unfold TwoBiteBlueGraph TwoBiteBlueProjection TwoBiteEmbedding
              rw [hBω]
              simp
            have h_inter_img :
                ((univ : Finset (Fin n)).filter
                  (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2)).card =
                (((univ : Finset (Fin n)).image ω.2.2) ∩
                  ((univ : Finset (Fin m)) ×ˢ
                    (univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))).card := by
              have h_eq :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_B.Adj b x.2 ∧ G_B.Adj c x.2)) =
                  (((univ : Finset (Fin n)).image ω.2.2) ∩
                    ((univ : Finset (Fin m)) ×ˢ
                      (univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))) := by
                ext x
                simp
              rw [← h_eq]
              have h_img :
                  (((univ : Finset (Fin n)).image ω.2.2).filter
                    (fun x => G_B.Adj b x.2 ∧ G_B.Adj c x.2)) =
                  ((univ : Finset (Fin n)).filter
                    (fun v => G_B.Adj b (ω.2.2 v).2 ∧ G_B.Adj c (ω.2.2 v).2)).image ω.2.2 := by
                ext x
                simp only [mem_filter, mem_image, mem_univ, true_and]
                constructor
                · rintro ⟨⟨v, rfl⟩, hP⟩
                  exact ⟨v, hP, rfl⟩
                · rintro ⟨v, hP, rfl⟩
                  exact ⟨⟨v, rfl⟩, hP⟩
              rw [h_img, card_image_of_injective _ ω.2.2.injective]
            simpa [h_inter, h_inter_img] using hbad
        dsimp [P_event]
        rw [h_red_equiv, h_blue_equiv]
      · simp [hc]
    have h_frac_eq :
        TwoBiteEventProbability n m p
          (fun ω =>
            ((((∃ r s : Fin m, r ≠ s ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
                > 100 * (Real.log (n : ℝ)) ^ 3) ∨
            (∃ b c : Fin m, b ≠ c ∧
              ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
                > 100 * (Real.log (n : ℝ)) ^ 3)) ∧ cond ω))) /
          TwoBiteEventProbability n m p cond =
        (↑((filter P_event univ).card) : ℝ) /
          ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by
      rw [h_num_eq]
      have h_bridges := TwoBiteFixedGraphsConditionalInjectionBridge n m p G_R G_B P_event
      rcases h_bridges with ⟨h_den, h_num2⟩
      rw [h_den, h_num2]
      have hd2 : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m *
          ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) ≠ 0 := by
        rw [← h_den]
        exact hd
      have hd_inner : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m ≠ 0 := by
        intro H
        rw [H, zero_mul] at hd2
        exact hd2 rfl
      have h_mul := mul_div_mul_left
        (↑((filter P_event univ).card) : ℝ)
        (↑(Fintype.card (Fin n ↪ Fin m × Fin m)) : ℝ) hd_inner
      convert h_mul
    rw [h_frac_eq]
    have hB_ne_0 : (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) ≠ 0 := by
      have h_den : TwoBiteEventProbability n m p cond =
          GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m *
            ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) :=
        (TwoBiteFixedGraphsConditionalInjectionBridge n m p G_R G_B P_event).1
      intro H
      have : GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m *
          ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) = 0 := by rw [H, mul_zero]
      rw [← h_den] at this
      exact hd this
    have hB_nonneg : (0 : ℝ) ≤ ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by positivity
    have hB_pos : (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) > 0 :=
      lt_of_le_of_ne hB_nonneg hB_ne_0.symm
    rw [div_le_iff₀ hB_pos]
    let Idx := Sum (Fin m × Fin m) (Fin m × Fin m)
    let PairP : Idx → (Fin n ↪ Fin m × Fin m) → Prop := fun idx ϕ =>
      match idx with
      | Sum.inl pair => RedP pair.1 pair.2 ϕ
      | Sum.inr pair => BlueP pair.1 pair.2 ϕ
    have h_union :
        (filter P_event univ).card ≤ ∑ idx : Idx, (filter (PairP idx) univ).card := by
      have h_subset :
          filter P_event univ ⊆ univ.biUnion (fun idx : Idx => filter (PairP idx) univ) := by
        intro ϕ hϕ
        simp only [mem_filter, mem_univ, true_and] at hϕ
        dsimp [P_event] at hϕ
        simp only [mem_biUnion, mem_univ, mem_filter, true_and]
        rcases hϕ with hred | hblue
        · rcases hred with ⟨r, s, hrs⟩
          exact ⟨Sum.inl (r, s), hrs⟩
        · rcases hblue with ⟨b, c, hbc⟩
          exact ⟨Sum.inr (b, c), hbc⟩
      exact (card_le_card h_subset).trans card_biUnion_le
    have h_union_real :
        (↑((filter P_event univ).card) : ℝ) ≤
          ∑ idx : Idx, ↑((filter (PairP idx) univ).card) := by
      exact_mod_cast h_union
    apply le_trans h_union_real
    have h_const_sum :
        (∑ idx : Idx,
          Real.exp (-2 * (Real.log (n : ℝ))^3) *
            ↑(Fintype.card (Fin n ↪ Fin m × Fin m))) =
        (2 : ℝ) * (m : ℝ)^2 * Real.exp (-2 * (Real.log (n : ℝ))^3) *
          ↑(Fintype.card (Fin n ↪ Fin m × Fin m)) := by
      rw [sum_const]
      simp [Idx]
      ring
    rw [← h_const_sum]
    apply sum_le_sum
    intro idx _
    cases idx with
    | inl pair =>
        by_cases hneq : pair.1 ≠ pair.2
        · simpa [PairP, RedP, T_val, hneq] using
            FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
              n m p hm hp h_support h_log h_ratio G_R pair.1 pair.2 hneq
              (h_codeg.1 pair.1 pair.2 hneq)
        · simp [PairP, RedP, hneq]
          positivity
    | inr pair =>
        by_cases hneq : pair.1 ≠ pair.2
        · simpa [PairP, BlueP, T_val, hneq] using
            FiberAndDegreeSameColorLiftedIntersectionSecondCoordinateTail
              n m p hm hp h_support h_log h_ratio G_B pair.1 pair.2 hneq
              (h_codeg.2 pair.1 pair.2 hneq)
        · simp [PairP, BlueP, hneq]
          positivity
