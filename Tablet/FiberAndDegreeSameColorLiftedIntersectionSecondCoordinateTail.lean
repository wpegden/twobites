import Tablet.FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeSameColorLiftedIntersectionSecondCoordinateTail]

theorem FiberAndDegreeSameColorLiftedIntersectionSecondCoordinateTail
    (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ))
    (h_ratio : (n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 * (m : ℝ))
    (G_B : SimpleGraph (Fin m))
    [DecidableRel G_B.Adj]
    (b c : Fin m)
    (hbc : b ≠ c)
    (hB : ((Finset.univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)).card : ℝ) ≤ Real.log (n : ℝ)) :
    ((Finset.univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
        ((Finset.univ : Finset (Fin m)) ×ˢ
          (Finset.univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))).card : ℝ)
        > 100 * (Real.log (n : ℝ)) ^ 3)).card : ℝ)
      ≤ Real.exp (-2 * (Real.log (n : ℝ))^3) *
        (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
-- BODY
  classical
  let A : Finset (Fin m) := Finset.univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)
  let swapEmbedding : (Fin n ↪ Fin m × Fin m) ≃ (Fin n ↪ Fin m × Fin m) :=
    { toFun := fun ϕ =>
        { toFun := fun v => ((ϕ v).2, (ϕ v).1)
          inj' := by
            intro x y hxy
            apply ϕ.injective
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy) }
      invFun := fun ϕ =>
        { toFun := fun v => ((ϕ v).2, (ϕ v).1)
          inj' := by
            intro x y hxy
            apply ϕ.injective
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy) }
      left_inv := by
        intro ϕ
        ext v <;> rfl
      right_inv := by
        intro ϕ
        ext v <;> rfl }
  let Pblue : (Fin n ↪ Fin m × Fin m) → Prop := fun ϕ =>
    ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
      ((Finset.univ : Finset (Fin m)) ×ˢ A)).card : ℝ)
      > 100 * (Real.log (n : ℝ)) ^ 3
  let Pred : (Fin n ↪ Fin m × Fin m) → Prop := fun ϕ =>
    ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
      (A ×ˢ (Finset.univ : Finset (Fin m)))).card : ℝ)
      > 100 * (Real.log (n : ℝ)) ^ 3
  have hswap_prop : ∀ ϕ : Fin n ↪ Fin m × Fin m, Pblue ϕ ↔ Pred (swapEmbedding ϕ) := by
    intro ϕ
    dsimp [Pblue, Pred, A]
    let hitA : Fin n → Prop := fun v => (ϕ v).2 ∈ A
    have hblue : ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
        ((Finset.univ : Finset (Fin m)) ×ˢ A)).card =
        ((Finset.univ : Finset (Fin n)).filter hitA).card) := by
      have hset :
          (((Finset.univ : Finset (Fin n)).image ϕ) ∩
            ((Finset.univ : Finset (Fin m)) ×ˢ A)) =
          ((Finset.univ : Finset (Fin n)).filter hitA).image ϕ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_product]
        constructor
        · rintro ⟨⟨v, hv⟩, hx⟩
          refine ⟨v, ?_, hv⟩
          simpa [hitA, ← hv] using hx
        · rintro ⟨v, hvA, hvx⟩
          refine ⟨⟨v, hvx⟩, ?_⟩
          simpa [hitA, hvx] using hvA
      rw [hset, Finset.card_image_of_injective _ ϕ.injective]
    have hred : ((((Finset.univ : Finset (Fin n)).image (swapEmbedding ϕ)) ∩
        (A ×ˢ (Finset.univ : Finset (Fin m)))).card =
        ((Finset.univ : Finset (Fin n)).filter hitA).card) := by
      have hset :
          (((Finset.univ : Finset (Fin n)).image (swapEmbedding ϕ)) ∩
            (A ×ˢ (Finset.univ : Finset (Fin m)))) =
          ((Finset.univ : Finset (Fin n)).filter hitA).image (swapEmbedding ϕ) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_product]
        constructor
        · rintro ⟨⟨v, hv⟩, hx⟩
          refine ⟨v, ?_, hv⟩
          dsimp [swapEmbedding] at hv
          simpa [hitA, ← hv] using hx
        · rintro ⟨v, hvA, hvx⟩
          refine ⟨⟨v, hvx⟩, ?_⟩
          rw [← hvx]
          simpa [hitA, swapEmbedding] using hvA
      rw [hset, Finset.card_image_of_injective _ (swapEmbedding ϕ).injective]
    rw [hblue, hred]
  have hswap : (Finset.univ.filter Pblue).card = (Finset.univ.filter Pred).card := by
    refine Finset.card_bij (fun ϕ _ => swapEmbedding ϕ) ?_ ?_ ?_
    · intro ϕ hϕ
      rw [Finset.mem_filter] at hϕ ⊢
      constructor
      · exact Finset.mem_univ _
      · exact (hswap_prop ϕ).mp hϕ.2
    · intro ϕ hϕ ψ hψ h
      exact swapEmbedding.injective h
    · intro ψ hψ
      refine ⟨swapEmbedding.symm ψ, ?_, ?_⟩
      · rw [Finset.mem_filter] at hψ ⊢
        constructor
        · exact Finset.mem_univ _
        · have hpred : Pred ψ := hψ.2
          simpa using (hswap_prop (swapEmbedding.symm ψ)).mpr (by simpa using hpred)
      · simp [swapEmbedding]
  rw [show
      (Finset.univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
          ((Finset.univ : Finset (Fin m)) ×ˢ
            (Finset.univ.filter (fun t => G_B.Adj b t ∧ G_B.Adj c t)))).card : ℝ)
          > 100 * (Real.log (n : ℝ)) ^ 3)).card
        = (Finset.univ.filter Pblue).card by rfl]
  rw [hswap]
  simpa [Pred, A] using
    FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
      n m p hm hp h_support h_log h_ratio G_B b c hbc hB
