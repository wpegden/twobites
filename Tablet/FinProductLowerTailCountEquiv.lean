import Tablet.UniformInjectionImage

open Finset Classical

-- [TABLET NODE: FinProductLowerTailCountEquiv]

theorem FinProductLowerTailCountEquiv (m n : ℕ) (K : Finset (Fin m × Fin m)) (T : ℝ) :
    ((Finset.univ.filter
        (fun S : Finset (Fin m × Fin m) => S.card = n ∧ ((S ∩ K).card : ℝ) < T)).card : ℝ)
      =
    (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
      (fun S =>
        if ((S ∩ K.image (finProdFinEquiv (m := m) (n := m))).card : ℝ) < T
        then (1 : ℝ) else 0) := by
-- BODY
  let e := finProdFinEquiv (m := m) (n := m)
  have h_bij :
      ((Finset.univ.filter
          (fun S : Finset (Fin m × Fin m) => S.card = n ∧ ((S ∩ K).card : ℝ) < T)).card : ℝ)
        =
      (((Finset.powersetCard n (Finset.univ : Finset (Fin m × Fin m))).filter
          (fun S => ((S ∩ K).card : ℝ) < T)).card : ℝ) := by
    apply congrArg
    congr 1
    ext S
    simp only [mem_filter, mem_univ, mem_powersetCard, true_and]
    simp [subset_univ]
  rw [h_bij]
  have h_sum :
      (((Finset.powersetCard n (Finset.univ : Finset (Fin m × Fin m))).filter
          (fun S => ((S ∩ K).card : ℝ) < T)).card : ℝ)
      =
      (Finset.powersetCard n (Finset.univ : Finset (Fin m × Fin m))).sum
        (fun S => if ((S ∩ K).card : ℝ) < T then (1 : ℝ) else 0) := by
    rw [sum_ite]
    simp
  rw [h_sum]
  apply sum_bij (fun S _ => S.image e)
  · intro S hS
    simp only [mem_powersetCard] at hS ⊢
    exact ⟨subset_univ _, by rw [card_image_of_injective _ e.injective, hS.2]⟩
  · intro S₁ _ S₂ _ h_eq
    have h_inj : Function.Injective (fun S : Finset (Fin m × Fin m) => S.image e) := fun A B hAB => by
      have h_symm : A.image e = B.image e := hAB
      have hA : (A.image e).image e.symm = A := by
        ext x
        simp only [mem_image, Equiv.symm_apply_eq]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, heq⟩
          have hzx : z = x := e.injective heq
          rwa [← hzx]
        · intro hx
          exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
      have hB : (B.image e).image e.symm = B := by
        ext x
        simp only [mem_image, Equiv.symm_apply_eq]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, heq⟩
          have hzx : z = x := e.injective heq
          rwa [← hzx]
        · intro hx
          exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
      rw [← hA, ← hB, h_symm]
    exact h_inj h_eq
  · intro S' hS'
    use S'.image e.symm
    simp only [mem_powersetCard] at hS' ⊢
    refine ⟨⟨subset_univ _, by rw [card_image_of_injective _ e.symm.injective, hS'.2]⟩, ?_⟩
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [Equiv.apply_symm_apply]
      exact hz
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, Equiv.apply_symm_apply _ _⟩
  · intro S _
    have h_inter : (S ∩ K).image e = S.image e ∩ K.image e := by
      ext x
      simp only [mem_image, mem_inter]
      constructor
      · rintro ⟨y, ⟨hyS, hyK⟩, rfl⟩
        exact ⟨⟨y, hyS, rfl⟩, ⟨y, hyK, rfl⟩⟩
      · rintro ⟨⟨y1, hy1, hy1eq⟩, ⟨y2, hy2, hy2eq⟩⟩
        have heq : y1 = y2 := e.injective (by rw [hy1eq, hy2eq])
        subst heq
        exact ⟨y1, ⟨hy1, hy2⟩, hy1eq⟩
    have h_card : ((S ∩ K).card : ℝ) = ((S.image e ∩ K.image e).card : ℝ) := by
      rw [← h_inter]
      rw [card_image_of_injective _ e.injective]
    by_cases hT : ((S.image e ∩ K.image e).card : ℝ) < T
    · rw [if_pos hT, if_pos (by rwa [h_card])]
    · rw [if_neg hT, if_neg (by rwa [h_card])]
