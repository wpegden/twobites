import Tablet.HypergeometricCountingTailBound
import Tablet.UniformInjectionImage
import Tablet.FinProductTailCountEquiv

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeFiberSizeImageHypergeometricTail]

theorem FiberAndDegreeFiberSizeImageHypergeometricTail
    (n m : ℕ) (K : Finset (Fin m × Fin m)) (hK : K.card = m)
    (T : ℝ) (h_support : n ≤ m * m) (hT : 0 < T) :
    ((Finset.univ.filter (fun (phi : Function.Embedding (Fin n) (Fin m × Fin m)) =>
      T < ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ))).card : ℝ)
      ≤ ((Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T) *
        (Fintype.card (α := Function.Embedding (Fin n) (Fin m × Fin m)) : ℝ) := by
-- BODY
  classical
  let inj_filter :=
    Finset.univ.filter (fun (phi : Function.Embedding (Fin n) (Fin m × Fin m)) =>
      T < ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ))
  let sub_filter :=
    Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = n ∧ T < ((S ∩ K).card : ℝ))
  let totalInj := Fintype.card (α := Function.Embedding (Fin n) (Fin m × Fin m))
  let chooseN := Nat.choose (m * m) n
  let e : (Fin m × Fin m) ≃ Fin (m * m) := finProdFinEquiv (m := m) (n := m)
  let Kset : Finset (Fin (m * m)) := K.image e
  have hKset_card : Kset.card = m := by
    dsimp [Kset]
    rw [Finset.card_image_of_injective _ e.injective, hK]
  have hmN : m ≤ m * m := by
    calc
      m = K.card := hK.symm
      _ ≤ Fintype.card (Fin m × Fin m) := Finset.card_le_univ K
      _ = m * m := by simp
  have hUI_nat : inj_filter.card * chooseN = sub_filter.card * totalInj := by
    dsimp [inj_filter, chooseN, sub_filter, totalInj]
    simpa using
      (UniformInjectionImage (n := n) (m := m) (k := n)
        (Finset.univ : Finset (Fin n)) (by simp)
        (fun S : Finset (Fin m × Fin m) => T < ((S ∩ K).card : ℝ)))
  have hUI : (inj_filter.card : ℝ) * (chooseN : ℝ) =
      (sub_filter.card : ℝ) * (totalInj : ℝ) := by
    exact_mod_cast hUI_nat
  have hchoose_pos : 0 < (chooseN : ℝ) := by
    dsimp [chooseN]
    exact_mod_cast Nat.choose_pos h_support
  have htotal_pos : 0 < (totalInj : ℝ) := by
    have hnonempty : Nonempty (Function.Embedding (Fin n) (Fin m × Fin m)) := by
      let f : Function.Embedding (Fin n) (Fin (m * m)) :=
        ⟨fun i => Fin.castLE h_support i,
          fun _ _ h => Fin.castLE_injective h_support h⟩
      exact ⟨f.trans e.symm.toEmbedding⟩
    dsimp [totalInj]
    exact_mod_cast Fintype.card_pos
  have hmu_eq :
      (n : ℝ) * ((m : ℝ) / (m * m : ℝ)) = (n : ℝ) / (m : ℝ) := by
    by_cases hm0 : (m : ℝ) = 0
    · simp [hm0]
    · have hN : (m * m : ℝ) = (m : ℝ) * (m : ℝ) := by
        simp
      rw [hN]
      field_simp [hm0]
  have hHyper :
      ((((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => T ≤ ((S ∩ Kset).card : ℝ))).card : ℝ) /
          (Nat.choose (m * m) n : ℝ)) ≤
        (Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T := by
    have h :=
      HypergeometricCountingTailBound (m * m) n m h_support hmN Kset hKset_card T hT
    simpa [hmu_eq, ge_iff_le] using h
  have hSubsets_le :
      (sub_filter.card : ℝ) / (chooseN : ℝ) ≤
        (Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T := by
    have h_equiv :
        (sub_filter.card : ℝ) =
          (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if T < ((S ∩ Kset).card : ℝ) then (1 : ℝ) else 0) := by
      dsimp [sub_filter, Kset]
      simpa [gt_iff_lt] using FinProductTailCountEquiv m n K T
    have h_sum_card :
        (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if T < ((S ∩ Kset).card : ℝ) then (1 : ℝ) else 0) =
          (((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
            (fun S => T < ((S ∩ Kset).card : ℝ))).card : ℝ) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    let gt_filter :=
      (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => T < ((S ∩ Kset).card : ℝ))
    let ge_filter :=
      (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => T ≤ ((S ∩ Kset).card : ℝ))
    have h_gt_le_ge : (gt_filter.card : ℝ) ≤ (ge_filter.card : ℝ) := by
      norm_cast
      apply Finset.card_le_card
      intro S hS
      simp [gt_filter, ge_filter] at hS ⊢
      exact ⟨hS.1, le_of_lt hS.2⟩
    rw [h_equiv, h_sum_card]
    have hdiv :=
      div_le_div_of_nonneg_right h_gt_le_ge (le_of_lt hchoose_pos)
    exact hdiv.trans (by simpa [chooseN, ge_filter] using hHyper)
  have hratio :
      (inj_filter.card : ℝ) / (totalInj : ℝ) =
        (sub_filter.card : ℝ) / (chooseN : ℝ) := by
    rw [div_eq_div_iff htotal_pos.ne.symm hchoose_pos.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hUI
  have hfinal :
      (inj_filter.card : ℝ) ≤
        ((Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T) * (totalInj : ℝ) := by
    calc
      (inj_filter.card : ℝ)
          = (totalInj : ℝ) * ((inj_filter.card : ℝ) / (totalInj : ℝ)) := by
            rw [mul_div_cancel₀ _ htotal_pos.ne.symm]
      _ = (totalInj : ℝ) * ((sub_filter.card : ℝ) / (chooseN : ℝ)) := by
            rw [hratio]
      _ ≤ (totalInj : ℝ) *
          ((Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T) := by
            exact mul_le_mul_of_nonneg_left hSubsets_le (le_of_lt htotal_pos)
      _ = ((Real.exp 1 * ((n : ℝ) / (m : ℝ)) / T) ^ T) * (totalInj : ℝ) := by
            ring
  simpa [inj_filter, totalInj] using hfinal
