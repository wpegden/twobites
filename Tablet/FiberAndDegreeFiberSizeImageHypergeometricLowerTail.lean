import Tablet.HypergeometricCountingLowerTailBound
import Tablet.UniformInjectionImage
import Tablet.FinProductLowerTailCountEquiv

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeFiberSizeImageHypergeometricLowerTail]

theorem FiberAndDegreeFiberSizeImageHypergeometricLowerTail
    (n m : ℕ) (K : Finset (Fin m × Fin m)) (hK : K.card = m)
    (δ : ℝ) (h_support : n ≤ m * m) (hm_pos : 0 < m)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 2 : ℝ)) :
    ((Finset.univ.filter (fun (phi : Function.Embedding (Fin n) (Fin m × Fin m)) =>
      ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ) <
        (1 - δ) * ((n : ℝ) / (m : ℝ)))).card : ℝ)
      ≤ Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * ((n : ℝ) / (m : ℝ))) *
        (Fintype.card (α := Function.Embedding (Fin n) (Fin m × Fin m)) : ℝ) := by
-- BODY
  classical
  let μ : ℝ := (n : ℝ) / (m : ℝ)
  let threshold : ℝ := (1 - δ) * μ
  let inj_filter :=
    Finset.univ.filter (fun (phi : Function.Embedding (Fin n) (Fin m × Fin m)) =>
      ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ) < threshold)
  let sub_filter :=
    Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = n ∧ ((S ∩ K).card : ℝ) < threshold)
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
    dsimp [inj_filter, chooseN, sub_filter, totalInj, threshold, μ]
    simpa using
      (UniformInjectionImage (n := n) (m := m) (k := n)
        (Finset.univ : Finset (Fin n)) (by simp)
        (fun S : Finset (Fin m × Fin m) =>
          ((S ∩ K).card : ℝ) < (1 - δ) * ((n : ℝ) / (m : ℝ))))
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
  have hδ_lt_one : δ < 1 := by
    linarith
  have hmu_eq :
      (n : ℝ) * ((m : ℝ) / (m * m : ℝ)) = μ := by
    dsimp [μ]
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hm_pos)
    have hN : (m * m : ℝ) = (m : ℝ) * (m : ℝ) := by
      simp
    rw [hN]
    field_simp [hm_ne]
  have hHyper :
      ((((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => ((S ∩ Kset).card : ℝ) < threshold)).card : ℝ) /
          (Nat.choose (m * m) n : ℝ)) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
    have h :=
      HypergeometricCountingLowerTailBound (m * m) n m
        h_support hmN Kset hKset_card δ hδ_pos hδ_lt_one
    simpa [threshold, μ, hmu_eq] using h
  have hSubsets_le :
      (sub_filter.card : ℝ) / (chooseN : ℝ) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
    have h_equiv :
        (sub_filter.card : ℝ) =
          (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if ((S ∩ Kset).card : ℝ) < threshold then (1 : ℝ) else 0) := by
      dsimp [sub_filter, Kset, threshold, μ]
      simpa using
        FinProductLowerTailCountEquiv m n K ((1 - δ) * ((n : ℝ) / (m : ℝ)))
    have h_sum_card :
        (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if ((S ∩ Kset).card : ℝ) < threshold then (1 : ℝ) else 0) =
          (((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
            (fun S => ((S ∩ Kset).card : ℝ) < threshold)).card : ℝ) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h_equiv, h_sum_card]
    simpa [chooseN] using hHyper
  have hratio :
      (inj_filter.card : ℝ) / (totalInj : ℝ) =
        (sub_filter.card : ℝ) / (chooseN : ℝ) := by
    rw [div_eq_div_iff htotal_pos.ne.symm hchoose_pos.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hUI
  have hfinal :
      (inj_filter.card : ℝ) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) * (totalInj : ℝ) := by
    calc
      (inj_filter.card : ℝ)
          = (totalInj : ℝ) * ((inj_filter.card : ℝ) / (totalInj : ℝ)) := by
            rw [mul_div_cancel₀ _ htotal_pos.ne.symm]
      _ = (totalInj : ℝ) * ((sub_filter.card : ℝ) / (chooseN : ℝ)) := by
            rw [hratio]
      _ ≤ (totalInj : ℝ) *
          Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
            exact mul_le_mul_of_nonneg_left hSubsets_le (le_of_lt htotal_pos)
      _ = Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) * (totalInj : ℝ) := by
            ring
  simpa [inj_filter, totalInj, threshold, μ] using hfinal
