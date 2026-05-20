import Tablet.FinProductLowerTailCountEquiv
import Tablet.FinProductTailCountEquiv
import Tablet.HypergeometricCountingLowerTailBound
import Tablet.HypergeometricCountingUpperChernoffBound
import Tablet.UniformInjectionImage

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeLiftedSizeImageHypergeometricTail]

theorem FiberAndDegreeLiftedSizeImageHypergeometricTail
    (n m q : ℕ) (K : Finset (Fin m × Fin m)) (hK : K.card = q)
    (δ : ℝ) (h_support : n ≤ m * m)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 2 : ℝ)) :
    let mu : ℝ := (n : ℝ) * ((q : ℝ) / (m * m : ℝ))
    ((Finset.univ.filter (fun (phi : Function.Embedding (Fin n) (Fin m × Fin m)) =>
      ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ) < (1 - δ) * mu ∨
        (1 + δ) * mu <
          ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ))).card : ℝ)
      ≤
        (Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) +
          Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu))) *
        (Fintype.card (α := Function.Embedding (Fin n) (Fin m × Fin m)) : ℝ) := by
-- BODY
  classical
  let mu : ℝ := (n : ℝ) * ((q : ℝ) / (m * m : ℝ))
  let lowerThreshold : ℝ := (1 - δ) * mu
  let upperThreshold : ℝ := (1 + δ) * mu
  let countHits : Function.Embedding (Fin n) (Fin m × Fin m) → ℝ :=
    fun phi => ((((Finset.univ : Finset (Fin n)).image phi) ∩ K).card : ℝ)
  let badInj :=
    Finset.univ.filter (fun phi : Function.Embedding (Fin n) (Fin m × Fin m) =>
      countHits phi < lowerThreshold ∨ upperThreshold < countHits phi)
  let upperInj :=
    Finset.univ.filter (fun phi : Function.Embedding (Fin n) (Fin m × Fin m) =>
      upperThreshold < countHits phi)
  let lowerInj :=
    Finset.univ.filter (fun phi : Function.Embedding (Fin n) (Fin m × Fin m) =>
      countHits phi < lowerThreshold)
  let upperSub :=
    Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = n ∧ upperThreshold < ((S ∩ K).card : ℝ))
  let lowerSub :=
    Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = n ∧ ((S ∩ K).card : ℝ) < lowerThreshold)
  let totalInj := Fintype.card (α := Function.Embedding (Fin n) (Fin m × Fin m))
  let chooseN := Nat.choose (m * m) n
  let e : (Fin m × Fin m) ≃ Fin (m * m) := finProdFinEquiv (m := m) (n := m)
  let Kset : Finset (Fin (m * m)) := K.image e
  have hKset_card : Kset.card = q := by
    dsimp [Kset]
    rw [Finset.card_image_of_injective _ e.injective, hK]
  have hqN : q ≤ m * m := by
    calc
      q = K.card := hK.symm
      _ ≤ Fintype.card (Fin m × Fin m) := Finset.card_le_univ K
      _ = m * m := by simp
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
  have hUpperUI_nat : upperInj.card * chooseN = upperSub.card * totalInj := by
    dsimp [upperInj, upperSub, chooseN, totalInj, countHits, upperThreshold, mu]
    simpa using
      (UniformInjectionImage (n := n) (m := m) (k := n)
        (Finset.univ : Finset (Fin n)) (by simp)
        (fun S : Finset (Fin m × Fin m) =>
          (1 + δ) * ((n : ℝ) * ((q : ℝ) / (m * m : ℝ))) <
            ((S ∩ K).card : ℝ)))
  have hUpperUI : (upperInj.card : ℝ) * (chooseN : ℝ) =
      (upperSub.card : ℝ) * (totalInj : ℝ) := by
    exact_mod_cast hUpperUI_nat
  have hLowerUI_nat : lowerInj.card * chooseN = lowerSub.card * totalInj := by
    dsimp [lowerInj, lowerSub, chooseN, totalInj, countHits, lowerThreshold, mu]
    simpa using
      (UniformInjectionImage (n := n) (m := m) (k := n)
        (Finset.univ : Finset (Fin n)) (by simp)
        (fun S : Finset (Fin m × Fin m) =>
          ((S ∩ K).card : ℝ) <
            (1 - δ) * ((n : ℝ) * ((q : ℝ) / (m * m : ℝ)))))
  have hLowerUI : (lowerInj.card : ℝ) * (chooseN : ℝ) =
      (lowerSub.card : ℝ) * (totalInj : ℝ) := by
    exact_mod_cast hLowerUI_nat
  have hUpperSubsets :
      ((((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => upperThreshold < ((S ∩ Kset).card : ℝ))).card : ℝ) /
          (Nat.choose (m * m) n : ℝ))
        ≤
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) := by
    have h :=
      HypergeometricCountingUpperChernoffBound (m * m) n q h_support hqN
        Kset hKset_card δ hδ_pos
    simpa [upperThreshold, mu] using h
  have hUpperSub_le :
      (upperSub.card : ℝ) / (chooseN : ℝ) ≤
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) := by
    have h_equiv :
        (upperSub.card : ℝ)
        =
          (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if upperThreshold < ((S ∩ Kset).card : ℝ) then (1 : ℝ) else 0) := by
      dsimp [upperSub, Kset, upperThreshold, mu]
      simpa [gt_iff_lt] using
        FinProductTailCountEquiv m n K
          ((1 + δ) * ((n : ℝ) * ((q : ℝ) / (m * m : ℝ))))
    have h_sum_card :
        (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if upperThreshold < ((S ∩ Kset).card : ℝ) then (1 : ℝ) else 0) =
          (((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
            (fun S => upperThreshold < ((S ∩ Kset).card : ℝ))).card : ℝ) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h_equiv, h_sum_card]
    simpa [chooseN] using hUpperSubsets
  have hUpperRatio :
      (upperInj.card : ℝ) / (totalInj : ℝ) =
        (upperSub.card : ℝ) / (chooseN : ℝ) := by
    rw [div_eq_div_iff htotal_pos.ne.symm hchoose_pos.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperUI
  have hUpper :
      (upperInj.card : ℝ) ≤
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) *
          (totalInj : ℝ) := by
    calc
      (upperInj.card : ℝ)
          = (totalInj : ℝ) * ((upperInj.card : ℝ) / (totalInj : ℝ)) := by
            rw [mul_div_cancel₀ _ htotal_pos.ne.symm]
      _ = (totalInj : ℝ) * ((upperSub.card : ℝ) / (chooseN : ℝ)) := by
            rw [hUpperRatio]
      _ ≤ (totalInj : ℝ) *
          Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) := by
            exact mul_le_mul_of_nonneg_left hUpperSub_le (le_of_lt htotal_pos)
      _ = Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) *
          (totalInj : ℝ) := by
            ring
  have hLowerSubsets :
      ((((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
        (fun S => ((S ∩ Kset).card : ℝ) < lowerThreshold)).card : ℝ) /
          (Nat.choose (m * m) n : ℝ))
        ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) := by
    have h :=
      HypergeometricCountingLowerTailBound (m * m) n q
        h_support hqN Kset hKset_card δ hδ_pos hδ_lt_one
    simpa [lowerThreshold, mu] using h
  have hLowerSub_le :
      (lowerSub.card : ℝ) / (chooseN : ℝ) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) := by
    have h_equiv :
        (lowerSub.card : ℝ) =
          (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if ((S ∩ Kset).card : ℝ) < lowerThreshold then (1 : ℝ) else 0) := by
      dsimp [lowerSub, Kset, lowerThreshold, mu]
      simpa using
        FinProductLowerTailCountEquiv m n K
          ((1 - δ) * ((n : ℝ) * ((q : ℝ) / (m * m : ℝ))))
    have h_sum_card :
        (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S =>
              if ((S ∩ Kset).card : ℝ) < lowerThreshold then (1 : ℝ) else 0) =
          (((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).filter
            (fun S => ((S ∩ Kset).card : ℝ) < lowerThreshold)).card : ℝ) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h_equiv, h_sum_card]
    simpa [chooseN] using hLowerSubsets
  have hLowerRatio :
      (lowerInj.card : ℝ) / (totalInj : ℝ) =
        (lowerSub.card : ℝ) / (chooseN : ℝ) := by
    rw [div_eq_div_iff htotal_pos.ne.symm hchoose_pos.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerUI
  have hLower :
      (lowerInj.card : ℝ) ≤
        Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) *
          (totalInj : ℝ) := by
    calc
      (lowerInj.card : ℝ)
          = (totalInj : ℝ) * ((lowerInj.card : ℝ) / (totalInj : ℝ)) := by
            rw [mul_div_cancel₀ _ htotal_pos.ne.symm]
      _ = (totalInj : ℝ) * ((lowerSub.card : ℝ) / (chooseN : ℝ)) := by
            rw [hLowerRatio]
      _ ≤ (totalInj : ℝ) *
          Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) := by
            exact mul_le_mul_of_nonneg_left hLowerSub_le (le_of_lt htotal_pos)
      _ = Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) *
          (totalInj : ℝ) := by
            ring
  have hbad_card :
      (badInj.card : ℝ) ≤ (lowerInj.card : ℝ) + (upperInj.card : ℝ) := by
    have hsubset : badInj ⊆ lowerInj ∪ upperInj := by
      intro phi hphi
      simp [badInj, lowerInj, upperInj, countHits, lowerThreshold, upperThreshold] at hphi ⊢
      exact hphi
    have hnat : badInj.card ≤ lowerInj.card + upperInj.card := by
      exact (Finset.card_le_card hsubset).trans (Finset.card_union_le lowerInj upperInj)
    exact_mod_cast hnat
  have hfinal :
      (badInj.card : ℝ) ≤
        (Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) +
          Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu))) *
          (totalInj : ℝ) := by
    calc
      (badInj.card : ℝ)
          ≤ (lowerInj.card : ℝ) + (upperInj.card : ℝ) := hbad_card
      _ ≤ Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) *
              (totalInj : ℝ) +
            Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu)) *
              (totalInj : ℝ) := by
            exact add_le_add hLower hUpper
      _ =
        (Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * mu) +
          Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * mu))) *
          (totalInj : ℝ) := by
            ring
  simpa [badInj, countHits, lowerThreshold, upperThreshold, totalInj, mu] using hfinal
