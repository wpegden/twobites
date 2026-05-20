import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.FiberAndDegreeMixedLiftedIntersectionHypergeometricBound
import Tablet.UniformInjectionImage
import Tablet.FinProductTailCountEquiv
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionFixedPairInjectionTail]

theorem FiberAndDegreeMixedLiftedIntersectionFixedPairInjectionTail
    (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ))
    (G_R G_B : SimpleGraph (Fin m))
    [DecidableRel G_R.Adj] [DecidableRel G_B.Adj]
    (r b : Fin m)
    (hR : ((Finset.univ.filter (G_R.Adj r)).card : ℝ) ≤ 2 * p * (m : ℝ))
    (hB : ((Finset.univ.filter (G_B.Adj b)).card : ℝ) ≤ 2 * p * (m : ℝ)) :
    ((Finset.univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
        ((Finset.univ.filter (G_R.Adj r)) ×ˢ
          (Finset.univ.filter (G_B.Adj b)))).card : ℝ)
        > 100 * (Real.log (n : ℝ)) ^ 3)).card : ℝ)
      ≤ Real.exp (-2 * (Real.log (n : ℝ))^3) *
        (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
-- BODY
  classical
  let L : ℝ := Real.log (n : ℝ)
  let T : ℝ := 100 * L ^ 3
  let K : Finset (Fin m × Fin m) :=
    (Finset.univ.filter (G_R.Adj r)) ×ˢ (Finset.univ.filter (G_B.Adj b))
  let badInj : ℕ :=
    (Finset.univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ((((Finset.univ : Finset (Fin n)).image ϕ) ∩ K).card : ℝ) > T)).card
  let badSub : ℕ :=
    (Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = n ∧ ((S ∩ K).card : ℝ) > T)).card
  let totalInj : ℕ := Fintype.card (Fin n ↪ Fin m × Fin m)
  let chooseN : ℕ := Nat.choose (m * m) n
  have hL_ge : 1 ≤ L := by simpa [L] using h_log
  have hL_nonneg : 0 ≤ L := by linarith
  have hT_pos : 0 < T := by
    dsimp [T]
    positivity
  have hn_ne_zero : n ≠ 0 := by
    intro hn
    subst n
    norm_num [L] at h_log
  have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hm_pos_nat : 0 < m * m := lt_of_lt_of_le hn_pos_nat h_support
  have hm_pos : 0 < (m * m : ℝ) := by exact_mod_cast hm_pos_nat
  have hchoose_pos_nat : 0 < chooseN := by
    dsimp [chooseN]
    exact Nat.choose_pos h_support
  have hchoose_pos : 0 < (chooseN : ℝ) := by exact_mod_cast hchoose_pos_nat
  have hUI_nat : badInj * chooseN = badSub * totalInj := by
    dsimp [badInj, chooseN, badSub, totalInj, K, T]
    simpa [L] using
      (UniformInjectionImage (n := n) (m := m) (k := n)
        (Finset.univ : Finset (Fin n)) (by simp)
        (fun S : Finset (Fin m × Fin m) =>
          ((S ∩ ((Finset.univ.filter (G_R.Adj r)) ×ˢ
            (Finset.univ.filter (G_B.Adj b)))).card : ℝ) >
              100 * (Real.log (n : ℝ)) ^ 3))
  have hUI : (badInj : ℝ) * (chooseN : ℝ) = (badSub : ℝ) * (totalInj : ℝ) := by
    exact_mod_cast hUI_nat
  let e : (Fin m × Fin m) ≃ Fin (m * m) := finProdFinEquiv (m := m) (n := m)
  let Kset : Finset (Fin (m * m)) := K.image e
  have hKset_card : Kset.card = K.card := by
    dsimp [Kset]
    rw [Finset.card_image_of_injective _ e.injective]
  have hK_le_N : Kset.card ≤ m * m := by
    rw [hKset_card]
    exact K.card_le_univ.trans_eq (by simp)
  have hK_card_real :
      (K.card : ℝ) ≤ 4 * p ^ 2 * (m : ℝ) ^ 2 := by
    have hcardK : K.card =
        (Finset.univ.filter (G_R.Adj r)).card *
          (Finset.univ.filter (G_B.Adj b)).card := by
      dsimp [K]
      rw [Finset.card_product]
    have hR_nonneg : 0 ≤ ((Finset.univ.filter (G_R.Adj r)).card : ℝ) := by positivity
    have hB_nonneg : 0 ≤ ((Finset.univ.filter (G_B.Adj b)).card : ℝ) := by positivity
    have hpmm_nonneg : 0 ≤ 2 * p * (m : ℝ) := by
      linarith
    have hmul := mul_le_mul hR hB hB_nonneg hpmm_nonneg
    rw [hcardK]
    norm_num at hmul ⊢
    nlinarith
  have hp_sq_n_le : 4 * p ^ 2 * (n : ℝ) ≤ L := by
    rw [hp, TwoBiteEdgeProbability]
    have hdiv_nonneg : 0 ≤ L / (n : ℝ) := div_nonneg hL_nonneg hn_pos.le
    have hsqrt_sq : (Real.sqrt (L / (n : ℝ))) ^ 2 = L / (n : ℝ) := by
      rw [Real.sq_sqrt hdiv_nonneg]
    rw [show 4 * ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) ^ 2 * (n : ℝ) =
        (L / (n : ℝ)) * (n : ℝ) by
      rw [mul_pow, hsqrt_sq]
      ring]
    field_simp [ne_of_gt hn_pos]
    norm_num
  have hmean_le : (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ)) ≤ L := by
    have hK_real : (Kset.card : ℝ) ≤ 4 * p ^ 2 * (m : ℝ) ^ 2 := by
      rw [hKset_card]
      exact hK_card_real
    have hden_eq : (m * m : ℝ) = (m : ℝ) ^ 2 := by norm_num [pow_two]
    have hden_pos : 0 < (m : ℝ) ^ 2 := by
      rw [← hden_eq]
      exact hm_pos
    have hdiv : (Kset.card : ℝ) / (m * m : ℝ) ≤ 4 * p ^ 2 := by
      rw [hden_eq]
      exact (div_le_iff₀ hden_pos).mpr (by
        nlinarith)
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hdiv hn_nonneg
    have this' :
        (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ)) ≤
          4 * p ^ 2 * (n : ℝ) := by
      calc
        (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ))
            ≤ (n : ℝ) * (4 * p ^ 2) := this
        _ = 4 * p ^ 2 * (n : ℝ) := by ring
    exact le_trans this' hp_sq_n_le
  have h_exp_arg :
      (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ)) * (Real.exp 1 - 1) - 1 * T
        ≤ -2 * L ^ 3 := by
    have hexp_le : Real.exp 1 - 1 ≤ (2 : ℝ) := by
      linarith [Real.exp_one_lt_three]
    have hexp_sub_nonneg : 0 ≤ Real.exp 1 - 1 := by
      have hone : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have hmean_nonneg : 0 ≤ (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ)) := by
      positivity
    have hfirst : (n : ℝ) * ((Kset.card : ℝ) / (m * m : ℝ)) * (Real.exp 1 - 1) ≤ L * 2 := by
      exact mul_le_mul hmean_le hexp_le hexp_sub_nonneg hL_nonneg
    have hpoly : L * 2 - T ≤ -2 * L ^ 3 := by
      dsimp [T]
      nlinarith [hL_ge, sq_nonneg L, sq_nonneg (L - 1)]
    linarith
  have hHyper :=
    FiberAndDegreeMixedLiftedIntersectionHypergeometricBound
      (m * m) n Kset.card Kset T 1
      hn_pos_nat h_support hK_le_N rfl hT_pos (by norm_num)
  have hSubsets_le :
      ((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
        (fun S => if ((S ∩ Kset).card : ℝ) > T then (1 : ℝ) else 0))
        ≤ Real.exp (-2 * L ^ 3) * (chooseN : ℝ) := by
    have hGTleGE :
        ((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
          (fun S => if ((S ∩ Kset).card : ℝ) > T then (1 : ℝ) else 0))
          ≤
        ((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
          (fun S => if ((S ∩ Kset).card : ℝ) ≥ T then (1 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro S _
      by_cases h : ((S ∩ Kset).card : ℝ) > T
      · simp [h, le_of_lt h]
      · by_cases hge : ((S ∩ Kset).card : ℝ) ≥ T <;> simp [h, hge]
    have hHyper' :
        (chooseN : ℝ)⁻¹ *
          ((Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
            (fun S => if ((S ∩ Kset).card : ℝ) ≥ T then (1 : ℝ) else 0))
        ≤ Real.exp (-2 * L ^ 3) := by
      dsimp [chooseN] at hHyper ⊢
      exact le_trans hHyper (Real.exp_le_exp.mpr (by
        simpa [Nat.cast_mul] using h_exp_arg))
    have hmul := mul_le_mul_of_nonneg_right hHyper' (show 0 ≤ (chooseN : ℝ) by positivity)
    rw [← div_eq_inv_mul] at hmul
    rw [div_mul_cancel₀ _ (ne_of_gt hchoose_pos)] at hmul
    exact le_trans hGTleGE hmul
  have hSub_bad :
      (badSub : ℝ) ≤ Real.exp (-2 * L ^ 3) * (chooseN : ℝ) := by
    have h_equiv :
        (badSub : ℝ) =
        (Finset.powersetCard n (Finset.univ : Finset (Fin (m * m)))).sum
          (fun S => if ((S ∩ Kset).card : ℝ) > T then (1 : ℝ) else 0) := by
      dsimp [badSub, Kset, K, T]
      simpa [L] using
        FinProductTailCountEquiv m n
          ((Finset.univ.filter (G_R.Adj r)) ×ˢ
            (Finset.univ.filter (G_B.Adj b)))
          (100 * (Real.log (n : ℝ)) ^ 3)
    rw [h_equiv]
    exact hSubsets_le
  have hfinal :
      (badInj : ℝ) ≤ Real.exp (-2 * L ^ 3) * (totalInj : ℝ) := by
    have htotal_nonneg : 0 ≤ (totalInj : ℝ) := by positivity
    calc
      (badInj : ℝ)
          = ((badInj : ℝ) * (chooseN : ℝ)) / (chooseN : ℝ) := by
            field_simp [ne_of_gt hchoose_pos]
      _ = ((badSub : ℝ) * (totalInj : ℝ)) / (chooseN : ℝ) := by rw [hUI]
      _ ≤ (Real.exp (-2 * L ^ 3) * (chooseN : ℝ) * (totalInj : ℝ)) / (chooseN : ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right hSub_bad htotal_nonneg
            · exact le_of_lt hchoose_pos
      _ = Real.exp (-2 * L ^ 3) * (totalInj : ℝ) := by
            field_simp [ne_of_gt hchoose_pos]
  dsimp [badInj, totalInj, T, L, K] at hfinal
  simpa using hfinal
