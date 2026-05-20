import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.HypergeometricCountingTailBound
import Tablet.UniformInjectionImage
import Tablet.FinProductTailCountEquiv
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail]

theorem FiberAndDegreeSameColorLiftedIntersectionFixedPairInjectionTail
    (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ))
    (h_ratio : (n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 * (m : ℝ))
    (G_R : SimpleGraph (Fin m))
    [DecidableRel G_R.Adj]
    (r s : Fin m)
    (hrs : r ≠ s)
    (hR : ((Finset.univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) :
    ((Finset.univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ((((Finset.univ : Finset (Fin n)).image ϕ) ∩
        ((Finset.univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)) ×ˢ
          (Finset.univ : Finset (Fin m)))).card : ℝ)
        > 100 * (Real.log (n : ℝ)) ^ 3)).card : ℝ)
      ≤ Real.exp (-2 * (Real.log (n : ℝ))^3) *
        (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
-- BODY
  have h_distinct : r ≠ s := hrs
  clear h_distinct
  let L := Real.log (n : ℝ)
  let K_base := univ.filter (fun t => G_R.Adj r t ∧ G_R.Adj s t)
  let K := K_base ×ˢ (univ : Finset (Fin m))
  let T := (100 : ℝ) * L ^ 3
  have hL_pos : 0 < L := by linarith
  have hT_pos : 0 < T := by
    dsimp [T]
    exact mul_pos (by norm_num) (pow_pos hL_pos 3)
  let N := m * m
  let m_mark := K.card
  let e_equiv := finProdFinEquiv (m := m) (n := m)
  let M := K.image e_equiv
  have h_M_card : M.card = m_mark := by
    exact card_image_of_injective _ e_equiv.injective
  have h_target_card : Fintype.card (Fin m × Fin m) = N := by
    simp [N]
  have hnN : n ≤ N := h_support
  have hmN : m_mark ≤ N := by
    have h := card_le_univ K
    simpa [m_mark, N] using h
  let P_prop (S : Finset (Fin m × Fin m)) : Prop := ((S ∩ K).card : ℝ) > T
  have h_Uniform_raw := UniformInjectionImage (univ : Finset (Fin n)) (card_fin n) P_prop
  let inj_filter :=
    univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ((((univ : Finset (Fin n)).image ϕ) ∩ K).card : ℝ) > T)
  let sub_filter :=
    univ.filter (fun S : Finset (Fin m × Fin m) => S.card = n ∧ ((S ∩ K).card : ℝ) > T)
  have h_Uniform_ℝ :
      (inj_filter.card : ℝ) * (Nat.choose (m * m) n : ℝ) =
        (sub_filter.card : ℝ) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
    have h1 :
        (univ.filter (fun ϕ : Fin n ↪ Fin m × Fin m => P_prop (image ϕ univ))).card =
          inj_filter.card := rfl
    have h2 :
        (univ.filter (fun S : Finset (Fin m × Fin m) => S.card = n ∧ P_prop S)).card =
          sub_filter.card := rfl
    rw [← h1, ← h2] at h_Uniform_raw
    norm_cast at h_Uniform_raw ⊢
  have h_Equiv :
      (sub_filter.card : ℝ) =
        (powersetCard n (univ : Finset (Fin (m * m)))).sum
          (fun S => if ((S ∩ M).card : ℝ) > T then (1 : ℝ) else 0) := by
    rw [← FinProductTailCountEquiv]
  have h_Sum_Card :
      (powersetCard n (univ : Finset (Fin N))).sum
          (fun S => if ((S ∩ M).card : ℝ) > T then (1 : ℝ) else 0) =
        ((powersetCard n (univ : Finset (Fin (m * m)))).filter
          (fun S => ((S ∩ M).card : ℝ) > T)).card := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    norm_cast
  let sub_filter_N :=
    (powersetCard n (univ : Finset (Fin (m * m)))).filter
      (fun S => ((S ∩ M).card : ℝ) ≥ T)
  have h_sub_le : (sub_filter.card : ℝ) ≤ (sub_filter_N.card : ℝ) := by
    rw [h_Equiv, h_Sum_Card]
    norm_cast
    apply Finset.card_le_card
    intro S hS
    rw [mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.le⟩
  let q := (m_mark : ℝ) / (N : ℝ)
  let mu := (n : ℝ) * q
  have h_Hyper :
      (sub_filter_N.card : ℝ) / (N.choose n : ℝ) ≤ (Real.exp 1 * mu / T) ^ T := by
    exact HypergeometricCountingTailBound N n m_mark hnN hmN M h_M_card T hT_pos
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    subst n
    norm_num [L] at hL_pos
  have h_n_pos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn_ne_zero
  have h_en_val : exp 1 ≤ (n : ℝ) := by
    have h1 := exp_le_exp.mpr h_log
    rwa [Real.exp_log h_n_pos] at h1
  have h_m_pos : (0 : ℝ) < m := by
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      have hzero : m * m = 0 := by simp [hm0]
      exact hn_ne_zero (Nat.eq_zero_of_le_zero (h_support.trans_eq hzero))
    exact_mod_cast Nat.pos_of_ne_zero hm_ne_zero
  have h_N_pos : (0 : ℝ) < N := by
    have hm_nat_pos : 0 < m := by exact_mod_cast h_m_pos
    exact_mod_cast Nat.mul_pos hm_nat_pos hm_nat_pos
  have h_mu_le : mu ≤ 2 * L ^ 3 := by
    have h_K_card_val : (m_mark : ℝ) = (K_base.card : ℝ) * (m : ℝ) := by
      simp [m_mark, K, card_product]
    have h_ratio_m : (n : ℝ) / (m : ℝ) ≤ 2 * L ^ 2 := by
      rw [div_le_iff₀ h_m_pos]
      simpa [L] using h_ratio
    have hK_le : (K_base.card : ℝ) ≤ L := by
      simpa [K_base, L] using hR
    calc
      mu = (K_base.card : ℝ) * ((n : ℝ) / (m : ℝ)) := by
        dsimp [mu, q, N]
        rw [h_K_card_val]
        field_simp [h_m_pos.ne.symm]
        norm_num [pow_two]
      _ ≤ L * (2 * L ^ 2) := by
        exact mul_le_mul hK_le h_ratio_m
          (div_nonneg (Nat.cast_nonneg n) h_m_pos.le) hL_pos.le
      _ = 2 * L ^ 3 := by ring
  have h_base_le : exp 1 * mu / T ≤ exp (-2) := by
    dsimp [T]
    have h1 : mu / L ^ 3 ≤ 2 := by
      rw [div_le_iff₀ (pow_pos hL_pos 3)]
      exact h_mu_le
    have h_rewrite :
        exp 1 * mu / (100 * L ^ 3) = exp 1 * (mu / L ^ 3) / 100 := by
      field_simp [hL_pos.ne']
    rw [h_rewrite]
    have h2 : exp 1 * (mu / L ^ 3) / 100 ≤ exp 1 * 2 / 100 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left h1 (exp_pos 1).le
      · norm_num
    apply h2.trans
    have h_exp50 : exp 1 / 50 ≤ exp (-2) := by
      rw [Real.exp_neg]
      rw [div_eq_mul_inv]
      rw [mul_inv_le_iff₀ (by norm_num : (0 : ℝ) < 50)]
      rw [le_inv_mul_iff₀ (exp_pos 2)]
      rw [mul_comm, ← exp_add]
      have h_log50 : exp 3 ≤ (50 : ℝ) := by
        calc
          exp 3 = (exp 1) ^ 3 := by
            rw [← Real.exp_nat_mul]
            ring_nf
          _ ≤ 3 ^ 3 := by
            exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_three.le 3
          _ ≤ (50 : ℝ) := by norm_num
      simpa [show (1 : ℝ) + 2 = 3 by ring] using h_log50
    simpa [show exp 1 * 2 / 100 = exp 1 / 50 by ring] using h_exp50
  have h_bound_T : (exp 1 * mu / T) ^ T ≤ (exp (-2)) ^ T := by
    by_cases hmu0 : mu = 0
    · rw [hmu0]
      simp only [mul_zero, zero_div]
      rw [zero_rpow hT_pos.ne.symm]
      exact (Real.rpow_pos_of_pos (exp_pos (-2)) T).le
    · have h_mu_nonneg : 0 ≤ mu := by
        dsimp [mu, q]
        exact mul_nonneg (Nat.cast_nonneg n) (div_nonneg (Nat.cast_nonneg m_mark) (Nat.cast_nonneg N))
      have h_base_pos : 0 < exp 1 * mu / T := by
        exact div_pos (mul_pos (exp_pos 1) (lt_of_le_of_ne h_mu_nonneg (Ne.symm hmu0))) hT_pos
      exact Real.rpow_le_rpow h_base_pos.le h_base_le hT_pos.le
  have h_choose_pos : (0 : ℝ) < N.choose n := by
    norm_cast
    exact Nat.choose_pos hnN
  have h_card_pos : (0 : ℝ) < Fintype.card (Fin n ↪ Fin m × Fin m) := by
    have : Nonempty (Fin n ↪ Fin m × Fin m) := by
      let f : Fin n ↪ Fin (m * m) :=
        ⟨fun i => Fin.castLE h_support i, fun _ _ h => Fin.castLE_injective h_support h⟩
      exact ⟨f.trans e_equiv.symm.toEmbedding⟩
    exact_mod_cast Fintype.card_pos
  have h_lhs :
      (inj_filter.card : ℝ) / (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) =
        (sub_filter.card : ℝ) / (N.choose n : ℝ) := by
    rw [div_eq_div_iff h_card_pos.ne.symm h_choose_pos.ne.symm]
    simpa [N] using h_Uniform_ℝ
  rw [show (inj_filter.card : ℝ) =
      (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) *
        ((inj_filter.card : ℝ) / (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)) by
        rw [mul_div_cancel₀ _ h_card_pos.ne.symm]]
  rw [h_lhs]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right
  · apply (div_le_div_of_nonneg_right h_sub_le h_choose_pos.le).trans
    apply h_Hyper.trans
    apply h_bound_T.trans
    calc
      (exp (-2)) ^ T = exp (-2 * T) := by
        rw [Real.rpow_def_of_pos (exp_pos (-2))]
        rw [Real.log_exp]
      _ ≤ exp (-2 * (Real.log (n : ℝ)) ^ 3) := by
        exact exp_le_exp.mpr (by
          dsimp [T, L]
          nlinarith [pow_nonneg hL_pos.le 3])
  · exact Nat.cast_nonneg _
