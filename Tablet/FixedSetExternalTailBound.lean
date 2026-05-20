import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Tablet.BoundedDifferencesProduct
import Tablet.FixedSetProductModelIngredients
import Tablet.FixedSetTailExponentInequality
import Tablet.GnpGraphWeight
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteEventProbabilitySumOverEmbeddings

-- [TABLET NODE: FixedSetExternalTailBound]

theorem FixedSetExternalTailBound :
    ∀ {n m k : ℕ} {p : ℝ} (I : Finset (Fin n))
      (ε ε1 ε2 : ℝ) {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      I.card = k →
      let m_sub := TwoBiteNaturalReducedVertexCount n
      let p_sub := TwoBiteEdgeProbability (1 / 2 : ℝ) n
      let L := Real.log (n : ℝ)
      let K := (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ)
      let C := RealChooseTwo K
      let Z_I : TwoBiteSample n m_sub p_sub → ℝ := fun ω => by
        classical
        exact
          let P_R := I.image (TwoBiteRedProjection ω)
          let P_B := I.image (TwoBiteBlueProjection ω)
          let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
          let S_I_ext := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ P_I
          let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
          let Z_pairs := ext_pairs.filter (fun e =>
            TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧
            TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
          (Z_pairs.card : ℝ)
      let mu : TwoBiteSample n m_sub p_sub → ℝ := fun _ => C / (2 * L)
      let t : ℝ := C / Real.sqrt L
      TwoBiteEventProbability n m_sub p_sub
        (fun ω => Z_I ω ≥ mu ω + t)
        ≤ Real.exp (-(C ^ 2 / (L * (m_sub : ℝ) * (n : ℝ).rpow (8 * ε)))) := by
-- BODY
  intros n m k p I ε ε1 ε2 n0 h_hier hn0 hm hp hk hI m_sub p_sub L K C Z_I mu t

  -- 1. Expose the substituted parameters
  have hm_sub : m_sub = m := hm.symm
  have hp_sub : p_sub = p := hp.symm
  have ht : t = C / Real.sqrt L := rfl

  have hn_pos_nat : 0 < n := by
    by_contra! h
    have hn_zero : n = 0 := le_antisymm h (Nat.zero_le n)
    subst hn_zero
    have h_vals := h_hier 0 hn0
    rcases h_vals with ⟨_, _, _, _, _, _, hm_le_mReal, _⟩
    have mReal_pos : 0 < (0 : ℝ) / (Real.log (0 : ℝ)) ^ 2 := by linarith
    norm_num at mReal_pos

  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos_nat

  have hL_pos : 0 < L := by
    have h_vals := h_hier n hn0
    rcases h_vals with ⟨_, _, _, _, _, _, hm_le_mReal, _⟩
    have mReal_pos : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by linarith
    dsimp [L]
    by_contra! h
    have hn_le_one : (n : ℝ) ≤ 1 := by
      have h1 : Real.exp (Real.log (n : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h
      rw [Real.exp_log hn_pos_real, Real.exp_zero] at h1
      exact h1
    have h_n_eq_one : (n : ℝ) = 1 := by
      have : (1 : ℝ) ≤ n := by
        exact Nat.one_le_cast.mpr hn_pos_nat
      exact le_antisymm hn_le_one this
    rw [h_n_eq_one] at mReal_pos
    have : Real.log 1 = 0 := Real.log_one
    rw [this] at mReal_pos
    norm_num at mReal_pos

  -- 2. Set up the external-pair random variable
  let r_prod := 2 * m_sub
  let c_prod := (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε))

  have hc_prod_pos : 0 < c_prod := by
    dsimp [c_prod]
    have hpow_pos : 0 < ((n : ℝ) ^ (4 * ε)) := Real.rpow_pos_of_pos hn_pos_real _
    nlinarith

  have hC_nonneg : 0 ≤ C := by
    dsimp [C, K]
    let a := TwoBiteNaturalIndependenceScale (1 + ε) n
    have hChoose_nat_nonneg : 0 ≤ RealChooseTwo (a : ℝ) := by
      by_cases ha0 : a = 0
      · simp [ha0, RealChooseTwo]
      · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
        have ha_one : (1 : ℝ) ≤ (a : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt ha_pos)
        have ha_nonneg : 0 ≤ (a : ℝ) := by exact_mod_cast Nat.zero_le a
        unfold RealChooseTwo
        nlinarith
    simpa [a] using hChoose_nat_nonneg

  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hC_nonneg (Real.sqrt_nonneg L)

  have h_tail_ineq : -(2 * t ^ 2) / ((r_prod : ℝ) * c_prod ^ 2) 
    ≤ -(C ^ 2 / (L * (m_sub : ℝ) * ((n : ℝ) ^ (8 * ε)))) := by
    apply FixedSetTailExponentInequality (m := m_sub) (C := C) (L := L) (ε := ε)
      (r := r_prod) (c := c_prod) (t := t)
    · exact hL_pos
    · exact hn_pos_nat
    · dsimp [r_prod]; push_cast; rfl
    · exact rfl
    · exact ht

  -- 3. Connect the sample law to the product-coordinate model
  have hI_scale : I.card = TwoBiteNaturalIndependenceScale (1 + ε) n := by
    rw [hI, hk]

  have bdp_ingredients : ∀ π : Fin n ↪ (Fin m_sub × Fin m_sub),
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
      (q : α → ℝ) (Z_prod : (Fin r_prod → α) → ℝ),
      (∀ a, 0 ≤ q a) ∧
      (Finset.univ.sum q = 1) ∧
      0 < c_prod ∧
      0 ≤ t ∧
      (∀ i v v', (∀ j, j ≠ i → v j = v' j) → |Z_prod v - Z_prod v'| ≤ c_prod) ∧
      (Finset.univ.sum (fun v : Fin r_prod → α =>
          (Finset.univ.prod (fun i => q (v i))) * Z_prod v) ≤ C / (2 * L)) ∧
      TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ Z_I ω ≥ mu ω + t)
      ≤ (Finset.univ.filter (fun v : Fin r_prod → α =>
          Finset.univ.sum (fun v' : Fin r_prod → α => (Finset.univ.prod (fun i => q (v' i))) * Z_prod v') + t ≤ Z_prod v)).sum (fun v => Finset.univ.prod (fun i => q (v i))) * TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
    exact FixedSetProductModelIngredients I ε ε1 ε2 h_hier hn0 hI_scale

  have h_vals := h_hier n hn0
  have hp_nonneg : 0 ≤ p_sub := h_vals.2.1
  have hp_le_one : p_sub ≤ 1 := le_trans h_vals.2.2.1 (by norm_num)

  -- 4. Prove conditional law using BoundedDifferencesProduct
  have conditional_law : ∀ π : Fin n ↪ (Fin m_sub × Fin m_sub),
    TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ Z_I ω ≥ mu ω + t)
      ≤ Real.exp (-(2 * t ^ 2) / ((r_prod : ℝ) * c_prod ^ 2)) *
        TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
    intro π
    rcases bdp_ingredients π with ⟨α, _, _, q, Z_prod, hq_nonneg, hq_sum, hc_pos, ht_nonneg, hdiff, h_expect_le, h_prob_le⟩
    have bdp := BoundedDifferencesProduct r_prod q c_prod t Z_prod hq_nonneg hq_sum hc_pos ht_nonneg hdiff
    have P_nonneg : 0 ≤ TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
      unfold TwoBiteEventProbability
      apply Finset.sum_nonneg
      intro ω _
      exact TwoBiteSampleWeightNonnegative ω hp_nonneg hp_le_one
    have h_mul := mul_le_mul_of_nonneg_right bdp P_nonneg
    exact le_trans h_prob_le h_mul

  -- 5. Instantiate FixedSetTailExponentInequality
  have BDP_application : ∀ π : Fin n ↪ (Fin m_sub × Fin m_sub),
    TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ Z_I ω ≥ mu ω + t)
      ≤ Real.exp (-(C ^ 2 / (L * (m_sub : ℝ) * ((n : ℝ) ^ (8 * ε))))) *
        TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
    intro π
    have P_nonneg : 0 ≤ TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
      unfold TwoBiteEventProbability
      apply Finset.sum_nonneg
      intro ω _
      exact TwoBiteSampleWeightNonnegative ω hp_nonneg hp_le_one
    have h_exp : Real.exp (-(2 * t ^ 2) / ((r_prod : ℝ) * c_prod ^ 2)) ≤ Real.exp (-(C ^ 2 / (L * (m_sub : ℝ) * ((n : ℝ) ^ (8 * ε))))) := Real.exp_le_exp.mpr h_tail_ineq
    have h_mul : Real.exp (-(2 * t ^ 2) / ((r_prod : ℝ) * c_prod ^ 2)) * TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) ≤ Real.exp (-(C ^ 2 / (L * (m_sub : ℝ) * ((n : ℝ) ^ (8 * ε))))) * TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := mul_le_mul_of_nonneg_right h_exp P_nonneg
    exact le_trans (conditional_law π) h_mul

  -- 6. Sum over all embeddings
  apply TwoBiteEventProbabilitySumOverEmbeddings
  · exact BDP_application
  · exact (Real.exp_pos _).le
