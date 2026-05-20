import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelVar
import Tablet.FinalPairsCardLeHalfSq
import Tablet.TwoBiteSmallCutoff
import Tablet.BiUnionOneChangeCardDifferenceBound
import Tablet.SmallClassFinalPairsContributionBound
import Mathlib.Tactic

-- [TABLET NODE: FixedSetProductModelLipschitz]

open scoped Classical

theorem FixedSetProductModelLipschitz {n : ℕ} (I : Finset (Fin n)) (ε : ℝ)
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (c_prod : ℝ) (hc_prod : c_prod = (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε))) :
    ∀ i v v', (∀ j, j ≠ i → v j = v' j) →
      |FixedSetProductModelVar I ε p_sub π v - FixedSetProductModelVar I ε p_sub π v'| ≤ c_prod := by
-- BODY
  intro i v v' hagree
  classical
  let omegaOf : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) →
      TwoBiteSample n m_sub p_sub := fun w =>
    (FixedSetFakeGraph (I.image (fun u => (π u).1)) (fun r => (w ⟨r.val, by omega⟩).1),
     FixedSetFakeGraph (I.image (fun u => (π u).2)) (fun b => (w ⟨b.val + m_sub, by omega⟩).2),
     π)
  let changed : TwoBiteBaseVertex m_sub :=
    if hi : i.val < m_sub then Sum.inl ⟨i.val, hi⟩
    else Sum.inr ⟨i.val - m_sub, by omega⟩
  let S : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) →
      Finset (TwoBiteBaseVertex m_sub) := fun w =>
    let P_R := I.image (TwoBiteRedProjection (omegaOf w))
    let P_B := I.image (TwoBiteBlueProjection (omegaOf w))
    let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
    (Finset.univ.filter (TwoBiteSmallClass (omegaOf w) ε I)) \ P_I
  let pred : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) →
      Fin n × Fin n → Prop := fun w e =>
    TwoBiteRedProjection (omegaOf w) e.1 ≠ TwoBiteRedProjection (omegaOf w) e.2 ∧
    TwoBiteBlueProjection (omegaOf w) e.1 ≠ TwoBiteBlueProjection (omegaOf w) e.2
  let F : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) →
      TwoBiteBaseVertex m_sub → Finset (Fin n × Fin n) := fun w x =>
    if x ∈ S w then
      @Finset.filter (Fin n × Fin n) (pred w)
        (fun e => Classical.propDecidable (pred w e))
        (TwoBiteFinalPairs (TwoBiteX (omegaOf w) I x))
    else ∅
  have hZset :
      ∀ w,
        (((S w).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX (omegaOf w) I x))).filter
            (pred w)) =
          Finset.univ.biUnion (F w) := by
    intro w
    apply Finset.ext
    intro e
    rw [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · intro he
      rcases he with ⟨⟨x, hxS, hePairs⟩, hePred⟩
      exact ⟨x, Finset.mem_univ x, by simp [F, hxS, hePairs, hePred]⟩
    · intro he
      rcases he with ⟨x, _hxU, heF⟩
      by_cases hxS : x ∈ S w
      · simp [F, hxS] at heF
        exact ⟨⟨x, hxS, heF.1⟩, heF.2⟩
      · simp [F, hxS] at heF
  have hZ :
      ∀ w, FixedSetProductModelVar I ε p_sub π w =
        ((Finset.univ.biUnion (F w)).card : ℝ) := by
    intro w
    dsimp [FixedSetProductModelVar, omegaOf, S, pred]
    exact congrArg (fun T : Finset (Fin n × Fin n) => (T.card : ℝ)) (hZset w)
  have hR_proj : ∀ w u, TwoBiteRedProjection (omegaOf w) u = (π u).1 := by
    intro w u
    rfl
  have hB_proj : ∀ w u, TwoBiteBlueProjection (omegaOf w) u = (π u).2 := by
    intro w u
    rfl
  have hX_eq :
      ∀ x, x ≠ changed → TwoBiteX (omegaOf v) I x = TwoBiteX (omegaOf v') I x := by
    intro x hxchg
    cases x with
    | inl r =>
        apply Finset.ext
        intro u
        simp only [TwoBiteX, TwoBiteLiftedNeighborhood, Finset.mem_filter, Finset.mem_univ,
          true_and]
        apply and_congr_right
        intro huI
        change (omegaOf v).1.Adj r (TwoBiteRedProjection (omegaOf v) u) ↔
          (omegaOf v').1.Adj r (TwoBiteRedProjection (omegaOf v') u)
        rw [hR_proj v u, hR_proj v' u]
        by_cases hrP : r ∈ I.image (fun u => (π u).1)
        · have hAdj_v_false : ¬ (omegaOf v).1.Adj r (π u).1 := by
            intro hAdj
            dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj] at hAdj
            rcases hAdj with h | h
            · exact h.2.1 (Finset.mem_image_of_mem (fun u => (π u).1) huI)
            · exact h.2.1 hrP
          have hAdj_v'_false : ¬ (omegaOf v').1.Adj r (π u).1 := by
            intro hAdj
            dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj] at hAdj
            rcases hAdj with h | h
            · exact h.2.1 (Finset.mem_image_of_mem (fun u => (π u).1) huI)
            · exact h.2.1 hrP
          exact ⟨fun h => False.elim (hAdj_v_false h),
            fun h => False.elim (hAdj_v'_false h)⟩
        · have hidx_ne : (⟨r.val, by omega⟩ : Fin (2 * m_sub)) ≠ i := by
            intro hidx
            apply hxchg
            dsimp [changed]
            have hlt : i.val < m_sub := by
              rw [← hidx]
              exact r.isLt
            rw [dif_pos hlt]
            apply congrArg Sum.inl
            apply Fin.ext
            change r.val = i.val
            exact congrArg (fun z : Fin (2 * m_sub) => z.val) hidx
          have hv_eq := hagree ⟨r.val, by omega⟩ hidx_ne
          dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj]
          simp [hrP, Finset.mem_image_of_mem (fun u => (π u).1) huI, hv_eq]
    | inr b =>
        apply Finset.ext
        intro u
        simp only [TwoBiteX, TwoBiteLiftedNeighborhood, Finset.mem_filter, Finset.mem_univ,
          true_and]
        apply and_congr_right
        intro huI
        change (omegaOf v).2.1.Adj b (TwoBiteBlueProjection (omegaOf v) u) ↔
          (omegaOf v').2.1.Adj b (TwoBiteBlueProjection (omegaOf v') u)
        rw [hB_proj v u, hB_proj v' u]
        by_cases hbP : b ∈ I.image (fun u => (π u).2)
        · have hAdj_v_false : ¬ (omegaOf v).2.1.Adj b (π u).2 := by
            intro hAdj
            dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj] at hAdj
            rcases hAdj with h | h
            · exact h.2.1 (Finset.mem_image_of_mem (fun u => (π u).2) huI)
            · exact h.2.1 hbP
          have hAdj_v'_false : ¬ (omegaOf v').2.1.Adj b (π u).2 := by
            intro hAdj
            dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj] at hAdj
            rcases hAdj with h | h
            · exact h.2.1 (Finset.mem_image_of_mem (fun u => (π u).2) huI)
            · exact h.2.1 hbP
          exact ⟨fun h => False.elim (hAdj_v_false h),
            fun h => False.elim (hAdj_v'_false h)⟩
        · have hidx_ne : (⟨b.val + m_sub, by omega⟩ : Fin (2 * m_sub)) ≠ i := by
            intro hidx
            apply hxchg
            dsimp [changed]
            have hnlt : ¬ i.val < m_sub := by
              have hi_val : i.val = b.val + m_sub := by
                exact congrArg Fin.val hidx.symm
              omega
            rw [dif_neg hnlt]
            apply congrArg Sum.inr
            apply Fin.ext
            change b.val = i.val - m_sub
            have hi_val : i.val = b.val + m_sub := by
              exact congrArg Fin.val hidx.symm
            omega
          have hv_eq := hagree ⟨b.val + m_sub, by omega⟩ hidx_ne
          dsimp [omegaOf, FixedSetFakeGraph, SimpleGraph.Adj]
          simp [hbP, Finset.mem_image_of_mem (fun u => (π u).2) huI, hv_eq]
  have hS_iff : ∀ x, x ≠ changed → (x ∈ S v ↔ x ∈ S v') := by
    intro x hxchg
    have hsmall :
        TwoBiteSmallClass (omegaOf v) ε I x ↔
          TwoBiteSmallClass (omegaOf v') ε I x := by
      dsimp [TwoBiteSmallClass]
      rw [hX_eq x hxchg]
    dsimp [S]
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [hsmall]
    simp [TwoBiteRedProjection, TwoBiteBlueProjection, TwoBiteEmbedding, omegaOf]
  have hpred_eq : pred v = pred v' := by
    funext e
    dsimp [pred]
    simp [TwoBiteRedProjection, TwoBiteBlueProjection, TwoBiteEmbedding, omegaOf]
  have hF_eq : ∀ x ∈ (Finset.univ : Finset (TwoBiteBaseVertex m_sub)).erase changed,
      F v x = F v' x := by
    intro x hx
    have hxne : x ≠ changed := (Finset.mem_erase.mp hx).1
    have hSx := hS_iff x hxne
    by_cases hxS : x ∈ S v
    · have hxS' : x ∈ S v' := hSx.mp hxS
      dsimp [F]
      rw [if_pos hxS, if_pos hxS', hX_eq x hxne, hpred_eq]
    · have hxS' : x ∉ S v' := by
        intro h
        exact hxS (hSx.mpr h)
      simp [F, hxS, hxS']
  have hc_nonneg : 0 ≤ c_prod := by
    rw [hc_prod]
    positivity
  have hF_bound :
      ∀ w, ((F w changed).card : ℝ) ≤ c_prod := by
    intro w
    by_cases hchg : changed ∈ S w
    · have hsmall : TwoBiteSmallClass (omegaOf w) ε I changed := by
        have hmem := (Finset.mem_sdiff.mp hchg).1
        exact (Finset.mem_filter.mp hmem).2
      simp [F, hchg]
      exact SmallClassFinalPairsContributionBound
        (omegaOf w) I ε changed c_prod hc_prod hsmall (pred w)
    · simp [F, hchg, hc_nonneg]
  have hdiff :=
    BiUnionOneChangeCardDifferenceBound
      (s := (Finset.univ : Finset (TwoBiteBaseVertex m_sub)))
      (A := F v) (B := F v') (k := changed) hF_eq
  have hmax :
      max (((F v changed).card : ℝ)) (((F v' changed).card : ℝ)) ≤ c_prod := by
    exact max_le (hF_bound v) (hF_bound v')
  rw [hZ v, hZ v']
  exact le_trans hdiff hmax
