import Tablet.FiberAndDegreeEvent
import Tablet.ClosedPairsBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteX
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff
import Tablet.TwoBiteLargeHugeVertices
import Tablet.LargeHugeVertexCountBound

-- [TABLET NODE: LargeClosedPairsBound]

theorem LargeClosedPairsBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      {ε ε1 ε2 : ℝ} {n0 : ℕ} (I : Finset (Fin n)),
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ)
        ε1 (I.card : ℝ) := by
-- BODY
  classical
  intro n m p ω ε ε1 ε2 n0 I hComparisons hn hI hFiber
  let L : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteLargeClass ω ε I x)
  let F : TwoBiteBaseVertex m → Finset (Fin n) := fun x => TwoBiteX ω I x
  let Cn : ℝ := 100 * (Real.log (n : ℝ)) ^ 3
  have hLargeHugeBound :
      ((TwoBiteLargeHugeVertices ω ε I).card : ℝ) <
        Real.rpow (n : ℝ) (1 / 4 : ℝ) :=
    LargeHugeVertexCountBound ω I ε ε1 ε2 hComparisons hn hI hFiber
  have hL_subset_largeHuge : L ⊆ TwoBiteLargeHugeVertices ω ε I := by
    intro x hx
    have hxLarge : TwoBiteLargeClass ω ε I x := by
      simpa [L] using hx
    simp [TwoBiteLargeHugeVertices, hxLarge]
  have hL_card_bound :
      (L.card : ℝ) < Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    exact lt_of_le_of_lt
      (by exact_mod_cast Finset.card_le_card hL_subset_largeHuge)
      hLargeHugeBound
  have hLargeClass_of_mem :
      ∀ x, x ∈ L → TwoBiteLargeClass ω ε I x := by
    intro x hx
    simpa [L] using hx
  have hPointLower :
      ∀ x, x ∈ L → TwoBiteLargeCutoff ε n < ((F x).card : ℝ) := by
    intro x hx
    exact (hLargeClass_of_mem x hx).1
  have hPointUpper :
      ∀ x, x ∈ L → ((F x).card : ℝ) ≤ TwoBiteHugeCutoff n := by
    intro x hx
    exact (hLargeClass_of_mem x hx).2
  have hF_subset_I : ∀ x : TwoBiteBaseVertex m, F x ⊆ I := by
    intro x v hv
    exact (by
      simpa [F, TwoBiteX] using hv :
        v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x).1
  dsimp [FiberAndDegreeEvent] at hFiber
  rcases hFiber with
    ⟨_hredFiber, _hblueFiber, _hredDegree, _hblueDegree, _hredPair,
      _hbluePair, _hliftedDegree, hredOverlap, hblueOverlap, hmixedOverlap,
      _hredOpposite, _hblueOpposite⟩
  have hF_inter_subset_lifted :
      ∀ x y : TwoBiteBaseVertex m,
        F x ∩ F y ⊆
          TwoBiteLiftedNeighborhood ω x ∩ TwoBiteLiftedNeighborhood ω y := by
    intro x y v hv
    have hvx : v ∈ F x := (Finset.mem_inter.mp hv).1
    have hvy : v ∈ F y := (Finset.mem_inter.mp hv).2
    have hvx' : v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x := by
      simpa [F, TwoBiteX] using hvx
    have hvy' : v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω y := by
      simpa [F, TwoBiteX] using hvy
    exact Finset.mem_inter.mpr ⟨hvx'.2, hvy'.2⟩
  have hPairwiseIntersection :
      ∀ x, x ∈ L → ∀ y, y ∈ L → x ≠ y →
        (((F x) ∩ (F y)).card : ℝ) ≤ Cn := by
    intro x hx y hy hxy
    have hcard_to_lifted :
        (((F x) ∩ (F y)).card : ℝ) ≤
          (((TwoBiteLiftedNeighborhood ω x) ∩
              (TwoBiteLiftedNeighborhood ω y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hF_inter_subset_lifted x y)
    cases x with
    | inl r =>
        cases y with
        | inl s =>
            have hrs : r ≠ s := by
              intro hrs
              exact hxy (by simp [hrs])
            exact le_trans hcard_to_lifted (by simpa [Cn] using hredOverlap r s hrs)
        | inr b =>
            exact le_trans hcard_to_lifted (by simpa [Cn] using hmixedOverlap r b)
    | inr b =>
        cases y with
        | inl r =>
            have hmixed :
                (((TwoBiteLiftedNeighborhood ω (Sum.inr b)) ∩
                    (TwoBiteLiftedNeighborhood ω (Sum.inl r))).card : ℝ) ≤ Cn := by
              simpa [Cn, Finset.inter_comm] using hmixedOverlap r b
            exact le_trans hcard_to_lifted hmixed
        | inr c =>
            have hbc : b ≠ c := by
              intro hbc
              exact hxy (by simp [hbc])
            exact le_trans hcard_to_lifted (by simpa [Cn] using hblueOverlap b c hbc)
  have hFiniteUnionLowerBound :
      ∀ B : Finset (TwoBiteBaseVertex m),
        (∀ x, x ∈ B → ∀ y, y ∈ B → x ≠ y →
          (((F x ∩ F y).card : ℝ) ≤ Cn)) →
        (B.sum (fun x => ((F x).card : ℝ)) -
            RealChooseTwo (B.card : ℝ) * Cn
          ≤ ((B.biUnion F).card : ℝ)) := by
    intro B
    refine Finset.induction_on B ?base ?step
    · intro _hoverlap
      simp [RealChooseTwo]
    · intro a s ha ih hoverlap
      have hoverlap_s :
          ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
            (((F x ∩ F y).card : ℝ) ≤ Cn) := by
        intro x hx y hy hxy
        exact hoverlap x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have ih' :
          s.sum (fun x => ((F x).card : ℝ)) -
              RealChooseTwo (s.card : ℝ) * Cn
            ≤ ((s.biUnion F).card : ℝ) :=
        ih hoverlap_s
      let U : Finset (Fin n) := s.biUnion F
      have hbi_insert : (insert a s).biUnion F = F a ∪ U := by
        ext v
        simp [U]
      have hcard_union_real :
          (((F a ∪ U).card : ℝ) + ((F a ∩ U).card : ℝ) =
            ((F a).card : ℝ) + (U.card : ℝ)) := by
        exact_mod_cast (Finset.card_union_add_card_inter (F a) U)
      have hcard_union_eq :
          (((F a ∪ U).card : ℝ) =
            ((F a).card : ℝ) + (U.card : ℝ) -
              ((F a ∩ U).card : ℝ)) := by
        linarith only [hcard_union_real]
      have hinter_subset :
          F a ∩ U ⊆ s.biUnion (fun y => F a ∩ F y) := by
        intro v hv
        rw [Finset.mem_inter] at hv
        rcases hv with ⟨hva, hvU⟩
        have hvU' : v ∈ s.biUnion F := by
          simpa [U] using hvU
        rw [Finset.mem_biUnion] at hvU'
        rcases hvU' with ⟨y, hy, hvy⟩
        rw [Finset.mem_biUnion]
        exact ⟨y, hy, by simp [hva, hvy]⟩
      have hinter_card_le :
          (((F a ∩ U).card : ℝ) ≤
            ((s.biUnion (fun y => F a ∩ F y)).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hinter_subset
      have hbi_card_le :
          (((s.biUnion (fun y => F a ∩ F y)).card : ℝ) ≤
            s.sum (fun y => ((F a ∩ F y).card : ℝ))) := by
        exact_mod_cast (Finset.card_biUnion_le
          (s := s) (t := fun y => F a ∩ F y))
      have hinter_sum_le :
          s.sum (fun y => ((F a ∩ F y).card : ℝ)) ≤ s.sum (fun _ => Cn) := by
        refine Finset.sum_le_sum ?_
        intro y hy
        have hay : a ≠ y := by
          intro hya
          exact ha (by simpa [hya] using hy)
        exact hoverlap a (Finset.mem_insert_self a s) y (Finset.mem_insert_of_mem hy) hay
      have hsum_const :
          s.sum (fun _ : TwoBiteBaseVertex m => Cn) = (s.card : ℝ) * Cn := by
        simp [nsmul_eq_mul]
      have hinter_le : (((F a ∩ U).card : ℝ) ≤ (s.card : ℝ) * Cn) := by
        calc
          ((F a ∩ U).card : ℝ)
              ≤ ((s.biUnion (fun y => F a ∩ F y)).card : ℝ) := hinter_card_le
          _ ≤ s.sum (fun y => ((F a ∩ F y).card : ℝ)) := hbi_card_le
          _ ≤ s.sum (fun _ : TwoBiteBaseVertex m => Cn) := hinter_sum_le
          _ = (s.card : ℝ) * Cn := hsum_const
      have hchoose_insert :
          RealChooseTwo ((insert a s).card : ℝ) =
            RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
        simp [ha, RealChooseTwo]
        ring
      have hsum_insert :
          (insert a s).sum (fun x => ((F x).card : ℝ)) =
            ((F a).card : ℝ) + s.sum (fun x => ((F x).card : ℝ)) := by
        simp [ha]
      rw [hbi_insert]
      rw [hsum_insert, hchoose_insert]
      have hmul :
          (RealChooseTwo (s.card : ℝ) + (s.card : ℝ)) * Cn =
            RealChooseTwo (s.card : ℝ) * Cn + (s.card : ℝ) * Cn := by
        ring
      rw [hmul]
      linarith only [ih', hcard_union_eq, hinter_le]
  let S : ℝ := L.sum (fun x => ((F x).card : ℝ))
  let E : ℝ := RealChooseTwo (L.card : ℝ) * Cn
  have hUnion_subset_I : L.biUnion F ⊆ I := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨x, _hx, hvx⟩
    exact hF_subset_I x hvx
  have hUnion_card_le :
      (((L.biUnion F).card : ℝ) ≤ (I.card : ℝ)) := by
    exact_mod_cast Finset.card_le_card hUnion_subset_I
  have hUnion_lower :
      L.sum (fun x => ((F x).card : ℝ)) -
          RealChooseTwo (L.card : ℝ) * Cn
        ≤ ((L.biUnion F).card : ℝ) :=
    hFiniteUnionLowerBound L hPairwiseIntersection
  have hI_ge_S_sub_E : S - E ≤ (I.card : ℝ) := by
    calc
      S - E =
          L.sum (fun x => ((F x).card : ℝ)) -
            RealChooseTwo (L.card : ℝ) * Cn := by
        rfl
      _ ≤ ((L.biUnion F).card : ℝ) := hUnion_lower
      _ ≤ (I.card : ℝ) := hUnion_card_le
  have hCompn := hComparisons n hn
  dsimp [ParameterHierarchyEventualComparisons] at hCompn
  rcases hCompn with
    ⟨_hm_pos, _hp_nonneg, _hp_le, _hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, hT1K,
      _h16, _h17, _h18, _h19, _h20, hEps2Small,
      hEps2Nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
      _hLargeHugeCutoff, _hStageUpper, hOneUnit, _hGap,
      _h33, _h34, _h35, _h36⟩
  let r : ℝ := Real.rpow (n : ℝ) (1 / 4 : ℝ)
  have hn_pos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
  have hn_one_nat : 1 ≤ n := Nat.succ_le_iff.mpr hn_pos_nat
  have hn_one_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one_real
  have hCn_nonneg : 0 ≤ Cn := by
    dsimp [Cn]
    positivity
  have hL_minus_one_le : (L.card : ℝ) - 1 ≤ r + (1 / 2 : ℝ) := by
    dsimp [r] at *
    linarith only [hL_card_bound]
  have hOneUnit' : Cn * (r + (1 / 2 : ℝ)) ≤ TwoBiteLargeCutoff ε n := by
    calc
      Cn * (r + (1 / 2 : ℝ))
          = 100 * (r + (1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by
            ring
      _ ≤ TwoBiteLargeCutoff ε n := by
        simpa [r, Cn] using hOneUnit
  have hCutoff_from_card :
      ((L.card : ℝ) - 1) * Cn ≤ TwoBiteLargeCutoff ε n := by
    have hmul :
        ((L.card : ℝ) - 1) * Cn ≤ (r + (1 / 2 : ℝ)) * Cn :=
      mul_le_mul_of_nonneg_right hL_minus_one_le hCn_nonneg
    calc
      ((L.card : ℝ) - 1) * Cn ≤ (r + (1 / 2 : ℝ)) * Cn := hmul
      _ = Cn * (r + (1 / 2 : ℝ)) := by ring
      _ ≤ TwoBiteLargeCutoff ε n := hOneUnit'
  have hTermLower :
      ∀ x, x ∈ L → ((L.card : ℝ) - 1) * Cn ≤ ((F x).card : ℝ) := by
    intro x hx
    exact le_trans hCutoff_from_card (le_of_lt (hPointLower x hx))
  have hSum_const :
      L.sum (fun _ : TwoBiteBaseVertex m => ((L.card : ℝ) - 1) * Cn) =
        (L.card : ℝ) * (((L.card : ℝ) - 1) * Cn) := by
    simp [nsmul_eq_mul]
  have hConstSum_le_S :
      (L.card : ℝ) * (((L.card : ℝ) - 1) * Cn) ≤ S := by
    calc
      (L.card : ℝ) * (((L.card : ℝ) - 1) * Cn) =
          L.sum (fun _ : TwoBiteBaseVertex m => ((L.card : ℝ) - 1) * Cn) :=
        hSum_const.symm
      _ ≤ L.sum (fun x => ((F x).card : ℝ)) := by
        exact Finset.sum_le_sum hTermLower
      _ = S := by
        rfl
  have hTwoE_le_S : 2 * E ≤ S := by
    calc
      2 * E = (L.card : ℝ) * (((L.card : ℝ) - 1) * Cn) := by
        dsimp [E]
        simp [RealChooseTwo]
        ring
      _ ≤ S := hConstSum_le_S
  have hS_le_twoI : S ≤ 2 * (I.card : ℝ) := by
    linarith only [hI_ge_S_sub_E, hTwoE_le_S]
  have hFinalPairs_card_bound :
      ∀ X : Finset (Fin n),
        ((TwoBiteFinalPairs X).card : ℝ) ≤ RealChooseTwo (X.card : ℝ) := by
    intro X
    refine Finset.induction_on X ?pair_base ?pair_step
    · simp [TwoBiteFinalPairs, TwoBitePairsInSet, RealChooseTwo]
    · intro a s ha ih
      let newPairs : Finset (Fin n × Fin n) :=
        (s.filter (fun y => a.val < y.val ∨ y.val < a.val)).image
          (fun y => if a.val < y.val then (a, y) else (y, a))
      have hinsert_subset :
          TwoBiteFinalPairs (insert a s) ⊆ TwoBiteFinalPairs s ∪ newPairs := by
        intro e he
        rcases e with ⟨u, v⟩
        dsimp [TwoBiteFinalPairs, TwoBitePairsInSet] at he ⊢
        simp only [Finset.mem_filter, Finset.mem_product] at he
        rcases he with ⟨⟨hu, hv⟩, huv⟩
        simp only [Finset.mem_union]
        rw [Finset.mem_insert] at hu hv
        rcases hu with rfl | hu_s
        · rcases hv with rfl | hv_s
          · exact False.elim ((Nat.lt_irrefl _) huv)
          · right
            dsimp [newPairs]
            rw [Finset.mem_image]
            refine ⟨v, ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨hv_s, Or.inl huv⟩
            · simp [huv]
        · rcases hv with rfl | hv_s
          · right
            dsimp [newPairs]
            rw [Finset.mem_image]
            refine ⟨u, ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨hu_s, Or.inr huv⟩
            · have hnot : ¬ v.val < u.val := fun hvu => (Nat.lt_asymm hvu) huv
              simp [hnot]
          · left
            dsimp [TwoBiteFinalPairs, TwoBitePairsInSet]
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hu_s, hv_s⟩, huv⟩
      have hnew_card_le :
          newPairs.card ≤ s.card := by
        have himage :
            newPairs.card ≤
              (s.filter (fun y => a.val < y.val ∨ y.val < a.val)).card := by
          dsimp [newPairs]
          exact Finset.card_image_le
        exact le_trans himage (Finset.card_le_card (Finset.filter_subset _ _))
      have hcard_step_nat :
          (TwoBiteFinalPairs (insert a s)).card ≤
            (TwoBiteFinalPairs s).card + s.card := by
        exact le_trans (Finset.card_le_card hinsert_subset)
          (le_trans (Finset.card_union_le (TwoBiteFinalPairs s) newPairs)
            (Nat.add_le_add_left hnew_card_le (TwoBiteFinalPairs s).card))
      have hcard_step_real :
          ((TwoBiteFinalPairs (insert a s)).card : ℝ) ≤
            ((TwoBiteFinalPairs s).card : ℝ) + (s.card : ℝ) := by
        exact_mod_cast hcard_step_nat
      have hchoose_insert :
          RealChooseTwo ((insert a s).card : ℝ) =
            RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
        simp [ha, RealChooseTwo]
        ring
      calc
        ((TwoBiteFinalPairs (insert a s)).card : ℝ)
            ≤ ((TwoBiteFinalPairs s).card : ℝ) + (s.card : ℝ) := hcard_step_real
        _ ≤ RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
          linarith only [ih]
        _ = RealChooseTwo ((insert a s).card : ℝ) := hchoose_insert.symm
  have hClosed_eq :
      TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I) =
        L.biUnion (fun x => TwoBiteFinalPairs (F x)) := by
    rfl
  have hClosed_card_le_sum :
      (((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) ≤
        L.sum (fun x => ((TwoBiteFinalPairs (F x)).card : ℝ))) := by
    rw [hClosed_eq]
    exact_mod_cast (Finset.card_biUnion_le
      (s := L) (t := fun x => TwoBiteFinalPairs (F x)))
  have hPairSum_le_weighted :
      L.sum (fun x => ((TwoBiteFinalPairs (F x)).card : ℝ)) ≤
        L.sum (fun x =>
          (1 / 2 : ℝ) * TwoBiteHugeCutoff n * ((F x).card : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    set c : ℝ := ((F x).card : ℝ) with hc_def
    have hc_nonneg : 0 ≤ c := by
      rw [hc_def]
      exact_mod_cast Nat.zero_le (F x).card
    have hc_le_t : c ≤ TwoBiteHugeCutoff n := by
      rw [hc_def]
      exact hPointUpper x hx
    have hchoose_le_half_sq : RealChooseTwo c ≤ (1 / 2 : ℝ) * c ^ 2 := by
      have hhalf_c_nonneg : 0 ≤ (1 / 2 : ℝ) * c := by
        exact mul_nonneg (by norm_num) hc_nonneg
      calc
        RealChooseTwo c = (1 / 2 : ℝ) * c ^ 2 - (1 / 2 : ℝ) * c := by
          dsimp [RealChooseTwo]
          ring
        _ ≤ (1 / 2 : ℝ) * c ^ 2 := by
          linarith only [hhalf_c_nonneg]
    have hsq_le_weighted :
        (1 / 2 : ℝ) * c ^ 2 ≤
          (1 / 2 : ℝ) * TwoBiteHugeCutoff n * c := by
      have hmul : c * c ≤ TwoBiteHugeCutoff n * c :=
        mul_le_mul_of_nonneg_right hc_le_t hc_nonneg
      calc
        (1 / 2 : ℝ) * c ^ 2 = (1 / 2 : ℝ) * (c * c) := by
          ring
        _ ≤ (1 / 2 : ℝ) * (TwoBiteHugeCutoff n * c) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = (1 / 2 : ℝ) * TwoBiteHugeCutoff n * c := by
          ring
    calc
      ((TwoBiteFinalPairs (F x)).card : ℝ)
          ≤ RealChooseTwo c := by
        rw [hc_def]
        exact hFinalPairs_card_bound (F x)
      _ ≤ (1 / 2 : ℝ) * c ^ 2 := hchoose_le_half_sq
      _ ≤ (1 / 2 : ℝ) * TwoBiteHugeCutoff n * c := hsq_le_weighted
      _ = (1 / 2 : ℝ) * TwoBiteHugeCutoff n * ((F x).card : ℝ) := by
        rw [hc_def]
  have hWeighted_sum_eq :
      L.sum (fun x =>
          (1 / 2 : ℝ) * TwoBiteHugeCutoff n * ((F x).card : ℝ)) =
        (1 / 2 : ℝ) * TwoBiteHugeCutoff n * S := by
    dsimp [S]
    simpa [mul_assoc] using
      (Finset.mul_sum L (fun x => ((F x).card : ℝ))
        ((1 / 2 : ℝ) * TwoBiteHugeCutoff n)).symm
  have hClosed_le_weighted :
      (((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) ≤
        (1 / 2 : ℝ) * TwoBiteHugeCutoff n * S) := by
    exact le_trans hClosed_card_le_sum
      (le_trans hPairSum_le_weighted (le_of_eq hWeighted_sum_eq))
  have hI_real :
      (I.card : ℝ) =
        (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) := by
    exact_mod_cast hI
  have hT1K_I :
      TwoBiteHugeCutoff n * (I.card : ℝ) ≤ ε1 * (I.card : ℝ) ^ 2 := by
    rw [hI_real]
    simpa [TwoBiteHugeCutoff] using hT1K
  have hε1_nonneg : 0 ≤ ε1 := by
    have h3eps_nonneg : 0 ≤ 3 * ε2 :=
      mul_nonneg (by norm_num) hEps2Nonneg
    have hdiv_nonneg : 0 ≤ ε1 / 10 :=
      le_trans h3eps_nonneg hEps2Small
    have hmul : 0 ≤ 10 * (ε1 / 10) :=
      mul_nonneg (by norm_num) hdiv_nonneg
    convert hmul using 1
    ring
  dsimp [ClosedPairsBound]
  by_cases hL_nonempty : L.Nonempty
  · rcases hL_nonempty with ⟨x, hx⟩
    have hHuge_nonneg : 0 ≤ TwoBiteHugeCutoff n := by
      have hx_nonneg : 0 ≤ ((F x).card : ℝ) := by exact_mod_cast Nat.zero_le (F x).card
      exact le_trans hx_nonneg (hPointUpper x hx)
    have hcoef_nonneg : 0 ≤ (1 / 2 : ℝ) * TwoBiteHugeCutoff n := by
      exact mul_nonneg (by norm_num) hHuge_nonneg
    have hweighted_le :
        (1 / 2 : ℝ) * TwoBiteHugeCutoff n * S ≤
          TwoBiteHugeCutoff n * (I.card : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hS_le_twoI hcoef_nonneg
      calc
        (1 / 2 : ℝ) * TwoBiteHugeCutoff n * S
            ≤ (1 / 2 : ℝ) * TwoBiteHugeCutoff n * (2 * (I.card : ℝ)) := by
          simpa [mul_assoc] using hmul
        _ = TwoBiteHugeCutoff n * (I.card : ℝ) := by
          ring
    exact le_trans hClosed_le_weighted (le_trans hweighted_le hT1K_I)
  · have hL_empty : L = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hL_nonempty ⟨x, hx⟩)
      · intro hx
        simp at hx
    have hClosed_empty :
        TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I) = ∅ := by
      rw [hClosed_eq, hL_empty]
      simp
    have hgoal_nonneg : 0 ≤ ε1 * (I.card : ℝ) ^ 2 :=
      mul_nonneg hε1_nonneg (sq_nonneg (I.card : ℝ))
    simpa [hClosed_empty] using hgoal_nonneg
