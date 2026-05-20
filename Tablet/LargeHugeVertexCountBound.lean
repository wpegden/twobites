import Tablet.FiberAndDegreeEvent
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteLargeHugeVertices
import Tablet.TwoBiteX
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff
import Tablet.RealChooseTwo

-- [TABLET NODE: LargeHugeVertexCountBound]

theorem LargeHugeVertexCountBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      ((TwoBiteLargeHugeVertices ω ε I).card : ℝ) <
        Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
-- BODY
  classical
  intro n m p ω I ε ε1 ε2 n0 hComparisons hn hI hFiber
  let A : Finset (TwoBiteBaseVertex m) := TwoBiteLargeHugeVertices ω ε I
  let Cn : ℝ := 100 * (Real.log (n : ℝ)) ^ 3
  have hCompn := hComparisons n hn
  dsimp [ParameterHierarchyEventualComparisons] at hCompn
  rcases hCompn with
    ⟨_hm_pos, _hp_nonneg, _hp_le, _hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      _h16, _h17, _h18, _h19, _h20, _heps2_small,
      _heps2_nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
        hLargeHugeCutoff, _hStageUpper, hOneUnit, hGap,
      _h33, _h34, _h35, _h36⟩
  dsimp [FiberAndDegreeEvent] at hFiber
  rcases hFiber with
    ⟨_hredFiber, _hblueFiber, _hredDegree, _hblueDegree, _hredPair,
      _hbluePair, _hliftedDegree, hredOverlap, hblueOverlap, hmixedOverlap,
      _hredOpposite, _hblueOpposite⟩
  have hPointLower :
      ∀ x, x ∈ A →
        TwoBiteLargeCutoff ε n < ((TwoBiteX ω I x).card : ℝ) := by
    intro x hx
    have hxClass :
        TwoBiteLargeClass ω ε I x ∨ TwoBiteHugeClass ω I x := by
      simpa [A, TwoBiteLargeHugeVertices] using hx
    rcases hxClass with hLarge | hHuge
    · exact hLarge.1
    · exact lt_trans hLargeHugeCutoff hHuge.1
  have hX_subset_I :
      ∀ x : TwoBiteBaseVertex m, TwoBiteX ω I x ⊆ I := by
    intro x v hv
    exact (by simpa [TwoBiteX] using hv : v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x).1
  have hX_inter_subset_lifted :
      ∀ x y : TwoBiteBaseVertex m,
        TwoBiteX ω I x ∩ TwoBiteX ω I y ⊆
          TwoBiteLiftedNeighborhood ω x ∩ TwoBiteLiftedNeighborhood ω y := by
    intro x y v hv
    have hvx : v ∈ TwoBiteX ω I x := (Finset.mem_inter.mp hv).1
    have hvy : v ∈ TwoBiteX ω I y := (Finset.mem_inter.mp hv).2
    have hvx' : v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x := by
      simpa [TwoBiteX] using hvx
    have hvy' : v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω y := by
      simpa [TwoBiteX] using hvy
    exact Finset.mem_inter.mpr
      ⟨hvx'.2, hvy'.2⟩
  have hPairwiseIntersection :
      ∀ x, x ∈ A → ∀ y, y ∈ A → x ≠ y →
        (((TwoBiteX ω I x) ∩ (TwoBiteX ω I y)).card : ℝ) ≤ Cn := by
    intro x hx y hy hxy
    have hcard_to_lifted :
        (((TwoBiteX ω I x) ∩ (TwoBiteX ω I y)).card : ℝ) ≤
          (((TwoBiteLiftedNeighborhood ω x) ∩
              (TwoBiteLiftedNeighborhood ω y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hX_inter_subset_lifted x y)
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
  let F : TwoBiteBaseVertex m → Finset (Fin n) := fun x => TwoBiteX ω I x
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
  have hFiniteSubfamily :
      ∀ B : Finset (TwoBiteBaseVertex m), B ⊆ A → B.Nonempty →
        (B.card : ℝ) * TwoBiteLargeCutoff ε n -
            RealChooseTwo (B.card : ℝ) * Cn < (I.card : ℝ) := by
    intro B hBA hBnonempty
    have hUnion_subset_I : B.biUnion F ⊆ I := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨x, _hx, hvx⟩
      exact hX_subset_I x hvx
    have hUnion_card_le :
        (((B.biUnion F).card : ℝ) ≤ (I.card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hUnion_subset_I
    have hOverlap_B :
        ∀ x, x ∈ B → ∀ y, y ∈ B → x ≠ y →
          (((F x ∩ F y).card : ℝ) ≤ Cn) := by
      intro x hx y hy hxy
      exact hPairwiseIntersection x (hBA hx) y (hBA hy) hxy
    have hUnion_lower :
        B.sum (fun x => ((F x).card : ℝ)) -
            RealChooseTwo (B.card : ℝ) * Cn
          ≤ ((B.biUnion F).card : ℝ) :=
      hFiniteUnionLowerBound B hOverlap_B
    have hSum_strict :
        B.sum (fun _ : TwoBiteBaseVertex m => TwoBiteLargeCutoff ε n) <
          B.sum (fun x => ((F x).card : ℝ)) := by
      refine Finset.sum_lt_sum ?hle ?hlt
      · intro x hx
        exact le_of_lt (hPointLower x (hBA hx))
      · rcases hBnonempty with ⟨x, hx⟩
        exact ⟨x, hx, hPointLower x (hBA hx)⟩
    have hsum_const :
        B.sum (fun _ : TwoBiteBaseVertex m => TwoBiteLargeCutoff ε n) =
          (B.card : ℝ) * TwoBiteLargeCutoff ε n := by
      simp [nsmul_eq_mul]
    have hPoint_sum :
        (B.card : ℝ) * TwoBiteLargeCutoff ε n <
          B.sum (fun x => ((F x).card : ℝ)) := by
      simpa [hsum_const] using hSum_strict
    have hLower_strict :
        (B.card : ℝ) * TwoBiteLargeCutoff ε n -
            RealChooseTwo (B.card : ℝ) * Cn <
          B.sum (fun x => ((F x).card : ℝ)) -
            RealChooseTwo (B.card : ℝ) * Cn := by
      linarith only [hPoint_sum]
    exact lt_of_lt_of_le (lt_of_lt_of_le hLower_strict hUnion_lower) hUnion_card_le
  let r : ℝ := Real.rpow (n : ℝ) (1 / 4 : ℝ)
  let t2 : ℝ := TwoBiteLargeCutoff ε n
  change ((A.card : ℝ) < r)
  by_contra hnot
  have hA_ge : r ≤ (A.card : ℝ) := le_of_not_gt hnot
  have hn_pos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
  have hn_one_nat : 1 ≤ n := Nat.succ_le_iff.mpr hn_pos_nat
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_one_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
  have hr_pos : 0 < r := by
      dsimp [r]
      exact Real.rpow_pos_of_pos hn_pos_real _
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  let b : ℕ := Nat.ceil r
  have hb_ge_r : r ≤ (b : ℝ) := by
      simpa [b] using (Nat.le_ceil r)
  have hb_lt_r1 : (b : ℝ) < r + 1 := by
      simpa [b] using (Nat.ceil_lt_add_one hr_nonneg)
  have hb_le_r1 : (b : ℝ) ≤ r + 1 := le_of_lt hb_lt_r1
  have hb_le_A : b ≤ A.card := by
      simpa [b] using ((Nat.ceil_le).2 hA_ge)
  rcases Finset.exists_subset_card_eq (s := A) hb_le_A with ⟨B, hBA, hBcard⟩
  have hb_pos : 0 < b := by
      by_contra hb_nonpos
      have hb_zero : b = 0 := Nat.eq_zero_of_not_pos hb_nonpos
      have hr_le_zero : r ≤ 0 := by
        simpa [b, hb_zero] using hb_ge_r
      exact (not_lt_of_ge hr_le_zero) hr_pos
  have hBnonempty : B.Nonempty := by
      exact Finset.card_pos.mp (by simpa [hBcard] using hb_pos)
  have hBbound :
        (b : ℝ) * t2 - RealChooseTwo (b : ℝ) * Cn < (I.card : ℝ) := by
      have h := hFiniteSubfamily B hBA hBnonempty
      simpa [hBcard, t2] using h
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one_real
  have hCn_nonneg : 0 ≤ Cn := by
      dsimp [Cn]
      positivity
  have hOneUnit' : Cn * (r + (1 / 2 : ℝ)) ≤ t2 := by
      calc
        Cn * (r + (1 / 2 : ℝ))
            = 100 * (r + (1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by
              ring
        _ ≤ t2 := by
          simpa [r, t2] using hOneUnit
  have hmid_le : ((b : ℝ) + r - 1) / 2 ≤ r + (1 / 2 : ℝ) := by
      linarith only [hb_le_r1]
  have hparent_nonneg :
        0 ≤ t2 - Cn * (((b : ℝ) + r - 1) / 2) := by
      have hmul_le :
          Cn * (((b : ℝ) + r - 1) / 2) ≤ Cn * (r + (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmid_le hCn_nonneg
      linarith only [hmul_le, hOneUnit']
  have hf_compare :
        r * t2 - RealChooseTwo r * Cn ≤
          (b : ℝ) * t2 - RealChooseTwo (b : ℝ) * Cn := by
      have hdiff :
          ((b : ℝ) * t2 - RealChooseTwo (b : ℝ) * Cn) -
              (r * t2 - RealChooseTwo r * Cn) =
            ((b : ℝ) - r) *
              (t2 - Cn * (((b : ℝ) + r - 1) / 2)) := by
        simp [RealChooseTwo]
        ring
      have hdiff_nonneg :
          0 ≤
            ((b : ℝ) * t2 - RealChooseTwo (b : ℝ) * Cn) -
              (r * t2 - RealChooseTwo r * Cn) := by
        rw [hdiff]
        exact mul_nonneg (sub_nonneg.mpr hb_ge_r) hparent_nonneg
      linarith only [hdiff_nonneg]
  have hI_real :
        (I.card : ℝ) =
          (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) := by
      exact_mod_cast hI
  have hGapI :
        (I.card : ℝ) < r * t2 - RealChooseTwo r * Cn := by
      rw [hI_real]
      simpa [r, t2, Cn, TwoBiteLargeCutoff] using hGap
  have hfr_lt_I :
        r * t2 - RealChooseTwo r * Cn < (I.card : ℝ) :=
      lt_of_le_of_lt hf_compare hBbound
  exact (lt_irrefl (I.card : ℝ) (lt_trans hGapI hfr_lt_I)).elim
