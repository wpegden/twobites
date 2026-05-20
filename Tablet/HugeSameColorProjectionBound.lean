import Tablet.ClosedPairsBound
import Tablet.FiberAndDegreeEvent
import Tablet.HugeFamilySizeBound
import Tablet.HugeSameColorProjectionDegreeBound
import Tablet.HugeSameColorProjectionPairNumerics
import Tablet.HugeSameColorProjectionSizeBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteProjectedPairSum
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteX

-- [TABLET NODE: HugeSameColorProjectionBound]

set_option maxHeartbeats 400000 in
theorem HugeSameColorProjectionBound :
    ∀ {n m k : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      I.card = k →
      FiberAndDegreeEvent ω ε2 →
        let hugeRed : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
        let hugeBlue : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
        ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω))
            ε1 (k : ℝ) ∧
          ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
            ε1 (k : ℝ) ∧
          ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
              TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
            ε1 (k : ℝ) := by
-- BODY
  classical
  intro n m k p ω I ε ε1 ε2 n0 _hε1 hcomparisons hn hm hp hk hI hfiber
  dsimp
  let huge : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x
  let H : Finset (TwoBiteBaseVertex m) :=
    Finset.univ.filter huge
  let hugeRed : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
  let hugeBlue : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
  let HRed : Finset (TwoBiteBaseVertex m) :=
    Finset.univ.filter hugeRed
  let HBlue : Finset (TwoBiteBaseVertex m) :=
    Finset.univ.filter hugeBlue
  let redTerm : TwoBiteBaseVertex m → ℝ :=
    fun x =>
      RealChooseTwo ((((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ))
  let blueTerm : TwoBiteBaseVertex m → ℝ :=
    fun x =>
      RealChooseTwo ((((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
  let D : ℝ := 2 * p * (m : ℝ)
  let t1 : ℝ := TwoBiteHugeCutoff n
  let Q : ℝ := RealChooseTwo D
  let SRed : ℝ := HRed.sum redTerm
  let SBlue : ℝ := HBlue.sum blueTerm
  let CRed : ℝ := HRed.card
  let CBlue : ℝ := HBlue.card
  have hpoint :=
    HugeSameColorProjectionDegreeBound ω I ε ε1 ε2 hcomparisons hn hm hp hfiber
  have hcomp := hcomparisons n hn
  dsimp [ParameterHierarchyEventualComparisons, TwoBiteEdgeProbability] at hcomp
  rcases hcomp with
    ⟨_hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      _h16, _h17, hpair_count_num, _h19, _h20, _h21, _heps2_nonneg, _heps2_le,
      _h24, _hrest⟩
  have hD_ge_one : 1 ≤ D := by
    simpa [D, TwoBiteEdgeProbability, hp, hm, mul_assoc] using hpm_ge_one
  have hchoose_control_nat :
      ∀ {c : ℕ}, (c : ℝ) ≤ D →
        0 ≤ RealChooseTwo (c : ℝ) ∧ RealChooseTwo (c : ℝ) ≤ RealChooseTwo D := by
    intro c hle
    have hD_nonneg : 0 ≤ D := by linarith only [hD_ge_one]
    have hD_minus_nonneg : 0 ≤ D - 1 := by linarith only [hD_ge_one]
    have hchooseD_nonneg : 0 ≤ RealChooseTwo D := by
      unfold RealChooseTwo
      nlinarith only [mul_nonneg hD_nonneg hD_minus_nonneg]
    by_cases hc : c ≤ 1
    · have hc_cases : c = 0 ∨ c = 1 := by omega
      rcases hc_cases with rfl | rfl
      · constructor
        · simp [RealChooseTwo]
        · simpa [RealChooseTwo] using hchooseD_nonneg
      · constructor
        · simp [RealChooseTwo]
        · simpa [RealChooseTwo] using hchooseD_nonneg
    · have hc_ge_two : 2 ≤ c := by omega
      have hc_real : 1 ≤ (c : ℝ) := by
        exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hc_ge_two)
      have hmono : RealChooseTwo (c : ℝ) ≤ RealChooseTwo D := by
        unfold RealChooseTwo
        nlinarith only [hle, hc_real, sq_nonneg (D - (c : ℝ))]
      have hnonneg : 0 ≤ RealChooseTwo (c : ℝ) := by
        have hc_cast_nonneg : 0 ≤ (c : ℝ) := by positivity
        have hc_minus_nonneg : 0 ≤ (c : ℝ) - 1 := by
          linarith only [hc_real]
        unfold RealChooseTwo
        nlinarith only [mul_nonneg hc_cast_nonneg hc_minus_nonneg]
      exact ⟨hnonneg, hmono⟩
  have hred_choose_control :
      ∀ x, x ∈ HRed →
        0 ≤ redTerm x ∧ redTerm x ≤ RealChooseTwo D := by
    intro x hx
    have hxprop : hugeRed x := by simpa [HRed] using hx
    rcases hxprop.2 with ⟨r, rfl⟩
    have hcard_le :
        ((((TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω)).card : ℝ) ≤
          D) := by
      simpa [D] using hpoint.1 r
    simpa [redTerm] using hchoose_control_nat hcard_le
  have hblue_choose_control :
      ∀ x, x ∈ HBlue →
        0 ≤ blueTerm x ∧ blueTerm x ≤ RealChooseTwo D := by
    intro x hx
    have hxprop : hugeBlue x := by simpa [HBlue] using hx
    rcases hxprop.2 with ⟨b, rfl⟩
    have hcard_le :
        ((((TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω)).card : ℝ) ≤
          D) := by
      simpa [D] using hpoint.2 b
    simpa [blueTerm] using hchoose_control_nat hcard_le
  have hred_sum : SRed ≤ CRed * Q := by
    dsimp [SRed, CRed, Q]
    calc
      HRed.sum redTerm
          ≤ HRed.sum (fun _ : TwoBiteBaseVertex m => RealChooseTwo D) := by
            exact Finset.sum_le_sum (fun x hx => (hred_choose_control x hx).2)
      _ = (HRed.card : ℝ) * RealChooseTwo D := by simp [nsmul_eq_mul]
  have hblue_sum : SBlue ≤ CBlue * Q := by
    dsimp [SBlue, CBlue, Q]
    calc
      HBlue.sum blueTerm
          ≤ HBlue.sum (fun _ : TwoBiteBaseVertex m => RealChooseTwo D) := by
            exact Finset.sum_le_sum (fun x hx => (hblue_choose_control x hx).2)
      _ = (HBlue.card : ℝ) * RealChooseTwo D := by simp [nsmul_eq_mul]
  have hred_sum_nonneg : 0 ≤ SRed := by
    dsimp [SRed]
    exact Finset.sum_nonneg (fun x hx => (hred_choose_control x hx).1)
  have hblue_sum_nonneg : 0 ≤ SBlue := by
    dsimp [SBlue]
    exact Finset.sum_nonneg (fun x hx => (hblue_choose_control x hx).1)
  have hfilter_union_subset : HRed ∪ HBlue ⊆ H := by
    intro x hx
    have hxmem : x ∈ HRed ∨ x ∈ HBlue := by simpa using hx
    have hxhuge : huge x := by
      rcases hxmem with hred | hblue
      · have hred' : x ∈ Finset.univ.filter hugeRed := by simpa only [HRed] using hred
        have hredprop : hugeRed x := (Finset.mem_filter.mp hred').2
        exact hredprop.1
      · have hblue' : x ∈ Finset.univ.filter hugeBlue := by simpa only [HBlue] using hblue
        have hblueprop : hugeBlue x := (Finset.mem_filter.mp hblue').2
        exact hblueprop.1
    change x ∈ Finset.univ.filter huge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxhuge⟩
  have hfilter_inter_empty : HRed ∩ HBlue = ∅ := by
    ext x
    constructor
    · intro hx
      have hxpair : x ∈ HRed ∧ x ∈ HBlue := Finset.mem_inter.mp hx
      have hred : x ∈ HRed := hxpair.1
      have hblue : x ∈ HBlue := hxpair.2
      have hred' : x ∈ Finset.univ.filter hugeRed := by simpa only [HRed] using hred
      have hblue' : x ∈ Finset.univ.filter hugeBlue := by simpa only [HBlue] using hblue
      have hredprop : hugeRed x := (Finset.mem_filter.mp hred').2
      have hblueprop : hugeBlue x := (Finset.mem_filter.mp hblue').2
      rcases hredprop.2 with ⟨r, hr⟩
      rcases hblueprop.2 with ⟨b, hb⟩
      rw [hr] at hb
      cases hb
    · intro hx
      cases hx
  have hcard_union :
      (HRed ∪ HBlue).card = HRed.card + HBlue.card := by
    simpa [hfilter_inter_empty] using
      (Finset.card_union_add_card_inter HRed HBlue)
  have hcard_sum_le : (HRed.card : ℝ) + (HBlue.card : ℝ) ≤ (H.card : ℝ) := by
    have hnat : HRed.card + HBlue.card ≤ H.card := by
      calc
        HRed.card + HBlue.card = (HRed ∪ HBlue).card := by
          exact hcard_union.symm
        _ ≤ H.card := Finset.card_le_card hfilter_union_subset
    exact_mod_cast hnat
  have hcard_sum_le' : CRed + CBlue ≤ (H.card : ℝ) := by
    change (HRed.card : ℝ) + (HBlue.card : ℝ) ≤ (H.card : ℝ)
    exact hcard_sum_le
  have hfamily := HugeFamilySizeBound ω I ε ε1 ε2 hcomparisons hn hk hI hfiber
  have hH_card : (H.card : ℝ) ≤ 2 * (k : ℝ) / t1 := by
    change
      (((Finset.univ.filter
          (fun x : TwoBiteBaseVertex m => TwoBiteHugeClass ω I x)).card : ℝ) ≤
        2 * (k : ℝ) / TwoBiteHugeCutoff n)
    exact hfamily.2
  have hnum :
      (2 * (k : ℝ) / t1) * RealChooseTwo D ≤ ε1 * (k : ℝ) ^ 2 := by
    have hk_cast :
        ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hk.symm
    simpa [D, t1, TwoBiteHugeCutoff, TwoBiteEdgeProbability, hp, hm, hk_cast,
      mul_assoc] using hpair_count_num
  have hsum_le_cardChoose :
      SRed + SBlue ≤ (CRed + CBlue) * Q := by
    calc
      SRed + SBlue
          ≤ CRed * Q + CBlue * Q := by
            exact add_le_add hred_sum hblue_sum
      _ = (CRed + CBlue) * Q := by
            ring
  have hcardChoose_le : (CRed + CBlue) * Q ≤ ε1 * (k : ℝ) ^ 2 := by
    have hcard : CRed + CBlue ≤ 2 * (k : ℝ) / t1 :=
      le_trans hcard_sum_le' hH_card
    change (CRed + CBlue) * RealChooseTwo (2 * p * (m : ℝ)) ≤ ε1 * (k : ℝ) ^ 2
    exact HugeSameColorProjectionPairNumerics hcard hD_ge_one hnum
  have htotal : SRed + SBlue ≤ ε1 * (k : ℝ) ^ 2 :=
    le_trans hsum_le_cardChoose hcardChoose_le
  have hred_bound : SRed ≤ ε1 * (k : ℝ) ^ 2 := by
    exact le_trans (le_add_of_nonneg_right hblue_sum_nonneg) htotal
  have hblue_bound : SBlue ≤ ε1 * (k : ℝ) ^ 2 := by
    exact le_trans (le_add_of_nonneg_left hred_sum_nonneg) htotal
  refine ⟨?_, ?_, ?_⟩
  · unfold ClosedPairsBound
    unfold TwoBiteProjectedPairSum
    refine le_of_eq_of_le ?_ hred_bound
    dsimp [SRed, HRed, hugeRed, redTerm]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro x hx
      rfl
  · unfold ClosedPairsBound
    unfold TwoBiteProjectedPairSum
    refine le_of_eq_of_le ?_ hblue_bound
    dsimp [SBlue, HBlue, hugeBlue, blueTerm]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro x hx
      rfl
  · unfold ClosedPairsBound
    unfold TwoBiteProjectedPairSum
    refine le_of_eq_of_le ?_ htotal
    dsimp [SRed, SBlue, HRed, HBlue, hugeRed, hugeBlue, redTerm, blueTerm]
    congr 1
    · refine Finset.sum_congr ?_ ?_
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro x hx
        rfl
    · refine Finset.sum_congr ?_ ?_
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro x hx
        rfl
