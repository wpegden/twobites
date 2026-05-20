import Tablet.FiberAndDegreeEvent
import Tablet.HugeFamilySizeBound
import Tablet.HugeSameColorProjectionDegreeBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteX

-- [TABLET NODE: HugeSameColorProjectionSizeBound]

theorem HugeSameColorProjectionSizeBound : by
  classical
  exact
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
        let HRed : Finset (TwoBiteBaseVertex m) :=
          (Finset.univ.filter hugeRed)
        let HBlue : Finset (TwoBiteBaseVertex m) :=
          (Finset.univ.filter hugeBlue)
        HRed.sum
            (fun x =>
              (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ)) +
          HBlue.sum
            (fun x =>
              (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
            ≤ (ε1 / 10) * (k : ℝ) := by
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
  let D : ℝ := 2 * p * (m : ℝ)
  let t1 : ℝ := TwoBiteHugeCutoff n
  have hpoint :=
    HugeSameColorProjectionDegreeBound ω I ε ε1 ε2 hcomparisons hn hm hp hfiber
  have hred_point :
      ∀ x, x ∈ HRed →
        (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ) ≤ D := by
    intro x hx
    have hxprop : hugeRed x := by simpa [HRed] using hx
    rcases hxprop.2 with ⟨r, rfl⟩
    simpa [D] using hpoint.1 r
  have hblue_point :
      ∀ x, x ∈ HBlue →
        (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ) ≤ D := by
    intro x hx
    have hxprop : hugeBlue x := by simpa [HBlue] using hx
    rcases hxprop.2 with ⟨b, rfl⟩
    simpa [D] using hpoint.2 b
  have hred_sum :
      HRed.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ))
        ≤ (HRed.card : ℝ) * D := by
    calc
      HRed.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ))
          ≤ HRed.sum (fun _ : TwoBiteBaseVertex m => D) := by
            exact Finset.sum_le_sum hred_point
      _ = (HRed.card : ℝ) * D := by simp [nsmul_eq_mul]
  have hblue_sum :
      HBlue.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
        ≤ (HBlue.card : ℝ) * D := by
    calc
      HBlue.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
          ≤ HBlue.sum (fun _ : TwoBiteBaseVertex m => D) := by
            exact Finset.sum_le_sum hblue_point
      _ = (HBlue.card : ℝ) * D := by simp [nsmul_eq_mul]
  have hfilter_union_subset : HRed ∪ HBlue ⊆ H := by
    intro x hx
    simp [HRed, HBlue, H, hugeRed, hugeBlue, huge] at hx ⊢
    exact hx.elim (fun h => h.1) (fun h => h.1)
  have hfilter_inter_empty : HRed ∩ HBlue = ∅ := by
    ext x
    cases x with
    | inl r => simp [HRed, HBlue, hugeRed, hugeBlue]
    | inr b => simp [HRed, HBlue, hugeRed, hugeBlue]
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
  have hcomp := hcomparisons n hn
  dsimp [ParameterHierarchyEventualComparisons, TwoBiteEdgeProbability] at hcomp
  rcases hcomp with
    ⟨_hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      _h16, hsame_color_num, _h18, _h19, _h20, _h21, _heps2_nonneg, _heps2_le,
      _h24, _hrest⟩
  have hD_nonneg : 0 ≤ D := by
    have hD_ge_one : 1 ≤ D := by
      simpa [D, TwoBiteEdgeProbability, hp, hm, mul_assoc] using hpm_ge_one
    linarith only [hD_ge_one]
  have hfamily := HugeFamilySizeBound ω I ε ε1 ε2 hcomparisons hn hk hI hfiber
  have hH_card : (H.card : ℝ) ≤ 2 * (k : ℝ) / t1 := by
    simpa [H, huge, t1] using hfamily.2
  have hnum :
      (2 * (k : ℝ) / t1) * D ≤ (ε1 / 10) * (k : ℝ) := by
    have hk_cast :
        ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hk.symm
    simpa [D, t1, TwoBiteHugeCutoff, TwoBiteEdgeProbability, hp, hm, hk_cast,
      mul_assoc] using hsame_color_num
  have hsum_le_cardD :
      HRed.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ)) +
        HBlue.sum
          (fun x => (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
        ≤ ((HRed.card : ℝ) + (HBlue.card : ℝ)) * D := by
    nlinarith only [hred_sum, hblue_sum]
  have hcardD_le : ((HRed.card : ℝ) + (HBlue.card : ℝ)) * D ≤
      (2 * (k : ℝ) / t1) * D := by
    exact mul_le_mul_of_nonneg_right (le_trans hcard_sum_le hH_card) hD_nonneg
  exact le_trans hsum_le_cardD (le_trans hcardD_le hnum)
