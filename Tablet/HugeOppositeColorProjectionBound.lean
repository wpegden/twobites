import Tablet.FiberAndDegreeEvent
import Tablet.HugeFamilySizeBound
import Tablet.HugeOppositeProjectionMassControl
import Tablet.HugeSameColorProjectionBound
import Tablet.HugeSameColorProjectionSizeBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.ProjectionOpenPairFunction
import Tablet.RealChooseTwoCappedSumBound
import Tablet.RealChooseTwoSumBound
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteProjectedPairSum
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteX

-- [TABLET NODE: HugeOppositeColorProjectionBound]

theorem HugeOppositeColorProjectionBound :
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
        TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) ≤
            (1 + ε1) *
              min
                (RealChooseTwo ((k : ℝ) -
                  ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((k : ℝ) -
                      ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
                        p * (n : ℝ))) ∧
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω) ≤
            (1 + ε1) *
              min
                (RealChooseTwo ((k : ℝ) -
                  ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((k : ℝ) -
                      ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
                        p * (n : ℝ))) := by
-- BODY
  classical
  intro n m k p ω I ε ε1 ε2 n0 hε1 hcomparisons hn hm hp hk hI hfiber
  dsimp
  let hugeRed : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
  let hugeBlue : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
  let HRed : Finset (TwoBiteBaseVertex m) :=
    Finset.univ.filter hugeRed
  let HBlue : Finset (TwoBiteBaseVertex m) :=
    Finset.univ.filter hugeBlue
  let redTerm : TwoBiteBaseVertex m → ℝ :=
    fun x => (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ)
  let blueTerm : TwoBiteBaseVertex m → ℝ :=
    fun x => (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ)
  let redMass : ℝ := HRed.sum redTerm
  let blueMass : ℝ := HBlue.sum blueTerm
  let redDeficit : ℝ :=
    (k : ℝ) - ((I.image (TwoBiteRedProjection ω)).card : ℝ)
  let blueDeficit : ℝ :=
    (k : ℝ) - ((I.image (TwoBiteBlueProjection ω)).card : ℝ)
  let blockScale : ℝ := p * (n : ℝ)
  have hmass :=
    HugeOppositeProjectionMassControl (n := n) (m := m) (k := k) (p := p)
      ω I ε ε1 ε2 (n0 := n0) hε1 hcomparisons hn hm hp hk hI hfiber
  dsimp only at hmass
  rcases hmass with
    ⟨hredCap, _hredMassLe, hredOne, hredSmall, hredLarge,
      hblueCap, _hblueMassLe, hblueOne, hblueSmall, hblueLarge⟩
  have hcomp := hcomparisons n hn
  dsimp [ParameterHierarchyEventualComparisons, TwoBiteEdgeProbability] at hcomp
  rcases hcomp with
    ⟨_hm_pos, hp_nonneg_raw, _hp_le, _hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      _h16, _h17, _h18, _h19, _h20, _hscale, hε2_nonneg,
      _hε2_le_one, _hrest⟩
  have hp_nonneg : 0 ≤ p := by
    simpa [TwoBiteEdgeProbability, hp] using hp_nonneg_raw
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hblock_nonneg : 0 ≤ blockScale := by
    dsimp [blockScale]
    exact mul_nonneg hp_nonneg hn_nonneg
  have hcap_nonneg : 0 ≤ (1 + ε2) * blockScale := by
    exact mul_nonneg (by linarith only [hε2_nonneg]) hblock_nonneg
  have hredTerm_nonneg : ∀ x, x ∈ HRed → 0 ≤ redTerm x := by
    intro x _hx
    dsimp [redTerm]
    exact_mod_cast Nat.zero_le (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card)
  have hblueTerm_nonneg : ∀ x, x ∈ HBlue → 0 ≤ blueTerm x := by
    intro x _hx
    dsimp [blueTerm]
    exact_mod_cast Nat.zero_le (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card)
  have hredTerm_cap : ∀ x, x ∈ HRed → redTerm x ≤ (1 + ε2) * blockScale := by
    intro x hx
    have hx' : x ∈ (Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeRed := by
      simpa [HRed] using hx
    have hxHuge : hugeRed x := (Finset.mem_filter.mp hx').2
    simpa [redTerm, blockScale, hugeRed] using hredCap x hxHuge
  have hblueTerm_cap : ∀ x, x ∈ HBlue → blueTerm x ≤ (1 + ε2) * blockScale := by
    intro x hx
    have hx' : x ∈ (Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeBlue := by
      simpa [HBlue] using hx
    have hxHuge : hugeBlue x := (Finset.mem_filter.mp hx').2
    simpa [blueTerm, blockScale, hugeBlue] using hblueCap x hxHuge
  have hchoose_sum_bound :
      ∀ (S : Finset (TwoBiteBaseVertex m)) (a : TwoBiteBaseVertex m → ℝ),
        (∀ x, x ∈ S → 0 ≤ a x) →
          S.sum (fun x => RealChooseTwo (a x)) ≤ RealChooseTwo (S.sum a) := by
    intro S a h_nonneg
    revert h_nonneg
    refine Finset.induction_on S ?choose_base ?choose_step
    · intro _h_nonneg
      simp [RealChooseTwo]
    · intro x S hx hrec h_nonneg_insert
      have hx_nonneg : 0 ≤ a x := h_nonneg_insert x (by simp [hx])
      have hS_nonneg : ∀ y, y ∈ S → 0 ≤ a y := by
        intro y hy
        exact h_nonneg_insert y (by simp [hy])
      have hsum_nonneg : 0 ≤ S.sum a :=
        Finset.sum_nonneg (fun y hy => hS_nonneg y hy)
      have hrec' :
          S.sum (fun y => RealChooseTwo (a y)) ≤ RealChooseTwo (S.sum a) :=
        hrec hS_nonneg
      have htwo :
          RealChooseTwo (S.sum a) + RealChooseTwo (a x) ≤
            RealChooseTwo (S.sum a + a x) := by
        have hidentity := RealChooseTwoSumBound (S.sum a) (a x)
        have hprod_nonneg : 0 ≤ S.sum a * a x :=
          mul_nonneg hsum_nonneg hx_nonneg
        have hrewrite :
            RealChooseTwo (S.sum a + a x) =
              RealChooseTwo (S.sum a) + RealChooseTwo (a x) + S.sum a * a x := by
          linarith
        rw [hrewrite]
        exact le_add_of_nonneg_right hprod_nonneg
      calc
        (insert x S).sum (fun y => RealChooseTwo (a y))
            = RealChooseTwo (a x) + S.sum (fun y => RealChooseTwo (a y)) := by
              simp [hx]
        _ ≤ RealChooseTwo (a x) + RealChooseTwo (S.sum a) := by
              linarith
        _ = RealChooseTwo (S.sum a) + RealChooseTwo (a x) := by
              ring
        _ ≤ RealChooseTwo (S.sum a + a x) := htwo
        _ = RealChooseTwo ((insert x S).sum a) := by
              simp [hx, add_comm]
  have hredChoose_to_mass :
      HRed.sum (fun x => RealChooseTwo (redTerm x)) ≤ RealChooseTwo redMass := by
    dsimp [redMass]
    exact hchoose_sum_bound HRed redTerm hredTerm_nonneg
  have hblueChoose_to_mass :
      HBlue.sum (fun x => RealChooseTwo (blueTerm x)) ≤ RealChooseTwo blueMass := by
    dsimp [blueMass]
    exact hchoose_sum_bound HBlue blueTerm hblueTerm_nonneg
  have hredChoose_to_split :
      (1 + ε2) * blockScale ≤ redMass →
        HRed.sum (fun x => RealChooseTwo (redTerm x)) ≤
          RealChooseTwo ((1 + ε2) * blockScale) +
            RealChooseTwo (redMass - (1 + ε2) * blockScale) := by
    intro hlarge
    dsimp [redMass]
    exact
      RealChooseTwoCappedSumBound HRed redTerm ((1 + ε2) * blockScale)
        hcap_nonneg hredTerm_nonneg hredTerm_cap hlarge
  have hblueChoose_to_split :
      (1 + ε2) * blockScale ≤ blueMass →
        HBlue.sum (fun x => RealChooseTwo (blueTerm x)) ≤
          RealChooseTwo ((1 + ε2) * blockScale) +
            RealChooseTwo (blueMass - (1 + ε2) * blockScale) := by
    intro hlarge
    dsimp [blueMass]
    exact
      RealChooseTwoCappedSumBound HBlue blueTerm ((1 + ε2) * blockScale)
        hcap_nonneg hblueTerm_nonneg hblueTerm_cap hlarge
  have hred_one_side :
      HRed.sum (fun x => RealChooseTwo (redTerm x)) ≤
        (1 + ε1) * RealChooseTwo redDeficit := by
    exact le_trans hredChoose_to_mass
      (by simpa [redMass, redDeficit, blockScale, HRed, redTerm, hugeRed] using hredOne)
  have hblue_one_side :
      HBlue.sum (fun x => RealChooseTwo (blueTerm x)) ≤
        (1 + ε1) * RealChooseTwo blueDeficit := by
    exact le_trans hblueChoose_to_mass
      (by simpa [blueMass, blueDeficit, blockScale, HBlue, blueTerm, hugeBlue] using hblueOne)
  have hred_two_side :
      HRed.sum (fun x => RealChooseTwo (redTerm x)) ≤
        (1 + ε1) *
          (RealChooseTwo blockScale + RealChooseTwo (redDeficit - blockScale)) := by
    by_cases hsmall : redMass ≤ (1 + ε2) * blockScale
    · exact le_trans hredChoose_to_mass
        (by
          simpa [redMass, redDeficit, blockScale, HRed, redTerm, hugeRed]
            using hredSmall hsmall)
    · have hlarge : (1 + ε2) * blockScale ≤ redMass := le_of_not_ge hsmall
      exact le_trans (hredChoose_to_split hlarge)
        (by
          simpa [redMass, redDeficit, blockScale, HRed, redTerm, hugeRed]
            using hredLarge hlarge)
  have hblue_two_side :
      HBlue.sum (fun x => RealChooseTwo (blueTerm x)) ≤
        (1 + ε1) *
          (RealChooseTwo blockScale + RealChooseTwo (blueDeficit - blockScale)) := by
    by_cases hsmall : blueMass ≤ (1 + ε2) * blockScale
    · exact le_trans hblueChoose_to_mass
        (by
          simpa [blueMass, blueDeficit, blockScale, HBlue, blueTerm, hugeBlue]
            using hblueSmall hsmall)
    · have hlarge : (1 + ε2) * blockScale ≤ blueMass := le_of_not_ge hsmall
      exact le_trans (hblueChoose_to_split hlarge)
        (by
          simpa [blueMass, blueDeficit, blockScale, HBlue, blueTerm, hugeBlue]
            using hblueLarge hlarge)
  have hred_min :
      HRed.sum (fun x => RealChooseTwo (redTerm x)) ≤
        (1 + ε1) *
          min (RealChooseTwo redDeficit)
            (RealChooseTwo blockScale + RealChooseTwo (redDeficit - blockScale)) := by
    by_cases hle :
        RealChooseTwo redDeficit ≤
          RealChooseTwo blockScale + RealChooseTwo (redDeficit - blockScale)
    · simpa [min_eq_left hle] using hred_one_side
    · have hle' :
          RealChooseTwo blockScale + RealChooseTwo (redDeficit - blockScale) ≤
            RealChooseTwo redDeficit := le_of_not_ge hle
      simpa [min_eq_right hle'] using hred_two_side
  have hblue_min :
      HBlue.sum (fun x => RealChooseTwo (blueTerm x)) ≤
        (1 + ε1) *
          min (RealChooseTwo blueDeficit)
            (RealChooseTwo blockScale + RealChooseTwo (blueDeficit - blockScale)) := by
    by_cases hle :
        RealChooseTwo blueDeficit ≤
          RealChooseTwo blockScale + RealChooseTwo (blueDeficit - blockScale)
    · simpa [min_eq_left hle] using hblue_one_side
    · have hle' :
          RealChooseTwo blockScale + RealChooseTwo (blueDeficit - blockScale) ≤
            RealChooseTwo blueDeficit := le_of_not_ge hle
      simpa [min_eq_right hle'] using hblue_two_side
  refine ⟨?_, ?_⟩
  · unfold TwoBiteProjectedPairSum
    refine le_of_eq_of_le ?_ (by simpa [redDeficit, blockScale] using hred_min)
    dsimp [HRed, hugeRed, redTerm]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro x _hx
      rfl
  · unfold TwoBiteProjectedPairSum
    refine le_of_eq_of_le ?_ (by simpa [blueDeficit, blockScale] using hblue_min)
    dsimp [HBlue, hugeBlue, blueTerm]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro x _hx
      rfl
