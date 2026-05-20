import Tablet.FixedSetHistoryCellBranchTranscriptSummation
import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellBlueFixedCountCellSummation]

theorem FixedSetHistoryCellBlueFixedCountCellSummation :
    ∀ {n m uR uB NR NB : ℕ} {p a : ℝ}
      (hist target : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (redSupportLabels :
        Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {BranchLabel : Type} [Fintype BranchLabel]
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {BlueLabel : Type} [Fintype BlueLabel]
      (blueSupport :
        BranchLabel →
          BlueLabel → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellEvent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          TwoBiteSample n m p → Prop)
      (cellWeight :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ),
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      uR ≤ uB →
      Fintype.card BlueLabel ≤ Nat.choose NR uB →
      redSupportLabels.card ≤ Nat.choose NB uR →
      (∀ B,
        B ∈ redSupportLabels →
          B.card = uR ∧
          B ⊆ terminal ∧
          ∀ e,
            e ∈ B →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          hist ω →
            ∃ B,
              B ∈ redSupportLabels ∧
                ∃ J : BlueLabel,
                  ∃ β : BranchLabel,
                    ∃ τ,
                      τ ∈ transcriptLabels ∧
                        cellEvent B J β τ ω) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  ∀ ω : TwoBiteSample n m p,
                    cellEvent B J β τ ω →
                      (blueSupport β J).card = uB ∧
                      blueSupport β J ⊆ terminal ∧
                      (∀ e,
                        e ∈ blueSupport β J →
                          match e with
                          | Sum.inl _ => False
                          | Sum.inr _ => True) ∧
                      τ.1 ⊆ terminal ∧
                      τ.2.1 ⊆ terminal ∧
                      Disjoint τ.1 τ.2.1 ∧
                      B ∪ blueSupport β J ⊆ τ.1 ∧
                      τ.2.2 ⊆ τ.2.1 ∧
                      max 0 (a - (uB : ℝ) - (uR : ℝ))
                        ≤ ((τ.2.2).card : ℝ) ∧
                      (∀ e,
                        e ∈ τ.1 →
                          TwoBiteEdgeCoordinateValue ω e) ∧
                      (∀ e,
                        e ∈ τ.2.1 →
                          ¬ TwoBiteEdgeCoordinateValue ω e)) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  0 ≤ cellWeight B J β τ) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  cellWeight B J β τ
                    ≤
                    p ^ τ.1.card *
                      ((1 : ℝ) - p) ^ τ.2.1.card) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  TwoBiteEventProbability n m p
                      (fun ω =>
                        target ω ∧ hist ω ∧
                          cellEvent B J β τ ω)
                    ≤
                    TwoBiteEventProbability n m p hist *
                      cellWeight B J β τ) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            (Finset.univ : Finset BranchLabel).sum
                (fun β =>
                  transcriptLabels.sum
                    (fun τ => cellWeight B J β τ))
              ≤
              p ^ uB * p ^ uR *
                Real.rpow ((1 : ℝ) - p)
                  (max 0 (a - (uB : ℝ) - (uR : ℝ)))) →
      TwoBiteConditionalProbability n m p target hist
        ≤
        (Nat.choose NR uB : ℝ) * p ^ uB *
          (Nat.choose NB uR : ℝ) * p ^ uR *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uB : ℝ) - (uR : ℝ))) := by
-- BODY
  classical
  intro n m uR uB NR NB p a hist target terminal redSupportLabels
    BranchLabel _ transcriptLabels BlueLabel _ blueSupport cellEvent cellWeight
    hp0 hphalf _huB_le_uR hred_card hblue_card _hblue_labels hcover
    _hcell_geometry hcellWeight_nonneg _hcellWeight_cylinder hcell_mass
    hfixed_pair_sum
  let Ω := TwoBiteSample n m p
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript :=
    Finset Coord × Finset Coord × Finset Coord
  let PairIndex := {B : Finset Coord // B ∈ redSupportLabels} × BlueLabel
  let TranscriptIndex := {τ : Transcript // τ ∈ transcriptLabels}
  let prob : (Ω → Prop) → ℝ := fun E => TwoBiteEventProbability n m p E
  let L : ℝ := max 0 (a - (uB : ℝ) - (uR : ℝ))
  let pairMass : ℝ :=
    p ^ uB * p ^ uR * Real.rpow ((1 : ℝ) - p) L
  let rhs : ℝ :=
    (Nat.choose NR uB : ℝ) * p ^ uB *
      (Nat.choose NB uR : ℝ) * p ^ uR *
        Real.rpow ((1 : ℝ) - p) L
  change TwoBiteConditionalProbability n m p target hist ≤ rhs
  have hp1 : p ≤ (1 : ℝ) := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
    exact le_trans hphalf hhalf_le_one
  have hone_minus_nonneg : 0 ≤ (1 : ℝ) - p := sub_nonneg.mpr hp1
  have hsample_nonneg : ∀ ω : Ω, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hprob_nonneg : ∀ E : Ω → Prop, 0 ≤ prob E := by
    intro E
    unfold prob TwoBiteEventProbability
    exact Finset.sum_nonneg (by
      intro ω hω
      exact hsample_nonneg ω)
  have hpairMass_nonneg : 0 ≤ pairMass := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hp0 _))
      (Real.rpow_nonneg hone_minus_nonneg L)
  have hrhs_nonneg : 0 ≤ rhs := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
          (Nat.cast_nonneg _))
        (pow_nonneg hp0 _))
      (Real.rpow_nonneg hone_minus_nonneg L)
  let liftedCellEvent :
      PairIndex → BranchLabel → TranscriptIndex → Ω → Prop :=
    fun b β τ ω => cellEvent b.1.1 b.2 β τ.1 ω
  let liftedWeight : PairIndex → BranchLabel → TranscriptIndex → ℝ :=
    fun b β τ => prob hist * cellWeight b.1.1 b.2 β τ.1
  have hlifted_cover :
      ∀ ω : Ω,
        target ω →
          hist ω →
            ∃ b β τ, liftedCellEvent b β τ ω := by
    intro ω htarget hhist
    rcases hcover ω htarget hhist with
      ⟨B, hB, J, β, τ, hτ, hcell⟩
    exact ⟨(⟨B, hB⟩, J), β, ⟨τ, hτ⟩, hcell⟩
  have hlifted_weight_nonneg :
      ∀ b β τ, 0 ≤ liftedWeight b β τ := by
    intro b β τ
    exact mul_nonneg (hprob_nonneg hist)
      (hcellWeight_nonneg b.1.1 b.1.2 b.2 β τ.1 τ.2)
  have hlifted_cell_bound :
      ∀ b β τ,
        TwoBiteEventProbability n m p
            (fun ω => target ω ∧ hist ω ∧ liftedCellEvent b β τ ω)
          ≤ liftedWeight b β τ := by
    intro b β τ
    simpa [liftedCellEvent, liftedWeight, prob] using
      hcell_mass b.1.1 b.1.2 b.2 β τ.1 τ.2
  have htranscript_sum :
      ∀ (B : Finset Coord) (J : BlueLabel) (β : BranchLabel),
        (Finset.univ : Finset TranscriptIndex).sum
            (fun τ => cellWeight B J β τ.1)
          =
          transcriptLabels.sum (fun τ => cellWeight B J β τ) := by
    intro B J β
    rw [Finset.univ_eq_attach transcriptLabels]
    simpa using
      (Finset.sum_attach transcriptLabels
        (fun τ => cellWeight B J β τ))
  have hinner_sum_bound :
      ∀ b : PairIndex,
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (Finset.univ : Finset TranscriptIndex).sum
                (fun τ => liftedWeight b β τ))
          ≤
          prob hist * pairMass := by
    intro b
    have hwithout_prob :
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (Finset.univ : Finset TranscriptIndex).sum
                (fun τ => cellWeight b.1.1 b.2 β τ.1))
          ≤ pairMass := by
      calc
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (Finset.univ : Finset TranscriptIndex).sum
                (fun τ => cellWeight b.1.1 b.2 β τ.1))
          =
            (Finset.univ : Finset BranchLabel).sum
              (fun β =>
                transcriptLabels.sum
                  (fun τ => cellWeight b.1.1 b.2 β τ)) := by
              refine Finset.sum_congr rfl ?_
              intro β hβ
              exact htranscript_sum b.1.1 b.2 β
        _ ≤ pairMass := by
          simpa [pairMass, L] using
            hfixed_pair_sum b.1.1 b.1.2 b.2
    calc
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (Finset.univ : Finset TranscriptIndex).sum
              (fun τ => liftedWeight b β τ))
        =
          prob hist *
            (Finset.univ : Finset BranchLabel).sum
              (fun β =>
                (Finset.univ : Finset TranscriptIndex).sum
                  (fun τ => cellWeight b.1.1 b.2 β τ.1)) := by
          simp [liftedWeight, Finset.mul_sum]
      _ ≤ prob hist * pairMass :=
        mul_le_mul_of_nonneg_left hwithout_prob (hprob_nonneg hist)
  have hpair_card :
      Fintype.card PairIndex =
        redSupportLabels.card * Fintype.card BlueLabel := by
    simp [PairIndex, Fintype.card_prod, Fintype.card_coe]
  have hpair_card_bound :
      (Fintype.card PairIndex : ℝ)
        ≤ (Nat.choose NB uR : ℝ) * (Nat.choose NR uB : ℝ) := by
    have hblue_card_real :
        (redSupportLabels.card : ℝ) ≤ (Nat.choose NB uR : ℝ) := by
      exact_mod_cast hblue_card
    have hred_card_real :
        (Fintype.card BlueLabel : ℝ) ≤ (Nat.choose NR uB : ℝ) := by
      exact_mod_cast hred_card
    rw [hpair_card, Nat.cast_mul]
    exact mul_le_mul hblue_card_real hred_card_real
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hweight_sum :
      (Finset.univ : Finset PairIndex).sum
          (fun b =>
            (Finset.univ : Finset BranchLabel).sum
              (fun β =>
                (Finset.univ : Finset TranscriptIndex).sum
                  (fun τ => liftedWeight b β τ)))
        ≤
        prob hist * rhs := by
    calc
      (Finset.univ : Finset PairIndex).sum
          (fun b =>
            (Finset.univ : Finset BranchLabel).sum
              (fun β =>
                (Finset.univ : Finset TranscriptIndex).sum
                  (fun τ => liftedWeight b β τ)))
        ≤
          (Finset.univ : Finset PairIndex).sum
            (fun _b => prob hist * pairMass) := by
          exact Finset.sum_le_sum (by
            intro b hb
            exact hinner_sum_bound b)
      _ =
          (Fintype.card PairIndex : ℝ) * (prob hist * pairMass) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
      _ ≤
          ((Nat.choose NB uR : ℝ) * (Nat.choose NR uB : ℝ)) *
            (prob hist * pairMass) := by
          exact mul_le_mul_of_nonneg_right hpair_card_bound
            (mul_nonneg (hprob_nonneg hist) hpairMass_nonneg)
      _ = prob hist * rhs := by
          ring
  have hraw :
      prob (fun ω : Ω => target ω ∧ hist ω) ≤ prob hist * rhs := by
    exact
      FixedSetHistoryCellBranchTranscriptSummation
        (n := n) (m := m) (p := p) (M := prob hist * rhs)
        hist target liftedCellEvent liftedWeight hp0 hp1
        (mul_nonneg (hprob_nonneg hist) hrhs_nonneg)
        hlifted_cover hlifted_weight_nonneg hlifted_cell_bound hweight_sum
  by_cases hden_zero : prob hist = 0
  · have hcond_zero :
        TwoBiteConditionalProbability n m p target hist = 0 := by
      simp [TwoBiteConditionalProbability, prob, hden_zero]
    simpa [hcond_zero] using hrhs_nonneg
  · have hden_pos : 0 < prob hist :=
      lt_of_le_of_ne (hprob_nonneg hist) (Ne.symm hden_zero)
    have hraw' :
        prob (fun ω : Ω => target ω ∧ hist ω) ≤ rhs * prob hist := by
      simpa [mul_comm] using hraw
    have hdiv :
        prob (fun ω : Ω => target ω ∧ hist ω) / prob hist ≤ rhs :=
      (div_le_iff₀ hden_pos).mpr hraw'
    simpa [TwoBiteConditionalProbability, prob, hden_zero] using hdiv
