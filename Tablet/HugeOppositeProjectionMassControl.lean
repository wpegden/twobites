import Tablet.FiberAndDegreeEvent
import Tablet.HugeFamilySizeBound
import Tablet.HugeOppositeProjectionLogSquareFromCutoff
import Tablet.HugeOppositeProjectionMassNumerics
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.ProjectionDeficitFromSubset
import Tablet.ProjectionDeficitFromHugeFamilyEstimates
import Tablet.ProjectionFiberCardBound
import Tablet.ProjectionMassBoundFromEstimates
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteX

-- [TABLET NODE: HugeOppositeProjectionMassControl]

theorem HugeOppositeProjectionMassControl : by
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
        let redMass : ℝ :=
          ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeRed).sum
            (fun x =>
              (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
        let blueMass : ℝ :=
          ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeBlue).sum
            (fun x =>
              (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ))
        let redDeficit : ℝ :=
          (k : ℝ) - ((I.image (TwoBiteRedProjection ω)).card : ℝ)
        let blueDeficit : ℝ :=
          (k : ℝ) - ((I.image (TwoBiteBlueProjection ω)).card : ℝ)
        let blockScale : ℝ := p * (n : ℝ)
        (∀ x : TwoBiteBaseVertex m, hugeRed x →
            (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ) ≤
              (1 + ε2) * blockScale) ∧
          redMass ≤ (1 + ε2) * redDeficit ∧
          RealChooseTwo redMass ≤
            (1 + ε1) * RealChooseTwo redDeficit ∧
          (redMass ≤ (1 + ε2) * blockScale →
            RealChooseTwo redMass ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (redDeficit - blockScale))) ∧
          ((1 + ε2) * blockScale ≤ redMass →
            RealChooseTwo ((1 + ε2) * blockScale) +
                RealChooseTwo (redMass - (1 + ε2) * blockScale) ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (redDeficit - blockScale))) ∧
          (∀ x : TwoBiteBaseVertex m, hugeBlue x →
            (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ) ≤
              (1 + ε2) * blockScale) ∧
          blueMass ≤ (1 + ε2) * blueDeficit ∧
          RealChooseTwo blueMass ≤
            (1 + ε1) * RealChooseTwo blueDeficit ∧
          (blueMass ≤ (1 + ε2) * blockScale →
            RealChooseTwo blueMass ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale))) ∧
          ((1 + ε2) * blockScale ≤ blueMass →
            RealChooseTwo ((1 + ε2) * blockScale) +
                RealChooseTwo (blueMass - (1 + ε2) * blockScale) ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale))) := by
-- BODY
  classical
  intro n m k p ω I ε ε1 ε2 n0 hε1 hcomparisons hn hm hp hk hI hfiber
  let hugeRed : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
  let hugeBlue : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
  let redMass : ℝ :=
    ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeRed).sum
      (fun x =>
        (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card : ℝ))
  let blueMass : ℝ :=
    ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeBlue).sum
      (fun x =>
        (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ))
  let redDeficit : ℝ :=
    (k : ℝ) - ((I.image (TwoBiteRedProjection ω)).card : ℝ)
  let blueDeficit : ℝ :=
    (k : ℝ) - ((I.image (TwoBiteBlueProjection ω)).card : ℝ)
  let blockScale : ℝ := p * (n : ℝ)
  dsimp only
  have hfiber_event : FiberAndDegreeEvent ω ε2 := hfiber
  dsimp [FiberAndDegreeEvent] at hfiber
  rcases hfiber with
    ⟨hredFiber, hblueFiber, hredDegree, hblueDegree, _hredPair,
      _hbluePair, hliftedDegree, hredOverlap, hblueOverlap,
      _hmixedOverlap, _hredOpposite, _hblueOpposite⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with ⟨_hxHuge, r, rfl⟩
    have hsubset :
        ((TwoBiteX ω I (Sum.inl r)).image (TwoBiteBlueProjection ω)) ⊆
          (TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
            (TwoBiteBlueProjection ω) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
      have hvLifted : v ∈ TwoBiteLiftedNeighborhood ω (Sum.inl r) := by
        simpa [TwoBiteX] using (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).2
      exact Finset.mem_image.mpr ⟨v, hvLifted, rfl⟩
    have himage_card :
        ((((TwoBiteX ω I (Sum.inl r)).image (TwoBiteBlueProjection ω)).card : ℝ) ≤
          (((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
              (TwoBiteBlueProjection ω)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsubset
    have himage_le_lifted :
        ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
            (TwoBiteBlueProjection ω)).card : ℝ) ≤
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r)).card : ℝ)) := by
      exact_mod_cast Finset.card_image_le
    have hlifted := hliftedDegree (Sum.inl r)
    unfold WithinRelativeError at hlifted
    have hlifted_upper :
        ((TwoBiteLiftedNeighborhood ω (Sum.inl r)).card : ℝ) ≤
          (1 + ε2) * (p * (n : ℝ)) := by
      have hdiff_le :
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r)).card : ℝ) -
              p * (n : ℝ) ≤ ε2 * (p * (n : ℝ)) :=
        le_trans (le_abs_self _) hlifted
      nlinarith only [hdiff_le]
    exact le_trans himage_card (le_trans himage_le_lifted hlifted_upper)
  · have hcomp := hcomparisons n hn
    dsimp [ParameterHierarchyEventualComparisons, TwoBiteEdgeProbability] at hcomp
    rcases hcomp with
      ⟨hm_pos, hp_nonneg_raw, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
        hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
        _h16, _h17, _h18, _h19, _h20, hscale, hε2_nonneg,
        hε2_le_one, hpm_le_t1, hC100_le_delta_t1_raw,
        _hC200_le_delta_t1_raw, _hC400_le_delta_t1_raw, _hrest⟩
    have hp_nonneg : 0 ≤ p := by
      simpa [TwoBiteEdgeProbability, hp] using hp_nonneg_raw
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      exact_mod_cast Nat.zero_le n
    have hblock_nonneg : 0 ≤ blockScale := by
      dsimp [blockScale]
      exact mul_nonneg hp_nonneg hn_nonneg
    have htwopm_sample_ge_one : 1 ≤ 2 * p * (m : ℝ) := by
      simpa [TwoBiteEdgeProbability, hp, hm] using hpm_ge_one
    have htwopm_le_delta_t1 :
        2 * p * (m : ℝ) ≤ (ε2 / 100) * TwoBiteHugeCutoff n := by
      simpa [TwoBiteEdgeProbability, hp, hm, TwoBiteHugeCutoff] using hpm_le_t1
    have ht1_ge_hundred : (100 : ℝ) ≤ TwoBiteHugeCutoff n := by
      have htwopm_le_cutoff :
          2 * p * (m : ℝ) ≤ (ε2 / 100) * TwoBiteHugeCutoff n := by
        simpa [TwoBiteEdgeProbability, hp, hm, TwoBiteHugeCutoff] using hpm_le_t1
      have hproduct_ge_one :
          1 ≤ (ε2 / 100) * TwoBiteHugeCutoff n :=
        le_trans htwopm_sample_ge_one htwopm_le_cutoff
      have hε2_over_nonneg : 0 ≤ ε2 / 100 := by
        nlinarith only [hε2_nonneg]
      have hε2_over_le : ε2 / 100 ≤ (1 : ℝ) / 100 := by
        nlinarith only [hε2_le_one]
      have ht1_pos : 0 < TwoBiteHugeCutoff n := by
        by_contra hnot
        have ht1_nonpos : TwoBiteHugeCutoff n ≤ 0 := le_of_not_gt hnot
        have hproduct_nonpos : (ε2 / 100) * TwoBiteHugeCutoff n ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hε2_over_nonneg ht1_nonpos
        linarith only [hproduct_ge_one, hproduct_nonpos]
      have hproduct_le :
          (ε2 / 100) * TwoBiteHugeCutoff n ≤
            ((1 : ℝ) / 100) * TwoBiteHugeCutoff n :=
        mul_le_mul_of_nonneg_right hε2_over_le ht1_pos.le
      nlinarith only [hproduct_ge_one, hproduct_le]
    have hblock_ge_one : 1 ≤ blockScale := by
      have hlog_sq_ge_two : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
        have hm_nat_pos : 0 < TwoBiteNaturalReducedVertexCount n := by
          exact_mod_cast hm_pos
        have hn_pos_nat : 0 < n := by
          by_contra hnot
          have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hnot
          subst n
          norm_num [TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount,
            TwoBiteStretch] at hm_nat_pos
        exact HugeOppositeProjectionLogSquareFromCutoff n hn_pos_nat ht1_ge_hundred
      have hm_half_ambient : 2 * (m : ℝ) ≤ (n : ℝ) := by
        have hm_le_reduced :
            (m : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
          simpa [hm] using hm_le
        have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hlog_sq_ge_two
        have htwo_m_le :
            2 * (m : ℝ) ≤
              2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hm_le_reduced (by norm_num)
        have htwo_n_le :
            (2 : ℝ) * (n : ℝ) ≤
              (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hlog_sq_ge_two hn_nonneg)
        have htwo_div_le :
            2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤ (n : ℝ) := by
          have hrewrite :
              2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) =
                ((2 : ℝ) * (n : ℝ)) / (Real.log (n : ℝ)) ^ 2 := by
            ring
          rw [hrewrite, div_le_iff₀ hlog_sq_pos]
          simpa [mul_comm, mul_left_comm, mul_assoc] using htwo_n_le
        exact le_trans htwo_m_le htwo_div_le
      have htwopm_le_block : 2 * p * (m : ℝ) ≤ blockScale := by
        have hmul : p * (2 * (m : ℝ)) ≤ p * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hm_half_ambient hp_nonneg
        calc
          2 * p * (m : ℝ) = p * (2 * (m : ℝ)) := by ring
          _ ≤ p * (n : ℝ) := hmul
          _ = blockScale := by
            dsimp [blockScale]
      exact le_trans htwopm_sample_ge_one htwopm_le_block
    have hε1_factor_nonneg : 0 ≤ 1 + ε1 := by
      linarith only [hε1]
    have hchoose_zero : RealChooseTwo (0 : ℝ) = 0 := by
      norm_num [RealChooseTwo]
    have hredMass_nonneg : 0 ≤ redMass := by
      dsimp [redMass]
      exact Finset.sum_nonneg (fun x _hx => by
        exact_mod_cast Nat.zero_le
          (((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card))
    have hredMass_nat : ∃ t : ℕ, redMass = t := by
      refine
        ⟨((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeRed).sum
            (fun x => ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)).card),
          ?_⟩
      dsimp [redMass]
      norm_num
    have hredProjection_card_le_k :
        (I.image (TwoBiteRedProjection ω)).card ≤ k := by
      calc
        (I.image (TwoBiteRedProjection ω)).card ≤ I.card :=
          Finset.card_image_le
        _ = k := hI
    have hredDeficit_nat : ∃ d : ℕ, redDeficit = d := by
      refine ⟨k - (I.image (TwoBiteRedProjection ω)).card, ?_⟩
      dsimp [redDeficit]
      exact (Nat.cast_sub (R := ℝ) hredProjection_card_le_k).symm
    have hchoose_nat_nonneg :
        ∀ {D : ℝ}, (∃ d : ℕ, D = d) → 0 ≤ RealChooseTwo D := by
      intro D hDnat
      rcases hDnat with ⟨d, hD⟩
      rw [hD]
      unfold RealChooseTwo
      by_cases hd_zero : d = 0
      · subst d
        norm_num
      by_cases hd_one : d = 1
      · subst d
        norm_num
      have hd_ge_two : 2 ≤ d := by omega
      have hd_nonneg_real : (0 : ℝ) ≤ d := by
        exact_mod_cast Nat.zero_le d
      have hd_minus_one_nonneg : 0 ≤ (d : ℝ) - 1 := by
        have hd_ge_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (by omega : 1 ≤ d)
        linarith only [hd_ge_one]
      have hprod : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) :=
        mul_nonneg hd_nonneg_real hd_minus_one_nonneg
      exact div_nonneg hprod (by norm_num)
    have hchoose_split_pair_nonneg :
        ∀ {D b : ℝ}, (∃ d : ℕ, D = d) → 0 ≤ b → 1 ≤ b →
          0 ≤ RealChooseTwo b + RealChooseTwo (D - b) := by
      intro D b hDnat hb_nonneg hb_ge_one
      rcases hDnat with ⟨d, hD⟩
      rw [hD]
      by_cases hd_zero : d = 0
      · subst d
        have hidentity :
            RealChooseTwo b + RealChooseTwo ((0 : ℝ) - b) = b ^ 2 := by
          unfold RealChooseTwo
          ring_nf
        have hnonneg : 0 ≤ RealChooseTwo b + RealChooseTwo ((0 : ℝ) - b) := by
          rw [hidentity]
          exact sq_nonneg b
        simpa using hnonneg
      by_cases hd_one : d = 1
      · subst d
        have hb_minus_one_nonneg : 0 ≤ b - 1 := by
          linarith only [hb_ge_one]
        have hprod : 0 ≤ b * (b - 1) :=
          mul_nonneg hb_nonneg hb_minus_one_nonneg
        have hidentity :
            RealChooseTwo b + RealChooseTwo ((1 : ℝ) - b) = b * (b - 1) := by
          unfold RealChooseTwo
          ring_nf
        have hnonneg : 0 ≤ RealChooseTwo b + RealChooseTwo ((1 : ℝ) - b) := by
          rw [hidentity]
          exact hprod
        simpa using hnonneg
      have hd_ge_two : 2 ≤ d := by omega
      have hd_nonneg_real : (0 : ℝ) ≤ d := by
        exact_mod_cast Nat.zero_le d
      have hd_minus_two_nonneg : 0 ≤ (d : ℝ) - 2 := by
        have hd_ge_two_real : (2 : ℝ) ≤ d := by
          exact_mod_cast hd_ge_two
        linarith only [hd_ge_two_real]
      have hprodD : 0 ≤ (d : ℝ) * ((d : ℝ) - 2) :=
        mul_nonneg hd_nonneg_real hd_minus_two_nonneg
      have hsquare : 0 ≤ (b - (d : ℝ) / 2) ^ 2 :=
        sq_nonneg (b - (d : ℝ) / 2)
      have htail_nonneg : 0 ≤ ((d : ℝ) * ((d : ℝ) - 2)) / 4 :=
        div_nonneg hprodD (by norm_num)
      have hidentity :
          RealChooseTwo b + RealChooseTwo ((d : ℝ) - b) =
            (b - (d : ℝ) / 2) ^ 2 + ((d : ℝ) * ((d : ℝ) - 2)) / 4 := by
        unfold RealChooseTwo
        ring_nf
      rw [hidentity]
      exact add_nonneg hsquare htail_nonneg
    have hbluePointwise :
        ∀ x : TwoBiteBaseVertex m, hugeBlue x →
          (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card : ℝ) ≤
            (1 + ε2) * blockScale := by
      intro x hx
      rcases hx with ⟨_hxHuge, b, rfl⟩
      have hsubset :
          ((TwoBiteX ω I (Sum.inr b)).image (TwoBiteRedProjection ω)) ⊆
            (TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
        have hvLifted : v ∈ TwoBiteLiftedNeighborhood ω (Sum.inr b) := by
          simpa [TwoBiteX] using (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).2
        exact Finset.mem_image.mpr ⟨v, hvLifted, rfl⟩
      have himage_card :
          ((((TwoBiteX ω I (Sum.inr b)).image (TwoBiteRedProjection ω)).card : ℝ) ≤
            (((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                (TwoBiteRedProjection ω)).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hsubset
      have himage_le_lifted :
          ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω)).card : ℝ) ≤
            ((TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ)) := by
        exact_mod_cast Finset.card_image_le
      have hlifted := hliftedDegree (Sum.inr b)
      unfold WithinRelativeError at hlifted
      have hlifted_upper :
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) ≤
            (1 + ε2) * (p * (n : ℝ)) := by
        have hdiff_le :
            ((TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) -
                p * (n : ℝ) ≤ ε2 * (p * (n : ℝ)) :=
          le_trans (le_abs_self _) hlifted
        nlinarith only [hdiff_le]
      simpa [blockScale] using
        le_trans himage_card (le_trans himage_le_lifted hlifted_upper)
    have hpm_nonneg : 0 ≤ p * (m : ℝ) := by
      nlinarith only [htwopm_sample_ge_one]
    have hredSameProjectionPointwise :
        ∀ r : Fin m,
          (((TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω)).card : ℝ)
            ≤ 2 * p * (m : ℝ) := by
      intro r
      have hsubset :
          ((TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω)) ⊆
            Finset.univ.filter (fun u : Fin m => (TwoBiteRedGraph ω).Adj r u) := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
        exact hv.2
      have hcard :
          ((((TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω)).card : ℝ) ≤
            (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) := by
        unfold GraphDegreeCount
        exact_mod_cast Finset.card_le_card hsubset
      have hdegree := hredDegree r
      unfold WithinRelativeError at hdegree
      have hdegree_upper :
          (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ) ≤
            (1 + ε2) * (p * (m : ℝ)) := by
        have hdiff_le :
            (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ) - p * (m : ℝ) ≤
              ε2 * (p * (m : ℝ)) :=
          le_trans (le_abs_self _) hdegree
        nlinarith only [hdiff_le]
      have htarget_upper :
          (1 + ε2) * (p * (m : ℝ)) ≤ 2 * p * (m : ℝ) := by
        nlinarith only [hε2_le_one, hpm_nonneg]
      exact le_trans hcard (le_trans hdegree_upper htarget_upper)
    have hblueSameProjectionPointwise :
        ∀ b : Fin m,
          (((TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω)).card : ℝ)
            ≤ 2 * p * (m : ℝ) := by
      intro b
      have hsubset :
          ((TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω)) ⊆
            Finset.univ.filter (fun u : Fin m => (TwoBiteBlueGraph ω).Adj b u) := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
        simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
        exact hv.2
      have hcard :
          ((((TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω)).card : ℝ) ≤
            (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)) := by
        unfold GraphDegreeCount
        exact_mod_cast Finset.card_le_card hsubset
      have hdegree := hblueDegree b
      unfold WithinRelativeError at hdegree
      have hdegree_upper :
          (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ) ≤
            (1 + ε2) * (p * (m : ℝ)) := by
        have hdiff_le :
            (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ) - p * (m : ℝ) ≤
              ε2 * (p * (m : ℝ)) :=
          le_trans (le_abs_self _) hdegree
        nlinarith only [hdiff_le]
      have htarget_upper :
          (1 + ε2) * (p * (m : ℝ)) ≤ 2 * p * (m : ℝ) := by
        nlinarith only [hε2_le_one, hpm_nonneg]
      exact le_trans hcard (le_trans hdegree_upper htarget_upper)
    have hredFiberUpper :
        ∀ r : Fin m,
          ((RedFiber ω r).card : ℝ) ≤
            2 * (Real.log (n : ℝ)) ^ 2 := by
      intro r
      have hf := hredFiber r
      unfold WithinRelativeError at hf
      have hbase_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
      have hdiff_le :
          ((RedFiber ω r).card : ℝ) -
              (Real.log (n : ℝ)) ^ 2 ≤
            ε2 * (Real.log (n : ℝ)) ^ 2 :=
        le_trans (le_abs_self _) hf
      have hupper :
          ((RedFiber ω r).card : ℝ) ≤
            (1 + ε2) * (Real.log (n : ℝ)) ^ 2 := by
        nlinarith only [hdiff_le]
      have hfactor :
          (1 + ε2) * (Real.log (n : ℝ)) ^ 2 ≤
            2 * (Real.log (n : ℝ)) ^ 2 := by
        nlinarith only [hε2_le_one, hbase_nonneg]
      exact le_trans hupper hfactor
    have hblueFiberUpper :
        ∀ b : Fin m,
          ((BlueFiber ω b).card : ℝ) ≤
            2 * (Real.log (n : ℝ)) ^ 2 := by
      intro b
      have hf := hblueFiber b
      unfold WithinRelativeError at hf
      have hbase_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
      have hdiff_le :
          ((BlueFiber ω b).card : ℝ) -
              (Real.log (n : ℝ)) ^ 2 ≤
            ε2 * (Real.log (n : ℝ)) ^ 2 :=
        le_trans (le_abs_self _) hf
      have hupper :
          ((BlueFiber ω b).card : ℝ) ≤
            (1 + ε2) * (Real.log (n : ℝ)) ^ 2 := by
        nlinarith only [hdiff_le]
      have hfactor :
          (1 + ε2) * (Real.log (n : ℝ)) ^ 2 ≤
            2 * (Real.log (n : ℝ)) ^ 2 := by
        nlinarith only [hε2_le_one, hbase_nonneg]
      exact le_trans hupper hfactor
    let hugeDeficitDelta : ℝ := ε2 / 100
    let hugeOverlapC : ℝ := 100 * (Real.log (n : ℝ)) ^ 3
    have hHugeDelta_nonneg : 0 ≤ hugeDeficitDelta := by
      dsimp [hugeDeficitDelta]
      nlinarith only [hε2_nonneg]
    have hn_pos_nat_for_log : 0 < n := by
      have hm_nat_pos : 0 < TwoBiteNaturalReducedVertexCount n := by
        exact_mod_cast hm_pos
      by_contra hnot
      have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hnot
      subst n
      norm_num [TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount,
        TwoBiteStretch] at hm_nat_pos
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg
        (by exact_mod_cast Nat.succ_le_of_lt hn_pos_nat_for_log)
    have hHugeOverlapC_nonneg : 0 ≤ hugeOverlapC := by
      dsimp [hugeOverlapC]
      exact mul_nonneg (by norm_num) (pow_nonneg hlog_nonneg 3)
    have hHugeC_loss_bound :
        (2 * (k : ℝ) / TwoBiteHugeCutoff n + 1) * hugeOverlapC ≤
          hugeDeficitDelta * TwoBiteHugeCutoff n := by
      dsimp [hugeOverlapC, hugeDeficitDelta]
      simpa [TwoBiteHugeCutoff, hk] using hC100_le_delta_t1_raw
    have hfullHuge_card_bound :
        ((((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
          (fun x => TwoBiteHugeClass ω I x)).card : ℝ)) ≤
            2 * (k : ℝ) / TwoBiteHugeCutoff n := by
      simpa using
        (HugeFamilySizeBound ω I ε ε1 ε2 hcomparisons hn hk hI
          hfiber_event).2
    have hblueMass_nonneg : 0 ≤ blueMass := by
      dsimp [blueMass]
      exact Finset.sum_nonneg (fun x _hx => by
        exact_mod_cast Nat.zero_le
          (((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card))
    have hblueMass_nat : ∃ t : ℕ, blueMass = t := by
      refine
        ⟨((Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeBlue).sum
            (fun x => ((TwoBiteX ω I x).image (TwoBiteRedProjection ω)).card),
          ?_⟩
      dsimp [blueMass]
      norm_num
    have hblueProjection_card_le_k :
        (I.image (TwoBiteBlueProjection ω)).card ≤ k := by
      calc
        (I.image (TwoBiteBlueProjection ω)).card ≤ I.card :=
          Finset.card_image_le
        _ = k := hI
    have hblueDeficit_nat : ∃ d : ℕ, blueDeficit = d := by
      refine ⟨k - (I.image (TwoBiteBlueProjection ω)).card, ?_⟩
      dsimp [blueDeficit]
      exact (Nat.cast_sub (R := ℝ) hblueProjection_card_le_k).symm
    have hblueRemainder :
        blueMass ≤ (1 + ε2) * blueDeficit ∧
          RealChooseTwo blueMass ≤
            (1 + ε1) * RealChooseTwo blueDeficit ∧
          (blueMass ≤ (1 + ε2) * blockScale →
            RealChooseTwo blueMass ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale))) ∧
          ((1 + ε2) * blockScale ≤ blueMass →
            RealChooseTwo ((1 + ε2) * blockScale) +
                RealChooseTwo (blueMass - (1 + ε2) * blockScale) ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale))) := by
      let blueHugeSet : Finset (TwoBiteBaseVertex m) :=
        (Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeBlue
      by_cases hblueHuge_empty : blueHugeSet = ∅
      · have hblueMass_zero : blueMass = 0 := by
          simp [blueMass, blueHugeSet, hblueHuge_empty]
        have hblueDeficit_nonneg : 0 ≤ blueDeficit := by
          rcases hblueDeficit_nat with ⟨d, hd⟩
          rw [hd]
          exact_mod_cast Nat.zero_le d
        have hfactor_nonneg : 0 ≤ 1 + ε2 := by
          nlinarith only [hε2_nonneg]
        have hblueMass_bound : blueMass ≤ (1 + ε2) * blueDeficit := by
          rw [hblueMass_zero]
          exact mul_nonneg hfactor_nonneg hblueDeficit_nonneg
        have hblueOneBlock :
            RealChooseTwo blueMass ≤
              (1 + ε1) * RealChooseTwo blueDeficit := by
          have hchoose_blue_nonneg : 0 ≤ RealChooseTwo blueDeficit :=
            hchoose_nat_nonneg hblueDeficit_nat
          have hright_nonneg :
              0 ≤ (1 + ε1) * RealChooseTwo blueDeficit :=
            mul_nonneg hε1_factor_nonneg hchoose_blue_nonneg
          calc
            RealChooseTwo blueMass = 0 := by
              rw [hblueMass_zero]
              exact hchoose_zero
            _ ≤ (1 + ε1) * RealChooseTwo blueDeficit := hright_nonneg
        refine ⟨hblueMass_bound, hblueOneBlock, ?_, ?_⟩
        · intro _hsmall
          have hpair_nonneg :
              0 ≤ RealChooseTwo blockScale +
                RealChooseTwo (blueDeficit - blockScale) :=
            hchoose_split_pair_nonneg hblueDeficit_nat hblock_nonneg hblock_ge_one
          have hright_nonneg :
              0 ≤ (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale)) :=
            mul_nonneg hε1_factor_nonneg hpair_nonneg
          calc
            RealChooseTwo blueMass = 0 := by
              rw [hblueMass_zero]
              exact hchoose_zero
            _ ≤
                (1 + ε1) *
                  (RealChooseTwo blockScale +
                    RealChooseTwo (blueDeficit - blockScale)) :=
              hright_nonneg
        · intro hlarge
          have hlarge_zero : (1 + ε2) * blockScale ≤ 0 := by
            rw [← hblueMass_zero]
            exact hlarge
          have hscaled_nonneg : 0 ≤ (1 + ε2) * blockScale :=
            mul_nonneg hfactor_nonneg hblock_nonneg
          have hscaled_zero : (1 + ε2) * blockScale = 0 :=
            le_antisymm hlarge_zero hscaled_nonneg
          have hfactor_ne_zero : 1 + ε2 ≠ 0 := by
            linarith only [hε2_nonneg]
          have hblock_zero : blockScale = 0 := by
            rcases (mul_eq_zero.mp hscaled_zero) with hfactor_zero | hblock_zero
            · exact False.elim (hfactor_ne_zero hfactor_zero)
            · exact hblock_zero
          have hleft_zero :
              RealChooseTwo ((1 + ε2) * blockScale) +
                  RealChooseTwo (blueMass - (1 + ε2) * blockScale) = 0 := by
            rw [hblueMass_zero, hscaled_zero]
            norm_num [RealChooseTwo]
          have hpair_nonneg :
              0 ≤ RealChooseTwo blockScale +
                RealChooseTwo (blueDeficit - blockScale) := by
            have hchoose_blue_nonneg : 0 ≤ RealChooseTwo blueDeficit :=
              hchoose_nat_nonneg hblueDeficit_nat
            rw [hblock_zero, sub_zero, hchoose_zero, zero_add]
            exact hchoose_blue_nonneg
          have hright_nonneg :
              0 ≤ (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (blueDeficit - blockScale)) :=
            mul_nonneg hε1_factor_nonneg hpair_nonneg
          calc
            RealChooseTwo ((1 + ε2) * blockScale) +
                RealChooseTwo (blueMass - (1 + ε2) * blockScale) = 0 :=
              hleft_zero
            _ ≤
                (1 + ε1) *
                  (RealChooseTwo blockScale +
                    RealChooseTwo (blueDeficit - blockScale)) :=
              hright_nonneg
      · have hblueHuge_nonempty : blueHugeSet.Nonempty := by
          exact Finset.nonempty_iff_ne_empty.mpr hblueHuge_empty
        rcases hblueHuge_nonempty with ⟨xBlue, hxBlueSet⟩
        have hxBlueHuge : hugeBlue xBlue := by
          simpa [blueHugeSet] using hxBlueSet
        rcases hxBlueHuge with ⟨hxBlueHugeClass, bBlue, rfl⟩
        have hblueWitness_subset_I :
            TwoBiteX ω I (Sum.inr bBlue) ⊆ I := by
          intro v hv
          exact (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).1
        have hblueDeficit_from_witness :
            (((TwoBiteX ω I (Sum.inr bBlue)).card : ℝ) -
                ((((TwoBiteX ω I (Sum.inr bBlue)).image
                    (TwoBiteBlueProjection ω)).card : ℝ))) ≤
              blueDeficit := by
          simpa [blueDeficit] using
            ProjectionDeficitFromSubset I (TwoBiteX ω I (Sum.inr bBlue))
              (TwoBiteBlueProjection ω) k hI hblueWitness_subset_I
        have hblueWitness_projection_le_delta :
            ((((TwoBiteX ω I (Sum.inr bBlue)).image
                (TwoBiteBlueProjection ω)).card : ℝ)) ≤
              (ε2 / 100) * TwoBiteHugeCutoff n :=
          le_trans (hblueSameProjectionPointwise bBlue) htwopm_le_delta_t1
        have hblueDeficit_ge : 98 ≤ blueDeficit := by
          have hdelta_le : ε2 / 100 ≤ (1 : ℝ) / 100 := by
            nlinarith only [hε2_le_one]
          have hcoef_ge : (99 : ℝ) / 100 ≤ 1 - ε2 / 100 := by
            nlinarith only [hdelta_le]
          have hcoef_nonneg : 0 ≤ 1 - ε2 / 100 := by
            nlinarith only [hdelta_le]
          have htarget_ge :
              (99 : ℝ) ≤ (1 - ε2 / 100) * TwoBiteHugeCutoff n := by
            have hmul :=
              mul_le_mul hcoef_ge ht1_ge_hundred
                (by norm_num : (0 : ℝ) ≤ 100) hcoef_nonneg
            norm_num at hmul
            exact hmul
          have hdeficit_gap_gt :
              (98 : ℝ) <
                ((TwoBiteX ω I (Sum.inr bBlue)).card : ℝ) -
                  ((((TwoBiteX ω I (Sum.inr bBlue)).image
                      (TwoBiteBlueProjection ω)).card : ℝ)) := by
            nlinarith only [hxBlueHugeClass.1, hblueWitness_projection_le_delta,
              htarget_ge]
          exact le_of_lt (lt_of_lt_of_le hdeficit_gap_gt hblueDeficit_from_witness)
        let blueSourceMass : ℝ :=
          blueHugeSet.sum (fun x => ((TwoBiteX ω I x).card : ℝ))
        have hblueSource_le_fiberMass :
            blueSourceMass ≤
              (2 * (Real.log (n : ℝ)) ^ 2) * blueMass := by
          have hpoint :
              ∀ x, x ∈ blueHugeSet →
                ((TwoBiteX ω I x).card : ℝ) ≤
                  (2 * (Real.log (n : ℝ)) ^ 2) *
                    (((TwoBiteX ω I x).image
                      (TwoBiteRedProjection ω)).card : ℝ) := by
            intro x hx
            have hxBlue : hugeBlue x := by
              simpa [blueHugeSet] using hx
            rcases hxBlue with ⟨_hxHuge, b, rfl⟩
            refine
              ProjectionFiberCardBound
                (TwoBiteX ω I (Sum.inr b)) (TwoBiteRedProjection ω)
                (2 * (Real.log (n : ℝ)) ^ 2) ?_
            intro r _hr
            have hfilter_subset :
                (TwoBiteX ω I (Sum.inr b)).filter
                    (fun v => TwoBiteRedProjection ω v = r) ⊆
                  RedFiber ω r := by
              intro v hv
              have hvr : TwoBiteRedProjection ω v = r :=
                (Finset.mem_filter.mp hv).2
              simp [RedFiber, hvr]
            have hcard :
                ((((TwoBiteX ω I (Sum.inr b)).filter
                    (fun v => TwoBiteRedProjection ω v = r)).card : ℝ) ≤
                  ((RedFiber ω r).card : ℝ)) := by
              exact_mod_cast Finset.card_le_card hfilter_subset
            exact le_trans hcard (hredFiberUpper r)
          calc
            blueSourceMass
                = blueHugeSet.sum
                    (fun x => ((TwoBiteX ω I x).card : ℝ)) := rfl
            _ ≤ blueHugeSet.sum
                  (fun x =>
                    (2 * (Real.log (n : ℝ)) ^ 2) *
                      (((TwoBiteX ω I x).image
                        (TwoBiteRedProjection ω)).card : ℝ)) := by
              exact Finset.sum_le_sum hpoint
            _ = (2 * (Real.log (n : ℝ)) ^ 2) * blueMass := by
              dsimp [blueMass, blueHugeSet]
              rw [← Finset.mul_sum]
        have hblueMass_bound : blueMass ≤ (1 + ε2) * blueDeficit := by
          have hblueMass_compress :
              (1 - ε2 / 100) * blueMass ≤ blueSourceMass := by
            have hblueMass_le_source : blueMass ≤ blueSourceMass := by
              calc
                blueMass =
                    blueHugeSet.sum
                      (fun x =>
                        (((TwoBiteX ω I x).image
                          (TwoBiteRedProjection ω)).card : ℝ)) := by
                  dsimp [blueMass, blueHugeSet]
                _ ≤ blueHugeSet.sum
                    (fun x => ((TwoBiteX ω I x).card : ℝ)) := by
                  exact Finset.sum_le_sum (fun x _hx => by
                    have hcard :
                        (((TwoBiteX ω I x).image
                          (TwoBiteRedProjection ω)).card) ≤
                          (TwoBiteX ω I x).card :=
                      Finset.card_image_le
                    exact_mod_cast hcard)
                _ = blueSourceMass := rfl
            have hscaled_le_mass :
                (1 - ε2 / 100) * blueMass ≤ blueMass := by
              nlinarith only [hblueMass_nonneg, hε2_nonneg]
            exact le_trans hscaled_le_mass hblueMass_le_source
          have hblueDeficit_linear :
              (1 - 2 * (ε2 / 100)) * blueSourceMass ≤ blueDeficit := by
            have hblueSet_subset_full :
                blueHugeSet ⊆
                  ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
                    (fun x => TwoBiteHugeClass ω I x)) := by
              intro x hx
              have hxBlue : hugeBlue x := by
                simpa [blueHugeSet] using hx
              simp [hxBlue.1]
            have hblueCard_bound :
                (blueHugeSet.card : ℝ) ≤
                  2 * (k : ℝ) / TwoBiteHugeCutoff n := by
              have hcard :
                  (blueHugeSet.card : ℝ) ≤
                    (((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
                      (fun x => TwoBiteHugeClass ω I x)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hblueSet_subset_full
              exact le_trans hcard hfullHuge_card_bound
            have hblueSize_lower :
                ∀ x, x ∈ blueHugeSet →
                  TwoBiteHugeCutoff n ≤ ((TwoBiteX ω I x).card : ℝ) := by
              intro x hx
              have hxBlue : hugeBlue x := by
                simpa [blueHugeSet] using hx
              exact le_of_lt hxBlue.1.1
            have hoverlap :
                ∀ x, x ∈ blueHugeSet → ∀ y, y ∈ blueHugeSet → x ≠ y →
                  (((TwoBiteX ω I x ∩ TwoBiteX ω I y).card : ℝ) ≤
                    hugeOverlapC) := by
              intro x hx y hy hxy
              have hxBlue : hugeBlue x := by
                simpa [blueHugeSet] using hx
              have hyBlue : hugeBlue y := by
                simpa [blueHugeSet] using hy
              rcases hxBlue with ⟨_hxHuge, b, rfl⟩
              rcases hyBlue with ⟨_hyHuge, c, rfl⟩
              have hbc : b ≠ c := by
                intro hbc
                apply hxy
                simp [hbc]
              have hsubset_inter :
                  TwoBiteX ω I (Sum.inr b) ∩ TwoBiteX ω I (Sum.inr c) ⊆
                    TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr c) := by
                intro v hv
                simp [TwoBiteX] at hv ⊢
                exact ⟨hv.1.2, hv.2.2⟩
              have hcard :
                  (((TwoBiteX ω I (Sum.inr b) ∩
                        TwoBiteX ω I (Sum.inr c)).card : ℝ) ≤
                    ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)) := by
                exact_mod_cast Finset.card_le_card hsubset_inter
              exact le_trans hcard
                (by simpa [hugeOverlapC] using hblueOverlap b c hbc)
            have hsameImage_point :
                ∀ x, x ∈ blueHugeSet →
                  ((((TwoBiteX ω I x).image
                    (TwoBiteBlueProjection ω)).card : ℝ) ≤
                    hugeDeficitDelta * ((TwoBiteX ω I x).card : ℝ)) := by
              intro x hx
              have hxBlue : hugeBlue x := by
                simpa [blueHugeSet] using hx
              rcases hxBlue with ⟨hxHuge, b, rfl⟩
              have hle_delta_t1 :
                  ((((TwoBiteX ω I (Sum.inr b)).image
                    (TwoBiteBlueProjection ω)).card : ℝ) ≤
                    hugeDeficitDelta * TwoBiteHugeCutoff n) := by
                simpa [hugeDeficitDelta] using
                  le_trans (hblueSameProjectionPointwise b)
                    htwopm_le_delta_t1
              have hdelta_t1_le_card :
                  hugeDeficitDelta * TwoBiteHugeCutoff n ≤
                    hugeDeficitDelta *
                      ((TwoBiteX ω I (Sum.inr b)).card : ℝ) :=
                mul_le_mul_of_nonneg_left (le_of_lt hxHuge.1)
                  hHugeDelta_nonneg
              exact le_trans hle_delta_t1 hdelta_t1_le_card
            have hsubsetI :
                ∀ x, x ∈ blueHugeSet → TwoBiteX ω I x ⊆ I := by
              intro x _hx v hv
              exact (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).1
            simpa [hugeDeficitDelta, hugeOverlapC, blueDeficit,
              blueSourceMass] using
              ProjectionDeficitFromHugeFamilyEstimates blueHugeSet I
                (fun x => TwoBiteX ω I x) (TwoBiteBlueProjection ω)
                k hugeDeficitDelta (TwoBiteHugeCutoff n) hugeOverlapC hI
                hsubsetI hblueSize_lower hoverlap hHugeDelta_nonneg
                hHugeOverlapC_nonneg hblueCard_bound hHugeC_loss_bound
                hsameImage_point
          exact
            ProjectionMassBoundFromEstimates
              (ε2 := ε2) (δ := ε2 / 100) (D := blueDeficit)
              (T := blueMass) (S := blueSourceMass)
              hε2_nonneg hε2_le_one rfl hblueMass_nonneg
              hblueMass_compress hblueDeficit_linear
        have hblueNumerics :=
          HugeOppositeProjectionMassNumerics
            (ε1 := ε1) (ε2 := ε2) (D := blueDeficit)
            (b := blockScale) (T := blueMass)
            hε1 hε2_nonneg hε2_le_one hscale hblueDeficit_ge hblock_nonneg
            hblueMass_nonneg hblueDeficit_nat hblueMass_nat hblueMass_bound
        exact
          ⟨hblueMass_bound, hblueNumerics.1, hblueNumerics.2.1,
            hblueNumerics.2.2⟩
    let redHugeSet : Finset (TwoBiteBaseVertex m) :=
      (Finset.univ : Finset (TwoBiteBaseVertex m)).filter hugeRed
    by_cases hredHuge_empty : redHugeSet = ∅
    · have hredMass_zero : redMass = 0 := by
        simp [redMass, redHugeSet, hredHuge_empty]
      have hredDeficit_nonneg : 0 ≤ redDeficit := by
        rcases hredDeficit_nat with ⟨d, hd⟩
        rw [hd]
        exact_mod_cast Nat.zero_le d
      have hfactor_nonneg : 0 ≤ 1 + ε2 := by
        nlinarith only [hε2_nonneg]
      have hredMass_bound : redMass ≤ (1 + ε2) * redDeficit := by
        rw [hredMass_zero]
        exact mul_nonneg hfactor_nonneg hredDeficit_nonneg
      have hredOneBlock :
          RealChooseTwo redMass ≤
            (1 + ε1) * RealChooseTwo redDeficit := by
        have hchoose_red_nonneg : 0 ≤ RealChooseTwo redDeficit :=
          hchoose_nat_nonneg hredDeficit_nat
        have hright_nonneg :
            0 ≤ (1 + ε1) * RealChooseTwo redDeficit :=
          mul_nonneg hε1_factor_nonneg hchoose_red_nonneg
        calc
          RealChooseTwo redMass = 0 := by
            rw [hredMass_zero]
            exact hchoose_zero
          _ ≤ (1 + ε1) * RealChooseTwo redDeficit := hright_nonneg
      refine ⟨hredMass_bound, hredOneBlock, ?_, ?_, ?_⟩
      · intro _hsmall
        have hpair_nonneg :
            0 ≤ RealChooseTwo blockScale +
              RealChooseTwo (redDeficit - blockScale) :=
          hchoose_split_pair_nonneg hredDeficit_nat hblock_nonneg hblock_ge_one
        have hright_nonneg :
            0 ≤ (1 + ε1) *
              (RealChooseTwo blockScale +
                RealChooseTwo (redDeficit - blockScale)) :=
          mul_nonneg hε1_factor_nonneg hpair_nonneg
        calc
          RealChooseTwo redMass = 0 := by
            rw [hredMass_zero]
            exact hchoose_zero
          _ ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (redDeficit - blockScale)) :=
            hright_nonneg
      · intro hlarge
        have hlarge_zero : (1 + ε2) * blockScale ≤ 0 := by
          rw [← hredMass_zero]
          exact hlarge
        have hscaled_nonneg : 0 ≤ (1 + ε2) * blockScale :=
          mul_nonneg hfactor_nonneg hblock_nonneg
        have hscaled_zero : (1 + ε2) * blockScale = 0 :=
          le_antisymm hlarge_zero hscaled_nonneg
        have hfactor_ne_zero : 1 + ε2 ≠ 0 := by
          linarith only [hε2_nonneg]
        have hblock_zero : blockScale = 0 := by
          rcases (mul_eq_zero.mp hscaled_zero) with hfactor_zero | hblock_zero
          · exact False.elim (hfactor_ne_zero hfactor_zero)
          · exact hblock_zero
        have hleft_zero :
            RealChooseTwo ((1 + ε2) * blockScale) +
                RealChooseTwo (redMass - (1 + ε2) * blockScale) = 0 := by
          rw [hredMass_zero, hscaled_zero]
          norm_num [RealChooseTwo]
        have hpair_nonneg :
            0 ≤ RealChooseTwo blockScale +
              RealChooseTwo (redDeficit - blockScale) := by
          have hchoose_red_nonneg : 0 ≤ RealChooseTwo redDeficit :=
            hchoose_nat_nonneg hredDeficit_nat
          rw [hblock_zero, sub_zero, hchoose_zero, zero_add]
          exact hchoose_red_nonneg
        have hright_nonneg :
            0 ≤ (1 + ε1) *
              (RealChooseTwo blockScale +
                RealChooseTwo (redDeficit - blockScale)) :=
          mul_nonneg hε1_factor_nonneg hpair_nonneg
        calc
          RealChooseTwo ((1 + ε2) * blockScale) +
              RealChooseTwo (redMass - (1 + ε2) * blockScale) = 0 :=
            hleft_zero
          _ ≤
              (1 + ε1) *
                (RealChooseTwo blockScale +
                  RealChooseTwo (redDeficit - blockScale)) :=
            hright_nonneg
      · refine ⟨hbluePointwise, ?_⟩
        exact hblueRemainder
    · have hredHuge_nonempty : redHugeSet.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr hredHuge_empty
      rcases hredHuge_nonempty with ⟨xRed, hxRedSet⟩
      have hxRedHuge : hugeRed xRed := by
        simpa [redHugeSet] using hxRedSet
      rcases hxRedHuge with ⟨hxRedHugeClass, rRed, rfl⟩
      have hredWitness_subset_I :
          TwoBiteX ω I (Sum.inl rRed) ⊆ I := by
        intro v hv
        exact (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).1
      have hredDeficit_from_witness :
          (((TwoBiteX ω I (Sum.inl rRed)).card : ℝ) -
              ((((TwoBiteX ω I (Sum.inl rRed)).image
                  (TwoBiteRedProjection ω)).card : ℝ))) ≤
            redDeficit := by
        simpa [redDeficit] using
          ProjectionDeficitFromSubset I (TwoBiteX ω I (Sum.inl rRed))
            (TwoBiteRedProjection ω) k hI hredWitness_subset_I
      have hredWitness_projection_le_delta :
          ((((TwoBiteX ω I (Sum.inl rRed)).image
              (TwoBiteRedProjection ω)).card : ℝ)) ≤
            (ε2 / 100) * TwoBiteHugeCutoff n :=
        le_trans (hredSameProjectionPointwise rRed) htwopm_le_delta_t1
      have hredDeficit_ge : 98 ≤ redDeficit := by
        have hdelta_le : ε2 / 100 ≤ (1 : ℝ) / 100 := by
          nlinarith only [hε2_le_one]
        have hcoef_ge : (99 : ℝ) / 100 ≤ 1 - ε2 / 100 := by
          nlinarith only [hdelta_le]
        have hcoef_nonneg : 0 ≤ 1 - ε2 / 100 := by
          nlinarith only [hdelta_le]
        have htarget_ge :
            (99 : ℝ) ≤ (1 - ε2 / 100) * TwoBiteHugeCutoff n := by
          have hmul :=
            mul_le_mul hcoef_ge ht1_ge_hundred
              (by norm_num : (0 : ℝ) ≤ 100) hcoef_nonneg
          norm_num at hmul
          exact hmul
        have hdeficit_gap_gt :
            (98 : ℝ) <
              ((TwoBiteX ω I (Sum.inl rRed)).card : ℝ) -
                ((((TwoBiteX ω I (Sum.inl rRed)).image
                    (TwoBiteRedProjection ω)).card : ℝ)) := by
          nlinarith only [hxRedHugeClass.1, hredWitness_projection_le_delta,
            htarget_ge]
        exact le_of_lt (lt_of_lt_of_le hdeficit_gap_gt hredDeficit_from_witness)
      let redSourceMass : ℝ :=
        redHugeSet.sum (fun x => ((TwoBiteX ω I x).card : ℝ))
      have hredSource_le_fiberMass :
          redSourceMass ≤
            (2 * (Real.log (n : ℝ)) ^ 2) * redMass := by
        have hpoint :
            ∀ x, x ∈ redHugeSet →
              ((TwoBiteX ω I x).card : ℝ) ≤
                (2 * (Real.log (n : ℝ)) ^ 2) *
                  (((TwoBiteX ω I x).image
                    (TwoBiteBlueProjection ω)).card : ℝ) := by
          intro x hx
          have hxRed : hugeRed x := by
            simpa [redHugeSet] using hx
          rcases hxRed with ⟨_hxHuge, r, rfl⟩
          refine
            ProjectionFiberCardBound
              (TwoBiteX ω I (Sum.inl r)) (TwoBiteBlueProjection ω)
              (2 * (Real.log (n : ℝ)) ^ 2) ?_
          intro b _hb
          have hfilter_subset :
              (TwoBiteX ω I (Sum.inl r)).filter
                  (fun v => TwoBiteBlueProjection ω v = b) ⊆
                BlueFiber ω b := by
            intro v hv
            have hvb : TwoBiteBlueProjection ω v = b :=
              (Finset.mem_filter.mp hv).2
            simp [BlueFiber, hvb]
          have hcard :
              ((((TwoBiteX ω I (Sum.inl r)).filter
                  (fun v => TwoBiteBlueProjection ω v = b)).card : ℝ) ≤
                ((BlueFiber ω b).card : ℝ)) := by
            exact_mod_cast Finset.card_le_card hfilter_subset
          exact le_trans hcard (hblueFiberUpper b)
        calc
          redSourceMass
              = redHugeSet.sum
                  (fun x => ((TwoBiteX ω I x).card : ℝ)) := rfl
          _ ≤ redHugeSet.sum
                (fun x =>
                  (2 * (Real.log (n : ℝ)) ^ 2) *
                    (((TwoBiteX ω I x).image
                      (TwoBiteBlueProjection ω)).card : ℝ)) := by
            exact Finset.sum_le_sum hpoint
          _ = (2 * (Real.log (n : ℝ)) ^ 2) * redMass := by
            dsimp [redMass, redHugeSet]
            rw [← Finset.mul_sum]
      have hredMass_bound : redMass ≤ (1 + ε2) * redDeficit := by
        have hredMass_compress :
            (1 - ε2 / 100) * redMass ≤ redSourceMass := by
          have hredMass_le_source : redMass ≤ redSourceMass := by
            calc
              redMass =
                  redHugeSet.sum
                    (fun x =>
                      (((TwoBiteX ω I x).image
                        (TwoBiteBlueProjection ω)).card : ℝ)) := by
                dsimp [redMass, redHugeSet]
              _ ≤ redHugeSet.sum
                  (fun x => ((TwoBiteX ω I x).card : ℝ)) := by
                exact Finset.sum_le_sum (fun x _hx => by
                  have hcard :
                      (((TwoBiteX ω I x).image
                        (TwoBiteBlueProjection ω)).card) ≤
                        (TwoBiteX ω I x).card :=
                    Finset.card_image_le
                  exact_mod_cast hcard)
              _ = redSourceMass := rfl
          have hscaled_le_mass :
              (1 - ε2 / 100) * redMass ≤ redMass := by
            nlinarith only [hredMass_nonneg, hε2_nonneg]
          exact le_trans hscaled_le_mass hredMass_le_source
        have hredDeficit_linear :
            (1 - 2 * (ε2 / 100)) * redSourceMass ≤ redDeficit := by
          have hredSet_subset_full :
              redHugeSet ⊆
                ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
                  (fun x => TwoBiteHugeClass ω I x)) := by
            intro x hx
            have hxRed : hugeRed x := by
              simpa [redHugeSet] using hx
            simp [hxRed.1]
          have hredCard_bound :
              (redHugeSet.card : ℝ) ≤
                2 * (k : ℝ) / TwoBiteHugeCutoff n := by
            have hcard :
                (redHugeSet.card : ℝ) ≤
                  (((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
                    (fun x => TwoBiteHugeClass ω I x)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hredSet_subset_full
            exact le_trans hcard hfullHuge_card_bound
          have hredSize_lower :
              ∀ x, x ∈ redHugeSet →
                TwoBiteHugeCutoff n ≤ ((TwoBiteX ω I x).card : ℝ) := by
            intro x hx
            have hxRed : hugeRed x := by
              simpa [redHugeSet] using hx
            exact le_of_lt hxRed.1.1
          have hoverlap :
              ∀ x, x ∈ redHugeSet → ∀ y, y ∈ redHugeSet → x ≠ y →
                (((TwoBiteX ω I x ∩ TwoBiteX ω I y).card : ℝ) ≤
                  hugeOverlapC) := by
            intro x hx y hy hxy
            have hxRed : hugeRed x := by
              simpa [redHugeSet] using hx
            have hyRed : hugeRed y := by
              simpa [redHugeSet] using hy
            rcases hxRed with ⟨_hxHuge, r, rfl⟩
            rcases hyRed with ⟨_hyHuge, s, rfl⟩
            have hrs : r ≠ s := by
              intro hrs
              apply hxy
              simp [hrs]
            have hsubset_inter :
                TwoBiteX ω I (Sum.inl r) ∩ TwoBiteX ω I (Sum.inl s) ⊆
                  TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                    TwoBiteLiftedNeighborhood ω (Sum.inl s) := by
              intro v hv
              simp [TwoBiteX] at hv ⊢
              exact ⟨hv.1.2, hv.2.2⟩
            have hcard :
                (((TwoBiteX ω I (Sum.inl r) ∩
                      TwoBiteX ω I (Sum.inl s)).card : ℝ) ≤
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)) := by
              exact_mod_cast Finset.card_le_card hsubset_inter
            exact le_trans hcard
              (by simpa [hugeOverlapC] using hredOverlap r s hrs)
          have hsameImage_point :
              ∀ x, x ∈ redHugeSet →
                ((((TwoBiteX ω I x).image
                  (TwoBiteRedProjection ω)).card : ℝ) ≤
                  hugeDeficitDelta * ((TwoBiteX ω I x).card : ℝ)) := by
            intro x hx
            have hxRed : hugeRed x := by
              simpa [redHugeSet] using hx
            rcases hxRed with ⟨hxHuge, r, rfl⟩
            have hle_delta_t1 :
                ((((TwoBiteX ω I (Sum.inl r)).image
                  (TwoBiteRedProjection ω)).card : ℝ) ≤
                  hugeDeficitDelta * TwoBiteHugeCutoff n) := by
              simpa [hugeDeficitDelta] using
                le_trans (hredSameProjectionPointwise r)
                  htwopm_le_delta_t1
            have hdelta_t1_le_card :
                hugeDeficitDelta * TwoBiteHugeCutoff n ≤
                  hugeDeficitDelta *
                    ((TwoBiteX ω I (Sum.inl r)).card : ℝ) :=
              mul_le_mul_of_nonneg_left (le_of_lt hxHuge.1)
                hHugeDelta_nonneg
            exact le_trans hle_delta_t1 hdelta_t1_le_card
          have hsubsetI :
              ∀ x, x ∈ redHugeSet → TwoBiteX ω I x ⊆ I := by
            intro x _hx v hv
            exact (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).1
          simpa [hugeDeficitDelta, hugeOverlapC, redDeficit,
            redSourceMass] using
            ProjectionDeficitFromHugeFamilyEstimates redHugeSet I
              (fun x => TwoBiteX ω I x) (TwoBiteRedProjection ω)
              k hugeDeficitDelta (TwoBiteHugeCutoff n) hugeOverlapC hI
              hsubsetI hredSize_lower hoverlap hHugeDelta_nonneg
              hHugeOverlapC_nonneg hredCard_bound hHugeC_loss_bound
              hsameImage_point
        exact
          ProjectionMassBoundFromEstimates
            (ε2 := ε2) (δ := ε2 / 100) (D := redDeficit)
            (T := redMass) (S := redSourceMass)
            hε2_nonneg hε2_le_one rfl hredMass_nonneg
            hredMass_compress hredDeficit_linear
      have hredNumerics :=
        HugeOppositeProjectionMassNumerics
          (ε1 := ε1) (ε2 := ε2) (D := redDeficit)
          (b := blockScale) (T := redMass)
          hε1 hε2_nonneg hε2_le_one hscale hredDeficit_ge hblock_nonneg
          hredMass_nonneg hredDeficit_nat hredMass_nat hredMass_bound
      refine ⟨hredMass_bound, hredNumerics.1, hredNumerics.2.1, hredNumerics.2.2, ?_⟩
      refine ⟨hbluePointwise, ?_⟩
      exact hblueRemainder
