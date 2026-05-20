import Tablet.BlueFiber
import Tablet.RedFiber
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.WithHighProbability
import Tablet.WithinRelativeError
import Tablet.ChernoffFiberTailExponentsPositive
import Tablet.FiberAndDegreeFixedFiberTailProbability
import Tablet.FiberAndDegreeNaturalMeanWithinRelativeError
import Tablet.HypergeometricMgfComparison
import Tablet.FiberAndDegreeFiberSizeInjectionMarginal
import Tablet.FiberAndDegreeFiberSizeImageHypergeometricTail
import Tablet.FiberAndDegreeFiberSizeImageHypergeometricUpperTailChernoff
import Tablet.FiberAndDegreeFiberSizeImageHypergeometricLowerTail
import Tablet.NaturalReducedVertexExpLogSqNegligible
import Tablet.NegligibleProbability
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular

open Filter

-- [TABLET NODE: FiberAndDegreeFiberSizeConcentration]

theorem FiberAndDegreeFiberSizeConcentration :
  ∀ η : ℝ, 0 < η →
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                (∀ r : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) ∧
                (∀ b : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)))) := by
-- BODY
  intro η hη β hβ m hm
  classical
  let δ : ℝ := min (η / 8) (1 / 4)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by norm_num)
  have hδ_le_eta8 : δ ≤ η / 8 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_quarter : δ ≤ (1 / 4 : ℝ) := by
    dsimp [δ]
    exact min_le_right _ _
  have hδ_le_half : δ ≤ (1 / 2 : ℝ) := by linarith
  let cU : ℝ := (1 + δ) * Real.log (1 + δ) - δ
  let cL : ℝ := δ + (1 - δ) * Real.log (1 - δ)
  have hc_pos := ChernoffFiberTailExponentsPositive δ hδ_pos hδ_le_half
  have hcU_pos : 0 < cU := by simpa [cU] using hc_pos.1
  have hcL_pos : 0 < cL := by simpa [cL] using hc_pos.2
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      (∀ r : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2)
        ((RedFiber ω r).card : ℝ)) ∧
      (∀ b : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2)
        ((BlueFiber ω b).card : ℝ))
  let p_fn : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  have hp_bounds :
      ∀ᶠ n in Filter.atTop,
        0 ≤ TwoBiteEdgeProbability β n ∧ TwoBiteEdgeProbability β n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hp
    simpa [hβ] using hp
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n),
          0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [hp_bounds] with n hp ω
    exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  have htotal_event := TwoBiteNaturalTotalMassOneEventually β hβ m hm
  have hTrue :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p_fn n) (fun _ => True)) := by
    unfold WithHighProbability
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [htotal_event] with n hn
    simpa [p_fn] using hn.2.symm
  have hmean_event := FiberAndDegreeNaturalMeanWithinRelativeError δ hδ_pos m hm
  have htailU :
      Tendsto
        (fun n : ℕ => (m n : ℝ) *
          Real.exp (-(cU / 2) * (Real.log (n : ℝ)) ^ 2))
        Filter.atTop (nhds 0) :=
    NaturalReducedVertexExpLogSqNegligible (cU / 2) (by positivity) m hm
  have htailL :
      Tendsto
        (fun n : ℕ => (m n : ℝ) *
          Real.exp (-(cL / 2) * (Real.log (n : ℝ)) ^ 2))
        Filter.atTop (nhds 0) :=
    NaturalReducedVertexExpLogSqNegligible (cL / 2) (by positivity) m hm
  have hEnvelope_tendsto :
      Tendsto
        (fun n : ℕ =>
          2 * ((m n : ℝ) *
            Real.exp (-(cU / 2) * (Real.log (n : ℝ)) ^ 2) +
          (m n : ℝ) *
            Real.exp (-(cL / 2) * (Real.log (n : ℝ)) ^ 2)))
        Filter.atTop (nhds 0) := by
    simpa using (htailU.add htailL).const_mul (2 : ℝ)
  have hBad :
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ True)) := by
    unfold NegligibleProbability
    have hbad_nonneg :
        ∀ᶠ n in Filter.atTop,
          0 ≤ TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ True) := by
      filter_upwards [hweight] with n hnw
      unfold TwoBiteEventProbability
      apply Finset.sum_nonneg
      intro ω hω
      exact hnw ω
    have hbad_bound :
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ True)
          ≤
          2 * ((m n : ℝ) *
            Real.exp (-(cU / 2) * (Real.log (n : ℝ)) ^ 2) +
          (m n : ℝ) *
            Real.exp (-(cL / 2) * (Real.log (n : ℝ)) ^ 2)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ), htotal_event, hmean_event, hp_bounds]
        with n hn_ge_one htotal_n hmean_n hp_n
      let M := m n
      let L2 : ℝ := (Real.log (n : ℝ)) ^ 2
      let μ : ℝ := (n : ℝ) / (M : ℝ)
      have hsupport : n ≤ M * M := by simpa [M] using htotal_n.1
      have hM_pos_nat : 0 < M := by
        by_contra hzero
        have hM0 : M = 0 := Nat.eq_zero_of_not_pos hzero
        have hn0 : n = 0 := by
          have hs : n ≤ 0 := by simpa [M, hM0] using hsupport
          exact Nat.eq_zero_of_le_zero hs
        omega
      have hM_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos_nat
      have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
      have hmean_abs : |μ - L2| ≤ δ * L2 := by
        simpa [M, μ, L2] using hmean_n
      have hμ_lower : (1 / 2 : ℝ) * L2 ≤ μ := by
        have hlow_raw : L2 - μ ≤ δ * L2 := by
          have hneg := neg_le_abs (μ - L2)
          linarith
        have hδL2_le : δ * L2 ≤ (1 / 2 : ℝ) * L2 := by
          exact mul_le_mul_of_nonneg_right hδ_le_half hL2_nonneg
        linarith
      have hμ_lower_delta : (1 - δ) * L2 ≤ μ := by
        have hlow_raw : L2 - μ ≤ δ * L2 := by
          have hneg := neg_le_abs (μ - L2)
          linarith
        linarith
      have hμ_upper : μ ≤ (1 + δ) * L2 := by
        have hup_raw : μ - L2 ≤ δ * L2 := by
          exact le_trans (le_abs_self _) hmean_abs
        linarith
      have hUexp :
          Real.exp (-(cU * μ)) ≤
            Real.exp (-(cU / 2) * L2) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hμ_lower hcU_pos.le
        nlinarith
      have hLexp :
          Real.exp (-(cL * μ)) ≤
            Real.exp (-(cL / 2) * L2) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hμ_lower hcL_pos.le
        nlinarith
      let BadSide : Bool × Fin M → TwoBiteSample n M (p_fn n) → Prop :=
        fun sx ω =>
          ¬ WithinRelativeError η L2
            ((((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ))
      let UpperSide : Bool × Fin M → TwoBiteSample n M (p_fn n) → Prop :=
        fun sx ω =>
          (1 + δ) * μ <
            ((((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ))
      let LowerSide : Bool × Fin M → TwoBiteSample n M (p_fn n) → Prop :=
        fun sx ω =>
          ((((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ)) <
            (1 - δ) * μ
      have prob_mono :
          ∀ {A B : TwoBiteSample n M (p_fn n) → Prop},
            (∀ ω, A ω → B ω) →
            TwoBiteEventProbability n M (p_fn n) A ≤
              TwoBiteEventProbability n M (p_fn n) B := by
        intro A B hAB
        unfold TwoBiteEventProbability
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
            exact hAB ω hω)
          (by
            intro ω _ _
            exact TwoBiteSampleWeightNonnegative ω hp_n.1 hp_n.2)
      have hbad_to_exists :
          ∀ ω : TwoBiteSample n M (p_fn n),
            (¬ Good n (by simpa [M] using ω) ∧ True) →
              ∃ sx : Bool × Fin M, BadSide sx ω := by
        intro ω hω
        dsimp [Good] at hω
        have hbad := hω.1
        by_cases hredAll :
            ∀ r : Fin M, WithinRelativeError η L2 ((RedFiber ω r).card : ℝ)
        · have hnotBlue :
              ¬ ∀ b : Fin M, WithinRelativeError η L2 ((BlueFiber ω b).card : ℝ) := by
            intro hblueAll
            apply hbad
            constructor
            · simpa [M, L2] using hredAll
            · simpa [M, L2] using hblueAll
          push Not at hnotBlue
          rcases hnotBlue with ⟨b, hb⟩
          exact ⟨⟨false, b⟩, by simpa [BadSide, M, L2] using hb⟩
        · push Not at hredAll
          rcases hredAll with ⟨r, hr⟩
          exact ⟨⟨true, r⟩, by simpa [BadSide, M, L2] using hr⟩
      have hbad_union :
          TwoBiteEventProbability n M (p_fn n)
            (fun ω => ¬ Good n (by simpa [M] using ω) ∧ True)
          ≤ ∑ sx : Bool × Fin M,
              TwoBiteEventProbability n M (p_fn n) (BadSide sx) := by
        exact le_trans (prob_mono hbad_to_exists)
          (TwoBiteEventProbabilityUnionBound hp_n.1 hp_n.2 BadSide)
      have hside_bound :
          ∀ sx : Bool × Fin M,
            TwoBiteEventProbability n M (p_fn n) (BadSide sx)
              ≤ Real.exp (-(cU * μ)) + Real.exp (-(cL * μ)) := by
        intro sx
        have htail := FiberAndDegreeFixedFiberTailProbability
          (n := n) (m := M) (p := p_fn n) sx.1 sx.2 δ
          hsupport hM_pos_nat hδ_pos hδ_le_half
        have hbad_subset :
            ∀ ω : TwoBiteSample n M (p_fn n),
              BadSide sx ω → UpperSide sx ω ∨ LowerSide sx ω := by
          intro ω hbadω
          dsimp [BadSide, UpperSide, LowerSide] at hbadω ⊢
          unfold WithinRelativeError at hbadω
          have habs_gt : η * L2 <
              |((((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ)) - L2| :=
            not_le.mp hbadω
          rcases (lt_abs.mp habs_gt) with hupper_case | hlower_case
          · left
            have hη_upper :
                (1 + δ) * μ ≤ (1 + η) * L2 := by
              have hδ_sq : (1 + δ) * ((1 + δ) * L2) ≤ (1 + η) * L2 := by
                have hcoef : (1 + δ) * (1 + δ) ≤ 1 + η := by
                  have hd_nonneg : 0 ≤ δ := hδ_pos.le
                  nlinarith [hδ_le_eta8, hδ_le_quarter, hη]
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hL2_nonneg
              exact le_trans
                (mul_le_mul_of_nonneg_left hμ_upper (by linarith [hδ_pos] : 0 ≤ 1 + δ))
                (by simpa [mul_assoc] using hδ_sq)
            have hactual_gt : (1 + η) * L2 <
                (((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ) := by
              linarith
            exact lt_of_le_of_lt hη_upper hactual_gt
          · right
            have hη_lower :
                (1 - η) * L2 ≤ (1 - δ) * μ := by
              have hcoef : 1 - η ≤ (1 - δ) * (1 - δ) := by
                nlinarith [hδ_le_eta8, hδ_le_quarter]
              have hcoef_nonneg : 0 ≤ 1 - δ := by linarith
              calc
                (1 - η) * L2 ≤ ((1 - δ) * (1 - δ)) * L2 := by
                  exact mul_le_mul_of_nonneg_right hcoef hL2_nonneg
                _ = (1 - δ) * ((1 - δ) * L2) := by ring
                _ ≤ (1 - δ) * μ := by
                  exact mul_le_mul_of_nonneg_left
                    hμ_lower_delta
                    hcoef_nonneg
            have hactual_lt : (((if sx.1 then RedFiber ω sx.2 else BlueFiber ω sx.2).card : ℕ) : ℝ) <
                (1 - η) * L2 := by
              linarith
            exact lt_of_lt_of_le hactual_lt hη_lower
        have hsplit :
            TwoBiteEventProbability n M (p_fn n) (BadSide sx)
              ≤ TwoBiteEventProbability n M (p_fn n) (UpperSide sx) +
                TwoBiteEventProbability n M (p_fn n) (LowerSide sx) := by
          let E : Bool → TwoBiteSample n M (p_fn n) → Prop :=
            fun b ω => if b then UpperSide sx ω else LowerSide sx ω
          have hto : ∀ ω, BadSide sx ω → ∃ b, E b ω := by
            intro ω hω
            rcases hbad_subset ω hω with hu | hl
            · exact ⟨true, by simpa [E] using hu⟩
            · exact ⟨false, by simpa [E] using hl⟩
          calc
            TwoBiteEventProbability n M (p_fn n) (BadSide sx)
                ≤ TwoBiteEventProbability n M (p_fn n) (fun ω => ∃ b, E b ω) :=
                  prob_mono hto
            _ ≤ ∑ b : Bool, TwoBiteEventProbability n M (p_fn n) (E b) :=
                  TwoBiteEventProbabilityUnionBound hp_n.1 hp_n.2 E
            _ = TwoBiteEventProbability n M (p_fn n) (UpperSide sx) +
                TwoBiteEventProbability n M (p_fn n) (LowerSide sx) := by
                  simp [E]
        calc
          TwoBiteEventProbability n M (p_fn n) (BadSide sx)
              ≤ TwoBiteEventProbability n M (p_fn n) (UpperSide sx) +
                TwoBiteEventProbability n M (p_fn n) (LowerSide sx) := hsplit
          _ ≤ Real.exp (-(cU * μ)) + Real.exp (-(cL * μ)) := by
            refine add_le_add ?_ ?_
            · simpa [UpperSide, cU, μ] using htail.1
            · calc
                TwoBiteEventProbability n M (p_fn n) (LowerSide sx)
                    ≤ Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
                      simpa [LowerSide, μ] using htail.2
                _ = Real.exp (-(cL * μ)) := by
                      congr 1
                      simp [cL]
                      ring
      have hsum_bound :
          (∑ sx : Bool × Fin M,
              TwoBiteEventProbability n M (p_fn n) (BadSide sx))
          ≤ (Fintype.card (Bool × Fin M) : ℝ) *
              (Real.exp (-(cU * μ)) + Real.exp (-(cL * μ))) := by
        calc
          (∑ sx : Bool × Fin M,
              TwoBiteEventProbability n M (p_fn n) (BadSide sx))
              ≤ ∑ _sx : Bool × Fin M,
                  (Real.exp (-(cU * μ)) + Real.exp (-(cL * μ))) := by
                    exact Finset.sum_le_sum (by intro sx _; exact hside_bound sx)
          _ = (Fintype.card (Bool × Fin M) : ℝ) *
              (Real.exp (-(cU * μ)) + Real.exp (-(cL * μ))) := by
                simp [Finset.sum_const, nsmul_eq_mul]
                ring
      have hcard_bool : (Fintype.card (Bool × Fin M) : ℝ) = 2 * (M : ℝ) := by
        simp [Fintype.card_prod]
      have hM_nonneg : 0 ≤ (M : ℝ) := by
        exact Nat.cast_nonneg M
      have hbound_exp :
          (Fintype.card (Bool × Fin M) : ℝ) *
              (Real.exp (-(cU * μ)) + Real.exp (-(cL * μ)))
          ≤ 2 * ((M : ℝ) *
            Real.exp (-(cU / 2) * L2) +
          (M : ℝ) *
            Real.exp (-(cL / 2) * L2)) := by
        rw [hcard_bool]
        nlinarith [hUexp, hLexp, Real.exp_pos (-(cU * μ)),
          Real.exp_pos (-(cL * μ)),
          Real.exp_pos (-(cU / 2) * L2), Real.exp_pos (-(cL / 2) * L2),
          hM_nonneg]
      simpa [M, p_fn] using (le_trans hbad_union (le_trans hsum_bound hbound_exp))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hEnvelope_tendsto hbad_nonneg hbad_bound
  have hWHP := WithHighProbabilityOfNegligibleBadOnRegular m p_fn Good
    (fun n _ω => True) hTrue hBad hweight
  simpa [Good, p_fn] using hWHP
