import Tablet.WithHighProbability
import Tablet.WithinRelativeError
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.FiberAndDegreeBaseDegreeConcentration
import Tablet.FiberAndDegreeLiftedSizeFixedVertexProbability
import Tablet.FiberAndDegreeLiftedSizeFixedVertexTail
import Tablet.FiberAndDegreeLiftedSizeImageHypergeometricTail
import Tablet.NaturalReducedVertexEdgeMassNegligible
import Tablet.HypergeometricMgfComparison
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular

open Filter

-- [TABLET NODE: FiberAndDegreeLiftedSizeConcentration]

theorem FiberAndDegreeLiftedSizeConcentration :
    ∀ η β : ℝ, 0 < η → β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                ∀ x : TwoBiteBaseVertex (m n),
                  WithinRelativeError η
                    (TwoBiteEdgeProbability β n * (n : ℝ))
                    ((TwoBiteLiftedNeighborhood ω x).card : ℝ))) := by
-- BODY
  intro η β hη hβ m hm
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
  have hthreeδ_le_eta : 3 * δ ≤ η := by
    nlinarith [hδ_le_eta8]
  let p_fn : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p_fn n) → Prop :=
    fun n ω =>
      ∀ x : TwoBiteBaseVertex (m n),
        WithinRelativeError η (p_fn n * (n : ℝ))
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ)
  let R : ∀ n : ℕ, TwoBiteSample n (m n) (p_fn n) → Prop :=
    fun n ω =>
      (∀ r : Fin (m n),
        WithinRelativeError δ (p_fn n * (m n : ℝ))
          (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
      (∀ b : Fin (m n),
        WithinRelativeError δ (p_fn n * (m n : ℝ))
          (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ))
  have hR :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p_fn n) (R n)) := by
    simpa [R, p_fn] using
      (FiberAndDegreeBaseDegreeConcentration δ β hδ_pos hβ m hm)
  have hp_bounds :
      ∀ᶠ n in Filter.atTop,
        0 ≤ p_fn n ∧ p_fn n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hp
    simpa [p_fn, hβ] using hp
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p_fn n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [hp_bounds] with n hp ω
    exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  let lowerExp : ℝ := δ + (1 - δ) * Real.log (1 - δ)
  let upperExp : ℝ := (1 + δ) * Real.log (1 + δ) - δ
  let cL : ℝ := lowerExp * (1 - δ)
  let cU : ℝ := upperExp * (1 - δ)
  have hchernoff := ChernoffFiberTailExponentsPositive δ hδ_pos hδ_le_half
  have hlowerExp_pos : 0 < lowerExp := by simpa [lowerExp] using hchernoff.2
  have hupperExp_pos : 0 < upperExp := by simpa [upperExp] using hchernoff.1
  have hone_sub_pos : 0 < (1 - δ : ℝ) := by linarith
  have hcL_pos : 0 < cL := by
    dsimp [cL]
    positivity
  have hcU_pos : 0 < cU := by
    dsimp [cU]
    positivity
  have htailL :
      Tendsto
        (fun n : ℕ =>
          (m n : ℝ) * Real.exp (-(cL * (p_fn n * (n : ℝ)))))
        Filter.atTop (nhds 0) := by
    simpa [p_fn, hβ] using
      (NaturalReducedVertexEdgeMassNegligible cL hcL_pos m hm)
  have htailU :
      Tendsto
        (fun n : ℕ =>
          (m n : ℝ) * Real.exp (-(cU * (p_fn n * (n : ℝ)))))
        Filter.atTop (nhds 0) := by
    simpa [p_fn, hβ] using
      (NaturalReducedVertexEdgeMassNegligible cU hcU_pos m hm)
  have hEnvelope_tendsto :
      Tendsto
        (fun n : ℕ =>
          2 * ((m n : ℝ) * Real.exp (-(cL * (p_fn n * (n : ℝ)))) +
            (m n : ℝ) * Real.exp (-(cU * (p_fn n * (n : ℝ))))))
        Filter.atTop (nhds 0) := by
    simpa using (htailL.add htailU).const_mul (2 : ℝ)
  have htotal_event := TwoBiteNaturalTotalMassOneEventually β hβ m hm
  have hBad :
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ R n ω)) := by
    unfold NegligibleProbability
    have hbad_nonneg :
        ∀ᶠ n in Filter.atTop,
          0 ≤ TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ R n ω) := by
      filter_upwards [hweight] with n hnw
      unfold TwoBiteEventProbability
      apply Finset.sum_nonneg
      intro ω hω
      exact hnw ω
    have hbad_bound :
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (p_fn n)
            (fun ω => ¬ Good n ω ∧ R n ω)
          ≤
          2 * ((m n : ℝ) * Real.exp (-(cL * (p_fn n * (n : ℝ)))) +
            (m n : ℝ) * Real.exp (-(cU * (p_fn n * (n : ℝ))))) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ), htotal_event, hp_bounds]
        with n hn_ge_one htotal_n hp_n
      let M := m n
      let p := p_fn n
      let target : ℝ := p * (n : ℝ)
      let C : ℝ :=
        Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) *
          ((1 - δ) * target)) +
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) *
          ((1 - δ) * target)))
      let BadX : TwoBiteBaseVertex M → TwoBiteSample n M p → Prop :=
        fun x ω =>
          (match x with
          | Sum.inl r =>
              WithinRelativeError δ (p * (M : ℝ))
                (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)
          | Sum.inr b =>
              WithinRelativeError δ (p * (M : ℝ))
                (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)) ∧
          ¬ WithinRelativeError (3 * δ) target
            ((TwoBiteLiftedNeighborhood ω x).card : ℝ)
      have hsupport : n ≤ M * M := by simpa [M] using htotal_n.1
      have hM_pos_nat : 0 < M := by
        by_contra hzero
        have hM0 : M = 0 := Nat.eq_zero_of_not_pos hzero
        have hn0 : n = 0 := by
          have hs : n ≤ 0 := by simpa [M, hM0] using hsupport
          exact Nat.eq_zero_of_le_zero hs
        omega
      have htarget_nonneg : 0 ≤ target := by
        dsimp [target]
        exact mul_nonneg hp_n.1 (Nat.cast_nonneg n)
      have prob_mono :
          ∀ {A B : TwoBiteSample n M p → Prop},
            (∀ ω, A ω → B ω) →
            TwoBiteEventProbability n M p A ≤ TwoBiteEventProbability n M p B := by
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
          ∀ ω : TwoBiteSample n M p,
            (¬ Good n (by simpa [M, p] using ω) ∧ R n (by simpa [M, p] using ω)) →
              ∃ x : TwoBiteBaseVertex M, BadX x ω := by
        intro ω hω
        rcases hω with ⟨hnotGood, hregular⟩
        dsimp [Good] at hnotGood
        push Not at hnotGood
        rcases hnotGood with ⟨x, hx_bad_eta⟩
        refine ⟨x, ?_⟩
        have hbad_three :
            ¬ WithinRelativeError (3 * δ) target
              ((TwoBiteLiftedNeighborhood ω x).card : ℝ) := by
          intro hthree
          apply hx_bad_eta
          unfold WithinRelativeError at hthree ⊢
          exact le_trans hthree
            (mul_le_mul_of_nonneg_right hthreeδ_le_eta htarget_nonneg)
        cases x with
        | inl r =>
            constructor
            · dsimp [R] at hregular
              simpa [M, p, target] using hregular.1 r
            · simpa [BadX, target] using hbad_three
        | inr b =>
            constructor
            · dsimp [R] at hregular
              simpa [M, p, target] using hregular.2 b
            · simpa [BadX, target] using hbad_three
      have hbad_union :
          TwoBiteEventProbability n M p
            (fun ω => ¬ Good n (by simpa [M, p] using ω) ∧
              R n (by simpa [M, p] using ω))
          ≤ ∑ x : TwoBiteBaseVertex M,
              TwoBiteEventProbability n M p (BadX x) := by
        exact le_trans (prob_mono hbad_to_exists)
          (TwoBiteEventProbabilityUnionBound hp_n.1 hp_n.2 BadX)
      have hside_bound :
          ∀ x : TwoBiteBaseVertex M,
            TwoBiteEventProbability n M p (BadX x) ≤ C := by
        intro x
        cases x with
        | inl r =>
            have htail :=
              FiberAndDegreeLiftedSizeFixedVertexProbability
                (n := n) (m := M) (p := p) (δ := δ)
                true r hsupport hM_pos_nat hp_n.1 hp_n.2 hδ_pos hδ_le_half
            simpa [BadX, C, target] using htail
        | inr b =>
            have htail :=
              FiberAndDegreeLiftedSizeFixedVertexProbability
                (n := n) (m := M) (p := p) (δ := δ)
                false b hsupport hM_pos_nat hp_n.1 hp_n.2 hδ_pos hδ_le_half
            simpa [BadX, C, target] using htail
      have hsum_bound :
          (∑ x : TwoBiteBaseVertex M,
              TwoBiteEventProbability n M p (BadX x))
          ≤ (Fintype.card (TwoBiteBaseVertex M) : ℝ) * C := by
        calc
          (∑ x : TwoBiteBaseVertex M,
              TwoBiteEventProbability n M p (BadX x))
              ≤ ∑ _x : TwoBiteBaseVertex M, C := by
                exact Finset.sum_le_sum (by intro x hx; exact hside_bound x)
          _ = (Fintype.card (TwoBiteBaseVertex M) : ℝ) * C := by
                simp [Finset.sum_const, nsmul_eq_mul]
      have hcard_base :
          (Fintype.card (TwoBiteBaseVertex M) : ℝ) = 2 * (M : ℝ) := by
        simp [TwoBiteBaseVertex, Fintype.card_sum]
        ring
      have hC_eq :
          C =
            Real.exp (-(cL * (p * (n : ℝ)))) +
              Real.exp (-(cU * (p * (n : ℝ)))) := by
        dsimp [C, cL, cU, lowerExp, upperExp, target]
        congr 1
        · ring_nf
        · ring_nf
      have hfinal_bound :
          (Fintype.card (TwoBiteBaseVertex M : Type) : ℝ) * C
          ≤ 2 * ((M : ℝ) * Real.exp (-(cL * (p * (n : ℝ)))) +
            (M : ℝ) * Real.exp (-(cU * (p * (n : ℝ))))) := by
        rw [hcard_base, hC_eq]
        ring_nf
        exact le_rfl
      simpa [M, p] using le_trans hbad_union (le_trans hsum_bound hfinal_bound)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hEnvelope_tendsto hbad_nonneg hbad_bound
  have hWHP :=
    WithHighProbabilityOfNegligibleBadOnRegular m p_fn Good R hR hBad hweight
  simpa [Good, p_fn] using hWHP
