import Tablet.FiberAndDegreeEvent
import Tablet.BlueFiber
import Tablet.RedFiber
import Tablet.GraphDegreeCount
import Tablet.GnpGraphWeight
import Tablet.WithHighProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight
import Tablet.OppositeProjectionCollisionBound
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.FiberAndDegreeOppositeProjectionFromCollision
import Tablet.FiberAndDegreeFiberToleranceTransfer
import Tablet.FiberAndDegreeBaseDegreeConcentration
import Tablet.FiberAndDegreeBaseCodegreeConcentration
import Tablet.FiberAndDegreeFiberSizeConcentration
import Tablet.FiberAndDegreeLiftedSizeConcentration
import Tablet.FiberAndDegreeLiftedIntersectionConcentration
import Tablet.FiberAndDegreeMixedLiftedIntersectionConcentration
import Tablet.HypergeometricMgfComparison
import Tablet.WithHighProbabilityThreeIntersection
import Tablet.TwoBiteEventProbabilityTotalMassBound

-- [TABLET NODE: FiberAndDegreeConcentration]

theorem FiberAndDegreeConcentration :
    ∀ ε2 β : ℝ, 0 < ε2 → β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω => FiberAndDegreeEvent ω ε2)) := by
-- BODY
  classical
  intro ε2 β hε2 hβ m hm
  have hOppositeCollision := OppositeProjectionCollisionBound β hβ m hm
  have hOppositeProjectionDet :
      ∀ n (ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n)),
        (∀ x : TwoBiteBaseVertex (m n),
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
            2 * TwoBiteEdgeProbability β n * (n : ℝ)) →
        (∀ r s : Fin (m n), r ≠ s →
          ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
            ≤ 100 * (Real.log (n : ℝ)) ^ 3) →
        (∀ b c : Fin (m n), b ≠ c →
          ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
            ≤ 100 * (Real.log (n : ℝ)) ^ 3) →
        (let sizeBound : Prop :=
            ∀ x : TwoBiteBaseVertex (m n),
            ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
              2 * TwoBiteEdgeProbability β n * (n : ℝ)
          let redBound : Prop :=
            ∀ r s : Fin (m n), r ≠ s →
            ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                  (TwoBiteBlueProjection ω)) ∩
                ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                  (TwoBiteBlueProjection ω))).card : ℝ)
              ≤
              (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                100 * (Real.log (n : ℝ)) ^ 3)
          let blueBound : Prop :=
            ∀ b c : Fin (m n), b ≠ c →
            ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                  (TwoBiteRedProjection ω)) ∩
                ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                  (TwoBiteRedProjection ω))).card : ℝ)
              ≤
              (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                100 * (Real.log (n : ℝ)) ^ 3)
          sizeBound → redBound ∧ blueBound) →
        (∀ r s : Fin (m n), r ≠ s →
          ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                (TwoBiteBlueProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                (TwoBiteBlueProjection ω))).card : ℝ)
            ≤ 2 * 100 * (Real.log (n : ℝ)) ^ 3) ∧
        (∀ b c : Fin (m n), b ≠ c →
          ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                (TwoBiteRedProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                (TwoBiteRedProjection ω))).card : ℝ)
            ≤ 2 * 100 * (Real.log (n : ℝ)) ^ 3) := by
    intro n ω hsize hRedIntersection hBlueIntersection hCollision
    exact FiberAndDegreeOppositeProjectionFromCollision ω hsize hRedIntersection hBlueIntersection hCollision

  let η : ℝ := min (ε2 / 10) (1 / 2)
  have hη_le_ε2 : η ≤ ε2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by linarith)
  have hη_le_half : η ≤ 1 / 2 := by
    dsimp [η]
    exact min_le_right _ _

  have hFiberTolerance :
      ∀ n (ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n)),
        (∀ r : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) →
        (∀ b : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)) →
        (∀ r : Fin (m n), WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) ∧
        (∀ b : Fin (m n), WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)) := by
    intro n ω hRed hBlue
    exact FiberAndDegreeFiberToleranceTransfer ω hη_le_ε2 hRed hBlue

  let fiberGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      (∀ r : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) ∧
      (∀ b : Fin (m n), WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ))

  let degreeGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      (∀ r : Fin (m n), WithinRelativeError ε2 (TwoBiteEdgeProbability β n * (m n : ℝ)) (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
      (∀ b : Fin (m n), WithinRelativeError ε2 (TwoBiteEdgeProbability β n * (m n : ℝ)) (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ))

  let baseCodegreeGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((Finset.univ.filter (fun t : Fin (m n) => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((Finset.univ.filter (fun t : Fin (m n) => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ 100 * Real.log (n : ℝ))

  let liftedSizeGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      ∀ x : TwoBiteBaseVertex (m n), WithinRelativeError η (TwoBiteEdgeProbability β n * (n : ℝ)) ((TwoBiteLiftedNeighborhood ω x).card : ℝ)

  let liftedIntersectionGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) ≤ 100 * (Real.log (n : ℝ)) ^ 3) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) ≤ 100 * (Real.log (n : ℝ)) ^ 3)

  let mixedLiftedIntersectionGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      ∀ r b, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) ≤ 100 * (Real.log (n : ℝ)) ^ 3

  let oppositeCollisionGood : ∀ n : ℕ, TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop :=
    fun n ω =>
      let sizeBound : Prop := ∀ x : TwoBiteBaseVertex (m n), ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (n : ℝ)
      let redBound : Prop := ∀ r s : Fin (m n), r ≠ s →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image (TwoBiteBlueProjection ω)) ∩
          ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image (TwoBiteBlueProjection ω))).card : ℝ) ≤
        (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) + 100 * (Real.log (n : ℝ)) ^ 3)
      let blueBound : Prop := ∀ b c : Fin (m n), b ≠ c →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image (TwoBiteRedProjection ω)) ∩
          ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image (TwoBiteRedProjection ω))).card : ℝ) ≤
        (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) + 100 * (Real.log (n : ℝ)) ^ 3)
      sizeBound → redBound ∧ blueBound

  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith) (by norm_num)
  have hFiber : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (fiberGood n)) := by
    exact FiberAndDegreeFiberSizeConcentration η hη_pos β hβ m hm
  have hDegree : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (degreeGood n)) := by
    simpa [degreeGood] using FiberAndDegreeBaseDegreeConcentration ε2 β hε2 hβ m hm
  have hBaseCodegree : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (baseCodegreeGood n)) := by
    simpa [baseCodegreeGood] using FiberAndDegreeBaseCodegreeConcentration β hβ m hm
  have hLiftedSize : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (liftedSizeGood n)) := by
    simpa [liftedSizeGood] using FiberAndDegreeLiftedSizeConcentration η β hη_pos hβ m hm
  have hLiftedIntersection : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (liftedIntersectionGood n)) := by
    simpa [liftedIntersectionGood] using FiberAndDegreeLiftedIntersectionConcentration β hβ m hm
  have hMixedLiftedIntersection : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (mixedLiftedIntersectionGood n)) := by
    simpa [mixedLiftedIntersectionGood] using FiberAndDegreeMixedLiftedIntersectionConcentration β hβ m hm

  have hOppositeCollisionGood : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (oppositeCollisionGood n)) := by
    simpa [oppositeCollisionGood] using hOppositeCollision

  have hprob_bounds :
      ∀ᶠ n in Filter.atTop,
        0 ≤ TwoBiteEdgeProbability β n ∧
          TwoBiteEdgeProbability β n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hn
    simpa [hβ] using hn

  have hweight : ∀ᶠ n in Filter.atTop, ∀ ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [hprob_bounds] with n hn
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hn.1 hn.2

  let p_fn := fun n => TwoBiteEdgeProbability β n
  let s1 := fiberGood
  let s2 := degreeGood
  let s3 := baseCodegreeGood
  let s4 := liftedSizeGood
  let s5 := liftedIntersectionGood
  let s6 := mixedLiftedIntersectionGood
  let s7 := oppositeCollisionGood

  have h123 := WithHighProbabilityThreeIntersection m p_fn s1 s2 s3 hFiber hDegree hBaseCodegree hweight
  have h456 := WithHighProbabilityThreeIntersection m p_fn s4 s5 s6 hLiftedSize hLiftedIntersection hMixedLiftedIntersection hweight
  have hAll := WithHighProbabilityThreeIntersection m p_fn
    (fun n ω => s1 n ω ∧ s2 n ω ∧ s3 n ω)
    (fun n ω => s4 n ω ∧ s5 n ω ∧ s6 n ω)
    s7 h123 h456 hOppositeCollisionGood hweight

  have prob_mono :
      ∀ {n : ℕ} {A B : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop},
        (∀ ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n), 0 ≤ TwoBiteSampleWeight ω) →
        (∀ ω, A ω → B ω) →
        TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) A ≤
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) B := by
    intro n A B hweight_n hAB
    classical
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro ω hω; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢; exact hAB ω hω)
      (by intro ω hωB hωnotA; exact hweight_n ω)

  have hUpperBound : ∀ᶠ n in Filter.atTop, TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (fun ω => FiberAndDegreeEvent ω ε2) ≤ (fun _ : ℕ => (1 : ℝ)) n := by
    filter_upwards [hweight] with n hwn
    exact le_trans
      (prob_mono hwn (by intro ω hω; trivial))
      (TwoBiteEventProbabilityTotalMassBound n (m n) (TwoBiteEdgeProbability β n))
  
  have hLowerBound : ∀ᶠ n in Filter.atTop, TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (fun ω => (s1 n ω ∧ s2 n ω ∧ s3 n ω) ∧ (s4 n ω ∧ s5 n ω ∧ s6 n ω) ∧ s7 n ω) ≤ TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) (fun ω => FiberAndDegreeEvent ω ε2) := by
    filter_upwards [hweight, hprob_bounds] with n hwn hp
    apply prob_mono hwn
    intro ω h
    have hF := h.1.1
    have hD := h.1.2.1
    have hBC := h.1.2.2
    have hLS := h.2.1.1
    have hLI := h.2.1.2.1
    have hMLI := h.2.1.2.2
    have hOC := h.2.2
    
    unfold FiberAndDegreeEvent
    have hFTol := hFiberTolerance n ω hF.1 hF.2
    have hpn_nonneg : 0 ≤ TwoBiteEdgeProbability β n * (n : ℝ) := by
      exact mul_nonneg hp.1 (Nat.cast_nonneg n)
    have hSizeBound : ∀ x : TwoBiteBaseVertex (m n), ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (n : ℝ) := by
      intro x
      have h1 := hLS x
      unfold WithinRelativeError at h1
      have hz1 : ((TwoBiteLiftedNeighborhood ω x).card : ℝ) - TwoBiteEdgeProbability β n * (n : ℝ) ≤ η * (TwoBiteEdgeProbability β n * (n : ℝ)) := le_trans (le_abs_self _) h1
      have hz2 : ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤ TwoBiteEdgeProbability β n * (n : ℝ) + η * (TwoBiteEdgeProbability β n * (n : ℝ)) := by linarith
      have hz3 : TwoBiteEdgeProbability β n * (n : ℝ) + η * (TwoBiteEdgeProbability β n * (n : ℝ)) = (1 + η) * (TwoBiteEdgeProbability β n * (n : ℝ)) := by ring
      have hz4 : (1 + η) * (TwoBiteEdgeProbability β n * (n : ℝ)) ≤ 2 * (TwoBiteEdgeProbability β n * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact hpn_nonneg
      linarith
    have hSizeBoundRel : ∀ x : TwoBiteBaseVertex (m n), WithinRelativeError ε2 (TwoBiteEdgeProbability β n * (n : ℝ)) ((TwoBiteLiftedNeighborhood ω x).card : ℝ) := by
      intro x
      have h1 := hLS x
      unfold WithinRelativeError at h1 ⊢
      have h2 : η * (TwoBiteEdgeProbability β n * (n : ℝ)) ≤ ε2 * (TwoBiteEdgeProbability β n * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact hη_le_ε2
        · exact hpn_nonneg
      linarith
    have hOppProj := hOppositeProjectionDet n ω hSizeBound hLI.1 hLI.2 hOC
    exact ⟨hFTol.1, hFTol.2, hD.1, hD.2, hBC.1, hBC.2, hSizeBoundRel, hLI.1, hLI.2, hMLI, hOppProj.1, hOppProj.2⟩

  unfold WithHighProbability at hAll ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hAll tendsto_const_nhds hLowerBound hUpperBound
