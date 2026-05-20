import Tablet.ClosedPairsBound
import Tablet.FiberAndDegreeEvent
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.SmallClosedPairsFixedSetTail
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteSmallClosedPairsEvent

set_option maxHeartbeats 600000

-- [TABLET NODE: SmallClosedPairsBadEventProbability]

theorem SmallClosedPairsBadEventProbability :
    ∀ (ε ε1 ε2 β : ℝ) {n0 n m k : ℕ},
      ParameterHierarchy ε ε1 ε2 n0 →
      β = (1 / 2 : ℝ) →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      TwoBiteEventProbability n m (TwoBiteEdgeProbability β n)
        (fun ω =>
          FiberAndDegreeEvent ω ε2 ∧
            ¬ TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω)
        ≤ (n : ℝ)⁻¹ := by
-- BODY
  classical
  intro ε ε1 ε2 β n0 n m k hpar hβ hn hm hk
  subst β
  subst m
  subst k
  rcases hpar with ⟨_, _, _, _, _, _, _, _, hcomp⟩
  have hcomp_n := hcomp n hn
  have hp0 : 0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
    simpa [TwoBiteEdgeProbability] using hcomp_n.2.1
  have hp1 : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 := by
    have hp_half : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := by
      simpa [TwoBiteEdgeProbability] using hcomp_n.2.2.1
    exact le_trans hp_half (by norm_num)
  let K := TwoBiteNaturalIndependenceScale (1 + ε) n
  let M := TwoBiteNaturalReducedVertexCount n
  let p := TwoBiteEdgeProbability (1 / 2 : ℝ) n
  let idx : Finset (Finset (Fin n)) :=
    Finset.powersetCard K (Finset.univ : Finset (Fin n))
  let fixedBad : Finset (Fin n) → TwoBiteSample n M p → Prop :=
    fun I ω =>
      FiberAndDegreeEvent ω ε2 ∧
        ¬ ClosedPairsBound
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
          ε1 (K : ℝ)
  have hweight_nonneg :
      ∀ ω : TwoBiteSample n M p, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hprob_mono :
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
        exact hweight_nonneg ω)
  have hcover :
      ∀ ω : TwoBiteSample n M p,
        (FiberAndDegreeEvent ω ε2 ∧
          ¬ TwoBiteSmallClosedPairsEvent (k := K) ε ε1 ω) →
        ∃ I ∈ idx, fixedBad I ω := by
    intro ω hω
    rcases hω with ⟨hfiber, hsmall⟩
    simp only [TwoBiteSmallClosedPairsEvent, not_forall] at hsmall
    rcases hsmall with ⟨I, hIcard, hIbad⟩
    have hImem : I ∈ idx := by
      simp [idx, Finset.mem_powersetCard, hIcard]
    exact ⟨I, hImem, hfiber, hIbad⟩
  have hunion_bound :
      TwoBiteEventProbability n M p (fun ω => ∃ I ∈ idx, fixedBad I ω) ≤
        ∑ I ∈ idx, TwoBiteEventProbability n M p (fixedBad I) := by
    have hpoint :
        ∀ ω : TwoBiteSample n M p,
          (if (∃ I ∈ idx, fixedBad I ω) then TwoBiteSampleWeight ω else 0) ≤
            ∑ I ∈ idx, (if fixedBad I ω then TwoBiteSampleWeight ω else 0) := by
      intro ω
      by_cases h : ∃ I ∈ idx, fixedBad I ω
      · rcases h with ⟨I, hI, hfixed⟩
        have h_exists : ∃ I ∈ idx, fixedBad I ω := ⟨I, hI, hfixed⟩
        simp [h_exists]
        have hnonneg :
            ∀ J ∈ idx, 0 ≤ (if fixedBad J ω then TwoBiteSampleWeight ω else 0) := by
          intro J hJ
          by_cases hJbad : fixedBad J ω
          · rw [if_pos hJbad]
            exact hweight_nonneg ω
          · rw [if_neg hJbad]
        have hsingle :
            (if fixedBad I ω then TwoBiteSampleWeight ω else 0) ≤
              ∑ J ∈ idx, (if fixedBad J ω then TwoBiteSampleWeight ω else 0) :=
          Finset.single_le_sum hnonneg hI
        rwa [if_pos hfixed] at hsingle
      · simp [h]
        exact Finset.sum_nonneg (by
          intro I hI
          by_cases hIbad : fixedBad I ω
          · rw [if_pos hIbad]
            exact hweight_nonneg ω
          · rw [if_neg hIbad])
    have hsum :
        (∑ ω : TwoBiteSample n M p,
            (if (∃ I ∈ idx, fixedBad I ω) then TwoBiteSampleWeight ω else 0)) ≤
          ∑ I ∈ idx, ∑ ω : TwoBiteSample n M p,
            (if fixedBad I ω then TwoBiteSampleWeight ω else 0) := by
      calc
        (∑ ω : TwoBiteSample n M p,
            (if (∃ I ∈ idx, fixedBad I ω) then TwoBiteSampleWeight ω else 0))
          ≤ ∑ ω : TwoBiteSample n M p,
              ∑ I ∈ idx, (if fixedBad I ω then TwoBiteSampleWeight ω else 0) := by
            exact Finset.sum_le_sum (by intro ω _; exact hpoint ω)
        _ = ∑ I ∈ idx, ∑ ω : TwoBiteSample n M p,
              (if fixedBad I ω then TwoBiteSampleWeight ω else 0) := by
            rw [Finset.sum_comm]
    unfold TwoBiteEventProbability
    rw [Finset.sum_filter]
    convert hsum using 1
    · refine Finset.sum_congr rfl ?_
      intro ω hω
      by_cases h : ∃ I ∈ idx, fixedBad I ω <;> simp [h]
    · refine Finset.sum_congr rfl ?_
      intro I hI
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro ω hω
      by_cases h : fixedBad I ω <;> simp [h]
  have htail_each :
      ∀ I ∈ idx,
        TwoBiteEventProbability n M p (fixedBad I) ≤
          Real.exp
            (-(RealChooseTwo (K : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (M : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) := by
    intro I hI
    have hIcard : I.card = K := by
      simpa [idx, Finset.mem_powersetCard] using hI
    have htail :=
      SmallClosedPairsFixedSetTail
        (n := n) (m := M) (k := K) (p := p) I ε ε1 ε2 hcomp hn rfl rfl rfl hIcard
    simpa [fixedBad, M, p, K] using htail
  have hsum_tail :
      (∑ I ∈ idx, TwoBiteEventProbability n M p (fixedBad I)) ≤
        (Nat.choose n K : ℝ) *
          Real.exp
            (-(RealChooseTwo (K : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (M : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) := by
    calc
      (∑ I ∈ idx, TwoBiteEventProbability n M p (fixedBad I))
        ≤ ∑ I ∈ idx,
            Real.exp
              (-(RealChooseTwo (K : ℝ) ^ 2 /
                (Real.log (n : ℝ) * (M : ℝ) *
                  Real.rpow (n : ℝ) (8 * ε)))) := by
          exact Finset.sum_le_sum (by intro I hI; exact htail_each I hI)
      _ =
          (idx.card : ℝ) *
            Real.exp
              (-(RealChooseTwo (K : ℝ) ^ 2 /
                (Real.log (n : ℝ) * (M : ℝ) *
                  Real.rpow (n : ℝ) (8 * ε)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ =
          (Nat.choose n K : ℝ) *
            Real.exp
              (-(RealChooseTwo (K : ℝ) ^ 2 /
                (Real.log (n : ℝ) * (M : ℝ) *
                  Real.rpow (n : ℝ) (8 * ε)))) := by
          have hidx_card : idx.card = Nat.choose n K := by
            simp [idx, Finset.card_powersetCard]
          rw [hidx_card]
  have hmc :
      Real.exp
          (-(RealChooseTwo (K : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (M : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) *
        (Nat.choose n K : ℝ) ≤ (n : ℝ)⁻¹ := by
    rcases hcomp_n with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hmc, _⟩
    simpa [K, M] using hmc
  calc
    TwoBiteEventProbability n M p
        (fun ω =>
          FiberAndDegreeEvent ω ε2 ∧
            ¬ TwoBiteSmallClosedPairsEvent (k := K) ε ε1 ω)
      ≤ TwoBiteEventProbability n M p (fun ω => ∃ I ∈ idx, fixedBad I ω) :=
        hprob_mono hcover
    _ ≤ ∑ I ∈ idx, TwoBiteEventProbability n M p (fixedBad I) :=
        hunion_bound
    _ ≤
        (Nat.choose n K : ℝ) *
          Real.exp
            (-(RealChooseTwo (K : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (M : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) :=
        hsum_tail
    _ =
        Real.exp
            (-(RealChooseTwo (K : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (M : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) *
          (Nat.choose n K : ℝ) := by
        rw [mul_comm]
    _ ≤ (n : ℝ)⁻¹ := hmc
