import Tablet.FiberAndDegreeEvent
import Tablet.GraphDegreeCount
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.WithinRelativeError
import Tablet.TwoBiteX

-- [TABLET NODE: HugeSameColorProjectionDegreeBound]

theorem HugeSameColorProjectionDegreeBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      FiberAndDegreeEvent ω ε2 →
      (∀ r : Fin m,
        (((TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω)).card : ℝ)
          ≤ 2 * p * (m : ℝ)) ∧
      (∀ b : Fin m,
        (((TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω)).card : ℝ)
          ≤ 2 * p * (m : ℝ)) := by
-- BODY
  classical
  intro n m p ω I ε ε1 ε2 n0 hcomparisons hn hm hp hfiber
  have hcomp := hcomparisons n hn
  dsimp [ParameterHierarchyEventualComparisons, TwoBiteEdgeProbability] at hcomp
  rcases hcomp with
    ⟨_hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      _h16, _h17, _h18, _h19, _h20, _h21, _heps2_nonneg, heps2_le,
      _h24, _hrest⟩
  have hpm_ge_one' : 1 ≤ 2 * p * (m : ℝ) := by
    simpa [TwoBiteEdgeProbability, hp, hm, mul_assoc] using hpm_ge_one
  have hpm_nonneg : 0 ≤ p * (m : ℝ) := by
    nlinarith only [hpm_ge_one']
  dsimp [FiberAndDegreeEvent] at hfiber
  rcases hfiber with
    ⟨_hredFiber, _hblueFiber, hredDegree, hblueDegree, _hredPair, _hbluePair,
      _hliftedDegree, _hredOverlap, _hblueOverlap, _hmixedOverlap,
      _hredOpposite, _hblueOpposite⟩
  refine ⟨?_, ?_⟩
  · intro r
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
      nlinarith only [heps2_le, hpm_nonneg]
    exact le_trans hcard (le_trans hdegree_upper htarget_upper)
  · intro b
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
      nlinarith only [heps2_le, hpm_nonneg]
    exact le_trans hcard (le_trans hdegree_upper htarget_upper)
