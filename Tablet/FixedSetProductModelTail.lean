import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelMass
import Tablet.FixedSetProductModelVar
import Tablet.FixedSetFakeGraph
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.FixedSetProductModelTailPushforward
import Tablet.FixedSetProductModelTailMonotone
import Tablet.TwoBiteEventProbabilityNonnegative

open scoped Classical BigOperators

-- [TABLET NODE: FixedSetProductModelTail]

theorem FixedSetProductModelTail {n : ℕ} (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ}
    (h_hier : ParameterHierarchyEventualComparisons ε ε1 ε2 n0)
    (hn0 : n0 < n)
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (hm : m_sub = TwoBiteNaturalReducedVertexCount n)
    (hp : p_sub = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (t mu : ℝ)
    (hmean :
      let r_prod := 2 * m_sub
      let P_R := I.image (fun u => (π u).1)
      let P_B := I.image (fun u => (π u).2)
      let q := FixedSetProductModelMassFn p_sub P_R P_B
      let Z_prod := FixedSetProductModelVar I ε p_sub π
      Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
        (Finset.univ.prod (fun i => q (v i))) * Z_prod v) ≤ mu) :
    let r_prod := 2 * m_sub
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    let Z_I : TwoBiteSample n m_sub p_sub → ℝ := fun ω => by
      classical
      exact
        let P_R := I.image (TwoBiteRedProjection ω)
        let P_B := I.image (TwoBiteBlueProjection ω)
        let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
        let S_I_ext := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ P_I
        let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
        let Z_pairs := ext_pairs.filter (fun e =>
          TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧
          TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
        (Z_pairs.card : ℝ)
    TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ Z_I ω ≥ mu + t)
      ≤ (Finset.univ.filter (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
          Finset.univ.sum (fun v' => (Finset.univ.prod (fun i => q (v' i))) * Z_prod v') + t ≤ Z_prod v)).sum (fun v => Finset.univ.prod (fun i => q (v i))) * TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
-- BODY
  intros r_prod P_R P_B q Z_prod Z_I
  have hcomp := h_hier n hn0
  have hp0 : 0 ≤ p_sub := by
    dsimp [ParameterHierarchyEventualComparisons] at hcomp
    have h_ge : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := hcomp.2.1
    rw [hp, TwoBiteEdgeProbability]
    exact h_ge
  have hp1 : p_sub ≤ 1 := by
    dsimp [ParameterHierarchyEventualComparisons] at hcomp
    have h_le : (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) ≤ (1 / 2 : ℝ) := hcomp.2.2.1
    rw [hp, TwoBiteEdgeProbability]
    have h_half : (1 / 2 : ℝ) ≤ 1 := by norm_num
    exact le_trans h_le h_half
  rw [FixedSetProductModelTailPushforward I ε p_sub hp0 hp1 π (fun z => z ≥ mu + t)]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right
  · apply FixedSetProductModelTailMonotone p_sub hp0 hp1 P_R P_B
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    constructor
    · exact hv.1
    · linarith [hv.2, hmean]
  · apply TwoBiteEventProbabilityNonnegative hp0 hp1
