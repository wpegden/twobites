import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.FixedSetProductModelMass
import Tablet.FixedSetProductModelLipschitz
import Tablet.FixedSetProductModelExpectation
import Tablet.FixedSetProductModelTail
import Tablet.FixedSetProductModelConstants
import Tablet.FinalPairsCardLeHalfSq
import Tablet.GnpGraphWeight
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteSmallCutoff
import Tablet.TwoBiteX
import Tablet.UniformInjectionWeight

-- [TABLET NODE: FixedSetProductModelIngredients]

theorem FixedSetProductModelIngredients {n : ℕ} (I : Finset (Fin n))
    (ε ε1 ε2 : ℝ) {n0 : ℕ}
    (h_hier : ParameterHierarchyEventualComparisons ε ε1 ε2 n0)
    (hn0 : n0 < n)
    (hI : I.card = TwoBiteNaturalIndependenceScale (1 + ε) n) :
    let m_sub := TwoBiteNaturalReducedVertexCount n
    let p_sub := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let L := Real.log (n : ℝ)
    let K := (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ)
    let C := RealChooseTwo K
    let r_prod := 2 * m_sub
    let c_prod := (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε))
    let t : ℝ := C / Real.sqrt L
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
    let mu : TwoBiteSample n m_sub p_sub → ℝ := fun _ => C / (2 * L)
    ∀ π : Fin n ↪ (Fin m_sub × Fin m_sub),
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
      (q : α → ℝ) (Z_prod : (Fin r_prod → α) → ℝ),
      (∀ a, 0 ≤ q a) ∧
      (Finset.univ.sum q = 1) ∧
      0 < c_prod ∧
      0 ≤ t ∧
      (∀ i v v', (∀ j, j ≠ i → v j = v' j) → |Z_prod v - Z_prod v'| ≤ c_prod) ∧
      (Finset.univ.sum (fun v : Fin r_prod → α =>
          (Finset.univ.prod (fun i => q (v i))) * Z_prod v) ≤ C / (2 * L)) ∧
      TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ Z_I ω ≥ mu ω + t)
      ≤ (Finset.univ.filter (fun v : Fin r_prod → α =>
          Finset.univ.sum (fun v' : Fin r_prod → α => (Finset.univ.prod (fun i => q (v' i))) * Z_prod v') + t ≤ Z_prod v)).sum (fun v => Finset.univ.prod (fun i => q (v i))) * TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) := by
-- BODY
    intro m_sub p_sub L K C r_prod c_prod t Z_I mu π
    let α := Finset (Fin m_sub) × Finset (Fin m_sub)
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    refine ⟨α, inferInstance, inferInstance, q, Z_prod, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (FixedSetProductModelMass p_sub (h_hier n hn0).2.1 (le_trans (h_hier n hn0).2.2.1 (by norm_num)) P_R P_B).1
    · exact (FixedSetProductModelMass p_sub (h_hier n hn0).2.1 (le_trans (h_hier n hn0).2.2.1 (by norm_num)) P_R P_B).2
    · exact (FixedSetProductModelConstants ε (pos_of_gt hn0)).1
    · exact (FixedSetProductModelConstants ε (pos_of_gt hn0)).2
    · exact FixedSetProductModelLipschitz I ε p_sub π c_prod rfl
    · exact FixedSetProductModelExpectation I ε ε1 ε2 h_hier hn0 hI p_sub π rfl rfl C L rfl rfl
    · exact FixedSetProductModelTail I ε ε1 ε2 h_hier hn0 p_sub π rfl rfl t (C / (2 * L))
        (FixedSetProductModelExpectation I ε ε1 ε2 h_hier hn0 hI p_sub π rfl rfl C L rfl rfl)
