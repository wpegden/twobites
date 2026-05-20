import Mathlib.Analysis.SpecialFunctions.Exp
import Tablet.ParameterHierarchyLogPositivity
import Tablet.SumChooseBound
import Tablet.PairsInSetLeHalfProduct
import Tablet.FinalPairsCardLeHalfSq
import Tablet.FixedSetTailExponentInequality
import Tablet.BoundedDifferencesProduct
import Tablet.ClosedPairsBound
import Tablet.FiberAndDegreeEvent
import Tablet.GnpGraphWeight
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteSmallCutoff
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX
import Tablet.UniformInjectionWeight
import Tablet.FixedSetSmallClosedPairsTailImplication
import Tablet.FixedSetExternalTailBound

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000
-- [TABLET NODE: SmallClosedPairsFixedSetTail]

theorem SmallClosedPairsFixedSetTail :
    ∀ {n m k : ℕ} {p : ℝ} (I : Finset (Fin n))
      (ε ε1 ε2 : ℝ) {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      I.card = k →
      TwoBiteEventProbability n m p
        (fun ω =>
          FiberAndDegreeEvent ω ε2 ∧
            ¬ ClosedPairsBound
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteSmallClass ω ε I)).card : ℝ)
              ε1 (k : ℝ))
        ≤
          Real.exp
            (-(RealChooseTwo (k : ℝ) ^ 2 /
              (Real.log (n : ℝ) * (m : ℝ) *
                Real.rpow (n : ℝ) (8 * ε)))) := by
-- BODY
  rintro n m k p I ε ε1 ε2 n0 h_hier hn_lt rfl rfl rfl hI
  have hL : 0 < Real.log (n : ℝ) := ParameterHierarchyLogPositivity h_hier hn_lt
  
  -- Unfold the failure of ClosedPairsBound
  simp only [ClosedPairsBound, not_le]

  -- Introduce parameters L and C as in the proof
  let L := Real.log (n : ℝ)
  let K := (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ)
  -- C is binomial coefficient for k, which has been substituted
  let C := RealChooseTwo K

  -- Isolate the main probability bound subgoal using the substituted parameters
  have h_prob_bound : TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n)
    (fun ω =>
      FiberAndDegreeEvent ω ε2 ∧
        ε1 * K ^ 2 <
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ))
    ≤ Real.exp (-(C ^ 2 / (L * (TwoBiteNaturalReducedVertexCount n : ℝ) * (n : ℝ).rpow (8 * ε)))) := by
    
    let C_I : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n) → ℝ := 
      fun ω => ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
    
    let A_int : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n) → ℝ := fun ω => by
      classical
      exact
        let P_R := I.image (TwoBiteRedProjection ω)
        let P_B := I.image (TwoBiteBlueProjection ω)
        let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
        let S_I_cap_P_I := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) ∩ P_I
        let pairs := S_I_cap_P_I.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
        (pairs.card : ℝ)
    let A_sf : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n) → ℝ := fun ω => by
      classical
      exact
        let pairs := TwoBiteFinalPairs I
        let sf_pairs := pairs.filter (fun e =>
          TwoBiteRedProjection ω e.1 = TwoBiteRedProjection ω e.2 ∨
          TwoBiteBlueProjection ω e.1 = TwoBiteBlueProjection ω e.2)
        (sf_pairs.card : ℝ)
    let Z_I : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n) → ℝ := fun ω => by
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
    let mu : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n) → ℝ := fun _ => C / (2 * L)
    let t : ℝ := C / Real.sqrt L

    have h_decomp : ∀ ω, FiberAndDegreeEvent ω ε2 → C_I ω ≤ A_int ω + A_sf ω + Z_I ω := by
      intro ω _
      dsimp only [C_I, A_int, A_sf, Z_I]
      classical
      -- Since they are defined with by classical exact, let's just do it cleanly
      have h_TwoBiteX_subset : ∀ (x : TwoBiteBaseVertex (TwoBiteNaturalReducedVertexCount n)), TwoBiteX ω I x ⊆ I := by
        intro x v hv
        exact (Finset.mem_filter.mp hv).1
      have h_TwoBiteFinalPairs_mono : ∀ {X Y : Finset (Fin n)}, X ⊆ Y → TwoBiteFinalPairs X ⊆ TwoBiteFinalPairs Y := by
        intro X Y h e he
        rw [TwoBiteFinalPairs, TwoBitePairsInSet] at he ⊢
        rw [Finset.mem_filter] at he ⊢
        exact ⟨Finset.mem_product.mpr ⟨h (Finset.mem_product.mp he.1).1, h (Finset.mem_product.mp he.1).2⟩, he.2⟩
      let P_R := I.image (TwoBiteRedProjection ω)
      let P_B := I.image (TwoBiteBlueProjection ω)
      let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
      let S_I_cap_P_I := (Finset.univ.filter (fun x => TwoBiteSmallClass ω ε I x)) ∩ P_I
      let A_int_pairs := S_I_cap_P_I.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
      let sf_pairs := (TwoBiteFinalPairs I).filter (fun e => TwoBiteRedProjection ω e.1 = TwoBiteRedProjection ω e.2 ∨ TwoBiteBlueProjection ω e.1 = TwoBiteBlueProjection ω e.2)
      let S_I_ext := (Finset.univ.filter (fun x => TwoBiteSmallClass ω ε I x)) \ P_I
      let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
      let Z_pairs := ext_pairs.filter (fun e => TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧ TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
      have h_C_I_union : ((Finset.univ : Finset (TwoBiteBaseVertex (TwoBiteNaturalReducedVertexCount n))).filter (fun x => TwoBiteSmallClass ω ε I x)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x)) ⊆ A_int_pairs ∪ ext_pairs := by
        intro e he
        rw [Finset.mem_union]
        rw [Finset.mem_biUnion] at he
        rcases he with ⟨x, hx, hxe⟩
        by_cases hx_P_I : x ∈ P_I
        · left
          exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_inter.mpr ⟨hx, hx_P_I⟩, hxe⟩
        · right
          exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hx_P_I⟩, hxe⟩
      have h_ext_subset : ext_pairs ⊆ sf_pairs ∪ Z_pairs := by
        intro e he
        rw [Finset.mem_union]
        by_cases h_sf : TwoBiteRedProjection ω e.1 = TwoBiteRedProjection ω e.2 ∨ TwoBiteBlueProjection ω e.1 = TwoBiteBlueProjection ω e.2
        · left
          rw [Finset.mem_filter]
          have h_subset : ext_pairs ⊆ TwoBiteFinalPairs I := by
            intro e' he'
            rw [Finset.mem_biUnion] at he'
            rcases he' with ⟨x, _, hxe'⟩
            exact h_TwoBiteFinalPairs_mono (h_TwoBiteX_subset x) hxe'
          exact ⟨h_subset he, h_sf⟩
        · right
          rw [Finset.mem_filter]
          push Not at h_sf
          exact ⟨he, h_sf⟩
      have h_C_I_eq : (TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card = (((Finset.univ : Finset (TwoBiteBaseVertex (TwoBiteNaturalReducedVertexCount n))).filter (fun x => TwoBiteSmallClass ω ε I x)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))).card := congr_arg Finset.card rfl
      have h1 : ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) ≤ (A_int_pairs.card : ℝ) + (ext_pairs.card : ℝ) := by
        calc
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) = ((((Finset.univ : Finset (TwoBiteBaseVertex (TwoBiteNaturalReducedVertexCount n))).filter (fun x => TwoBiteSmallClass ω ε I x)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))).card : ℝ) := by exact_mod_cast h_C_I_eq
          _ ≤ ((A_int_pairs ∪ ext_pairs).card : ℝ) := by exact_mod_cast Finset.card_le_card h_C_I_union
          _ ≤ (A_int_pairs.card : ℝ) + (ext_pairs.card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
      have h2 : (ext_pairs.card : ℝ) ≤ (sf_pairs.card : ℝ) + (Z_pairs.card : ℝ) := by
        calc
          (ext_pairs.card : ℝ) ≤ ((sf_pairs ∪ Z_pairs).card : ℝ) := by exact_mod_cast Finset.card_le_card h_ext_subset
          _ ≤ (sf_pairs.card : ℝ) + (Z_pairs.card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
      linarith
    have h_A_int : ∀ ω, FiberAndDegreeEvent ω ε2 → A_int ω ≤ (ε1 / 2) * K ^ 2 := by
      intro ω _
      classical
      let m_val := TwoBiteNaturalReducedVertexCount n
      let P_R := I.image (TwoBiteRedProjection ω)
      let P_B := I.image (TwoBiteBlueProjection ω)
      let P_I := (P_R.image (Sum.inl : Fin m_val → TwoBiteBaseVertex m_val)) ∪ (P_B.image (Sum.inr : Fin m_val → TwoBiteBaseVertex m_val))
      let S_I_cap_P_I := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) ∩ P_I
      have h_P_R_card : (P_R.card : ℝ) ≤ K := by
        calc
          (P_R.card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast Finset.card_image_le
          _ = K := by rw [hI]
      have h_P_B_card : (P_B.card : ℝ) ≤ K := by
        calc
          (P_B.card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast Finset.card_image_le
          _ = K := by rw [hI]
      have h_P_I_card : (P_I.card : ℝ) ≤ 2 * K := by
        have h_union : (P_I.card : ℝ) ≤ ((P_R.image (Sum.inl : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) + ((P_B.image (Sum.inr : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
        calc
          (P_I.card : ℝ) ≤ ((P_R.image (Sum.inl : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) + ((P_B.image (Sum.inr : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) := h_union
          _ ≤ (P_R.card : ℝ) + (P_B.card : ℝ) := by
            have h1 : ((P_R.image (Sum.inl : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) ≤ (P_R.card : ℝ) := by exact_mod_cast Finset.card_image_le
            have h2 : ((P_B.image (Sum.inr : Fin m_val → TwoBiteBaseVertex m_val)).card : ℝ) ≤ (P_B.card : ℝ) := by exact_mod_cast Finset.card_image_le
            linarith
          _ ≤ K + K := by linarith
          _ = 2 * K := by ring
      have h_S_I_cap_P_I_card : (S_I_cap_P_I.card : ℝ) ≤ 2 * K := by
        have h_inter : S_I_cap_P_I ⊆ P_I := by
          intro x hx
          exact (Finset.mem_inter.mp hx).2
        calc
          (S_I_cap_P_I.card : ℝ) ≤ (P_I.card : ℝ) := by exact_mod_cast Finset.card_le_card h_inter
          _ ≤ 2 * K := h_P_I_card
      have h_pair_bound : ∀ x ∈ S_I_cap_P_I, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤ (TwoBiteSmallCutoff ε n) ^ 2 / 2 := by
        intro x hx
        rw [Finset.mem_inter, Finset.mem_filter] at hx
        have h_small := hx.1.2
        have h_card_le : ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteSmallCutoff ε n := h_small.2
        have h_final_pairs : ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤ ((TwoBiteX ω I x).card : ℝ) ^ 2 / 2 := by
          exact FinalPairsCardLeHalfSq (TwoBiteX ω I x)
        calc ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤ ((TwoBiteX ω I x).card : ℝ) ^ 2 / 2 := h_final_pairs
          _ ≤ (TwoBiteSmallCutoff ε n) ^ 2 / 2 := by
            have h_nonneg : 0 ≤ ((TwoBiteX ω I x).card : ℝ) := Nat.cast_nonneg _
            nlinarith
      have h_A_int_sum : A_int ω ≤ ∑ x ∈ S_I_cap_P_I, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := by
        have h_eq : A_int ω = ((S_I_cap_P_I.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))).card : ℝ) := rfl
        calc
          A_int ω = ((S_I_cap_P_I.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))).card : ℝ) := h_eq
          _ ≤ ∑ x ∈ S_I_cap_P_I, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      have h_t3 : TwoBiteSmallCutoff ε n = Real.rpow (n : ℝ) (2 * ε) := rfl
      have h_hier_all := h_hier n hn_lt
      rcases h_hier_all with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_hier_t3, _⟩
      have hk : (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) = K := by rfl
      rw [hk] at h_hier_t3
      calc
        A_int ω ≤ ∑ x ∈ S_I_cap_P_I, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := h_A_int_sum
        _ ≤ ∑ x ∈ S_I_cap_P_I, ((TwoBiteSmallCutoff ε n) ^ 2 / 2) := Finset.sum_le_sum (fun x hx => h_pair_bound x hx)
        _ = (S_I_cap_P_I.card : ℝ) * ((TwoBiteSmallCutoff ε n) ^ 2 / 2) := by simp [mul_comm]
        _ ≤ (2 * K) * ((TwoBiteSmallCutoff ε n) ^ 2 / 2) := by
          have h_nonneg : 0 ≤ (TwoBiteSmallCutoff ε n) ^ 2 / 2 := by positivity
          exact mul_le_mul_of_nonneg_right h_S_I_cap_P_I_card h_nonneg
        _ = K * (TwoBiteSmallCutoff ε n) ^ 2 := by ring
        _ = (Real.rpow (n : ℝ) (2 * ε)) ^ 2 * K := by rw [h_t3]; ring
        _ ≤ (ε1 / 2) * K ^ 2 := h_hier_t3
    have h_A_sf : ∀ ω, FiberAndDegreeEvent ω ε2 → A_sf ω ≤ 2 * K * L ^ 2 := by
      intro ω h_fiber_local
      have h_hier_all := h_hier n hn_lt
      rcases h_hier_all with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_e2_le_1, _⟩
      have h_bound_red : ∀ a ∈ I, ((I.filter (fun b => TwoBiteRedProjection ω a = TwoBiteRedProjection ω b)).card : ℝ) ≤ 2 * L ^ 2 := by
        intro a _
        have h_sub : (I.filter (fun b => TwoBiteRedProjection ω a = TwoBiteRedProjection ω b)) ⊆ RedFiber ω (TwoBiteRedProjection ω a) := by
          intro b hb
          rw [Finset.mem_filter] at hb
          rw [RedFiber, Finset.mem_filter]
          exact ⟨Finset.mem_univ b, hb.2.symm⟩
        have h_fiber_bound : ((RedFiber ω (TwoBiteRedProjection ω a)).card : ℝ) ≤ 2 * L ^ 2 := by
          have h1 := h_fiber_local.1 (TwoBiteRedProjection ω a)
          unfold WithinRelativeError at h1
          have h2 := le_of_abs_le h1
          have h_L2_nonneg : 0 ≤ L ^ 2 := sq_nonneg _
          nlinarith
        have h_le := @Finset.card_le_card _ _ (RedFiber ω (TwoBiteRedProjection ω a)) h_sub
        calc
          ((I.filter (fun b => TwoBiteRedProjection ω a = TwoBiteRedProjection ω b)).card : ℝ) ≤ ((RedFiber ω (TwoBiteRedProjection ω a)).card : ℝ) := by exact_mod_cast h_le
          _ ≤ 2 * L ^ 2 := h_fiber_bound
      have h_bound_blue : ∀ a ∈ I, ((I.filter (fun b => TwoBiteBlueProjection ω a = TwoBiteBlueProjection ω b)).card : ℝ) ≤ 2 * L ^ 2 := by
        intro a _
        have h_sub : (I.filter (fun b => TwoBiteBlueProjection ω a = TwoBiteBlueProjection ω b)) ⊆ BlueFiber ω (TwoBiteBlueProjection ω a) := by
          intro b hb
          rw [Finset.mem_filter] at hb
          rw [BlueFiber, Finset.mem_filter]
          exact ⟨Finset.mem_univ b, hb.2.symm⟩
        have h_fiber_bound : ((BlueFiber ω (TwoBiteBlueProjection ω a)).card : ℝ) ≤ 2 * L ^ 2 := by
          have h1 := h_fiber_local.2.1 (TwoBiteBlueProjection ω a)
          unfold WithinRelativeError at h1
          have h2 := le_of_abs_le h1
          have h_L2_nonneg : 0 ≤ L ^ 2 := sq_nonneg _
          nlinarith
        have h_le := @Finset.card_le_card _ _ (BlueFiber ω (TwoBiteBlueProjection ω a)) h_sub
        calc
          ((I.filter (fun b => TwoBiteBlueProjection ω a = TwoBiteBlueProjection ω b)).card : ℝ) ≤ ((BlueFiber ω (TwoBiteBlueProjection ω a)).card : ℝ) := by exact_mod_cast h_le
          _ ≤ 2 * L ^ 2 := h_fiber_bound
      have h_red := SumChooseBound I (TwoBiteRedProjection ω) (2 * L ^ 2) h_bound_red
      have h_blue := SumChooseBound I (TwoBiteBlueProjection ω) (2 * L ^ 2) h_bound_blue
      let p_red := fun (e : Fin n × Fin n) => TwoBiteRedProjection ω e.1 = TwoBiteRedProjection ω e.2
      let p_blue := fun (e : Fin n × Fin n) => TwoBiteBlueProjection ω e.1 = TwoBiteBlueProjection ω e.2
      have h_red_half := PairsInSetLeHalfProduct (fun v : Fin n => v.val) I p_red (fun a b hab => hab.symm)
      have h_blue_half := PairsInSetLeHalfProduct (fun v : Fin n => v.val) I p_blue (fun a b hab => hab.symm)
      have h_sf_le : A_sf ω ≤ (((TwoBiteFinalPairs I).filter p_red).card : ℝ) + (((TwoBiteFinalPairs I).filter p_blue).card : ℝ) := by
        have h_sub : (TwoBiteFinalPairs I).filter (fun e => p_red e ∨ p_blue e) ⊆ ((TwoBiteFinalPairs I).filter p_red) ∪ ((TwoBiteFinalPairs I).filter p_blue) := by
          intro e he
          rw [Finset.mem_filter] at he
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          rcases he.2 with h1 | h2
          · left; exact ⟨he.1, h1⟩
          · right; exact ⟨he.1, h2⟩
        have h_eq : A_sf ω = (((TwoBiteFinalPairs I).filter (fun e => p_red e ∨ p_blue e)).card : ℝ) := rfl
        calc
          A_sf ω = (((TwoBiteFinalPairs I).filter (fun e => p_red e ∨ p_blue e)).card : ℝ) := h_eq
          _ ≤ (((((TwoBiteFinalPairs I).filter p_red) ∪ ((TwoBiteFinalPairs I).filter p_blue))).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
          _ ≤ (((TwoBiteFinalPairs I).filter p_red).card : ℝ) + (((TwoBiteFinalPairs I).filter p_blue).card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
      have h_final : 2 * A_sf ω ≤ 4 * K * L ^ 2 := by
        calc
          2 * A_sf ω ≤ 2 * ((((TwoBiteFinalPairs I).filter p_red).card : ℝ) + (((TwoBiteFinalPairs I).filter p_blue).card : ℝ)) := by linarith
          _ = 2 * (((TwoBiteFinalPairs I).filter p_red).card : ℝ) + 2 * (((TwoBiteFinalPairs I).filter p_blue).card : ℝ) := by ring
          _ ≤ (((I.product I).filter p_red).card : ℝ) + (((I.product I).filter p_blue).card : ℝ) := by exact add_le_add h_red_half h_blue_half
          _ ≤ I.card * (2 * L ^ 2) + I.card * (2 * L ^ 2) := by exact add_le_add h_red h_blue
          _ = 4 * K * L ^ 2 := by rw [hI]; ring
      linarith
    have h_mu : ∀ ω, FiberAndDegreeEvent ω ε2 → mu ω ≤ C / (2 * L) := by
      intro ω _
      exact le_refl (C / (2 * L))
    have h_hier1 : (1 / (2 * L)) * C + 2 * K * L ^ 2 + (1 / Real.sqrt L) * C ≤ (2 / Real.sqrt L) * C :=
      (h_hier n hn_lt).2.2.2.2.2.2.2.2.2.2.1
    have h_hier2 : (2 / Real.sqrt L) * C ≤ (ε1 / 2) * K ^ 2 :=
      (h_hier n hn_lt).2.2.2.2.2.2.2.2.2.2.2.2.1

    have h_implication : ∀ ω, FiberAndDegreeEvent ω ε2 → ε1 * K ^ 2 < C_I ω → Z_I ω ≥ mu ω + t := by
      intro ω h_fiber h_fail
      exact FixedSetSmallClosedPairsTailImplication
        (h_decomp ω h_fiber)
        (h_A_int ω h_fiber)
        (h_A_sf ω h_fiber)
        (h_mu ω h_fiber)
        rfl
        h_hier1
        h_hier2
        h_fail

    have h_event_subset : ∀ ω, 
      (FiberAndDegreeEvent ω ε2 ∧ ε1 * K ^ 2 < C_I ω) → Z_I ω ≥ mu ω + t := by
      rintro ω ⟨h1, h2⟩
      exact h_implication ω h1 h2

    have h_external_tail : TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n) (TwoBiteEdgeProbability (1 / 2) n)
      (fun ω => Z_I ω ≥ mu ω + t)
      ≤ Real.exp (-(C ^ 2 / (L * (TwoBiteNaturalReducedVertexCount n : ℝ) * (n : ℝ).rpow (8 * ε)))) := by
      exact FixedSetExternalTailBound I ε ε1 ε2 h_hier hn_lt rfl rfl rfl hI

    -- remaining target should be the probability bound for the external-tail event
    -- which is exactly `h_external_tail`, so we'd conclude using monotonicity
    apply le_trans _ h_external_tail
    unfold TwoBiteEventProbability
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω h_in
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_in ⊢
      exact h_event_subset ω h_in
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω (h_hier n hn_lt).2.1 (le_trans (h_hier n hn_lt).2.2.1 (by norm_num))

  exact h_prob_bound
