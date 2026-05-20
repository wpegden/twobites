import Mathlib.Tactic
import Tablet.FiberAndDegreeLiftedSizeFixedVertexTail
import Tablet.GraphDegreeCount
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.TwoBiteFixedGraphsConditionalInjectionBridge
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight

open Finset Classical

-- [TABLET NODE: FiberAndDegreeLiftedSizeFixedVertexProbability]

theorem FiberAndDegreeLiftedSizeFixedVertexProbability {n m : ℕ} {p δ : ℝ}
    (redSide : Bool) (x : Fin m)
    (h_support : n ≤ m * m) (hm_pos : 0 < m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 2 : ℝ)) :
    let C : ℝ :=
      Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) *
        ((1 - δ) * (p * (n : ℝ)))) +
      Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) *
        ((1 - δ) * (p * (n : ℝ)))))
    TwoBiteEventProbability n m p
      (fun ω =>
        (if redSide then
          WithinRelativeError δ (p * (m : ℝ))
            (GraphDegreeCount (TwoBiteRedGraph ω) x : ℝ)
        else
          WithinRelativeError δ (p * (m : ℝ))
            (GraphDegreeCount (TwoBiteBlueGraph ω) x : ℝ)) ∧
        ¬ WithinRelativeError (3 * δ) (p * (n : ℝ))
          ((TwoBiteLiftedNeighborhood ω
            (if redSide then Sum.inl x else Sum.inr x)).card : ℝ))
      ≤ C := by
-- BODY
  classical
  let target : ℝ := p * (n : ℝ)
  let degreeTarget : ℝ := p * (m : ℝ)
  let C : ℝ :=
    Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) *
      ((1 - δ) * target)) +
    Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) *
      ((1 - δ) * target)))
  let vertex : TwoBiteBaseVertex m := if redSide then Sum.inl x else Sum.inr x
  let degreeGood : TwoBiteSample n m p → Prop :=
    fun ω =>
      if redSide then
        WithinRelativeError δ degreeTarget
          (GraphDegreeCount (TwoBiteRedGraph ω) x : ℝ)
      else
        WithinRelativeError δ degreeTarget
          (GraphDegreeCount (TwoBiteBlueGraph ω) x : ℝ)
  let badLifted : TwoBiteSample n m p → Prop :=
    fun ω =>
      ¬ WithinRelativeError (3 * δ) target
        ((TwoBiteLiftedNeighborhood ω vertex).card : ℝ)
  let Event : TwoBiteSample n m p → Prop := fun ω => degreeGood ω ∧ badLifted ω
  let A := SimpleGraph (Fin m)
  let pairWeight : A × A → ℝ := fun GG => GnpGraphWeight p GG.1 * GnpGraphWeight p GG.2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hgraph_nonneg : ∀ G : A, 0 ≤ GnpGraphWeight p G := by
    intro G
    unfold GnpGraphWeight
    exact Finset.prod_nonneg (by
      intro e he
      by_cases hAdj : G.Adj e.1 e.2
      · simp [hAdj, hp0]
      · have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
        simp [hAdj, h1mp])
  have hpair_nonneg : ∀ GG : A × A, 0 ≤ pairWeight GG := by
    intro GG
    dsimp [pairWeight]
    exact mul_nonneg (hgraph_nonneg GG.1) (hgraph_nonneg GG.2)
  have prob_mono :
      ∀ {E F : TwoBiteSample n m p → Prop},
        (∀ ω, E ω → F ω) →
        TwoBiteEventProbability n m p E ≤ TwoBiteEventProbability n m p F := by
    intro E F hEF
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω _ _
        exact TwoBiteSampleWeightNonnegative ω hp0 hp1)
  let fixedEvent : A × A → TwoBiteSample n m p → Prop :=
    fun GG ω => Event ω ∧ ω.1 = GG.1 ∧ ω.2.1 = GG.2
  have h_event_subset :
      ∀ ω : TwoBiteSample n m p, Event ω → ∃ GG : A × A, fixedEvent GG ω := by
    intro ω hω
    exact ⟨(ω.1, ω.2.1), hω, rfl, rfl⟩
  have h_union :
      TwoBiteEventProbability n m p Event ≤
        ∑ GG : A × A, TwoBiteEventProbability n m p (fixedEvent GG) := by
    exact le_trans (prob_mono h_event_subset)
      (TwoBiteEventProbabilityUnionBound hp0 hp1 fixedEvent)
  have htotal_nonempty : Nonempty (Fin n ↪ (Fin m × Fin m)) := by
    have hle_card :
        Fintype.card (Fin n) ≤ Fintype.card (Fin m × Fin m) := by
      simpa [Fintype.card_fin, Fintype.card_prod] using h_support
    exact Function.Embedding.nonempty_of_card_le hle_card
  have htotal_pos : 0 < (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr htotal_nonempty
  have htotal_ne_nat : Fintype.card (Fin n ↪ (Fin m × Fin m)) ≠ 0 :=
    Nat.ne_of_gt (Fintype.card_pos_iff.mpr htotal_nonempty)
  have hU :
      UniformInjectionWeight n m =
        (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
    unfold UniformInjectionWeight
    rw [if_neg htotal_ne_nat]
  have hfixed_bound :
      ∀ GG : A × A,
        TwoBiteEventProbability n m p (fixedEvent GG) ≤ C * pairWeight GG := by
    intro GG
    let G_R : SimpleGraph (Fin m) := GG.1
    let G_B : SimpleGraph (Fin m) := GG.2
    let baseDegree : ℕ :=
      if redSide then GraphDegreeCount G_R x else GraphDegreeCount G_B x
    let q : ℕ := baseDegree * m
    let K : Finset (Fin m × Fin m) :=
      if redSide then
        (Finset.univ.filter (fun y : Fin m => G_R.Adj x y)) ×ˢ
          (Finset.univ : Finset (Fin m))
      else
        (Finset.univ : Finset (Fin m)) ×ˢ
          (Finset.univ.filter (fun y : Fin m => G_B.Adj x y))
    have hK : K.card = q := by
      by_cases hside : redSide
      · simp [K, q, baseDegree, GraphDegreeCount, hside, Finset.card_product]
      · simp [K, q, baseDegree, GraphDegreeCount, hside, Finset.card_product, Nat.mul_comm]
    by_cases hdegGG :
        if redSide then
          WithinRelativeError δ degreeTarget (GraphDegreeCount G_R x : ℝ)
        else
          WithinRelativeError δ degreeTarget (GraphDegreeCount G_B x : ℝ)
    · have hmean :
          WithinRelativeError δ target
            ((n : ℝ) * ((q : ℝ) / (m * m : ℝ))) := by
        have hm_pos_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
        let d : ℝ := (baseDegree : ℝ)
        have hdeg_abs : |d - degreeTarget| ≤ δ * degreeTarget := by
          unfold WithinRelativeError at hdegGG
          by_cases hside : redSide
          · have hd : d = (GraphDegreeCount G_R x : ℝ) := by
              simp [d, baseDegree, hside]
            simpa [degreeTarget, hd, hside] using hdegGG
          · have hd : d = (GraphDegreeCount G_B x : ℝ) := by
              simp [d, baseDegree, hside]
            simpa [degreeTarget, hd, hside] using hdegGG
        have hq_ratio :
            ((q : ℝ) / (m * m : ℝ)) = d / (m : ℝ) := by
          dsimp [q, d]
          rw [Nat.cast_mul]
          have hm_cast_ne : ((m : ℝ) * (m : ℝ)) ≠ 0 := by positivity
          field_simp [hm_ne, hm_cast_ne]
        unfold WithinRelativeError
        rw [hq_ratio]
        have hfactor :
            (n : ℝ) * (d / (m : ℝ)) - target =
              ((n : ℝ) / (m : ℝ)) * (d - degreeTarget) := by
          dsimp [target, degreeTarget]
          field_simp [hm_ne]
        rw [hfactor, abs_mul]
        have hn_div_nonneg : 0 ≤ (n : ℝ) / (m : ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hdeg_abs hn_div_nonneg
        have hrewrite :
            (n : ℝ) / (m : ℝ) * (δ * degreeTarget) = δ * target := by
          dsimp [target, degreeTarget]
          field_simp [hm_ne]
        rw [abs_of_nonneg hn_div_nonneg]
        calc
          (n : ℝ) / (m : ℝ) * |d - degreeTarget|
              ≤ (n : ℝ) / (m : ℝ) * (δ * degreeTarget) := hmul
          _ = δ * target := hrewrite
      let P : (Fin n ↪ Fin m × Fin m) → Prop :=
        fun φ =>
          ¬ WithinRelativeError (3 * δ) target
            (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ)
      letI : DecidablePred P := Classical.decPred P
      have hcount_bound_raw :
          ((Finset.univ.filter (fun φ : Fin n ↪ Fin m × Fin m =>
            ¬ WithinRelativeError (3 * δ) target
              (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ))).card : ℝ)
            ≤ C * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
        have htail :=
          FiberAndDegreeLiftedSizeFixedVertexTail
            n m q K p δ hK h_support hp0 hδ_pos hδ_le hmean
        convert htail using 1
        · apply congrArg (fun S : Finset (Fin n ↪ Fin m × Fin m) => (S.card : ℝ))
          ext φ
          simp [target]
      have hcount_bound :
          ((Finset.univ.filter P).card : ℝ)
            ≤ C * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
        have hcard_eq :
            (Finset.univ.filter P).card =
              (Finset.univ.filter (fun φ : Fin n ↪ Fin m × Fin m =>
                ¬ WithinRelativeError (3 * δ) target
                  (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ))).card := by
          apply congrArg Finset.card
          ext φ
          simp [P]
        exact_mod_cast hcard_eq ▸ hcount_bound_raw
      have hbad_equiv :
          ∀ ω : TwoBiteSample n m p,
            ω.1 = G_R → ω.2.1 = G_B → (badLifted ω ↔ P ω.2.2) := by
        intro ω hR hB
        have hneigh :
            TwoBiteLiftedNeighborhood ω vertex =
              Finset.univ.filter (fun v : Fin n => ω.2.2 v ∈ K) := by
          by_cases hside : redSide
          · ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteRedProjection,
              TwoBiteEmbedding, vertex, K, hside, hR]
          · ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteBlueGraph, TwoBiteBlueProjection,
              TwoBiteEmbedding, vertex, K, hside, hB]
        have hcard :
            (Finset.univ.filter (fun v : Fin n => ω.2.2 v ∈ K)).card =
              (((Finset.univ : Finset (Fin n)).image ω.2.2) ∩ K).card := by
          have himage :
              ((Finset.univ.filter (fun v : Fin n => ω.2.2 v ∈ K)).image ω.2.2) =
                (((Finset.univ : Finset (Fin n)).image ω.2.2) ∩ K) := by
            ext y
            constructor
            · intro hy
              rcases Finset.mem_image.mp hy with ⟨v, hv, hyv⟩
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hyv⟩,
                  by simpa [← hyv] using (Finset.mem_filter.mp hv).2⟩
            · intro hy
              rcases Finset.mem_inter.mp hy with ⟨hyimg, hyK⟩
              rcases Finset.mem_image.mp hyimg with ⟨v, -, hyv⟩
              exact Finset.mem_image.mpr
                ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hyv] using hyK⟩, hyv⟩
          rw [← himage]
          exact (Finset.card_image_of_injective _ (ω.2.2).injective).symm
        dsimp [badLifted, P]
        rw [hneigh, hcard]
      have hfixed_eq :
          TwoBiteEventProbability n m p (fixedEvent GG) =
            TwoBiteEventProbability n m p
              (fun ω => P ω.2.2 ∧ ω.1 = G_R ∧ ω.2.1 = G_B) := by
        apply congrArg
        ext ω
        constructor
        · intro hω
          rcases hω with ⟨hEvent, hR, hB⟩
          exact ⟨(hbad_equiv ω hR hB).mp hEvent.2, hR, hB⟩
        · intro hω
          rcases hω with ⟨hPω, hR, hB⟩
          refine ⟨?_, hR, hB⟩
          constructor
          · dsimp [Event, degreeGood, G_R, G_B]
            by_cases hside : redSide
            · simpa [hside, hR, hB, TwoBiteRedGraph] using hdegGG
            · simpa [hside, hR, hB, TwoBiteBlueGraph] using hdegGG
          · exact (hbad_equiv ω hR hB).mpr hPω
      have hbridge :=
        (TwoBiteFixedGraphsConditionalInjectionBridge n m p G_R G_B P).2
      have hunit :
          UniformInjectionWeight n m *
              ((Finset.univ.filter P).card : ℝ) ≤ C := by
        rw [hU]
        calc
          (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)⁻¹ *
              ((Finset.univ.filter P).card : ℝ)
              = ((Finset.univ.filter P).card : ℝ) *
                  (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)⁻¹ := by ring
          _ ≤ (C * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)) *
                (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)⁻¹ := by
                exact mul_le_mul_of_nonneg_right
                  (by simpa [P] using hcount_bound)
                  (inv_nonneg.mpr htotal_pos.le)
          _ = C := by
                field_simp [htotal_pos.ne']
      calc
        TwoBiteEventProbability n m p (fixedEvent GG)
            = GnpGraphWeight p G_R * GnpGraphWeight p G_B *
                UniformInjectionWeight n m *
                  ((Finset.univ.filter P).card : ℝ) := by
              rw [hfixed_eq]
              simpa using hbridge
        _ = pairWeight GG *
              (UniformInjectionWeight n m *
                ((Finset.univ.filter P).card : ℝ)) := by
              simp [pairWeight, G_R, G_B]
              ring
        _ ≤ pairWeight GG * C := by
              exact mul_le_mul_of_nonneg_left hunit (hpair_nonneg GG)
        _ = C * pairWeight GG := by ring
    · have hfalse :
        ∀ ω : TwoBiteSample n m p, ¬ fixedEvent GG ω := by
        intro ω hω
        rcases hω with ⟨hEvent, hR, hB⟩
        apply hdegGG
        dsimp [Event, degreeGood, G_R, G_B] at hEvent
        by_cases hside : redSide
        · simpa [hside, hR, hB, TwoBiteRedGraph] using hEvent.1
        · simpa [hside, hR, hB, TwoBiteBlueGraph] using hEvent.1
      have hzero :
          TwoBiteEventProbability n m p (fixedEvent GG) = 0 := by
        unfold TwoBiteEventProbability
        rw [Finset.sum_filter]
        apply Finset.sum_eq_zero
        intro ω hω
        simp [hfalse ω]
      rw [hzero]
      exact mul_nonneg hC_nonneg (hpair_nonneg GG)
  have hsum_bound :
      (∑ GG : A × A, TwoBiteEventProbability n m p (fixedEvent GG))
        ≤ ∑ GG : A × A, C * pairWeight GG := by
    exact Finset.sum_le_sum (by intro GG hGG; exact hfixed_bound GG)
  have hpair_sum :
      (∑ GG : A × A, C * pairWeight GG) = C := by
    calc
      (∑ GG : A × A, C * pairWeight GG)
          = C * (∑ GG : A × A, pairWeight GG) := by
            rw [Finset.mul_sum]
      _ = C * ((∑ G : A, GnpGraphWeight p G) *
            (∑ G : A, GnpGraphWeight p G)) := by
            congr 1
            dsimp [pairWeight]
            rw [← Finset.univ_product_univ, Finset.sum_product]
            calc
              (∑ x : A, ∑ x_1 : A, GnpGraphWeight p x * GnpGraphWeight p x_1)
                  = ∑ x : A, GnpGraphWeight p x *
                      (∑ x_1 : A, GnpGraphWeight p x_1) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    rw [Finset.mul_sum]
              _ = (∑ x : A, GnpGraphWeight p x) *
                    (∑ x_1 : A, GnpGraphWeight p x_1) := by
                    rw [Finset.sum_mul]
      _ = C := by
            have hsum : (∑ G : A, GnpGraphWeight p G) = 1 := by
              simpa [A] using GnpGraphWeightSumOne m p
            rw [hsum]
            ring
  calc
    TwoBiteEventProbability n m p
      (fun ω =>
        (if redSide then
          WithinRelativeError δ (p * (m : ℝ))
            (GraphDegreeCount (TwoBiteRedGraph ω) x : ℝ)
        else
          WithinRelativeError δ (p * (m : ℝ))
            (GraphDegreeCount (TwoBiteBlueGraph ω) x : ℝ)) ∧
        ¬ WithinRelativeError (3 * δ) (p * (n : ℝ))
          ((TwoBiteLiftedNeighborhood ω
            (if redSide then Sum.inl x else Sum.inr x)).card : ℝ))
        = TwoBiteEventProbability n m p Event := by
          apply congrArg
          ext ω
          simp [Event, degreeGood, badLifted, target, degreeTarget, vertex]
    _ ≤ ∑ GG : A × A, TwoBiteEventProbability n m p (fixedEvent GG) := h_union
    _ ≤ C := le_trans hsum_bound (by rw [hpair_sum])
