import Tablet.TwoBiteTouchedProjectedPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStageRevealedVertex
import Tablet.TwoBiteStageF1
import Tablet.TwoBiteStageF2
import Tablet.TwoBiteProjectionContains
import Tablet.TwoBiteBaseFiber
import Tablet.TwoBiteBaseAdj
import Tablet.TwoBiteX
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteLargeHugeVertices
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff
import Tablet.LargeHugeVertexCountBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: StagedTouchedPairsBound]

theorem StagedTouchedPairsBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      ((TwoBiteTouchedProjectedPairs ω ε I).card : ℝ) ≤
        ε1 * (I.card : ℝ) ^ 2 := by
-- BODY
  classical
  intro n m p ω I ε ε1 ε2 n0 hε1_nonneg hComparisons hn hI hFiber
  have hPairSet_red_endpoints :
      ∀ q : Fin m × Fin m,
        Sum.inl q ∈ TwoBiteProjectionPairSet ω I →
          TwoBiteProjectionContains ω I (Sum.inl q.1) ∧
            TwoBiteProjectionContains ω I (Sum.inl q.2) := by
    intro q hq
    simp [TwoBiteProjectionPairSet, TwoBiteBasePairs, TwoBitePairsInSet,
      TwoBiteProjectionContains] at hq ⊢
    exact ⟨hq.1.1, hq.1.2⟩
  have hPairSet_blue_endpoints :
      ∀ q : Fin m × Fin m,
        Sum.inr q ∈ TwoBiteProjectionPairSet ω I →
          TwoBiteProjectionContains ω I (Sum.inr q.1) ∧
            TwoBiteProjectionContains ω I (Sum.inr q.2) := by
    intro q hq
    simp [TwoBiteProjectionPairSet, TwoBiteBasePairs, TwoBitePairsInSet,
      TwoBiteProjectionContains] at hq ⊢
    exact ⟨hq.1.1, hq.1.2⟩
  have hTouched_endpoint_stage :
      ∀ e ∈ TwoBiteTouchedProjectedPairs ω ε I,
        ∃ x : TwoBiteBaseVertex m,
          (TwoBiteStageF1 ω I x ∨ TwoBiteStageF2 ω ε I x) ∧
            match e with
            | Sum.inl q => x = Sum.inl q.1 ∨ x = Sum.inl q.2
            | Sum.inr q => x = Sum.inr q.1 ∨ x = Sum.inr q.2 := by
    intro e he
    have he_pair : e ∈ TwoBiteProjectionPairSet ω I := by
      simpa [TwoBiteTouchedProjectedPairs] using (Finset.mem_filter.mp he).1
    have he_touch : TwoBiteProjectionPairTouched ω ε I e := by
      simpa [TwoBiteTouchedProjectedPairs] using (Finset.mem_filter.mp he).2
    cases e with
    | inl q =>
        have hends := hPairSet_red_endpoints q he_pair
        dsimp [TwoBiteProjectionPairTouched] at he_touch
        rcases he_touch with hrev | hrev
        · dsimp [TwoBiteStageRevealedVertex] at hrev
          rcases hrev with hnot | hgood
          · exact False.elim (hnot hends.1)
          · exact ⟨Sum.inl q.1, hgood, Or.inl rfl⟩
        · dsimp [TwoBiteStageRevealedVertex] at hrev
          rcases hrev with hnot | hgood
          · exact False.elim (hnot hends.2)
          · exact ⟨Sum.inl q.2, hgood, Or.inr rfl⟩
    | inr q =>
        have hends := hPairSet_blue_endpoints q he_pair
        dsimp [TwoBiteProjectionPairTouched] at he_touch
        rcases he_touch with hrev | hrev
        · dsimp [TwoBiteStageRevealedVertex] at hrev
          rcases hrev with hnot | hgood
          · exact False.elim (hnot hends.1)
          · exact ⟨Sum.inr q.1, hgood, Or.inl rfl⟩
        · dsimp [TwoBiteStageRevealedVertex] at hrev
          rcases hrev with hnot | hgood
          · exact False.elim (hnot hends.2)
          · exact ⟨Sum.inr q.2, hgood, Or.inr rfl⟩
  let stageVertices : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteStageF1 ω I x ∨ TwoBiteStageF2 ω ε I x)
  have hTouched_endpoint_in_stage :
      ∀ e ∈ TwoBiteTouchedProjectedPairs ω ε I,
        ∃ x ∈ stageVertices,
          match e with
          | Sum.inl q => x = Sum.inl q.1 ∨ x = Sum.inl q.2
          | Sum.inr q => x = Sum.inr q.1 ∨ x = Sum.inr q.2 := by
    intro e he
    rcases hTouched_endpoint_stage e he with ⟨x, hxStage, hxEndpoint⟩
    exact ⟨x, by simp [stageVertices, hxStage], hxEndpoint⟩
  have hLargeHuge_bound :
      ((TwoBiteLargeHugeVertices ω ε I).card : ℝ) <
        Real.rpow (n : ℝ) (1 / 4 : ℝ) :=
    LargeHugeVertexCountBound ω I ε ε1 ε2 hComparisons hn hI hFiber
  let f2Vertices : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteStageF2 ω ε I x)
  have hF2_card_lt_of_subset :
      f2Vertices ⊆ TwoBiteLargeHugeVertices ω ε I →
        ((f2Vertices.card : ℝ) < Real.rpow (n : ℝ) (1 / 4 : ℝ)) := by
    intro hF2_subset
    exact lt_of_le_of_lt
      (by exact_mod_cast Finset.card_le_card hF2_subset)
      hLargeHuge_bound
  have hStage_numeric_absorb :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
        ε1 * (I.card : ℝ) ^ 2 := by
    have hCompn := hComparisons n hn
    dsimp [ParameterHierarchyEventualComparisons] at hCompn
    rcases hCompn with
      ⟨_hm_pos, _hp_nonneg, _hp_le, _hpm_ge_one, _hkReal_le, _hk_lt,
        _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
        _h16, _h17, _h18, _h19, _h20, _heps2_small,
        _heps2_nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
        _hLargeHugeCutoff, _hStageUpper, _hOneUnit, _hGap,
        _h33, hStageTouchedAbsorb, _h35, _h36⟩
    have hK :
        ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℕ) : ℝ) =
          (I.card : ℝ) := by
      exact_mod_cast hI.symm
    simpa [hK] using hStageTouchedAbsorb
  have hL_pos : 0 < Real.log (n : ℝ) := by
    have hCompn := hComparisons n hn
    dsimp [ParameterHierarchyEventualComparisons] at hCompn
    rcases hCompn with
      ⟨hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
        _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
        _h16, _h17, _h18, _h19, _h20, _heps2_small,
        _heps2_nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
        _hLargeHugeCutoff, _hStageUpper, _hOneUnit, _hGap,
        _h33, _h34, _h35, _h36⟩
    have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
    have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) :=
      Real.sqrt_nonneg _
    have hsqrt_pos :
        0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
      by_contra hnot
      have hsqrt_zero :
          Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) = 0 :=
        le_antisymm (le_of_not_gt hnot) hsqrt_nonneg
      nlinarith only [hpm_ge_one, hm_pos, hsqrt_zero]
    have hratio_pos :
        0 < Real.log (n : ℝ) / (n : ℝ) :=
      Real.sqrt_pos.mp hsqrt_pos
    have hmul_pos :
        0 < (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) :=
      mul_pos hratio_pos hn_real_pos
    rwa [div_mul_cancel₀ _ (ne_of_gt hn_real_pos)] at hmul_pos
  have hBase_pairs_incident_card_le :
      ∀ (X : Finset (Fin m)) (r : Fin m),
        (((TwoBiteBasePairs X).filter
          (fun q : Fin m × Fin m => q.1 = r ∨ q.2 = r)).card) ≤
          X.card := by
    intro X r
    let partner : Fin m × Fin m → Fin m :=
      fun q => if q.1 = r then q.2 else q.1
    refine Finset.card_le_card_of_injOn partner ?incident_maps ?incident_inj
    · intro q hq
      have hq' := hq
      simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq'
      rcases hq'.2 with hqr | hqr
      · simp [partner, hqr, hq'.1.1.2]
      · have hnot : q.1 ≠ r := by
          intro h
          have hlt : q.2.val < q.2.val := by
            calc
              q.2.val = r.val := by simpa [hqr]
              _ = q.1.val := by simpa [h]
              _ < q.2.val := hq'.1.2
          exact (lt_irrefl q.2.val hlt).elim
        simp [partner, hnot, hq'.1.1.1]
    · intro a ha b hb hab
      have ha' := ha
      have hb' := hb
      simp [TwoBiteBasePairs, TwoBitePairsInSet] at ha' hb'
      rcases ha'.2 with ha_inc | ha_inc <;> rcases hb'.2 with hb_inc | hb_inc
      · have ha_partner : partner a = a.2 := by simp [partner, ha_inc]
        have hb_partner : partner b = b.2 := by simp [partner, hb_inc]
        have h2 : a.2 = b.2 := by simpa [ha_partner, hb_partner] using hab
        cases a
        cases b
        simp_all
      · have ha_partner : partner a = a.2 := by simp [partner, ha_inc]
        have hb_not : b.1 ≠ r := by
          intro h
          have hlt : b.2.val < b.2.val := by
            calc
              b.2.val = r.val := by simpa [hb_inc]
              _ = b.1.val := by simpa [h]
              _ < b.2.val := hb'.1.2
          exact (lt_irrefl b.2.val hlt).elim
        have hb_partner : partner b = b.1 := by simp [partner, hb_not]
        have h_eq : a.2 = b.1 := by simpa [ha_partner, hb_partner] using hab
        have hlt : b.1.val < b.1.val := by
          calc
            b.1.val < b.2.val := hb'.1.2
            _ = r.val := by simpa [hb_inc]
            _ = a.1.val := by simpa [ha_inc]
            _ < a.2.val := ha'.1.2
            _ = b.1.val := by simpa [h_eq]
        exact (lt_irrefl b.1.val hlt).elim
      · have ha_not : a.1 ≠ r := by
          intro h
          have hlt : a.2.val < a.2.val := by
            calc
              a.2.val = r.val := by simpa [ha_inc]
              _ = a.1.val := by simpa [h]
              _ < a.2.val := ha'.1.2
          exact (lt_irrefl a.2.val hlt).elim
        have ha_partner : partner a = a.1 := by simp [partner, ha_not]
        have hb_partner : partner b = b.2 := by simp [partner, hb_inc]
        have h_eq : a.1 = b.2 := by simpa [ha_partner, hb_partner] using hab
        have hlt : a.1.val < a.1.val := by
          calc
            a.1.val < a.2.val := ha'.1.2
            _ = r.val := by simpa [ha_inc]
            _ = b.1.val := by simpa [hb_inc]
            _ < b.2.val := hb'.1.2
            _ = a.1.val := by simpa [h_eq]
        exact (lt_irrefl a.1.val hlt).elim
      · have ha_not : a.1 ≠ r := by
          intro h
          have hlt : a.2.val < a.2.val := by
            calc
              a.2.val = r.val := by simpa [ha_inc]
              _ = a.1.val := by simpa [h]
              _ < a.2.val := ha'.1.2
          exact (lt_irrefl a.2.val hlt).elim
        have hb_not : b.1 ≠ r := by
          intro h
          have hlt : b.2.val < b.2.val := by
            calc
              b.2.val = r.val := by simpa [hb_inc]
              _ = b.1.val := by simpa [h]
              _ < b.2.val := hb'.1.2
          exact (lt_irrefl b.2.val hlt).elim
        have ha_partner : partner a = a.1 := by simp [partner, ha_not]
        have hb_partner : partner b = b.1 := by simp [partner, hb_not]
        have h1 : a.1 = b.1 := by simpa [ha_partner, hb_partner] using hab
        cases a
        cases b
        simp_all
  let incidentPairs : TwoBiteBaseVertex m →
      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    fun x =>
      (TwoBiteProjectionPairSet ω I).filter
        (fun e =>
          match x, e with
          | Sum.inl r, Sum.inl q => q.1 = r ∨ q.2 = r
          | Sum.inr b, Sum.inr q => q.1 = b ∨ q.2 = b
          | _, _ => False)
  have hTouched_subset :
      TwoBiteTouchedProjectedPairs ω ε I ⊆
        stageVertices.biUnion incidentPairs := by
    intro e he
    rcases hTouched_endpoint_in_stage e he with ⟨x, hxStage, hxEndpoint⟩
    have he_pair : e ∈ TwoBiteProjectionPairSet ω I := by
      simpa [TwoBiteTouchedProjectedPairs] using (Finset.mem_filter.mp he).1
    rw [Finset.mem_biUnion]
    refine ⟨x, hxStage, ?_⟩
    cases e with
    | inl q =>
        rcases hxEndpoint with hx | hx
        · subst x
          simp [incidentPairs, he_pair]
        · subst x
          simp [incidentPairs, he_pair]
    | inr q =>
        rcases hxEndpoint with hx | hx
        · subst x
          simp [incidentPairs, he_pair]
        · subst x
          simp [incidentPairs, he_pair]
  have hIncident_card_le :
      ∀ x ∈ stageVertices, (incidentPairs x).card ≤ I.card := by
    intro x hx
    cases x with
    | inl r =>
        let redIncident : Finset (Fin m × Fin m) :=
          (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).filter
            (fun q => q.1 = r ∨ q.2 = r)
        have hsubset :
            incidentPairs (Sum.inl r) ⊆ redIncident.image Sum.inl := by
          intro e he
          cases e with
          | inl q =>
              simp [incidentPairs, redIncident, TwoBiteProjectionPairSet] at he ⊢
              exact he
          | inr q =>
              simp [incidentPairs] at he
        have h1 : (incidentPairs (Sum.inl r)).card ≤ (redIncident.image Sum.inl).card :=
          Finset.card_le_card hsubset
        have h2 : (redIncident.image Sum.inl).card ≤ redIncident.card :=
          Finset.card_image_le (s := redIncident) (f := (Sum.inl :
            Fin m × Fin m → Sum (Fin m × Fin m) (Fin m × Fin m)))
        have h3 : redIncident.card ≤ (I.image (TwoBiteRedProjection ω)).card := by
          simpa [redIncident] using
            hBase_pairs_incident_card_le (I.image (TwoBiteRedProjection ω)) r
        have h4 : (I.image (TwoBiteRedProjection ω)).card ≤ I.card :=
          Finset.card_image_le (s := I) (f := TwoBiteRedProjection ω)
        exact le_trans h1 (le_trans h2 (le_trans h3 h4))
    | inr b =>
        let blueIncident : Finset (Fin m × Fin m) :=
          (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).filter
            (fun q => q.1 = b ∨ q.2 = b)
        have hsubset :
            incidentPairs (Sum.inr b) ⊆ blueIncident.image Sum.inr := by
          intro e he
          cases e with
          | inl q =>
              simp [incidentPairs] at he
          | inr q =>
              simp [incidentPairs, blueIncident, TwoBiteProjectionPairSet] at he ⊢
              exact he
        have h1 : (incidentPairs (Sum.inr b)).card ≤ (blueIncident.image Sum.inr).card :=
          Finset.card_le_card hsubset
        have h2 : (blueIncident.image Sum.inr).card ≤ blueIncident.card :=
          Finset.card_image_le (s := blueIncident) (f := (Sum.inr :
            Fin m × Fin m → Sum (Fin m × Fin m) (Fin m × Fin m)))
        have h3 : blueIncident.card ≤ (I.image (TwoBiteBlueProjection ω)).card := by
          simpa [blueIncident] using
            hBase_pairs_incident_card_le (I.image (TwoBiteBlueProjection ω)) b
        have h4 : (I.image (TwoBiteBlueProjection ω)).card ≤ I.card :=
          Finset.card_image_le (s := I) (f := TwoBiteBlueProjection ω)
        exact le_trans h1 (le_trans h2 (le_trans h3 h4))
  have hTouched_card_nat_le :
      (TwoBiteTouchedProjectedPairs ω ε I).card ≤
        stageVertices.card * I.card := by
    have hTouched_card_le_union :
        (TwoBiteTouchedProjectedPairs ω ε I).card ≤
          (stageVertices.biUnion incidentPairs).card :=
      Finset.card_le_card hTouched_subset
    have hUnion_card_le_sum :
        (stageVertices.biUnion incidentPairs).card ≤
          stageVertices.sum (fun x => (incidentPairs x).card) :=
      Finset.card_biUnion_le
    have hsum_le :
        stageVertices.sum (fun x => (incidentPairs x).card) ≤
          stageVertices.sum (fun _x => I.card) := by
      exact Finset.sum_le_sum hIncident_card_le
    have hsum_const :
        stageVertices.sum (fun _x : TwoBiteBaseVertex m => I.card) =
          stageVertices.card * I.card := by
      simp
    exact le_trans hTouched_card_le_union
      (le_trans hUnion_card_le_sum (by simpa [hsum_const] using hsum_le))
  let f1Vertices : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteStageF1 ω I x)
  have hF1_card_le :
      ((f1Vertices.card : ℝ) ≤ 2 * (I.card : ℝ) / Real.log (n : ℝ)) := by
    let L : ℝ := Real.log (n : ℝ)
    let fiberFor : TwoBiteBaseVertex m → Finset (Fin n) :=
      fun x => TwoBiteBaseFiber ω x ∩ I
    let color : TwoBiteBaseVertex m → Bool := fun x =>
      match x with
      | Sum.inl _ => false
      | Sum.inr _ => true
    have hfiber_lower :
        ∀ x ∈ f1Vertices, L < ((fiberFor x).card : ℝ) := by
      intro x hx
      have hxF1 : TwoBiteStageF1 ω I x := by
        simpa [f1Vertices] using (Finset.mem_filter.mp hx).2
      simpa [fiberFor, L, TwoBiteStageF1] using hxF1.2
    have hsum_lower :
        (f1Vertices.card : ℝ) * L ≤
          f1Vertices.sum (fun x => ((fiberFor x).card : ℝ)) := by
      calc
        (f1Vertices.card : ℝ) * L =
            f1Vertices.sum (fun _x : TwoBiteBaseVertex m => L) := by
          simp [nsmul_eq_mul]
        _ ≤ f1Vertices.sum (fun x => ((fiberFor x).card : ℝ)) := by
          exact Finset.sum_le_sum (fun x hx => le_of_lt (hfiber_lower x hx))
    have hsigma_card :
        (f1Vertices.sigma fiberFor).card =
          f1Vertices.sum (fun x => (fiberFor x).card) := by
      exact Finset.card_sigma f1Vertices fiberFor
    have hsigma_lower :
        (f1Vertices.card : ℝ) * L ≤
          ((f1Vertices.sigma fiberFor).card : ℝ) := by
      have hsigma_card_real :
          ((f1Vertices.sigma fiberFor).card : ℝ) =
            f1Vertices.sum (fun x => ((fiberFor x).card : ℝ)) := by
        exact_mod_cast hsigma_card
      simpa [hsigma_card_real] using hsum_lower
    let codomain : Finset (Fin n × Bool) :=
      I.product (Finset.univ : Finset Bool)
    have hsigma_to_product :
        (f1Vertices.sigma fiberFor).card ≤ codomain.card := by
      refine Finset.card_le_card_of_injOn
        (fun z : Sigma fun _ : TwoBiteBaseVertex m => Fin n =>
          (z.2, color z.1)) ?f1_maps ?f1_inj
      · intro z hz
        rcases z with ⟨x, v⟩
        have hz' := Finset.mem_sigma.mp hz
        rcases hz' with ⟨_hxF1, hvfiber⟩
        have hvI : v ∈ I := (Finset.mem_inter.mp hvfiber).2
        simp [codomain, hvI]
      · intro a ha b hb hab
        rcases a with ⟨x, v⟩
        rcases b with ⟨y, w⟩
        have ha' := Finset.mem_sigma.mp ha
        have hb' := Finset.mem_sigma.mp hb
        rcases ha' with ⟨_hxF1mem, hvfiber⟩
        rcases hb' with ⟨_hyF1mem, hwfiber⟩
        have hvw : v = w := by
          exact congrArg Prod.fst hab
        have hcolor : color x = color y := by
          exact congrArg Prod.snd hab
        have hxy : x = y := by
          cases x with
          | inl r =>
              cases y with
              | inl s =>
                  have hvProj : TwoBiteRedProjection ω v = r := by
                    simpa [fiberFor, TwoBiteBaseFiber, RedFiber] using
                      (Finset.mem_inter.mp hvfiber).1
                  have hwProj : TwoBiteRedProjection ω w = s := by
                    simpa [fiberFor, TwoBiteBaseFiber, RedFiber] using
                      (Finset.mem_inter.mp hwfiber).1
                  have hrs : r = s := by
                    calc
                      r = TwoBiteRedProjection ω v := hvProj.symm
                      _ = TwoBiteRedProjection ω w := by rw [hvw]
                      _ = s := hwProj
                  simp [hrs]
              | inr b =>
                  simp [color] at hcolor
          | inr b =>
              cases y with
              | inl r =>
                  simp [color] at hcolor
              | inr c =>
                  have hvProj : TwoBiteBlueProjection ω v = b := by
                    simpa [fiberFor, TwoBiteBaseFiber, BlueFiber] using
                      (Finset.mem_inter.mp hvfiber).1
                  have hwProj : TwoBiteBlueProjection ω w = c := by
                    simpa [fiberFor, TwoBiteBaseFiber, BlueFiber] using
                      (Finset.mem_inter.mp hwfiber).1
                  have hbc : b = c := by
                    calc
                      b = TwoBiteBlueProjection ω v := hvProj.symm
                      _ = TwoBiteBlueProjection ω w := by rw [hvw]
                      _ = c := hwProj
                  simp [hbc]
        subst y
        cases hvw
        rfl
    have hcodomain_card : codomain.card = I.card * 2 := by
      simp [codomain]
    have hsigma_upper :
        ((f1Vertices.sigma fiberFor).card : ℝ) ≤ 2 * (I.card : ℝ) := by
      have hnat : (f1Vertices.sigma fiberFor).card ≤ I.card * 2 := by
        simpa [hcodomain_card] using hsigma_to_product
      have hreal : ((f1Vertices.sigma fiberFor).card : ℝ) ≤ (I.card : ℝ) * 2 := by
        exact_mod_cast hnat
      nlinarith
    have hmul :
        (f1Vertices.card : ℝ) * L ≤ 2 * (I.card : ℝ) :=
      le_trans hsigma_lower hsigma_upper
    have hdiv :
        (f1Vertices.card : ℝ) ≤ 2 * (I.card : ℝ) / L := by
      rw [le_div_iff₀ (by simpa [L] using hL_pos)]
      simpa [L] using hmul
    simpa [L] using hdiv
  have hF2_subset :
      f2Vertices ⊆ TwoBiteLargeHugeVertices ω ε I := by
    intro x hx
    have hxF2 : TwoBiteStageF2 ω ε I x := by
      simpa [f2Vertices] using (Finset.mem_filter.mp hx).2
    let L : ℝ := Real.log (n : ℝ)
    let Nbase : Finset (TwoBiteBaseVertex m) :=
      (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
        (fun y => TwoBiteStageF1 ω I y ∧ TwoBiteBaseAdj ω x y)
    have hNgt :
        TwoBiteLargeCutoff ε n / L < (Nbase.card : ℝ) := by
      simpa [TwoBiteStageF2, Nbase, L] using hxF2.2
    let fiberFor : TwoBiteBaseVertex m → Finset (Fin n) :=
      fun y => TwoBiteBaseFiber ω y ∩ I
    let X : Finset (Fin n) := TwoBiteX ω I x
    have hfiber_lower :
        ∀ y ∈ Nbase, L < ((fiberFor y).card : ℝ) := by
      intro y hy
      have hyF1 : TwoBiteStageF1 ω I y := by
        simpa [Nbase] using (Finset.mem_filter.mp hy).2.1
      simpa [fiberFor, L, TwoBiteStageF1] using hyF1.2
    have hsum_lower :
        (Nbase.card : ℝ) * L ≤
          Nbase.sum (fun y => ((fiberFor y).card : ℝ)) := by
      calc
        (Nbase.card : ℝ) * L = Nbase.sum (fun _y : TwoBiteBaseVertex m => L) := by
          simp [nsmul_eq_mul]
        _ ≤ Nbase.sum (fun y => ((fiberFor y).card : ℝ)) := by
          exact Finset.sum_le_sum (fun y hy => le_of_lt (hfiber_lower y hy))
    have hsigma_card :
        (Nbase.sigma fiberFor).card =
          Nbase.sum (fun y => (fiberFor y).card) := by
      exact Finset.card_sigma Nbase fiberFor
    have hsigma_to_X :
        (Nbase.sigma fiberFor).card ≤ X.card := by
      refine Finset.card_le_card_of_injOn
        (fun z : Sigma fun _ : TwoBiteBaseVertex m => Fin n => z.2) ?f2_maps ?f2_inj
      · intro z hz
        rcases z with ⟨y, v⟩
        have hz' := Finset.mem_sigma.mp hz
        rcases hz' with ⟨hyN, hvfiber⟩
        have hyAdj : TwoBiteBaseAdj ω x y := by
          simpa [Nbase] using (Finset.mem_filter.mp hyN).2.2
        have hvI : v ∈ I := (Finset.mem_inter.mp hvfiber).2
        cases x with
        | inl r =>
            cases y with
            | inl s =>
                have hvProj : TwoBiteRedProjection ω v = s := by
                  simpa [fiberFor, TwoBiteBaseFiber, RedFiber] using
                    (Finset.mem_inter.mp hvfiber).1
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood, hvI, hvProj,
                  TwoBiteBaseAdj] using hyAdj
            | inr b =>
                simp [TwoBiteBaseAdj] at hyAdj
        | inr b =>
            cases y with
            | inl r =>
                simp [TwoBiteBaseAdj] at hyAdj
            | inr c =>
                have hvProj : TwoBiteBlueProjection ω v = c := by
                  simpa [fiberFor, TwoBiteBaseFiber, BlueFiber] using
                    (Finset.mem_inter.mp hvfiber).1
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood, hvI, hvProj,
                  TwoBiteBaseAdj] using hyAdj
      · intro a ha b hb hab
        rcases a with ⟨y, v⟩
        rcases b with ⟨z, w⟩
        have ha' := Finset.mem_sigma.mp ha
        have hb' := Finset.mem_sigma.mp hb
        rcases ha' with ⟨hyN, hvfiber⟩
        rcases hb' with ⟨hzN, hwfiber⟩
        have hyAdj : TwoBiteBaseAdj ω x y := by
          simpa [Nbase] using (Finset.mem_filter.mp hyN).2.2
        have hzAdj : TwoBiteBaseAdj ω x z := by
          simpa [Nbase] using (Finset.mem_filter.mp hzN).2.2
        have hyz : y = z := by
          cases x with
          | inl r =>
              cases y with
              | inl s =>
                  cases z with
                  | inl t =>
                      have hvProj : TwoBiteRedProjection ω v = s := by
                        simpa [fiberFor, TwoBiteBaseFiber, RedFiber] using
                          (Finset.mem_inter.mp hvfiber).1
                      have hwProj : TwoBiteRedProjection ω w = t := by
                        simpa [fiberFor, TwoBiteBaseFiber, RedFiber] using
                          (Finset.mem_inter.mp hwfiber).1
                      have hvw : v = w := by simpa using hab
                      have hst : s = t := by
                        calc
                          s = TwoBiteRedProjection ω v := hvProj.symm
                          _ = TwoBiteRedProjection ω w := by rw [hvw]
                          _ = t := hwProj
                      simp [hst]
                  | inr c =>
                      simp [TwoBiteBaseAdj] at hzAdj
              | inr b =>
                  simp [TwoBiteBaseAdj] at hyAdj
          | inr b =>
              cases y with
              | inl r =>
                  simp [TwoBiteBaseAdj] at hyAdj
              | inr c =>
                  cases z with
                  | inl r =>
                      simp [TwoBiteBaseAdj] at hzAdj
                  | inr d =>
                      have hvProj : TwoBiteBlueProjection ω v = c := by
                        simpa [fiberFor, TwoBiteBaseFiber, BlueFiber] using
                          (Finset.mem_inter.mp hvfiber).1
                      have hwProj : TwoBiteBlueProjection ω w = d := by
                        simpa [fiberFor, TwoBiteBaseFiber, BlueFiber] using
                          (Finset.mem_inter.mp hwfiber).1
                      have hvw : v = w := by simpa using hab
                      have hcd : c = d := by
                        calc
                          c = TwoBiteBlueProjection ω v := hvProj.symm
                          _ = TwoBiteBlueProjection ω w := by rw [hvw]
                          _ = d := hwProj
                      simp [hcd]
        subst z
        cases hab
        rfl
    have hlarge_lt_X : TwoBiteLargeCutoff ε n < (X.card : ℝ) := by
      have hsum_le_X :
          Nbase.sum (fun y => ((fiberFor y).card : ℝ)) ≤ (X.card : ℝ) := by
        have hnat :
            Nbase.sum (fun y => (fiberFor y).card) ≤ X.card := by
          simpa [hsigma_card] using hsigma_to_X
        exact_mod_cast hnat
      have hmul :
          TwoBiteLargeCutoff ε n < (Nbase.card : ℝ) * L := by
        have hmul' :
            (TwoBiteLargeCutoff ε n / L) * L < (Nbase.card : ℝ) * L :=
          mul_lt_mul_of_pos_right hNgt (by simpa [L] using hL_pos)
        rwa [div_mul_cancel₀ _ (ne_of_gt (by simpa [L] using hL_pos))] at hmul'
      exact lt_of_lt_of_le hmul (le_trans hsum_lower hsum_le_X)
    have hX_subset_I : X ⊆ I := by
      intro v hv
      exact (by simpa [X, TwoBiteX] using hv :
        v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x).1
    have hX_nat_le_I : X.card ≤ I.card :=
      Finset.card_le_card hX_subset_I
    by_cases hX_le_huge : ((X.card : ℝ) ≤ TwoBiteHugeCutoff n)
    · simp [TwoBiteLargeHugeVertices, TwoBiteLargeClass, TwoBiteHugeClass, X,
        hlarge_lt_X, hX_le_huge]
    · have hHuge_lt : TwoBiteHugeCutoff n < ((X.card : ℝ)) := lt_of_not_ge hX_le_huge
      simp [TwoBiteLargeHugeVertices, TwoBiteLargeClass, TwoBiteHugeClass, X,
        hHuge_lt, hX_nat_le_I]
  have hStage_card_le_real :
      ((stageVertices.card : ℝ) ≤
        2 * (I.card : ℝ) / Real.log (n : ℝ) +
          Real.rpow (n : ℝ) (1 / 4 : ℝ)) := by
    have hStage_subset : stageVertices ⊆ f1Vertices ∪ f2Vertices := by
      intro x hx
      have hxStage : TwoBiteStageF1 ω I x ∨ TwoBiteStageF2 ω ε I x := by
        simpa [stageVertices] using (Finset.mem_filter.mp hx).2
      rcases hxStage with hxF1 | hxF2
      · exact Finset.mem_union.mpr
          (Or.inl (by simp [f1Vertices, hxF1]))
      · exact Finset.mem_union.mpr
          (Or.inr (by simp [f2Vertices, hxF2]))
    have hStage_nat_le :
        stageVertices.card ≤ f1Vertices.card + f2Vertices.card := by
      exact le_trans (Finset.card_le_card hStage_subset)
        (Finset.card_union_le f1Vertices f2Vertices)
    have hStage_real_le :
        ((stageVertices.card : ℝ) ≤
          (f1Vertices.card : ℝ) + (f2Vertices.card : ℝ)) := by
      exact_mod_cast hStage_nat_le
    have hF2_card_le :
        ((f2Vertices.card : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ)) :=
      le_of_lt (hF2_card_lt_of_subset hF2_subset)
    nlinarith only [hStage_real_le, hF1_card_le, hF2_card_le]
  have hTouched_real_le :
      ((TwoBiteTouchedProjectedPairs ω ε I).card : ℝ) ≤
        (stageVertices.card : ℝ) * (I.card : ℝ) := by
    exact_mod_cast hTouched_card_nat_le
  have hI_nonneg : 0 ≤ (I.card : ℝ) := by exact_mod_cast Nat.zero_le I.card
  have hStage_mul_le :
      (stageVertices.card : ℝ) * (I.card : ℝ) ≤
        (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            Real.rpow (n : ℝ) (1 / 4 : ℝ)) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hStage_card_le_real hI_nonneg
    nlinarith only [hmul]
  exact le_trans hTouched_real_le
    (le_trans hStage_mul_le hStage_numeric_absorb)
