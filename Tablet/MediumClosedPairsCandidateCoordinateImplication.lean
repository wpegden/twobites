import Tablet.MediumClosedPairsCandidateCellTail
import Tablet.MediumClosedPairsDeterministicWitnessCandidatePackage

open scoped BigOperators

-- [TABLET NODE: MediumClosedPairsCandidateCoordinateImplication]

theorem MediumClosedPairsCandidateCoordinateImplication
    {n m S : ℕ} {ε ε1 : ℝ}
    (i : {I : Finset (Fin n) //
        I.card = TwoBiteNaturalIndependenceScale (1 + ε) n} ×
      (Fin S → TwoBiteBaseVertex m))
    (π : Fin n ↪ (Fin m × Fin m))
    (ω : TwoBiteSample n m (TwoBiteEdgeProbability (1 / 2 : ℝ) n)) :
    let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
    let A : ℝ := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
      (6 * (Real.log (n : ℝ)) ^ 2)
    let I : Finset (Fin n) := i.1.1
    let coverB : Finset (TwoBiteBaseVertex m) := Finset.univ.image i.2
    let BR : Finset (Fin m) :=
      Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ coverB)
    let BB : Finset (Fin m) :=
      Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ coverB)
    let PR : Finset (Fin m) := I.image (fun v => (π v).1)
    let PB : Finset (Fin m) := I.image (fun v => (π v).2)
    let Candidate :
      TwoBiteSample n m (TwoBiteEdgeProbability (1 / 2 : ℝ) n) → Prop :=
      fun ω =>
        ¬ ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteMediumClass ω ε I)).card : ℝ)
            ε1 (K : ℝ) ∧
          ∃ B : Finset (TwoBiteBaseVertex m),
            let A0 := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
            B.Nonempty ∧
            B.card ≤ S ∧
            B ⊆ coverB ∧
            (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
            A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
            (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
              ≤ A0 + TwoBiteLargeCutoff ε n ∧
            (B.card : ℝ) * TwoBiteSmallCutoff ε n
              ≤ A0 + TwoBiteLargeCutoff ε n ∧
            (let redCenters : Finset (Fin m) :=
                Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
             let blueCenters : Finset (Fin m) :=
                Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
             let redProjection : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
             let blueProjection : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
             let normalize : Fin m × Fin m → Fin m × Fin m :=
                fun e => if e.1.val < e.2.val then e else (e.2, e.1)
             let redOrdered : Finset (Fin m × Fin m) :=
                @Finset.filter (Fin m × Fin m)
                  (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
                  (Classical.decPred _)
                  (redCenters.product redProjection)
             let blueOrdered : Finset (Fin m × Fin m) :=
                @Finset.filter (Fin m × Fin m)
                  (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
                  (Classical.decPred _)
                  (blueCenters.product blueProjection)
             let redEdges : Finset (Fin m × Fin m) := redOrdered.image normalize
             let blueEdges : Finset (Fin m × Fin m) := blueOrdered.image normalize
             A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
              ((redEdges.card + blueEdges.card : ℕ) : ℝ))
    let t : ℕ := Nat.ceil A
    let normalize : Fin m × Fin m → Fin m × Fin m :=
      fun e => if e.1.val < e.2.val then e else (e.2, e.1)
    let redRaw : Finset (Fin m × Fin m) :=
      (BR.product PR).filter (fun e => e.1 ≠ e.2)
    let blueRaw : Finset (Fin m × Fin m) :=
      (BB.product PB).filter (fun e => e.1 ≠ e.2)
    let C : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      redRaw.image
          (fun e => (Sum.inl (normalize e) :
            Sum (Fin m × Fin m) (Fin m × Fin m))) ∪
        blueRaw.image
          (fun e => (Sum.inr (normalize e) :
            Sum (Fin m × Fin m) (Fin m × Fin m)))
    TwoBiteEmbedding ω = π →
    Candidate ω →
    t ≤
      (@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
        (fun e => TwoBiteEdgeCoordinateValue ω e)
        (Classical.decPred _) C).card := by
-- BODY
  classical
  intro K A I coverB BR BB PR PB Candidate t normalize redRaw blueRaw C hcell hcand
  rcases hcand with ⟨_hbad, B, hB⟩
  dsimp only at hB
  rcases hB with
    ⟨_hBne, _hBcard, hBsub, _hBmedium, _hsum_gt, _hsum_le, _hBsmall,
      hcoord⟩
  let redCentersB : Finset (Fin m) :=
    Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
  let blueCentersB : Finset (Fin m) :=
    Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
  let redProjectionω : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
  let blueProjectionω : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
  let redOrdered : Finset (Fin m × Fin m) :=
    @Finset.filter (Fin m × Fin m)
      (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
      (Classical.decPred _)
      (redCentersB.product redProjectionω)
  let blueOrdered : Finset (Fin m × Fin m) :=
    @Finset.filter (Fin m × Fin m)
      (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
      (Classical.decPred _)
      (blueCentersB.product blueProjectionω)
  let redEdges : Finset (Fin m × Fin m) := redOrdered.image normalize
  let blueEdges : Finset (Fin m × Fin m) := blueOrdered.image normalize
  have hcoord' :
      A < ((redEdges.card + blueEdges.card : ℕ) : ℝ) := by
    simpa [A, redCentersB, blueCentersB, redProjectionω, blueProjectionω,
      redOrdered, blueOrdered, redEdges, blueEdges, normalize] using hcoord
  have hceil : t ≤ redEdges.card + blueEdges.card := by
    rw [Nat.ceil_le]
    exact le_of_lt hcoord'
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let redSet : Finset Coord :=
    redEdges.image
      (fun e => (Sum.inl e : Sum (Fin m × Fin m) (Fin m × Fin m)))
  let blueSet : Finset Coord :=
    blueEdges.image
      (fun e => (Sum.inr e : Sum (Fin m × Fin m) (Fin m × Fin m)))
  let E : Finset Coord := redSet ∪ blueSet
  have hred_card : redSet.card = redEdges.card := by
    dsimp [redSet]
    simpa using
      (Finset.card_image_of_injective redEdges
        (fun _ _ h => Sum.inl.inj h))
  have hblue_card : blueSet.card = blueEdges.card := by
    dsimp [blueSet]
    simpa using
      (Finset.card_image_of_injective blueEdges
        (fun _ _ h => Sum.inr.inj h))
  have hdisjoint : Disjoint redSet blueSet := by
    rw [Finset.disjoint_left]
    intro x hxred hxblue
    rcases Finset.mem_image.mp hxred with ⟨r, _hr, hrx⟩
    rcases Finset.mem_image.mp hxblue with ⟨b, _hb, hbx⟩
    rw [← hrx] at hbx
    cases hbx
  have hEcard : E.card = redEdges.card + blueEdges.card := by
    dsimp [E]
    rw [Finset.card_union_of_disjoint hdisjoint]
    rw [hred_card, hblue_card]
  have hEsubset :
      E ⊆
        (@Finset.filter Coord
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C) := by
    intro z hz
    dsimp [E, redSet, blueSet] at hz
    rw [Finset.mem_union] at hz
    rw [Finset.mem_filter]
    rcases hz with hz | hz
    · rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have he_parts := Finset.mem_filter.mp he
      have he_prod := Finset.mem_product.mp he_parts.1
      have he_adj : (TwoBiteRedGraph ω).Adj e.1 e.2 := he_parts.2
      have he_ne : e.1 ≠ e.2 := SimpleGraph.Adj.ne he_adj
      have he_center : e.1 ∈ BR := by
        have heB : Sum.inl e.1 ∈ B := (Finset.mem_filter.mp he_prod.1).2
        have heCover : Sum.inl e.1 ∈ coverB := hBsub heB
        simp [BR, heCover]
      have he_proj : e.2 ∈ PR := by
        rcases Finset.mem_image.mp he_prod.2 with ⟨v, hvI, hv⟩
        refine Finset.mem_image.mpr ⟨v, hvI, ?_⟩
        simpa [TwoBiteRedProjection, hcell] using hv
      have he_raw : e ∈ redRaw := by
        simp [redRaw, he_center, he_proj, he_ne]
      have hCmem : (Sum.inl (normalize e) : Coord) ∈ C := by
        dsimp [C]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨e, he_raw, rfl⟩)
      have hpresent :
          TwoBiteEdgeCoordinateValue ω (Sum.inl (normalize e) : Coord) := by
        have hnorm :
            (TwoBiteRedGraph ω).Adj (normalize e).1 (normalize e).2 := by
          dsimp [normalize]
          by_cases hlt : e.1.val < e.2.val
          · simpa [hlt] using he_adj
          · simpa [hlt] using he_adj.symm
        simpa [TwoBiteEdgeCoordinateValue] using hnorm
      exact ⟨hCmem, hpresent⟩
    · rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have he_parts := Finset.mem_filter.mp he
      have he_prod := Finset.mem_product.mp he_parts.1
      have he_adj : (TwoBiteBlueGraph ω).Adj e.1 e.2 := he_parts.2
      have he_ne : e.1 ≠ e.2 := SimpleGraph.Adj.ne he_adj
      have he_center : e.1 ∈ BB := by
        have heB : Sum.inr e.1 ∈ B := (Finset.mem_filter.mp he_prod.1).2
        have heCover : Sum.inr e.1 ∈ coverB := hBsub heB
        simp [BB, heCover]
      have he_proj : e.2 ∈ PB := by
        rcases Finset.mem_image.mp he_prod.2 with ⟨v, hvI, hv⟩
        refine Finset.mem_image.mpr ⟨v, hvI, ?_⟩
        simpa [TwoBiteBlueProjection, hcell] using hv
      have he_raw : e ∈ blueRaw := by
        simp [blueRaw, he_center, he_proj, he_ne]
      have hCmem : (Sum.inr (normalize e) : Coord) ∈ C := by
        dsimp [C]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨e, he_raw, rfl⟩)
      have hpresent :
          TwoBiteEdgeCoordinateValue ω (Sum.inr (normalize e) : Coord) := by
        have hnorm :
            (TwoBiteBlueGraph ω).Adj (normalize e).1 (normalize e).2 := by
          dsimp [normalize]
          by_cases hlt : e.1.val < e.2.val
          · simpa [hlt] using he_adj
          · simpa [hlt] using he_adj.symm
        simpa [TwoBiteEdgeCoordinateValue] using hnorm
      exact ⟨hCmem, hpresent⟩
  have hcard_sub :
      E.card ≤
        (@Finset.filter Coord
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C).card :=
    Finset.card_le_card hEsubset
  have hedge_le :
      redEdges.card + blueEdges.card ≤
        (@Finset.filter Coord
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C).card := by
    simpa [hEcard] using hcard_sub
  exact le_trans hceil hedge_le
