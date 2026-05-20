import Tablet.FinsetPowersetCylinderMass
import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedReleasedCylinderLeafExpansion]

theorem FixedSetHistoryCellRedReleasedCylinderLeafExpansion :
    ∀ {m uR uB : ℕ} {p : ℝ}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [Fintype BranchLabel]
      (blueTrace :
        BranchLabel →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {RedLabel : Type} [Fintype RedLabel]
      (J : RedLabel)
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellRealized :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (selectedPresentSibling :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)]
      [DecidablePred
        (fun leaf :
          BranchLabel ×
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) =>
          leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2)]
      [DecidablePred
        (fun e : Sum (Fin m × Fin m) (Fin m × Fin m) =>
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True)],
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      B.card = uB →
      B ⊆ terminal →
      (∀ e,
        e ∈ B →
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
          (redSupport β J).card = uR ∧
          redSupport β J ⊆ terminal ∧
          (∀ e,
            e ∈ redSupport β J →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) ∧
          τ.1 ⊆ terminal ∧
          τ.2.1 ⊆ terminal ∧
          Disjoint τ.1 τ.2.1 ∧
          B ∪ redSupport β J ⊆ τ.1 ∧
          (∀ e,
            e ∈ terminal →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
                (e ∈ blueTrace β ↔ e ∈ τ.1) ∧
                (e ∉ blueTrace β ↔ e ∈ τ.2.1)) ∧
          τ.2.2 ⊆ τ.2.1) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (assignmentCompatible A β τ ∨
                ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ↔
              (τ.1 ⊆ A ∧
                Disjoint (τ.2.1 \ τ.2.2) A ∧
                (∀ e,
                  e ∈ terminal →
                    e ∉ τ.2.2 →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)))) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  (β ≠ β' ∨ τ ≠ τ') →
                    ¬ ((assignmentCompatible A β τ ∨
                        ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ∧
                       (assignmentCompatible A β' τ' ∨
                        ∃ e ∈ τ'.2.2, selectedPresentSibling A β' τ' e))) →
      let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
      let Transcript := Finset Coord × Finset Coord × Finset Coord
      let Pair := BranchLabel × Transcript
      let realizedPairs : Finset Pair :=
        (Finset.univ.filter
          (fun leaf => leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2))
      let releasedCondition : Finset Coord → Pair → Prop :=
        fun A leaf =>
          leaf.2.1 ⊆ A ∧
          Disjoint (leaf.2.2.1 \ leaf.2.2.2) A ∧
          (∀ e,
            e ∈ terminal →
              e ∉ leaf.2.2.2 →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
                (e ∈ blueTrace leaf.1 ↔ e ∈ A))
      letI :
        DecidablePred
          (fun A : Finset Coord =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf) :=
        Classical.decPred _
      realizedPairs.sum
          (fun leaf =>
            p ^ leaf.2.1.card *
              ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card))
        ≤
        (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          (fun A =>
            p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
-- BODY
  classical
  intro m uR uB p terminal B BranchLabel _ blueTrace transcriptLabels
    RedLabel _ J redSupport cellRealized assignmentCompatible
    selectedPresentSibling _ _ _ hp hp_half hBcard hBterm hBblue hred
    hspan hspan_disj
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let Pair := BranchLabel × Transcript
  let realizedPairs : Finset Pair :=
    (Finset.univ.filter
      (fun leaf => leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2))
  let releasedCondition : Finset Coord → Pair → Prop :=
    fun A leaf =>
      leaf.2.1 ⊆ A ∧
      Disjoint (leaf.2.2.1 \ leaf.2.2.2) A ∧
      (∀ e,
        e ∈ terminal →
          e ∉ leaf.2.2.2 →
          (match e with
          | Sum.inl _ => False
          | Sum.inr _ => True) →
            (e ∈ blueTrace leaf.1 ↔ e ∈ A))
  letI :
    DecidablePred
      (fun A : Finset Coord =>
        ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf) :=
    Classical.decPred _
  let weight : Finset Coord → ℝ :=
    fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)
  change
    realizedPairs.sum
        (fun leaf =>
          p ^ leaf.2.1.card *
            ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card))
      ≤
      (terminal.powerset.filter
        (fun A =>
          ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
        weight
  have hleaf_sum :
      ∀ leaf, leaf ∈ realizedPairs →
        (terminal.powerset.filter
          (fun A => releasedCondition A leaf)).sum weight =
          p ^ leaf.2.1.card *
            ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card) := by
    intro leaf hleaf
    have hinfo :
        leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 :=
      (Finset.mem_filter.mp hleaf).2
    rcases hred leaf.1 leaf.2 hinfo.1 hinfo.2 with
      ⟨hRcard, hRterm, hRred, hPterm, hAterm, hPAdisj,
        hBRsub, hbluegeom, hZsub⟩
    have hDterm : leaf.2.2.1 \ leaf.2.2.2 ⊆ terminal := by
      intro e he
      exact hAterm (Finset.mem_sdiff.mp he).1
    have hPDdisj : Disjoint leaf.2.1 (leaf.2.2.1 \ leaf.2.2.2) :=
      hPAdisj.mono_right Finset.sdiff_subset
    have hfilter_eq :
        terminal.powerset.filter (fun A => releasedCondition A leaf) =
          terminal.powerset.filter
            (fun A => leaf.2.1 ⊆ A ∧ Disjoint (leaf.2.2.1 \ leaf.2.2.2) A) := by
      ext A
      constructor
      · intro hA
        rcases Finset.mem_filter.mp hA with ⟨hApow, hrel⟩
        exact Finset.mem_filter.mpr ⟨hApow, hrel.1, hrel.2.1⟩
      · intro hA
        rcases Finset.mem_filter.mp hA with ⟨hApow, hsimple⟩
        refine Finset.mem_filter.mpr ⟨hApow, ?_⟩
        refine ⟨hsimple.1, hsimple.2, ?_⟩
        intro e heterm he_not_Z heblue
        have hblue_pair := hbluegeom e heterm heblue
        constructor
        · intro he_trace
          exact hsimple.1 (hblue_pair.1.mp he_trace)
        · intro heA
          by_contra he_not_trace
          have he_absent : e ∈ leaf.2.2.1 := hblue_pair.2.mp he_not_trace
          have heD : e ∈ leaf.2.2.1 \ leaf.2.2.2 :=
            Finset.mem_sdiff.mpr ⟨he_absent, he_not_Z⟩
          exact (Finset.disjoint_left.mp hsimple.2 heD) heA
    have hDcard :
        (leaf.2.2.1 \ leaf.2.2.2).card =
          leaf.2.2.1.card - leaf.2.2.2.card :=
      Finset.card_sdiff_of_subset hZsub
    calc
      (terminal.powerset.filter
          (fun A => releasedCondition A leaf)).sum weight
          =
        (terminal.powerset.filter
          (fun A => leaf.2.1 ⊆ A ∧ Disjoint (leaf.2.2.1 \ leaf.2.2.2) A)).sum
          weight := by
          rw [hfilter_eq]
      _ =
        p ^ leaf.2.1.card *
          ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card) := by
          simpa [weight, hDcard] using
            FinsetPowersetCylinderMass
              terminal leaf.2.1 (leaf.2.2.1 \ leaf.2.2.2) p
              hPterm hDterm hPDdisj
  have huniq :
      ∀ A, A ∈ terminal.powerset →
        ∀ leaf, leaf ∈ realizedPairs → releasedCondition A leaf →
          ∀ leaf', leaf' ∈ realizedPairs → releasedCondition A leaf' →
            leaf = leaf' := by
    intro A hApow leaf hleaf hrel leaf' hleaf' hrel'
    by_cases hEq : leaf = leaf'
    · exact hEq
    · exfalso
      have hAterm : A ⊆ terminal := Finset.mem_powerset.mp hApow
      have hinfo :
          leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 :=
        (Finset.mem_filter.mp hleaf).2
      have hinfo' :
          leaf'.2 ∈ transcriptLabels ∧ cellRealized leaf'.1 leaf'.2 :=
        (Finset.mem_filter.mp hleaf').2
      have hdiff : leaf.1 ≠ leaf'.1 ∨ leaf.2 ≠ leaf'.2 := by
        by_cases hβ : leaf.1 = leaf'.1
        · right
          intro hτ
          exact hEq (Prod.ext hβ hτ)
        · exact Or.inl hβ
      have hspan_leaf :
          assignmentCompatible A leaf.1 leaf.2 ∨
            ∃ e ∈ leaf.2.2.2, selectedPresentSibling A leaf.1 leaf.2 e :=
        ((hspan A leaf.1 leaf.2).mpr hrel) hAterm hinfo.1 hinfo.2
      have hspan_leaf' :
          assignmentCompatible A leaf'.1 leaf'.2 ∨
            ∃ e ∈ leaf'.2.2.2, selectedPresentSibling A leaf'.1 leaf'.2 e :=
        ((hspan A leaf'.1 leaf'.2).mpr hrel') hAterm hinfo'.1 hinfo'.2
      exact
        (hspan_disj A leaf.1 leaf'.1 leaf.2 leaf'.2
          hAterm hinfo.1 hinfo'.1 hinfo.2 hinfo'.2 hdiff)
          ⟨hspan_leaf, hspan_leaf'⟩
  have hunion_sum :
      realizedPairs.sum
          (fun leaf =>
            (terminal.powerset.filter
              (fun A => releasedCondition A leaf)).sum weight)
        =
        (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          weight := by
    let cellSet : Pair → Finset (Finset Coord) :=
      fun leaf => terminal.powerset.filter (fun A => releasedCondition A leaf)
    have hcover :
        terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf) =
          realizedPairs.biUnion cellSet := by
      ext A
      constructor
      · intro hA
        rcases Finset.mem_filter.mp hA with ⟨hApow, leaf, hleaf, hrel⟩
        rw [Finset.mem_biUnion]
        exact ⟨leaf, hleaf, by simp [cellSet, hApow, hrel]⟩
      · intro hA
        rw [Finset.mem_biUnion] at hA
        rcases hA with ⟨leaf, hleaf, hAleaf⟩
        have hAleaf' : A ∈ terminal.powerset.filter
            (fun A => releasedCondition A leaf) := by
          simpa [cellSet] using hAleaf
        rcases Finset.mem_filter.mp hAleaf' with ⟨hApow, hrel⟩
        exact Finset.mem_filter.mpr ⟨hApow, leaf, hleaf, hrel⟩
    have hdisj : (↑realizedPairs : Set Pair).PairwiseDisjoint cellSet := by
      rw [Finset.pairwiseDisjoint_iff]
      intro leaf hleaf leaf' hleaf' hnonempty
      rcases hnonempty with ⟨A, hA⟩
      have hAleft : A ∈ terminal.powerset ∧ releasedCondition A leaf := by
        have hmem : A ∈ cellSet leaf := (Finset.mem_inter.mp hA).1
        simpa [cellSet] using hmem
      have hAright : A ∈ terminal.powerset ∧ releasedCondition A leaf' := by
        have hmem : A ∈ cellSet leaf' := (Finset.mem_inter.mp hA).2
        simpa [cellSet] using hmem
      exact huniq A hAleft.1 leaf hleaf hAleft.2 leaf' hleaf' hAright.2
    calc
      realizedPairs.sum
          (fun leaf =>
            (terminal.powerset.filter
              (fun A => releasedCondition A leaf)).sum weight)
          =
          (realizedPairs.biUnion cellSet).sum weight := by
          rw [Finset.sum_biUnion hdisj]
      _ =
        (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          weight := by
          rw [← hcover]
  have hEq :
      realizedPairs.sum
          (fun leaf =>
            p ^ leaf.2.1.card *
              ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card))
        =
        (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          weight := by
    calc
      realizedPairs.sum
          (fun leaf =>
            p ^ leaf.2.1.card *
              ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card))
          =
        realizedPairs.sum
          (fun leaf =>
            (terminal.powerset.filter
              (fun A => releasedCondition A leaf)).sum weight) := by
          refine Finset.sum_congr rfl ?_
          intro leaf hleaf
          exact (hleaf_sum leaf hleaf).symm
      _ =
        (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          weight := hunion_sum
  exact le_of_eq hEq
