import Mathlib.Tactic.Linarith
import Tablet.FinsetBlueFiberRedSupportMass
import Tablet.FinsetBlueSupportMassBound
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace

-- [TABLET NODE: FixedSetHistoryCellRedReleasedCylinderUnionMassBound]

theorem FixedSetHistoryCellRedReleasedCylinderUnionMassBound :
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
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            (match e with
            | Sum.inl _ => False
            | Sum.inr _ => True) →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
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
          (∀ e,
            e ∈ τ.2.2 →
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
      (terminal.powerset.filter
          (fun A =>
            ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)).sum
          (fun A =>
            p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
        ≤
        p ^ uR * p ^ uB := by
-- BODY
  classical
  intro m uR uB p terminal B BranchLabel _ blueTrace transcriptLabels
    RedLabel _ J redSupport cellRealized _ _ _ hp hp_half hBcard hBterm
    hBblue hbranch hred
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let Pair := BranchLabel × Transcript
  let isBlue : Coord → Prop :=
    fun e =>
      match e with
      | Sum.inl _ => False
      | Sum.inr _ => True
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
          isBlue e →
            (e ∈ blueTrace leaf.1 ↔ e ∈ A))
  letI :
    DecidablePred
      (fun A : Finset Coord =>
        ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf) :=
    Classical.decPred _
  let weight : Finset Coord → ℝ :=
    fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)
  let target : Finset (Finset Coord) :=
    terminal.powerset.filter
      (fun A =>
        ∃ leaf, leaf ∈ realizedPairs ∧ releasedCondition A leaf)
  let blueTerminal : Finset Coord := terminal.filter isBlue
  let bluePart : Finset Coord → Finset Coord :=
    fun A => A ∩ blueTerminal
  let blueWeight : Finset Coord → ℝ :=
    fun S => p ^ S.card * ((1 : ℝ) - p) ^ (blueTerminal.card - S.card)
  let traces : Finset (Finset Coord) := target.image bluePart
  change target.sum weight ≤ p ^ uR * p ^ uB
  have hp_one : p ≤ (1 : ℝ) := by
    linarith
  have hq_nonneg : 0 ≤ (1 : ℝ) - p := by
    linarith
  have hweight_nonneg :
      ∀ A ∈ terminal.powerset, 0 ≤ weight A := by
    intro A hA
    exact mul_nonneg (pow_nonneg hp _) (pow_nonneg hq_nonneg _)
  have hblueTerm : blueTerminal ⊆ terminal := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hBblueTerm : B ⊆ blueTerminal := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hBterm he, hBblue e he⟩
  have htarget_cover :
      target = traces.biUnion (fun S => target.filter (fun A => bluePart A = S)) := by
    ext A
    constructor
    · intro hA
      rw [Finset.mem_biUnion]
      exact
        ⟨bluePart A, Finset.mem_image.mpr ⟨A, hA, rfl⟩,
          Finset.mem_filter.mpr ⟨hA, rfl⟩⟩
    · intro hA
      rw [Finset.mem_biUnion] at hA
      rcases hA with ⟨S, hS, hAfiber⟩
      exact (Finset.mem_filter.mp hAfiber).1
  have hfiber_disj :
      (↑traces : Set (Finset Coord)).PairwiseDisjoint
        (fun S => target.filter (fun A => bluePart A = S)) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro S hS S' hS' hnonempty
    rcases hnonempty with ⟨A, hA⟩
    have hleft :
        A ∈ target.filter (fun A => bluePart A = S) :=
      (Finset.mem_inter.mp hA).1
    have hright :
        A ∈ target.filter (fun A => bluePart A = S') :=
      (Finset.mem_inter.mp hA).2
    have hS_eq : bluePart A = S := (Finset.mem_filter.mp hleft).2
    have hS'_eq : bluePart A = S' := (Finset.mem_filter.mp hright).2
    exact hS_eq.symm.trans hS'_eq
  have htarget_sum :
      target.sum weight =
        traces.sum
          (fun S => (target.filter (fun A => bluePart A = S)).sum weight) := by
    calc
      target.sum weight =
          (traces.biUnion
            (fun S => target.filter (fun A => bluePart A = S))).sum weight := by
          rw [← htarget_cover]
      _ =
          traces.sum
            (fun S => (target.filter (fun A => bluePart A = S)).sum weight) := by
          rw [Finset.sum_biUnion hfiber_disj]
  have hblue_of_not_red :
      ∀ e : Coord,
        isBlue e →
        (match e with
        | Sum.inl _ => True
        | Sum.inr _ => False) →
          False := by
    intro e heBlue heRed
    cases e <;> simp [isBlue] at heBlue heRed
  have htrace_agree_of_same_bluePart :
      ∀ {A A' : Finset Coord} {leaf leaf' : Pair},
        A ∈ target →
        A' ∈ target →
        releasedCondition A leaf →
        releasedCondition A' leaf' →
        leaf ∈ realizedPairs →
        leaf' ∈ realizedPairs →
        bluePart A = bluePart A' →
          ∀ e, e ∈ terminal → isBlue e →
            (e ∈ blueTrace leaf.1 ↔ e ∈ blueTrace leaf'.1) := by
    intro A A' leaf leaf' hAtarget hA'target hrel hrel' hleaf hleaf'
      hbluepart e heterm heblue
    have hinfo : leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 :=
      (Finset.mem_filter.mp hleaf).2
    have hinfo' : leaf'.2 ∈ transcriptLabels ∧ cellRealized leaf'.1 leaf'.2 :=
      (Finset.mem_filter.mp hleaf').2
    rcases hred leaf.1 leaf.2 hinfo.1 hinfo.2 with
      ⟨hRcard, hRterm, hRred, hZred, hPterm, hAterm, hPAdisj,
        hBRsub, hbluegeom, hZsub⟩
    rcases hred leaf'.1 leaf'.2 hinfo'.1 hinfo'.2 with
      ⟨hRcard', hRterm', hRred', hZred', hPterm', hAterm', hPAdisj',
        hBRsub', hbluegeom', hZsub'⟩
    have he_not_Z : e ∉ leaf.2.2.2 := by
      intro heZ
      exact hblue_of_not_red e heblue (hZred e heZ)
    have he_not_Z' : e ∉ leaf'.2.2.2 := by
      intro heZ
      exact hblue_of_not_red e heblue (hZred' e heZ)
    have he_blueTerm : e ∈ blueTerminal :=
      Finset.mem_filter.mpr ⟨heterm, heblue⟩
    have hA_iff_bluePart : e ∈ A ↔ e ∈ bluePart A := by
      constructor
      · intro heA
        exact Finset.mem_inter.mpr ⟨heA, he_blueTerm⟩
      · intro heA
        exact (Finset.mem_inter.mp heA).1
    have hA'_iff_bluePart : e ∈ A' ↔ e ∈ bluePart A' := by
      constructor
      · intro heA
        exact Finset.mem_inter.mpr ⟨heA, he_blueTerm⟩
      · intro heA
        exact (Finset.mem_inter.mp heA).1
    have hA_iff_A' : e ∈ A ↔ e ∈ A' := by
      calc
        e ∈ A ↔ e ∈ bluePart A := hA_iff_bluePart
        _ ↔ e ∈ bluePart A' := by rw [hbluepart]
        _ ↔ e ∈ A' := hA'_iff_bluePart.symm
    have htraceA := hrel.2.2 e heterm he_not_Z heblue
    have htraceA' := hrel'.2.2 e heterm he_not_Z' heblue
    exact htraceA.trans (hA_iff_A'.trans htraceA'.symm)
  have hfiber_bound :
      ∀ S ∈ traces,
        (target.filter (fun A => bluePart A = S)).sum weight
          ≤ p ^ uR * blueWeight S := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨A0, hA0target, hS_eq⟩
    rcases Finset.mem_filter.mp hA0target with ⟨hA0pow, leaf0, hleaf0, hrel0⟩
    have hinfo0 : leaf0.2 ∈ transcriptLabels ∧ cellRealized leaf0.1 leaf0.2 :=
      (Finset.mem_filter.mp hleaf0).2
    rcases hred leaf0.1 leaf0.2 hinfo0.1 hinfo0.2 with
      ⟨hRcard0, hRterm0, hRred0, hZred0, hPterm0, hAterm0, hPAdisj0,
        hBRsub0, hbluegeom0, hZsub0⟩
    let R : Finset Coord := redSupport leaf0.1 J
    have hSblue : S ⊆ blueTerminal := by
      intro e heS
      have he_bluePart : e ∈ bluePart A0 := by
        simpa [hS_eq] using heS
      exact (Finset.mem_inter.mp he_bluePart).2
    have hRblue : Disjoint R blueTerminal := by
      rw [Finset.disjoint_left]
      intro e heR heBlueT
      have heBlue : isBlue e := (Finset.mem_filter.mp heBlueT).2
      exact hblue_of_not_red e heBlue (hRred0 e heR)
    let redFiber : Finset (Finset Coord) :=
      terminal.powerset.filter (fun A => A ∩ blueTerminal = S ∧ R ⊆ A)
    have hfiber_subset :
        target.filter (fun A => bluePart A = S) ⊆ redFiber := by
      intro A hAfiber
      rcases Finset.mem_filter.mp hAfiber with ⟨hAtarget, hbluepartA⟩
      rcases Finset.mem_filter.mp hAtarget with ⟨hApow, leaf, hleaf, hrel⟩
      have hsame_blue : bluePart A = bluePart A0 := by
        calc
          bluePart A = S := hbluepartA
          _ = bluePart A0 := hS_eq.symm
      have htrace_eq :
          ∀ e, e ∈ terminal → isBlue e →
            (e ∈ blueTrace leaf.1 ↔ e ∈ blueTrace leaf0.1) :=
        htrace_agree_of_same_bluePart hAtarget hA0target hrel hrel0
          hleaf hleaf0 hsame_blue
      have hβ : leaf.1 = leaf0.1 := hbranch leaf.1 leaf0.1 htrace_eq
      have hinfo : leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 :=
        (Finset.mem_filter.mp hleaf).2
      rcases hred leaf.1 leaf.2 hinfo.1 hinfo.2 with
        ⟨hRcard, hRterm, hRred, hZred, hPterm, hAterm, hPAdisj,
          hBRsub, hbluegeom, hZsub⟩
      have hRsubA : R ⊆ A := by
        intro e heR
        have heRleaf : e ∈ redSupport leaf.1 J := by
          simpa [R, hβ] using heR
        exact hrel.1 (hBRsub (Finset.mem_union.mpr (Or.inr heRleaf)))
      exact Finset.mem_filter.mpr
        ⟨hApow, by simpa [bluePart] using hbluepartA, hRsubA⟩
    have hredFiber_sum :
        redFiber.sum weight =
          p ^ uR * blueWeight S := by
      simpa [redFiber, R, weight, blueWeight] using
        FinsetBlueFiberRedSupportMass terminal blueTerminal R S p uR
          hblueTerm hSblue hRterm0 hRcard0 hRblue
    have hsubset_sum :
        (target.filter (fun A => bluePart A = S)).sum weight
          ≤ redFiber.sum weight := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hfiber_subset ?_
      intro A hA hAnot
      have hApow : A ∈ terminal.powerset := (Finset.mem_filter.mp hA).1
      exact hweight_nonneg A hApow
    exact le_trans hsubset_sum (le_of_eq hredFiber_sum)
  have htraces_subset :
      traces ⊆ blueTerminal.powerset.filter (fun S => B ⊆ S) := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨A, hAtarget, hS_eq⟩
    rcases Finset.mem_filter.mp hAtarget with ⟨hApow, leaf, hleaf, hrel⟩
    have hSblue : S ⊆ blueTerminal := by
      intro e heS
      have he_bluePart : e ∈ bluePart A := by
        simpa [hS_eq] using heS
      exact (Finset.mem_inter.mp he_bluePart).2
    have hinfo : leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 :=
      (Finset.mem_filter.mp hleaf).2
    rcases hred leaf.1 leaf.2 hinfo.1 hinfo.2 with
      ⟨hRcard, hRterm, hRred, hZred, hPterm, hAterm, hPAdisj,
        hBRsub, hbluegeom, hZsub⟩
    have hBsubS : B ⊆ S := by
      intro e heB
      have heA : e ∈ A :=
        hrel.1 (hBRsub (Finset.mem_union.mpr (Or.inl heB)))
      have he_bluePart : e ∈ bluePart A :=
        Finset.mem_inter.mpr ⟨heA, hBblueTerm heB⟩
      simpa [hS_eq] using he_bluePart
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSblue, hBsubS⟩
  have hblue_sum :
      traces.sum blueWeight ≤ p ^ uB := by
    simpa [blueWeight] using
      FinsetBlueSupportMassBound blueTerminal B traces p uB
        hp hp_one hBblueTerm hBcard htraces_subset
  have hp_uR_nonneg : 0 ≤ p ^ uR := pow_nonneg hp _
  have hfiber_total :
      target.sum weight ≤ traces.sum (fun S => p ^ uR * blueWeight S) := by
    rw [htarget_sum]
    refine Finset.sum_le_sum ?_
    intro S hS
    exact hfiber_bound S hS
  calc
    target.sum weight ≤ traces.sum (fun S => p ^ uR * blueWeight S) :=
      hfiber_total
    _ = p ^ uR * traces.sum blueWeight := by
      rw [Finset.mul_sum]
    _ ≤ p ^ uR * p ^ uB :=
      mul_le_mul_of_nonneg_left hblue_sum hp_uR_nonneg
