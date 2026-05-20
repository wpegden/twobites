import Tablet.ClosedPairsBound
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellGlobalBlueExceptionalWitness]

theorem FixedSetHistoryCellGlobalBlueExceptionalWitness :
    ∀ {n m k : ℕ} {p ε ε1 ε2 : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      0 ≤ ε1 →
      (∀ branch : TwoBiteSample n m p,
        hist branch →
          ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ER ⊆ terminal ∧
            EB ⊆ terminal ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ => True
                  | Sum.inr _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ ER)) ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)
                  | Sum.inr _ => True) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ EB))) →
      ∃ NBexc : ℕ,
        (NBexc : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∀ branch : TwoBiteSample n m p,
          hist branch →
            ∃ EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              EB ⊆ terminal ∧
              (EB.card : ℝ) ≤ (NBexc : ℝ) ∧
              ∀ ω : TwoBiteSample n m p,
                hist ω →
                (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
                (∀ e,
                  e ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue branch e)) →
                (∀ e,
                  e ∈ terminal →
                    match e with
                    | Sum.inl _ =>
                        (TwoBiteEdgeCoordinateValue ω e ↔
                          TwoBiteEdgeCoordinateValue branch e)
                    | Sum.inr _ => True) →
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                  (∀ e,
                    e ∈ TwoBiteStagedOpenPairs ω ε I →
                    TwoBiteEdgeCoordinateValue ω e →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet
                      (↑I : Set (Fin n)) →
                      e ∈ EB) := by
-- BODY
  classical
  intro n m k p ε ε1 ε2 I hist recorded terminal hε1 hbranch
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Branch := {branch : TwoBiteSample n m p // hist branch}
  let Relevant (branch : TwoBiteSample n m p) : Prop :=
    ∃ ω : TwoBiteSample n m p,
      hist ω ∧
        (∀ x : Fin n, ω.2.2 x = branch.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue branch e)) ∧
            (∀ e,
              e ∈ terminal →
                match e with
                | Sum.inl _ =>
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue branch e)
                | Sum.inr _ => True) ∧
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω
  let rawEB : Branch → Finset Coord := fun branch =>
    Classical.choose
      (Classical.choose_spec (hbranch branch.1 branch.2))
  let chosenEB : Branch → Finset Coord := fun branch =>
    if Relevant branch.1 then rawEB branch else ∅
  have hbound_nonneg : 0 ≤ 3 * ε1 * (k : ℝ) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hε1) (sq_nonneg (k : ℝ))
  have hchosen_subset :
      ∀ branch : Branch, chosenEB branch ⊆ terminal := by
    intro branch
    by_cases hrel : Relevant branch.1
    · have hpack :=
        Classical.choose_spec
          (Classical.choose_spec (hbranch branch.1 branch.2))
      have hchosen_eq : chosenEB branch = rawEB branch := by
        dsimp [chosenEB]
        exact if_pos hrel
      rw [hchosen_eq]
      change rawEB branch ⊆ terminal
      exact hpack.2.1
    · have hchosen_eq : chosenEB branch = ∅ := by
        dsimp [chosenEB]
        exact if_neg hrel
      rw [hchosen_eq]
      exact Finset.empty_subset terminal
  have hchosen_bound :
      ∀ branch : Branch,
        ((chosenEB branch).card : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 := by
    intro branch
    by_cases hrel : Relevant branch.1
    · have hrel_pos := hrel
      rcases hrel with
        ⟨ω, hωhist, hemb, hrecorded, hterminal, hregular⟩
      have hpack :=
        Classical.choose_spec
          (Classical.choose_spec (hbranch branch.1 branch.2))
      have hblue :=
        hpack.2.2.2 ω hωhist hemb hrecorded hterminal hregular
      have hchosen_eq : chosenEB branch = rawEB branch := by
        dsimp [chosenEB]
        exact if_pos hrel_pos
      rw [hchosen_eq]
      change ClosedPairsBound (((rawEB branch).card : ℝ)) (3 * ε1) (k : ℝ)
      exact hblue.1
    · have hchosen_eq : chosenEB branch = ∅ := by
        dsimp [chosenEB]
        exact if_neg hrel
      rw [hchosen_eq]
      simpa only [Finset.card_empty, Nat.cast_zero] using hbound_nonneg
  have hchosen_cover :
      ∀ branch : Branch,
        ∀ ω : TwoBiteSample n m p,
          hist ω →
          (∀ x : Fin n, ω.2.2 x = branch.1.2.2 x) →
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue branch.1 e)) →
          (∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch.1 e)
              | Sum.inr _ => True) →
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
            (∀ e,
              e ∈ TwoBiteStagedOpenPairs ω ε I →
              TwoBiteEdgeCoordinateValue ω e →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
              (TwoBiteFinalGraph ω).2.2.IsIndepSet
                (↑I : Set (Fin n)) →
              e ∈ chosenEB branch) := by
    intro branch ω hωhist hemb hrecorded hterminal hregular e hopen hpresent hblue_color hind
    by_cases hrel : Relevant branch.1
    · have hpack :=
        Classical.choose_spec
          (Classical.choose_spec (hbranch branch.1 branch.2))
      have hblue :=
        hpack.2.2.2 ω hωhist hemb hrecorded hterminal hregular
      have hmem := hblue.2 e hopen hpresent hblue_color hind
      have hchosen_eq : chosenEB branch = rawEB branch := by
        dsimp [chosenEB]
        exact if_pos hrel
      rw [hchosen_eq]
      change e ∈ rawEB branch
      exact hmem
    · exact False.elim
        (hrel ⟨ω, hωhist, hemb, hrecorded, hterminal, hregular⟩)
  let NBexc : ℕ := (Finset.univ.sup fun branch : Branch => (chosenEB branch).card)
  refine ⟨NBexc, ?_, ?_⟩
  · dsimp [NBexc]
    change
      (fun t : ℕ => (t : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2)
        ((Finset.univ : Finset Branch).sup fun branch => (chosenEB branch).card)
    refine Finset.sup_induction
      (s := (Finset.univ : Finset Branch))
      (f := fun branch : Branch => (chosenEB branch).card)
      (p := fun t : ℕ => (t : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2)
      ?hbot ?hsup ?hmem
    · simpa using hbound_nonneg
    · intro a ha b hb
      change ((max a b : ℕ) : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2
      simpa only [Nat.cast_max] using max_le ha hb
    · intro branch _hmem
      exact hchosen_bound branch
  · intro branch hhist
    let branch' : Branch := ⟨branch, hhist⟩
    refine ⟨chosenEB branch', hchosen_subset branch', ?_, ?_⟩
    · have hcard_le : (chosenEB branch').card ≤ NBexc := by
        dsimp [NBexc]
        exact Finset.le_sup
          (s := (Finset.univ : Finset Branch))
          (f := fun branch : Branch => (chosenEB branch).card)
          (show branch' ∈ (Finset.univ : Finset Branch) by simp)
      exact_mod_cast hcard_le
    · exact hchosen_cover branch'
