import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Tablet.FixedSetCylinderProductMassFactor
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteEventProbabilityUnionBound

-- [TABLET NODE: MediumClosedPairsEmbeddingCellCoordinateUnionBridge]

open scoped BigOperators

theorem MediumClosedPairsEmbeddingCellCoordinateUnionBridge
    {n m t : ℕ} {p : ℝ}
    (π : Fin n ↪ (Fin m × Fin m))
    (BR BB PR PB : Finset (Fin m))
    (hp_pos : 0 < p) (hp_lt : p < 1) :
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
    TwoBiteEventProbability n m p
      (fun ω =>
        TwoBiteEmbedding ω = π ∧
          t ≤
            (@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
              (fun e => TwoBiteEdgeCoordinateValue ω e)
              (Classical.decPred _) C).card)
      ≤
        ((Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
            p ^ t) *
          TwoBiteEventProbability n m p
            (fun ω => TwoBiteEmbedding ω = π) := by
-- BODY
  classical
  intro normalize redRaw blueRaw C
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Cell : TwoBiteSample n m p → Prop := fun ω => TwoBiteEmbedding ω = π
  let PresentMany : TwoBiteSample n m p → Prop :=
    fun ω =>
      t ≤
        (@Finset.filter Coord
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C).card
  let ι := {A : Finset Coord // A ∈ C.powersetCard t}
  let Candidate : ι → TwoBiteSample n m p → Prop :=
    fun A ω =>
      Cell ω ∧ ∀ e, e ∈ (A : Finset Coord) → TwoBiteEdgeCoordinateValue ω e
  have hp0 : 0 ≤ p := le_of_lt hp_pos
  have hp1 : p ≤ 1 := le_of_lt hp_lt
  have hnormalize_oriented :
      ∀ e : Fin m × Fin m, e.1 ≠ e.2 →
        (normalize e).1.val < (normalize e).2.val := by
    intro e hne
    dsimp [normalize]
    by_cases hlt : e.1.val < e.2.val
    · simp [hlt]
    · simp [hlt]
      have hne_val : e.1.val ≠ e.2.val := by
        intro hval
        exact hne (Fin.ext hval)
      omega
  have hC_oriented :
      ∀ e : Coord, e ∈ C →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val := by
    intro e heC
    simp only [C, Finset.mem_union] at heC
    rcases heC with heRed | heBlue
    · rcases Finset.mem_image.mp heRed with ⟨q, hq, rfl⟩
      have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
      exact hnormalize_oriented q hne
    · rcases Finset.mem_image.mp heBlue with ⟨q, hq, rfl⟩
      have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
      exact hnormalize_oriented q hne
  have hredRaw_card : redRaw.card ≤ (BR.product PR).card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hblueRaw_card : blueRaw.card ≤ (BB.product PB).card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hredImage_card :
      (redRaw.image
        (fun e => (Sum.inl (normalize e) :
          Sum (Fin m × Fin m) (Fin m × Fin m)))).card ≤ redRaw.card :=
    Finset.card_image_le
  have hblueImage_card :
      (blueRaw.image
        (fun e => (Sum.inr (normalize e) :
          Sum (Fin m × Fin m) (Fin m × Fin m)))).card ≤ blueRaw.card :=
    Finset.card_image_le
  have hCcard :
      C.card ≤ BR.card * PR.card + BB.card * PB.card := by
    calc
      C.card
          ≤ (redRaw.image
                (fun e => (Sum.inl (normalize e) :
                  Sum (Fin m × Fin m) (Fin m × Fin m)))).card +
              (blueRaw.image
                (fun e => (Sum.inr (normalize e) :
                  Sum (Fin m × Fin m) (Fin m × Fin m)))).card := by
            simpa [C] using
              Finset.card_union_le
                (redRaw.image
                  (fun e => (Sum.inl (normalize e) :
                    Sum (Fin m × Fin m) (Fin m × Fin m))))
                (blueRaw.image
                  (fun e => (Sum.inr (normalize e) :
                    Sum (Fin m × Fin m) (Fin m × Fin m))))
      _ ≤ redRaw.card + blueRaw.card := Nat.add_le_add hredImage_card hblueImage_card
      _ ≤ (BR.product PR).card + (BB.product PB).card :=
            Nat.add_le_add hredRaw_card hblueRaw_card
      _ = BR.card * PR.card + BB.card * PB.card := by simp
  have hcell_nonneg :
      0 ≤ TwoBiteEventProbability n m p Cell :=
    TwoBiteEventProbabilityNonnegative hp0 hp1 Cell
  have hfixed :
      ∀ A : Finset Coord, A ∈ C.powersetCard t →
        TwoBiteEventProbability n m p
            (fun ω =>
              Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e)
          ≤ p ^ t * TwoBiteEventProbability n m p Cell := by
    intro A hA
    have hA_subset_C : A ⊆ C := (Finset.mem_powersetCard.mp hA).1
    have hA_card : A.card = t := (Finset.mem_powersetCard.mp hA).2
    have hA_oriented :
        ∀ e : Coord, e ∈ A →
          match e with
          | Sum.inl q => q.1.val < q.2.val
          | Sum.inr q => q.1.val < q.2.val := by
      intro e he
      exact hC_oriented e (hA_subset_C he)
    let ω0 : TwoBiteSample n m p := (⊥, ⊥, π)
    have hω0_cell : Cell ω0 := by
      rfl
    have hCylinder :
        ∀ ω : TwoBiteSample n m p,
          Cell ω ↔
            (∀ x : Fin n, ω.2.2 x = ω0.2.2 x) ∧
            (∀ e : Coord,
              e ∈ (∅ : Finset Coord) →
                (TwoBiteEdgeCoordinateValue ω e ↔
                  TwoBiteEdgeCoordinateValue ω0 e)) := by
      intro ω
      constructor
      · intro hω
        constructor
        · intro x
          simpa [Cell, TwoBiteEmbedding, ω0] using congrArg (fun f => f x) hω
        · intro e he
          simp at he
      · intro hω
        apply DFunLike.ext
        intro x
        simpa [Cell, TwoBiteEmbedding, ω0] using hω.1 x
    have hRecordedOriented :
        ∀ e : Coord, e ∈ (∅ : Finset Coord) →
          match e with
          | Sum.inl q => q.1.val < q.2.val
          | Sum.inr q => q.1.val < q.2.val := by
      intro e he
      simp at he
    have hProductUnrecorded :
        ∀ e : Coord, e ∈ A → e ∉ (∅ : Finset Coord) := by
      intro e _heA heEmpty
      simp at heEmpty
    have hA_self : A ⊆ A := by intro e he; exact he
    have hmass :=
      FixedSetCylinderProductMassFactor
        (hist := Cell)
        (recorded := (∅ : Finset Coord))
        (product := A)
        (ω0 := ω0)
        hp_pos hp_lt hω0_cell hCylinder hRecordedOriented
        hProductUnrecorded hA_oriented A hA_self
    have hEventEq :
        TwoBiteEventProbability n m p
            (fun ω =>
              Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e)
          =
        TwoBiteEventProbability n m p
            (fun ω =>
              (∀ e, e ∈ A →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
              Cell ω) := by
      have hEventIff :
          ∀ ω : TwoBiteSample n m p,
            (Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e) ↔
              (∀ e, e ∈ A →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
              Cell ω := by
        intro ω
        constructor
        · intro hω
          constructor
          · intro e he
            constructor
            · intro _hedge
              exact he
            · intro _he
              exact hω.2 e he
          · exact hω.1
        · intro hω
          constructor
          · exact hω.2
          · intro e he
            exact (hω.1 e he).2 he
      have hPred :
          (fun ω : TwoBiteSample n m p =>
              Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e)
            =
          (fun ω : TwoBiteSample n m p =>
              (∀ e, e ∈ A →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
              Cell ω) := by
        funext ω
        exact propext (hEventIff ω)
      exact congrArg (TwoBiteEventProbability n m p) hPred
    have heq :
        TwoBiteEventProbability n m p
            (fun ω =>
              Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e)
          =
            p ^ t * TwoBiteEventProbability n m p Cell := by
      calc
        TwoBiteEventProbability n m p
            (fun ω =>
              Cell ω ∧ ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e)
            =
          TwoBiteEventProbability n m p
            (fun ω =>
              (∀ e, e ∈ A →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
              Cell ω) := hEventEq
        _ =
            (p ^ A.card * ((1 : ℝ) - p) ^ (A.card - A.card)) *
              TwoBiteEventProbability n m p Cell := hmass.2
        _ = p ^ t * TwoBiteEventProbability n m p Cell := by
          simp [hA_card]
    exact le_of_eq heq
  have hcover :
      ∀ ω : TwoBiteSample n m p,
        Cell ω ∧ PresentMany ω →
          ∃ A : ι, Candidate A ω := by
    intro ω hω
    let present : Finset Coord :=
      @Finset.filter Coord
        (fun e => TwoBiteEdgeCoordinateValue ω e)
        (Classical.decPred _) C
    obtain ⟨A, hA_sub, hA_card⟩ :=
      Finset.exists_subset_card_eq (s := present) hω.2
    have hA_mem : A ∈ C.powersetCard t := by
      rw [Finset.mem_powersetCard]
      constructor
      · intro e heA
        exact (Finset.mem_filter.mp (hA_sub heA)).1
      · exact hA_card
    refine ⟨⟨A, hA_mem⟩, ?_⟩
    constructor
    · exact hω.1
    · intro e heA
      exact (Finset.mem_filter.mp (hA_sub heA)).2
  have hmono :
      TwoBiteEventProbability n m p
          (fun ω => Cell ω ∧ PresentMany ω)
        ≤ TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω) := by
    unfold TwoBiteEventProbability
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hcover ω hω
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hunion :
      TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω)
        ≤ ∑ A : ι, TwoBiteEventProbability n m p (Candidate A) :=
    TwoBiteEventProbabilityUnionBound hp0 hp1 Candidate
  have hsum_tail :
      (∑ A : ι, TwoBiteEventProbability n m p (Candidate A)) ≤
        ∑ _A : ι, p ^ t * TwoBiteEventProbability n m p Cell := by
    refine Finset.sum_le_sum ?_
    intro A _hA
    exact hfixed (A : Finset Coord) A.property
  have htail_sum :
      (∑ _A : ι, p ^ t * TwoBiteEventProbability n m p Cell) =
        ((C.powersetCard t).card : ℝ) *
          (p ^ t * TwoBiteEventProbability n m p Cell) := by
    simp [ι, nsmul_eq_mul]
  have hcard_choose : ((C.powersetCard t).card : ℝ) = (Nat.choose C.card t : ℝ) := by
    rw [Finset.card_powersetCard]
  have hchoose_le : (Nat.choose C.card t : ℝ) ≤
      (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) := by
    exact_mod_cast Nat.choose_le_choose t hCcard
  have htail_nonneg : 0 ≤ p ^ t * TwoBiteEventProbability n m p Cell := by
    exact mul_nonneg (pow_nonneg hp0 t) hcell_nonneg
  calc
    TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ PresentMany ω)
        ≤ TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω) := hmono
    _ ≤ ∑ A : ι, TwoBiteEventProbability n m p (Candidate A) := hunion
    _ ≤ ∑ _A : ι, p ^ t * TwoBiteEventProbability n m p Cell := hsum_tail
    _ =
        ((C.powersetCard t).card : ℝ) *
          (p ^ t * TwoBiteEventProbability n m p Cell) := htail_sum
    _ =
        (Nat.choose C.card t : ℝ) *
          (p ^ t * TwoBiteEventProbability n m p Cell) := by rw [hcard_choose]
    _ ≤
        (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
          (p ^ t * TwoBiteEventProbability n m p Cell) := by
        exact mul_le_mul_of_nonneg_right hchoose_le htail_nonneg
    _ =
        ((Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
            p ^ t) *
          TwoBiteEventProbability n m p Cell := by ring
