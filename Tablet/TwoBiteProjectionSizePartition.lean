import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteEventProbability

-- [TABLET NODE: TwoBiteProjectionSizePartition]

theorem TwoBiteProjectionSizePartition :
    ∀ {n m k : ℕ} {p : ℝ}
      (I : Finset (Fin n)) (event : TwoBiteSample n m p → Prop),
      I.card = k →
      TwoBiteEventProbability n m p event =
        (Finset.range (k + 1)).sum (fun ℓR =>
          (Finset.range (k + 1)).sum (fun ℓB =>
            TwoBiteEventProbability n m p
              (fun ω =>
                event ω ∧
                  TwoBiteProjectionSizeEvent
                    (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I))) := by
-- BODY
  intro n m k p I event hI
  classical
  let idx : Finset (ℕ × ℕ) :=
    (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))
  let cellSet : ℕ × ℕ → Finset (TwoBiteSample n m p) :=
    fun ij =>
      Finset.univ.filter (fun ω : TwoBiteSample n m p =>
        event ω ∧
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ij.1) (ℓB := ij.2) ω I)
  have hcover :
      (Finset.univ.filter event) = idx.biUnion cellSet := by
    ext ω
    constructor
    · intro hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      let ℓR := (I.image (TwoBiteRedProjection ω)).card
      let ℓB := (I.image (TwoBiteBlueProjection ω)).card
      have hℓR_le : ℓR ≤ k := by
        dsimp [ℓR]
        exact le_trans Finset.card_image_le (le_of_eq hI)
      have hℓB_le : ℓB ≤ k := by
        dsimp [ℓB]
        exact le_trans Finset.card_image_le (le_of_eq hI)
      have hcell :
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I := by
        simp [TwoBiteProjectionSizeEvent, ℓR, ℓB, hI]
      rw [Finset.mem_biUnion]
      refine ⟨(ℓR, ℓB), ?_, ?_⟩
      · simpa [idx, Finset.mem_product] using ⟨hℓR_le, hℓB_le⟩
      · simp [cellSet, hω, hcell]
    · intro hω
      rw [Finset.mem_biUnion] at hω
      rcases hω with ⟨ij, hij, hωij⟩
      have hωij' :
          event ω ∧
            TwoBiteProjectionSizeEvent
              (k := k) (ℓR := ij.1) (ℓB := ij.2) ω I := by
        simpa [cellSet] using hωij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hωij'.1
  have hdisj : (↑idx : Set (ℕ × ℕ)).PairwiseDisjoint cellSet := by
    rw [Finset.pairwiseDisjoint_iff]
    intro a ha b hb hnonempty
    rcases hnonempty with ⟨ω, hω⟩
    simp only [Finset.mem_inter] at hω
    have haCell :
        event ω ∧
          TwoBiteProjectionSizeEvent
            (k := k) (ℓR := a.1) (ℓB := a.2) ω I := by
      simpa [cellSet] using hω.1
    have hbCell :
        event ω ∧
          TwoBiteProjectionSizeEvent
            (k := k) (ℓR := b.1) (ℓB := b.2) ω I := by
      simpa [cellSet] using hω.2
    rcases haCell.2 with ⟨_, hRa, hBa⟩
    rcases hbCell.2 with ⟨_, hRb, hBb⟩
    ext
    · exact hRa.symm.trans hRb
    · exact hBa.symm.trans hBb
  unfold TwoBiteEventProbability
  rw [hcover]
  rw [Finset.sum_biUnion hdisj]
  dsimp [idx, cellSet]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro ℓR hℓR
  refine Finset.sum_congr rfl ?_
  intro ℓB hℓB
  refine Finset.sum_congr ?_ ?_
  · ext ω
    simp [TwoBiteProjectionSizeEvent]
  · intro ω hω
    rfl
