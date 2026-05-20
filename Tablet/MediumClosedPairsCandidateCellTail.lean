import Mathlib.Tactic
import Tablet.MediumClosedPairsEmbeddingCellCoordinateUnionBridge
import Tablet.MediumClosedPairsNaturalFixedPairTail
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: MediumClosedPairsCandidateCellTail]

theorem MediumClosedPairsCandidateCellTail
    {n m : ℕ} {ε : ℝ}
    (π : Fin n ↪ (Fin m × Fin m))
    (BR BB PR PB : Finset (Fin m))
    (Candidate :
      TwoBiteSample n m (TwoBiteEdgeProbability (1 / 2 : ℝ) n) → Prop)
    [DecidablePred Candidate]
    (hp_pos : 0 < TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (hp_lt : TwoBiteEdgeProbability (1 / 2 : ℝ) n < 1) :
    let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let A : ℝ := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
      (6 * (Real.log (n : ℝ)) ^ 2)
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
    0 < A →
    PR.card ≤ K →
    PB.card ≤ K →
    p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1) →
    Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) ≤ A / 4 →
    (∀ ω : TwoBiteSample n m p,
      TwoBiteEmbedding ω = π →
      Candidate ω →
      t ≤
        (@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C).card) →
    TwoBiteEventProbability n m p
      (fun ω => TwoBiteEmbedding ω = π ∧ Candidate ω)
      ≤
        Real.exp (-(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))) *
          TwoBiteEventProbability n m p
            (fun ω => TwoBiteEmbedding ω = π) := by
-- BODY
  classical
  intro K p A t normalize redRaw blueRaw C hApos hPR hPB hmean htail himp
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Cell : TwoBiteSample n m p → Prop := fun ω => TwoBiteEmbedding ω = π
  let PresentMany : TwoBiteSample n m p → Prop :=
    fun ω =>
      t ≤
        (@Finset.filter Coord
          (fun e => TwoBiteEdgeCoordinateValue ω e)
          (Classical.decPred _) C).card
  have hp0 : 0 ≤ p := le_of_lt hp_pos
  have hp1 : p ≤ 1 := le_of_lt hp_lt
  have hmono :
      TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ Candidate ω)
        ≤
      TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ PresentMany ω) := by
    unfold TwoBiteEventProbability
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨hω.1, himp ω hω.1 hω.2⟩
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hbridge :
      TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ PresentMany ω)
        ≤
        ((Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
            p ^ t) *
          TwoBiteEventProbability n m p Cell := by
    simpa [Cell, PresentMany, Coord, C, redRaw, blueRaw, normalize] using
      (MediumClosedPairsEmbeddingCellCoordinateUnionBridge
        (n := n) (m := m) (t := t) (p := p)
        π BR BB PR PB hp_pos hp_lt)
  have hcoef :
      (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
          p ^ t
        ≤ Real.exp (-(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))) := by
    have hself :
        (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
            p ^ t
          ≤
        (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
            p ^ t := le_rfl
    simpa [K, p, A, t] using
      (MediumClosedPairsNaturalFixedPairTail
        (α := Fin m) (β := Fin m) ε n BR BB PR PB
        ((Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
          p ^ t)
        hApos hp0 hPR hPB hmean htail hself)
  have hcell_nonneg :
      0 ≤ TwoBiteEventProbability n m p Cell :=
    TwoBiteEventProbabilityNonnegative hp0 hp1 Cell
  have hbridge_tail :
      TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ PresentMany ω)
        ≤
        Real.exp (-(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))) *
          TwoBiteEventProbability n m p Cell :=
    le_trans hbridge (mul_le_mul_of_nonneg_right hcoef hcell_nonneg)
  have hresult :
      TwoBiteEventProbability n m p
        (fun ω => Cell ω ∧ Candidate ω)
        ≤
        Real.exp (-(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))) *
          TwoBiteEventProbability n m p Cell :=
    le_trans hmono hbridge_tail
  simpa [Cell] using hresult
