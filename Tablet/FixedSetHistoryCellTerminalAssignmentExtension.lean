import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellTerminalAssignmentExtension]

theorem FixedSetHistoryCellTerminalAssignmentExtension :
    ∀ {n m : ℕ} {p : ℝ}
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      (∀ e,
        e ∈ recorded →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ e,
        e ∈ terminal →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ e, e ∈ terminal → e ∉ recorded) →
      ∀ (base : TwoBiteSample n m p)
        (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          ∃ ωA : TwoBiteSample n m p,
            (∀ x : Fin n, ωA.2.2 x = base.2.2 x) ∧
            (∀ c,
              c ∈ recorded →
                (TwoBiteEdgeCoordinateValue ωA c ↔
                  TwoBiteEdgeCoordinateValue base c)) ∧
            (∀ e,
              e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ωA e ↔ e ∈ A)) := by
-- BODY
  classical
  intro n m p recorded terminal hrecorded_universe hterminal_universe
    hterminal_not_recorded base A _hA_terminal
  let canonicalPair (u v : Fin m) : Fin m × Fin m :=
    if u.val < v.val then (u, v) else (v, u)
  have hcanonical_swap :
      ∀ {u v : Fin m}, u ≠ v → canonicalPair v u = canonicalPair u v := by
    intro u v huv_ne
    unfold canonicalPair
    by_cases huv : u.val < v.val
    · have hvu_not : ¬ v.val < u.val := Nat.not_lt.mpr (Nat.le_of_lt huv)
      simp [huv, hvu_not]
    · have hvu : v.val < u.val := by
        have hval_ne : u.val ≠ v.val := by
          intro hval
          exact huv_ne (Fin.ext hval)
        exact lt_of_le_of_ne (Nat.not_lt.mp huv) hval_ne.symm
      simp [huv, hvu]
  let redGraph : SimpleGraph (Fin m) :=
    { Adj := fun u v =>
        u ≠ v ∧
          if Sum.inl (canonicalPair u v) ∈ terminal then
            Sum.inl (canonicalPair u v) ∈ A
          else
            base.1.Adj u v
      symm := by
        intro u v huv
        have hswap : canonicalPair v u = canonicalPair u v :=
          hcanonical_swap huv.1
        constructor
        · exact huv.1.symm
        · by_cases hterm : Sum.inl (canonicalPair u v) ∈ terminal
          · have hA : Sum.inl (canonicalPair u v) ∈ A := by
              simpa [hterm] using huv.2
            have hterm' : Sum.inl (canonicalPair v u) ∈ terminal := by
              simpa [hswap] using hterm
            simpa [hterm', hswap, hterm] using hA
          · have hbase : base.1.Adj u v := by
              simpa [hterm] using huv.2
            have hterm' : Sum.inl (canonicalPair v u) ∉ terminal := by
              simpa [hswap] using hterm
            simpa [hterm'] using base.1.symm hbase
      loopless := by
        exact ⟨fun u huu => huu.1 rfl⟩ }
  let blueGraph : SimpleGraph (Fin m) :=
    { Adj := fun u v =>
        u ≠ v ∧
          if Sum.inr (canonicalPair u v) ∈ terminal then
            Sum.inr (canonicalPair u v) ∈ A
          else
            base.2.1.Adj u v
      symm := by
        intro u v huv
        have hswap : canonicalPair v u = canonicalPair u v :=
          hcanonical_swap huv.1
        constructor
        · exact huv.1.symm
        · by_cases hterm : Sum.inr (canonicalPair u v) ∈ terminal
          · have hA : Sum.inr (canonicalPair u v) ∈ A := by
              simpa [hterm] using huv.2
            have hterm' : Sum.inr (canonicalPair v u) ∈ terminal := by
              simpa [hswap] using hterm
            simpa [hterm', hswap, hterm] using hA
          · have hbase : base.2.1.Adj u v := by
              simpa [hterm] using huv.2
            have hterm' : Sum.inr (canonicalPair v u) ∉ terminal := by
              simpa [hswap] using hterm
            simpa [hterm'] using base.2.1.symm hbase
      loopless := by
        exact ⟨fun u huu => huu.1 rfl⟩ }
  let ωA : TwoBiteSample n m p := (redGraph, blueGraph, base.2.2)
  refine ⟨ωA, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro c hc
    cases c with
    | inl q =>
        have hlt : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using
            hrecorded_universe (Sum.inl q) hc
        have hne : q.1 ≠ q.2 := by
          intro hq
          exact hlt.ne (by simpa using congrArg Fin.val hq)
        have hlt_fin : q.1 < q.2 := by
          simpa using hlt
        have hcanon : canonicalPair q.1 q.2 = q := by
          simp [canonicalPair, hlt_fin]
        have hnot_terminal : Sum.inl q ∉ terminal := by
          intro hterm
          exact hterminal_not_recorded (Sum.inl q) hterm hc
        change redGraph.Adj q.1 q.2 ↔ base.1.Adj q.1 q.2
        change
          (q.1 ≠ q.2 ∧
              (if Sum.inl (canonicalPair q.1 q.2) ∈ terminal then
                Sum.inl (canonicalPair q.1 q.2) ∈ A
              else
                base.1.Adj q.1 q.2)) ↔
            base.1.Adj q.1 q.2
        rw [hcanon]
        simp [hne, hnot_terminal]
    | inr q =>
        have hlt : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using
            hrecorded_universe (Sum.inr q) hc
        have hne : q.1 ≠ q.2 := by
          intro hq
          exact hlt.ne (by simpa using congrArg Fin.val hq)
        have hlt_fin : q.1 < q.2 := by
          simpa using hlt
        have hcanon : canonicalPair q.1 q.2 = q := by
          simp [canonicalPair, hlt_fin]
        have hnot_terminal : Sum.inr q ∉ terminal := by
          intro hterm
          exact hterminal_not_recorded (Sum.inr q) hterm hc
        change blueGraph.Adj q.1 q.2 ↔ base.2.1.Adj q.1 q.2
        change
          (q.1 ≠ q.2 ∧
              (if Sum.inr (canonicalPair q.1 q.2) ∈ terminal then
                Sum.inr (canonicalPair q.1 q.2) ∈ A
              else
                base.2.1.Adj q.1 q.2)) ↔
            base.2.1.Adj q.1 q.2
        rw [hcanon]
        simp [hne, hnot_terminal]
  · intro e he
    cases e with
    | inl q =>
        have hlt : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using
            hterminal_universe (Sum.inl q) he
        have hne : q.1 ≠ q.2 := by
          intro hq
          exact hlt.ne (by simpa using congrArg Fin.val hq)
        have hlt_fin : q.1 < q.2 := by
          simpa using hlt
        have hcanon : canonicalPair q.1 q.2 = q := by
          simp [canonicalPair, hlt_fin]
        change redGraph.Adj q.1 q.2 ↔ Sum.inl q ∈ A
        change
          (q.1 ≠ q.2 ∧
              (if Sum.inl (canonicalPair q.1 q.2) ∈ terminal then
                Sum.inl (canonicalPair q.1 q.2) ∈ A
              else
                base.1.Adj q.1 q.2)) ↔
            Sum.inl q ∈ A
        rw [hcanon]
        simp [hne, he]
    | inr q =>
        have hlt : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using
            hterminal_universe (Sum.inr q) he
        have hne : q.1 ≠ q.2 := by
          intro hq
          exact hlt.ne (by simpa using congrArg Fin.val hq)
        have hlt_fin : q.1 < q.2 := by
          simpa using hlt
        have hcanon : canonicalPair q.1 q.2 = q := by
          simp [canonicalPair, hlt_fin]
        change blueGraph.Adj q.1 q.2 ↔ Sum.inr q ∈ A
        change
          (q.1 ≠ q.2 ∧
              (if Sum.inr (canonicalPair q.1 q.2) ∈ terminal then
                Sum.inr (canonicalPair q.1 q.2) ∈ A
              else
                base.2.1.Adj q.1 q.2)) ↔
            Sum.inr q ∈ A
        rw [hcanon]
        simp [hne, he]
