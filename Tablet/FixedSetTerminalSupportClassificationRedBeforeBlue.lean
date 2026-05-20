import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetTerminalSupportClassificationRedBeforeBlue]

theorem FixedSetTerminalSupportClassificationRedBeforeBlue :
    ∀ {m : ℕ}
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      (∀ e, e ∈ terminal ↔
        e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
      ∃ order : List (Sum (Fin m × Fin m) (Fin m × Fin m)),
        order.Nodup ∧
        order.toFinset = terminal ∧
        TwoBiteTerminalOrderRedBeforeBlue terminal order ∧
        (∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (e : Sum (Fin m × Fin m) (Fin m × Fin m))
          (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
          order = pre ++ e :: suffix →
            match e with
            | Sum.inl q =>
                ∀ r : Fin m,
                  r.val < q.1.val →
                  r.val < q.2.val →
                    Sum.inl (r, q.1) ∈ recorded ∪ pre.toFinset ∧
                      Sum.inl (r, q.2) ∈ recorded ∪ pre.toFinset
            | Sum.inr q =>
                ∀ b : Fin m,
                  b.val < q.1.val →
                  b.val < q.2.val →
                    Sum.inr (b, q.1) ∈ recorded ∪ pre.toFinset ∧
                      Sum.inr (b, q.2) ∈ recorded ∪ pre.toFinset) := by
-- BODY
  classical
  intro m recorded terminal hterminal
  let α := Sum (Fin m × Fin m) (Fin m × Fin m)
  let rank : α → ℕ := fun e =>
    match e with
    | Sum.inl q => q.1.val
    | Sum.inr q => m + q.1.val
  let cmp : α → α → Bool := fun e f => decide (rank e ≤ rank f)
  let order : List α := terminal.toList.mergeSort cmp
  have htrans :
      ∀ a b c : α, cmp a b = true → cmp b c = true → cmp a c = true := by
    intro a b c hab hbc
    have hab' : rank a ≤ rank b := by simpa [cmp] using hab
    have hbc' : rank b ≤ rank c := by simpa [cmp] using hbc
    simpa [cmp] using le_trans hab' hbc'
  have htotal : ∀ a b : α, (cmp a b || cmp b a) = true := by
    intro a b
    by_cases hab : rank a ≤ rank b
    · simp [cmp, hab]
    · have hba : rank b ≤ rank a := le_of_not_ge hab
      simp [cmp, hab, hba]
  have hsortedOrder :
      List.Pairwise (fun x y : α => cmp x y = true) order := by
    simpa [order] using List.pairwise_mergeSort htrans htotal terminal.toList
  have prefix_of_rank_lt :
      ∀ (pre : List α) (e : α) (suffix : List α),
        order = pre ++ e :: suffix →
          ∀ {c : α}, c ∈ terminal → rank c < rank e → c ∈ pre := by
    intro pre e suffix horder c hcTerm hlt
    have hcOrder : c ∈ order := by
      simpa [order, List.mem_mergeSort] using hcTerm
    have hcSplit : c ∈ pre ∨ c = e ∨ c ∈ suffix := by
      have : c ∈ pre ++ e :: suffix := by
        simpa [horder] using hcOrder
      simpa using this
    rcases hcSplit with hcpre | hce | hcsuf
    · exact hcpre
    · subst c
      exact (Nat.lt_irrefl (rank e) hlt).elim
    · have hsortedSplit :
          List.Pairwise (fun x y : α => cmp x y = true)
            (pre ++ e :: suffix) := by
        simpa [horder] using hsortedOrder
      have htail :
          List.Pairwise (fun x y : α => cmp x y = true)
            (e :: suffix) :=
        (List.pairwise_append.mp hsortedSplit).2.1
      have hcmp : cmp e c = true :=
        (List.pairwise_cons.mp htail).1 c hcsuf
      have hle : rank e ≤ rank c := by simpa [cmp] using hcmp
      exact (not_lt_of_ge hle hlt).elim
  refine ⟨order, ?_, ?_, ?_, ?_⟩
  · have hnodup : terminal.toList.Nodup := Finset.nodup_toList terminal
    exact hnodup.mergeSort
  · ext e
    simp [order, List.mem_mergeSort]
  · intro pre e suffix horder hblue c hcTerm hred
    cases e with
    | inl q =>
        simp [TwoBiteCoordinateIsBlue] at hblue
    | inr q =>
        cases c with
        | inl s =>
            have hlt : rank (Sum.inl s) < rank (Sum.inr q) := by
              have hslt : s.1.val < m := s.1.isLt
              have hle : m ≤ m + q.1.val := Nat.le_add_right m q.1.val
              exact Nat.lt_of_lt_of_le hslt hle
            have hcPre := prefix_of_rank_lt pre (Sum.inr q) suffix horder
              (c := Sum.inl s) hcTerm hlt
            simpa using hcPre
        | inr s =>
            simp [TwoBiteCoordinateIsRed] at hred
  · intro pre e suffix horder
    have heOrder : e ∈ order := by
      rw [horder]
      simp
    have heTerm : e ∈ terminal := by
      simpa [order, List.mem_mergeSort] using heOrder
    have heUniverse : e ∈ TwoBiteTerminalCoordinateUniverse m := by
      exact ((hterminal e).mp heTerm).1
    have support_mem
        (c : α)
        (hcUniverse : c ∈ TwoBiteTerminalCoordinateUniverse m)
        (hlt : rank c < rank e) :
        c ∈ recorded ∪ pre.toFinset := by
        by_cases hcRecorded : c ∈ recorded
        · exact Finset.mem_union.mpr (Or.inl hcRecorded)
        · have hcTerm : c ∈ terminal := by
            exact (hterminal c).mpr ⟨hcUniverse, hcRecorded⟩
          have hcPre : c ∈ pre := prefix_of_rank_lt pre e suffix horder hcTerm hlt
          exact Finset.mem_union.mpr (Or.inr (by simpa using hcPre))
    cases e with
    | inl q =>
        have hqInc : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using heUniverse
        intro r hr1 hr2
        constructor
        · have hcUniverse :
              Sum.inl (r, q.1) ∈ TwoBiteTerminalCoordinateUniverse m := by
            simp [TwoBiteTerminalCoordinateUniverse]
            exact hr1
          have hlt : rank (Sum.inl (r, q.1)) < rank (Sum.inl q) := by
            simpa [rank] using hr1
          exact support_mem (Sum.inl (r, q.1)) hcUniverse hlt
        · have hcUniverse :
              Sum.inl (r, q.2) ∈ TwoBiteTerminalCoordinateUniverse m := by
            simp [TwoBiteTerminalCoordinateUniverse]
            exact hr2
          have hlt : rank (Sum.inl (r, q.2)) < rank (Sum.inl q) := by
            simpa [rank] using hr1
          exact support_mem (Sum.inl (r, q.2)) hcUniverse hlt
    | inr q =>
        have hqInc : q.1.val < q.2.val := by
          simpa [TwoBiteTerminalCoordinateUniverse] using heUniverse
        intro b hb1 hb2
        constructor
        · have hcUniverse :
              Sum.inr (b, q.1) ∈ TwoBiteTerminalCoordinateUniverse m := by
            simp [TwoBiteTerminalCoordinateUniverse]
            exact hb1
          have hlt : rank (Sum.inr (b, q.1)) < rank (Sum.inr q) := by
            simpa [rank] using Nat.add_lt_add_left hb1 m
          exact support_mem (Sum.inr (b, q.1)) hcUniverse hlt
        · have hcUniverse :
              Sum.inr (b, q.2) ∈ TwoBiteTerminalCoordinateUniverse m := by
            simp [TwoBiteTerminalCoordinateUniverse]
            exact hb2
          have hlt : rank (Sum.inr (b, q.2)) < rank (Sum.inr q) := by
            simpa [rank] using Nat.add_lt_add_left hb1 m
          exact support_mem (Sum.inr (b, q.2)) hcUniverse hlt
