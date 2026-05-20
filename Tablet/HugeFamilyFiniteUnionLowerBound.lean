import Tablet.RealChooseTwo

-- [TABLET NODE: HugeFamilyFiniteUnionLowerBound]

theorem HugeFamilyFiniteUnionLowerBound :
    ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      (B : Finset α) (A : α → Finset β) (C : ℝ),
      (∀ x, x ∈ B → ∀ y, y ∈ B → x ≠ y →
        (((A x ∩ A y).card : ℝ) ≤ C)) →
      (B.sum (fun x => ((A x).card : ℝ)) -
          RealChooseTwo (B.card : ℝ) * C
        ≤ ((B.biUnion A).card : ℝ)) := by
-- BODY
  classical
  intro α β _ _ B A C
  refine Finset.induction_on B ?base ?step
  · intro _hoverlap
    simp [RealChooseTwo]
  · intro a s ha ih hoverlap
    have hoverlap_s :
        ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
          (((A x ∩ A y).card : ℝ) ≤ C) := by
      intro x hx y hy hxy
      exact hoverlap x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have ih' :
        s.sum (fun x => ((A x).card : ℝ)) -
            RealChooseTwo (s.card : ℝ) * C
          ≤ ((s.biUnion A).card : ℝ) :=
      ih hoverlap_s
    let U : Finset β := s.biUnion A
    have hbi_insert : (insert a s).biUnion A = A a ∪ U := by
      ext v
      simp [U]
    have hcard_union_real :
        (((A a ∪ U).card : ℝ) + ((A a ∩ U).card : ℝ) =
          ((A a).card : ℝ) + (U.card : ℝ)) := by
      exact_mod_cast (Finset.card_union_add_card_inter (A a) U)
    have hcard_union_eq :
        (((A a ∪ U).card : ℝ) =
          ((A a).card : ℝ) + (U.card : ℝ) -
            ((A a ∩ U).card : ℝ)) := by
      linarith only [hcard_union_real]
    have hinter_subset :
        A a ∩ U ⊆ s.biUnion (fun y => A a ∩ A y) := by
      intro v hv
      rw [Finset.mem_inter] at hv
      rcases hv with ⟨hva, hvU⟩
      have hvU' : v ∈ s.biUnion A := by
        simpa [U] using hvU
      rw [Finset.mem_biUnion] at hvU'
      rcases hvU' with ⟨y, hy, hvy⟩
      rw [Finset.mem_biUnion]
      exact ⟨y, hy, by simp [hva, hvy]⟩
    have hinter_card_le :
        (((A a ∩ U).card : ℝ) ≤
          ((s.biUnion (fun y => A a ∩ A y)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hinter_subset
    have hbi_card_le :
        (((s.biUnion (fun y => A a ∩ A y)).card : ℝ) ≤
          s.sum (fun y => ((A a ∩ A y).card : ℝ))) := by
      exact_mod_cast (Finset.card_biUnion_le
        (s := s) (t := fun y => A a ∩ A y))
    have hinter_sum_le :
        s.sum (fun y => ((A a ∩ A y).card : ℝ)) ≤ s.sum (fun _ => C) := by
      refine Finset.sum_le_sum ?_
      intro y hy
      have hay : a ≠ y := by
        intro hya
        exact ha (by simpa [hya] using hy)
      exact hoverlap a (Finset.mem_insert_self a s) y (Finset.mem_insert_of_mem hy) hay
    have hsum_const : s.sum (fun _ : α => C) = (s.card : ℝ) * C := by
      simp [nsmul_eq_mul]
    have hinter_le : (((A a ∩ U).card : ℝ) ≤ (s.card : ℝ) * C) := by
      calc
        ((A a ∩ U).card : ℝ)
            ≤ ((s.biUnion (fun y => A a ∩ A y)).card : ℝ) := hinter_card_le
        _ ≤ s.sum (fun y => ((A a ∩ A y).card : ℝ)) := hbi_card_le
        _ ≤ s.sum (fun _ : α => C) := hinter_sum_le
        _ = (s.card : ℝ) * C := hsum_const
    have hchoose_insert :
        RealChooseTwo ((insert a s).card : ℝ) =
          RealChooseTwo (s.card : ℝ) + (s.card : ℝ) := by
      simp [ha, RealChooseTwo]
      ring
    have hsum_insert :
        (insert a s).sum (fun x => ((A x).card : ℝ)) =
          ((A a).card : ℝ) + s.sum (fun x => ((A x).card : ℝ)) := by
      simp [ha]
    rw [hbi_insert]
    rw [hsum_insert, hchoose_insert]
    nlinarith [ih', hcard_union_eq, hinter_le]
