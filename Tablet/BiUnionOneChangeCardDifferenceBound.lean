import Tablet.CommonUnionCardDifferenceBound

-- [TABLET NODE: BiUnionOneChangeCardDifferenceBound]

open scoped Classical

lemma BiUnionOneChangeCardDifferenceBound {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (A B : ι → Finset α) (k : ι)
    (h : ∀ x ∈ s.erase k, A x = B x) :
    |(((s.biUnion A).card : ℝ) - ((s.biUnion B).card : ℝ))| ≤
      max (((A k).card : ℝ)) (((B k).card : ℝ)) := by
-- BODY
  classical
  have h_common :
      (s.erase k).biUnion A = (s.erase k).biUnion B := by
    apply Finset.ext
    intro z
    rw [Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · intro hz
      rcases hz with ⟨x, hx, hzA⟩
      exact ⟨x, hx, by simpa [h x hx] using hzA⟩
    · intro hz
      rcases hz with ⟨x, hx, hzB⟩
      exact ⟨x, hx, by simpa [h x hx] using hzB⟩
  by_cases hk : k ∈ s
  · have hA :
        s.biUnion A = (s.erase k).biUnion A ∪ A k := by
      rw [← Finset.insert_erase hk, Finset.biUnion_insert,
        Finset.erase_insert (by simp)]
      rw [Finset.union_comm]
    have hB :
        s.biUnion B = (s.erase k).biUnion A ∪ B k := by
      rw [← Finset.insert_erase hk, Finset.biUnion_insert,
        Finset.erase_insert (by simp), ← h_common]
      rw [Finset.union_comm]
    rw [hA, hB]
    exact CommonUnionCardDifferenceBound ((s.erase k).biUnion A) (A k) (B k)
  · have hs_eq : s.erase k = s := by
      ext x
      simp [hk]
    have h_all : ∀ x ∈ s, A x = B x := by
      intro x hx
      exact h x (by simpa [hs_eq] using hx)
    have hbi : s.biUnion A = s.biUnion B := by
      apply Finset.ext
      intro z
      rw [Finset.mem_biUnion, Finset.mem_biUnion]
      constructor
      · intro hz
        rcases hz with ⟨x, hx, hzA⟩
        exact ⟨x, hx, by simpa [h_all x hx] using hzA⟩
      · intro hz
        rcases hz with ⟨x, hx, hzB⟩
        exact ⟨x, hx, by simpa [h_all x hx] using hzB⟩
    rw [hbi]
    simp
