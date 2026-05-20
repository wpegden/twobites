import Tablet.RealChooseTwo
import Mathlib.Algebra.BigOperators.Field

-- [TABLET NODE: RealChooseTwoCappedSumBound]

theorem RealChooseTwoCappedSumBound :
    ∀ {α : Type*} (s : Finset α) (a : α → ℝ) (M : ℝ),
      0 ≤ M →
      (∀ x, x ∈ s → 0 ≤ a x) →
      (∀ x, x ∈ s → a x ≤ M) →
      M ≤ s.sum a →
        s.sum (fun x => RealChooseTwo (a x)) ≤
          RealChooseTwo M + RealChooseTwo (s.sum a - M) := by
-- BODY
  classical
  intro α s a M hM h_nonneg h_cap hM_le
  have hsq_nonneg :
      ∀ (t : Finset α) (b : α → ℝ),
        (∀ x, x ∈ t → 0 ≤ b x) →
          t.sum (fun x => (b x) ^ 2) ≤ (t.sum b) ^ 2 := by
    intro t b hb_nonneg
    revert hb_nonneg
    refine Finset.induction_on t ?sq_base ?sq_step
    · intro _hb_nonneg
      simp
    · intro x t hx hrec hb_insert
      have hx_nonneg : 0 ≤ b x := hb_insert x (by simp [hx])
      have ht_nonneg : ∀ y, y ∈ t → 0 ≤ b y := by
        intro y hy
        exact hb_insert y (by simp [hy])
      have hsum_nonneg : 0 ≤ t.sum b :=
        Finset.sum_nonneg (fun y hy => ht_nonneg y hy)
      have hrec' : t.sum (fun y => (b y) ^ 2) ≤ (t.sum b) ^ 2 :=
        hrec ht_nonneg
      calc
        (insert x t).sum (fun y => (b y) ^ 2)
            = (b x) ^ 2 + t.sum (fun y => (b y) ^ 2) := by
              simp [hx]
        _ ≤ (b x) ^ 2 + (t.sum b) ^ 2 := by
              linarith
        _ ≤ (b x + t.sum b) ^ 2 := by
              nlinarith [mul_nonneg hx_nonneg hsum_nonneg]
        _ = ((insert x t).sum b) ^ 2 := by
              simp [hx]
  have hsq_split :
      ∀ (t : Finset α) (b : α → ℝ) (M : ℝ),
        0 ≤ M →
        (∀ x, x ∈ t → 0 ≤ b x) →
        (∀ x, x ∈ t → b x ≤ M) →
        M ≤ t.sum b →
          t.sum (fun x => (b x) ^ 2) ≤ M ^ 2 + (t.sum b - M) ^ 2 := by
    intro t b M hM ht_nonneg ht_cap hM_le_t
    revert ht_nonneg ht_cap hM_le_t
    refine Finset.induction_on t ?split_base ?split_step
    · intro _ht_nonneg _ht_cap hM_le_t
      simp at hM_le_t ⊢
      nlinarith [hM]
    · intro x t hx hrec ht_nonneg ht_cap hM_le_insert
      have hx_nonneg : 0 ≤ b x := ht_nonneg x (by simp [hx])
      have hx_cap : b x ≤ M := ht_cap x (by simp [hx])
      have ht_nonneg' : ∀ y, y ∈ t → 0 ≤ b y := by
        intro y hy
        exact ht_nonneg y (by simp [hy])
      have ht_cap' : ∀ y, y ∈ t → b y ≤ M := by
        intro y hy
        exact ht_cap y (by simp [hy])
      have hsum_insert : (insert x t).sum b = b x + t.sum b := by
        simp [hx]
      have hsq_insert :
          (insert x t).sum (fun y => (b y) ^ 2) =
            (b x) ^ 2 + t.sum (fun y => (b y) ^ 2) := by
        simp [hx]
      by_cases hM_le_t : M ≤ t.sum b
      · have hrec' :
            t.sum (fun y => (b y) ^ 2) ≤ M ^ 2 + (t.sum b - M) ^ 2 :=
          hrec ht_nonneg' ht_cap' hM_le_t
        rw [hsq_insert, hsum_insert]
        nlinarith [hrec', hx_nonneg, hM_le_t]
      · have ht_sum_le_M : t.sum b ≤ M := le_of_not_ge hM_le_t
        have ht_sq :
            t.sum (fun y => (b y) ^ 2) ≤ (t.sum b) ^ 2 :=
          hsq_nonneg t b ht_nonneg'
        rw [hsq_insert, hsum_insert]
        nlinarith [ht_sq, hx_cap, ht_sum_le_M]
  have hsq :
      s.sum (fun x => (a x) ^ 2) ≤ M ^ 2 + (s.sum a - M) ^ 2 :=
    hsq_split s a M hM h_nonneg h_cap hM_le
  have hsum_choose_eq :
      s.sum (fun x => RealChooseTwo (a x)) =
        (s.sum (fun x => (a x) ^ 2) - s.sum a) / 2 := by
    simp_rw [RealChooseTwo]
    have hterm : ∀ x, a x * (a x - 1) = a x ^ 2 - a x := by
      intro x
      ring
    simp_rw [hterm]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib]
  rw [hsum_choose_eq]
  unfold RealChooseTwo
  nlinarith
