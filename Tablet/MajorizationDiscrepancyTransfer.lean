import Tablet.Preamble

open Finset Real

-- [TABLET NODE: MajorizationDiscrepancyTransfer]

theorem MajorizationDiscrepancyTransfer :
    ∀ N : ℕ, ∀ b x : Fin N → ℝ,
    (∀ i : Fin N, ∃ k : ℕ, b i = k) →
    (∀ i : Fin N, ∃ k : ℕ, x i = k) →
    (∑ i, x i) = (∑ i, b i) →
    (∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i) →
    (∀ r : ℕ, r ≤ N →
      ∑ i ∈ univ.filter (·.val < r), b i ≤ ∑ i ∈ univ.filter (·.val < r), x i) →
    x ≠ b →
    ∃ i j : Fin N, i.val < j.val ∧
      b i < x i ∧ x j < b j ∧
      ∃ δ : ℕ, 0 < δ ∧ (δ : ℝ) ≤ x i - b i ∧ (δ : ℝ) ≤ b j - x j ∧
      ∀ r : ℕ, i.val < r → r ≤ j.val → (δ : ℝ) ≤ (∑ k ∈ univ.filter (·.val < r), x k) - (∑ k ∈ univ.filter (·.val < r), b k) := by
-- BODY
  intro N b x hb hx hsum hmon hpref hne
  
  have sum_filter_lt_succ : ∀ (f : Fin N → ℝ) (i : Fin N),
    ∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val + 1), f k = (∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), f k) + f i := by
    intro f i
    have : univ.filter (fun k : Fin N => k.val < i.val + 1) = insert i (univ.filter (fun k : Fin N => k.val < i.val)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      omega
    rw [this]
    have h_notin : i ∉ univ.filter (fun k : Fin N => k.val < i.val) := by simp
    rw [sum_insert h_notin]
    ring

  have sum_split_at_i : ∀ (f : Fin N → ℝ) (i : Fin N) (r : ℕ), i.val < r → r ≤ N →
    ∑ k ∈ univ.filter (fun k : Fin N => k.val < r), f k =
      (∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), f k) +
      f i +
      ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), f k := by
    intro f i r hir _hr
    have H : univ.filter (fun k : Fin N => k.val < r) =
        (univ.filter (fun k : Fin N => k.val < i.val)) ∪
        {i} ∪
        (univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
      omega
    rw [H]
    have hd1 : Disjoint (univ.filter (fun k : Fin N => k.val < i.val)) {i} := by
      simp [disjoint_singleton_right]
    have hd2 : Disjoint ((univ.filter (fun k : Fin N => k.val < i.val)) ∪ {i}) (univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r)) := by
      simp only [disjoint_union_left]
      constructor
      · simp only [disjoint_left, mem_filter, mem_univ, true_and, not_and]
        intro x hx
        omega
      · simp only [disjoint_singleton_left, mem_filter, mem_univ, true_and, not_and]
        omega
    rw [sum_union hd2, sum_union hd1, sum_singleton]

  have hne' : ∃ i, x i ≠ b i := Function.ne_iff.mp hne
  let S := univ.filter (fun i => x i ≠ b i)
  have hS_nonempty : S.Nonempty := by
    rcases hne' with ⟨i, hi⟩
    use i
    simp [S, hi]
  let i := S.min' hS_nonempty
  have hi_mem : i ∈ S := Finset.min'_mem S hS_nonempty
  have hi_min : ∀ k ∈ S, i ≤ k := fun k hk => Finset.min'_le S k hk

  have heq : ∀ k : Fin N, k.val < i.val → x k = b k := by
    intro k hk
    have : k ∉ S := by
      intro h
      have := hi_min k h
      omega
    simp only [S, mem_filter, mem_univ, true_and, ne_eq, not_not] at this
    exact this

  have hsum_eq : ∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), x k = ∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), b k := by
    apply sum_congr rfl
    intro k hk
    simp at hk
    exact heq k hk

  have hpref_i : ∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val + 1), b k ≤ ∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val + 1), x k := by
    apply hpref
    have := i.isLt
    omega

  rw [sum_filter_lt_succ b i, sum_filter_lt_succ x i] at hpref_i
  rw [hsum_eq] at hpref_i
  have h_bi_le_xi : b i ≤ x i := by linarith
  have h_bi_lt_xi : b i < x i := by
    have : x i ≠ b i := by
      have := hi_mem
      simp only [S, mem_filter, mem_univ, true_and, ne_eq] at this
      exact this
    exact lt_of_le_of_ne h_bi_le_xi this.symm

  have h_exists_j : ∃ j, x j < b j := by
    by_contra h_not
    push Not at h_not
    have : ∑ k, b k < ∑ k, x k := by
      apply sum_lt_sum
      · intro k _
        exact h_not k
      · use i
        simp [h_bi_lt_xi]
    linarith

  let S_j := univ.filter (fun j => x j < b j)
  have hS_j_nonempty : S_j.Nonempty := by
    rcases h_exists_j with ⟨j, hj⟩
    use j
    simp [S_j, hj]
  let j := S_j.min' hS_j_nonempty
  have hj_mem : j ∈ S_j := Finset.min'_mem S_j hS_j_nonempty
  have hj_min : ∀ k ∈ S_j, j ≤ k := fun k hk => Finset.min'_le S_j k hk

  have hj_lt_bj : x j < b j := by
    have := hj_mem
    simp only [S_j, mem_filter, mem_univ, true_and] at this
    exact this

  have hi_lt_j : i.val < j.val := by
    by_contra h_not
    push Not at h_not
    have h_j_lt_i : j.val < i.val ∨ j.val = i.val := lt_or_eq_of_le h_not
    rcases h_j_lt_i with h_j_lt_i | h_j_eq_i
    · have := heq j h_j_lt_i
      linarith
    · have := Fin.ext h_j_eq_i
      rw [this] at hj_lt_bj
      linarith

  have h_xk_ge_bk : ∀ k : Fin N, k.val < j.val → b k ≤ x k := by
    intro k hk
    by_contra h_not
    push Not at h_not
    have : k ∉ S_j := by
      intro h
      have := hj_min k h
      omega
    simp only [S_j, mem_filter, mem_univ, true_and, not_lt] at this
    linarith

  use i, j
  refine ⟨hi_lt_j, h_bi_lt_xi, hj_lt_bj, 1, by omega, ?_, ?_, ?_⟩

  · have h_xi : ∃ k : ℕ, x i = k := hx i
    have h_bi : ∃ k : ℕ, b i = k := hb i
    rcases h_xi with ⟨k_xi, hk_xi⟩
    rcases h_bi with ⟨k_bi, hk_bi⟩
    rw [hk_xi, hk_bi]
    have : (k_bi : ℝ) < (k_xi : ℝ) := by
      rw [← hk_bi, ← hk_xi]
      exact h_bi_lt_xi
    have h_lt : k_bi < k_xi := Nat.cast_lt.mp this
    have h_ge : 1 ≤ k_xi - k_bi := by omega
    have h_ge_real : ((1 : ℕ) : ℝ) ≤ ((k_xi - k_bi : ℕ) : ℝ) := Nat.cast_le.mpr h_ge
    have h2 : (k_xi : ℝ) - (k_bi : ℝ) = ((k_xi - k_bi : ℕ) : ℝ) := by
      exact (Nat.cast_sub (le_of_lt h_lt)).symm
    rw [h2]
    exact h_ge_real

  · have h_xj : ∃ k : ℕ, x j = k := hx j
    have h_bj : ∃ k : ℕ, b j = k := hb j
    rcases h_xj with ⟨k_xj, hk_xj⟩
    rcases h_bj with ⟨k_bj, hk_bj⟩
    rw [hk_xj, hk_bj]
    have : (k_xj : ℝ) < (k_bj : ℝ) := by
      rw [← hk_bj, ← hk_xj]
      exact hj_lt_bj
    have h_lt : k_xj < k_bj := Nat.cast_lt.mp this
    have h_ge : 1 ≤ k_bj - k_xj := by omega
    have h_ge_real : ((1 : ℕ) : ℝ) ≤ ((k_bj - k_xj : ℕ) : ℝ) := Nat.cast_le.mpr h_ge
    have h2 : (k_bj : ℝ) - (k_xj : ℝ) = ((k_bj - k_xj : ℕ) : ℝ) := by
      exact (Nat.cast_sub (le_of_lt h_lt)).symm
    rw [h2]
    exact h_ge_real

  · intro r hir hrj
    have hrN : r ≤ N := by
      have := j.isLt
      omega
    rw [sum_split_at_i x i r hir hrN, sum_split_at_i b i r hir hrN]
    rw [hsum_eq]
    have h1 : ((1 : ℕ) : ℝ) ≤ x i - b i := by
      have h_xi : ∃ k : ℕ, x i = k := hx i
      have h_bi : ∃ k : ℕ, b i = k := hb i
      rcases h_xi with ⟨k_xi, hk_xi⟩
      rcases h_bi with ⟨k_bi, hk_bi⟩
      rw [hk_xi, hk_bi]
      have : (k_bi : ℝ) < (k_xi : ℝ) := by
        rw [← hk_bi, ← hk_xi]
        exact h_bi_lt_xi
      have h_lt : k_bi < k_xi := Nat.cast_lt.mp this
      have h_ge : 1 ≤ k_xi - k_bi := by omega
      have h_ge_real : ((1 : ℕ) : ℝ) ≤ ((k_xi - k_bi : ℕ) : ℝ) := Nat.cast_le.mpr h_ge
      have h2 : (k_xi : ℝ) - (k_bi : ℝ) = ((k_xi - k_bi : ℕ) : ℝ) := by
        exact (Nat.cast_sub (le_of_lt h_lt)).symm
      rw [h2]
      exact h_ge_real
    have h2 : (0 : ℝ) ≤ ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), x k - ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), b k := by
      rw [← sum_sub_distrib]
      apply sum_nonneg
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      have : b k ≤ x k := by
        apply h_xk_ge_bk
        omega
      linarith
    have h3 : (∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), b k) + x i +
      ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), x k -
      ((∑ k ∈ univ.filter (fun k : Fin N => k.val < i.val), b k) + b i +
      ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), b k) =
      (x i - b i) + (∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), x k - ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), b k) := by ring
    rw [h3]
    have h_final : ((1 : ℕ) : ℝ) + 0 ≤ (x i - b i) + (∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), x k - ∑ k ∈ univ.filter (fun k : Fin N => i.val < k.val ∧ k.val < r), b k) := add_le_add h1 h2
    rw [add_zero] at h_final
    exact h_final

