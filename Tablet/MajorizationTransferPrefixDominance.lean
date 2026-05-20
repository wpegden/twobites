import Tablet.Preamble

open Finset Real

-- [TABLET NODE: MajorizationTransferPrefixDominance]

theorem MajorizationTransferPrefixDominance :
    ∀ N : ℕ, ∀ b x : Fin N → ℝ,
    ∀ i j : Fin N, i.val < j.val →
    ∀ δ : ℝ, 0 < δ → δ ≤ x i - b i → δ ≤ b j - x j →
    (∀ r : ℕ, i.val < r → r ≤ j.val → δ ≤ (∑ k ∈ univ.filter (·.val < r), x k) - (∑ k ∈ univ.filter (·.val < r), b k)) →
    (∀ r : ℕ, r ≤ N → ∑ k ∈ univ.filter (·.val < r), b k ≤ ∑ k ∈ univ.filter (·.val < r), x k) →
    (∑ k, x k) = (∑ k, b k) →
    ∀ y : Fin N → ℝ,
    y i = x i - δ →
    y j = x j + δ →
    (∀ k : Fin N, k ≠ i → k ≠ j → y k = x k) →
    (∑ k, y k) = (∑ k, b k) ∧
    (∀ r : ℕ, r ≤ N → ∑ k ∈ univ.filter (·.val < r), b k ≤ ∑ k ∈ univ.filter (·.val < r), y k) := by
-- BODY
  intros N b x i j hij δ hδ hδi hδj hr_mid hr_all hsum y hyi hyj hyk
  have sum_y_eq : ∀ s : Finset (Fin N), ∑ k ∈ s, y k = ∑ k ∈ s, x k - (if i ∈ s then δ else 0) + (if j ∈ s then δ else 0) := by
    intro s
    have hy_eq : ∀ k, y k = x k - (if k = i then δ else 0) + (if k = j then δ else 0) := by
      intro k
      by_cases hki : k = i
      · rw [hki, hyi]
        have : j ≠ i := ne_of_gt hij
        simp [this.symm]
      · by_cases hkj : k = j
        · rw [hkj, hyj]
          have : j ≠ i := ne_of_gt hij
          simp [this]
        · rw [hyk k hki hkj]
          simp [hki, hkj]
    rw [sum_congr rfl (fun k _ => hy_eq k)]
    rw [sum_add_distrib, sum_sub_distrib]
    have eq1 : (fun k => if k = i then δ else 0) = fun k => if k = i then (fun _ => δ) k else 0 := rfl
    have eq2 : (fun k => if k = j then δ else 0) = fun k => if k = j then (fun _ => δ) k else 0 := rfl
    rw [eq1, eq2, Finset.sum_ite_eq', Finset.sum_ite_eq']
  constructor
  · have h := sum_y_eq univ
    simp at h
    linarith [h, hsum]
  · intro r hr
    have h := sum_y_eq (univ.filter (·.val < r))
    rw [h]
    by_cases hri : r ≤ i.val
    · have hi : i ∉ univ.filter (·.val < r) := fun h_in => not_lt.mpr hri (mem_filter.mp h_in).2
      have h_rj : r ≤ j.val := le_trans hri (le_of_lt hij)
      have hj : j ∉ univ.filter (·.val < r) := fun h_in => not_lt.mpr h_rj (mem_filter.mp h_in).2
      rw [if_neg hi, if_neg hj]
      have := hr_all r hr
      linarith
    · push Not at hri
      by_cases hrj : r ≤ j.val
      · have hi : i ∈ univ.filter (·.val < r) := mem_filter.mpr ⟨mem_univ i, hri⟩
        have hj : j ∉ univ.filter (·.val < r) := fun h_in => not_lt.mpr hrj (mem_filter.mp h_in).2
        rw [if_pos hi, if_neg hj]
        have h_mid := hr_mid r hri hrj
        linarith
      · push Not at hrj
        have hi : i ∈ univ.filter (·.val < r) := mem_filter.mpr ⟨mem_univ i, hri⟩
        have hj : j ∈ univ.filter (·.val < r) := mem_filter.mpr ⟨mem_univ j, hrj⟩
        rw [if_pos hi, if_pos hj]
        have := hr_all r hr
        linarith
