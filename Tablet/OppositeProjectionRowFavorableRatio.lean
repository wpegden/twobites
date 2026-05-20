import Tablet.Preamble

-- [TABLET NODE: OppositeProjectionRowFavorableRatio]

open scoped Classical BigOperators

theorem OppositeProjectionRowFavorableRatio (m : ℕ) (S : ℕ) (h q : ℕ) (h_le_q : h ≤ q) (q_le_m : q ≤ m) (h_le_S : h ≤ S) :
  (((Nat.descFactorial S h : ℝ) * (Nat.descFactorial (m - h) (q - h) : ℝ)) / (Nat.descFactorial m q : ℝ)) =
  (∏ l ∈ Finset.range h, ((S - l : ℝ) / (m - l : ℝ))) := by
-- BODY
  have descFactorial_add : ∀ j, Nat.descFactorial m (h + j) = Nat.descFactorial m h * Nat.descFactorial (m - h) j := by
    intro j
    induction j with
    | zero =>
      rw [Nat.add_zero, Nat.descFactorial_zero, mul_one]
    | succ j ih =>
      rw [Nat.add_succ, Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
      have h1 : m - (h + j) = m - h - j := by omega
      rw [h1]
      ring
  have H1 : Nat.descFactorial m q = Nat.descFactorial m h * Nat.descFactorial (m - h) (q - h) := by
    have h2 : q = h + (q - h) := by omega
    nth_rw 1 [h2]
    apply descFactorial_add
  rw [H1, Nat.cast_mul]
  have hz : (Nat.descFactorial (m - h) (q - h) : ℝ) ≠ 0 := by
    have h_pos : 0 < Nat.descFactorial (m - h) (q - h) := by
      apply Nat.pos_of_ne_zero
      intro h_contra
      rw [Nat.descFactorial_eq_zero_iff_lt] at h_contra
      omega
    exact Nat.cast_ne_zero.mpr (ne_of_gt h_pos)
  rw [mul_div_mul_right _ _ hz]
  have hs_prod : (Nat.descFactorial S h : ℝ) = ∏ l ∈ Finset.range h, (S - l : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : x ≤ S := by omega
    rw [Nat.cast_sub this]
  have hm_prod : (Nat.descFactorial m h : ℝ) = ∏ l ∈ Finset.range h, (m - l : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : x ≤ m := by omega
    rw [Nat.cast_sub this]
  rw [hs_prod, hm_prod, ← Finset.prod_div_distrib]
