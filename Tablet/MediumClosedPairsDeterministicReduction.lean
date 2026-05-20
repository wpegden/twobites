import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: MediumClosedPairsDeterministicReduction]

open scoped BigOperators

theorem MediumClosedPairsDeterministicReduction {α : Type} [DecidableEq α]
    (M : Finset α) (w : α → ℕ) (edgeCount : Finset α → ℕ)
    (A L t2 lower : ℝ)
    (hA_nonneg : 0 ≤ A) (hL_pos : 0 < L)
    (hlarge : A < ∑ x ∈ M, (w x : ℝ))
    (hupper : ∀ x ∈ M, (w x : ℝ) ≤ t2)
    (hlower : ∀ x ∈ M, lower ≤ (w x : ℝ))
    (hcharge : ∀ B : Finset α, B ⊆ M →
      ∑ x ∈ B, (w x : ℝ) ≤ L * (edgeCount B : ℝ)) :
    ∃ B : Finset α,
      B.Nonempty ∧
      B ⊆ M ∧
      A < ∑ x ∈ B, (w x : ℝ) ∧
      (∑ x ∈ B, (w x : ℝ)) ≤ A + t2 ∧
      (B.card : ℝ) * lower ≤ A + t2 ∧
      A / L < (edgeCount B : ℝ) := by
-- BODY
  classical
  let S (B : Finset α) : ℝ := ∑ x ∈ B, (w x : ℝ)
  have hex :
      ∃ r : ℕ, ∃ B : Finset α, B ⊆ M ∧ A < S B ∧ B.card = r := by
    exact ⟨M.card, M, by intro x hx; exact hx, by simpa [S] using hlarge, rfl⟩
  let r : ℕ := Nat.find hex
  obtain ⟨B, hBinfo⟩ := Nat.find_spec hex
  rcases hBinfo with ⟨hBM, hBA, hBcard_find⟩
  have hBcard : B.card = r := by
    simpa [r] using hBcard_find
  have hminimal :
      ∀ C : Finset α, C ⊆ M → A < S C → B.card ≤ C.card := by
    intro C hCM hCA
    have hC :
        ∃ B' : Finset α, B' ⊆ M ∧ A < S B' ∧ B'.card = C.card :=
      ⟨C, hCM, hCA, rfl⟩
    have hfind : r ≤ C.card := by
      simpa [r] using Nat.find_min' hex hC
    exact hBcard.trans_le hfind
  have hB_nonempty : B.Nonempty := by
    have hcard_pos : 0 < B.card := by
      by_contra hnot
      have hcard_zero : B.card = 0 := Nat.eq_zero_of_not_pos hnot
      have hBempty : B = ∅ := Finset.card_eq_zero.mp hcard_zero
      have hS_zero : S B = 0 := by
        simp [S, hBempty]
      linarith
    exact Finset.card_pos.mp hcard_pos
  have hB_nonempty_out := hB_nonempty
  obtain ⟨b, hb⟩ := hB_nonempty
  have herase_sub : B.erase b ⊆ M := by
    intro x hx
    exact hBM (Finset.mem_of_mem_erase hx)
  have herase_not_large : ¬ A < S (B.erase b) := by
    intro herase_large
    have hmin := hminimal (B.erase b) herase_sub herase_large
    exact not_le_of_gt (Finset.card_erase_lt_of_mem hb) hmin
  have herase_le : S (B.erase b) ≤ A := le_of_not_gt herase_not_large
  have hbM : b ∈ M := hBM hb
  have hsum_decomp : S B = S (B.erase b) + (w b : ℝ) := by
    exact (Finset.sum_erase_add B (fun x => (w x : ℝ)) hb).symm
  have hsum_upper : S B ≤ A + t2 := by
    rw [hsum_decomp]
    linarith [herase_le, hupper b hbM]
  have hconst_sum : (∑ _x ∈ B, lower) = (B.card : ℝ) * lower := by
    simp [nsmul_eq_mul]
  have hcard_lower_to_sum : (B.card : ℝ) * lower ≤ S B := by
    rw [← hconst_sum]
    exact Finset.sum_le_sum (fun x hx => hlower x (hBM hx))
  have hcard_control : (B.card : ℝ) * lower ≤ A + t2 :=
    le_trans hcard_lower_to_sum hsum_upper
  have hA_lt_edge_mass : A < L * (edgeCount B : ℝ) :=
    lt_of_lt_of_le hBA (hcharge B hBM)
  have hedge_lower : A / L < (edgeCount B : ℝ) := by
    rw [div_lt_iff₀ hL_pos]
    nlinarith
  exact ⟨B, hB_nonempty_out, hBM, by simpa [S] using hBA,
    by simpa [S] using hsum_upper, hcard_control, hedge_lower⟩
