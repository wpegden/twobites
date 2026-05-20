import Tablet.Preamble
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Tablet.MajorizationAdjacentSwapDistance

open Finset Equiv Equiv.Perm

-- [TABLET NODE: MajorizationAdjacentInversionSorting]

theorem MajorizationAdjacentInversionSorting (N : ℕ) (b y : Fin N → ℝ)
    (hb : ∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i) :
    ∃ u_star : Fin N → ℝ, (∃ σ : Perm (Fin N), ∀ i, u_star i = y (σ i)) ∧
      (∀ i j : Fin N, i.val ≤ j.val → u_star j ≤ u_star i) ∧
      ∑ i, |u_star i - b i| ≤ ∑ i, |y i - b i| := by
-- BODY
  let score (σ : Perm (Fin N)) : ℝ := ∑ i, (i.val : ℝ) * y (σ i)
  have _ : DecidableRel (fun τ σ : Perm (Fin N) => score τ < score σ) := Classical.decRel _
  let rank (σ : Perm (Fin N)) : ℕ := (univ.filter (fun τ => score τ < score σ)).card
  have rank_strict_mono : ∀ {σ1 σ2 : Perm (Fin N)}, score σ1 < score σ2 → rank σ1 < rank σ2 := by
    intro σ1 σ2 h
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · use σ1
      simp [h]
    · intro τ
      simp only [mem_filter, mem_univ, true_and]
      intro hτ
      exact lt_trans hτ h

  have sum_insert_two' : ∀ (f : Fin N → ℝ) (r r_next : Fin N), r ≠ r_next → ∑ i, f i = f r + f r_next + ∑ i ∈ univ \ {r, r_next}, f i := by
    intro f r r_next h_neq
    have eq_univ : (univ : Finset (Fin N)) = insert r (insert r_next (univ \ {r, r_next})) := by
      ext x
      simp
      tauto
    nth_rw 1 [eq_univ]
    have h1 : r ∉ insert r_next (univ \ {r, r_next}) := by simp [h_neq]
    rw [sum_insert h1]
    have h2 : r_next ∉ univ \ {r, r_next} := by simp
    rw [sum_insert h2]
    rw [add_assoc]

  have score_swap : ∀ (σ : Perm (Fin N)) (r : Fin N) (hr : r.val + 1 < N),
      y (σ r) < y (σ ⟨r.val + 1, hr⟩) →
      score (σ * swap r ⟨r.val + 1, hr⟩) < score σ := by
    intro σ r hr hu
    let r_next : Fin N := ⟨r.val + 1, hr⟩
    have hr_neq : r ≠ r_next := by
      intro h_eq
      have : r.val = r_next.val := Fin.ext_iff.mp h_eq
      dsimp [r_next] at this
      linarith
    have eq1 := sum_insert_two' (fun i => (i.val : ℝ) * y (σ i)) r r_next hr_neq
    have eq2 := sum_insert_two' (fun i => (i.val : ℝ) * y (σ ((swap r r_next) i))) r r_next hr_neq
    have h_r : (r.val : ℝ) * y (σ ((swap r r_next) r)) = (r.val : ℝ) * y (σ r_next) := by dsimp; rw [swap_apply_left]
    have h_next : (r_next.val : ℝ) * y (σ ((swap r r_next) r_next)) = (r_next.val : ℝ) * y (σ r) := by dsimp; rw [swap_apply_right]
    have h_rest : ∑ i ∈ univ \ {r, r_next}, (i.val : ℝ) * y (σ ((swap r r_next) i)) = ∑ i ∈ univ \ {r, r_next}, (i.val : ℝ) * y (σ i) := by
      apply sum_congr rfl
      intro x hx
      simp at hx
      have h_ne1 : x ≠ r := by tauto
      have h_ne2 : x ≠ r_next := by tauto
      rw [swap_apply_of_ne_of_ne h_ne1 h_ne2]
    have H1 : score σ = (r.val : ℝ) * y (σ r) + (r_next.val : ℝ) * y (σ r_next) + ∑ i ∈ univ \ {r, r_next}, (i.val : ℝ) * y (σ i) := by
      dsimp [score]
      exact eq1
    have H2 : score (σ * swap r r_next) = (r.val : ℝ) * y (σ r_next) + (r_next.val : ℝ) * y (σ r) + ∑ i ∈ univ \ {r, r_next}, (i.val : ℝ) * y (σ i) := by
      dsimp [score]
      rw [eq2]
      dsimp only
      rw [h_r, h_next, h_rest]
    change score (σ * swap r r_next) < score σ
    rw [H1, H2]
    have H_val : (r_next.val : ℝ) = (r.val : ℝ) + 1 := by
      have eq : r_next.val = r.val + 1 := rfl
      rw [eq]
      push_cast
      rfl
    rw [H_val]
    linarith

  have not_desc_exists_adj : ∀ (u : Fin N → ℝ), (¬ ∀ i j : Fin N, i.val ≤ j.val → u j ≤ u i) →
      ∃ r : Fin N, ∃ hr : r.val + 1 < N, u r < u ⟨r.val + 1, hr⟩ := by
    intro u h
    by_contra h_contra
    push Not at h_contra
    apply h
    intro i j hij
    have H : ∀ d, ∀ k : Fin N, k.val + d = j.val → u j ≤ u k := by
      intro d
      induction d with
      | zero =>
        intro k hk
        have h_eq : k = j := Fin.ext (by linarith)
        rw [h_eq]
      | succ d ih =>
        intro k hk
        have hk_lt : k.val + 1 < N := by
          have h_j_lt : j.val < N := j.prop
          linarith
        have H_adj := h_contra k hk_lt
        have H_ih := ih ⟨k.val + 1, hk_lt⟩ (by linarith)
        exact le_trans H_ih H_adj
    exact H (j.val - i.val) i (Nat.add_sub_of_le hij)

  have sorting_path_aux : ∀ (k : ℕ), ∀ σ : Perm (Fin N), rank σ = k →
      ∃ σ_star : Perm (Fin N),
        (∀ i j : Fin N, i.val ≤ j.val → y (σ_star j) ≤ y (σ_star i)) ∧
        ∑ i, |y (σ_star i) - b i| ≤ ∑ i, |y (σ i) - b i| := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro σ hk
      by_cases h_desc : ∀ i j : Fin N, i.val ≤ j.val → y (σ j) ≤ y (σ i)
      · exact ⟨σ, h_desc, le_rfl⟩
      · have h_adj := not_desc_exists_adj (y ∘ σ) h_desc
        rcases h_adj with ⟨r, hr, hu⟩
        let r_next : Fin N := ⟨r.val + 1, hr⟩
        let σ' := σ * swap r r_next
        have h_score := score_swap σ r hr hu
        have h_rank := rank_strict_mono h_score
        have h_rank_eq : rank σ' < k := by
          rw [← hk]
          exact h_rank
        have H_ih := ih (rank σ') h_rank_eq σ' rfl
        rcases H_ih with ⟨σ_star, h_star_desc, h_star_dist⟩
        use σ_star
        refine ⟨h_star_desc, ?_⟩
        have h_swap_dist := MajorizationAdjacentSwapDistance N b (y ∘ σ) hb r hr hu
        exact le_trans h_star_dist h_swap_dist

  have H := sorting_path_aux (rank (1 : Perm (Fin N))) (1 : Perm (Fin N)) rfl
  rcases H with ⟨σ_star, h_desc, h_dist⟩
  use y ∘ σ_star
  refine ⟨⟨σ_star, fun _ => rfl⟩, h_desc, ?_⟩
  have h_y : y = y ∘ (1 : Perm (Fin N)) := by ext i; rfl
  nth_rw 1 [h_y]
  exact h_dist