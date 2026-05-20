import Tablet.Preamble
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative

open Finset
open scoped Classical

-- [TABLET NODE: TwoBiteEventProbabilityUnionBound]

theorem TwoBiteEventProbabilityUnionBound {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [Fintype ι] (E : ι → TwoBiteSample n m p → Prop) :
    TwoBiteEventProbability n m p (fun ω => ∃ i, E i ω) ≤
    ∑ i, TwoBiteEventProbability n m p (E i) := by
-- BODY
  have h_eq : ∀ (event : TwoBiteSample n m p → Prop), TwoBiteEventProbability n m p event = ∑ ω, if event ω then TwoBiteSampleWeight ω else 0 := by
    intro event
    unfold TwoBiteEventProbability
    exact sum_filter _ _
  rw [h_eq (fun ω => ∃ i, E i ω)]
  have h2 : (∑ i, TwoBiteEventProbability n m p (E i)) = ∑ i, ∑ ω, if E i ω then TwoBiteSampleWeight ω else 0 := by
    apply sum_congr rfl
    intro i _
    rw [h_eq (E i)]
  rw [h2]
  have h3 : (∑ i, ∑ ω, if E i ω then TwoBiteSampleWeight ω else 0) = 
            ∑ ω, ∑ i, if E i ω then TwoBiteSampleWeight ω else 0 := sum_comm
  rw [h3]
  apply sum_le_sum
  intro ω _
  split_ifs with h_ex
  · have h_pos : (univ.filter (fun i => E i ω)).Nonempty := by
      rcases h_ex with ⟨i, hi⟩
      use i
      rw [mem_filter]
      exact ⟨mem_univ _, hi⟩
    have h_ge_1 : (1 : ℝ) ≤ (univ.filter (fun i => E i ω)).card := by
      exact_mod_cast card_pos.mpr h_pos
    have h_sum : ∑ i ∈ univ.filter (fun i => E i ω), TwoBiteSampleWeight ω = 
                 (univ.filter (fun i => E i ω)).card * TwoBiteSampleWeight ω := by
      rw [sum_const]
      simp
    have h4 : (∑ i, if E i ω then TwoBiteSampleWeight ω else 0) = 
              ∑ i ∈ univ.filter (fun i => E i ω), TwoBiteSampleWeight ω := (sum_filter _ _).symm
    rw [h4, h_sum]
    have h_w_nonneg : 0 ≤ TwoBiteSampleWeight ω := TwoBiteSampleWeightNonnegative ω hp0 hp1
    nlinarith
  · have h4 : (∑ i, if E i ω then TwoBiteSampleWeight ω else 0) = 
              ∑ i ∈ univ.filter (fun i => E i ω), TwoBiteSampleWeight ω := (sum_filter _ _).symm
    rw [h4]
    have h_sum : ∑ i ∈ univ.filter (fun i => E i ω), TwoBiteSampleWeight ω = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [mem_filter] at hi
      exact False.elim (h_ex ⟨i, hi.2⟩)
    rw [h_sum]
