import Tablet.GnpGraphWeight
import Tablet.GnpCylinderSum

open Classical

-- [TABLET NODE: GnpCodegreeBound]

theorem GnpCodegreeBound (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r s : Fin m) (hrs : r ≠ s) (T : ℕ) :
    (∑ G : SimpleGraph (Fin m),
      if T ≤ (Finset.univ.filter (fun t => G.Adj r t ∧ G.Adj s t)).card then
        GnpGraphWeight p G
      else 0) ≤
    (Nat.choose m T : ℝ) * (p ^ 2) ^ T := by
-- BODY
  have hW : ∀ G : SimpleGraph (Fin m), 0 ≤ GnpGraphWeight p G := by
    intro G
    unfold GnpGraphWeight
    apply Finset.prod_nonneg
    intro x _
    split_ifs <;> linarith
  have h_bound : (∑ G : SimpleGraph (Fin m),
      if T ≤ (Finset.univ.filter (fun t => G.Adj r t ∧ G.Adj s t)).card then
        GnpGraphWeight p G
      else 0) ≤
      ∑ S ∈ Finset.powersetCard T Finset.univ,
        ∑ G : SimpleGraph (Fin m),
          if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0 := by
    calc
      (∑ G : SimpleGraph (Fin m),
        if T ≤ (Finset.univ.filter (fun t => G.Adj r t ∧ G.Adj s t)).card then
          GnpGraphWeight p G
        else 0)
      _ ≤ ∑ G : SimpleGraph (Fin m),
            ∑ S ∈ Finset.powersetCard T Finset.univ,
              if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0 := by
        apply Finset.sum_le_sum
        intro G _
        by_cases hG : T ≤ (Finset.univ.filter (fun t => G.Adj r t ∧ G.Adj s t)).card
        · rw [if_pos hG]
          obtain ⟨S, hS1, hS2⟩ := Finset.exists_subset_card_eq hG
          have hS_mem : S ∈ Finset.powersetCard T Finset.univ := by
            simp only [Finset.mem_powersetCard, Finset.subset_univ, hS2, and_self]
          have hS_cond : ∀ t ∈ S, G.Adj r t ∧ G.Adj s t := by
            intro t ht
            exact (Finset.mem_filter.mp (hS1 ht)).right
          have : GnpGraphWeight p G ≤ (if ∀ t ∈ S, G.Adj r t ∧ G.Adj s t then GnpGraphWeight p G else 0) := by
            rw [if_pos hS_cond]
          apply le_trans this
          apply Finset.single_le_sum (a := S)
          · intro S_1 _
            split_ifs
            · exact hW G
            · rfl
          · exact hS_mem
        · rw [if_neg hG]
          apply Finset.sum_nonneg
          intro S_1 _
          split_ifs
          · exact hW G
          · rfl
      _ = ∑ S ∈ Finset.powersetCard T Finset.univ,
            ∑ G : SimpleGraph (Fin m),
              if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0 := by
        exact Finset.sum_comm
  apply le_trans h_bound
  have h_inner : ∀ S ∈ Finset.powersetCard T Finset.univ,
      (∑ G : SimpleGraph (Fin m),
        if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) ≤ (p^2)^T := by
    intro S hS
    simp only [Finset.mem_powersetCard] at hS
    by_cases hr : r ∈ S
    · have : ∀ G : SimpleGraph (Fin m), (if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) = 0 := by
        intro G
        have hnot : ¬(∀ t ∈ S, G.Adj r t ∧ G.Adj s t) := by
          intro h
          have := h r hr
          have h_adj : G.Adj r r := this.1
          revert h_adj
          simp
        rw [if_neg hnot]
      have hsum : (∑ G : SimpleGraph (Fin m), if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro G _
        exact this G
      rw [hsum]
      have hp2 : 0 ≤ p^2 := sq_nonneg p
      exact pow_nonneg hp2 T
    · by_cases hs : s ∈ S
      · have : ∀ G : SimpleGraph (Fin m), (if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) = 0 := by
          intro G
          have hnot : ¬(∀ t ∈ S, G.Adj r t ∧ G.Adj s t) := by
            intro h
            have := h s hs
            have h_adj : G.Adj s s := this.2
            revert h_adj
            simp
          rw [if_neg hnot]
        have hsum : (∑ G : SimpleGraph (Fin m), if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro G _
          exact this G
        rw [hsum]
        have hp2 : 0 ≤ p^2 := sq_nonneg p
        exact pow_nonneg hp2 T
      · rw [GnpCylinderSum m p S r s hrs hr hs]
        rw [hS.2]
  have h_bound2 : (∑ S ∈ Finset.powersetCard T Finset.univ,
            ∑ G : SimpleGraph (Fin m),
              if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) ≤
          ∑ S ∈ Finset.powersetCard T (Finset.univ : Finset (Fin m)), (p^2)^T := by
    apply Finset.sum_le_sum
    intro S hS
    exact h_inner S hS
  apply le_trans h_bound2
  rw [Finset.sum_const]
  rw [Finset.card_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl
