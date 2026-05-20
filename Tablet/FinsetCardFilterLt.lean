import Tablet.Preamble
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

-- [TABLET NODE: FinsetCardFilterLt]

theorem FinsetCardFilterLt {α : Type} [LinearOrder α] [DecidableEq α] (s : Finset α) :
    ((s.product s).filter (fun e => e.1 < e.2)).card = s.card.choose 2 := by
-- BODY
  let S := s.product s
  let L := S.filter (fun e => e.1 < e.2)
  let G := S.filter (fun e => e.2 < e.1)
  let D := S.filter (fun e => e.1 = e.2)

  have h_LG_card : L.card = G.card := by
    let f : α × α ↪ α × α := ⟨fun e => (e.2, e.1), fun e1 e2 h => by
      injection h with h1 h2
      exact Prod.ext h2 h1⟩
    have hG : G = L.map f := by
      ext e
      constructor
      · intro h
        let h_filter := Finset.mem_filter.mp h
        let hS := h_filter.1
        let hgt := h_filter.2
        let h_prod := Finset.mem_product.mp hS
        let h_s1 := h_prod.1
        let h_s2 := h_prod.2
        apply Finset.mem_map.mpr
        use (e.2, e.1)
        constructor
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            exact ⟨h_s2, h_s1⟩
          · exact hgt
        · exact Prod.eta e
      · intro h
        obtain ⟨e', he', he_eq⟩ := Finset.mem_map.mp h
        let h_filter' := Finset.mem_filter.mp he'
        let hS' := h_filter'.1
        let hlt' := h_filter'.2
        let h_prod' := Finset.mem_product.mp hS'
        let h_s1' := h_prod'.1
        let h_s2' := h_prod'.2
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          rw [← he_eq]
          exact ⟨h_s2', h_s1'⟩
        · rw [← he_eq]
          exact hlt'
    rw [hG, Finset.card_map]

  have h_D_card : D.card = s.card := by
    let f : α ↪ α × α := ⟨fun x => (x, x), fun x y h => (Prod.mk.inj h).1⟩
    have hD : D = s.map f := by
      ext e
      constructor
      · intro h
        let h_filter := Finset.mem_filter.mp h
        let hS := h_filter.1
        let heq := h_filter.2
        let h_prod := Finset.mem_product.mp hS
        let h_s1 := h_prod.1
        apply Finset.mem_map.mpr
        use e.1
        constructor
        · exact h_s1
        · dsimp [f]
          apply Prod.ext
          · rfl
          · exact heq
      · intro h
        obtain ⟨x, hx, he_eq⟩ := Finset.mem_map.mp h
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          rw [← he_eq]
          exact ⟨hx, hx⟩
        · rw [← he_eq]
          rfl
    rw [hD, Finset.card_map]

  have h_S_card : S.card = L.card + G.card + D.card := by
    have h_union : S = L ∪ G ∪ D := by
      ext e
      rw [Finset.mem_union, Finset.mem_union]
      constructor
      · intro h
        rcases lt_trichotomy e.1 e.2 with hlt | heq | hgt
        · left; left; apply Finset.mem_filter.mpr; exact ⟨h, hlt⟩
        · right; apply Finset.mem_filter.mpr; exact ⟨h, heq⟩
        · left; right; apply Finset.mem_filter.mpr; exact ⟨h, hgt⟩
      · intro h
        cases h with
        | inl hLG =>
          cases hLG with
          | inl hL => exact (Finset.mem_filter.mp hL).1
          | inr hG => exact (Finset.mem_filter.mp hG).1
        | inr hD => exact (Finset.mem_filter.mp hD).1
    rw [h_union, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · rw [Finset.disjoint_left]
      intro e hL hG
      let hlt := (Finset.mem_filter.mp hL).2
      let hgt := (Finset.mem_filter.mp hG).2
      exact lt_asymm hlt hgt
    · apply Finset.disjoint_union_left.mpr
      constructor
      · rw [Finset.disjoint_left]
        intro e hL hD
        let hlt := (Finset.mem_filter.mp hL).2
        let heq := (Finset.mem_filter.mp hD).2
        rw [heq] at hlt
        exact lt_irrefl _ hlt
      · rw [Finset.disjoint_left]
        intro e hG hD
        let hgt := (Finset.mem_filter.mp hG).2
        let heq := (Finset.mem_filter.mp hD).2
        rw [heq] at hgt
        exact lt_irrefl _ hgt

  have h_S_val : S.card = s.card * s.card := Finset.card_product s s
  
  have h_arith : s.card * s.card = 2 * L.card + s.card := by
    rw [← h_S_val, h_S_card, h_LG_card, h_D_card, two_mul, add_assoc]

  have h_2L : 2 * L.card = s.card * (s.card - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [h_arith]
    rw [Nat.add_sub_cancel]
  
  rw [Nat.choose_two_right, ← h_2L, Nat.mul_div_cancel_left _ (by norm_num)]
