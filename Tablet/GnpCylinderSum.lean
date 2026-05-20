import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Mathlib.Tactic

open Classical

-- [TABLET NODE: GnpCylinderSum]

theorem GnpCylinderSum (m : ℕ) (p : ℝ) (S : Finset (Fin m)) (r s : Fin m)
    (hrs : r ≠ s) (hr : r ∉ S) (hs : s ∉ S) :
    (∑ G : SimpleGraph (Fin m),
      if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) =
    (p^2) ^ S.card := by
-- BODY
  let GnpEdge := {e : Fin m × Fin m // e.1.val < e.2.val}
  let gnpGraphBoolEquiv : SimpleGraph (Fin m) ≃ (GnpEdge → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        SimpleGraph.mk
          (fun i j =>
            if h : i.val < j.val then
              f ⟨(i, j), h⟩ = true
            else if h' : j.val < i.val then
              f ⟨(j, i), h'⟩ = true
            else
              False)
          (by
            intro i j
            by_cases hij : i.val < j.val
            · have hji : ¬ j.val < i.val := by omega
              simp [hij, hji]
            · by_cases hji : j.val < i.val
              · simp [hij, hji]
              · simp [hij, hji])
          ⟨fun i => by simp⟩
      left_inv := by
        intro G
        apply SimpleGraph.ext
        funext i j
        apply propext
        by_cases hij : i.val < j.val
        · simp [hij]
        · by_cases hji : j.val < i.val
          · simp [hij, hji, SimpleGraph.adj_comm]
          · have hij_eq : i = j := by apply Fin.ext; omega
            subst j
            simp
      right_inv := by
        intro f
        funext e
        rcases e with ⟨⟨i, j⟩, hij⟩
        dsimp
        simp [hij] }

  have gnp_graph_weight_eq_prod : ∀ G : SimpleGraph (Fin m),
      GnpGraphWeight p G = ∏ x : GnpEdge, if (gnpGraphBoolEquiv G x) then p else 1 - p := by
    intro G
    unfold GnpGraphWeight
    let pred : Fin m × Fin m → Prop := fun x => x.1.val < x.2.val
    let f : Fin m × Fin m → ℝ := fun x => if G.Adj x.1 x.2 then p else 1 - p
    have hprod : ((Finset.univ.filter pred).prod f) = ∏ x : GnpEdge, f x.1 := by
      apply Finset.prod_subtype (s := Finset.univ.filter pred) (p := fun x => x.1.val < x.2.val)
      intro x
      simp [pred]
    simpa [gnpGraphBoolEquiv, GnpEdge, f] using hprod

  let cylinderReq : GnpEdge → Prop := fun e =>
    (e.1.1 = r ∧ e.1.2 ∈ S) ∨ (e.1.1 ∈ S ∧ e.1.2 = r) ∨
    (e.1.1 = s ∧ e.1.2 ∈ S) ∨ (e.1.1 ∈ S ∧ e.1.2 = s)

  have cylinderReq_iff : ∀ G : SimpleGraph (Fin m),
      (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) ↔ (∀ x : GnpEdge, cylinderReq x → gnpGraphBoolEquiv G x = true) := by
    intro G
    constructor
    · intro h x hx
      simp only [gnpGraphBoolEquiv, Equiv.coe_fn_mk, decide_eq_true_eq]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; exact (h _ h2).1
      · subst h2; exact G.symm (h _ h1).1
      · subst h1; exact (h _ h2).2
      · subst h2; exact G.symm (h _ h1).2
    · intro h t ht
      constructor
      · by_cases hrt : r.val < t.val
        · have := h ⟨(r, t), hrt⟩ (Or.inl ⟨rfl, ht⟩)
          simpa [gnpGraphBoolEquiv] using this
        · have htr : t.val < r.val := by
            have hne : r ≠ t := by rintro rfl; exact hr ht
            omega
          have := h ⟨(t, r), htr⟩ (Or.inr (Or.inl ⟨ht, rfl⟩))
          simpa [gnpGraphBoolEquiv, SimpleGraph.adj_comm] using this
      · by_cases hst : s.val < t.val
        · have := h ⟨(s, t), hst⟩ (Or.inr (Or.inr (Or.inl ⟨rfl, ht⟩)))
          simpa [gnpGraphBoolEquiv] using this
        · have hts : t.val < s.val := by
            have hne : s ≠ t := by rintro rfl; exact hs ht
            omega
          have := h ⟨(t, s), hts⟩ (Or.inr (Or.inr (Or.inr ⟨ht, rfl⟩)))
          simpa [gnpGraphBoolEquiv, SimpleGraph.adj_comm] using this

  have filter_cylinderReq_card :
      (Finset.univ.filter (fun e : GnpEdge => cylinderReq e)).card = 2 * S.card := by
    let P := fun p : Fin m × Fin m => p.1.val < p.2.val ∧
      ((p.1 = r ∧ p.2 ∈ S) ∨ (p.1 ∈ S ∧ p.2 = r) ∨ (p.1 = s ∧ p.2 ∈ S) ∨ (p.1 ∈ S ∧ p.2 = s))
    let E_pairs := Finset.univ.filter P
    have h_card : (Finset.univ.filter (fun e : GnpEdge => cylinderReq e)).card = E_pairs.card := by
      have : (Finset.univ.filter (fun e : GnpEdge => cylinderReq e)).image Subtype.val = E_pairs := by
        ext p
        simp only [E_pairs, cylinderReq, P, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨⟨p1, p2⟩, hlt⟩, hreq, heq⟩
          dsimp at heq
          subst heq
          exact ⟨hlt, hreq⟩
        · rintro ⟨hlt, hreq⟩
          use ⟨p, hlt⟩
      rw [← this, Finset.card_image_of_injective _ Subtype.val_injective]

    let E_r := Finset.univ.filter (fun p : Fin m × Fin m => p.1.val < p.2.val ∧ ((p.1 = r ∧ p.2 ∈ S) ∨ (p.1 ∈ S ∧ p.2 = r)))
    let E_s := Finset.univ.filter (fun p : Fin m × Fin m => p.1.val < p.2.val ∧ ((p.1 = s ∧ p.2 ∈ S) ∨ (p.1 ∈ S ∧ p.2 = s)))

    have hd : Disjoint E_r E_s := by
      rw [Finset.disjoint_filter]
      rintro p _ h_r h_s
      rcases h_r.2 with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
      · rcases h_s.2 with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
        · subst hr1 hs1; exact hrs rfl
        · subst hr1 hs2; exact hr hs1
      · rcases h_s.2 with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
        · subst hr2 hs1; exact hs hr1
        · subst hr2 hs2; exact hrs rfl

    have h_union : E_pairs = E_r ∪ E_s := by
      ext p
      simp only [E_pairs, P, E_r, E_s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto

    let f_r : Fin m → Fin m × Fin m := fun t => if r.val < t.val then (r, t) else (t, r)
    have hinj_r : ∀ x ∈ S, ∀ y ∈ S, f_r x = f_r y → x = y := by
      intro x hx y hy hxy
      dsimp [f_r] at hxy
      split_ifs at hxy with h1 h2 h3
      · exact congrArg Prod.snd hxy
      · have : r = y := congrArg Prod.fst hxy; subst y; exact (hr hy).elim
      · have : x = r := congrArg Prod.fst hxy; subst x; exact (hr hx).elim
      · exact congrArg Prod.fst hxy
    have heq_img_r : E_r = S.image f_r := by
      ext p
      simp only [E_r, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hlt, ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩⟩
        · use p.2, hp2
          dsimp [f_r]; rw [if_pos (by rw [←hp1]; exact hlt)]
          ext <;> simp [hp1]
        · use p.1, hp1
          dsimp [f_r]; rw [if_neg (by rw [←hp2]; exact asymm hlt)]
          ext <;> simp [hp2]
      · rintro ⟨t, ht, ht_eq⟩
        dsimp [f_r] at ht_eq
        split_ifs at ht_eq with h1
        · subst ht_eq; refine ⟨h1, Or.inl ⟨rfl, ht⟩⟩
        · subst ht_eq
          have h_lt : t.val < r.val := by
            have hne : t ≠ r := by rintro rfl; exact hr ht
            have hne2 : t.val ≠ r.val := fun eq => hne (Fin.ext eq)
            have h_not : ¬(r.val < t.val) := h1
            omega
          refine ⟨by exact h_lt, Or.inr ⟨ht, rfl⟩⟩

    have hc_r : E_r.card = S.card := by
      rw [heq_img_r, Finset.card_image_of_injOn hinj_r]

    let f_s : Fin m → Fin m × Fin m := fun t => if s.val < t.val then (s, t) else (t, s)
    have hinj_s : ∀ x ∈ S, ∀ y ∈ S, f_s x = f_s y → x = y := by
      intro x hx y hy hxy
      dsimp [f_s] at hxy
      split_ifs at hxy with h1 h2 h3
      · exact congrArg Prod.snd hxy
      · have : s = y := congrArg Prod.fst hxy; subst y; exact (hs hy).elim
      · have : x = s := congrArg Prod.fst hxy; subst x; exact (hs hx).elim
      · exact congrArg Prod.fst hxy
    have heq_img_s : E_s = S.image f_s := by
      ext p
      simp only [E_s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hlt, ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩⟩
        · use p.2, hp2
          dsimp [f_s]; rw [if_pos (by rw [←hp1]; exact hlt)]
          ext <;> simp [hp1]
        · use p.1, hp1
          dsimp [f_s]; rw [if_neg (by rw [←hp2]; exact asymm hlt)]
          ext <;> simp [hp2]
      · rintro ⟨t, ht, ht_eq⟩
        dsimp [f_s] at ht_eq
        split_ifs at ht_eq with h1
        · subst ht_eq; refine ⟨h1, Or.inl ⟨rfl, ht⟩⟩
        · subst ht_eq
          have h_lt : t.val < s.val := by
            have hne : t ≠ s := by rintro rfl; exact hs ht
            have hne2 : t.val ≠ s.val := fun eq => hne (Fin.ext eq)
            have h_not : ¬(s.val < t.val) := h1
            omega
          refine ⟨by exact h_lt, Or.inr ⟨ht, rfl⟩⟩

    have hc_s : E_s.card = S.card := by
      rw [heq_img_s, Finset.card_image_of_injOn hinj_s]

    rw [h_card, h_union, Finset.card_union_of_disjoint hd, hc_r, hc_s, two_mul]

  let q_S : (GnpEdge → Bool) → ℝ := fun f =>
    if (∀ x : GnpEdge, cylinderReq x → f x = true)
    then ∏ x : GnpEdge, if f x then p else 1 - p
    else 0

  have h_eq : ∀ G, (if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0) = q_S (gnpGraphBoolEquiv G) := by
    intro G
    unfold q_S
    by_cases h : ∀ t ∈ S, G.Adj r t ∧ G.Adj s t
    · rw [if_pos h]
      have h2 : ∀ x : GnpEdge, cylinderReq x → gnpGraphBoolEquiv G x = true := (cylinderReq_iff G).mp h
      rw [if_pos h2]
      exact gnp_graph_weight_eq_prod G
    · rw [if_neg h]
      have h2 : ¬(∀ x : GnpEdge, cylinderReq x → gnpGraphBoolEquiv G x = true) := mt (cylinderReq_iff G).mpr h
      rw [if_neg h2]

  calc
    (∑ G : SimpleGraph (Fin m),
      if (∀ t ∈ S, G.Adj r t ∧ G.Adj s t) then GnpGraphWeight p G else 0)
    _ = ∑ G : SimpleGraph (Fin m), q_S (gnpGraphBoolEquiv G) := Finset.sum_congr rfl (fun G _ => h_eq G)
    _ = ∑ f : GnpEdge → Bool, q_S f := gnpGraphBoolEquiv.sum_comp _
    _ = ∑ f ∈ Fintype.piFinset (fun _ : GnpEdge => (Finset.univ : Finset Bool)),
          ∏ x : GnpEdge, (if cylinderReq x → f x = true then if f x then p else 1 - p else 0) := by
      rw [Fintype.piFinset_univ]
      apply Finset.sum_congr rfl
      intro f _
      unfold q_S
      by_cases h : ∀ x, cylinderReq x → f x = true
      · rw [if_pos h]
        apply Finset.prod_congr rfl
        intro x _
        have hx : cylinderReq x → f x = true := h x
        rw [if_pos hx]
      · rw [if_neg h]
        have hnot : ∃ x, ¬(cylinderReq x → f x = true) := by simpa using h
        rcases hnot with ⟨x, hx⟩
        have : ∏ x_1 : GnpEdge, (if cylinderReq x_1 → f x_1 = true then if f x_1 = true then p else 1 - p else 0) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ x)
          rw [if_neg hx]
        rw [this]
    _ = ∏ x : GnpEdge,
          ∑ b ∈ (Finset.univ : Finset Bool),
            if (cylinderReq x → b = true)
            then (if b = true then p else 1 - p)
            else 0 := by
      exact Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun x b => if cylinderReq x → b = true then if b = true then p else 1 - p else 0)
    _ = ∏ x : GnpEdge,
          if cylinderReq x then p else 1 := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : cylinderReq x
      · have : (∑ b ∈ (Finset.univ : Finset Bool),
            if (cylinderReq x → b = true)
            then (if b = true then p else 1 - p)
            else 0) = p := by
          have hdec : Decidable (cylinderReq x) := Classical.dec _
          rw [Fintype.sum_bool]
          simp [hx]
        rw [this, if_pos hx]
      · have : (∑ b ∈ (Finset.univ : Finset Bool),
            if (cylinderReq x → b = true)
            then (if b = true then p else 1 - p)
            else 0) = 1 := by
          have hdec : Decidable (cylinderReq x) := Classical.dec _
          rw [Fintype.sum_bool]
          simp [hx]
        rw [this, if_neg hx]
    _ = p ^ (Finset.univ.filter (fun e => cylinderReq e)).card := by
      have : (∏ x : GnpEdge, if cylinderReq x then p else 1) = ∏ x ∈ Finset.univ.filter (fun e => cylinderReq e), p := by
        exact (Finset.prod_filter cylinderReq (fun _ => p)).symm
      rw [this, Finset.prod_const]
    _ = p ^ (2 * S.card) := by
      rw [filter_cylinderReq_card]
    _ = (p^2) ^ S.card := by
      rw [pow_mul]
