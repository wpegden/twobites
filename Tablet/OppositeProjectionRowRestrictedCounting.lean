import Tablet.Preamble
import Mathlib.Data.Fintype.CardEmbedding

open scoped Classical BigOperators
open Finset

-- [TABLET NODE: OppositeProjectionRowRestrictedCounting]

theorem OppositeProjectionRowRestrictedCounting {A Y : Type*} [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (B : Finset A) (X : Finset Y) :
    (Finset.univ.filter (fun (f : A ↪ Y) => ∀ a ∈ B, f a ∈ X)).card =
      Nat.descFactorial X.card B.card * Nat.descFactorial (Fintype.card Y - B.card) (Fintype.card A - B.card) := by
-- BODY
  let s := Finset.univ.filter (fun (f : A ↪ Y) => ∀ a ∈ B, f a ∈ X)
  let t := Finset.univ.filter (fun (g : {a // a ∈ B} ↪ Y) => ∀ x, g x ∈ X)
  let f_proj : (A ↪ Y) → ({a // a ∈ B} ↪ Y) := fun f => (Function.Embedding.subtype _).trans f
  
  have Ht : t.card = Nat.descFactorial X.card B.card := by
    have e1 : {g : {a // a ∈ B} ↪ Y // ∀ x, g x ∈ X} ≃ ({a // a ∈ B} ↪ {y // y ∈ X}) := {
      toFun := fun ⟨g, hg⟩ => ⟨fun a => ⟨g a, hg a⟩, fun a₁ a₂ heq => g.injective (congrArg Subtype.val heq)⟩
      invFun := fun g => ⟨(g.trans (Function.Embedding.subtype _)), fun a => (g a).2⟩
      left_inv := fun ⟨g, hg⟩ => Subtype.ext (Function.Embedding.ext fun a => rfl)
      right_inv := fun g => Function.Embedding.ext fun a => Subtype.ext rfl
    }
    have eq_t : t.card = Fintype.card {g : {a // a ∈ B} ↪ Y // ∀ x, g x ∈ X} := by
      exact (Fintype.card_of_subtype t (by intro x; simp [t])).symm
    rw [eq_t, Fintype.card_congr e1, Fintype.card_embedding_eq]
    have hX : Fintype.card {y // y ∈ X} = X.card := Fintype.card_of_subtype X (by intro x; simp)
    have hB : Fintype.card {a // a ∈ B} = B.card := Fintype.card_of_subtype B (by intro x; simp)
    rw [hX, hB]
    
  have Hf : ∀ g ∈ t, (s.filter (fun f => f_proj f = g)).card = Nat.descFactorial (Fintype.card Y - B.card) (Fintype.card A - B.card) := by
    intro g hg
    let fiberEquiv : {f : A ↪ Y // (Function.Embedding.subtype (fun a => a ∈ B)).trans f = g} ≃ ({a // a ∉ B} ↪ {y // y ∉ Finset.image (fun a => g a) Finset.univ}) := {
      toFun := fun ⟨f, hf⟩ =>
        ⟨fun a => ⟨f a.1, by
          intro h_mem
          rw [Finset.mem_image] at h_mem
          rcases h_mem with ⟨w, _, hw⟩
          have : f a.1 = g w := hw.symm
          have hf_g : f w.1 = g w := by
            have : f w.1 = ((Function.Embedding.subtype _).trans f) w := rfl
            rw [this, hf]
          rw [← hf_g] at this
          have heq := f.injective this
          have hwB := w.2
          rw [← heq] at hwB
          exact a.2 hwB⟩,
        fun a₁ a₂ heq => Subtype.ext (f.injective (congrArg Subtype.val heq))⟩
      invFun := fun h =>
        ⟨⟨fun a => if ha : a ∈ B then g ⟨a, ha⟩ else h ⟨a, ha⟩, by
          intro a₁ a₂ heq
          by_cases ha₁ : a₁ ∈ B <;> by_cases ha₂ : a₂ ∈ B
          · simp only [dif_pos ha₁, dif_pos ha₂] at heq
            exact congrArg Subtype.val (g.injective heq)
          · simp only [dif_pos ha₁, dif_neg ha₂] at heq
            have h2 := (h ⟨a₂, ha₂⟩).2
            have : (h ⟨a₂, ha₂⟩).val ∈ Finset.image (fun a => g a) Finset.univ := by
              rw [← heq]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            contradiction
          · simp only [dif_neg ha₁, dif_pos ha₂] at heq
            have h2 := (h ⟨a₁, ha₁⟩).2
            have : (h ⟨a₁, ha₁⟩).val ∈ Finset.image (fun a => g a) Finset.univ := by
              rw [heq]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            contradiction
          · simp only [dif_neg ha₁, dif_neg ha₂] at heq
            exact congrArg Subtype.val (h.injective (Subtype.ext heq))⟩,
        by
          ext a
          dsimp
          rw [dif_pos a.2]⟩
      left_inv := fun ⟨f, hf⟩ => Subtype.ext (Function.Embedding.ext fun a => by
        dsimp
        by_cases ha : a ∈ B
        · rw [dif_pos ha]
          have : f a = ((Function.Embedding.subtype _).trans f) ⟨a, ha⟩ := rfl
          rw [this, hf]
        · exact dif_neg ha)
      right_inv := fun h => Function.Embedding.ext fun a => Subtype.ext (by
        dsimp
        exact dif_neg a.2)
    }

    have e_card : (s.filter (fun f => f_proj f = g)).card = Fintype.card {f : A ↪ Y // f_proj f = g} := by
      have sub_eq : (s.filter (fun f => f_proj f = g)) = Finset.univ.filter (fun f => f_proj f = g) := by
        ext f
        simp only [s, mem_filter, mem_univ, true_and, f_proj]
        constructor
        · intro h
          exact h.2
        · intro heq
          have h1 : ∀ a ∈ B, f a ∈ X := by
            intro a ha
            have eq1 : f a = ((Function.Embedding.subtype _).trans f) ⟨a, ha⟩ := rfl
            rw [eq1, heq]
            simp only [t, mem_filter, mem_univ, true_and] at hg
            exact hg ⟨a, ha⟩
          exact ⟨h1, heq⟩
      rw [sub_eq]
      exact (Fintype.card_of_subtype _ (by intro x; simp)).symm
    rw [e_card, Fintype.card_congr fiberEquiv, Fintype.card_embedding_eq]
    have h_dom : Fintype.card {a // a ∉ B} = Fintype.card A - B.card := by
      have : Fintype.card A = Fintype.card {a // a ∈ B} + Fintype.card {a // a ∉ B} := by
        rw [← Fintype.card_sum]
        exact Fintype.card_congr (Equiv.sumCompl (fun a => a ∈ B)).symm
      have hB : Fintype.card {a // a ∈ B} = B.card := Fintype.card_of_subtype B (by intro x; simp)
      omega
    have h_codom : Fintype.card {y // y ∉ Finset.image (fun a => g a) Finset.univ} = Fintype.card Y - B.card := by
      have : Fintype.card Y = Fintype.card {y // y ∈ Finset.image (fun a => g a) Finset.univ} + Fintype.card {y // y ∉ Finset.image (fun a => g a) Finset.univ} := by
        rw [← Fintype.card_sum]
        exact Fintype.card_congr (Equiv.sumCompl (fun y => y ∈ Finset.image (fun a => g a) Finset.univ)).symm
      have h_img : Fintype.card {y // y ∈ Finset.image (fun a => g a) Finset.univ} = B.card := by
        have h1 : Fintype.card {y // y ∈ Finset.image (fun a => g a) Finset.univ} = (Finset.image (fun a => g a) Finset.univ).card := Fintype.card_of_subtype _ (by intro x; simp)
        have h2 : (Finset.image (fun a => g a) Finset.univ).card = (Finset.univ : Finset {a // a ∈ B}).card := Finset.card_image_of_injective _ g.injective
        have hB : (Finset.univ : Finset {a // a ∈ B}).card = B.card := by
          have h3 : Fintype.card {a // a ∈ B} = B.card := Fintype.card_of_subtype B (by intro x; simp)
          exact h3
        rw [h1, h2, hB]
      omega
    rw [h_dom, h_codom]

  have Himg : ∀ a ∈ s, f_proj a ∈ t := by
    intro a ha
    simp only [s, mem_filter, mem_univ, true_and] at ha
    simp only [t, mem_filter, mem_univ, true_and, f_proj]
    intro x
    exact ha x.1 x.2

  calc (Finset.univ.filter (fun (f : A ↪ Y) => ∀ a ∈ B, f a ∈ X)).card
    _ = s.card := rfl
    _ = t.card * Nat.descFactorial (Fintype.card Y - B.card) (Fintype.card A - B.card) := by
      have eq_sum : ∑ b ∈ t, (s.filter (fun a => f_proj a = b)).card = t.card * Nat.descFactorial (Fintype.card Y - B.card) (Fintype.card A - B.card) := Finset.sum_const_nat Hf
      have eq1 := sum_card_fiberwise_eq_card_filter s t f_proj
      have eq_s : s.filter (fun a => f_proj a ∈ t) = s := filter_true_of_mem Himg
      rw [eq_s] at eq1
      rw [← eq1, eq_sum]
    _ = Nat.descFactorial X.card B.card * Nat.descFactorial (Fintype.card Y - B.card) (Fintype.card A - B.card) := by rw [Ht]
