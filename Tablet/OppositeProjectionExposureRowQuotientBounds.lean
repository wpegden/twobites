import Tablet.OppositeProjectionRowInjectionCounting

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureRowQuotientBounds]

theorem OppositeProjectionExposureRowQuotientBounds (n m : ℕ)
    (U₀ V₀ T : Finset (Fin n)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    let S := Finset.univ.image η
    let R := fun i : Fin m => Finset.filter (fun v : Fin n => ρ v = i) Finset.univ
    let rowAll := fun i : Fin m =>
      (Finset.univ.filter (fun f : ({v : Fin n // v ∈ R i} → Fin m) =>
        Function.Injective f ∧
          ∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u)).card
    let rowGood := fun i : Fin m =>
      (Finset.univ.filter (fun f : ({v : Fin n // v ∈ R i} → Fin m) =>
        Function.Injective f ∧
          (∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u) ∧
          ∀ v : {v : Fin n // v ∈ R i}, (v.1 : Fin n) ∈ T → f v ∈ S)).card
    T ⊆ V₀ →
    (∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v) →
    (∀ i : Fin m, (rowAll i : ℝ) ≠ 0) →
    (∀ i : Fin m, 0 ≤ (rowGood i : ℝ) / (rowAll i : ℝ)) ∧
    (∀ i : Fin m,
      (rowGood i : ℝ) / (rowAll i : ℝ) ≤ ((S.card : ℝ) / (m : ℝ)) ^
        ((T ∩ R i).card)) := by
-- BODY
  intro S R rowAll rowGood hT hrows h_row_ne
  constructor
  · intro i
    have hden_nonneg : 0 ≤ (rowAll i : ℝ) := by positivity
    have hden_pos : 0 < (rowAll i : ℝ) :=
      lt_of_le_of_ne hden_nonneg (Ne.symm (h_row_ne i))
    exact div_nonneg (by positivity) (le_of_lt hden_pos)
  · intro i
    by_cases h_empty_card : (T ∩ R i).card = 0
    · have h_empty_set : T ∩ R i = ∅ := Finset.card_eq_zero.mp h_empty_card
      have h_same : rowGood i = rowAll i := by
        dsimp [rowGood, rowAll]
        apply congrArg Finset.card
        ext f
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hf
          exact ⟨hf.1, hf.2.1⟩
        · intro hf
          refine ⟨hf.1, hf.2, ?_⟩
          intro v hvT
          have hvInt : (v.1 : Fin n) ∈ T ∩ R i :=
            Finset.mem_inter.mpr ⟨hvT, v.2⟩
          have hvEmpty : (v.1 : Fin n) ∈ (∅ : Finset (Fin n)) := by
            simpa [h_empty_set] using hvInt
          exact False.elim (by simpa using hvEmpty)
      have hquot : (rowGood i : ℝ) / (rowAll i : ℝ) = 1 := by
        rw [h_same]
        exact div_self (h_row_ne i)
      rw [hquot, h_empty_card]
      simp
    · have h_nonempty : (T ∩ R i).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h_empty_card)
      rcases h_nonempty with ⟨v₀, hv₀⟩
      have hv₀T : v₀ ∈ T := (Finset.mem_inter.mp hv₀).1
      have hv₀R : v₀ ∈ R i := (Finset.mem_inter.mp hv₀).2
      have hv₀V : v₀ ∈ V₀ := hT hv₀T
      have hv₀ρ : ρ v₀ = i := by
        have hv : v₀ ∈ Finset.filter (fun v : Fin n => ρ v = i) Finset.univ := by
          simpa [R] using hv₀R
        exact (Finset.mem_filter.mp hv).2
      have h_no_u : ∀ u : U₀, ¬ ((u.1 : Fin n) ∈ R i) := by
        intro u huR
        have hu : (u.1 : Fin n) ∈
            Finset.filter (fun v : Fin n => ρ v = i) Finset.univ := by
          simpa [R] using huR
        have huρ : ρ u.1 = i := (Finset.mem_filter.mp hu).2
        have h_eq : ρ u.1 = ρ v₀ := by rw [huρ, hv₀ρ]
        exact (hrows u.1 u.2 v₀ hv₀V) h_eq
      let A := {v : Fin n // v ∈ R i}
      let B : Finset A := Finset.univ.filter (fun v : A => (v.1 : Fin n) ∈ T)
      let q := Fintype.card A
      let h := B.card
      have h_card_B : h = (T ∩ R i).card := by
        dsimp [h, B, A]
        change ((R i).attach.filter
            (fun v : {v : Fin n // v ∈ R i} => (v.1 : Fin n) ∈ T)).card =
          (T ∩ R i).card
        have hmap :
            Finset.map (Function.Embedding.subtype (fun v : Fin n => v ∈ R i))
                ((R i).attach.filter
                  (fun v : {v : Fin n // v ∈ R i} => (v.1 : Fin n) ∈ T)) =
              T ∩ R i := by
          ext x
          simp only [mem_map, mem_filter, mem_attach, true_and,
            Function.Embedding.coe_subtype, mem_inter]
          constructor
          · rintro ⟨y, hyT, rfl⟩
            exact ⟨hyT, y.2⟩
          · intro hx
            exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
        rw [← hmap, Finset.card_map]
      have h_le_q : h ≤ q := by
        dsimp [h, q]
        exact Finset.card_le_univ B
      have h_all_card : (rowAll i : ℝ) = (Nat.descFactorial m q : ℝ) := by
        have h_filter :
            rowAll i =
              (Finset.univ.filter
                (fun f : A → Fin m => Function.Injective f)).card := by
          dsimp [rowAll, A]
          apply congrArg Finset.card
          ext f
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · intro hf
            exact hf.1
          · intro hf
            refine ⟨hf, ?_⟩
            intro u huR
            exact False.elim ((h_no_u u) huR)
        have h_sub :
            (Finset.univ.filter
              (fun f : A → Fin m => Function.Injective f)).card =
              Fintype.card {f : A → Fin m // Function.Injective f} := by
          exact (Fintype.card_of_subtype _ (by intro x; simp)).symm
        have h_equiv :
            Fintype.card {f : A → Fin m // Function.Injective f} =
              Fintype.card (A ↪ Fin m) := by
          exact Fintype.card_congr
            ({ toFun := fun f => ⟨f.1, f.2⟩
               invFun := fun f => ⟨f, f.injective⟩
               left_inv := by
                intro f
                rfl
               right_inv := by
                intro f
                cases f
                rfl } :
              {f : A → Fin m // Function.Injective f} ≃ (A ↪ Fin m))
        rw [h_filter, h_sub, h_equiv]
        have h_emb := @Fintype.card_embedding_eq A (Fin m) _ _ _
        simp only [Fintype.card_fin] at h_emb
        rw [h_emb]
      have h_good_card :
          (rowGood i : ℝ) =
            (Nat.descFactorial S.card h : ℝ) *
              (Nat.descFactorial (m - h) (q - h) : ℝ) := by
        have h_filter :
            rowGood i =
              (Finset.univ.filter
                (fun f : A → Fin m =>
                  Function.Injective f ∧
                    ∀ v : A, (v.1 : Fin n) ∈ T → f v ∈ S)).card := by
          dsimp [rowGood, A]
          apply congrArg Finset.card
          ext f
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · intro hf
            exact ⟨hf.1, hf.2.2⟩
          · intro hf
            refine ⟨hf.1, ?_, hf.2⟩
            intro u huR
            exact False.elim ((h_no_u u) huR)
        have h_fun_sub :
            (Finset.univ.filter
              (fun f : A → Fin m =>
                Function.Injective f ∧
                  ∀ v : A, (v.1 : Fin n) ∈ T → f v ∈ S)).card =
              Fintype.card
                {f : A → Fin m //
                  Function.Injective f ∧
                    ∀ v : A, (v.1 : Fin n) ∈ T → f v ∈ S} := by
          exact (Fintype.card_of_subtype _ (by intro x; simp)).symm
        have h_emb_sub :
            (Finset.univ.filter
              (fun f : A ↪ Fin m => ∀ a ∈ B, f a ∈ S)).card =
              Fintype.card {f : A ↪ Fin m // ∀ a ∈ B, f a ∈ S} := by
          exact (Fintype.card_of_subtype _ (by intro x; simp)).symm
        have h_equiv :
            Fintype.card
                {f : A → Fin m //
                  Function.Injective f ∧
                    ∀ v : A, (v.1 : Fin n) ∈ T → f v ∈ S} =
              Fintype.card {f : A ↪ Fin m // ∀ a ∈ B, f a ∈ S} := by
          exact Fintype.card_congr
            ({ toFun := fun f =>
                ⟨⟨f.1, f.2.1⟩, by
                  intro a ha
                  have haT : (a.1 : Fin n) ∈ T := by
                    simpa [B] using ha
                  exact f.2.2 a haT⟩
               invFun := fun f =>
                ⟨f.1, ⟨f.1.injective, by
                  intro a haT
                  have haB : a ∈ B := by simp [B, haT]
                  exact f.2 a haB⟩⟩
               left_inv := by
                intro f
                rfl
               right_inv := by
                intro f
                cases f
                rfl } :
              {f : A → Fin m //
                Function.Injective f ∧
                  ∀ v : A, (v.1 : Fin n) ∈ T → f v ∈ S} ≃
                {f : A ↪ Fin m // ∀ a ∈ B, f a ∈ S})
        rw [h_filter, h_fun_sub, h_equiv]
        rw [← h_emb_sub]
        have h_rest := OppositeProjectionRowRestrictedCounting (A := A) (Y := Fin m) B S
        rw [h_rest]
        simp [q, h]
      have hq_le_m : q ≤ m := by
        have h_desc_ne : (Nat.descFactorial m q : ℝ) ≠ 0 := by
          rw [← h_all_card]
          exact h_row_ne i
        have h_desc_nat_ne : Nat.descFactorial m q ≠ 0 := by
          exact_mod_cast h_desc_ne
        by_contra hnot
        have hlt : m < q := Nat.lt_of_not_ge hnot
        exact h_desc_nat_ne (Nat.descFactorial_eq_zero_iff_lt.mpr hlt)
      have hS_le_m : S.card ≤ m := by
        calc
          S.card ≤ Fintype.card (Fin m) := Finset.card_le_univ S
          _ = m := Fintype.card_fin m
      have h_row_bound :
          (rowGood i : ℝ) / (rowAll i : ℝ) ≤
            ((S.card : ℝ) / (m : ℝ)) ^ h := by
        rw [h_good_card, h_all_card]
        by_cases h_cases : h ≤ S.card
        · have hr := OppositeProjectionRowFavorableRatio m S.card h q h_le_q hq_le_m h_cases
          have hb := OppositeProjectionFallingFactorialBound S.card m h hS_le_m h_cases
          rw [hr]
          exact hb
        · push Not at h_cases
          have hz := OppositeProjectionRowFavorableZero S.card h h_cases
          rw [hz]
          simp
          positivity
      simpa [h_card_B] using h_row_bound
