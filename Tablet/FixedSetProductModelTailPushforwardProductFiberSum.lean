import Tablet.Preamble
import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelMass
import Mathlib.Data.Fintype.BigOperators

-- [TABLET NODE: FixedSetProductModelTailPushforwardProductFiberSum]

open scoped Classical BigOperators

set_option maxHeartbeats 1000000 in
theorem FixedSetProductModelTailPushforwardProductFiberSum {n : ℕ} (I : Finset (Fin n))
    {m_sub : ℕ} (p_sub : ℝ) (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1)
    (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (H : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) → Prop) :
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let D_v : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun v =>
      (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1,
       fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2)
    let valid_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : Prop :=
      (∀ x ∈ P_R, D.1 x = ∅) ∧ (∀ x ∉ P_R, D.1 x ⊆ P_R) ∧
      (∀ y ∈ P_B, D.2 y = ∅) ∧ (∀ y ∉ P_B, D.2 y ⊆ P_B)
    let ν_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : ℝ :=
      (∏ x ∈ Finset.univ \ P_R, p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card)) *
      (∏ y ∈ Finset.univ \ P_B, p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card))
    (Finset.univ.filter (fun v => H (D_v v))).sum (fun v => Finset.univ.prod (fun i => q (v i)))
    = (Finset.univ.filter (fun D => valid_D D ∧ H D)).sum ν_D := by
-- BODY
  intro P_R P_B q D_v valid_D ν_D
  classical
  let α := Finset (Fin m_sub) × Finset (Fin m_sub)
  let Data := (Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))
  let redIdx : Fin m_sub → Fin (2 * m_sub) := fun x => ⟨x.val, by omega⟩
  let blueIdx : Fin m_sub → Fin (2 * m_sub) := fun y => ⟨y.val + m_sub, by omega⟩
  let weight : (Fin (2 * m_sub) → α) → ℝ :=
    fun v => Finset.univ.prod (fun i => q (v i))
  let fiberMass : Data → ℝ := fun D =>
    (Finset.univ.filter (fun v : Fin (2 * m_sub) → α => D_v v = D)).sum weight
  have h_sum_q : ∑ a : α, q a = 1 :=
    (FixedSetProductModelMass p_sub hp0 hp1 P_R P_B).2

  have h_firstCoord :
      ∀ R : Finset (Fin m_sub),
        (Finset.univ.sum (fun a : α => if a.1 = R then q a else 0))
          =
          if R ⊆ P_R then p_sub ^ R.card * (1 - p_sub) ^ (P_R.card - R.card) else 0 := by
    intro R
    by_cases hR : R ⊆ P_R
    · rw [if_pos hR]
      rw [Fintype.sum_prod_type]
      have h_outer :
          (∑ x : Finset (Fin m_sub),
              ∑ y : Finset (Fin m_sub), (if (x, y).1 = R then q (x, y) else 0)) =
            ∑ y : Finset (Fin m_sub), q (R, y) := by
        rw [Fintype.sum_eq_single R]
        · simp
        · intro x hx
          simp [hx]
      rw [h_outer]
      have h_support :
          ∀ y : Finset (Fin m_sub), y ∉ P_B.powerset → q (R, y) = 0 := by
        intro y hy
        change FixedSetProductModelMassFn p_sub P_R P_B (R, y) = 0
        unfold FixedSetProductModelMassFn
        rw [if_neg]
        intro h
        exact hy (by simpa using h.2)
      rw [← Finset.sum_subset (Finset.subset_univ P_B.powerset) (fun y _ hy => h_support y hy)]
      have h_eval :
          ∀ y ∈ P_B.powerset,
            q (R, y) =
              (p_sub ^ R.card * (1 - p_sub) ^ (P_R.card - R.card)) *
                (p_sub ^ y.card * (1 - p_sub) ^ (P_B.card - y.card)) := by
        intro y hy
        change FixedSetProductModelMassFn p_sub P_R P_B (R, y) = _
        unfold FixedSetProductModelMassFn
        rw [if_pos (by exact ⟨hR, by simpa using hy⟩)]
      rw [Finset.sum_congr rfl h_eval]
      rw [← Finset.mul_sum]
      have h_sum :
          (∑ y ∈ P_B.powerset,
            p_sub ^ y.card * (1 - p_sub) ^ (P_B.card - y.card)) = 1 := by
        rw [Finset.sum_powerset]
        have h_inner (j : ℕ) :
            ∑ A ∈ P_B.powersetCard j,
                p_sub ^ A.card * (1 - p_sub) ^ (P_B.card - A.card) =
              (P_B.card.choose j : ℝ) *
                (p_sub ^ j * (1 - p_sub) ^ (P_B.card - j)) := by
          have h_body :
              ∀ A ∈ P_B.powersetCard j,
                p_sub ^ A.card * (1 - p_sub) ^ (P_B.card - A.card) =
                  p_sub ^ j * (1 - p_sub) ^ (P_B.card - j) := by
            intro A hA
            rw [Finset.mem_powersetCard] at hA
            simp [hA.2]
          rw [Finset.sum_congr rfl h_body]
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        simp_rw [h_inner]
        have h_match :
            (∑ j ∈ Finset.range (P_B.card + 1),
                (P_B.card.choose j : ℝ) *
                  (p_sub ^ j * (1 - p_sub) ^ (P_B.card - j))) =
              (∑ j ∈ Finset.range (P_B.card + 1),
                p_sub ^ j * (1 - p_sub) ^ (P_B.card - j) *
                  (P_B.card.choose j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm]
        rw [h_match]
        rw [← add_pow p_sub (1 - p_sub) P_B.card]
        simp
      rw [h_sum, mul_one]
    · rw [if_neg hR]
      apply Finset.sum_eq_zero
      intro a ha
      by_cases haR : a.1 = R
      · rw [if_pos haR]
        change FixedSetProductModelMassFn p_sub P_R P_B a = 0
        unfold FixedSetProductModelMassFn
        rw [if_neg]
        intro h
        exact hR (by simpa [← haR] using h.1)
      · rw [if_neg haR]

  have h_secondCoord :
      ∀ B : Finset (Fin m_sub),
        (Finset.univ.sum (fun a : α => if a.2 = B then q a else 0))
          =
          if B ⊆ P_B then p_sub ^ B.card * (1 - p_sub) ^ (P_B.card - B.card) else 0 := by
    intro B
    by_cases hB : B ⊆ P_B
    · rw [if_pos hB]
      rw [Fintype.sum_prod_type]
      have h_inner :
          (∑ x : Finset (Fin m_sub),
              ∑ y : Finset (Fin m_sub), (if (x, y).2 = B then q (x, y) else 0)) =
            ∑ x : Finset (Fin m_sub), q (x, B) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Fintype.sum_eq_single B]
        · simp
        · intro y hy
          simp [hy]
      rw [h_inner]
      have h_support :
          ∀ x : Finset (Fin m_sub), x ∉ P_R.powerset → q (x, B) = 0 := by
        intro x hx
        change FixedSetProductModelMassFn p_sub P_R P_B (x, B) = 0
        unfold FixedSetProductModelMassFn
        rw [if_neg]
        intro h
        exact hx (by simpa using h.1)
      rw [← Finset.sum_subset (Finset.subset_univ P_R.powerset) (fun x _ hx => h_support x hx)]
      have h_eval :
          ∀ x ∈ P_R.powerset,
            q (x, B) =
              (p_sub ^ x.card * (1 - p_sub) ^ (P_R.card - x.card)) *
                (p_sub ^ B.card * (1 - p_sub) ^ (P_B.card - B.card)) := by
        intro x hx
        change FixedSetProductModelMassFn p_sub P_R P_B (x, B) = _
        unfold FixedSetProductModelMassFn
        rw [if_pos (by exact ⟨by simpa using hx, hB⟩)]
      rw [Finset.sum_congr rfl h_eval]
      rw [← Finset.sum_mul]
      have h_sum :
          (∑ x ∈ P_R.powerset,
            p_sub ^ x.card * (1 - p_sub) ^ (P_R.card - x.card)) = 1 := by
        rw [Finset.sum_powerset]
        have h_inner (j : ℕ) :
            ∑ A ∈ P_R.powersetCard j,
                p_sub ^ A.card * (1 - p_sub) ^ (P_R.card - A.card) =
              (P_R.card.choose j : ℝ) *
                (p_sub ^ j * (1 - p_sub) ^ (P_R.card - j)) := by
          have h_body :
              ∀ A ∈ P_R.powersetCard j,
                p_sub ^ A.card * (1 - p_sub) ^ (P_R.card - A.card) =
                  p_sub ^ j * (1 - p_sub) ^ (P_R.card - j) := by
            intro A hA
            rw [Finset.mem_powersetCard] at hA
            simp [hA.2]
          rw [Finset.sum_congr rfl h_body]
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        simp_rw [h_inner]
        have h_match :
            (∑ j ∈ Finset.range (P_R.card + 1),
                (P_R.card.choose j : ℝ) *
                  (p_sub ^ j * (1 - p_sub) ^ (P_R.card - j))) =
              (∑ j ∈ Finset.range (P_R.card + 1),
                p_sub ^ j * (1 - p_sub) ^ (P_R.card - j) *
                  (P_R.card.choose j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm]
        rw [h_match]
        rw [← add_pow p_sub (1 - p_sub) P_R.card]
        simp
      rw [h_sum, one_mul]
    · rw [if_neg hB]
      apply Finset.sum_eq_zero
      intro a ha
      by_cases haB : a.2 = B
      · rw [if_pos haB]
        change FixedSetProductModelMassFn p_sub P_R P_B a = 0
        unfold FixedSetProductModelMassFn
        rw [if_neg]
        intro h
        exact hB (by simpa [← haB] using h.2)
      · rw [if_neg haB]

  have h_prod_outside :
      ∀ (P : Finset (Fin m_sub)) (F : Fin m_sub → ℝ),
        (∏ x : Fin m_sub, if x ∈ P then 1 else F x) =
          ∏ x ∈ Finset.univ \ P, F x := by
    intro P F
    calc
      (∏ x : Fin m_sub, if x ∈ P then 1 else F x)
          = (∏ x : Fin m_sub, if x ∉ P then F x else 1) := by
            apply Finset.prod_congr rfl
            intro x hx
            by_cases hxP : x ∈ P <;> simp [hxP]
      _ = ∏ x ∈ (Finset.univ.filter (fun x : Fin m_sub => x ∉ P)), F x := by
            rw [← Finset.prod_filter]
      _ = ∏ x ∈ Finset.univ \ P, F x := by
            congr 1
            ext x
            simp

  have h_prod_split :
      ∀ f : Fin (2 * m_sub) → ℝ,
        (∏ i : Fin (2 * m_sub), f i) =
          (∏ x : Fin m_sub, f (redIdx x)) *
            (∏ y : Fin m_sub, f (blueIdx y)) := by
    intro f
    let eIdx : Fin m_sub ⊕ Fin m_sub ≃ Fin (2 * m_sub) :=
      finSumFinEquiv.trans (finCongr (by omega))
    have hleft : ∀ x : Fin m_sub, eIdx (Sum.inl x) = redIdx x := by
      intro x
      apply Fin.ext
      simp [eIdx, redIdx, finSumFinEquiv_apply_left, Fin.castAdd]
    have hright : ∀ y : Fin m_sub, eIdx (Sum.inr y) = blueIdx y := by
      intro y
      apply Fin.ext
      simp [eIdx, blueIdx, finSumFinEquiv_apply_right, Fin.natAdd]
      omega
    calc
      (∏ i : Fin (2 * m_sub), f i)
          = ∏ s : Fin m_sub ⊕ Fin m_sub, f (eIdx s) := by
            exact (Equiv.prod_comp eIdx f).symm
      _ =
          (∏ x : Fin m_sub, f (eIdx (Sum.inl x))) *
            (∏ y : Fin m_sub, f (eIdx (Sum.inr y))) := by
            rw [Fintype.prod_sum_type]
      _ =
          (∏ x : Fin m_sub, f (redIdx x)) *
            (∏ y : Fin m_sub, f (blueIdx y)) := by
            have hL :
                (∏ x : Fin m_sub, f (eIdx (Sum.inl x))) =
                  ∏ x : Fin m_sub, f (redIdx x) := by
              apply Finset.prod_congr rfl
              intro x hx
              rw [hleft x]
            have hR :
                (∏ y : Fin m_sub, f (eIdx (Sum.inr y))) =
                  ∏ y : Fin m_sub, f (blueIdx y) := by
              apply Finset.prod_congr rfl
              intro y hy
              rw [hright y]
            rw [hL, hR]

  have h_fiberMass :
      ∀ D : Data, fiberMass D = if valid_D D then ν_D D else 0 := by
    intro D
    by_cases hDvalid : valid_D D
    · rw [if_pos hDvalid]
      let coord : Fin (2 * m_sub) → α → ℝ := fun i a =>
        if hi : i.val < m_sub then
          let x : Fin m_sub := ⟨i.val, hi⟩
          if x ∈ P_R then q a else if a.1 = D.1 x then q a else 0
        else
          let y : Fin m_sub := ⟨i.val - m_sub, by omega⟩
          if y ∈ P_B then q a else if a.2 = D.2 y then q a else 0
      have h_coord_red :
          ∀ (x : Fin m_sub) (a : α),
            coord (redIdx x) a =
              if x ∈ P_R then q a else if a.1 = D.1 x then q a else 0 := by
        intro x a
        have hlt : (redIdx x).val < m_sub := by
          dsimp [redIdx]
          exact x.isLt
        have hxrec : (⟨(redIdx x).val, hlt⟩ : Fin m_sub) = x := by
          apply Fin.ext
          rfl
        simp [coord, hlt, hxrec]
      have h_coord_blue :
          ∀ (y : Fin m_sub) (a : α),
            coord (blueIdx y) a =
              if y ∈ P_B then q a else if a.2 = D.2 y then q a else 0 := by
        intro y a
        have hnot : ¬ (blueIdx y).val < m_sub := by
          dsimp [blueIdx]
          omega
        have hyrec : (⟨(blueIdx y).val - m_sub, by omega⟩ : Fin m_sub) = y := by
          apply Fin.ext
          dsimp [blueIdx]
          omega
        simp [coord, hnot, hyrec]
      have h_point :
          ∀ v : Fin (2 * m_sub) → α,
            (if D_v v = D then weight v else 0) =
              Finset.univ.prod (fun i => coord i (v i)) := by
        intro v
        by_cases hvD : D_v v = D
        · rw [if_pos hvD]
          dsimp [weight]
          apply Finset.prod_congr rfl
          intro i hi_mem
          by_cases hred : i.val < m_sub
          · let x : Fin m_sub := ⟨i.val, hred⟩
            have hidx : redIdx x = i := by
              apply Fin.ext
              rfl
            by_cases hxP : x ∈ P_R
            · rw [← hidx, h_coord_red x (v (redIdx x))]
              simp [hxP]
            · have hx_eq : (v i).1 = D.1 x := by
                have hcomp := congrArg (fun E => E.1 x) hvD
                simpa [D_v, redIdx, hidx, hxP] using hcomp
              have hx_eq' : (v (redIdx x)).1 = D.1 x := by
                simpa [hidx] using hx_eq
              rw [← hidx, h_coord_red x (v (redIdx x))]
              simp [hxP, hx_eq']
          · let y : Fin m_sub := ⟨i.val - m_sub, by omega⟩
            have hidx : blueIdx y = i := by
              apply Fin.ext
              dsimp [blueIdx, y]
              omega
            by_cases hyP : y ∈ P_B
            · rw [← hidx, h_coord_blue y (v (blueIdx y))]
              simp [hyP]
            · have hy_eq : (v i).2 = D.2 y := by
                have hcomp := congrArg (fun E => E.2 y) hvD
                simpa [D_v, blueIdx, hidx, hyP] using hcomp
              have hy_eq' : (v (blueIdx y)).2 = D.2 y := by
                simpa [hidx] using hy_eq
              rw [← hidx, h_coord_blue y (v (blueIdx y))]
              simp [hyP, hy_eq']
        · rw [if_neg hvD]
          have hbad :
              (∃ x : Fin m_sub, x ∉ P_R ∧ (v (redIdx x)).1 ≠ D.1 x) ∨
                (∃ y : Fin m_sub, y ∉ P_B ∧ (v (blueIdx y)).2 ≠ D.2 y) := by
            by_contra hnone
            apply hvD
            have hredEq :
                ∀ x : Fin m_sub, x ∉ P_R → (v (redIdx x)).1 = D.1 x := by
              intro x hxP
              by_contra hxne
              exact hnone (Or.inl ⟨x, hxP, hxne⟩)
            have hblueEq :
                ∀ y : Fin m_sub, y ∉ P_B → (v (blueIdx y)).2 = D.2 y := by
              intro y hyP
              by_contra hyne
              exact hnone (Or.inr ⟨y, hyP, hyne⟩)
            apply Prod.ext
            · funext x
              by_cases hxP : x ∈ P_R
              · simp [D_v, hxP, hDvalid.1 x hxP]
              · simpa [D_v, redIdx, hxP] using (hredEq x hxP)
            · funext y
              by_cases hyP : y ∈ P_B
              · simp [D_v, hyP, hDvalid.2.2.1 y hyP]
              · simpa [D_v, blueIdx, hyP] using (hblueEq y hyP)
          rcases hbad with hbadR | hbadB
          · rcases hbadR with ⟨x, hxP, hxne⟩
            rw [Finset.prod_eq_zero (Finset.mem_univ (redIdx x))]
            rw [h_coord_red x (v (redIdx x))]
            simp [hxP, hxne]
          · rcases hbadB with ⟨y, hyP, hyne⟩
            rw [Finset.prod_eq_zero (Finset.mem_univ (blueIdx y))]
            rw [h_coord_blue y (v (blueIdx y))]
            simp [hyP, hyne]
      dsimp [fiberMass]
      rw [Finset.sum_filter]
      rw [Finset.sum_congr rfl (fun v _ => h_point v)]
      rw [← Fintype.prod_sum]
      rw [h_prod_split (fun i : Fin (2 * m_sub) => ∑ a : α, coord i a)]
      have h_red_sum :
          ∀ x : Fin m_sub,
            (∑ a : α, coord (redIdx x) a) =
              if x ∈ P_R then 1
              else p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card) := by
        intro x
        by_cases hxP : x ∈ P_R
        · rw [if_pos hxP]
          have h_eq : ∀ a : α, coord (redIdx x) a = q a := by
            intro a
            rw [h_coord_red x a]
            simp [hxP]
          rw [Finset.sum_congr rfl (fun a _ => h_eq a), h_sum_q]
        · rw [if_neg hxP]
          have h_eq :
              (∑ a : α, coord (redIdx x) a) =
                ∑ a : α, if a.1 = D.1 x then q a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [h_coord_red x a]
            simp [hxP]
          rw [h_eq, h_firstCoord (D.1 x), if_pos (hDvalid.2.1 x hxP)]
      have h_blue_sum :
          ∀ y : Fin m_sub,
            (∑ a : α, coord (blueIdx y) a) =
              if y ∈ P_B then 1
              else p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card) := by
        intro y
        by_cases hyP : y ∈ P_B
        · rw [if_pos hyP]
          have h_eq : ∀ a : α, coord (blueIdx y) a = q a := by
            intro a
            rw [h_coord_blue y a]
            simp [hyP]
          rw [Finset.sum_congr rfl (fun a _ => h_eq a), h_sum_q]
        · rw [if_neg hyP]
          have h_eq :
              (∑ a : α, coord (blueIdx y) a) =
                ∑ a : α, if a.2 = D.2 y then q a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [h_coord_blue y a]
            simp [hyP]
          rw [h_eq, h_secondCoord (D.2 y), if_pos (hDvalid.2.2.2 y hyP)]
      have h_red_prod :
          (∏ x : Fin m_sub, ∑ a : α, coord (redIdx x) a) =
            ∏ x ∈ Finset.univ \ P_R,
              p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card) := by
        rw [Finset.prod_congr rfl (fun x _ => h_red_sum x)]
        exact h_prod_outside P_R
          (fun x => p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card))
      have h_blue_prod :
          (∏ y : Fin m_sub, ∑ a : α, coord (blueIdx y) a) =
            ∏ y ∈ Finset.univ \ P_B,
              p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card) := by
        rw [Finset.prod_congr rfl (fun y _ => h_blue_sum y)]
        exact h_prod_outside P_B
          (fun y => p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card))
      rw [h_red_prod, h_blue_prod]
    · rw [if_neg hDvalid]
      dsimp [fiberMass]
      apply Finset.sum_eq_zero
      intro v hv_mem
      have hvD : D_v v = D := (Finset.mem_filter.mp hv_mem).2
      by_cases hRempty : ∀ x ∈ P_R, D.1 x = ∅
      · by_cases hRsub : ∀ x ∉ P_R, D.1 x ⊆ P_R
        · by_cases hBempty : ∀ y ∈ P_B, D.2 y = ∅
          · by_cases hBsub : ∀ y ∉ P_B, D.2 y ⊆ P_B
            · exact False.elim (hDvalid ⟨hRempty, hRsub, hBempty, hBsub⟩)
            · push Not at hBsub
              rcases hBsub with ⟨y, hyP, hynotSub⟩
              have hy_eq : (v (blueIdx y)).2 = D.2 y := by
                have hcomp := congrArg (fun E => E.2 y) hvD
                simpa [D_v, blueIdx, hyP] using hcomp
              apply Finset.prod_eq_zero (Finset.mem_univ (blueIdx y))
              change FixedSetProductModelMassFn p_sub P_R P_B (v (blueIdx y)) = 0
              unfold FixedSetProductModelMassFn
              rw [if_neg]
              intro h
              exact hynotSub (by simpa [← hy_eq] using h.2)
          · push Not at hBempty
            rcases hBempty with ⟨y, hyP, hyNonempty⟩
            have hyempty : D.2 y = ∅ := by
              have hcomp := congrArg (fun E => E.2 y) hvD
              simpa [D_v, hyP] using hcomp.symm
            exact False.elim (hyNonempty.ne_empty hyempty)
        · push Not at hRsub
          rcases hRsub with ⟨x, hxP, hxnotSub⟩
          have hx_eq : (v (redIdx x)).1 = D.1 x := by
            have hcomp := congrArg (fun E => E.1 x) hvD
            simpa [D_v, redIdx, hxP] using hcomp
          apply Finset.prod_eq_zero (Finset.mem_univ (redIdx x))
          change FixedSetProductModelMassFn p_sub P_R P_B (v (redIdx x)) = 0
          unfold FixedSetProductModelMassFn
          rw [if_neg]
          intro h
          exact hxnotSub (by simpa [← hx_eq] using h.1)
      · push Not at hRempty
        rcases hRempty with ⟨x, hxP, hxNonempty⟩
        have hxempty : D.1 x = ∅ := by
          have hcomp := congrArg (fun E => E.1 x) hvD
          simpa [D_v, hxP] using hcomp.symm
        exact False.elim (hxNonempty.ne_empty hxempty)

  have h_partition :
      (Finset.univ.filter (fun v : Fin (2 * m_sub) → α => H (D_v v))).sum weight =
        Finset.univ.sum (fun D : Data => if H D then fiberMass D else 0) := by
    rw [Finset.sum_filter]
    have h_fiber :=
      Finset.sum_fiberwise
        (s := (Finset.univ : Finset (Fin (2 * m_sub) → α)))
        (g := D_v)
        (f := fun v : Fin (2 * m_sub) → α => if H (D_v v) then weight v else 0)
    calc
      Finset.univ.sum
          (fun v : Fin (2 * m_sub) → α => if H (D_v v) then weight v else 0)
          =
        Finset.univ.sum
          (fun D : Data =>
            (Finset.univ.filter (fun v : Fin (2 * m_sub) → α => D_v v = D)).sum
              (fun v => if H (D_v v) then weight v else 0)) := by
          simpa [Data] using h_fiber.symm
      _ =
        Finset.univ.sum (fun D : Data => if H D then fiberMass D else 0) := by
          apply Finset.sum_congr rfl
          intro D hD
          by_cases hHD : H D
          · rw [if_pos hHD]
            dsimp [fiberMass]
            apply Finset.sum_congr rfl
            intro v hv
            have hvD : D_v v = D := (Finset.mem_filter.mp hv).2
            simp [hvD, hHD]
          · rw [if_neg hHD]
            apply Finset.sum_eq_zero
            intro v hv
            have hvD : D_v v = D := (Finset.mem_filter.mp hv).2
            simp [hvD, hHD]
  rw [h_partition]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  rw [h_fiberMass D]
  by_cases hHD : H D
  · by_cases hVD : valid_D D
    · simp [hHD, hVD, ν_D]
    · simp [hHD, hVD]
  · simp [hHD]
