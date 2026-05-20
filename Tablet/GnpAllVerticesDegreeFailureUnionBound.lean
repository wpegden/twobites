import Tablet.GnpVertexDegreeUpperTailUnionBound
import Tablet.WithinRelativeError
import Mathlib.Tactic

open Classical

-- [TABLET NODE: GnpAllVerticesDegreeFailureUnionBound]

theorem GnpAllVerticesDegreeFailureUnionBound (m : ℕ) (p ε t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (∑ G : SimpleGraph (Fin m),
      if ¬ ∀ v : Fin m,
          WithinRelativeError ε (p * (m : ℝ)) (GraphDegreeCount G v : ℝ)
      then GnpGraphWeight p G else 0) ≤
    (m : ℝ) *
      (Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          (1 - p + p * Real.exp t) ^ (m - 1) +
        Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          (1 - p + p * Real.exp (-t)) ^ (m - 1)) := by
-- BODY
  classical
  let upperCommon : ℝ :=
    Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
      (1 - p + p * Real.exp t) ^ (m - 1)
  let lowerCommon : ℝ :=
    Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
      (1 - p + p * Real.exp (-t)) ^ (m - 1)
  have hIncidentCard :
      ∀ r : Fin m,
        (Finset.univ.filter
          (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
            e.1.1 = r ∨ e.1.2 = r)).card = m - 1 := by
    intro r
    let E := {e : Fin m × Fin m // e.1.val < e.2.val}
    let incident : E → Prop := fun e => e.1.1 = r ∨ e.1.2 = r
    let s : Finset (Fin m) := Finset.univ.erase r
    let tt : Finset E := Finset.univ.filter incident
    have hcard' : s.card = tt.card := by
      apply Finset.card_bij
        (i := fun w hw =>
          if h : r.val < w.val then
            (⟨(r, w), h⟩ : E)
          else
            (⟨(w, r), by
              have hwne : w ≠ r := (Finset.mem_erase.mp hw).1
              have hvalne : r.val ≠ w.val := by
                intro hval
                exact hwne (Fin.ext hval).symm
              have hle : w.val ≤ r.val := Nat.le_of_not_gt h
              exact lt_of_le_of_ne hle hvalne.symm⟩ : E))
      · intro w hw
        by_cases h : r.val < w.val
        · simp [tt, incident, h]
        · simp [tt, incident, h]
      · intro w1 hw1 w2 hw2 heq
        by_cases h1 : r.val < w1.val
        · by_cases h2 : r.val < w2.val
          · simpa [h1, h2] using congrArg (fun e : E => e.1.2) heq
          · have hp : (r, w1) = (w2, r) := by
              simpa [h1, h2] using congrArg Subtype.val heq
            have hw1r : w1 = r := congrArg Prod.snd hp
            have hw1ne : w1 ≠ r := (Finset.mem_erase.mp hw1).1
            exact (hw1ne hw1r).elim
        · by_cases h2 : r.val < w2.val
          · have hp : (w1, r) = (r, w2) := by
              simpa [h1, h2] using congrArg Subtype.val heq
            have hw2r : w2 = r := (congrArg Prod.snd hp).symm
            have hw2ne : w2 ≠ r := (Finset.mem_erase.mp hw2).1
            exact (hw2ne hw2r).elim
          · simpa [h1, h2] using congrArg (fun e : E => e.1.1) heq
      · intro e he
        rcases e with ⟨⟨a, b⟩, hab⟩
        simp only [tt, incident, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ha | hb
        · subst a
          refine ⟨b, ?_, ?_⟩
          · simp [s]
            intro hbr
            subst b
            simp at hab
          · have hlt : r.val < b.val := hab
            simp [hlt]
        · subst b
          refine ⟨a, ?_, ?_⟩
          · simp [s]
            intro har
            subst a
            simp at hab
          · have hnlt : ¬ r.val < a.val := not_lt.mpr (Nat.le_of_lt hab)
            apply Subtype.ext
            simp [hnlt]
    have hs : s.card = m - 1 := by
      simp [s]
    rw [← hcard', hs]
  have hW : ∀ G : SimpleGraph (Fin m), 0 ≤ GnpGraphWeight p G := by
    intro G
    unfold GnpGraphWeight
    apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact hp0
    · linarith
  have hsplit :
      ∀ (G : SimpleGraph (Fin m)) (v : Fin m),
        ¬ WithinRelativeError ε (p * (m : ℝ)) (GraphDegreeCount G v : ℝ) →
          (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) ∨
          (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) := by
    intro G v hfail
    unfold WithinRelativeError at hfail
    have hlt : ε * (p * (m : ℝ)) <
        |(GraphDegreeCount G v : ℝ) - p * (m : ℝ)| := not_le.mp hfail
    by_cases hnonneg : 0 ≤ (GraphDegreeCount G v : ℝ) - p * (m : ℝ)
    · have hpos : ε * (p * (m : ℝ)) <
          (GraphDegreeCount G v : ℝ) - p * (m : ℝ) := by
        simpa [abs_of_nonneg hnonneg] using hlt
      left
      nlinarith
    · have hneg : (GraphDegreeCount G v : ℝ) - p * (m : ℝ) < 0 :=
        lt_of_not_ge hnonneg
      have hlow : ε * (p * (m : ℝ)) <
          -((GraphDegreeCount G v : ℝ) - p * (m : ℝ)) := by
        simpa [abs_of_neg hneg] using hlt
      right
      nlinarith
  have hpoint :
      (∑ G : SimpleGraph (Fin m),
        if ¬ ∀ v : Fin m,
            WithinRelativeError ε (p * (m : ℝ)) (GraphDegreeCount G v : ℝ)
        then GnpGraphWeight p G else 0) ≤
      ∑ G : SimpleGraph (Fin m),
        ∑ v : Fin m,
          ((if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
              GnpGraphWeight p G else 0) +
            (if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
              GnpGraphWeight p G else 0)) := by
    apply Finset.sum_le_sum
    intro G _
    by_cases hbad : ¬ ∀ v : Fin m,
        WithinRelativeError ε (p * (m : ℝ)) (GraphDegreeCount G v : ℝ)
    · rw [if_pos hbad]
      rcases not_forall.mp hbad with ⟨v, hvbad⟩
      have hvsplit := hsplit G v hvbad
      have hnonneg_terms :
          ∀ x ∈ (Finset.univ : Finset (Fin m)),
            0 ≤
              ((if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G x : ℝ) then
                  GnpGraphWeight p G else 0) +
                (if (GraphDegreeCount G x : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
                  GnpGraphWeight p G else 0)) := by
        intro x _
        apply add_nonneg
        · split_ifs
          · exact hW G
          · rfl
        · split_ifs
          · exact hW G
          · rfl
      have hvle :
          GnpGraphWeight p G ≤
            ((if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
                GnpGraphWeight p G else 0) +
              (if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
                GnpGraphWeight p G else 0)) := by
        rcases hvsplit with hupper | hlower
        · rw [if_pos hupper]
          exact le_add_of_nonneg_right (by split_ifs <;> first | exact hW G | rfl)
        · rw [if_pos hlower]
          exact le_add_of_nonneg_left (by split_ifs <;> first | exact hW G | rfl)
      exact le_trans hvle
        (Finset.single_le_sum hnonneg_terms (Finset.mem_univ v))
    · rw [if_neg hbad]
      apply Finset.sum_nonneg
      intro v _
      apply add_nonneg
      · split_ifs
        · exact hW G
        · rfl
      · split_ifs
        · exact hW G
        · rfl
  have hsum_rearrange :
      (∑ G : SimpleGraph (Fin m),
        ∑ v : Fin m,
          ((if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
              GnpGraphWeight p G else 0) +
            (if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
              GnpGraphWeight p G else 0))) =
      ∑ v : Fin m,
        ((∑ G : SimpleGraph (Fin m),
          if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
            GnpGraphWeight p G else 0) +
        (∑ G : SimpleGraph (Fin m),
          if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
            GnpGraphWeight p G else 0)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_add_distrib]
  have htails :
      ∀ v : Fin m,
        ((∑ G : SimpleGraph (Fin m),
          if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
            GnpGraphWeight p G else 0) +
        (∑ G : SimpleGraph (Fin m),
          if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
            GnpGraphWeight p G else 0)) ≤ upperCommon + lowerCommon := by
    intro v
    have hfixed := GnpVertexDegreeUpperTailUnionBound m p ε t v hp0 hp1 ht
    have hcard :
        (Finset.univ.filter
          (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
            e.1.1 = v ∨ e.1.2 = v)).card = m - 1 := hIncidentCard v
    have hu :
        (∑ G : SimpleGraph (Fin m),
          if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
            GnpGraphWeight p G else 0) ≤ upperCommon := by
      simpa [upperCommon, hcard] using hfixed.1
    have hl :
        (∑ G : SimpleGraph (Fin m),
          if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
            GnpGraphWeight p G else 0) ≤ lowerCommon := by
      simpa [lowerCommon, hcard] using hfixed.2
    exact add_le_add hu hl
  calc
    (∑ G : SimpleGraph (Fin m),
      if ¬ ∀ v : Fin m,
          WithinRelativeError ε (p * (m : ℝ)) (GraphDegreeCount G v : ℝ)
      then GnpGraphWeight p G else 0)
      ≤ ∑ G : SimpleGraph (Fin m),
        ∑ v : Fin m,
          ((if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
              GnpGraphWeight p G else 0) +
            (if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
              GnpGraphWeight p G else 0)) := hpoint
    _ = ∑ v : Fin m,
        ((∑ G : SimpleGraph (Fin m),
          if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G v : ℝ) then
            GnpGraphWeight p G else 0) +
        (∑ G : SimpleGraph (Fin m),
          if (GraphDegreeCount G v : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
            GnpGraphWeight p G else 0)) := hsum_rearrange
    _ ≤ ∑ v : Fin m, (upperCommon + lowerCommon) := by
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin m)))
          (fun v _ => htails v))
    _ = (Fintype.card (Fin m) : ℕ) • (upperCommon + lowerCommon) := by
      rw [Finset.sum_const, Finset.card_univ]
    _ = (m : ℝ) * (upperCommon + lowerCommon) := by
      simp [Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = (m : ℝ) *
      (Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
          (1 - p + p * Real.exp t) ^ (m - 1) +
        Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
          (1 - p + p * Real.exp (-t)) ^ (m - 1)) := by
      rfl
