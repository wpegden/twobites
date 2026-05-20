import Tablet.TwoBiteSample
import Tablet.TwoBiteEmbedding
import Tablet.FixedSetProductModelVar
import Tablet.FixedSetFakeGraph
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX

open scoped Classical

-- [TABLET NODE: FixedSetProductModelTailPushforwardAgreement]

theorem FixedSetProductModelTailPushforwardAgreement {n : ℕ} (I : Finset (Fin n)) (ε : ℝ)
    {m_sub : ℕ} (p_sub : ℝ)
    (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (H : ℝ → Prop) :
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    let Z_I : TwoBiteSample n m_sub p_sub → ℝ := fun ω => by
      classical
      exact
        let P_R := I.image (TwoBiteRedProjection ω)
        let P_B := I.image (TwoBiteBlueProjection ω)
        let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
        let S_I_ext := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ P_I
        let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
        let Z_pairs := ext_pairs.filter (fun e =>
          TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧
          TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
        (Z_pairs.card : ℝ)
    let D_ω : TwoBiteSample n m_sub p_sub → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun ω =>
      (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r),
       fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b))
    let D_v : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun v =>
      (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1,
       fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2)
    let H_D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) → Prop :=
      fun D => ∃ v, D_v v = D ∧ H (Z_prod v)
    (∀ ω, TwoBiteEmbedding ω = π → (H (Z_I ω) ↔ H_D (D_ω ω))) ∧
    (Finset.univ.filter (fun v => H (Z_prod v)) = Finset.univ.filter (fun v => H_D (D_v v))) := by
-- BODY
  intros P_R P_B Z_prod Z_I D_ω D_v H_D
  have hPR : P_R = I.image (fun u => (π u).1) := rfl
  have hPB : P_B = I.image (fun u => (π u).2) := rfl
  have hD_v_def : D_v = fun v =>
      (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1,
       fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2) := rfl
  have Z_prod_eq : ∀ (v v' : Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)), D_v v = D_v v' → Z_prod v = Z_prod v' := by
    intro v v' h_eq
    dsimp [Z_prod, FixedSetProductModelVar]
    have hR : (FixedSetFakeGraph (Finset.image (fun u => (π u).1) I) (fun i => (v ⟨i.val, by omega⟩).1)) =
              (FixedSetFakeGraph (Finset.image (fun u => (π u).1) I) (fun i => (v' ⟨i.val, by omega⟩).1)) := by
      rw [← hPR]
      apply SimpleGraph.ext
      ext x y
      dsimp [FixedSetFakeGraph, SimpleGraph.Adj]
      have h1 := congr_arg Prod.fst h_eq
      rw [hD_v_def] at h1
      dsimp at h1
      apply or_congr
      · apply and_congr_right; intro hx
        apply and_congr_right; intro hy
        have h1y := congr_fun h1 y
        simp only [if_neg hy] at h1y
        rw [h1y]
      · apply and_congr_right; intro hy
        apply and_congr_right; intro hx
        have h1x := congr_fun h1 x
        simp only [if_neg hx] at h1x
        rw [h1x]
    have hB : (FixedSetFakeGraph (Finset.image (fun u => (π u).2) I) (fun i => (v ⟨i.val + m_sub, by omega⟩).2)) =
              (FixedSetFakeGraph (Finset.image (fun u => (π u).2) I) (fun i => (v' ⟨i.val + m_sub, by omega⟩).2)) := by
      rw [← hPB]
      apply SimpleGraph.ext
      ext x y
      dsimp [FixedSetFakeGraph, SimpleGraph.Adj]
      have h1 := congr_arg Prod.snd h_eq
      rw [hD_v_def] at h1
      dsimp at h1
      apply or_congr
      · apply and_congr_right; intro hx
        apply and_congr_right; intro hy
        have h1y := congr_fun h1 y
        simp only [if_neg hy] at h1y
        rw [h1y]
      · apply and_congr_right; intro hy
        apply and_congr_right; intro hx
        have h1x := congr_fun h1 x
        simp only [if_neg hx] at h1x
        rw [h1x]
    rw [hR, hB]
  have Z_eq : ∀ (ω : TwoBiteSample n m_sub p_sub) (hπ : TwoBiteEmbedding ω = π) (v : Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)),
      (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1) = (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r)) →
      (fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2) = (fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b)) →
      Z_prod v = Z_I ω := by
    intro ω hπ v hD_R hD_B
    dsimp [Z_prod, FixedSetProductModelVar, Z_I]
    set ω_prod : TwoBiteSample n m_sub p_sub :=
      (FixedSetFakeGraph (I.image (fun u => (π u).1)) (fun i => (v ⟨i.val, by omega⟩).1),
       FixedSetFakeGraph (I.image (fun u => (π u).2)) (fun i => (v ⟨i.val + m_sub, by omega⟩).2),
       π)
    have h_P_R_def : P_R = I.image (fun u => (π u).1) := hPR
    have h_P_B_def : P_B = I.image (fun u => (π u).2) := hPB
    have hR_proj : ∀ u, TwoBiteRedProjection ω_prod u = TwoBiteRedProjection ω u := by
      intro u; change (π u).1 = (ω.2.2 u).1; have h_emb : ω.2.2 = π := hπ; rw [h_emb]
    have hB_proj : ∀ u, TwoBiteBlueProjection ω_prod u = TwoBiteBlueProjection ω u := by
      intro u; change (π u).2 = (ω.2.2 u).2; have h_emb : ω.2.2 = π := hπ; rw [h_emb]
    have hPR_eq : I.image (TwoBiteRedProjection ω_prod) = P_R := by
      rw [hPR]; apply Finset.image_congr; intro u _; rfl
    have hPB_eq : I.image (TwoBiteBlueProjection ω_prod) = P_B := by
      rw [hPB]; apply Finset.image_congr; intro u _; rfl
    have hX_R : ∀ x, x ∉ I.image (TwoBiteRedProjection ω_prod) →
        TwoBiteX ω_prod I (Sum.inl x) = TwoBiteX ω I (Sum.inl x) := by
      intro x hx
      dsimp [TwoBiteX, TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteBlueGraph]
      apply Finset.ext; intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply and_congr_right; intro hu
      change ω_prod.1.Adj x (TwoBiteRedProjection ω_prod u) ↔ ω.1.Adj x (TwoBiteRedProjection ω u)
      have huR : TwoBiteRedProjection ω_prod u ∈ P_R := by rw [← hPR_eq]; exact Finset.mem_image_of_mem _ hu
      have huR' : TwoBiteRedProjection ω u ∈ P_R := by rw [← hPR_eq, ← hR_proj u]; exact Finset.mem_image_of_mem _ hu
      have hD := congr_fun hD_R x
      split_ifs at hD with hx_in
      · rw [← hPR_eq] at hx_in; contradiction
      · have h_adj_prod : ω_prod.1.Adj x (TwoBiteRedProjection ω_prod u) ↔ TwoBiteRedProjection ω_prod u ∈ (v ⟨x.val, by omega⟩).1 := by
          dsimp [ω_prod, FixedSetFakeGraph, SimpleGraph.Adj]
          constructor
          · intro h_adj; rcases h_adj with h1 | h2; exfalso; exact hx_in (by rw [hPR]; exact h1.1); exact h2.2.2
          · intro h_in; apply Or.inr; exact ⟨by rw [← hPR]; exact huR, by rw [← hPR]; exact hx_in, h_in⟩
        have h_in_filter : TwoBiteRedProjection ω u ∈ P_R.filter (fun r => ω.1.Adj x r) ↔ ω.1.Adj x (TwoBiteRedProjection ω u) := by
          rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨huR', h⟩⟩
        have h_v_eq_filter : TwoBiteRedProjection ω_prod u ∈ (v ⟨x.val, by omega⟩).1 ↔ TwoBiteRedProjection ω u ∈ P_R.filter (fun r => ω.1.Adj x r) := by
          rw [hD, hR_proj u]
        exact Iff.trans h_adj_prod (Iff.trans h_v_eq_filter h_in_filter)
    have hX_B : ∀ y, y ∉ I.image (TwoBiteBlueProjection ω_prod) →
        TwoBiteX ω_prod I (Sum.inr y) = TwoBiteX ω I (Sum.inr y) := by
      intro y hy
      dsimp [TwoBiteX, TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteBlueGraph]
      apply Finset.ext; intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply and_congr_right; intro hu
      change ω_prod.2.1.Adj y (TwoBiteBlueProjection ω_prod u) ↔ ω.2.1.Adj y (TwoBiteBlueProjection ω u)
      have huB : TwoBiteBlueProjection ω_prod u ∈ P_B := by rw [← hPB_eq]; exact Finset.mem_image_of_mem _ hu
      have huB' : TwoBiteBlueProjection ω u ∈ P_B := by rw [← hPB_eq, ← hB_proj u]; exact Finset.mem_image_of_mem _ hu
      have hD := congr_fun hD_B y
      split_ifs at hD with hy_in
      · rw [← hPB_eq] at hy_in; contradiction
      · have h_adj_prod : ω_prod.2.1.Adj y (TwoBiteBlueProjection ω_prod u) ↔ TwoBiteBlueProjection ω_prod u ∈ (v ⟨y.val + m_sub, by omega⟩).2 := by
          dsimp [ω_prod, FixedSetFakeGraph, SimpleGraph.Adj]
          constructor
          · intro h_adj; rcases h_adj with h1 | h2; exfalso; exact hy_in (by rw [hPB]; exact h1.1); exact h2.2.2
          · intro h_in; apply Or.inr; exact ⟨by rw [← hPB]; exact huB, by rw [← hPB]; exact hy_in, h_in⟩
        have h_in_filter : TwoBiteBlueProjection ω u ∈ P_B.filter (fun b => ω.2.1.Adj y b) ↔ ω.2.1.Adj y (TwoBiteBlueProjection ω u) := by
          rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨huB', h⟩⟩
        have h_v_eq_filter : TwoBiteBlueProjection ω_prod u ∈ (v ⟨y.val + m_sub, by omega⟩).2 ↔ TwoBiteBlueProjection ω u ∈ P_B.filter (fun b => ω.2.1.Adj y b) := by
          rw [hD, hB_proj u]
        exact Iff.trans h_adj_prod (Iff.trans h_v_eq_filter h_in_filter)
    have hP_I_eq : (I.image (TwoBiteRedProjection ω_prod)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω_prod)).image Sum.inr =
                   (I.image (TwoBiteRedProjection ω)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω)).image Sum.inr := by
      congr 2
      · apply Finset.image_congr; intro u hu; exact hR_proj u
      · apply Finset.image_congr; intro u hu; exact hB_proj u
    have hX_all : ∀ z, z ∉ ((I.image (TwoBiteRedProjection ω)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω)).image Sum.inr) →
        TwoBiteX ω_prod I z = TwoBiteX ω I z := by
      intro z hz
      have hz_prod : z ∉ ((I.image (TwoBiteRedProjection ω_prod)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω_prod)).image Sum.inr) := by
        rw [hP_I_eq]; exact hz
      rw [Finset.mem_union, not_or] at hz_prod
      cases z with
      | inl x =>
        apply hX_R
        intro hx
        apply hz_prod.1
        apply Finset.mem_image_of_mem _ hx
      | inr y =>
        apply hX_B
        intro hy
        apply hz_prod.2
        apply Finset.mem_image_of_mem _ hy
    have hSmallClass_eq : (Finset.univ.filter (TwoBiteSmallClass ω_prod ε I)) \ ((I.image (TwoBiteRedProjection ω_prod)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω_prod)).image Sum.inr) =
                       (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ ((I.image (TwoBiteRedProjection ω)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω)).image Sum.inr) := by
      rw [hP_I_eq]
      apply Finset.ext
      intro z
      rw [Finset.mem_sdiff, Finset.mem_sdiff]
      apply and_congr_left
      intro hz
      rw [Finset.mem_filter, Finset.mem_filter]
      apply and_congr_right
      intro _
      dsimp [TwoBiteSmallClass]
      have hXz := hX_all z hz
      rw [hXz]
    have h_pairs_eq : ((Finset.univ.filter (TwoBiteSmallClass ω_prod ε I)) \ ((I.image (TwoBiteRedProjection ω_prod)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω_prod)).image Sum.inr)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω_prod I x)) =
                      ((Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ ((I.image (TwoBiteRedProjection ω)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω)).image Sum.inr)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x)) := by
      rw [hSmallClass_eq]
      apply Finset.ext
      intro e
      rw [Finset.mem_biUnion, Finset.mem_biUnion]
      apply exists_congr
      intro x
      apply and_congr_right
      intro hx
      rw [Finset.mem_sdiff] at hx
      have hXx := hX_all x hx.2
      rw [hXx]
    have hz_pairs_eq : (((Finset.univ.filter (TwoBiteSmallClass ω_prod ε I)) \ ((I.image (TwoBiteRedProjection ω_prod)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω_prod)).image Sum.inr)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω_prod I x))).filter (fun e => ¬ TwoBiteRedProjection ω_prod e.1 = TwoBiteRedProjection ω_prod e.2 ∧ ¬ TwoBiteBlueProjection ω_prod e.1 = TwoBiteBlueProjection ω_prod e.2) =
                      (((Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ ((I.image (TwoBiteRedProjection ω)).image Sum.inl ∪ (I.image (TwoBiteBlueProjection ω)).image Sum.inr)).biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))).filter (fun e => ¬ TwoBiteRedProjection ω e.1 = TwoBiteRedProjection ω e.2 ∧ ¬ TwoBiteBlueProjection ω e.1 = TwoBiteBlueProjection ω e.2) := by
      rw [h_pairs_eq]
      apply Finset.ext
      intro e
      rw [Finset.mem_filter, Finset.mem_filter]
      apply and_congr_right
      intro _
      have hr1 := hR_proj e.1
      have hr2 := hR_proj e.2
      have hb1 := hB_proj e.1
      have hb2 := hB_proj e.2
      rw [hr1, hr2, hb1, hb2]
    exact congrArg (fun S : Finset (Fin n × Fin n) => (S.card : ℝ)) hz_pairs_eq
  constructor
  · intro ω hω
    constructor
    · intro HZI
      set v_ω : Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub) := fun i =>
        if h : i.val < m_sub then
          let x : Fin m_sub := ⟨i.val, h⟩
          (if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r), ∅)
        else
          let y : Fin m_sub := ⟨i.val - m_sub, by omega⟩
          (∅, if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b))
      use v_ω
      have hD_eq : D_v v_ω = D_ω ω := by
        ext : 1
        · apply funext; intro a
          dsimp [D_v, D_ω, v_ω]
          have ha_lt : (a : ℕ) < m_sub := a.2
          rw [dif_pos ha_lt]
          split_ifs <;> rfl
        · apply funext; intro b
          dsimp [D_v, D_ω, v_ω]
          have hb_lt : ¬ ((b : ℕ) + m_sub) < m_sub := by omega
          rw [dif_neg hb_lt]
          have h_b_eq : (⟨(b : ℕ) + m_sub - m_sub, by omega⟩ : Fin m_sub) = b := by ext; dsimp; omega
          rw [h_b_eq]
          split_ifs <;> rfl
      constructor
      · exact hD_eq
      · have hD_v_eq_1 : (fun x => if x ∈ P_R then ∅ else (v_ω ⟨x.val, by omega⟩).1) = (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r)) := by
          ext x
          dsimp [v_ω]
          have hx_lt : (x : ℕ) < m_sub := x.2
          rw [dif_pos hx_lt]
          split_ifs <;> rfl
        have hD_v_eq_2 : (fun y => if y ∈ P_B then ∅ else (v_ω ⟨y.val + m_sub, by omega⟩).2) = (fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b)) := by
          ext y
          dsimp [v_ω]
          have hy_lt : ¬ ((y : ℕ) + m_sub) < m_sub := by omega
          rw [dif_neg hy_lt]
          have h_y_eq : (⟨(y : ℕ) + m_sub - m_sub, by omega⟩ : Fin m_sub) = y := by ext; dsimp; omega
          rw [h_y_eq]
          split_ifs <;> rfl
        have hz := Z_eq ω hω v_ω hD_v_eq_1 hD_v_eq_2
        exact hz.symm ▸ HZI
    · intro HH
      rcases HH with ⟨v, hv1, hv2⟩
      have hv_R : (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1) = (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r)) := by
        have h1 := congr_arg Prod.fst hv1
        exact h1
      have hv_B : (fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2) = (fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b)) := by
        have h1 := congr_arg Prod.snd hv1
        exact h1
      have hz := Z_eq ω hω v hv_R hv_B
      exact hz ▸ hv2
  · apply Finset.ext
    intro v
    rw [Finset.mem_filter, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro Hv
      exact ⟨v, rfl, Hv⟩
    · intro ⟨v', hv'1, hv'2⟩
      have hz := Z_prod_eq v v' hv'1.symm
      exact hz.symm ▸ hv'2
