import Tablet.GnpGraphWeight
import Tablet.ProductWeightSumOne
import Mathlib.Tactic

open Classical

-- [TABLET NODE: GnpVertexIncidentEdgeGeneratingFunction]

theorem GnpVertexIncidentEdgeGeneratingFunction (m : ℕ) (p z : ℝ) (r : Fin m) :
    (∑ G : SimpleGraph (Fin m),
      (∏ e : {e : Fin m × Fin m // e.1.val < e.2.val},
        if e.1.1 = r ∨ e.1.2 = r then
          if G.Adj e.1.1 e.1.2 then z else 1
        else 1) *
      GnpGraphWeight p G) =
    (1 - p + p * z) ^
      ((Finset.univ.filter
        (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
          e.1.1 = r ∨ e.1.2 = r)).card) := by
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
      GnpGraphWeight p G =
        ∏ x : GnpEdge, if (gnpGraphBoolEquiv G x) then p else 1 - p := by
    intro G
    unfold GnpGraphWeight
    let pred : Fin m × Fin m → Prop := fun x => x.1.val < x.2.val
    let f : Fin m × Fin m → ℝ := fun x => if G.Adj x.1 x.2 then p else 1 - p
    have hprod :
        ((Finset.univ.filter pred).prod f) = ∏ x : GnpEdge, f x.1 := by
      apply Finset.prod_subtype
        (s := Finset.univ.filter pred)
        (p := fun x => x.1.val < x.2.val)
      intro x
      simp [pred]
    simpa [gnpGraphBoolEquiv, GnpEdge, f] using hprod

  let incidentReq : GnpEdge → Prop := fun e => e.1.1 = r ∨ e.1.2 = r
  let q : (GnpEdge → Bool) → ℝ := fun f =>
    (∏ x : GnpEdge,
      if incidentReq x then
        if f x then z else 1
      else 1) *
    (∏ x : GnpEdge, if f x then p else 1 - p)

  have h_eq : ∀ G : SimpleGraph (Fin m),
      ((∏ e : GnpEdge,
        if e.1.1 = r ∨ e.1.2 = r then
          if G.Adj e.1.1 e.1.2 then z else 1
        else 1) *
      GnpGraphWeight p G) =
        q (gnpGraphBoolEquiv G) := by
    intro G
    unfold q incidentReq
    rw [gnp_graph_weight_eq_prod G]
    congr 1
    apply Finset.prod_congr rfl
    intro x _
    simp [gnpGraphBoolEquiv]

  calc
    (∑ G : SimpleGraph (Fin m),
      (∏ e : GnpEdge,
        if e.1.1 = r ∨ e.1.2 = r then
          if G.Adj e.1.1 e.1.2 then z else 1
        else 1) *
      GnpGraphWeight p G)
        = ∑ G : SimpleGraph (Fin m), q (gnpGraphBoolEquiv G) := by
          exact Finset.sum_congr rfl (fun G _ => h_eq G)
    _ = ∑ f : GnpEdge → Bool, q f := by
          exact gnpGraphBoolEquiv.sum_comp q
    _ = ∑ f ∈ Fintype.piFinset (fun _ : GnpEdge => (Finset.univ : Finset Bool)),
          ∏ x : GnpEdge,
            ((if incidentReq x then
                if f x then z else 1
              else 1) *
            (if f x then p else 1 - p)) := by
          rw [Fintype.piFinset_univ]
          apply Finset.sum_congr rfl
          intro f _
          unfold q
          rw [← Finset.prod_mul_distrib]
    _ = ∏ x : GnpEdge,
          ∑ b ∈ (Finset.univ : Finset Bool),
            ((if incidentReq x then
                if b then z else 1
              else 1) *
            (if b then p else 1 - p)) := by
          exact
            Finset.sum_prod_piFinset
              (Finset.univ : Finset Bool)
              (fun x b =>
                ((if incidentReq x then
                    if b then z else 1
                  else 1) *
                (if b then p else 1 - p)))
    _ = ∏ x : GnpEdge, if incidentReq x then 1 - p + p * z else 1 := by
          apply Finset.prod_congr rfl
          intro x _
          by_cases hx : incidentReq x
          · have :
                (∑ b ∈ (Finset.univ : Finset Bool),
                  ((if incidentReq x then
                      if b then z else 1
                    else 1) *
                  (if b then p else 1 - p))) =
                1 - p + p * z := by
              rw [Fintype.sum_bool]
              simp [hx]
              ring
            rw [this, if_pos hx]
          · have :
                (∑ b ∈ (Finset.univ : Finset Bool),
                  ((if incidentReq x then
                      if b then z else 1
                    else 1) *
                  (if b then p else 1 - p))) = 1 := by
              rw [Fintype.sum_bool]
              simp [hx]
            rw [this, if_neg hx]
    _ = (1 - p + p * z) ^
        ((Finset.univ.filter (fun e : GnpEdge => incidentReq e)).card) := by
          have :
              (∏ x : GnpEdge, if incidentReq x then 1 - p + p * z else 1) =
                ∏ x ∈ Finset.univ.filter (fun e : GnpEdge => incidentReq e),
                  (1 - p + p * z) := by
            exact (Finset.prod_filter incidentReq (fun _ => 1 - p + p * z)).symm
          rw [this, Finset.prod_const]
