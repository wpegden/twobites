import Tablet.GnpGraphWeight
import Tablet.ProductWeightSumOne

-- [TABLET NODE: GnpGraphWeightSumOne]

theorem GnpGraphWeightSumOne :
    ∀ (m : ℕ) (p : ℝ),
      Finset.univ.sum (fun G : SimpleGraph (Fin m) => GnpGraphWeight p G) = 1 := by
-- BODY
  intro m p
  classical
  let Edge := {e : Fin m × Fin m // e.1.val < e.2.val}
  let graphBoolEquiv :
      SimpleGraph (Fin m) ≃ (Edge → Bool) := by
    refine
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
        left_inv := ?_
        right_inv := ?_ }
    · intro G
      apply SimpleGraph.ext
      funext i j
      apply propext
      by_cases hij : i.val < j.val
      · simp [hij]
      · by_cases hji : j.val < i.val
        · simp [hij, hji, SimpleGraph.adj_comm]
        · have hij_eq : i = j := by
            apply Fin.ext
            omega
          subst j
          simp
    · intro f
      funext e
      rcases e with ⟨⟨i, j⟩, hij⟩
      dsimp
      simp [hij]
  let q : (Edge → Bool) → ℝ :=
    fun f => Finset.univ.prod (fun x : Edge => if f x then p else 1 - p)
  have hweight_eq :
      ∀ G : SimpleGraph (Fin m), GnpGraphWeight p G = q (graphBoolEquiv G) := by
    intro G
    unfold GnpGraphWeight
    let pred : Fin m × Fin m → Prop := fun x => x.1.val < x.2.val
    let f : Fin m × Fin m → ℝ :=
      fun x => if G.Adj x.1 x.2 then p else 1 - p
    have hprod :
        ((Finset.univ.filter pred).prod f) =
          Finset.univ.prod (fun x : Edge => f x.1) := by
      simpa [pred, Edge] using
        (Finset.prod_subtype (s := Finset.univ.filter pred)
          (h := by intro x; simp [pred]) f)
    simpa [q, graphBoolEquiv, Edge, pred, f] using hprod
  calc
    Finset.univ.sum (fun G : SimpleGraph (Fin m) => GnpGraphWeight p G)
        = Finset.univ.sum (fun G : SimpleGraph (Fin m) => q (graphBoolEquiv G)) := by
          exact Finset.sum_congr rfl (by intro G hG; exact hweight_eq G)
    _ = Finset.univ.sum (fun f : Edge → Bool => q f) := by
          exact graphBoolEquiv.sum_comp q
    _ = ∑ f ∈ Fintype.piFinset (fun _ : Edge => (Finset.univ : Finset Bool)),
          ∏ x : Edge, (if f x then p else 1 - p) := by
          rw [Fintype.piFinset_univ]
    _ = ∏ _x : Edge, ∑ b ∈ (Finset.univ : Finset Bool), (if b then p else 1 - p) := by
          simpa using
            (Finset.sum_prod_piFinset
              (s := (Finset.univ : Finset Bool))
              (g := fun _x : Edge => fun b : Bool => if b then p else 1 - p))
    _ = 1 := by
          simp
