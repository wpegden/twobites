import Tablet.Preamble

-- [TABLET NODE: SumChooseBound]

lemma SumChooseBound {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (proj : α → β) (bound : ℝ)
    (h_bound : ∀ a ∈ I, ((I.filter (fun b => proj a = proj b)).card : ℝ) ≤ bound) :
    (((I.product I).filter (fun (e : α × α) => proj e.1 = proj e.2)).card : ℝ) ≤ I.card * bound := by
-- BODY
  have h_disj : (I : Set α).PairwiseDisjoint (fun a => (I.filter (fun b => proj a = proj b)).image (fun b => (a, b))) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro e he1 he2
    rw [Finset.mem_image] at he1 he2
    rcases he1 with ⟨x, _, hx_eq⟩
    rcases he2 with ⟨y, _, hy_eq⟩
    have h_eq : (a, x) = (b, y) := hx_eq.trans hy_eq.symm
    injection h_eq with h_eq_a _
    exact hab h_eq_a
  have h_eq : ((I.product I).filter (fun e => proj e.1 = proj e.2)) = I.biUnion (fun a => (I.filter (fun b => proj a = proj b)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp [and_assoc]
  have h1 : ((I.product I).filter (fun e => proj e.1 = proj e.2)).card = ∑ a ∈ I, (I.filter (fun b => proj a = proj b)).card := by
    rw [h_eq, Finset.card_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.card_image_of_injective
    intro x y hxy
    injection hxy
  calc
    (((I.product I).filter (fun (e : α × α) => proj e.1 = proj e.2)).card : ℝ) = ∑ a ∈ I, ((I.filter (fun b => proj a = proj b)).card : ℝ) := by exact_mod_cast h1
    _ ≤ ∑ a ∈ I, bound := Finset.sum_le_sum (fun a ha => h_bound a ha)
    _ = I.card * bound := by simp [mul_comm]
