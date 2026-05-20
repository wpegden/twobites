import Tablet.Preamble

-- [TABLET NODE: FixedSetFakeGraph]

/--
\begin{definition}[Fixed-Set Fake Graph]
For $m_{sub}\in\mathbb N$, a finite set
$P\subseteq\mathrm{Fin}(m_{sub})$, and a family of finite sets
$A:\mathrm{Fin}(m_{sub})\to\mathcal P(\mathrm{Fin}(m_{sub}))$,
$\mathrm{FixedSetFakeGraph}(P,A)$ is the simple graph on
$\mathrm{Fin}(m_{sub})$ with adjacency relation
\[
x\sim y \Longleftrightarrow
(x\in P,\ y\notin P,\ x\in A(y))\ \text{or}\
(y\in P,\ x\notin P,\ y\in A(x)).
\]
\end{definition}
-/
noncomputable def FixedSetFakeGraph {m_sub : ℕ} (P : Finset (Fin m_sub)) (A : Fin m_sub → Finset (Fin m_sub)) : SimpleGraph (Fin m_sub) :=
-- BODY
  SimpleGraph.mk
    (fun x y => (x ∈ P ∧ y ∉ P ∧ x ∈ A y) ∨ (y ∈ P ∧ x ∉ P ∧ y ∈ A x))
    (fun x y h => by
      cases h with
      | inl h1 => exact Or.inr h1
      | inr h2 => exact Or.inl h2)
    ⟨fun x h => by
      cases h with
      | inl h1 => exact h1.2.1 h1.1
      | inr h2 => exact h2.2.1 h2.1⟩
