import Tablet.Preamble

-- [TABLET NODE: FixedSetProductModelMassFn]

/--
\begin{definition}[Fixed-Set Product Model Mass]
Fix $M \in \mathbb N$, a probability $p_0 \in \mathbb R$, and subsets $P_R, P_B \subseteq \mathrm{Fin}(M)$.
For $a = (A_R, A_B) \in \mathcal P(\mathrm{Fin}(M)) \times \mathcal P(\mathrm{Fin}(M))$, define
\[
q(a) = p_0^{|A_R|}(1-p_0)^{|P_R|-|A_R|} p_0^{|A_B|}(1-p_0)^{|P_B|-|A_B|}
\]
if $A_R \subseteq P_R$ and $A_B \subseteq P_B$, and $q(a) = 0$ otherwise.
\end{definition}
-/
noncomputable def FixedSetProductModelMassFn {m_sub : ℕ} (p_sub : ℝ) (P_R P_B : Finset (Fin m_sub)) (a : Finset (Fin m_sub) × Finset (Fin m_sub)) : ℝ :=
-- BODY
  if a.1 ⊆ P_R ∧ a.2 ⊆ P_B then
    (p_sub ^ a.1.card * (1 - p_sub) ^ (P_R.card - a.1.card)) *
    (p_sub ^ a.2.card * (1 - p_sub) ^ (P_B.card - a.2.card))
  else 0
