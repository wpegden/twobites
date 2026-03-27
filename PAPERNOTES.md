# Paper Notes

## Scope
- Formalization scope for this project: the main-result material in Sections 2-4, together with the appendix inequalities actually used there.
- Section 5 on hypergraph Ramsey numbers is explicitly only a proof sketch and is out of scope for the current formalization project.

## Corrections And Clarifications
- Global small-`ε` reduction: the proof repeatedly assumes `0 < ε_2 << ε_1 << ε << 1` and later uses inequalities that require `ε` to be sufficiently small, for example `n^{4ε} k = o(k^2)`, `1 - 8ε > 0`, and `-1 + ε + 22ε^2 < 0`. To match Theorem `main` as stated for all `ε > 0`, the paper should explicitly say that it suffices to prove the result for sufficiently small `ε`, since the conclusion is monotone in `ε`.
- `reference.tex:331-334` (`lem:fiber_and_degree`): the proof is only sketched. For Lean planning, this should be split into routine concentration components: fiber size concentration, degree concentration in `G_R`/`G_B`, concentration of `|N_v|`, codegree bounds `|N_v ∩ N_w| = O(log^3 n)`, and projected codegree bounds. The projected codegree estimates use sampling without replacement in the blue/red coordinates.
- `reference.tex:421-422` (`lem:med`): the second bipartite graph should be on `(B_B, π_B(I))`, not `(B_B, π_R(I))`.
- `reference.tex:436` (`lem:med`): the final probability bound has the wrong event. The argument gives a bound by `P(\mathcal O \cup \mathcal D^c)`, not `P(\mathcal O^c \cup \mathcal D^c)`.
- `reference.tex:477-491` (`lem:small`): the McDiarmid step is valid, but only after making the independence mechanism explicit. For `v ∉ π_R(I) ∪ π_B(I)`, the variable `Y_v` depends only on edges between `v` and `π_R(I)` or `π_B(I)`; these edge sets are disjoint across different `v`, so the `Y_v` are independent.
- `reference.tex:557` (`lem:huge`): `N_3(v_1)` is undefined. The intended bound is `x_{v_1} ≤ |N_{v_1}| ≤ (1 + ε_2)pn`, or equivalently `|\pi_B(X_{v_1}(I))| ≤ (1 + ε_2)pn`.
- `reference.tex:578-580` (`lem:huge`): the expression `π(I) \setminus (\bigcup X_{v_i}(I))` is ill-typed because `π(I) ⊆ V_R × V_B` while `X_{v_i}(I) ⊆ V(G)`. The intended inequality is
  `|π_R(I)| ≤ |π_R(\bigcup X_{v_i}(I))| + |I \setminus \bigcup X_{v_i}(I)|`,
  which then yields `|\bigcup X_{v_i}(I)| ≤ k - |π_R(I)| + o(k)`.
- `reference.tex:533-580` (`lem:huge`): beyond the two corrections above, the manuscript keeps the huge-case union-size and projected-codegree losses only at qualitative `o(k)` scale. It never names explicit blue/red slack parameters for those two witness-error pieces. The Lean development therefore has to expose exact branchwise smallness hypotheses for those pieces instead of recovering a single canonical constant from the text. With only the displayed scale assumptions, one can formalize at best the coarse bounds `paperHugeWitnessDegreeBranchParam ≤ 3κ`, `paperHugeWitnessCodegBranchParam ≤ 3κ`, and hence `paperHugeWitnessBranchParam ≤ 6κ`; the genuinely small branch slacks needed by the final huge-case route require an extra large-`n` specialization that the manuscript leaves implicit. The union-size / degree part of that specialization is now explicit in Lean via `paperHugeWitnessDegreeBranchParam_eventually_le`; the projected-codegree part still has to be quantified separately.
- `reference.tex:639` (`lem:RISI`): `U_B` should be `T_B ∩ E(G_B)`, not `T_B ∩ E(G_R)`.
- `reference.tex:663` (`lem:RISI`): `T_I` should be `T_R ∪ T_B`, or the sentence should simply say that every unrevealed open pair lies in `T_R ∪ T_B` and must be a non-edge.
- `reference.tex:668-669` (`lem:RISI`): `f(\ell_r,\ell_B)` should be `f(\ell_R,\ell_B)`.
- `reference.tex:746` (proof of Theorem `main`): `P(B_I \cap \mathcal R)` should be `P(\mathcal B_I \cap \mathcal R)`.
- Main asymptotic check: after simplifying the exponent in the three cases of `lem:RI`, the coefficient is negative for sufficiently small `ε`; the delicate middle regime (`1 - ε/2 < x_R + x_B < 1 + ε/2`) was checked separately during this paper-check pass and did not reveal a gap.

## Open Questions
- No genuine gap found in the main-result proof chain.
