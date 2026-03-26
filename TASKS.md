# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Prove the target statements presented in `PaperTheorems.lean`.
- [ ] Keep reusable proof infrastructure in separate support files when that yields a cleaner project structure.
- [ ] Maintain `TASKS.md` and `PLAN.md` as the proof frontier moves.
- [ ] Keep sorrys within the configured policy.
- [ ] Do not introduce unapproved axioms.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Finish the parameter-only Section 3 witness arithmetic in `repo/Twobites/ParameterBounds.lean` so the new `|I| \le \lceil k \rceil` witness wrappers in `repo/Twobites/IndependentSets.lean` specialize to the paper's deterministic `\varepsilon_1 k^2` bounds for `L_I`, `M_I`, and the diagonal `H_I` contributions.
- [ ] Finish the huge-case bookkeeping in `repo/Twobites/IndependentSets.lean` by replacing the current abstract `min`-bounds in terms of the union-error quantity with the paper's concrete `k-|\pi_R(I)|` / `k-|\pi_B(I)|` min-expression estimates for the cross-projection terms in Lemma `lem:huge`.
- [ ] Strengthen `repo/Twobites/ParameterBounds.lean` from the current threshold-order lemmas and the reduction lemma for `t_2 ≤ t_1` to an actual large-`n` proof of that comparison and the related asymptotic bounds used later in Sections 3-4.
- [ ] Connect the new `finalGraph.CliqueFree 3` theorem and the part-restricted closed-pair bookkeeping to the eventual independence-number proofs in `repo/PaperTheorems.lean`.

## Completed
- [x] Add the abstract huge-case `min`-expression bounds in `repo/Twobites/IndependentSets.lean`: the red/blue cross-projection pair counts now satisfy `min { choose(total), choose(cap) + choose(total - cap) }` bounds once supplied with a per-vertex cap, a lower bound placing the cap below the total weight, and the existing projection-union-plus-intersection-error estimate.
- [x] Add the capped-sum convexity theorem in `repo/Twobites/IndependentSets.lean`: if each term is at most a cap and the total exceeds that cap, then `sum choose 2` is bounded by `choose cap + choose (total - cap)`, with projection-specialized corollaries for the red/blue huge cross-projection sums.
- [x] Add the convexity/choose-of-total-weight step for the huge-case projection sums in `repo/Twobites/IndependentSets.lean`: `partPairCount`, `redProjectionPairCount`, and `blueProjectionPairCount` are now bounded by `choose` of their total weights, and the red/blue huge cross-projection sides already reduce under `GoodEventD` to `choose` of the new projection-union-plus-intersection-error quantities.
- [x] Add paper-facing deterministic aliases in `repo/Twobites/IndependentSets.lean` for the current Section 3 support results: `paper_large_deterministic`, `paper_medium_deterministic`, `paper_huge_red_diagonal_deterministic`, and `paper_huge_blue_diagonal_deterministic` now package the `GoodEventD` bounds with the new `|I| \le \lceil k \rceil` witness arithmetic interface.
- [x] Extend the huge-case projection bookkeeping in `repo/Twobites/IndependentSets.lean` with `redProjectionUnion` / `blueProjectionUnion` and the corresponding union-plus-pairwise-intersection bounds, including the `GoodEventD` specializations for `H_I \cap V_R` and `H_I \cap V_B` that start the cross-projection argument behind Lemma `lem:huge`.
- [x] Add `|I| \le \lceil k \rceil` witness wrappers in `repo/Twobites/IndependentSets.lean`: the large, medium, and diagonal huge `GoodEventD` lemmas now accept a parameter-only witness inequality on `\lceil k \rceil` and package direct `\varepsilon_1 k^2` conclusions once the remaining Section 3 arithmetic bounds are supplied.
- [x] Add the first witness-inequality-to-contribution lemmas in `repo/Twobites/IndependentSets.lean`: `GoodEventD` now gives large/medium and diagonal-huge bounds once a Section 3 witness-size inequality is supplied, plus the filter-cardinality helper lemmas needed for `H_I ∩ V_R` and `H_I ∩ V_B`.
- [x] Extend `repo/Twobites/ParameterBounds.lean` with ceiling-level threshold arithmetic (`ceil_paperT1_le_paperKNat`, `ceil_paperT2_le_paperKNat`, `ceil_paperT3_le_ceil_paperT2`, `ceil_paperT2_le_ceil_paperT1_of_loglog_le`) so the new witness/cardinality lemmas have the right natural-number interfaces.
- [x] Add the witness-subset/cardinality infrastructure in `repo/Twobites/IndependentSets.lean`: lower-bound the `partWeight` of a family from a natural lower bound on every `|X_v(I)|`, extract fixed-size witness subsets with `Finset.exists_subset_card_eq`, and deduce `L_I`, `M_I`, and `H_I` cardinality bounds from `GoodEventD` once the corresponding threshold inequalities are supplied.
- [x] Clean the current `repo/Twobites/IndependentSets.lean` linter warnings while extending the `GoodEventD` machinery.
- [x] Encode the deterministic good event `𝒟` in `repo/Twobites/IndependentSets.lean` as `GoodEventD`, and derive from it the inherited `X_v(I)` codegree bounds, projected codegree bounds, and `partWeight` / projection-weight upper bounds needed by the counting lemmas.
- [x] Turn the earlier explicit-hypothesis wrappers into actual deterministic support lemmas in `repo/Twobites/IndependentSets.lean`: `GoodEventD` now yields raw large/medium/small contribution bounds and the diagonal huge red/blue contribution bounds on `H_I ∩ V_R` and `H_I ∩ V_B`.
- [x] Add the first paper-style contribution wrappers under explicit weight hypotheses: large/medium/small `partPairCount` bounds and huge red/blue projection-pair bounds in `repo/Twobites/IndependentSets.lean`.
- [x] Isolate the remaining analytic comparison for `t_2 ≤ t_1` in `repo/Twobites/ParameterBounds.lean` as a reusable reduction lemma from a log-log growth hypothesis.
- [x] Add the partition-usage lemmas in `repo/Twobites/IndependentSets.lean`: every base vertex falls into one of `H_I/L_I/M_I/S_I`, the adjacent regimes are disjoint unconditionally, and the remaining disjointness statements are isolated behind the threshold-order hypotheses they need.
- [x] Add the first huge-regime projection contribution bounds in `repo/Twobites/IndependentSets.lean` via `redProjectionPairCount`, `blueProjectionPairCount`, and their `|I|/2` upper bounds in terms of projection weights.
- [x] Add the first actual deterministic counting lemmas in `repo/Twobites/IndependentSets.lean`: `partWeight`, `partPairCount`, projection-weight sums, and `choose 2` upper bounds specialized to `H_I`, `L_I`, `M_I`, and `S_I`.
- [x] Strengthen `repo/Twobites/ParameterBounds.lean` with the first concrete threshold-order inequalities, including `t_3 ≤ t_2` and explicit bounds placing `t_1` and `t_2` below `k` under large-`n` / small-`ε` hypotheses.
- [x] Upgrade the local deletion lemmas in `repo/Twobites/Construction.lean` into triangle-free / `CliqueFree 3` theorems for `retainedRed`, `retainedBlue`, and `finalGraph`.
- [x] Extend `repo/Twobites/IndependentSets.lean` to the paper's `H_I`, `L_I`, `M_I`, `S_I` partition, projected-image bookkeeping, and restricted `ClosedPairOn` / `ClosedPairPlusOn` predicates.
- [x] Extend `repo/Twobites/ParameterBounds.lean` with the paper's Section 3 thresholds `t_1`, `t_2`, `t_3` and their basic positivity lemmas.
- [x] Prove the first deterministic deletion lemmas in `repo/Twobites/Construction.lean`: deleted edges cannot survive retained color layers, and the later edge of a monochromatic triangle cannot survive in `finalGraph`.
- [x] Start `repo/Twobites/IndependentSets.lean` with the paper's `X_v(I)`, `X_v^+(I)`, closed/open pair predicates, and witness-to-closed-pair lemmas.
- [x] Extend `repo/Twobites/Construction.lean` through the paper's triangle-deletion bookkeeping: ordered coordinate pairs, monochromatic and mixed deletion witnesses, retained color layers, and the final simple graph.
- [x] Make the bridge between natural graph parameters and real asymptotic abbreviations explicit in `repo/Twobites/ParameterBounds.lean` via `paperSNat`, `paperMNat`, `paperKNat`, and comparison lemmas.
- [x] Add the first deterministic support layer in `repo/Twobites/Construction.lean`: construction data, projections, finite-set images, fibers, and the raw red/blue/simple lifted graphs.
- [x] Add the first parameter support layer in `repo/Twobites/ParameterBounds.lean`: paper-style definitions of `s`, `m`, `p`, `k` together with basic positivity and squaring lemmas.
- [x] Put the substantive paper-facing definitions and theorem statements directly in `repo/PaperDefinitions.lean` and `repo/PaperTheorems.lean`, while keeping the `repo/Twobites/` files buildable.
- [x] State the paper-facing main theorem, Ramsey lower-bound theorem, and witness-form Ramsey corollary as Lean propositions with no axioms or `sorry`s.
- [x] Write `repo/PLAN.md` for the main-results formalization, including statement choices, imports, reusable definitions, and dependency order.
- [x] Read `repo/paper/reference.tex` end to end, with the paper-check focused on the main-result sections.
- [x] Check the proof chain for Theorem `main`, including Lemmas `lem:fiber_and_degree`, `lem:large`, `lem:med`, `lem:small`, `lem:huge`, `lem:RISI`, and `lem:RI`.
- [x] Record corrections, hidden assumptions, and proof clarifications in `repo/PAPERNOTES.md`.
- [x] Confirm that no genuine gap was found in the main-result argument; the hypergraph section is only a proof sketch and remains out of scope for this formalization project.
