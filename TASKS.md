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
- [ ] Extend `repo/Twobites/ParameterBounds.lean` from the current threshold definitions and positivity lemmas to the paper's concrete large-`n` and small-`ε` ordering inequalities used later in Sections 3-4.
- [ ] Extend `repo/Twobites/IndependentSets.lean` from the new `H_I`, `L_I`, `M_I`, `S_I` partition and restricted closed-pair interface to the actual deterministic counting lemmas used in `lem:huge`, `lem:RISI`, and `lem:RI`.
- [ ] Connect the new `finalGraph.CliqueFree 3` theorem and the part-restricted closed-pair bookkeeping to the eventual independence-number proofs in `repo/PaperTheorems.lean`.

## Completed
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
