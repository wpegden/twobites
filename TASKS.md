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
- [ ] Extend `repo/Twobites/Construction.lean` from the raw two-color lift to the triangle-deletion bookkeeping and retained-edge simple graph from `repo/PLAN.md`.
- [ ] Extend `repo/Twobites/ParameterBounds.lean` from the basic parameter identities to the actual large-`n` and small-`ε` inequalities used later in Sections 3-4.
- [ ] Start the deterministic independent-set/open-pair layer that bridges the construction API to the proofs of `lem:huge`, `lem:RISI`, and `lem:RI`.

## Completed
- [x] Add the first deterministic support layer in `repo/Twobites/Construction.lean`: construction data, projections, finite-set images, fibers, and the raw red/blue/simple lifted graphs.
- [x] Add the first parameter support layer in `repo/Twobites/ParameterBounds.lean`: paper-style definitions of `s`, `m`, `p`, `k` together with basic positivity and squaring lemmas.
- [x] Put the substantive paper-facing definitions and theorem statements directly in `repo/PaperDefinitions.lean` and `repo/PaperTheorems.lean`, while keeping the `repo/Twobites/` files buildable.
- [x] State the paper-facing main theorem, Ramsey lower-bound theorem, and witness-form Ramsey corollary as Lean propositions with no axioms or `sorry`s.
- [x] Write `repo/PLAN.md` for the main-results formalization, including statement choices, imports, reusable definitions, and dependency order.
- [x] Read `repo/paper/reference.tex` end to end, with the paper-check focused on the main-result sections.
- [x] Check the proof chain for Theorem `main`, including Lemmas `lem:fiber_and_degree`, `lem:large`, `lem:med`, `lem:small`, `lem:huge`, `lem:RISI`, and `lem:RI`.
- [x] Record corrections, hidden assumptions, and proof clarifications in `repo/PAPERNOTES.md`.
- [x] Confirm that no genuine gap was found in the main-result argument; the hypergraph section is only a proof sketch and remains out of scope for this formalization project.
