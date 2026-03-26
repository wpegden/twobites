# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Create `PaperDefinitions.lean` with the definitions needed to state the paper results.
- [ ] Create `PaperTheorems.lean` with theorem statements as close to the paper as Lean allows.
- [ ] Keep the files easy for a human to compare against the paper.
- [ ] Make both files syntactically valid Lean.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Implement `repo/Twobites/Construction.lean` with the two-color lift, projection maps, fibers, and final simple-graph interface from `repo/PLAN.md`.
- [ ] Implement `repo/Twobites/ParameterBounds.lean` with the large-`n` inequalities for `s`, `m`, `p`, and `k`.
- [ ] Revisit the proposition signatures in `PaperDefinitions.lean` and `PaperTheorems.lean` only if the helper modules force a better public interface.

## Completed
- [x] Put the substantive paper-facing definitions and theorem statements directly in `repo/PaperDefinitions.lean` and `repo/PaperTheorems.lean`, while keeping the `repo/Twobites/` files buildable.
- [x] State the paper-facing main theorem, Ramsey lower-bound theorem, and witness-form Ramsey corollary as Lean propositions with no axioms or `sorry`s.
- [x] Write `repo/PLAN.md` for the main-results formalization, including statement choices, imports, reusable definitions, and dependency order.
- [x] Read `repo/paper/reference.tex` end to end, with the paper-check focused on the main-result sections.
- [x] Check the proof chain for Theorem `main`, including Lemmas `lem:fiber_and_degree`, `lem:large`, `lem:med`, `lem:small`, `lem:huge`, `lem:RISI`, and `lem:RI`.
- [x] Record corrections, hidden assumptions, and proof clarifications in `repo/PAPERNOTES.md`.
- [x] Confirm that no genuine gap was found in the main-result argument; the hypergraph section is only a proof sketch and remains out of scope for this formalization project.
