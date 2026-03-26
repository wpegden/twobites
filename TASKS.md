# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Use `repo/paper/reference.tex`, `PAPERNOTES.md`, and the current repo state to build `PLAN.md`.
- [ ] Produce a comprehensive roadmap for definitions, theorem statements, and proof dependencies.
- [ ] Identify what can come from mathlib versus what must be formalized here.
- [ ] Use `NEED_INPUT` for external-result or design-choice questions that need a human decision.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Create `repo/Twobites/PaperDefinitions.lean` with the public definitions identified in `repo/PLAN.md`.
- [ ] Create `repo/Twobites/PaperTheorems.lean` with statement skeletons for Theorem `main` and the Ramsey lower-bound corollary/witness theorem.
- [ ] Start the helper-module implementation from `repo/PLAN.md`, beginning with the deterministic construction data and parameter-arithmetic layer.

## Completed
- [x] Write `repo/PLAN.md` for the main-results formalization, including statement choices, imports, reusable definitions, and dependency order.
- [x] Read `repo/paper/reference.tex` end to end, with the paper-check focused on the main-result sections.
- [x] Check the proof chain for Theorem `main`, including Lemmas `lem:fiber_and_degree`, `lem:large`, `lem:med`, `lem:small`, `lem:huge`, `lem:RISI`, and `lem:RI`.
- [x] Record corrections, hidden assumptions, and proof clarifications in `repo/PAPERNOTES.md`.
- [x] Confirm that no genuine gap was found in the main-result argument; the hypergraph section is only a proof sketch and remains out of scope for this formalization project.
