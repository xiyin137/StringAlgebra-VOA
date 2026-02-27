# StringAlgebra-VOA Comprehensive Development Plan

Date: 2026-02-27  
Primary goal: mathematically rigorous formalization of free boson and free fermion CFTs, including OPE and correlation functions, in Lean.

## 1. Scope and Success Criteria

This plan targets a complete algebraic CFT pipeline inside `StringAlgebra/VOA`:

1. Rigorous free boson VOA construction (Heisenberg/Fock).
2. Rigorous free fermion (super) VOA construction (Clifford/CAR).
3. Fully formalized OPE coefficient calculus (not simplified placeholders).
4. Correlator layer with vacuum expectation values and proved identities.
5. Proof integrity gates: no `sorry`, no `axiom`, no hidden choice smuggling.

Success means:

1. Theories compile end-to-end under `lake build StringAlgebra.VOA`.
2. Core constructions are definitional (not naming-only interfaces).
3. Main theorem set includes explicit OPE and correlator statements for both free theories.

## 2. Current State (Gap Assessment)

### 2.1 Strengths

1. `StringAlgebra/VOA/*.lean` is currently `sorry`-free.
2. Extensive locality/fusion/Virasoro infrastructure exists.
3. Build and audit discipline is already strong.

### 2.2 Blocking Gaps for Full CFT Rigor

1. Free boson is only a lightweight example shell, not a full Fock-space VOA realization.
2. Free fermion/super-VOA layer is absent.
3. `FormalDistributions.nthProduct` is currently simplified; full residue/Jacobi-grade formalism is missing.
4. Correlator objects (n-point functions, vacuum expectation maps, Wick expansions) are not yet formalized.
5. Analytic-strength claims are not yet separated from algebraic formalization boundaries.

## 3. Mathematical Foundation Track

### 3.1 Reference Acquisition and Reading Notes

Deliverables:

1. Curated reference set in `references/` focused on:
   - VOA axioms and Jacobi/Borcherds identities.
   - Free boson and free fermion constructions.
   - Algebraic correlator formalisms and Wick theorem.
2. Structured reading notes in `RESEARCH_NOTES.md`:
   - theorem extracts,
   - exact dependency graph,
   - Lean implementation implications.

Acceptance criteria:

1. Every major theorem implemented has at least one cited primary source in notes.
2. Notes distinguish proven statements vs future targets.

### 3.2 Formalization Conventions

1. Keep algebraic CFT and analytic CFT layers explicitly separated.
2. Avoid hidden coercion-heavy proof style when theorem interfaces can be explicit.
3. Prefer reusable theorem bundles over ad hoc one-off lemmas.

## 4. Workstreams

## WS1: Formal Distribution and OPE Core Hardening

Target files:

1. `StringAlgebra/VOA/FormalDistributions.lean`
2. `StringAlgebra/VOA/VertexAlgebra.lean`

Tasks:

1. Replace simplified `nthProduct` semantics with a faithful formal mode-sum/residue definition.
2. Strengthen `OPEData` from container-level to theorem-connected structure.
3. Add explicit bridges:
   - locality `↔` finite singular OPE order,
   - mode coefficients from OPE poles,
   - normal-order operation compatibility with locality.
4. Add a formally tracked theorem family for Jacobi/Borcherds consequences.

Acceptance criteria:

1. No simplified placeholder formula remains in core OPE operations.
2. At least one theorem proving OPE coefficient extraction from mode operations exists and is used downstream.

## WS2: Super Algebra and Free Fermion Core

Target files (new + existing):

1. `StringAlgebra/VOA/SuperBasic.lean` (new)
2. `StringAlgebra/VOA/SuperFormalDistributions.lean` (new)
3. `StringAlgebra/VOA/Examples.lean` (integration)

Tasks:

1. Introduce parity-graded structures needed for super-VOA reasoning.
2. Define CAR/Clifford mode algebra interface.
3. Construct free fermion state space and field assignment.
4. Prove fermionic locality/sign conventions at mode level.

Acceptance criteria:

1. Free fermion construction produces a typed (super) VOA-like object with explicit axioms.
2. Fermion field self-OPE singular part is formalized with sign-correctness lemmas.

## WS3: Free Boson (Heisenberg/Fock) Construction

Target files:

1. `StringAlgebra/VOA/Examples.lean` (or split to `FreeBoson.lean`)
2. `StringAlgebra/VOA/Modules.lean` (module/representation bridge)

Tasks:

1. Define Heisenberg mode algebra representation on Fock space.
2. Construct bosonic field and vacuum/conformal vectors.
3. Prove VOA axioms for free boson realization (at current algebraic rigor level).
4. Add normal ordering and mode commutator consequences needed for OPE/correlators.

Acceptance criteria:

1. Free boson is an actual constructed object, not only a data shell.
2. Canonical boson OPE statement is proven in the formal distribution layer.

## WS4: Correlator and Wick Infrastructure

Target files (new + existing):

1. `StringAlgebra/VOA/Correlators.lean` (new)
2. `StringAlgebra/VOA/FormalDistributions.lean`
3. `StringAlgebra/VOA/VertexAlgebra.lean`

Tasks:

1. Define vacuum expectation functional and n-point correlator objects.
2. Define field insertion order and normal-ordered correlator interfaces.
3. Formalize Wick-style recursive decomposition framework.
4. Prove baseline identities:
   - 1-point vacuum vanishing for non-vacuum states,
   - 2-point free boson and free fermion kernels,
   - factorization rules under normal ordering assumptions.

Acceptance criteria:

1. Correlators are first-class Lean definitions with reusable API.
2. Free boson/free fermion 2-point correlators are explicit theorem outputs.

## WS5: Representation/Fusion Integration

Target files:

1. `StringAlgebra/VOA/Modules.lean`
2. `StringAlgebra/VOA/Examples.lean`

Tasks:

1. Connect free-theory modules to existing fusion interfaces.
2. Add semisimplicity/complement/decomposition consequences where assumptions allow.
3. Bridge correlator identities to intertwiner/fusion statements where algebraically meaningful.

Acceptance criteria:

1. Free-theory constructions can feed existing module/fusion APIs.
2. No theorem states “rational” or “finite” without explicit assumptions.

## WS6: Documentation, Audit, and Release Gates

Target files:

1. `TODO.md`
2. `RESEARCH_NOTES.md`
3. `README.md`
4. `DEVELOPMENT_PLAN.md`

Tasks:

1. Keep pass-by-pass logs synchronized with code.
2. Record theorem families and source references.
3. Maintain reproducible checks and audit commands.

Acceptance criteria:

1. Documentation matches current code state.
2. Each major theorem family is cross-referenced to at least one source note.

## 5. Milestones

### M0: Foundation Lock

1. Confirm baseline build/audit.
2. Finalize reference list and reading-note schema.
3. Freeze theorem naming conventions for new free-theory files.

### M1: OPE Core Upgrade

1. Replace simplified `nthProduct`.
2. Prove OPE-locality bridge lemmas.
3. Ensure downstream files compile with upgraded definitions.

### M2: Free Boson Formalization

1. Implement Fock construction interfaces.
2. Prove Heisenberg-mode/OPE core theorems.
3. Add canonical free boson correlator theorem set (2-point minimum).

### M3: Free Fermion Formalization

1. Implement super/CAR layer.
2. Prove fermion OPE sign-sensitive identities.
3. Add canonical free fermion correlator theorem set (2-point minimum).

### M4: Correlator + Wick Layer

1. Introduce `Correlators.lean`.
2. Prove recursive/formal Wick decomposition theorems.
3. Connect correlators with normal ordering and OPE data.

### M5: Integration and Hardening

1. Bridge to module/fusion interfaces.
2. Complete docs and source traceability.
3. Pass full quality gates.

## 6. Quality Gates (Must Pass Every Milestone)

1. `lake build StringAlgebra.VOA`
2. `rg -n "\\bsorry\\b" StringAlgebra/VOA/*.lean` returns empty
3. `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA/*.lean` returns empty
4. New theorem interfaces include explicit assumptions (no hidden global strengthening).
5. No replacement of hard proofs with definitional stubs.

## 7. Risk Register and Mitigation

1. Risk: super-VOA machinery introduces large refactor surface.
   Mitigation: isolate in new files (`SuperBasic`, `SuperFormalDistributions`) before touching existing VOA APIs.
2. Risk: correlator formalization drifts into analysis.
   Mitigation: keep first implementation purely algebraic/formal and mark analytic upgrades explicitly.
3. Risk: OPE core upgrade breaks existing lemma graph.
   Mitigation: introduce compatibility lemmas and migrate in small compile-safe increments.
4. Risk: theorem sprawl without usable API.
   Mitigation: each batch must include extraction/projection lemmas and at least one downstream usage proof.

## 8. Immediate Next Sprint (Concrete)

1. Upgrade `nthProduct` definition and prove compatibility lemmas for all existing users.
2. Introduce a minimal super-algebra foundation file with parity and sign rules.
3. Create `Correlators.lean` with vacuum expectation and 2-point correlator definitions.
4. Add free boson 2-point correlator theorem based on Heisenberg commutator infrastructure.
5. Add reference-backed reading notes section dedicated to free boson/free fermion rigorous construction.

## 9. Completion Definition

This plan is complete when:

1. Free boson and free fermion constructions are formalized as concrete objects with proved OPE theorems.
2. Correlator layer exists with proved baseline identities and Wick-style infrastructure.
3. All quality gates remain green and documented.
