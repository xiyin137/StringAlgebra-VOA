# StringAlgebra-VOA

Lean 4 formalization of vertex operator algebra infrastructure.

## Scope

1. `StringAlgebra/VOA/Basic.lean`
2. `StringAlgebra/VOA/SuperBasic.lean`
3. `StringAlgebra/VOA/FormalDistributions.lean`
4. `StringAlgebra/VOA/SuperFormalDistributions.lean`
5. `StringAlgebra/VOA/VertexAlgebra.lean`
6. `StringAlgebra/VOA/Virasoro.lean`
7. `StringAlgebra/VOA/Modules.lean`
8. `StringAlgebra/VOA/Correlators.lean`
9. `StringAlgebra/VOA/Examples.lean`
10. `StringAlgebra/VOA/Correlators/Basics.lean`
11. `StringAlgebra/VOA/Correlators/ThreePoint12.lean`
12. `StringAlgebra/VOA/Correlators/ThreePoint23.lean`
13. `StringAlgebra/VOA/Correlators/ThreePoint13.lean`
14. `StringAlgebra/VOA/Correlators/TwoPoint.lean`
15. `StringAlgebra/VOA/Examples/Boson.lean`
16. `StringAlgebra/VOA/Examples/AffineLattice.lean`
17. `StringAlgebra/VOA/Examples/Fermion.lean`
18. `StringAlgebra/VOA/Examples/Additional.lean`
19. `StringAlgebra/VOA/Modules/Core.lean`
20. `StringAlgebra/VOA/Modules/Intertwining.lean`
21. `StringAlgebra/VOA/Modules/Fusion.lean`
22. `StringAlgebra/VOA/Modules/Advanced.lean`

## Planning and Notes

1. `TODO.md`: pass-by-pass log plus free CFT roadmap.
2. `DEVELOPMENT_PLAN.md`: comprehensive plan for rigorous free boson/free fermion + OPE/correlator development.
3. `RESEARCH_NOTES.md`: reference-backed notes used for theorem-family planning.

## Build

```bash
lake build StringAlgebra.VOA
```

## Audit

```bash
rg -n '^\s*sorry\b' StringAlgebra/VOA --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/VOA --glob '*.lean'
rg -n '^[[:space:]]*axiom\b|^[[:space:]]*admit\b|Classical\.choose|Classical\.epsilon|^[[:space:]]*unsafe\s' StringAlgebra/VOA --glob '*.lean'
```

## Status (2026-02-27)

1. Theorem-level `sorry` count: `0`
2. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` in `StringAlgebra/VOA/*.lean`.
3. Super and correlator infrastructure (`SuperBasic`, `SuperFormalDistributions`, `Correlators`) is integrated in the root `StringAlgebra/VOA.lean` target.
4. Free CFT development phases (boson/fermion/OPE/correlators) are tracked explicitly in `TODO.md`.
5. Correlator code has been split into `StringAlgebra/VOA/Correlators/` submodules while keeping `StringAlgebra/VOA/Correlators.lean` as the stable facade import.
6. Example code has been split into `StringAlgebra/VOA/Examples/` submodules while keeping `StringAlgebra/VOA/Examples.lean` as the stable facade import.
7. Module theory code has been split into `StringAlgebra/VOA/Modules/` submodules while keeping `StringAlgebra/VOA/Modules.lean` as the stable facade import.
8. Correlator baseline now includes one-point state-mode API plus vacuum-insertion reductions:
   - two-point to one-point mode correlators
   - three-point to two-point mode correlators
   - state-level two-/three-point wrappers with corresponding vacuum-reduction lemmas
   - state-level two-point commutator/anticommutator wrappers with OPE-regime extraction lemmas
   - state-level three-point commutator/anticommutator wrappers (pair `12/23/13`) with OPE-regime extraction for all pairs
   - state-level apply-form commutator/anticommutator simplifications for all three-point pairs (`12/23/13`)
   - state-level `nthProduct` wrappers for two-point commutator/anticommutator and all three-point pairs (`12/23/13`)
   - state-level two-point mode OPE extraction wrappers (`opeCoefficient`, cutoff-vanishing, piecewise, `coefficientOrZero`)
   - state-level two-point commutator/anticommutator wrappers in direct `coefficientOrZero` form
   - normalized two-point mixed-regime OPE extraction aliases with explicit `ab/ba` orientation naming at formal and state levels
   - state-level two-/three-point linearity wrappers (`add/smul/neg/sub`) and two-point state commutator/anticommutator linearity wrappers under explicit `Y`-compatibility hypotheses
   - complete two-point commutator/anticommutator linearity families (`add/smul/neg/sub`) at formal level plus state-level wrappers (explicit `Y`-compatibility for state formulas)
   - complete three-point `(1,2)` commutator/anticommutator linearity families (`add/smul/neg/sub`) at formal level plus state-level wrappers (explicit `Y`-compatibility for state formulas)
   - normalized three-point `(1,2)` mixed-regime OPE extraction aliases with explicit `ab/ba` orientation naming at formal and state levels
   - complete three-point `(2,3)` commutator/anticommutator linearity families (`add/smul/neg/sub`) at formal level plus state-level wrappers (explicit `Y`-compatibility for state formulas)
   - normalized three-point `(2,3)` mixed-regime OPE extraction aliases with explicit `bc/cb` orientation naming at formal and state levels
   - complete three-point `(1,3)` commutator/anticommutator linearity families (`add/smul/neg/sub`) at formal level plus state-level wrappers (explicit `Y`-compatibility for state formulas)
   - normalized three-point `(2,3)` mixed-regime OPE extraction aliases with `left/right` naming (left = `(b,c)`, right = `(c,b)`) at formal and state levels
   - normalized three-point `(1,3)` mixed-regime OPE extraction aliases with `left/right` naming (left = `(b,a)`, right = `(b,c)`) at formal and state levels
   - normalized three-point `(1,3)` strict-below OPE extraction aliases with explicit `ba/bc` orientation naming at formal and state levels

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. MZV: https://github.com/xiyin137/StringAlgebra-MZV
3. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity
4. MTC: https://github.com/xiyin137/StringAlgebra-MTC
