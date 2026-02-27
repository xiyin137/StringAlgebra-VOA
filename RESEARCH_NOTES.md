# VOA Research Notes (Reference-Driven)

Date: 2026-02-27
Sources: PDFs in `references/` via `read_references.py`

## 1. High-Signal Extracts

### A. Modular Virasoro and Framed VOAs

Reference:

1. `references/dong-lam-ren-modular-virasoro-voa.pdf` (arXiv:1709.04167v2)

Key points extracted:

1. For characteristic `ch(F) != 2` (and often excluding `7` for representation separation), modular Virasoro VOA behavior mirrors complex-case fusion behavior for `L(1/2,0)` families.
2. Explicit fusion products for `L(1/2,0), L(1/2,1/2), L(1/2,1/16)` are highlighted as foundational.
3. Intertwining-operator spaces and fusion-rule symmetry are explicitly discussed.
4. Tensor (fusion) product is presented via a universal mapping property.
5. Rationality of modular framed VOAs is a major result direction.

Formalization impact:

1. Strengthen `Modules.lean` around universal-property-based tensor/fusion products.
2. Add fusion symmetry lemmas beyond existence of finite bounds.
3. Improve `Examples.lean` framed/moonshine-facing assumptions using explicit module-family data.

### B. Twisted Heisenberg-Virasoro VOA

Reference:

1. `references/guo-wang-twisted-heisenberg-virasoro-voa.pdf` (arXiv:1612.06991v1)

Key points extracted:

1. There are category-correspondence results between restricted Lie algebra modules and vertex-algebra module notions.
2. A tensor-product decomposition theorem (`Theorem 3.16`) identifies the VOA as Heisenberg × Virasoro-type factorization under nondegeneracy assumptions.
3. Commutant characterization is central.
4. Zhu algebra analysis is used to prove non-rationality / non-`C2`-cofiniteness in specific cases.

Formalization impact:

1. Add explicit commutant/tensor decomposition interfaces in `Examples.lean`.
2. Add theorem stubs/lemmas in `Modules.lean` connecting rationality claims to algebraic finiteness criteria.
3. Improve cross-links between module/fusion semantics and VOA decomposition APIs.

### C. Strong Locality and Conformal Nets

Reference:

1. `references/carpi-kawahigashi-longo-weiner-voa-conformal-nets.pdf` (arXiv:1503.01260v4)

Key points extracted:

1. Strong locality is built from energy bounds + locality at the net level.
2. Strong locality is closed under tensor products and unitary subalgebras.
3. There is a one-to-one correspondence between unitary subalgebras of a strongly local VOA and covariant subnets.
4. Galois/coset correspondence statements are available in this framework.

Formalization impact:

1. Add an optional future abstraction layer for analytic/locality strengthening around `mutuallyLocal`.
2. Extend `Examples.lean` with “closure under tensor/subalgebra” theorem interfaces (axiomatic in this repo for now).
3. Provide bridge theorems that connect algebraic and analytic locality assumptions cleanly.

### D. Moonshine via Tensor/Simple-Current Structure

Reference:

1. `references/shimakura-e8-approach-moonshine-voa.pdf` (arXiv:1009.4752v1)

Key points extracted:

1. Fusion rules are treated as algebraic structure on module classes.
2. Aut(V)-action preserves fusion rules.
3. Tensor-product fusion factorization for `V^k` is explicit.
4. Simple-current extension mechanisms are central in construction flow.

Formalization impact:

1. Add module-class/fusion-action interfaces in `Modules.lean`.
2. Extend `Examples.lean` moonshine section with explicit fusion-action assumptions and consequences.
3. Add tensor-fusion compatibility lemmas to align with `IntertwiningOperator` infrastructure.

### E. Generalized Heisenberg Intertwiners

Reference:

1. `references/tuite-zuevsky-generalized-voa-heisenberg.pdf` (arXiv:1106.6149v2)

Key points extracted:

1. Creative intertwining operators are constructed explicitly for Heisenberg module extensions.
2. A generalized VOA structure (complex-parameterized) is emphasized.

Formalization impact:

1. Enrich `IntertwiningOperator` APIs with “creative” constructor-style structure.
2. Add examples showing how Heisenberg constructions induce generalized operator families.

### F. Correlator/OPE Core References (Direct Verification, 2026-02-27)

References downloaded/read:

1. `references/borcherds-1986-vertex-algebras-kac-moody-monster.pdf`
2. `references/frenkel-bourbaki-vertex-algebras-and-algebraic-curves-2000.pdf`

Primary extracts used for verification:

1. Borcherds 1986:
   - defines mode products `u_n(v)` via generalized/normal-ordered vertex operators;
   - states truncation and vacuum-style identities (conditions i-v in §4);
   - positions vertex algebras as a noncommutative generalization of commutative rings with derivation.
2. Frenkel (Bourbaki, 2000):
   - explicit vacuum/translation/locality axioms (§2.2);
   - associativity/OPE identity `Y(A,z)Y(B,w)C = Y(Y(A,z-w)B,w)C` (§2.6, Formula (7));
   - commutator extraction from OPE singular terms (§2.6, Formula (9));
   - n-point function proposition and bootstrap/symmetry structure (§2.7, Proposition 2.7);
   - Heisenberg OPE example and boson-fermion correspondence sections (§2.6, §3.3).

Impact on `Correlators.lean` assessment:

1. Confirmed alignment:
   - algebraic (non-analytic) correlator setup is consistent with the formal-distribution mode framework;
   - two-point commutator/anticommutator to `nthProduct` formulas match the OPE-singular-term extraction philosophy;
   - n-point correlator interface is directionally consistent with the references’ n-point/OPE formalism.
2. Confirmed rigor gap:
   - current core `nthProduct` in `FormalDistributions.lean` remains a simplified model, so the implementation is not yet full-reference-level Jacobi/Borcherds realization.

Availability note:

1. Full monographs cited in source comments (Kac *Vertex Algebras for Beginners*, Frenkel-Ben-Zvi AMS book) are not openly downloadable from the queried AMS endpoints in this environment (access redirects/403). The Bourbaki article by Frenkel was used as an open primary source for direct formula verification.

## 2. Immediate Formalization Targets (Backlog-Ready)

### T1: Fusion Product Universal Property

Target file:

1. `StringAlgebra/VOA/Modules.lean`

Planned additions:

1. A structure encoding universal mapping property for tensor/fusion products.
2. Bridge theorem from universal property to uniqueness up to isomorphism.
3. Compatibility with existing `fusionRules`.

### T2: Fusion Symmetry and Tensor Compatibility

Target file:

1. `StringAlgebra/VOA/Modules.lean`

Planned additions:

1. Symmetry interfaces for fusion multiplicities.
2. Tensor-product compatibility theorem shell for fusion multiplicities.
3. Explicit dependency on rationality/cofiniteness assumptions as parameters, not hidden assumptions.

### T3: Commutant/Tensor Decomposition Interfaces

Target files:

1. `StringAlgebra/VOA/Examples.lean`
2. `StringAlgebra/VOA/Modules.lean`

Planned additions:

1. Abstract commutant package with decomposition statement.
2. Heisenberg-Virasoro decomposition interface mirroring extracted theorem shape.
3. Derived consequences for representation and Zhu-style finiteness criteria hooks.

### T4: Locality Closure Layer (Algebraic)

Target files:

1. `StringAlgebra/VOA/FormalDistributions.lean`
2. `StringAlgebra/VOA/VertexAlgebra.lean`

Planned additions:

1. More closure lemmas for locality under algebraic operations.
2. Reusable bridge lemmas so module-layer proofs avoid direct axiom-level rewrites.
3. Separation between current coefficient-model simplifications and future stronger Jacobi/Borcherds formulations.

## 3. Notes on Reliability

1. These notes are extracted from PDF text parsing (`PyMuPDF`) and can include OCR/line-break artifacts.
2. Formalization tasks above are scoped to the existing repository style: explicit assumptions, no hidden choice, no proof-gap smuggling.
3. For theorem-statement exactness, cross-check cited paper sections during implementation-level theorem finalization.

## 4. Suggested Next Sprint Mapping

1. `VOA-WS1-04`: locality closure layer expansion informed by strong-locality decomposition patterns.
2. `VOA-WS2-02`: additional Virasoro-mode derived lemmas needed by fusion symmetry wrappers.
3. `VOA-WS3-01`: fusion universal-property structure in `Modules.lean`.
4. `VOA-WS4-02`: Heisenberg-Virasoro commutant/tensor decomposition interfaces in `Examples.lean`.
