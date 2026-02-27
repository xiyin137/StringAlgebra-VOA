# VOA Soundness TODO (Dependency-Driven)

Date: 2026-02-26

This file tracks semantic and proof debt for `StringAlgebra/VOA` under `agent.md` rigor rules.

## Current Verified State

1. `lake build StringAlgebra.VOA` passes.
2. `StringAlgebra/VOA/*.lean` is `sorry`-free (proof-level `sorry` count: 0).
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in VOA Lean files.
4. Placeholder `True := trivial` stubs in core module/formal-distribution/example interfaces have been removed.
5. Conformal-weight extraction and lattice rationality criteria now use explicit witness packages (`L0Grading`, `RationalityCriterion`) instead of implicit selection.
6. `FormalDistributions.lean` now includes explicit locality constructors/derived symmetry lemmas (`mutuallyLocal_of_mode_commute`, `mutuallyLocal_symm`).
7. Redundant field-projection theorem shells in `Examples.lean` were removed (including direct criterion-direction wrappers), keeping the example interface focused on substantive statements.
8. Additional unused shell wrappers in `FormalDistributions.lean` (definitional and witness-projection helper theorems) were removed to reduce non-semantic interface noise.

## Infrastructure Launch (2026-02-27)

1. Added WS1 algebraic infrastructure in `FormalDistributions.lean`:
   - field-property closure lemmas (`zero`, `add`, `smul`)
   - locality closure lemmas (`zero`, `add`, `smul`, symmetry reuse)
   - `nthProduct` algebra lemmas (`zero`, `add`, evaluation helpers)
2. Added WS1/WS2 bridge lemmas in `VertexAlgebra.lean`:
   - `nProduct` right-linearity helpers
   - applied translation commutator theorem
   - locality symmetry + vacuum locality forms
   - Virasoro relation rewritten in `L` notation + explicit `L0Grading` existence packaging
3. Added reference-driven planning artifact:
   - `RESEARCH_NOTES.md` with formalization targets extracted from downloaded VOA references.
4. Post-launch checks:
   - `lake build StringAlgebra.VOA` passes
   - `sorry`/`axiom`/assumption-bundle audit counts remain zero

## Infrastructure Expansion (2026-02-27, pass 2)

1. Extended WS1 closure algebra in `FormalDistributions.lean`:
   - derivative closure under `neg`/`sub`
   - field-property closure under `neg`/`sub`
   - locality closure under `neg`/`sub` (left/right forms)
   - `nthProduct` bilinearity infrastructure under `smul`/`neg`/`sub`
2. Extended WS1/WS2 bridge layer in `VertexAlgebra.lean`:
   - `nProduct` `neg`/`sub` right-linearity lemmas
   - rearranged translation commutator formula `translation_apply_nProduct`
   - locality-closure bridge lemmas with explicit `Y`-compatibility hypotheses (`add`/`sub`)
   - applied Virasoro relation theorem + derived `L(0)` commutator special cases
3. Deep-sorry audit:
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean`: `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` in VOA Lean files
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes

## Infrastructure Expansion (2026-02-27, pass 3)

1. Added deeper WS1 `FormalDistributions` infrastructure:
   - `derivative_identity`
   - transfer of field property through fixed-mode products (`hasFieldProperty_nthProduct_right`)
   - normal-ordered product closure (`zero`/`add` and field-property transfer lemmas)
   - Dong witness accessors + normal-ordered specialization (`DongLemmaData.mutuallyLocal_*`)
2. Added deeper WS2 bridge lemmas in `VertexAlgebra.lean`:
   - derived vacuum-translation field identity `Y_translation_vacuum_eq_zero`
   - independent derivation of `translation_vacuum` from derivative + creation axioms
   - explicit `L(0)` action lemmas from grading witnesses (`L_zero_weight_spec`,
     `L_zero_conformalWeight_spec`, `exists_weight_L0_action`)
3. Added WS3/WS4 compatibility refinements:
   - `FusionTensorProduct` canonical simplification lemmas (`hom_self_eq_id`, `iso_*` simp lemmas)
   - lattice-model bridge theorem for pairwise fusion bounds
     (`fusion_rules_bounded_pos_pair_of_positiveDefinite`)
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 4)

1. Added VOA-level WS1 bridge from lower truncation to field calculus:
   - state-field field-property theorem (`Y_hasFieldProperty`)
   - derived field-property transfer for state-level `nthProduct`/normal ordering
2. Added explicit Dong-closure contract on state fields (`VertexAlgebra.DongClosed`) and
   derived locality theorems:
   - `locality_nthProduct`
   - `locality_normalOrderedProduct`
3. Extended WS2 Virasoro derivations:
   - diagonal commutator specialization `[L(m),L(m)]` in scaled form
     (`virasoro_relation_L_diag`, applied form)
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 5)

1. Added Dong-closure state-layer assumption hierarchy in `VertexAlgebra.lean`:
   - `DongClosedData` (witness-driven closure package on state fields)
   - canonical instance `DongClosedData -> DongClosed`
2. Added symmetric/right-oriented locality derivations for Dong-closed operations:
   - `locality_right_nthProduct`
   - `locality_right_normalOrderedProduct`
3. Added additional field-property bridges for state operations:
   - `Y_nthProduct_hasFieldProperty_right`
   - `Y_normalOrderedProduct_hasFieldProperty_right`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 6)

1. Added module-level Dong/locality assumption hierarchy in `Modules.lean`:
   - `ModuleLocality`
   - `ModuleDongClosedData`
   - `ModuleDongClosed`
   - canonical instance `ModuleLocality + ModuleDongClosedData -> ModuleDongClosed`
2. Added module-field Dong-closed locality derivations:
   - `VAModule.locality_nthProduct`
   - `VAModule.locality_right_nthProduct`
   - `VAModule.locality_normalOrderedProduct`
   - `VAModule.locality_right_normalOrderedProduct`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 7)

1. Added intertwiner compatibility contracts in `Modules.lean`:
   - linear-map commutation forms of Jacobi at mode `-1`
     (`jacobi_identity_action_comp`, symmetric variant)
   - reusable proposition class + canonical instance:
     `IntertwiningOperator.ModeMinusOneCompatible`
2. Added module/intertwiner Dong-locality bridge theorems:
   - `source_locality_nthProduct`
   - `target_locality_nthProduct`
   - `target_locality_normalOrderedProduct`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 8)

1. Added adjoint-module bridges in `Modules.lean` to connect state-level and module-level Dong/locality layers:
   - `adjointModuleLocality`
   - `adjointModuleDongClosedData` (from `VertexAlgebra.DongClosedData`)
   - `adjointModuleDongClosed` (from `VertexAlgebra.DongClosed`)
2. Added derived specialization theorem:
   - `VAModule.adjoint_locality_nthProduct`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 9)

1. Expanded module-action and field-property infrastructure in `Modules.lean`:
   - vacuum action mode API:
     `action_vacuum_mode`, `action_vacuum_mode_ne`,
     `action_vacuum_mode_minus_one`, `action_vacuum_mode_minus_one_apply`
   - module-field property bridges:
     `Y_M_hasFieldProperty`,
     `Y_M_nthProduct_hasFieldProperty_right`,
     `Y_M_normalOrderedProduct_hasFieldProperty_right`
2. Added explicit module-locality bridges for both module and intertwiner layers:
   - module state-field locality:
     `stateField_locality`, `stateField_locality_symm`, `stateField_locality_self`
   - intertwiner source/target locality transport:
     `source_locality`, `target_locality`,
     `source_locality_symm`, `target_locality_symm`
3. Expanded fusion tensor-product universal API:
   - `hom_unique`
   - compositionality theorem `hom_comp`
   - intertwiner-generator compatibility on canonical isomorphisms:
     `iso_apply_incl`, `iso_symm_apply_incl`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 10)

1. Extended intertwiner vacuum-mode simplification API in `Modules.lean`:
   - linear-map composition simplifications at mode `-1`:
     `action_comp_vacuum_minus_one_source`,
     `action_comp_vacuum_minus_one_target`
   - applied simplifications:
     `action_apply_vacuum_minus_one_source`,
     `action_apply_vacuum_minus_one_target`
2. Strengthened universal fusion-product coherence lemmas:
   - canonical self-composition simplifications:
     `hom_comp_self_left`, `hom_comp_self_right`
   - canonical isomorphism transitivity:
     `iso_trans`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 11)

1. Extended fusion universal-map coherence in `Modules.lean`:
   - higher associativity form over four realizations:
     `FusionTensorProduct.hom_comp_assoc`
   - opposite-side inverse identity:
     `FusionTensorProduct.hom_comp_hom_eq_id_left`
2. Added canonical fusion-isomorphism symmetry API:
   - `FusionTensorProduct.iso_symm_eq_iso`
3. Expanded lattice rationality bridge infrastructure in `Examples.lean`:
   - criterion accessor:
     `LatticeVOA.rational_iff_positiveDefinite`
   - rationality-to-bounds bridges:
     `LatticeVOA.fusion_rules_bounded_pos_of_rational`
     `LatticeVOA.fusion_rules_bounded_pos_pair_of_rational`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 12)

1. Expanded Virasoro algebra infrastructure in `Virasoro.lean`:
   - bracket decomposition helpers:
     `VirasoroAlgebra.bracket_of_sum_ne_zero`,
     `VirasoroAlgebra.bracket_of_sum_eq_zero`,
     `VirasoroAlgebra.bracket_zero_zero`,
     `VirasoroAlgebra.bracket_zero_left`,
     `VirasoroAlgebra.bracket_zero_right`
2. Added representation-level Virasoro commutator specializations:
   - vector-applied relation:
     `VirasoroRep.virasoro_relation_apply`
   - zero-mode specializations:
     `VirasoroRep.virasoro_relation_zero_left`,
     `VirasoroRep.virasoro_relation_zero_left_simplified`,
     `VirasoroRep.virasoro_relation_zero_right`,
     `VirasoroRep.virasoro_relation_zero_right_simplified`
   - applied zero-mode forms:
     `VirasoroRep.virasoro_relation_zero_left_apply`,
     `VirasoroRep.virasoro_relation_zero_right_apply`
3. Added highest-weight and Verma-module bridge utilities:
   - `VirasoroRep.HighestWeightState` accessors:
     `L0_apply_state`, `annihilation_of_pos`, `annihilation_one`
   - canonical Verma-to-highest-weight packaging:
     `VirasoroRep.VermaModule.highestWeightState`
     plus projection/annihilation lemmas
4. Added minimal-model and Sugawara convenience API:
   - `MinimalModel.p_gt_q`, `MinimalModel.q_ge_two`, `MinimalModel.coprime_p_q`,
     `MinimalModel.centralChargeQ`
   - `sugawaraTensor_apply`, `sugawaraTensor_eq_zero`
5. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 13)

1. Expanded conformal-weight witness API in `VertexAlgebra.lean`:
   - added explicit witness existence in conformal-weight notation:
     `ConformalVertexAlgebra.exists_conformalWeight_action`
   - added `PrimaryState` accessors:
     `PrimaryState.weight_condition_apply`,
     `PrimaryState.is_primary_of_pos`,
     `PrimaryState.is_primary_one`
2. Added morphism transport API for state/mode operations:
   - vertex-algebra hom transport:
     `VertexAlgebraHom.map_nProduct`,
     `VertexAlgebraHom.map_nProduct_vacuum_left`,
     `VertexAlgebraHom.map_vacuum_minus1_action`
   - VOA hom transport:
     `VOAHom.map_L`,
     `VOAHom.map_translation`
3. Added primary-state transport across VOA homomorphisms:
   - `VOAHom.mapPrimaryState`
   - projection lemmas:
     `VOAHom.mapPrimaryState_state`,
     `VOAHom.mapPrimaryState_weight`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 14)

1. Expanded Dong-closure specialization API in `FormalDistributions.lean`:
   - added mode-`0` specializations:
     `DongLemmaData.mutuallyLocal_nthProduct_zero`,
     `DongLemmaData.mutuallyLocal_right_nthProduct_zero`
   - added right-oriented mode-`-1` specialization:
     `DongLemmaData.mutuallyLocal_right_nthProduct_neg_one`
2. Expanded normal-ordered algebraic API:
   - linearity/scalar and sign/subtraction interfaces:
     `normalOrderedProduct_smul_left`,
     `normalOrderedProduct_smul_right`,
     `normalOrderedProduct_neg_left`,
     `normalOrderedProduct_neg_right`,
     `normalOrderedProduct_sub_left`,
     `normalOrderedProduct_sub_right`
3. Added explicit normal-ordered re-expression lemmas through `nthProduct (-1)`:
   - `DongLemmaData.mutuallyLocal_normalOrderedProduct_via_nthProduct_neg_one`
   - `DongLemmaData.mutuallyLocal_right_normalOrderedProduct_via_nthProduct_neg_one`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 15)

1. Expanded morphism-construction infrastructure in `VertexAlgebra.lean`:
   - added identity and composition constructors for vertex-algebra morphisms:
     `VertexAlgebraHom.idHom`, `VertexAlgebraHom.compHom`
   - added identity/composition projection simp lemmas:
     `VertexAlgebraHom.idHom_toLinearMap`,
     `VertexAlgebraHom.compHom_toLinearMap`,
     `VertexAlgebraHom.compHom_apply`
2. Expanded VOA-level morphism-construction infrastructure:
   - added identity and composition constructors:
     `VOAHom.idHom`, `VOAHom.compHom`
   - added projection simp lemmas:
     `VOAHom.idHom_toLinearMap`,
     `VOAHom.compHom_toLinearMap`,
     `VOAHom.compHom_apply`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 16)

1. Expanded morphism-coherence API in `VertexAlgebra.lean` for vertex-algebra homs:
   - added apply-level identity/composition simplifications:
     `VertexAlgebraHom.idHom_apply`,
     `VertexAlgebraHom.compHom_id_right_apply`,
     `VertexAlgebraHom.compHom_id_left_apply`,
     `VertexAlgebraHom.compHom_assoc_apply`
   - added composition transport on `n`-products:
     `VertexAlgebraHom.map_nProduct_compHom`
2. Expanded apply-level coherence for VOA homs:
   - `VOAHom.idHom_apply`,
     `VOAHom.compHom_id_right_apply`,
     `VOAHom.compHom_id_left_apply`,
     `VOAHom.compHom_assoc_apply`
3. Added composition-aware primary-state transport projections:
   - `VOAHom.mapPrimaryState_comp_state`
   - `VOAHom.mapPrimaryState_comp_weight`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 17)

1. Added extensional/compositional coherence for morphism constructions in `VertexAlgebra.lean`:
   - `VertexAlgebraHom.ext` (extensional equality via underlying linear map)
   - structure-level identity/associativity laws:
     `VertexAlgebraHom.compHom_id_right`,
     `VertexAlgebraHom.compHom_id_left`,
     `VertexAlgebraHom.compHom_assoc`
2. Added apply-level coherence and transport enrichments:
   - `VertexAlgebraHom.map_nProduct_compHom`
   - `VOAHom.map_L_compHom`
   - `VOAHom.map_translation_compHom`
3. Added VOA-level structure equalities for composition constructors:
   - `VOAHom.compHom_id_right`,
     `VOAHom.compHom_id_left`,
     `VOAHom.compHom_assoc`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 18)

1. Expanded `VertexOperatorAlgebra` derived API in `VertexAlgebra.lean`:
   - structural wrappers:
     `VertexOperatorAlgebra.exists_decomposition`,
     `VertexOperatorAlgebra.finite_component`,
     `VertexOperatorAlgebra.lower_truncated_exists`
2. Added canonical component-membership bridges:
   - `VertexOperatorAlgebra.vacuum_mem_component_zero`
   - `VertexOperatorAlgebra.conformalVector_mem_component_two`
3. Added grading-to-`L(0)` action specializations:
   - `VertexOperatorAlgebra.L0_action_on_component`
   - `VertexOperatorAlgebra.L0_vacuum`
   - `VertexOperatorAlgebra.L0_conformalVector`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 19)

1. Expanded rational/fusion bridge layer in `Modules.lean`:
   - positivity-to-finiteness projection:
     `fusion_rules_finite_of_bounded_pos`
   - pair-bound projections:
     `fusion_rules_bounded_pos_of_pair_left`,
     `fusion_rules_bounded_pos_of_pair_right`
2. Added generic pair-bound constructor:
   - `fusion_rules_bounded_pos_pair_of_bounds`
   which combines two ordered positive bounds into one common positive bound.
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 20)

1. Expanded lattice-fusion bridge layer in `Examples.lean`:
   - finite-bound projections:
     `LatticeVOA.fusion_rules_finite_of_positiveDefinite`,
     `LatticeVOA.fusion_rules_finite_of_rational`
   - swapped-order positive bound projections:
     `LatticeVOA.fusion_rules_bounded_pos_of_positiveDefinite_swapped`,
     `LatticeVOA.fusion_rules_bounded_pos_of_rational_swapped`
2. These bridges now connect lattice criteria directly to both:
   - non-positive finite bounds (`fusion_rules_finite_of_bounded_pos` path)
   - swapped ordered pair bounds (`fusion_rules_bounded_pos_of_pair_right` path)
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 21)

1. Expanded finite-fusion infrastructure in `Modules.lean`:
   - finite-pair assembly from two finite ordered bounds:
     `fusion_rules_finite_pair_of_finite_bounds`
   - finite-pair projection helpers:
     `fusion_rules_finite_of_pair_finite_left`,
     `fusion_rules_finite_of_pair_finite_right`
   - rational swapped-order finiteness wrapper:
     `fusion_rules_finite_of_rational_swapped`
2. Expanded lattice-criteria finite bridge layer in `Examples.lean`:
   - common finite pair bounds:
     `LatticeVOA.fusion_rules_finite_pair_of_positiveDefinite`,
     `LatticeVOA.fusion_rules_finite_pair_of_rational`
   - swapped-order finite bounds:
     `LatticeVOA.fusion_rules_finite_of_positiveDefinite_swapped`,
     `LatticeVOA.fusion_rules_finite_of_rational_swapped`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 22)

1. Expanded Virasoro algebra-level commutator infrastructure in `Virasoro.lean`:
   - diagonal bracket simplification:
     `VirasoroAlgebra.bracket_diag`
   - zero-mode skew bridge:
     `VirasoroAlgebra.bracket_zero_right_eq_neg_bracket_zero_left`
2. Expanded representation-level diagonal/zero specializations:
   - right-hand-side diagonal specialization and applied form:
     `VirasoroRep.virasoro_relation_diag_rhs`,
     `VirasoroRep.virasoro_relation_diag_rhs_apply`
   - double-zero commutator simplifications:
     `VirasoroRep.virasoro_relation_zero_zero`,
     `VirasoroRep.virasoro_relation_zero_zero_apply`
3. Expanded highest-weight/Verma convenience API:
   - `HighestWeightState.annihilation_two`
   - `VermaModule.hw_annihilation_one`
   - `VermaModule.hw_annihilation_two`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Virasoro` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 23)

1. Expanded fusion pair-symmetry infrastructure in `Modules.lean`:
   - positive pair symmetry:
     `fusion_rules_bounded_pos_pair_symm`
   - finite pair symmetry:
     `fusion_rules_finite_pair_symm`
   - rational swapped-orientation pair wrappers:
     `fusion_rules_bounded_pos_pair_of_rational_swapped`,
     `fusion_rules_finite_pair_of_rational_swapped`
2. Expanded lattice bridge layer in `Examples.lean` with swapped-orientation pair wrappers:
   - positive pair wrappers:
     `LatticeVOA.fusion_rules_bounded_pos_pair_of_positiveDefinite_swapped`,
     `LatticeVOA.fusion_rules_bounded_pos_pair_of_rational_swapped`
   - finite pair wrappers:
     `LatticeVOA.fusion_rules_finite_pair_of_positiveDefinite_swapped`,
     `LatticeVOA.fusion_rules_finite_pair_of_rational_swapped`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA.Modules` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 24)

1. Expanded deep fusion-bound conversion infrastructure in `Modules.lean`:
   - finite-to-positive single-bound upgrade:
     `fusion_rules_bounded_pos_of_finite`
   - single-order equivalence:
     `fusion_rules_bounded_pos_iff_finite`
   - finite-to-positive common-pair upgrade:
     `fusion_rules_bounded_pos_pair_of_finite_pair`
   - common-pair equivalence:
     `fusion_rules_bounded_pos_pair_iff_finite_pair`
2. Added rational-specialized equivalence corollaries in `Modules.lean`:
   - `fusion_rules_bounded_pos_iff_finite_of_rational`
   - `fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational`
   - swapped-order analogues:
     `fusion_rules_bounded_pos_iff_finite_of_rational_swapped`,
     `fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational_swapped`
3. Extended lattice bridge layer in `Examples.lean` with equivalence wrappers:
   - `LatticeVOA.fusion_rules_bounded_pos_iff_finite`
   - `LatticeVOA.fusion_rules_bounded_pos_pair_iff_finite_pair`
   - swapped-order wrappers:
     `LatticeVOA.fusion_rules_bounded_pos_iff_finite_swapped`,
     `LatticeVOA.fusion_rules_bounded_pos_pair_iff_finite_pair_swapped`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Modules` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 25)

1. Added super-algebra foundation module `SuperBasic.lean`:
   - parity core (`Parity`, parity add/mul, associativity/commutativity lemmas)
   - Koszul-sign infrastructure:
     `Parity.sign`, `Parity.koszulSign`,
     symmetry and square-to-one lemmas
2. Added super-grading interfaces:
   - `SuperGraded` with parity predicates and dichotomy lemmas
   - `SuperMul` with multiplicative parity compatibility and derived triple-product parity theorem
3. Added fermionic endomorphism infrastructure:
   - graded commutator and anticommutator operators:
     `gradedComm`, `antiComm`
   - CAR mode-family package:
     `CARFamily` with derived off-diagonal and diagonal anticommutator lemmas
4. Integrated super layer into umbrella module:
   - `StringAlgebra/VOA.lean` now imports `StringAlgebra.VOA.SuperBasic`
   - module overview list includes `SuperBasic.lean`
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.SuperBasic` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 26)

1. Added super-formal-distribution bridge module `SuperFormalDistributions.lean`:
   - parity-labeled field wrapper:
     `SuperFormalDistribution`
   - parity-preserving derivative and inherited field-property lemmas
   - even/odd embedding constructors for ordinary formal distributions
2. Added super-locality infrastructure:
   - Koszul-signed mode locality predicate:
     `SuperFormalDistribution.superMutuallyLocal`
   - relation constructor:
     `superMutuallyLocal_of_mode_relation`
   - bridge theorems:
     `superMutuallyLocal_even_even_iff`
     `superMutuallyLocal_odd_odd_iff`
3. Added CAR-to-super-locality bridge:
   - `CARFamily.toFormalDistribution`
   - `CARFamily.superMutuallyLocal_odd_self`
4. Integrated module into umbrella import graph:
   - `StringAlgebra/VOA.lean` now imports
     `StringAlgebra.VOA.SuperFormalDistributions`
   - module overview list includes `SuperFormalDistributions.lean`
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.SuperFormalDistributions` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 27)

1. Expanded example-layer free-fermion infrastructure in `Examples.lean`:
   - added `FreeFermionVOA` structure with explicit `CARFamily` mode package
   - added canonical fermion-field projections:
     `FreeFermionVOA.fermionField`,
     `FreeFermionVOA.fermionSuperField`
2. Added rigorous CAR-derived locality theorems for the free-fermion scaffold:
   - odd super-locality:
     `FreeFermionVOA.fermion_superLocal`
   - eventual mode anticommutativity:
     `FreeFermionVOA.fermion_modes_eventually_anticommute`
3. Integrated super-formal-distribution bridge into examples:
   - `Examples.lean` now imports `StringAlgebra.VOA.SuperFormalDistributions`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 28)

1. Strengthened super-locality theorem layer in `SuperFormalDistributions.lean`:
   - added symmetry theorem:
     `SuperFormalDistribution.superMutuallyLocal_symm`
   - proof uses explicit Koszul-sign involutivity (`s^2 = 1`) at the mode-action level
2. Added explicit CAR anticommutator truncation theorem:
   - `CARFamily.eventual_anticommutator_zero`
   giving concrete eventual anticommutator vanishing above total mode index `1`
3. This deepens the CAR-to-super-locality bridge from existential packaging to
   explicit mode-action vanishing statements.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.SuperFormalDistributions` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 29)

1. Expanded free-boson infrastructure in `Examples.lean`:
   - endomorphism commutator primitive:
     `endComm` with applied-form lemma `endComm_apply`
   - Heisenberg mode realization package:
     `HeisenbergModeFamily`
   - commutator specialization theorems:
     `HeisenbergModeFamily.commutator_offdiag`,
     `HeisenbergModeFamily.commutator_diag`,
     `HeisenbergModeFamily.eventual_commutator_zero`
2. Added algebraic free-boson scaffold:
   - `FreeBosonVOA` with canonical field extraction `FreeBosonVOA.bosonField`
   - derived theorem:
     `FreeBosonVOA.boson_modes_eventually_commute`
3. This complements the prior free-fermion CAR scaffold with a bosonic Heisenberg-mode layer.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 30)

1. Added normalized mode-correlator infrastructure in `Examples.lean`:
   - `ModeVacuumData` with normalized vacuum expectation (`vacuum_norm`)
2. Extended Heisenberg mode layer to explicit two-point identities:
   - `HeisenbergModeFamily.twoPoint`
   - `HeisenbergModeFamily.twoPoint_commutator`
   - `HeisenbergModeFamily.twoPoint_commutator_offdiag`
3. Extended CAR mode layer to explicit two-point identities:
   - `CARFamily.twoPoint`
   - `CARFamily.twoPoint_anticommutator`
   - `CARFamily.twoPoint_anticommutator_offdiag`
4. Added free-theory wrappers/corollaries:
   - boson:
     `FreeBosonVOA.twoPoint`,
     `FreeBosonVOA.twoPoint_commutator`,
     `FreeBosonVOA.twoPoint_commutator_offdiag`,
     `FreeBosonVOA.twoPoint_commutator_diag`
   - fermion:
     `FreeFermionVOA.twoPoint`,
     `FreeFermionVOA.twoPoint_anticommutator`,
     `FreeFermionVOA.twoPoint_anticommutator_offdiag`,
     `FreeFermionVOA.twoPoint_anticommutator_diag`
5. This provides direct algebraic 2-point commutator/anticommutator formulae tied to
   the new free boson/free fermion mode scaffolds.
6. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 31)

1. Connected free-theory mode correlators to the shared `Correlators` API in `Examples.lean`:
   - added import:
     `StringAlgebra.VOA.Correlators`
   - added conversion:
     `ModeVacuumData.toVacuumFunctional` (with explicit vacuum-identification hypothesis)
2. Added bosonic correlator-API bridge theorems:
   - `FreeBosonVOA.twoPoint_eq_twoPointModes_swapped`
   - `FreeBosonVOA.twoPointModes_commutator`
3. Added fermionic correlator-API bridge theorems:
   - `FreeFermionVOA.twoPoint_eq_twoPointModes_swapped`
   - `FreeFermionVOA.twoPointModes_anticommutator`
4. These results make the free boson/free fermion two-point commutator identities
   directly available in `twoPointModes` form (with explicit mode-order conversion).
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 32)

1. Expanded shared correlator algebra in `Correlators.lean`:
   - `twoPointCommutator` and `twoPointAnticommutator` definitions
   - explicit epsilon-form projections:
     `twoPointCommutator_eq`,
     `twoPointAnticommutator_eq`
2. Extended example-layer free-field bridges to use the new correlator primitives:
   - boson:
     `FreeBosonVOA.twoPointCommutator`
   - fermion:
     `FreeFermionVOA.twoPointAnticommutator`
3. This removes mode-order friction when expressing free-field two-point identities
   and gives a canonical commutator/anticommutator API at correlator level.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 33)

1. Added primitive-form free-field correlator corollaries in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointCommutator_primitive`,
     `FreeBosonVOA.twoPointCommutator_primitive_offdiag`,
     `FreeBosonVOA.twoPointCommutator_primitive_diag`
   - fermion:
     `FreeFermionVOA.twoPointAnticommutator_primitive`,
     `FreeFermionVOA.twoPointAnticommutator_primitive_offdiag`,
     `FreeFermionVOA.twoPointAnticommutator_primitive_diag`
2. These theorems expose diagonal/off-diagonal support directly on the shared
   correlator primitives (`twoPointCommutator` / `twoPointAnticommutator`)
   without requiring manual rewriting through `twoPointModes`.
3. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 34)

1. Added mode-to-`nthProduct` extraction lemmas in `FormalDistributions.lean`:
   - `nthProduct_apply_mode_sum`
   - `mode_commutator_eq_nthProduct_sub_apply`
   - `mode_anticommutator_eq_nthProduct_add_apply`
2. Added correlator-level `nthProduct` projection lemmas in `Correlators.lean`:
   - `twoPointCommutator_eq_nthProduct_sub`
   - `twoPointAnticommutator_eq_nthProduct_add`
3. Added free-theory `nthProduct`-evaluation corollaries in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointCommutator_primitive_eq_nthProduct_sub`,
     `FreeBosonVOA.twoPoint_nthProduct_sub_evaluation`
   - fermion:
     `FreeFermionVOA.twoPointAnticommutator_primitive_eq_nthProduct_add`,
     `FreeFermionVOA.twoPoint_nthProduct_add_evaluation`
4. This establishes a direct theorem chain:
   mode (anti)commutator -> `nthProduct` mode-sum expression -> two-point correlator identity.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.FormalDistributions` passes
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 35)

1. Added explicit OPE-to-`nthProduct` compatibility contracts in `FormalDistributions.lean`:
   - `OPECompatibility`
   - access/extraction lemmas:
     `OPECompatibility.coefficient_eq_nthProduct`,
     `OPECompatibility.coefficient_apply_eq_mode_comp`,
     `OPECompatibility.coefficient_apply_mode_sum`
2. This provides a rigorous interface linking OPE singular-coefficient fields to
   concrete mode products, eliminating ambiguity in coefficient extraction semantics.
3. Verified compatibility with correlator and free-field infrastructure:
   - `Correlators.lean` `twoPoint(anti)commutator` `nthProduct` projection lemmas remain green
   - `Examples.lean` free boson/free fermion `nthProduct` evaluation corollaries remain green
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.FormalDistributions` passes
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 36)

1. Added finite-order OPE to correlator extraction layer for free boson models in `Examples.lean`:
   - `FreeBosonVOA.twoPointModes_eq_opeCoefficient`
   - `FreeBosonVOA.twoPointModes_eq_zero_of_ge_opeOrder`
   - model-level wrappers:
     `FreeBosonVOA.twoPoint_eq_opeCoefficient_leftMode`,
     `FreeBosonVOA.twoPoint_eq_zero_of_ge_opeOrder_leftMode`
2. Added finite-order OPE to correlator extraction layer for free fermion models in `Examples.lean`:
   - `FreeFermionVOA.twoPointModes_eq_opeCoefficient`
   - `FreeFermionVOA.twoPointModes_eq_zero_of_ge_opeOrder`
   - model-level wrappers:
     `FreeFermionVOA.twoPoint_eq_opeCoefficient_leftMode`,
     `FreeFermionVOA.twoPoint_eq_zero_of_ge_opeOrder_leftMode`
3. This adds a rigorous theorem pipeline from finite-order OPE data to explicit
   two-point coefficient extraction and high-mode vanishing for both free boson
   and free fermion infrastructures.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 37)

1. Added explicit rigorous CFT assumption bundles in `Examples.lean`:
   - `FreeBosonVOA.CFTData`
   - `FreeFermionVOA.CFTData`
   Each package includes:
   - normalized vacuum data (`ModeVacuumData`) with vacuum identification,
   - finite-order self-OPE witness (`OPEFiniteOrder`) for the distinguished free field.
2. Added packaged extraction APIs (boson and fermion, parallel shape):
   - `CFTData.vacuumFunctional`
   - `CFTData.twoPointCoefficient`
   - `CFTData.twoPointModes_eq_twoPointCoefficient`
   - `CFTData.twoPoint_eq_twoPointCoefficient_leftMode`
   - `CFTData.twoPointModes_eq_zero_of_ge_opeOrder`
   - `CFTData.twoPoint_eq_zero_of_ge_opeOrder_leftMode`
3. This reduces theorem-argument duplication and promotes a reusable, fully explicit
   assumption contract for rigorous free-boson/free-fermion OPE/correlator development.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 38)

1. Strengthened finite-order OPE infrastructure in `FormalDistributions.lean`:
   - `OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply`
   - `OPEFiniteOrder.mode_comp_eq_zero_of_ge`
   These provide explicit high-mode vanishing as vector/endomorphism statements.
2. Added unified piecewise extraction theorem in `Correlators.lean`:
   - `twoPointModes_eq_opeCoefficient_or_zero`
   This gives a single formula:
   - if `j < order`, evaluate via OPE coefficient field;
   - else, correlator mode vanishes.
3. Lifted the piecewise theorem to free-model APIs in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointModes_eq_opeCoefficient_or_zero`,
     `FreeBosonVOA.twoPoint_eq_opeCoefficient_or_zero_leftMode`,
     plus `FreeBosonVOA.CFTData` packaged variants.
   - fermion:
     `FreeFermionVOA.twoPointModes_eq_opeCoefficient_or_zero`,
     `FreeFermionVOA.twoPoint_eq_opeCoefficient_or_zero_leftMode`,
     plus `FreeFermionVOA.CFTData` packaged variants.
4. This closes a rigor gap by exposing finite-order OPE consequences in a complete
   case-split theorem form, avoiding manual theorem branching in downstream arguments.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.FormalDistributions` passes
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 39)

1. Added canonical finite-order OPE coefficient extension in `FormalDistributions.lean`:
   - `OPEFiniteOrder.coefficientOrZero : ℕ → FormalDistribution`
   - structural lemmas:
     `coefficientOrZero_of_lt`,
     `coefficientOrZero_of_ge`,
     `coefficientOrZero_eq_nthProduct`
2. Added mode-level extraction through the canonical extension:
   - `OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum`
   - `OPEFiniteOrder.mode_comp_eq_coefficientOrZero_mode_sum`
3. Added correlator-level canonical extraction in `Correlators.lean`:
   - `twoPointModes_eq_coefficientOrZero`
   expressing two-point mode correlators directly as vacuum expectation values of
   `coefficientOrZero` evaluated at mode `j+n`.
4. Lifted this canonical extraction into free-theory APIs in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointModes_eq_coefficientOrZero`,
     `FreeBosonVOA.twoPoint_eq_coefficientOrZero_leftMode`,
     `FreeBosonVOA.CFTData.twoPointCoefficientOrZero`,
     `FreeBosonVOA.CFTData.twoPointModes_eq_twoPointCoefficientOrZero`,
     `FreeBosonVOA.CFTData.twoPoint_eq_twoPointCoefficientOrZero_leftMode`
   - fermion:
     `FreeFermionVOA.twoPointModes_eq_coefficientOrZero`,
     `FreeFermionVOA.twoPoint_eq_coefficientOrZero_leftMode`,
     `FreeFermionVOA.CFTData.twoPointCoefficientOrZero`,
     `FreeFermionVOA.CFTData.twoPointModes_eq_twoPointCoefficientOrZero`,
     `FreeFermionVOA.CFTData.twoPoint_eq_twoPointCoefficientOrZero_leftMode`
5. This provides a cleaner rigorous interface for downstream proofs by replacing ad hoc
   `if`-splits with a canonical extended coefficient field.
6. Post-expansion check:
   - `lake build StringAlgebra.VOA.FormalDistributions` passes
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 40)

1. Added correlator-level canonical split corollaries in `Correlators.lean`,
   derived from `twoPointModes_eq_coefficientOrZero`:
   - `twoPointModes_eq_opeCoefficient_of_lt`
   - `twoPointModes_eq_zero_of_ge_opeOrder'`
2. Strengthened `CFTData` canonical extension interfaces in `Examples.lean`
   for both free boson and free fermion:
   - `twoPointCoefficientOrZero_eq_twoPointCoefficient_of_lt`
   - `twoPointCoefficientOrZero_eq_zero_of_ge`
   - `twoPointCoefficientOrZero_eq_opeCoefficient_or_zero`
3. This makes the canonical `coefficientOrZero` path fully theorem-complete:
   - strict-lt extraction,
   - ge-order vanishing,
   - piecewise normal form.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 41)

1. Expanded correlator algebra infrastructure in `Correlators.lean`:
   - `twoPointModes` linearity APIs:
     `twoPointModes_smul_left`, `twoPointModes_smul_right`,
     `twoPointModes_neg_left`, `twoPointModes_neg_right`,
     `twoPointModes_sub_left`, `twoPointModes_sub_right`
   - `twoPointCommutator` linearity APIs:
     `twoPointCommutator_add_left`, `twoPointCommutator_add_right`,
     `twoPointCommutator_smul_left`, `twoPointCommutator_smul_right`
   - `twoPointAnticommutator` linearity APIs:
     `twoPointAnticommutator_add_left`, `twoPointAnticommutator_add_right`,
     `twoPointAnticommutator_smul_left`, `twoPointAnticommutator_smul_right`
2. This adds a robust algebraic rewriting layer for correlator expressions,
   reducing manual mode-level expansion in downstream free-field and OPE proofs.
3. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 42)

1. Added cross-orientation high-mode vanishing theorems in `Correlators.lean`:
   - `twoPointCommutator_eq_zero_of_ge_opeOrders`
   - `twoPointAnticommutator_eq_zero_of_ge_opeOrders`
   These require finite-order OPE data in both orientations `(a,b)` and `(b,a)`.
2. Specialized the new vanishing layer to free self-field models in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointCommutator_eq_zero_of_ge_opeOrder_pair`,
     `FreeBosonVOA.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair`
   - fermion:
     `FreeFermionVOA.twoPointCommutator_eq_zero_of_ge_opeOrder_pair`,
     `FreeFermionVOA.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair`
3. Added packaged `CFTData` wrappers for both free models:
   - boson:
     `CFTData.twoPointCommutator_eq_zero_of_ge_opeOrder_pair`,
     `CFTData.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair`
   - fermion:
     `CFTData.twoPointCommutator_eq_zero_of_ge_opeOrder_pair`,
     `CFTData.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair`
4. This closes a practical rigor gap by providing direct high-mode vanishing APIs for
   two-point (anti)commutators at the canonical free-CFT abstraction levels.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 43)

1. Added natural-index coefficient-or-zero expansion theorems in `Correlators.lean`:
   - `twoPointCommutator_eq_coefficientOrZero_sub`
   - `twoPointAnticommutator_eq_coefficientOrZero_add`
   These use finite-order OPE data in both orientations and express (anti)commutators
   as vacuum expectations of explicit coefficient-or-zero combinations.
2. Lifted these formulas to free boson / free fermion interfaces in `Examples.lean`:
   - boson:
     `FreeBosonVOA.twoPointCommutator_eq_coefficientOrZero_sub`,
     `FreeBosonVOA.twoPointAnticommutator_eq_coefficientOrZero_add`
   - fermion:
     `FreeFermionVOA.twoPointCommutator_eq_coefficientOrZero_sub`,
     `FreeFermionVOA.twoPointAnticommutator_eq_coefficientOrZero_add`
3. Added packaged `CFTData` wrappers for both free models:
   - boson:
     `CFTData.twoPointCommutator_eq_twoPointCoefficientOrZero_sub`,
     `CFTData.twoPointAnticommutator_eq_twoPointCoefficientOrZero_add`
   - fermion:
     `CFTData.twoPointCommutator_eq_twoPointCoefficientOrZero_sub`,
     `CFTData.twoPointAnticommutator_eq_twoPointCoefficientOrZero_add`
4. This unifies canonical coefficient extraction and correlator-level (anti)commutator
   identities at the same abstraction layer used for rigorous free-CFT packaging.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 44)

1. Extended finite-order OPE evaluation API in `FormalDistributions.lean`:
   - `OPEFiniteOrder.coefficientOrZero_apply_mode_sum`
   - `OPEFiniteOrder.coefficientOrZero_apply_mode_sum_of_lt`
   - `OPEFiniteOrder.coefficientOrZero_apply_mode_sum_of_ge`
   giving direct mode-sum evaluation of `coefficientOrZero` at all order regimes.
2. Added generic canonical coefficient abstraction in `Correlators.lean`:
   - `twoPointCoefficientOrZero` (correlator-level scalar extraction)
   - bridges and order-split theorems:
     `twoPointModes_eq_twoPointCoefficientOrZero`,
     `twoPointCoefficientOrZero_eq_opeCoefficient_of_lt`,
     `twoPointCoefficientOrZero_eq_zero_of_ge`,
     `twoPointCoefficientOrZero_eq_opeCoefficient_or_zero`
3. Added canonical commutator/anticommutator formulas in terms of generic
   `twoPointCoefficientOrZero` values:
   - `twoPointCommutator_eq_twoPointCoefficientOrZero_sub`
   - `twoPointAnticommutator_eq_twoPointCoefficientOrZero_add`
4. Added coherence lemmas in `Examples.lean` showing packaged free-theory
   `CFTData.twoPointCoefficientOrZero` matches the generic correlator definition:
   - boson: `CFTData.twoPointCoefficientOrZero_eq_generic`
   - fermion: `CFTData.twoPointCoefficientOrZero_eq_generic`
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.FormalDistributions` passes
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`
   - no `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in `StringAlgebra/VOA/*.lean`

## Infrastructure Expansion (2026-02-27, pass 45)

1. Added explicit source provenance in `Correlators.lean`:
   - file-level `## References` section now records the upstream texts used for
     mode/OPE/correlator conventions (Kac, Frenkel-Ben-Zvi, Borcherds).
2. Updated `README.md` for current infrastructure reality:
   - expanded scope list to include `SuperBasic`, `SuperFormalDistributions`,
     and `Correlators`;
   - added planning/notes pointers (`StringAlgebra/VOA/TODO.md`,
     `DEVELOPMENT_PLAN.md`, `RESEARCH_NOTES.md`);
   - refreshed status date to `2026-02-27`.
3. Tightened README audit regex for `axiom`/`admit` to line-anchored forms to
   avoid false positives from comment prose (e.g. "VOAs admit ...").
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean`: `0`
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Infrastructure Expansion (2026-02-27, pass 46)

1. Reference package hardening for correlator rigor review:
   - downloaded canonical primary paper:
     `references/borcherds-1986-vertex-algebras-kac-moody-monster.pdf`
     from Borcherds' Berkeley papers index (`va/va.pdf`);
   - downloaded open Frenkel reference used for VA/OPE formulas:
     `references/frenkel-bourbaki-vertex-algebras-and-algebraic-curves-2000.pdf`.
2. Performed direct text extraction checks (`read_references.py`) focused on:
   - vacuum/translation/locality axiom shape;
   - associativity/OPE identity;
   - mode-commutator extraction from OPE singular terms;
   - n-point correlation-function proposition.
3. Added a dedicated source-validation section to `RESEARCH_NOTES.md`:
   - `### F. Correlator/OPE Core References (Direct Verification, 2026-02-27)`.
   This records exactly what was verified and where current implementation still
   falls short of full Jacobi/Borcherds-level realization.
4. Availability tracking:
   - AMS endpoints for full monographs (`Kac`/`Frenkel-Ben-Zvi` book editions)
     returned access restrictions (403/redirect), so open primary alternatives were used
     for formula-level verification.

## Infrastructure Expansion (2026-02-27, pass 47)

1. Extended `Correlators.lean` with explicit 3-point first-pair (anti)commutator infrastructure:
   - new primitives:
     `threePointCommutator12`,
     `threePointAnticommutator12`
   - canonical expansions:
     `threePointCommutator12_eq`,
     `threePointAnticommutator12_eq`,
     `threePointCommutator12_eq_nthProduct_sub`,
     `threePointAnticommutator12_eq_nthProduct_add`
   - finite-order OPE extraction + high-mode vanishing:
     `threePointCommutator12_eq_coefficientOrZero_sub`,
     `threePointAnticommutator12_eq_coefficientOrZero_add`,
     `threePointCommutator12_eq_zero_of_ge_opeOrders`,
     `threePointAnticommutator12_eq_zero_of_ge_opeOrders`.
2. Added free-model wrappers in `Examples.lean` for both boson and fermion:
   - `FreeBosonVOA.*`:
     `threePointCommutator12_eq_coefficientOrZero_sub`,
     `threePointAnticommutator12_eq_coefficientOrZero_add`,
     `threePointCommutator12_eq_zero_of_ge_opeOrder_pair`,
     `threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair`
   - `FreeFermionVOA.*`:
     `threePointCommutator12_eq_coefficientOrZero_sub`,
     `threePointAnticommutator12_eq_coefficientOrZero_add`,
     `threePointCommutator12_eq_zero_of_ge_opeOrder_pair`,
     `threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair`.
3. Added packaged `CFTData`-level wrappers for the same 3-point theorem family:
   - boson `CFTData.*` and fermion `CFTData.*` each now expose
     `threePointCommutator12_eq_coefficientOrZero_sub`,
     `threePointAnticommutator12_eq_coefficientOrZero_add`,
     `threePointCommutator12_eq_zero_of_ge_opeOrder_pair`,
     `threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair`.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean`: `0`
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Infrastructure Expansion (2026-02-27, pass 48)

1. Extended `Correlators.lean` with mixed-regime three-point first-pair extraction
   theorems (`lt/ge` combinations) for both commutator and anticommutator:
   - strict-below-order extraction:
     `threePointCommutator12_eq_opeCoefficient_sub_of_lt`,
     `threePointAnticommutator12_eq_opeCoefficient_add_of_lt`
   - mixed-order extraction:
     `threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right`,
     `threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right`,
     `threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right`,
     `threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right`.
2. Added free-boson wrappers in `Examples.lean` for the new mixed-regime family:
   - `FreeBosonVOA.*` now exposes all six theorem names above specialized to
     `bosonField` self-OPE data.
3. Added free-fermion wrappers in `Examples.lean` for the same mixed-regime
   family:
   - `FreeFermionVOA.*` now exposes all six theorem names above specialized to
     `fermionField` self-OPE data.
4. Added packaged `CFTData` wrappers (both boson and fermion):
   - `FreeBosonVOA.CFTData.*` and `FreeFermionVOA.CFTData.*` each now include
     the six mixed-regime theorem forms for first-pair three-point
     commutator/anticommutator extraction.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count command
     `rg -n '^\\s*sorry\\b' StringAlgebra/VOA --glob '*.lean'`
     returns no matches
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Infrastructure Expansion (2026-02-27, pass 49)

1. Extended `Correlators.lean` with full 3-point last-pair `(2,3)` infrastructure:
   - new primitives:
     `threePointCommutator23`,
     `threePointAnticommutator23`
   - canonical expansions:
     `threePointCommutator23_eq`,
     `threePointAnticommutator23_eq`,
     `threePointCommutator23_eq_nthProduct_sub`,
     `threePointAnticommutator23_eq_nthProduct_add`
   - finite-order OPE extraction + high-mode vanishing:
     `threePointCommutator23_eq_coefficientOrZero_sub`,
     `threePointAnticommutator23_eq_coefficientOrZero_add`,
     `threePointCommutator23_eq_zero_of_ge_opeOrders`,
     `threePointAnticommutator23_eq_zero_of_ge_opeOrders`
   - strict/mixed order extraction family:
     `threePointCommutator23_eq_opeCoefficient_sub_of_lt`,
     `threePointAnticommutator23_eq_opeCoefficient_add_of_lt`,
     `threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k`,
     `threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k`.
2. Added free-model wrapper families in `Examples.lean` for pair `(2,3)`:
   - `FreeBosonVOA.*`:
     coefficient-or-zero, high-mode vanishing, strict-below extraction,
     and mixed-regime extraction for all six theorem forms above.
   - `FreeFermionVOA.*`:
     the same theorem family specialized to `fermionField`.
3. Added packaged `CFTData` wrappers for pair `(2,3)`:
   - `FreeBosonVOA.CFTData.*` and `FreeFermionVOA.CFTData.*` now each expose:
     `threePointCommutator23_eq_coefficientOrZero_sub`,
     `threePointAnticommutator23_eq_coefficientOrZero_add`,
     `threePointCommutator23_eq_zero_of_ge_opeOrder_pair`,
     `threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair`,
     `threePointCommutator23_eq_opeCoefficient_sub_of_lt`,
     `threePointAnticommutator23_eq_opeCoefficient_add_of_lt`,
     `threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k`,
     `threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k`.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count command
     `rg -n '^\\s*sorry\\b' StringAlgebra/VOA --glob '*.lean'`
     returns no matches
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Infrastructure Expansion (2026-02-27, pass 50)

1. Completed pairwise 3-point correlator core by adding the missing first/third
   insertion family in `Correlators.lean`:
   - new primitives:
     `threePointCommutator13`,
     `threePointAnticommutator13`
   - canonical expansions:
     `threePointCommutator13_eq`,
     `threePointAnticommutator13_eq`
2. Added finite-order OPE extraction for pair `(1,3)` using middle-field OPE
   data in both channels `(b,a)` and `(b,c)`:
   - `threePointCommutator13_eq_coefficientOrZero_sub`,
   - `threePointAnticommutator13_eq_coefficientOrZero_add`.
3. Added high-mode vanishing for pair `(1,3)` when the middle index is above
   both relevant OPE orders:
   - `threePointCommutator13_eq_zero_of_ge_opeOrders`,
   - `threePointAnticommutator13_eq_zero_of_ge_opeOrders`.
4. Added strict/mixed index extraction family for pair `(1,3)`:
   - strict-below extraction:
     `threePointCommutator13_eq_opeCoefficient_sub_of_lt`,
     `threePointAnticommutator13_eq_opeCoefficient_add_of_lt`;
   - mixed regimes:
     `threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`,
     `threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`.
5. Post-expansion check:
   - `lake build StringAlgebra.VOA.Correlators` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count command
     `rg -n '^\\s*sorry\\b' StringAlgebra/VOA --glob '*.lean'`
     returns no matches
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Infrastructure Expansion (2026-02-27, pass 51)

1. Extended `Examples.lean` with pair `(1,3)` theorem wrappers for both free
   theories, using explicit middle-channel OPE assumptions:
   - `FreeBosonVOA.*` now exposes:
     `threePointCommutator13_eq_coefficientOrZero_sub`,
     `threePointAnticommutator13_eq_coefficientOrZero_add`,
     `threePointCommutator13_eq_zero_of_ge_opeOrders`,
     `threePointAnticommutator13_eq_zero_of_ge_opeOrders`,
     `threePointCommutator13_eq_opeCoefficient_sub_of_lt`,
     `threePointAnticommutator13_eq_opeCoefficient_add_of_lt`,
     `threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`,
     `threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`.
2. Added the same pair `(1,3)` wrapper family for fermions:
   - `FreeFermionVOA.*` exposes the corresponding ten theorem names above,
     replacing `bosonField` with `fermionField`.
3. Design note:
   - pair `(1,3)` extraction depends on OPE data for the middle field against
     the first/third fields, so wrappers are parameterized by explicit
     middle-channel witnesses (`Oba`, `Obc`) instead of reusing only the
     packaged self-OPE witness.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA.Examples` passes
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count command
     `rg -n '^\\s*sorry\\b' StringAlgebra/VOA --glob '*.lean'`
     returns no matches
   - strict audit command
     `rg -n "^[[:space:]]*axiom\\b|^[[:space:]]*admit\\b|Classical\\.choose|Classical\\.epsilon" StringAlgebra/VOA --glob '*.lean'`
     returns no matches

## Free CFT Development Plan (2026-02-27)

Goal: full rigorous free-boson and free-fermion CFT formalization at the OPE/correlator layer.

### Phase A (Completed Core)

1. Algebraic free-model scaffolds:
   - `FreeBosonVOA`, `FreeFermionVOA`
   - `ModeVacuumData`
2. OPE/correlator bridge infrastructure:
   - finite-order OPE package `OPEFiniteOrder`
   - canonical extension `coefficientOrZero`
   - correlator extraction APIs (`twoPointModes`, `twoPointCoefficientOrZero`, commutator/anticommutator forms)
3. Packaged free-model assumptions:
   - `FreeBosonVOA.CFTData`
   - `FreeFermionVOA.CFTData`

### Phase B (Next Milestones)

1. Construct explicit finite-order self-OPE witnesses for canonical free fields:
   - boson: Heisenberg normalization -> explicit singular-part order/data
   - fermion: CAR normalization -> explicit singular-part order/data
2. Derive canonical closed-form 2-point (anti)commutator identities directly from those witnesses,
   minimizing manual case splits via canonical coefficient APIs.
3. Add mixed-regime theorem families (`lt/ge` combinations) at free-model package level for
   both commutator and anticommutator correlators.

### Phase C (Rigor Completion Targets)

1. Upgrade from witness-driven free-field assumptions to construction-driven witnesses
   where available in current infrastructure.
2. Extend from 2-point to 3-point and higher mode-correlator APIs with compatible OPE
   extraction/vanishing patterns.
3. Connect free-field OPE/correlator interfaces to module/intertwiner layers by explicit
   transport lemmas (no implicit assumption wrappers).

### Acceptance Gates

1. `lake build StringAlgebra.VOA` must pass.
2. `StringAlgebra/VOA/*.lean` remains `sorry`-free.
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon`.
4. New free-CFT claims must be backed by explicit witness data or derived theorem chains.

## VOA Dependency Graph

```text
Basic
  -> SuperBasic
  -> FormalDistributions
  -> SuperFormalDistributions
  -> VertexAlgebra
  -> Virasoro
  -> Modules
  -> Correlators
  -> Examples

Detailed edge chain:
Basic -> SuperBasic
Basic -> FormalDistributions -> VertexAlgebra -> Virasoro -> Modules -> Examples
Basic -> FormalDistributions -> VertexAlgebra -> Correlators
Basic -> FormalDistributions -> VertexAlgebra -> Correlators -> Examples
Basic -> FormalDistributions -> SuperFormalDistributions
Basic -> FormalDistributions -> SuperFormalDistributions -> Examples
```

## Theorem Flow Toward Representation/Fusion Layer

```text
Formal-distribution locality/OPE interfaces
-> vertex algebra axioms (vacuum/translation/locality)
-> conformal/Virasoro structures
-> module/intertwining/fusion interfaces
-> example families (Heisenberg, affine, lattice, moonshine)
```

## Audit Matrix

1. `Basic.lean`: low risk. Formal Laurent-series infrastructure is explicit and stable.
2. `FormalDistributions.lean`: medium risk. Locality/OPE interfaces are explicit; full Borcherds/Dong closure is still witness-driven.
3. `VertexAlgebra.lean`: medium risk. Core axioms are explicit; conformal-weight extraction now uses explicit grading witnesses.
4. `Virasoro.lean`: medium risk. Virasoro and minimal-model interfaces are explicit; full representation-theoretic closure remains pending.
5. `Modules.lean`: medium-high risk. Module/fusion structures are explicit; fusion finiteness now has positive finite-bound theorems, while complete reducibility and deeper fusion semantics still need stronger derived closure theorems.
6. `Examples.lean`: medium-high risk. Example families are explicit and type-safe; lattice rationality criteria now include explicit forward/backward implication lemmas, while deeper construction-specific theorem derivations are pending.

## Open Work Packages

### WP1 - Jacobi/Borcherds Internalization

Targets: `FormalDistributions.lean`, `VertexAlgebra.lean`

1. Replace coefficient-model simplifications with progressively richer Jacobi/Borcherds formulations.
2. Internalize Dong-lemma closure from explicit witness contracts to derived lemmas where feasible.
3. Strengthen locality/OPE compatibility theorems beyond mode-level commutation shells.

### WP2 - Conformal/Virasoro Closure

Targets: `VertexAlgebra.lean`, `Virasoro.lean`

1. Expand explicit `L(0)` grading witness usage across conformal-dependent APIs.
2. Add additional derived Virasoro-mode identities from the scaled commutator axiom.
3. Tighten primary-state interfaces with more derived consequences.

### WP3 - Module/Fusion Semantics

Target: `Modules.lean`

1. Strengthen complete-reducibility interfaces toward semisimple decomposition witnesses.
2. Add explicit compatibility contracts between intertwining operators and VOA actions.
3. Improve fusion-finiteness statements from tautological bounds to representation-theoretic bounds where infrastructure exists.

### WP4 - Example Realization Depth

Target: `Examples.lean`

1. Refine each example section with construction-level assumptions and derived consequences.
2. Keep rationality/classification claims tied to explicit criteria data, not informal naming.
3. Connect example statements to module/fusion interfaces by explicit lemmas.

## Anti-Smuggling Gates

1. No `axiom`.
2. No `sorry`.
3. No fabricated outputs in core algebra/module operations.
4. Any external assumption contract must be explicit and minimal.
