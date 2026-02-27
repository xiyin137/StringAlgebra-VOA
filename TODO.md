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
   - `sorry`/`axiom`/`admit`/hidden-choice audit counts remain zero
   - explicit assumption-package classes are now part of the intended interface surface

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

1. Expanded one-point correlator infrastructure in `Correlators.lean`:
   - added mode/state specializations:
     `onePointModes`, `onePointStateModes`
   - added direct evaluation forms:
     `onePointModes_eq`, `onePointStateModes_eq`
2. Added one-point vacuum/creation consequences:
   - positive-mode vanishing from creation:
     `onePointStateModes_eq_zero_of_nat`
   - mode `-1` extraction and vacuum Kronecker form:
     `onePointStateModes_minus_one`,
     `onePointVacuumModes_eq_ite`,
     `onePointVacuumModes_minus_one`,
     `onePointVacuumModes_eq_zero_of_ne`
3. Added two-point reductions with vacuum insertions:
   - piecewise reductions to one-point correlators:
     `twoPointModes_vacuum_left_eq`,
     `twoPointModes_vacuum_right_eq`
   - mode-`-1` and off-`-1` simplifications:
     `twoPointModes_vacuum_left_minus_one`,
     `twoPointModes_vacuum_left_eq_zero_of_ne`,
     `twoPointModes_vacuum_right_minus_one`,
     `twoPointModes_vacuum_right_eq_zero_of_ne`
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 22)

1. Expanded three-point correlator vacuum-reduction API in `Correlators.lean`:
   - piecewise reductions by insertion slot:
     `threePointModes_vacuum_left_eq`,
     `threePointModes_vacuum_middle_eq`,
     `threePointModes_vacuum_right_eq`
2. Added mode-`-1` simplification and off-`-1` vanishing corollaries:
   - left slot:
     `threePointModes_vacuum_left_minus_one`,
     `threePointModes_vacuum_left_eq_zero_of_ne`
   - middle slot:
     `threePointModes_vacuum_middle_minus_one`,
     `threePointModes_vacuum_middle_eq_zero_of_ne`
   - right slot:
     `threePointModes_vacuum_right_minus_one`,
     `threePointModes_vacuum_right_eq_zero_of_ne`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 23)

1. Added state-level correlator wrappers in `Correlators.lean`:
   - `twoPointStateModes`, `threePointStateModes`
   - direct evaluation forms:
     `twoPointStateModes_eq`, `threePointStateModes_eq`
2. Added first-mode creation consequences for state insertions:
   - `twoPointStateModes_eq_zero_of_nat_left`
   - `threePointStateModes_eq_zero_of_nat_left`
3. Added state-level vacuum-reduction API:
   - two-point:
     `twoPointStateModes_vacuum_left_eq`,
     `twoPointStateModes_vacuum_right_eq`,
     plus mode-`-1` and off-`-1` corollaries
   - three-point:
     `threePointStateModes_vacuum_left_eq`,
     `threePointStateModes_vacuum_middle_eq`,
     `threePointStateModes_vacuum_right_eq`,
     plus mode-`-1` and off-`-1` corollaries
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 24)

1. Added state-level two-point commutator/anticommutator definitions in `Correlators.lean`:
   - `twoPointStateCommutator`, `twoPointStateAnticommutator`
   - state-form expansion lemmas:
     `twoPointStateCommutator_eq`,
     `twoPointStateAnticommutator_eq`,
     `twoPointStateCommutator_eq_apply`,
     `twoPointStateAnticommutator_eq_apply`
2. Added state-level OPE-regime wrappers for two-point commutator/anticommutator:
   - at/above-order vanishing:
     `twoPointStateCommutator_eq_zero_of_ge_opeOrders`,
     `twoPointStateAnticommutator_eq_zero_of_ge_opeOrders`
   - coefficient-or-zero forms:
     `twoPointStateCommutator_eq_twoPointCoefficientOrZero_sub`,
     `twoPointStateAnticommutator_eq_twoPointCoefficientOrZero_add`
   - strict-below extraction:
     `twoPointStateCommutator_eq_opeCoefficient_sub_of_lt`,
     `twoPointStateAnticommutator_eq_opeCoefficient_add_of_lt`
   - mixed-regime extraction:
     `twoPointStateCommutator_eq_opeCoefficient_of_ge_left_lt_right`,
     `twoPointStateAnticommutator_eq_opeCoefficient_of_ge_left_lt_right`,
     `twoPointStateCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right`,
     `twoPointStateAnticommutator_eq_opeCoefficient_of_lt_left_ge_right`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 25)

1. Added state-level three-point commutator/anticommutator wrappers in `Correlators.lean`:
   - pair `(1,2)`:
     `threePointStateCommutator12`, `threePointStateAnticommutator12`
     with expansion/apply lemmas:
     `threePointStateCommutator12_eq`,
     `threePointStateAnticommutator12_eq`,
     `threePointStateCommutator12_eq_apply`,
     `threePointStateAnticommutator12_eq_apply`
   - pair `(2,3)`:
     `threePointStateCommutator23`, `threePointStateAnticommutator23`
     with expansion lemmas:
     `threePointStateCommutator23_eq`,
     `threePointStateAnticommutator23_eq`
   - pair `(1,3)`:
     `threePointStateCommutator13`, `threePointStateAnticommutator13`
     with expansion lemmas:
     `threePointStateCommutator13_eq`,
     `threePointStateAnticommutator13_eq`
2. Added state-level OPE-regime wrappers for the three-point `(1,2)` family:
   - coefficient-or-zero forms:
     `threePointStateCommutator12_eq_coefficientOrZero_sub`,
     `threePointStateAnticommutator12_eq_coefficientOrZero_add`
   - at/above-order vanishing:
     `threePointStateCommutator12_eq_zero_of_ge_opeOrders`,
     `threePointStateAnticommutator12_eq_zero_of_ge_opeOrders`
   - strict-below extraction:
     `threePointStateCommutator12_eq_opeCoefficient_sub_of_lt`,
     `threePointStateAnticommutator12_eq_opeCoefficient_add_of_lt`
   - mixed-regime extraction:
     `threePointStateCommutator12_eq_opeCoefficient_of_ge_left_lt_right`,
     `threePointStateAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right`,
     `threePointStateCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right`,
     `threePointStateAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 26)

1. Completed state-level OPE-regime wrappers for the remaining three-point commutator families in `Correlators.lean`:
   - pair `(2,3)` wrappers:
     `threePointStateCommutator23_eq_coefficientOrZero_sub`,
     `threePointStateAnticommutator23_eq_coefficientOrZero_add`,
     `threePointStateCommutator23_eq_zero_of_ge_opeOrders`,
     `threePointStateAnticommutator23_eq_zero_of_ge_opeOrders`,
     `threePointStateCommutator23_eq_opeCoefficient_sub_of_lt`,
     `threePointStateAnticommutator23_eq_opeCoefficient_add_of_lt`,
     `threePointStateCommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointStateAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k`,
     `threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k`,
     `threePointStateAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k`
   - pair `(1,3)` wrappers:
     `threePointStateCommutator13_eq_coefficientOrZero_sub`,
     `threePointStateAnticommutator13_eq_coefficientOrZero_add`,
     `threePointStateCommutator13_eq_zero_of_ge_opeOrders`,
     `threePointStateAnticommutator13_eq_zero_of_ge_opeOrders`,
     `threePointStateCommutator13_eq_opeCoefficient_sub_of_lt`,
     `threePointStateAnticommutator13_eq_opeCoefficient_add_of_lt`,
     `threePointStateCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointStateAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc`,
     `threePointStateCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`,
     `threePointStateAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc`
2. With this pass, all three commutator pair families `(1,2)`, `(2,3)`, `(1,3)` now have state-level OPE-regime APIs mirroring the established mode-level theorem families.
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 27)

1. Expanded state-level commutator/anticommutator simplification API in `Correlators.lean`:
   - three-point pair `(2,3)` apply forms:
     `threePointStateCommutator23_eq_apply`,
     `threePointStateAnticommutator23_eq_apply`
   - three-point pair `(1,3)` apply forms:
     `threePointStateCommutator13_eq_apply`,
     `threePointStateAnticommutator13_eq_apply`
2. Added state-level `nthProduct` wrappers in `Correlators.lean`:
   - three-point pair `(1,2)`:
     `threePointStateCommutator12_eq_nthProduct_sub`,
     `threePointStateAnticommutator12_eq_nthProduct_add`
   - three-point pair `(2,3)`:
     `threePointStateCommutator23_eq_nthProduct_sub`,
     `threePointStateAnticommutator23_eq_nthProduct_add`
   - two-point commutator/anticommutator:
     `twoPointStateCommutator_eq_nthProduct_sub`,
     `twoPointStateAnticommutator_eq_nthProduct_add`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 28)

1. Completed `(1,3)` `nthProduct` commutator/anticommutator layer in `Correlators.lean`:
   - mode-level middle-insertion `nthProduct` forms:
     `threePointCommutator13_eq_nthProduct_sub`,
     `threePointAnticommutator13_eq_nthProduct_add`
   - state-level wrappers:
     `threePointStateCommutator13_eq_nthProduct_sub`,
     `threePointStateAnticommutator13_eq_nthProduct_add`
2. Added state-level two-point extended-coefficient wrappers in `Correlators.lean`:
   - `twoPointStateCommutator_eq_coefficientOrZero_sub`
   - `twoPointStateAnticommutator_eq_coefficientOrZero_add`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 29)

1. Added state-level two-point mode OPE extraction wrappers in `Correlators.lean`:
   - coefficient extraction / vanishing / piecewise:
     `twoPointStateModes_eq_opeCoefficient`,
     `twoPointStateModes_eq_zero_of_ge_opeOrder`,
     `twoPointStateModes_eq_opeCoefficient_or_zero`
   - `coefficientOrZero` and canonical-value forms:
     `twoPointStateModes_eq_coefficientOrZero`,
     `twoPointStateModes_eq_twoPointCoefficientOrZero`
   - strict cutoff specializations:
     `twoPointStateModes_eq_opeCoefficient_of_lt`,
     `twoPointStateModes_eq_zero_of_ge_opeOrder'`
2. With this pass, the two-point mode OPE API now has direct state-level wrappers parallel to the formal-distribution layer.
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 30)

1. Added state-level linearity wrappers for point correlators in `Correlators.lean`,
   using explicit state-field compatibility hypotheses (`Y` preserving `add/smul/neg/sub`)
   where required:
   - three-point state-mode layer:
     `threePointStateModes_add_left`,
     `threePointStateModes_add_middle`,
     `threePointStateModes_add_right`,
     `threePointStateModes_smul_left`,
     `threePointStateModes_smul_middle`,
     `threePointStateModes_smul_right`,
     `threePointStateModes_neg_left`,
     `threePointStateModes_neg_middle`,
     `threePointStateModes_neg_right`,
     `threePointStateModes_sub_left`,
     `threePointStateModes_sub_middle`,
     `threePointStateModes_sub_right`
   - two-point state-mode layer:
     `twoPointStateModes_add_left`,
     `twoPointStateModes_add_right`,
     `twoPointStateModes_smul_left`,
     `twoPointStateModes_smul_right`,
     `twoPointStateModes_neg_left`,
     `twoPointStateModes_neg_right`,
     `twoPointStateModes_sub_left`,
     `twoPointStateModes_sub_right`
2. Added state-level two-point commutator/anticommutator linearity wrappers
   under the same explicit `Y`-compatibility hypotheses:
   - commutator:
     `twoPointStateCommutator_add_left`,
     `twoPointStateCommutator_add_right`,
     `twoPointStateCommutator_smul_left`,
     `twoPointStateCommutator_smul_right`
   - anticommutator:
     `twoPointStateAnticommutator_add_left`,
     `twoPointStateAnticommutator_add_right`,
     `twoPointStateAnticommutator_smul_left`,
     `twoPointStateAnticommutator_smul_right`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 31)

1. Completed two-point commutator/anticommutator linearity families in `Correlators.lean`
   by adding missing negation/subtraction lemmas at the formal-distribution level:
   - commutator:
     `twoPointCommutator_neg_left`,
     `twoPointCommutator_neg_right`,
     `twoPointCommutator_sub_left`,
     `twoPointCommutator_sub_right`
   - anticommutator:
     `twoPointAnticommutator_neg_left`,
     `twoPointAnticommutator_neg_right`,
     `twoPointAnticommutator_sub_left`,
     `twoPointAnticommutator_sub_right`
2. Added matching state-level wrappers under explicit state-field compatibility hypotheses
   (`Y` preserving `neg/sub`):
   - commutator:
     `twoPointStateCommutator_neg_left`,
     `twoPointStateCommutator_neg_right`,
     `twoPointStateCommutator_sub_left`,
     `twoPointStateCommutator_sub_right`
   - anticommutator:
     `twoPointStateAnticommutator_neg_left`,
     `twoPointStateAnticommutator_neg_right`,
     `twoPointStateAnticommutator_sub_left`,
     `twoPointStateAnticommutator_sub_right`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 32)

1. Added complete linearity API (`add/smul/neg/sub`) for the three-point
   `(1,2)` commutator and anticommutator families in `Correlators.lean`:
   - formal-distribution layer:
     `threePointCommutator12_*` and `threePointAnticommutator12_*`
     with left/middle/right variants for all four operations
2. Added matching state-level `(1,2)` commutator/anticommutator wrappers under
   explicit `Y`-compatibility hypotheses (`Y` preserving `add/smul/neg/sub`):
   - `threePointStateCommutator12_*`
   - `threePointStateAnticommutator12_*`
   (left/middle/right variants for all four operations)
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 33)

1. Added three-point `(2,3)` commutator/anticommutator linearity core in
   `Correlators.lean`:
   - formal-distribution layer (`add/smul`, left/middle/right):
     `threePointCommutator23_add_left`,
     `threePointCommutator23_add_middle`,
     `threePointCommutator23_add_right`,
     `threePointCommutator23_smul_left`,
     `threePointCommutator23_smul_middle`,
     `threePointCommutator23_smul_right`,
     `threePointAnticommutator23_add_left`,
     `threePointAnticommutator23_add_middle`,
     `threePointAnticommutator23_add_right`,
     `threePointAnticommutator23_smul_left`,
     `threePointAnticommutator23_smul_middle`,
     `threePointAnticommutator23_smul_right`
2. Added matching state-level `(2,3)` wrappers with explicit `Y`-compatibility
   hypotheses:
   - `threePointStateCommutator23_add_*` and `threePointStateCommutator23_smul_*`
   - `threePointStateAnticommutator23_add_*` and `threePointStateAnticommutator23_smul_*`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 34)

1. Completed three-point `(2,3)` commutator/anticommutator linearity families in
   `Correlators.lean` by adding the missing negation/subtraction layer:
   - formal-distribution layer:
     `threePointCommutator23_neg_*`, `threePointCommutator23_sub_*`,
     `threePointAnticommutator23_neg_*`, `threePointAnticommutator23_sub_*`
     (left/middle/right variants)
2. Added matching state-level `(2,3)` negation/subtraction wrappers under explicit
   `Y`-compatibility hypotheses (`Y` preserving `neg/sub`):
   - `threePointStateCommutator23_neg_*`, `threePointStateCommutator23_sub_*`
   - `threePointStateAnticommutator23_neg_*`, `threePointStateAnticommutator23_sub_*`
   (left/middle/right variants)
3. With passes 33-34 together, `(2,3)` now has full `add/smul/neg/sub` linearity
   coverage at both formal and state levels.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 35)

1. Added three-point `(1,3)` commutator/anticommutator linearity core in
   `Correlators.lean`:
   - formal-distribution layer (`add/smul`, left/middle/right):
     `threePointCommutator13_add_*`,
     `threePointCommutator13_smul_*`,
     `threePointAnticommutator13_add_*`,
     `threePointAnticommutator13_smul_*`
2. Added matching state-level `(1,3)` wrappers with explicit `Y`-compatibility
   hypotheses:
   - `threePointStateCommutator13_add_*` and `threePointStateCommutator13_smul_*`
   - `threePointStateAnticommutator13_add_*` and `threePointStateAnticommutator13_smul_*`
3. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## Infrastructure Expansion (2026-02-27, pass 36)

1. Completed three-point `(1,3)` commutator/anticommutator linearity families in
   `Correlators.lean` by adding the missing negation/subtraction layer:
   - formal-distribution layer:
     `threePointCommutator13_neg_*`, `threePointCommutator13_sub_*`,
     `threePointAnticommutator13_neg_*`, `threePointAnticommutator13_sub_*`
     (left/middle/right variants)
2. Added matching state-level `(1,3)` negation/subtraction wrappers under explicit
   `Y`-compatibility hypotheses (`Y` preserving `neg/sub`):
   - `threePointStateCommutator13_neg_*`, `threePointStateCommutator13_sub_*`
   - `threePointStateAnticommutator13_neg_*`, `threePointStateAnticommutator13_sub_*`
   (left/middle/right variants)
3. With passes 35-36 together, `(1,3)` now has full `add/smul/neg/sub` linearity
   coverage at both formal and state levels.
4. Post-expansion check:
   - `lake build StringAlgebra.VOA` passes
   - theorem-level `sorry` count in `StringAlgebra/VOA/*.lean` remains `0`

## VOA Dependency Graph

```text
Basic
  -> FormalDistributions
  -> VertexAlgebra
  -> Virasoro
  -> Modules
  -> Examples

Detailed edge chain:
Basic -> FormalDistributions -> VertexAlgebra -> Virasoro -> Modules -> Examples
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
