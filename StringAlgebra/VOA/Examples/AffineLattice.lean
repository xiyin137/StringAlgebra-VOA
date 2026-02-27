/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Examples.Boson

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Affine VOA

The VOA V_k(𝔤) associated to an affine Lie algebra ĝ at level k.
-/

/-- Data for an affine Lie algebra -/
structure AffineLieAlgebraData (R : Type*) [CommRing R] where
  /-- Dimension of the simple Lie algebra g -/
  dim : ℕ
  /-- The level k -/
  level : R
  /-- The dual Coxeter number h^∨ -/
  dualCoxeter : R
  /-- Structure constants f^{abc} -/
  structureConstants : Fin dim → Fin dim → Fin dim → R
  /-- Killing form κ_{ab} -/
  killingForm : Fin dim → Fin dim → R

/-- The affine VOA V_k(𝔤) at level k -/
structure AffineVOA (R : Type*) [CommRing R] where
  /-- The affine Lie algebra data -/
  data : AffineLieAlgebraData R
  /-- Non-critical level condition: k ≠ -h^∨ -/
  non_critical : data.level + data.dualCoxeter ≠ 0

namespace AffineVOA

variable {R : Type*} [CommRing R]

end AffineVOA

/-! ## Lattice VOA

The VOA V_L associated to an even integral lattice L.
-/

/-- An even integral lattice -/
structure EvenLattice (R : Type*) [CommRing R] where
  /-- The rank of the lattice -/
  rank : ℕ
  /-- The bilinear form ⟨·,·⟩: L × L → ℤ -/
  bilinearForm : Fin rank → Fin rank → ℤ
  /-- Symmetry -/
  symmetric : ∀ i j, bilinearForm i j = bilinearForm j i
  /-- Even: ⟨α, α⟩ ∈ 2ℤ for all α -/
  even : ∀ i, 2 ∣ bilinearForm i i

/-- The lattice VOA V_L -/
structure LatticeVOA (R : Type*) [CommRing R] where
  /-- The even lattice -/
  lattice : EvenLattice R

namespace LatticeVOA

variable {R : Type*} [CommRing R]

universe uC

/-- The central charge equals the rank: c = rank(L) -/
def centralCharge (V : LatticeVOA R) : R := V.lattice.rank

/-- Positivity predicate for the underlying lattice form. -/
def positiveDefinite (V : LatticeVOA R) : Prop :=
  ∀ i, 0 < V.lattice.bilinearForm i i

/-- Explicit rationality criterion package for lattice VOAs. -/
structure RationalityCriterion (V : LatticeVOA R) where
  /-- Rationality predicate for the VOA model. -/
  rational : Prop
  /-- Rationality is equivalent to positive definiteness of the lattice form. -/
  iff_positive_definite : rational ↔ positiveDefinite V

/-- Forward implication from an explicit rationality criterion package. -/
theorem rational_of_positiveDefinite {V : LatticeVOA R}
    (criterion : RationalityCriterion (R := R) V)
    (hpos : positiveDefinite V) : criterion.rational :=
  criterion.iff_positive_definite.mpr hpos

/-- Backward implication from an explicit rationality criterion package. -/
theorem positiveDefinite_of_rational {V : LatticeVOA R}
    (criterion : RationalityCriterion (R := R) V)
    (hrat : criterion.rational) : positiveDefinite V :=
  criterion.iff_positive_definite.mp hrat

/-- Accessor form of the lattice rationality criterion equivalence. -/
theorem rational_iff_positiveDefinite {V : LatticeVOA R}
    (criterion : RationalityCriterion (R := R) V) :
    criterion.rational ↔ positiveDefinite V :=
  criterion.iff_positive_definite

/-- A concrete VOA realization attached to a lattice model and criterion package. -/
structure RationalModel (V : LatticeVOA R) where
  /-- The carrier of the concrete VOA model. -/
  Carrier : Type uC
  [addCommGroup : AddCommGroup Carrier]
  [module : Module R Carrier]
  [voa : VertexOperatorAlgebra R Carrier]
  [rationalVOA : RationalVOA R Carrier]
  /-- Criterion package connected to this lattice model. -/
  criterion : RationalityCriterion (R := R) V

attribute [instance] RationalModel.addCommGroup RationalModel.module RationalModel.voa
  RationalModel.rationalVOA

/-- Positive-definite lattice criteria give positive finite fusion bounds in any concrete model. -/
theorem fusion_rules_bounded_pos_of_positiveDefinite
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  have _hcriterion : model.criterion.rational :=
    rational_of_positiveDefinite (R := R) model.criterion hpos
  simpa using fusion_rules_bounded_pos (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Positive-definite lattice criteria also provide one common positive bound
    for both ordered fusion pairs `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_bounded_pos_pair_of_positiveDefinite
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  have _hcriterion : model.criterion.rational :=
    rational_of_positiveDefinite (R := R) model.criterion hpos
  simpa using fusion_rules_bounded_pos_pair (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Rational lattice criteria induce positive finite fusion bounds
    by reduction to the positive-definite criterion. -/
theorem fusion_rules_bounded_pos_of_rational
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  have hpos : positiveDefinite V :=
    positiveDefinite_of_rational (R := R) model.criterion hrat
  exact fusion_rules_bounded_pos_of_positiveDefinite (R := R) model hpos

/-- Rational lattice criteria induce one common positive finite bound
    for both ordered fusion pairs `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_bounded_pos_pair_of_rational
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  have hpos : positiveDefinite V :=
    positiveDefinite_of_rational (R := R) model.criterion hrat
  exact fusion_rules_bounded_pos_pair_of_positiveDefinite (R := R) model hpos

/-- Positive-definite lattice criteria also provide a swapped-orientation common positive bound
    for ordered pairs `(M₂,M₁)` and `(M₁,M₂)`. -/
theorem fusion_rules_bounded_pos_pair_of_positiveDefinite_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_bounded_pos_pair_symm
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_positiveDefinite (R := R) model hpos)

/-- Rational lattice criteria also provide a swapped-orientation common positive bound
    for ordered pairs `(M₂,M₁)` and `(M₁,M₂)`. -/
theorem fusion_rules_bounded_pos_pair_of_rational_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_bounded_pos_pair_symm
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_rational (R := R) model hrat)

/-- Positive-definite lattice criteria imply finite fusion bounds
    by forgetting positivity from the positive-bound theorem. -/
theorem fusion_rules_finite_of_positiveDefinite
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_positiveDefinite (R := R) model hpos)

/-- Rational lattice criteria imply finite fusion bounds. -/
theorem fusion_rules_finite_of_rational
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_rational (R := R) model hrat)

/-- Positive-definite lattice criteria imply one common finite bound
    for both ordered pairs `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_finite_pair_of_positiveDefinite
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  have _hcriterion : model.criterion.rational :=
    rational_of_positiveDefinite (R := R) model.criterion hpos
  simpa using StringAlgebra.VOA.fusion_rules_finite_pair_of_rational
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Rational lattice criteria imply one common finite bound
    for both ordered pairs `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_finite_pair_of_rational
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  have hpos : positiveDefinite V :=
    positiveDefinite_of_rational (R := R) model.criterion hrat
  exact fusion_rules_finite_pair_of_positiveDefinite (R := R) model hpos

/-- Positive-definite lattice criteria imply a swapped-orientation common finite bound
    for ordered pairs `(M₂,M₁)` and `(M₁,M₂)`. -/
theorem fusion_rules_finite_pair_of_positiveDefinite_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_finite_pair_symm
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_finite_pair_of_positiveDefinite (R := R) model hpos)

/-- Rational lattice criteria imply a swapped-orientation common finite bound
    for ordered pairs `(M₂,M₁)` and `(M₁,M₂)`. -/
theorem fusion_rules_finite_pair_of_rational_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_finite_pair_symm
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_finite_pair_of_rational (R := R) model hrat)

/-- Positive-definite criteria also give a positive bound for the swapped ordered pair `(M₂,M₁)`. -/
theorem fusion_rules_bounded_pos_of_positiveDefinite_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_bounded_pos_of_pair_right (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_positiveDefinite (R := R) model hpos)

/-- Positive-definite criteria imply a finite bound for the swapped ordered pair `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_positiveDefinite_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hpos : positiveDefinite V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_finite_of_pair_bounded_pos_right
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_positiveDefinite (R := R) model hpos)

/-- Rational criteria also give a positive bound for the swapped ordered pair `(M₂,M₁)`. -/
theorem fusion_rules_bounded_pos_of_rational_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_bounded_pos_of_pair_right (R := R) (V := model.Carrier)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_rational (R := R) model hrat)

/-- Rational criteria imply a finite bound for the swapped ordered pair `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_rational_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    (hrat : model.criterion.rational)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := model.Carrier)
      (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact StringAlgebra.VOA.fusion_rules_finite_of_pair_bounded_pos_right
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair_of_rational (R := R) model hrat)

/-- In a concrete lattice model, positive and finite ordered bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  StringAlgebra.VOA.fusion_rules_bounded_pos_iff_finite
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- In a concrete lattice model, positive and finite common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  StringAlgebra.VOA.fusion_rules_bounded_pos_pair_iff_finite_pair
    (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- In a concrete lattice model, positive and finite swapped ordered bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  StringAlgebra.VOA.fusion_rules_bounded_pos_iff_finite
    (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

/-- In a concrete lattice model, positive and finite swapped common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair_swapped
    {V : LatticeVOA R}
    (model : RationalModel (R := R) V)
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R model.Carrier M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R model.Carrier M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R model.Carrier M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := model.Carrier) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  StringAlgebra.VOA.fusion_rules_bounded_pos_pair_iff_finite_pair
    (R := R) (V := model.Carrier) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

end LatticeVOA


end StringAlgebra.VOA
