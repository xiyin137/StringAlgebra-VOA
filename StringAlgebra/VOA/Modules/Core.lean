/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra

/-!
# Modules over Vertex Algebras

This file defines modules, twisted modules, and intertwining operators for VOAs.

## Main Definitions

* `VAModule` - A module over a vertex algebra
* `TwistedModule` - A twisted module (for orbifold constructions)
* `IntertwiningOperator` - Intertwining operators between modules
* `FusionRules` - Fusion rules N_{ij}^k

## References

* Frenkel, Lepowsky, Meurman, "Vertex Operator Algebras and the Monster"
* Dong, Li, Mason, "Twisted representations of vertex operator algebras"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Modules over Vertex Algebras

A V-module is a vector space M with a vertex operator Y_M : V → End(M)[[z, z⁻¹]]
satisfying the module axioms.
-/

/-- A module M over a vertex algebra V -/
class VAModule (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The module vertex operator Y_M : V → End(M)[[z, z⁻¹]] -/
  Y_M : V → FormalDistribution R M
  /-- The vacuum acts as identity: Y_M(|0⟩, z) = Id_M -/
  vacuum_axiom : Y_M (VertexAlgebra.vacuum (R := R)) = FormalDistribution.identity
  /-- Vacuum mode identity: `(Y_M |0⟩)_{-1} = id_M`. -/
  vacuum_mode_minus_one : ∀ m : M, (Y_M (VertexAlgebra.vacuum (R := R))) (-1) m = m
  /-- Lower truncation: for each a ∈ V, m ∈ M, a(n)m = 0 for n >> 0 -/
  lower_truncation : ∀ a : V, ∀ m : M, ∃ N : ℤ, ∀ n : ℤ, n > N → (Y_M a) n m = 0

/-- Assumption package: module fields are pairwise mutually local. -/
class ModuleLocality (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] : Prop where
  locality : ∀ a b : V,
    mutuallyLocal R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b)

/-- Assumption package: each module-field triple carries Dong-closure witness data. -/
class ModuleDongClosedData (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] : Prop where
  data : ∀ a b c : V,
    DongLemmaData (R := R) (V := M)
      (VAModule.Y_M (R := R) (M := M) a)
      (VAModule.Y_M (R := R) (M := M) b)
      (VAModule.Y_M (R := R) (M := M) c)

/-- Assumption package: Dong closure on module fields in theorem form. -/
class ModuleDongClosed (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] : Prop where
  closure :
    ∀ a b c : V, ∀ n : ℤ,
      mutuallyLocal R M
        (nthProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b) n)
        (VAModule.Y_M (R := R) (M := M) c)

namespace VAModule

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]

/-- The action of a(n) on M -/
def action (a : V) (n : ℤ) : Module.End R M := (Y_M a) n

/-- Explicit mode formula for the module vacuum field action. -/
theorem action_vacuum_mode (n : ℤ) :
    action (R := R) (V := V) (M := M) (VertexAlgebra.vacuum (R := R)) n =
      if n = -1 then (LinearMap.id : Module.End R M) else 0 := by
  have h := congrArg (fun F : FormalDistribution R M => F n)
    (VAModule.vacuum_axiom (R := R) (V := V) (M := M))
  simpa [action, FormalDistribution.identity] using h

/-- Away from mode `-1`, the vacuum field acts by zero on a module. -/
theorem action_vacuum_mode_ne (n : ℤ) (hn : n ≠ -1) :
    action (R := R) (V := V) (M := M) (VertexAlgebra.vacuum (R := R)) n = 0 := by
  simp [action_vacuum_mode (R := R) (V := V) (M := M) n, hn]

/-- At mode `-1`, the vacuum field action is the identity map on a module. -/
@[simp] theorem action_vacuum_mode_minus_one :
    action (R := R) (V := V) (M := M) (VertexAlgebra.vacuum (R := R)) (-1) =
      (LinearMap.id : Module.End R M) := by
  simpa using action_vacuum_mode (R := R) (V := V) (M := M) (-1)

/-- Applied form of module vacuum mode `-1` identity. -/
@[simp] theorem action_vacuum_mode_minus_one_apply (m : M) :
    action (R := R) (V := V) (M := M) (VertexAlgebra.vacuum (R := R)) (-1) m = m := by
  exact congrArg (fun f : Module.End R M => f m)
    (action_vacuum_mode_minus_one (R := R) (V := V) (M := M))

/-- Every module state field has the field property (restatement of module lower truncation). -/
theorem Y_M_hasFieldProperty (a : V) :
    FormalDistribution.hasFieldProperty (VAModule.Y_M (R := R) (V := V) (M := M) a) := by
  intro m
  exact VAModule.lower_truncation (R := R) (V := V) (M := M) a m

/-- For fixed mode `j`, the `nthProduct` of module fields has field property on vectors. -/
theorem Y_M_nthProduct_hasFieldProperty_right (a b : V) (j : ℤ) :
    FormalDistribution.hasFieldProperty
      (nthProduct R M (VAModule.Y_M (R := R) (V := V) (M := M) a)
        (VAModule.Y_M (R := R) (V := V) (M := M) b) j) := by
  exact hasFieldProperty_nthProduct_right (R := R) (V := M)
    (VAModule.Y_M (R := R) (V := V) (M := M) a)
    (VAModule.Y_M (R := R) (V := V) (M := M) b)
    j
    (Y_M_hasFieldProperty (R := R) (V := V) (M := M) b)

/-- The normal-ordered product of module fields has field property on vectors. -/
theorem Y_M_normalOrderedProduct_hasFieldProperty_right (a b : V) :
    FormalDistribution.hasFieldProperty
      (normalOrderedProduct R M (VAModule.Y_M (R := R) (V := V) (M := M) a)
        (VAModule.Y_M (R := R) (V := V) (M := M) b)) := by
  simpa [normalOrderedProduct] using
    Y_M_nthProduct_hasFieldProperty_right (R := R) (V := V) (M := M) a b (-1)

/-- Locality bridge for module state fields from `ModuleLocality`. -/
theorem stateField_locality [ModuleLocality R V M] (a b : V) :
    mutuallyLocal R M
      (VAModule.Y_M (R := R) (V := V) (M := M) a)
      (VAModule.Y_M (R := R) (V := V) (M := M) b) :=
  ModuleLocality.locality (R := R) (V := V) (M := M) a b

/-- Symmetric orientation of module-state locality. -/
theorem stateField_locality_symm [ModuleLocality R V M] (a b : V) :
    mutuallyLocal R M
      (VAModule.Y_M (R := R) (V := V) (M := M) b)
      (VAModule.Y_M (R := R) (V := V) (M := M) a) := by
  exact mutuallyLocal_symm (R := R) (V := M)
    (VAModule.Y_M (R := R) (V := V) (M := M) a)
    (VAModule.Y_M (R := R) (V := V) (M := M) b)
    (stateField_locality (R := R) (V := V) (M := M) a b)

/-- A module field is local with itself under `ModuleLocality`. -/
theorem stateField_locality_self [ModuleLocality R V M] (a : V) :
    mutuallyLocal R M
      (VAModule.Y_M (R := R) (V := V) (M := M) a)
      (VAModule.Y_M (R := R) (V := V) (M := M) a) :=
  stateField_locality (R := R) (V := V) (M := M) a a

/-- `ModuleLocality` and `ModuleDongClosedData` yield `ModuleDongClosed`. -/
instance (priority := 100) moduleDongClosed_of_data
    [ModuleLocality R V M] [ModuleDongClosedData R V M] : ModuleDongClosed R V M where
  closure := by
    intro a b c n
    exact (ModuleDongClosedData.data (R := R) (V := V) (M := M) a b c).closure n
      (ModuleLocality.locality (R := R) (V := V) (M := M) a b)
      (ModuleLocality.locality (R := R) (V := V) (M := M) a c)
      (ModuleLocality.locality (R := R) (V := V) (M := M) b c)

/-- Dong-closed locality for module-field `nthProduct`s. -/
theorem locality_nthProduct [ModuleDongClosed R V M] (a b c : V) (n : ℤ) :
    mutuallyLocal R M
      (nthProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b) n)
      (VAModule.Y_M (R := R) (M := M) c) :=
  ModuleDongClosed.closure (R := R) (V := V) (M := M) a b c n

/-- Symmetric form of Dong-closed module-field `nthProduct` locality. -/
theorem locality_right_nthProduct [ModuleDongClosed R V M] (a b c : V) (n : ℤ) :
    mutuallyLocal R M
      (VAModule.Y_M (R := R) (M := M) c)
      (nthProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b) n) := by
  exact mutuallyLocal_symm (R := R) (V := M)
    (nthProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b) n)
    (VAModule.Y_M (R := R) (M := M) c)
    (locality_nthProduct (R := R) (V := V) (M := M) a b c n)

/-- Dong-closed locality for module normal-ordered fields. -/
theorem locality_normalOrderedProduct [ModuleDongClosed R V M] (a b c : V) :
    mutuallyLocal R M
      (normalOrderedProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b))
      (VAModule.Y_M (R := R) (M := M) c) := by
  simpa [normalOrderedProduct] using
    locality_nthProduct (R := R) (V := V) (M := M) a b c (-1)

/-- Symmetric form of Dong-closed module normal-ordered locality. -/
theorem locality_right_normalOrderedProduct [ModuleDongClosed R V M] (a b c : V) :
    mutuallyLocal R M
      (VAModule.Y_M (R := R) (M := M) c)
      (normalOrderedProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b)) := by
  exact mutuallyLocal_symm (R := R) (V := M)
    (normalOrderedProduct R M (VAModule.Y_M (R := R) (M := M) a) (VAModule.Y_M (R := R) (M := M) b))
    (VAModule.Y_M (R := R) (M := M) c)
    (locality_normalOrderedProduct (R := R) (V := V) (M := M) a b c)

/-- V is a module over itself (the adjoint module) -/
instance adjointModule : VAModule R V V where
  Y_M := VertexAlgebra.Y
  vacuum_axiom := VertexAlgebra.vacuum_axiom
  vacuum_mode_minus_one := by
    intro v
    simpa [VertexAlgebra.nProduct] using
      (VertexAlgebra.vacuum_minus1_product (R := R) (a := v))
  lower_truncation := fun a v => VertexAlgebra.lower_truncation (R := R) a v

/-- The adjoint module inherits locality from the ambient vertex algebra. -/
instance adjointModuleLocality : ModuleLocality R V V where
  locality := VertexAlgebra.locality (R := R)

/-- Dong witness data on state fields induces Dong witness data on the adjoint module. -/
instance adjointModuleDongClosedData [VertexAlgebra.DongClosedData (R := R) (V := V)] :
    ModuleDongClosedData R V V where
  data a b c := VertexAlgebra.DongClosedData.data (R := R) (V := V) a b c

/-- Direct bridge: Dong closure on state fields implies Dong closure on the adjoint module. -/
instance adjointModuleDongClosed [VertexAlgebra.DongClosed (R := R) (V := V)] :
    ModuleDongClosed R V V where
  closure a b c n := VertexAlgebra.locality_nthProduct (R := R) (V := V) a b c n

/-- Adjoint-module `nthProduct` locality specialized from state-level Dong closure. -/
theorem adjoint_locality_nthProduct [VertexAlgebra.DongClosed (R := R) (V := V)]
    (a b c : V) (n : ℤ) :
    mutuallyLocal R V
      (nthProduct R V (VAModule.Y_M (R := R) (V := V) (M := V) a)
        (VAModule.Y_M (R := R) (V := V) (M := V) b) n)
      (VAModule.Y_M (R := R) (V := V) (M := V) c) :=
  locality_nthProduct (R := R) (V := V) (M := V) a b c n

end VAModule

/-! ## Graded Modules (for VOAs)

A module over a VOA inherits a grading from L(0).
-/

/-- A graded module over a VOA V.
    The grading may be shifted: M = ⊕_n M_{h+n} where h is the conformal weight. -/
structure GradedVAModule (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] where
  /-- The graded components -/
  component : ℤ → Submodule R M
  /-- The lowest weight (conformal weight of the module) -/
  lowestWeight : ℤ
  /-- The L(0) eigenvalue condition -/
  L0_eigenvalue : ∀ n : ℤ, ∀ m ∈ component n,
    (VAModule.Y_M (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 m = (n : ℤ) • m
  /-- Lower truncation: M_n = 0 for n < lowestWeight -/
  lower_truncation : ∀ n : ℤ, n < lowestWeight → component n = ⊥

/-! ## Irreducible and Admissible Modules -/

/-- An irreducible V-module has no proper submodules -/
def isIrreducible (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] : Prop :=
  ∀ N : Submodule R M,
    (∀ a : V, ∀ n : ℤ, ∀ m ∈ N, (VAModule.Y_M (R := R) a) n m ∈ N) →
    N = ⊥ ∨ N = ⊤

/-- An admissible module: each L(0)-eigenspace is finite-dimensional -/
def isAdmissible (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M) : Prop :=
  ∀ n : ℤ, Module.Finite R (grading.component n : Submodule R M)

/-- An ordinary module: admissible + L(0) eigenvalues are bounded below -/
def isOrdinary (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M) : Prop :=
  isAdmissible R V M grading ∧
  ∃ N : ℤ, ∀ n : ℤ, n < N → grading.component n = ⊥


end StringAlgebra.VOA
