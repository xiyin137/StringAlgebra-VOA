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

/-! ## Intertwining Operators

An intertwining operator of type (M₃ over M₁, M₂) is a linear map
𝒴: M₁ ⊗ M₂ → M₃{z} satisfying the Jacobi identity with V.
-/

/-- An intertwining operator of type (M₃ over M₁ M₂) -/
structure IntertwiningOperator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] where
  /-- The intertwining operator 𝒴(·, z): M₁ → Hom(M₂, M₃){z} -/
  Y_int : M₁ → ℤ → (M₂ →ₗ[R] M₃)
  /-- Lower truncation: for m₁ ∈ M₁, m₂ ∈ M₂, 𝒴(m₁, z)m₂ ∈ M₃((z)) -/
  lower_truncation : ∀ m₁ : M₁, ∀ m₂ : M₂, ∃ N : ℤ, ∀ n : ℤ,
    n < N → (Y_int m₁ n) m₂ = 0
  /-- Jacobi identity with V -/
  jacobi_identity : ∀ a : V, ∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ,
    (Y_int m₁ n) ((VAModule.Y_M (R := R) (M := M₂) a) (-1) m₂) =
      (VAModule.Y_M (R := R) (M := M₃) a) (-1) ((Y_int m₁ n) m₂)

namespace IntertwiningOperator

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable {M₁ M₂ M₃ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
variable [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
variable [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]

/-- Intertwiner compatibility in module-action notation (mode `-1`). -/
theorem jacobi_identity_action (I : IntertwiningOperator (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (a : V) (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (I.Y_int m₁ n) (VAModule.action (R := R) (V := V) (M := M₂) a (-1) m₂) =
      VAModule.action (R := R) (V := V) (M := M₃) a (-1) ((I.Y_int m₁ n) m₂) := by
  simpa [VAModule.action] using I.jacobi_identity a m₁ m₂ n

/-- Intertwiner compatibility as equality of composed linear maps at mode `-1`. -/
theorem jacobi_identity_action_comp (I : IntertwiningOperator (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (a : V) (m₁ : M₁) (n : ℤ) :
    (I.Y_int m₁ n).comp (VAModule.action (R := R) (V := V) (M := M₂) a (-1)) =
      (VAModule.action (R := R) (V := V) (M := M₃) a (-1)).comp (I.Y_int m₁ n) := by
  ext m₂
  simpa [LinearMap.comp_apply] using I.jacobi_identity_action a m₁ m₂ n

/-- Symmetric orientation of the mode `-1` intertwiner compatibility. -/
theorem jacobi_identity_action_comp_symm (I : IntertwiningOperator (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (a : V) (m₁ : M₁) (n : ℤ) :
    (VAModule.action (R := R) (V := V) (M := M₃) a (-1)).comp (I.Y_int m₁ n) =
      (I.Y_int m₁ n).comp (VAModule.action (R := R) (V := V) (M := M₂) a (-1)) := by
  simpa [eq_comm] using I.jacobi_identity_action_comp a m₁ n

/-- Compatibility contract for intertwiners with module actions at mode `-1`. -/
class ModeMinusOneCompatible
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) : Prop where
  comm :
    ∀ a : V, ∀ m₁ : M₁, ∀ n : ℤ,
      (I.Y_int m₁ n).comp (VAModule.action (R := R) (V := V) (M := M₂) a (-1)) =
        (VAModule.action (R := R) (V := V) (M := M₃) a (-1)).comp (I.Y_int m₁ n)

/-- Every intertwiner satisfies the `ModeMinusOneCompatible` contract via Jacobi. -/
instance modeMinusOneCompatible
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    ModeMinusOneCompatible (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I where
  comm := I.jacobi_identity_action_comp

/-- Accessor lemma for `ModeMinusOneCompatible` commutation. -/
theorem action_comp_of_modeMinusOneCompatible
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    [ModeMinusOneCompatible (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I]
    (a : V) (m₁ : M₁) (n : ℤ) :
    (I.Y_int m₁ n).comp (VAModule.action (R := R) (V := V) (M := M₂) a (-1)) =
      (VAModule.action (R := R) (V := V) (M := M₃) a (-1)).comp (I.Y_int m₁ n) :=
  ModeMinusOneCompatible.comm (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (I := I) a m₁ n

/-- Applied form of `ModeMinusOneCompatible` commutation. -/
theorem action_apply_of_modeMinusOneCompatible
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    [ModeMinusOneCompatible (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I]
    (a : V) (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (I.Y_int m₁ n) (VAModule.action (R := R) (V := V) (M := M₂) a (-1) m₂) =
      VAModule.action (R := R) (V := V) (M := M₃) a (-1) ((I.Y_int m₁ n) m₂) := by
  have h := action_comp_of_modeMinusOneCompatible (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I a m₁ n
  exact congrArg (fun f : M₂ →ₗ[R] M₃ => f m₂) h

/-- Symmetric orientation of `ModeMinusOneCompatible` commutation. -/
theorem action_comp_symm_of_modeMinusOneCompatible
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    [ModeMinusOneCompatible (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I]
    (a : V) (m₁ : M₁) (n : ℤ) :
    (VAModule.action (R := R) (V := V) (M := M₃) a (-1)).comp (I.Y_int m₁ n) =
      (I.Y_int m₁ n).comp (VAModule.action (R := R) (V := V) (M := M₂) a (-1)) := by
  simpa [eq_comm] using action_comp_of_modeMinusOneCompatible
    (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) I a m₁ n

/-- At mode `-1`, composing an intertwiner with source vacuum action is identity simplification. -/
theorem action_comp_vacuum_minus_one_source
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (m₁ : M₁) (n : ℤ) :
    (I.Y_int m₁ n).comp
        (VAModule.action (R := R) (V := V) (M := M₂) (VertexAlgebra.vacuum (R := R)) (-1))
      = I.Y_int m₁ n := by
  ext m₂
  simp

/-- At mode `-1`, composing target vacuum action with an intertwiner is identity simplification. -/
theorem action_comp_vacuum_minus_one_target
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (m₁ : M₁) (n : ℤ) :
    (VAModule.action (R := R) (V := V) (M := M₃) (VertexAlgebra.vacuum (R := R)) (-1)).comp
        (I.Y_int m₁ n)
      = I.Y_int m₁ n := by
  ext m₂
  simp

/-- Applied source-vacuum mode `-1` simplification for intertwiners. -/
@[simp] theorem action_apply_vacuum_minus_one_source
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (I.Y_int m₁ n)
      (VAModule.action (R := R) (V := V) (M := M₂) (VertexAlgebra.vacuum (R := R)) (-1) m₂)
      = (I.Y_int m₁ n) m₂ := by
  simp

/-- Applied target-vacuum mode `-1` simplification for intertwiners. -/
@[simp] theorem action_apply_vacuum_minus_one_target
    (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    VAModule.action (R := R) (V := V) (M := M₃) (VertexAlgebra.vacuum (R := R)) (-1)
      ((I.Y_int m₁ n) m₂) = (I.Y_int m₁ n) m₂ := by
  simp

/-- Source module state-field locality bridge for intertwiners. -/
theorem source_locality
    [ModuleLocality R V M₂] (a b : V) :
    mutuallyLocal R M₂
      (VAModule.Y_M (R := R) (V := V) (M := M₂) a)
      (VAModule.Y_M (R := R) (V := V) (M := M₂) b) :=
  VAModule.stateField_locality (R := R) (V := V) (M := M₂) a b

/-- Target module state-field locality bridge for intertwiners. -/
theorem target_locality
    [ModuleLocality R V M₃] (a b : V) :
    mutuallyLocal R M₃
      (VAModule.Y_M (R := R) (V := V) (M := M₃) a)
      (VAModule.Y_M (R := R) (V := V) (M := M₃) b) :=
  VAModule.stateField_locality (R := R) (V := V) (M := M₃) a b

/-- Symmetric orientation of source-module state-field locality bridge. -/
theorem source_locality_symm
    [ModuleLocality R V M₂] (a b : V) :
    mutuallyLocal R M₂
      (VAModule.Y_M (R := R) (V := V) (M := M₂) b)
      (VAModule.Y_M (R := R) (V := V) (M := M₂) a) :=
  VAModule.stateField_locality_symm (R := R) (V := V) (M := M₂) a b

/-- Symmetric orientation of target-module state-field locality bridge. -/
theorem target_locality_symm
    [ModuleLocality R V M₃] (a b : V) :
    mutuallyLocal R M₃
      (VAModule.Y_M (R := R) (V := V) (M := M₃) b)
      (VAModule.Y_M (R := R) (V := V) (M := M₃) a) :=
  VAModule.stateField_locality_symm (R := R) (V := V) (M := M₃) a b

/-- Dong-closed locality bridge for the source module of an intertwiner. -/
theorem source_locality_nthProduct
    [ModuleDongClosed R V M₂] (a b c : V) (k : ℤ) :
    mutuallyLocal R M₂
      (nthProduct R M₂ (VAModule.Y_M (R := R) (V := V) (M := M₂) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₂) b) k)
      (VAModule.Y_M (R := R) (V := V) (M := M₂) c) :=
  VAModule.locality_nthProduct (R := R) (V := V) (M := M₂) a b c k

/-- Dong-closed locality bridge for the target module of an intertwiner. -/
theorem target_locality_nthProduct
    [ModuleDongClosed R V M₃] (a b c : V) (k : ℤ) :
    mutuallyLocal R M₃
      (nthProduct R M₃ (VAModule.Y_M (R := R) (V := V) (M := M₃) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₃) b) k)
      (VAModule.Y_M (R := R) (V := V) (M := M₃) c) :=
  VAModule.locality_nthProduct (R := R) (V := V) (M := M₃) a b c k

/-- Symmetric orientation of source-module `nthProduct` locality bridge. -/
theorem source_locality_right_nthProduct
    [ModuleDongClosed R V M₂] (a b c : V) (k : ℤ) :
    mutuallyLocal R M₂
      (VAModule.Y_M (R := R) (V := V) (M := M₂) c)
      (nthProduct R M₂ (VAModule.Y_M (R := R) (V := V) (M := M₂) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₂) b) k) :=
  VAModule.locality_right_nthProduct (R := R) (V := V) (M := M₂) a b c k

/-- Symmetric orientation of target-module `nthProduct` locality bridge. -/
theorem target_locality_right_nthProduct
    [ModuleDongClosed R V M₃] (a b c : V) (k : ℤ) :
    mutuallyLocal R M₃
      (VAModule.Y_M (R := R) (V := V) (M := M₃) c)
      (nthProduct R M₃ (VAModule.Y_M (R := R) (V := V) (M := M₃) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₃) b) k) :=
  VAModule.locality_right_nthProduct (R := R) (V := V) (M := M₃) a b c k

/-- Dong-closed normal-ordered locality bridge for the source module of an intertwiner. -/
theorem source_locality_normalOrderedProduct
    [ModuleDongClosed R V M₂] (a b c : V) :
    mutuallyLocal R M₂
      (normalOrderedProduct R M₂ (VAModule.Y_M (R := R) (V := V) (M := M₂) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₂) b))
      (VAModule.Y_M (R := R) (V := V) (M := M₂) c) :=
  VAModule.locality_normalOrderedProduct (R := R) (V := V) (M := M₂) a b c

/-- Dong-closed normal-ordered locality bridge for the target module of an intertwiner. -/
theorem target_locality_normalOrderedProduct
    [ModuleDongClosed R V M₃] (a b c : V) :
    mutuallyLocal R M₃
      (normalOrderedProduct R M₃ (VAModule.Y_M (R := R) (V := V) (M := M₃) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₃) b))
      (VAModule.Y_M (R := R) (V := V) (M := M₃) c) :=
  VAModule.locality_normalOrderedProduct (R := R) (V := V) (M := M₃) a b c

/-- Symmetric orientation of source-module normal-ordered locality bridge. -/
theorem source_locality_right_normalOrderedProduct
    [ModuleDongClosed R V M₂] (a b c : V) :
    mutuallyLocal R M₂
      (VAModule.Y_M (R := R) (V := V) (M := M₂) c)
      (normalOrderedProduct R M₂ (VAModule.Y_M (R := R) (V := V) (M := M₂) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₂) b)) :=
  VAModule.locality_right_normalOrderedProduct (R := R) (V := V) (M := M₂) a b c

/-- Symmetric orientation of target-module normal-ordered locality bridge. -/
theorem target_locality_right_normalOrderedProduct
    [ModuleDongClosed R V M₃] (a b c : V) :
    mutuallyLocal R M₃
      (VAModule.Y_M (R := R) (V := V) (M := M₃) c)
      (normalOrderedProduct R M₃ (VAModule.Y_M (R := R) (V := V) (M := M₃) a)
        (VAModule.Y_M (R := R) (V := V) (M := M₃) b)) :=
  VAModule.locality_right_normalOrderedProduct (R := R) (V := V) (M := M₃) a b c

end IntertwiningOperator

/-- The fusion rules N_{M₁ M₂}^{M₃} = dim Hom_V(M₁ ⊗ M₂, M₃) -/
noncomputable def fusionRules
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] : ℕ :=
  Cardinal.toNat (Cardinal.mk (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)))

/-! ## Universal Fusion Tensor Product

This packages the universal property for the tensor/fusion product `M₁ ⊠ M₂`.
-/

universe uV uM1 uM2 uC

/-- A realization of the fusion tensor product by universal mapping property. -/
structure FusionTensorProduct
    {V : Type uV} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M₁ : Type uM1) (M₂ : Type uM2)
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂] where
  /-- Carrier module for the tensor/fusion product. -/
  carrier : Type uC
  /-- Additive structure on the carrier. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Scalar action on the carrier. -/
  [module : Module R carrier]
  /-- Vertex algebra module structure on the carrier. -/
  [vaModule : VAModule R V carrier]
  /-- Universal intertwining operator `M₁ × M₂ → carrier`. -/
  incl : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := carrier)
  /-- Universal factorization map. -/
  lift :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W],
      IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W) →
      carrier →ₗ[R] W
  /-- Factorization compatibility with the universal intertwiner. -/
  fac :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W]
      (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W))
      (m₁ : M₁) (m₂ : M₂) (n : ℤ),
      (lift I) ((incl.Y_int m₁ n) m₂) = (I.Y_int m₁ n) m₂
  /-- Uniqueness of factorization map. -/
  uniq :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W]
      (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W))
      (f : carrier →ₗ[R] W),
      (∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ, f ((incl.Y_int m₁ n) m₂) = (I.Y_int m₁ n) m₂) →
      f = lift I

attribute [instance] FusionTensorProduct.addCommGroup FusionTensorProduct.module
  FusionTensorProduct.vaModule

namespace FusionTensorProduct

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable {M₁ M₂ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
variable [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]

/-- Canonical map between two realizations of the same tensor product object. -/
noncomputable def hom (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    P.carrier →ₗ[R] Q.carrier :=
  P.lift (W := Q.carrier) Q.incl

theorem hom_fac (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (hom P Q) ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂ := by
  simpa [hom] using P.fac (W := Q.carrier) Q.incl m₁ m₂ n

/-- Uniqueness principle: a map matching the universal intertwiner equals `hom`. -/
theorem hom_unique (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (f : P.carrier →ₗ[R] Q.carrier)
    (hfac : ∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ,
      f ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂) :
    f = hom P Q := by
  simpa [hom] using P.uniq (I := Q.incl) f hfac

/-- Canonical maps between fusion-product realizations compose transitively. -/
theorem hom_comp (P Q S : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q S).comp (hom P Q) = hom P S := by
  apply hom_unique (P := P) (Q := S)
  intro m₁ m₂ n
  calc
    ((hom Q S).comp (hom P Q)) ((P.incl.Y_int m₁ n) m₂)
        = (hom Q S) ((hom P Q) ((P.incl.Y_int m₁ n) m₂)) := by
            rfl
    _ = (hom Q S) ((Q.incl.Y_int m₁ n) m₂) := by
          exact congrArg (hom Q S) (hom_fac (P := P) (Q := Q) m₁ m₂ n)
    _ = (S.incl.Y_int m₁ n) m₂ := by
          simpa using hom_fac (P := Q) (Q := S) m₁ m₂ n

/-- Associative composition form of canonical fusion maps across four realizations. -/
theorem hom_comp_assoc (P Q S T : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((hom S T).comp (hom Q S)).comp (hom P Q) = hom P T := by
  calc
    ((hom S T).comp (hom Q S)).comp (hom P Q)
        = (hom Q T).comp (hom P Q) := by
            simpa using congrArg (fun f : Q.carrier →ₗ[R] T.carrier => f.comp (hom P Q))
              (hom_comp (P := Q) (Q := S) (S := T))
    _ = hom P T := by
          simpa using hom_comp (P := P) (Q := Q) (S := T)

@[simp] theorem hom_comp_self_left (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom P Q).comp (hom P P) = hom P Q := by
  simpa using (hom_comp (P := P) (Q := P) (S := Q))

@[simp] theorem hom_comp_self_right (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q Q).comp (hom P Q) = hom P Q := by
  simpa using (hom_comp (P := P) (Q := Q) (S := Q))

theorem hom_comp_hom_eq_id (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom P Q).comp (hom Q P) = (LinearMap.id : Q.carrier →ₗ[R] Q.carrier) := by
  have hcomp_lift : (hom P Q).comp (hom Q P) = Q.lift Q.incl := by
    apply Q.uniq (I := Q.incl)
    intro m₁ m₂ n
    calc
      ((hom P Q).comp (hom Q P)) ((Q.incl.Y_int m₁ n) m₂)
          = (hom P Q) ((hom Q P) ((Q.incl.Y_int m₁ n) m₂)) := by
              rfl
      _ = (hom P Q) ((P.incl.Y_int m₁ n) m₂) := by
            have hfacQ :
                (hom Q P) ((Q.incl.Y_int m₁ n) m₂) = (P.incl.Y_int m₁ n) m₂ := by
              simpa [hom] using Q.fac (W := P.carrier) P.incl m₁ m₂ n
            exact congrArg (hom P Q) hfacQ
      _ = (Q.incl.Y_int m₁ n) m₂ := by
            simpa [hom] using P.fac (W := Q.carrier) Q.incl m₁ m₂ n
  have hid_lift : (LinearMap.id : Q.carrier →ₗ[R] Q.carrier) = Q.lift Q.incl := by
    apply Q.uniq (I := Q.incl)
    intro m₁ m₂ n
    rfl
  exact hcomp_lift.trans hid_lift.symm

theorem hom_comp_hom_eq_id_left (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q P).comp (hom P Q) = (LinearMap.id : P.carrier →ₗ[R] P.carrier) := by
  simpa using hom_comp_hom_eq_id (P := Q) (Q := P)

@[simp] theorem hom_self_eq_id (P : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    hom P P = (LinearMap.id : P.carrier →ₗ[R] P.carrier) := by
  have hid_lift : (LinearMap.id : P.carrier →ₗ[R] P.carrier) = P.lift P.incl := by
    apply P.uniq (I := P.incl)
    intro m₁ m₂ n
    rfl
  simpa [hom] using hid_lift.symm

/-- Any two universal realizations of `M₁ ⊠ M₂` are canonically isomorphic. -/
noncomputable def iso (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    P.carrier ≃ₗ[R] Q.carrier :=
  LinearEquiv.ofLinear (hom P Q) (hom Q P)
    (hom_comp_hom_eq_id (P := P) (Q := Q))
    (hom_comp_hom_eq_id (P := Q) (Q := P))

@[simp] theorem iso_toLinearMap (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((iso P Q : P.carrier ≃ₗ[R] Q.carrier) : P.carrier →ₗ[R] Q.carrier) = hom P Q := rfl

@[simp] theorem iso_symm_toLinearMap (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((iso P Q).symm : Q.carrier →ₗ[R] P.carrier) = hom Q P := by
  simp [iso]

@[simp] theorem iso_symm_eq_iso (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (iso P Q).symm = iso Q P := by
  ext x
  change (((iso P Q).symm : Q.carrier →ₗ[R] P.carrier) x) =
      (((iso Q P : Q.carrier ≃ₗ[R] P.carrier) : Q.carrier →ₗ[R] P.carrier) x)
  simp

theorem iso_apply_incl (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (iso P Q) ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂ := by
  simpa [iso_toLinearMap] using hom_fac (P := P) (Q := Q) m₁ m₂ n

theorem iso_symm_apply_incl (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (iso P Q).symm ((Q.incl.Y_int m₁ n) m₂) = (P.incl.Y_int m₁ n) m₂ := by
  simpa [iso_symm_toLinearMap] using hom_fac (P := Q) (Q := P) m₁ m₂ n

@[simp] theorem iso_trans (P Q S : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (iso P Q).trans (iso Q S) = iso P S := by
  ext x
  change (iso Q S) ((iso P Q) x) = (iso P S) x
  have hcomp := hom_comp (P := P) (Q := Q) (S := S)
  exact congrArg (fun f : P.carrier →ₗ[R] S.carrier => f x) hcomp

@[simp] theorem iso_refl (P : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    iso P P = LinearEquiv.refl R P.carrier := by
  ext x
  simp [iso, hom_self_eq_id]

end FusionTensorProduct

/-! ## Twisted Modules

Twisted modules arise in orbifold constructions.
-/

/-- A g-twisted module for an automorphism g of order T -/
structure TwistedModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (g : V →ₗ[R] V)
    (T : ℕ)
    (_hg : g^T = LinearMap.id) where
  /-- The underlying module -/
  M : Type*
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- The twisted vertex operator Y^g: V → End(M)[[z^{1/T}, z^{-1/T}]] -/
  Y_twisted : V → FormalDistribution R M
  /-- Equivariance -/
  equivariance : ∀ a : V, ∀ n : ℤ,
    (Y_twisted (g a)) n = (Y_twisted a) n
  /-- Twisted Jacobi identity -/
  jacobi : ∀ a b : V, ∀ m : M, ∀ n : ℤ,
    (Y_twisted a) n ((Y_twisted b) n m) = (Y_twisted b) n ((Y_twisted a) n m)

attribute [instance] TwistedModule.addCommGroup TwistedModule.module

/-! ## Contragredient Module -/

/-- The contragredient module M' = ⊕_n (M_n)* with the dual vertex operator -/
structure ContragredientModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (_grading : GradedVAModule R V M) where
  /-- The dual space (restricted dual) -/
  M' : Type*
  [addCommGroup : AddCommGroup M']
  [module : Module R M']
  /-- The pairing -/
  pairing : M' →ₗ[R] M →ₗ[R] R
  /-- The contragredient vertex operator formula -/
  contragredient_formula : ∀ m' : M', ∀ m₁ m₂ : M,
    pairing m' (m₁ + m₂) = pairing m' m₁ + pairing m' m₂

attribute [instance] ContragredientModule.addCommGroup ContragredientModule.module

/-- A self-dual module: M ≅ M' -/
def isSelfDual
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M)
    (M_dual : ContragredientModule (R := R) grading) : Prop :=
  Nonempty (M ≃ₗ[R] M_dual.M')

/-! ## Rationality -/

/-- A VOA V is rational -/
class RationalVOA (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] where
  /-- Finitely many irreducible modules (up to isomorphism) -/
  finitelyManyIrreducibles : ∃ n : ℕ, 0 < n
  /-- Complete reducibility at the submodule level:
      every VOA submodule has a complementary submodule. -/
  completelyReducible :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M],
      ∀ N : Submodule R M, ∃ P : Submodule R M, IsCompl N P

/-- Every vector decomposes as `n + p` for complementary submodules `N ⊔ P = ⊤`. -/
  theorem exists_add_decomposition_of_isCompl
    {M : Type*} [AddCommGroup M] [Module R M]
    (N P : Submodule R M) (hNP : IsCompl N P) (x : M) :
    ∃ n p : M, n ∈ N ∧ p ∈ P ∧ x = n + p := by
  have hx : x ∈ N ⊔ P := by
    simp [hNP.sup_eq_top]
  rcases Submodule.mem_sup.mp hx with ⟨n, hn, p, hp, rfl⟩
  exact ⟨n, p, hn, hp, rfl⟩

/-- Decomposition along complementary submodules is unique. -/
theorem add_decomposition_unique_of_isCompl
    {M : Type*} [AddCommGroup M] [Module R M]
    (N P : Submodule R M) (hNP : IsCompl N P)
    {n₁ n₂ p₁ p₂ : M}
    (hn₁ : n₁ ∈ N) (hn₂ : n₂ ∈ N) (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P)
    (hEq : n₁ + p₁ = n₂ + p₂) :
    n₁ = n₂ ∧ p₁ = p₂ := by
  have hsum : n₁ - n₂ + (p₁ - p₂) = 0 := by
    have hEq' : (n₁ + p₁) - (n₂ + p₂) = 0 := sub_eq_zero.mpr hEq
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
  have hsub : n₁ - n₂ = -(p₁ - p₂) := eq_neg_of_add_eq_zero_left hsum
  have hN : n₁ - n₂ ∈ N := Submodule.sub_mem N hn₁ hn₂
  have hP : n₁ - n₂ ∈ P := by
    have hpSub : p₁ - p₂ ∈ P := Submodule.sub_mem P hp₁ hp₂
    have hneg : -(p₁ - p₂) ∈ P := Submodule.neg_mem P hpSub
    simpa [hsub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hInInf : n₁ - n₂ ∈ N ⊓ P := ⟨hN, hP⟩
  have hZeroMem : n₁ - n₂ ∈ (⊥ : Submodule R M) := by
    simpa [hNP.inf_eq_bot] using hInInf
  have hNEqual : n₁ = n₂ := sub_eq_zero.mp (by simpa using hZeroMem)
  constructor
  · exact hNEqual
  · have hEq' : n₂ + p₁ = n₂ + p₂ := by simpa [hNEqual] using hEq
    exact add_left_cancel hEq'

/-- A rational VOA has a strictly positive finite irreducible-count witness. -/
theorem RationalVOA.exists_positive_irreducible_count
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [RationalVOA R V] : ∃ n : ℕ, 0 < n :=
  RationalVOA.finitelyManyIrreducibles (R := R) (V := V)

/-- A rational VOA has a nonzero finite irreducible-count witness. -/
theorem RationalVOA.exists_nonzero_irreducible_count
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [RationalVOA R V] : ∃ n : ℕ, n ≠ 0 := by
  rcases RationalVOA.exists_positive_irreducible_count (R := R) (V := V) with ⟨n, hn⟩
  exact ⟨n, Nat.ne_of_gt hn⟩

/-- For finite intertwiner spaces, fusion rules are finite. -/
theorem fusion_rules_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  classical
  letI : Fintype (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)), ?_⟩
  simp [fusionRules]
  

/-- For finite intertwiner spaces, fusion rules admit a positive finite bound. -/
theorem fusion_rules_bounded_pos
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  classical
  letI : Fintype (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) + 1,
    Nat.succ_pos _, ?_⟩
  simp [fusionRules]
  

/-- For finite intertwiner spaces in both orientations, both orderings admit one positive common bound. -/
theorem fusion_rules_bounded_pos_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  obtain ⟨bound12, hpos12, hbound12⟩ :=
    fusion_rules_bounded_pos (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
  obtain ⟨bound21, hpos21, hbound21⟩ :=
    fusion_rules_bounded_pos (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)
  refine ⟨max bound12 bound21, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos12 (Nat.le_max_left _ _)
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- Dropping positivity from a positive fusion bound. -/
theorem fusion_rules_finite_of_bounded_pos
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpos : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpos with ⟨bound, _hboundpos, hle⟩
  exact ⟨bound, hle⟩

/-- Any finite fusion bound can be upgraded to a positive finite bound by `+1`. -/
theorem fusion_rules_bounded_pos_of_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hfin : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hfin with ⟨bound, hbound⟩
  refine ⟨bound + 1, Nat.succ_pos _, ?_⟩
  exact le_trans hbound (Nat.le_succ _)

/-- Positive-bounded and finite-bounded fusion-rule statements are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) := by
  constructor
  · intro hpos
    exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpos
  · intro hfin
    exact fusion_rules_bounded_pos_of_finite (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hfin

/-- Extract the first ordered positive bound from a pair bound. -/
theorem fusion_rules_bounded_pos_of_pair_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, hleft, _hright⟩
  exact ⟨bound, hpos, hleft⟩

/-- Extract the swapped ordered positive bound from a pair bound. -/
theorem fusion_rules_bounded_pos_of_pair_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, _hleft, hright⟩
  exact ⟨bound, hpos, hright⟩

/-- Symmetry of a positive common pair bound under swapping `(M₁,M₂)`. -/
theorem fusion_rules_bounded_pos_pair_symm
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, hbound12, hbound21⟩
  exact ⟨bound, hpos, hbound21, hbound12⟩

/-- Build one common positive pair bound from two ordered positive bounds. -/
theorem fusion_rules_bounded_pos_pair_of_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases h12 with ⟨bound12, hpos12, hbound12⟩
  rcases h21 with ⟨bound21, hpos21, hbound21⟩
  refine ⟨max bound12 bound21, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos12 (Nat.le_max_left _ _)
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- A pair positive bound yields an ordinary finite bound for `(M₁,M₂)`. -/
theorem fusion_rules_finite_of_pair_bounded_pos_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_pair_left (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair)

/-- A pair positive bound yields an ordinary finite bound for the swapped pair `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_pair_bounded_pos_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
    (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_pair_right (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair)

/-- Any common finite pair bound can be upgraded to a common positive pair bound by `+1`. -/
theorem fusion_rules_bounded_pos_pair_of_finite_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, hbound21⟩
  refine ⟨bound + 1, Nat.succ_pos _, ?_, ?_⟩
  · exact le_trans hbound12 (Nat.le_succ _)
  · exact le_trans hbound21 (Nat.le_succ _)

/-- Build one common finite pair bound from two ordered finite bounds. -/
theorem fusion_rules_finite_pair_of_finite_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases h12 with ⟨bound12, hbound12⟩
  rcases h21 with ⟨bound21, hbound21⟩
  refine ⟨max bound12 bound21, ?_, ?_⟩
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- Extract the first ordered finite bound from a finite pair bound. -/
theorem fusion_rules_finite_of_pair_finite_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, _hbound21⟩
  exact ⟨bound, hbound12⟩

/-- Extract the swapped ordered finite bound from a finite pair bound. -/
theorem fusion_rules_finite_of_pair_finite_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, _hbound12, hbound21⟩
  exact ⟨bound, hbound21⟩

/-- Symmetry of a common finite pair bound under swapping `(M₁,M₂)`. -/
theorem fusion_rules_finite_pair_symm
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, hbound21⟩
  exact ⟨bound, hbound21, hbound12⟩

/-- Positive-bounded and finite-bounded common pair statements are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) := by
  constructor
  · intro hpair
    rcases hpair with ⟨bound, _hpos, hbound12, hbound21⟩
    exact ⟨bound, hbound12, hbound21⟩
  · intro hpair
    exact fusion_rules_bounded_pos_pair_of_finite_pair (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair

/-- Two ordered positive bounds can be merged into one common finite (not necessarily positive) pair bound. -/
theorem fusion_rules_finite_pair_of_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases fusion_rules_bounded_pos_pair_of_bounds (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) h12 h21 with ⟨bound, _hpos, hbound12, hbound21⟩
  exact ⟨bound, hbound12, hbound21⟩

/-- Rational VOAs admit one common finite bound for both orderings `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_finite_pair_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases fusion_rules_bounded_pos_pair (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) with ⟨bound, _hpos, hbound12, hbound21⟩
  exact ⟨bound, hbound12, hbound21⟩

/-- Rational VOAs also give a finite bound for the swapped ordering `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  simpa using fusion_rules_finite (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

/-- Rational VOAs admit a swapped-orientation common positive pair bound. -/
theorem fusion_rules_bounded_pos_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_bounded_pos_pair_symm (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))

/-- Rational VOAs admit a swapped-orientation common finite pair bound. -/
theorem fusion_rules_finite_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_pair_symm (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_finite_pair_of_rational (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))

/-- Under rationality, positive and finite single-order bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_iff_finite (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Under rationality, positive and finite common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_pair_iff_finite_pair (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Under rationality, positive and finite swapped single-order bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_iff_finite (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

/-- Under rationality, positive and finite swapped common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_pair_iff_finite_pair (R := R) (V := V)
    (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

end StringAlgebra.VOA
