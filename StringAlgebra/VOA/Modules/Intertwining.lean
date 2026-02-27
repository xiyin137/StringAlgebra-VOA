/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Modules.Core

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

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


end StringAlgebra.VOA
