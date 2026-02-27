/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.FormalDistributions

/-!
# Vertex Algebras

This file defines vertex algebras and vertex operator algebras (VOAs).

## Main Definitions

* `VertexAlgebra` - A vertex algebra (V, Y, |0⟩, T)
* `VertexOperatorAlgebra` - A VOA with conformal vector ω

## Main Results

* `vacuum_axiom` - Y(|0⟩, z) = Id
* `creation_axiom` - Y(a, z)|0⟩|_{z=0} = a
* `translation_axiom` - [T, Y(a, z)] = ∂_z Y(a, z)
* `locality` - (z-w)^N [Y(a,z), Y(b,w)] = 0 for some N

## References

* Borcherds, "Vertex algebras, Kac-Moody algebras, and the Monster"
* Frenkel, Lepowsky, Meurman, "Vertex Operator Algebras and the Monster"
* Kac, "Vertex Algebras for Beginners"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Vertex Algebra Definition -/

/-- A vertex algebra over R. -/
class VertexAlgebra (V : Type*) [AddCommGroup V] [Module R V] where
  /-- The vertex operator map: a ↦ Y(a, z) = ∑_n a(n) z^{-n-1} -/
  Y : V → FormalDistribution R V
  /-- The vacuum vector |0⟩ -/
  vacuum : V
  /-- The translation operator T -/
  translation : Module.End R V
  /-- **Vacuum Axiom**: Y(|0⟩, z) = Id_V (the identity field) -/
  vacuum_axiom : Y vacuum = FormalDistribution.identity
  /-- **Creation Axiom (annihilation)**: a(n)|0⟩ = 0 for n ≥ 0 -/
  creation_axiom_annihilation : ∀ a : V, ∀ n : ℕ, (Y a) n vacuum = 0
  /-- **Creation Axiom (value)**: a(-1)|0⟩ = a -/
  creation_axiom_value : ∀ a : V, (Y a) (-1) vacuum = a
  /-- **Lower Truncation Axiom**: for all a, b, a(n)b = 0 for n >> 0. -/
  lower_truncation : ∀ a b : V, ∃ N : ℤ, ∀ n : ℤ, n > N → (Y a) n b = 0
  /-- **Translation Axiom**: [T, a(n)] = -n · a(n-1) -/
  translation_axiom : ∀ a : V, ∀ n : ℤ,
    translation ∘ₗ (Y a) n - (Y a) n ∘ₗ translation = (-n : ℤ) • (Y a) (n - 1)
  /-- **Translation-Derivative Axiom**: Y(T(a), z) = ∂_z Y(a, z). -/
  translation_derivative_axiom : ∀ a : V,
    Y (translation a) = FormalDistribution.derivative (Y a)
  /-- **Translation on vacuum**: T|0⟩ = 0 -/
  translation_vacuum : translation vacuum = 0
  /-- **Locality Axiom**: For all a, b ∈ V, Y(a, z) and Y(b, z) are mutually local. -/
  locality : ∀ a b : V, mutuallyLocal R V (Y a) (Y b)

namespace VertexAlgebra

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]

/-- The n-th product of a and b: a(n)b -/
def nProduct (a : V) (n : ℤ) (b : V) : V := (VertexAlgebra.Y (R := R) a) n b

@[simp] theorem nProduct_zero_right (a : V) (n : ℤ) :
    nProduct (R := R) a n (0 : V) = 0 := by
  simp [nProduct]

@[simp] theorem nProduct_add_right (a : V) (n : ℤ) (b c : V) :
    nProduct (R := R) a n (b + c) =
      nProduct (R := R) a n b + nProduct (R := R) a n c := by
  simp [nProduct]

@[simp] theorem nProduct_smul_right (a : V) (n : ℤ) (r : R) (b : V) :
    nProduct (R := R) a n (r • b) = r • nProduct (R := R) a n b := by
  simp [nProduct]

@[simp] theorem nProduct_neg_right (a : V) (n : ℤ) (b : V) :
    nProduct (R := R) a n (-b) = -nProduct (R := R) a n b := by
  simp [nProduct]

@[simp] theorem nProduct_sub_right (a : V) (n : ℤ) (b c : V) :
    nProduct (R := R) a n (b - c) =
      nProduct (R := R) a n b - nProduct (R := R) a n c := by
  simp [sub_eq_add_neg]

/-- The vacuum is annihilated by positive modes of the identity field -/
theorem vacuum_annihilates_positive (a : V) (n : ℕ) :
    nProduct (R := R) (VertexAlgebra.vacuum (R := R)) n a = 0 := by
  simp only [nProduct]
  rw [VertexAlgebra.vacuum_axiom (R := R)]
  unfold FormalDistribution.identity
  have h : (n : ℤ) ≠ -1 := by omega
  simp [h]

/-- The (-1)-product with vacuum gives the identity: |0⟩(-1)a = a -/
theorem vacuum_minus1_product (a : V) :
    nProduct (R := R) (VertexAlgebra.vacuum (R := R)) (-1) a = a := by
  simp only [nProduct]
  rw [VertexAlgebra.vacuum_axiom (R := R)]
  simp [FormalDistribution.identity]

/-- Y(T(a), z) = ∂_z Y(a, z) -/
theorem translation_derivative (a : V) :
    VertexAlgebra.Y (R := R) (VertexAlgebra.translation (R := R) a) =
    FormalDistribution.derivative (VertexAlgebra.Y (R := R) a) := by
  simpa using VertexAlgebra.translation_derivative_axiom (R := R) a

/-- Applied form of the translation commutator identity. -/
theorem translation_commutator_apply (a : V) (n : ℤ) (v : V) :
    VertexAlgebra.translation (R := R) (nProduct (R := R) a n v) -
      nProduct (R := R) a n (VertexAlgebra.translation (R := R) v) =
      (-n : ℤ) • nProduct (R := R) a (n - 1) v := by
  simpa [nProduct] using
    congrArg (fun f : Module.End R V => f v) (VertexAlgebra.translation_axiom (R := R) a n)

/-- Rearranged translation commutator: `T(a(n)v) = a(n)T(v) + (-n)a(n-1)v`. -/
theorem translation_apply_nProduct (a : V) (n : ℤ) (v : V) :
    VertexAlgebra.translation (R := R) (nProduct (R := R) a n v) =
      nProduct (R := R) a n (VertexAlgebra.translation (R := R) v) +
      (-n : ℤ) • nProduct (R := R) a (n - 1) v := by
  have h :=
    sub_eq_iff_eq_add.mp (translation_commutator_apply (R := R) a n v)
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- `Y(T|0⟩,z) = 0` from translation-derivative plus the vacuum field identity. -/
theorem Y_translation_vacuum_eq_zero :
    VertexAlgebra.Y (R := R) (VertexAlgebra.translation (R := R) (VertexAlgebra.vacuum (R := R))) =
      (0 : FormalDistribution R V) := by
  calc
    VertexAlgebra.Y (R := R) (VertexAlgebra.translation (R := R) (VertexAlgebra.vacuum (R := R)))
        = FormalDistribution.derivative
            (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) := by
              simpa using
                VertexAlgebra.translation_derivative_axiom (R := R) (VertexAlgebra.vacuum (R := R))
    _ = FormalDistribution.derivative (FormalDistribution.identity : FormalDistribution R V) := by
          simp [VertexAlgebra.vacuum_axiom (R := R)]
    _ = (0 : FormalDistribution R V) := by simp

/-- Derivation of `T|0⟩ = 0` from the translation-derivative axiom and creation axiom. -/
theorem translation_vacuum_from_derivative :
    VertexAlgebra.translation (R := R) (VertexAlgebra.vacuum (R := R)) = (0 : V) := by
  have hY := Y_translation_vacuum_eq_zero (R := R) (V := V)
  have hmode := congrArg
    (fun F : FormalDistribution R V => F (-1) (VertexAlgebra.vacuum (R := R))) hY
  simpa [VertexAlgebra.creation_axiom_value (R := R)] using hmode

/-- Every state field satisfies the field property (restatement of lower truncation). -/
theorem Y_hasFieldProperty (a : V) :
    FormalDistribution.hasFieldProperty (VertexAlgebra.Y (R := R) a) := by
  intro v
  exact VertexAlgebra.lower_truncation (R := R) a v

/-- For fixed mode `j`, the `nthProduct` of two state fields has field property
    in the second state argument. -/
theorem Y_nthProduct_hasFieldProperty_right (a b : V) (j : ℤ) :
    FormalDistribution.hasFieldProperty
      (nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) j) := by
  exact hasFieldProperty_nthProduct_right (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) j (Y_hasFieldProperty (R := R) b)

/-- The normal-ordered product of two state fields has field property
    in the second state argument. -/
theorem Y_normalOrderedProduct_hasFieldProperty_right (a b : V) :
    FormalDistribution.hasFieldProperty
      (normalOrderedProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b)) := by
  simpa [normalOrderedProduct] using
    Y_nthProduct_hasFieldProperty_right (R := R) (a := a) (b := b) (-1)

/-- Locality is symmetric in VOA states. -/
theorem locality_symm (a b : V) :
    mutuallyLocal R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) := by
  exact (mutuallyLocal_symm (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (VertexAlgebra.locality (R := R) a b)

/-- The vacuum field is local with every state field (left form). -/
theorem locality_vacuum_left (a : V) :
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R)))
      (VertexAlgebra.Y (R := R) a) :=
  VertexAlgebra.locality (R := R) (VertexAlgebra.vacuum (R := R)) a

/-- The vacuum field is local with every state field (right form). -/
theorem locality_vacuum_right (a : V) :
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) a)
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) :=
  locality_symm (R := R) (a := VertexAlgebra.vacuum (R := R)) (b := a)

/-- Any field is local with itself. -/
theorem locality_self (a : V) :
    mutuallyLocal R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) a) :=
  VertexAlgebra.locality (R := R) a a

/-- Locality is closed under addition in the left state argument. -/
theorem locality_add_left (a b c : V) :
    (VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b) →
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) (a + b))
      (VertexAlgebra.Y (R := R) c) := by
  intro hYadd
  simpa [hYadd] using mutuallyLocal_add_left (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c)
    (VertexAlgebra.locality (R := R) a c) (VertexAlgebra.locality (R := R) b c)

/-- Locality is closed under addition in the right state argument. -/
theorem locality_add_right (a b c : V) :
    (VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c) →
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) a)
      (VertexAlgebra.Y (R := R) (b + c)) := by
  intro hYadd
  simpa [hYadd] using mutuallyLocal_add_right (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c)
    (VertexAlgebra.locality (R := R) a b) (VertexAlgebra.locality (R := R) a c)

/-- Locality is closed under subtraction in the left state argument. -/
theorem locality_sub_left (a b c : V) :
    (VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b) →
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) (a - b))
      (VertexAlgebra.Y (R := R) c) := by
  intro hYsub
  simpa [hYsub] using mutuallyLocal_sub_left (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c)
    (VertexAlgebra.locality (R := R) a c) (VertexAlgebra.locality (R := R) b c)

/-- Locality is closed under subtraction in the right state argument. -/
theorem locality_sub_right (a b c : V) :
    (VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c) →
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) a)
      (VertexAlgebra.Y (R := R) (b - c)) := by
  intro hYsub
  simpa [hYsub] using mutuallyLocal_sub_right (R := R) (V := V)
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c)
    (VertexAlgebra.locality (R := R) a b) (VertexAlgebra.locality (R := R) a c)

/-- Assumption package encoding Dong-style closure on state fields. -/
class DongClosed : Prop where
  closure :
    ∀ a b c : V, ∀ n : ℤ,
      mutuallyLocal R V
        (nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) n)
        (VertexAlgebra.Y (R := R) c)

/-- Assumption package: each triple of state fields comes with Dong-closure data. -/
class DongClosedData : Prop where
  data :
    ∀ a b c : V,
      DongLemmaData (R := R) (V := V)
        (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c)

/-- `DongClosedData` implies `DongClosed` by applying VOA locality to the Dong witness. -/
instance (priority := 100) dongClosed_of_dongClosedData [DongClosedData (R := R) (V := V)] :
    DongClosed (R := R) (V := V) where
  closure := by
    intro a b c n
    exact (DongClosedData.data (R := R) (V := V) a b c).closure n
      (VertexAlgebra.locality (R := R) a b)
      (VertexAlgebra.locality (R := R) a c)
      (VertexAlgebra.locality (R := R) b c)

/-- Under Dong closure, `nthProduct` of state fields is local with any state field. -/
theorem locality_nthProduct [DongClosed (R := R) (V := V)] (a b c : V) (n : ℤ) :
    mutuallyLocal R V
      (nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) n)
      (VertexAlgebra.Y (R := R) c) :=
  DongClosed.closure (R := R) (V := V) a b c n

/-- Symmetric form of Dong-closed locality for state-field `nthProduct`s. -/
theorem locality_right_nthProduct [DongClosed (R := R) (V := V)] (a b c : V) (n : ℤ) :
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) c)
      (nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) n) := by
  exact mutuallyLocal_symm (R := R) (V := V)
    (nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) n)
    (VertexAlgebra.Y (R := R) c)
    (locality_nthProduct (R := R) (V := V) a b c n)

/-- Under Dong closure, normal-ordered state fields are local with any state field. -/
theorem locality_normalOrderedProduct [DongClosed (R := R) (V := V)] (a b c : V) :
    mutuallyLocal R V
      (normalOrderedProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
      (VertexAlgebra.Y (R := R) c) := by
  simpa [normalOrderedProduct] using locality_nthProduct (R := R) (V := V) a b c (-1)

/-- Symmetric form for Dong-closed normal-ordered locality. -/
theorem locality_right_normalOrderedProduct [DongClosed (R := R) (V := V)] (a b c : V) :
    mutuallyLocal R V
      (VertexAlgebra.Y (R := R) c)
      (normalOrderedProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b)) := by
  exact mutuallyLocal_symm (R := R) (V := V)
    (normalOrderedProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (VertexAlgebra.Y (R := R) c)
    (locality_normalOrderedProduct (R := R) (V := V) a b c)

/-- The state-field correspondence is injective -/
theorem state_field_injective : Function.Injective (VertexAlgebra.Y (R := R) (V := V)) := by
  intro a b hab
  have h1 : (VertexAlgebra.Y (R := R) a) (-1) (VertexAlgebra.vacuum (R := R)) =
            (VertexAlgebra.Y (R := R) b) (-1) (VertexAlgebra.vacuum (R := R)) := by rw [hab]
  rw [VertexAlgebra.creation_axiom_value (R := R),
      VertexAlgebra.creation_axiom_value (R := R)] at h1
  exact h1

end VertexAlgebra

end StringAlgebra.VOA
