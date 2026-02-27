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

/-! ## Conformal Vertex Algebra -/

/-- A conformal vertex algebra is a vertex algebra with a conformal vector ω.
    The Virasoro relation is stated in the scaled form:
    12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n}
    to avoid division in a general CommRing. -/
class ConformalVertexAlgebra (V : Type*) [AddCommGroup V] [Module R V]
    extends VertexAlgebra R V where
  /-- The conformal vector ω -/
  conformalVector : V
  /-- The central charge c -/
  centralCharge : R
  /-- L(-1) = T (translation generator) -/
  L_minus1_eq_translation : (Y conformalVector) 0 = translation
  /-- L(0) gives the grading (conformal weight) -/
  L0_grading : ∃ (weight : V → ℤ), ∀ a : V,
    (Y conformalVector) 1 a = (weight a : ℤ) • a
  /-- Virasoro relations (scaled by 12 to avoid division):
      12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n}
      With L_n = ω(n+1), this becomes a relation on ω modes. -/
  virasoro_relation : ∀ m n : ℤ,
    (12 : R) • ((Y conformalVector) (m + 1) ∘ₗ (Y conformalVector) (n + 1) -
    (Y conformalVector) (n + 1) ∘ₗ (Y conformalVector) (m + 1)) =
    (12 : R) • ((m - n : ℤ) • (Y conformalVector) (m + n + 1)) +
    if m + n = 0 then (centralCharge * (m^3 - m) : R) • LinearMap.id else 0

namespace ConformalVertexAlgebra

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The Virasoro modes L(n).
    With convention Y(ω, z) = ∑_n L_n z^{-n-2} and Y(a, z) = ∑_n a(n) z^{-n-1},
    we have L_n = ω(n+1). -/
def L [ConformalVertexAlgebra R V] (n : ℤ) : Module.End R V :=
  (VertexAlgebra.Y (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) (n + 1)

variable [ConformalVertexAlgebra R V]

/-- L(-1) is the translation operator -/
theorem L_minus1 : L (R := R) (V := V) (-1) = VertexAlgebra.translation (R := R) := by
  unfold L
  exact ConformalVertexAlgebra.L_minus1_eq_translation (R := R) (V := V)

@[simp] theorem L_apply (n : ℤ) (v : V) :
    L (R := R) (V := V) n v =
      (VertexAlgebra.Y (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V)))
        (n + 1) v := rfl

/-- Virasoro relation in terms of the `L` mode notation. -/
theorem virasoro_relation_L (m n : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) m) =
    (12 : R) • ((m - n : ℤ) • L (R := R) (V := V) (m + n)) +
      if m + n = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) • LinearMap.id
      else 0 := by
  simpa [L, add_assoc, add_comm, add_left_comm] using
    ConformalVertexAlgebra.virasoro_relation (R := R) (V := V) m n

/-- Applied vector form of the Virasoro relation in `L` notation. -/
theorem virasoro_relation_L_apply (m n : ℤ) (v : V) :
    ((12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) m)) v =
    ((12 : R) • ((m - n : ℤ) • L (R := R) (V := V) (m + n)) +
      if m + n = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
          (LinearMap.id : Module.End R V)
      else (0 : Module.End R V)) v := by
  exact congrArg (fun f : Module.End R V => f v) (virasoro_relation_L (R := R) (V := V) m n)

/-- Special case `[L(0), L(n)] = -n L(n)` in the scaled convention. -/
theorem virasoro_relation_L_zero_left (n : ℤ) :
    (12 : R) • (L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) 0) =
    (12 : R) • ((-n : ℤ) • L (R := R) (V := V) n) := by
  simpa using virasoro_relation_L (R := R) (V := V) 0 n

/-- Special case `[L(m), L(0)] = m L(m)` in the scaled convention. -/
theorem virasoro_relation_L_zero_right (m : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) 0 -
      L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) m) =
    (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) := by
  calc
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) 0 -
        L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) m) =
      (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) +
        (if m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else 0) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            virasoro_relation_L (R := R) (V := V) m 0
    _ = (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) := by
          by_cases hm : m = 0
          · simp [hm]
          · simp [hm]

/-- Diagonal specialization `m = n` of the scaled Virasoro relation. -/
theorem virasoro_relation_L_diag (m : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
      L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m) = 0 := by
  have hbase := virasoro_relation_L (R := R) (V := V) m m
  have hcentral :
      (if m + m = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
          (LinearMap.id : Module.End R V)
      else (0 : Module.End R V)) = 0 := by
    by_cases h2m : m + m = 0
    · have hm : m = 0 := by omega
      subst hm
      simp [h2m]
    · simp [h2m]
  calc
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
        L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m) =
      (12 : R) • ((m - m : ℤ) • L (R := R) (V := V) (m + m)) +
        (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by
          simpa [sub_eq_add_neg] using hbase
    _ = 0 + (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by simp
    _ = (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by simp
    _ = 0 := hcentral

/-- Applied form of `[L(m), L(m)] = 0` in the scaled convention. -/
theorem virasoro_relation_L_diag_apply (m : ℤ) (v : V) :
    ((12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
      L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m)) v = 0 := by
  exact congrArg (fun f : Module.End R V => f v)
    (virasoro_relation_L_diag (R := R) (V := V) m)

/-- Explicit witness of the `L(0)`-grading action. -/
structure L0Grading where
  /-- Weight function on states. -/
  weight : V → ℤ
  /-- `L(0)` acts by the weight on each state. -/
  weight_spec : ∀ a : V,
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 a = (weight a : ℤ) • a

/-- The conformal weight of a state from explicit grading data. -/
def conformalWeight (G : L0Grading (R := R) (V := V)) (a : V) : ℤ :=
  G.weight a

/-- `L(0)`-eigenvalue relation for the explicit conformal weight. -/
theorem conformalWeight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 a =
      (conformalWeight (R := R) (V := V) G a : ℤ) • a :=
  G.weight_spec a

/-- `L(0)`-action in terms of explicit grading witness `G`. -/
theorem L_zero_weight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    L (R := R) (V := V) 0 a = (G.weight a : ℤ) • a := by
  simpa [L] using G.weight_spec a

/-- `L(0)`-action using `conformalWeight` accessor. -/
theorem L_zero_conformalWeight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    L (R := R) (V := V) 0 a =
      (conformalWeight (R := R) (V := V) G a : ℤ) • a := by
  simpa [conformalWeight] using L_zero_weight_spec (R := R) (V := V) G a

/-- `ConformalVertexAlgebra.L0_grading` packaged as explicit data. -/
theorem exists_L0Grading : Nonempty (L0Grading (R := R) (V := V)) := by
  rcases ConformalVertexAlgebra.L0_grading (R := R) (V := V) with ⟨weight, hweight⟩
  exact ⟨⟨weight, hweight⟩⟩

/-- Existence of an `L(0)` weight function directly in `L`-notation. -/
theorem exists_weight_L0_action : ∃ (weight : V → ℤ), ∀ a : V,
    L (R := R) (V := V) 0 a = (weight a : ℤ) • a := by
  rcases exists_L0Grading (R := R) (V := V) with ⟨G⟩
  exact ⟨G.weight, fun a => by simpa [L] using G.weight_spec a⟩

/-- Existence of explicit conformal-weight grading data in `L`-notation form. -/
theorem exists_conformalWeight_action :
    ∃ G : L0Grading (R := R) (V := V), ∀ a : V,
      L (R := R) (V := V) 0 a = (conformalWeight (R := R) (V := V) G a : ℤ) • a := by
  rcases exists_L0Grading (R := R) (V := V) with ⟨G⟩
  exact ⟨G, fun a => L_zero_conformalWeight_spec (R := R) (V := V) G a⟩

/-- A primary state of weight h: L(n)a = 0 for n > 0, L(0)a = ha -/
structure PrimaryState where
  state : V
  weight : ℤ
  is_primary : ∀ n : ℕ, n > 0 → L (R := R) (V := V) (n : ℤ) state = 0
  weight_condition : L (R := R) (V := V) 0 state = (weight : ℤ) • state

namespace PrimaryState

@[simp] theorem weight_condition_apply (p : PrimaryState (R := R) (V := V)) :
    L (R := R) (V := V) 0 p.state = (p.weight : ℤ) • p.state :=
  p.weight_condition

theorem is_primary_of_pos (p : PrimaryState (R := R) (V := V)) (n : ℕ) (hn : n > 0) :
    L (R := R) (V := V) (n : ℤ) p.state = 0 :=
  p.is_primary n hn

@[simp] theorem is_primary_one (p : PrimaryState (R := R) (V := V)) :
    L (R := R) (V := V) (1 : ℤ) p.state = 0 := by
  simpa using p.is_primary 1 (by decide)

end PrimaryState

end ConformalVertexAlgebra

/-! ## Vertex Operator Algebra (VOA) -/

/-- A Vertex Operator Algebra (VOA) is a ℤ-graded conformal vertex algebra
    with the grading given by L(0) eigenvalues. -/
class VertexOperatorAlgebra (V : Type*) [AddCommGroup V] [Module R V]
    extends ConformalVertexAlgebra R V where
  /-- The graded components V = ⊕_n V_n -/
  component : ℤ → Submodule R V
  /-- V decomposes as a direct sum -/
  decomposition : ∀ v : V, ∃ (s : Finset ℤ), v ∈ ⨆ n ∈ s, component n
  /-- The grading matches L(0) eigenvalues -/
  grading_matches_L0 : ∀ n : ℤ, ∀ v ∈ component n,
    (Y conformalVector) 1 v = (n : ℤ) • v
  /-- Finite-dimensionality: each V_n is finite-dimensional -/
  finite_dimensional : ∀ n : ℤ, Module.Finite R (component n)
  /-- Lower truncation: V_n = 0 for n << 0 -/
  lower_truncated : ∃ N : ℤ, ∀ n : ℤ, n < N → component n = ⊥
  /-- The vacuum has weight 0: |0⟩ ∈ V_0 -/
  vacuum_weight : vacuum ∈ component 0
  /-- The conformal vector has weight 2: ω ∈ V_2 -/
  conformal_vector_weight : conformalVector ∈ component 2

namespace VertexOperatorAlgebra

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [VertexOperatorAlgebra R V]

theorem exists_decomposition (v : V) :
    ∃ (s : Finset ℤ), v ∈ ⨆ n ∈ s, VertexOperatorAlgebra.component (R := R) (V := V) n :=
  VertexOperatorAlgebra.decomposition (R := R) (V := V) v

theorem finite_component (n : ℤ) :
    Module.Finite R (VertexOperatorAlgebra.component (R := R) (V := V) n) :=
  VertexOperatorAlgebra.finite_dimensional (R := R) (V := V) n

theorem lower_truncated_exists :
    ∃ N : ℤ, ∀ n : ℤ, n < N → VertexOperatorAlgebra.component (R := R) (V := V) n = ⊥ :=
  VertexOperatorAlgebra.lower_truncated (R := R) (V := V)

@[simp] theorem vacuum_mem_component_zero :
    VertexAlgebra.vacuum (R := R) ∈ VertexOperatorAlgebra.component (R := R) (V := V) 0 :=
  VertexOperatorAlgebra.vacuum_weight (R := R) (V := V)

@[simp] theorem conformalVector_mem_component_two :
    ConformalVertexAlgebra.conformalVector (R := R) (V := V) ∈
      VertexOperatorAlgebra.component (R := R) (V := V) 2 :=
  VertexOperatorAlgebra.conformal_vector_weight (R := R) (V := V)

theorem L0_action_on_component (n : ℤ) (v : V)
    (hv : v ∈ VertexOperatorAlgebra.component (R := R) (V := V) n) :
    ConformalVertexAlgebra.L (R := R) (V := V) 0 v = (n : ℤ) • v := by
  simpa [ConformalVertexAlgebra.L] using
    VertexOperatorAlgebra.grading_matches_L0 (R := R) (V := V) n v hv

theorem L0_vacuum :
    ConformalVertexAlgebra.L (R := R) (V := V) 0 (VertexAlgebra.vacuum (R := R)) = 0 := by
  have h :=
    L0_action_on_component (R := R) (V := V) 0 (VertexAlgebra.vacuum (R := R))
      (vacuum_mem_component_zero (R := R) (V := V))
  simpa using h

theorem L0_conformalVector :
    ConformalVertexAlgebra.L (R := R) (V := V) 0
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) =
      (2 : ℤ) • (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) :=
  L0_action_on_component (R := R) (V := V) 2
    (ConformalVertexAlgebra.conformalVector (R := R) (V := V))
    (conformalVector_mem_component_two (R := R) (V := V))

end VertexOperatorAlgebra

/-! ## Morphisms of Vertex Algebras -/

/-- A morphism of vertex algebras preserving all structure -/
structure VertexAlgebraHom (V W : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    [AddCommGroup W] [Module R W] [VertexAlgebra R W] where
  /-- The underlying linear map -/
  toLinearMap : V →ₗ[R] W
  /-- Preserves the vertex operator: φ(Y(a,z)b) = Y(φ(a),z)φ(b) -/
  map_Y : ∀ a b : V, ∀ n : ℤ,
    toLinearMap ((VertexAlgebra.Y (R := R) a) n b) =
    (VertexAlgebra.Y (R := R) (toLinearMap a)) n (toLinearMap b)
  /-- Preserves the vacuum -/
  map_vacuum : toLinearMap (VertexAlgebra.vacuum (R := R)) =
               VertexAlgebra.vacuum (R := R)

/-- A VOA homomorphism also preserves the conformal vector -/
structure VOAHom (V W : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [AddCommGroup W] [Module R W] [VertexOperatorAlgebra R W]
    extends VertexAlgebraHom R V W where
  /-- Preserves the conformal vector -/
  map_conformal : toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) =
                  ConformalVertexAlgebra.conformalVector (R := R) (V := W)

namespace VertexAlgebraHom

variable {R : Type*} [CommRing R]
variable {V W U : Type*}
variable [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable [AddCommGroup W] [Module R W] [VertexAlgebra R W]
variable [AddCommGroup U] [Module R U] [VertexAlgebra R U]

/-- Identity vertex-algebra homomorphism. -/
def idHom (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    VertexAlgebraHom R V V where
  toLinearMap := LinearMap.id
  map_Y := by intro a b n; rfl
  map_vacuum := rfl

/-- Composition of vertex-algebra homomorphisms. -/
def compHom (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    VertexAlgebraHom R V U where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_Y := by
    intro a b n
    calc
      (g.toLinearMap.comp f.toLinearMap) ((VertexAlgebra.Y (R := R) a) n b)
          = g.toLinearMap (f.toLinearMap ((VertexAlgebra.Y (R := R) a) n b)) := rfl
      _ = g.toLinearMap ((VertexAlgebra.Y (R := R) (f.toLinearMap a)) n (f.toLinearMap b)) := by
            simpa using congrArg g.toLinearMap (f.map_Y a b n)
      _ = (VertexAlgebra.Y (R := R) (g.toLinearMap (f.toLinearMap a))) n
            (g.toLinearMap (f.toLinearMap b)) := by
              simpa using g.map_Y (f.toLinearMap a) (f.toLinearMap b) n
  map_vacuum := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (VertexAlgebra.vacuum (R := R))
          = g.toLinearMap (f.toLinearMap (VertexAlgebra.vacuum (R := R))) := rfl
      _ = g.toLinearMap (VertexAlgebra.vacuum (R := R)) := by simpa using congrArg g.toLinearMap f.map_vacuum
      _ = VertexAlgebra.vacuum (R := R) := g.map_vacuum

@[simp] theorem idHom_toLinearMap (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    (idHom (R := R) V).toLinearMap = LinearMap.id := rfl

@[simp] theorem compHom_toLinearMap (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    (compHom (R := R) g f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

@[simp] theorem compHom_apply (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap a = g.toLinearMap (f.toLinearMap a) := rfl

@[ext] theorem ext {f g : VertexAlgebraHom R V W} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  simp

@[simp] theorem idHom_apply (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] (a : V) :
    (idHom (R := R) V).toLinearMap a = a := rfl

@[simp] theorem compHom_id_right_apply (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) f (idHom (R := R) V)).toLinearMap a = f.toLinearMap a := by
  rfl

@[simp] theorem compHom_id_left_apply (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) (idHom (R := R) W) f).toLinearMap a = f.toLinearMap a := by
  rfl

theorem compHom_assoc_apply
    {X : Type*} [AddCommGroup X] [Module R X] [VertexAlgebra R X]
    (h : VertexAlgebraHom R U X) (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W)
    (a : V) :
    (compHom (R := R) h (compHom (R := R) g f)).toLinearMap a =
      (compHom (R := R) (compHom (R := R) h g) f).toLinearMap a := rfl

@[simp] theorem compHom_id_right (f : VertexAlgebraHom R V W) :
    compHom (R := R) f (idHom (R := R) V) = f := by
  ext a
  rfl

@[simp] theorem compHom_id_left (f : VertexAlgebraHom R V W) :
    compHom (R := R) (idHom (R := R) W) f = f := by
  ext a
  rfl

@[simp] theorem compHom_assoc
    {X : Type*} [AddCommGroup X] [Module R X] [VertexAlgebra R X]
    (h : VertexAlgebraHom R U X) (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    compHom (R := R) h (compHom (R := R) g f) =
      compHom (R := R) (compHom (R := R) h g) f := by
  ext a
  rfl

theorem map_nProduct_compHom
    (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W)
    (a b : V) (n : ℤ) :
    (compHom (R := R) g f).toLinearMap (VertexAlgebra.nProduct (R := R) (V := V) a n b) =
      VertexAlgebra.nProduct (R := R) (V := U)
        ((compHom (R := R) g f).toLinearMap a)
        n
        ((compHom (R := R) g f).toLinearMap b) := by
  simpa [VertexAlgebra.nProduct] using (compHom (R := R) g f).map_Y a b n

@[simp] theorem map_nProduct (f : VertexAlgebraHom R V W) (a b : V) (n : ℤ) :
    f.toLinearMap (VertexAlgebra.nProduct (R := R) (V := V) a n b) =
      VertexAlgebra.nProduct (R := R) (V := W) (f.toLinearMap a) n (f.toLinearMap b) := by
  simpa [VertexAlgebra.nProduct] using f.map_Y a b n

theorem map_nProduct_vacuum_left (f : VertexAlgebraHom R V W) (a : V) (n : ℤ) :
    f.toLinearMap
      (VertexAlgebra.nProduct (R := R) (V := V) (VertexAlgebra.vacuum (R := R)) n a) =
      VertexAlgebra.nProduct (R := R) (V := W) (VertexAlgebra.vacuum (R := R)) n (f.toLinearMap a) := by
  have h := f.map_nProduct (a := VertexAlgebra.vacuum (R := R)) (b := a) (n := n)
  rw [f.map_vacuum] at h
  exact h

theorem map_vacuum_minus1_action (f : VertexAlgebraHom R V W) (a : V) :
    f.toLinearMap
      (VertexAlgebra.nProduct (R := R) (V := V) (VertexAlgebra.vacuum (R := R)) (-1) a) =
      VertexAlgebra.nProduct (R := R) (V := W) (VertexAlgebra.vacuum (R := R)) (-1)
        (f.toLinearMap a) := by
  simpa using f.map_nProduct_vacuum_left (a := a) (-1)

end VertexAlgebraHom

namespace VOAHom

variable {R : Type*} [CommRing R]
variable {V W U : Type*}
variable [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
variable [AddCommGroup W] [Module R W] [VertexOperatorAlgebra R W]
variable [AddCommGroup U] [Module R U] [VertexOperatorAlgebra R U]

/-- Identity VOA homomorphism. -/
def idHom (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] :
    VOAHom R V V where
  toLinearMap := LinearMap.id
  map_Y := by intro a b n; rfl
  map_vacuum := rfl
  map_conformal := rfl

/-- Composition of VOA homomorphisms. -/
def compHom (g : VOAHom R W U) (f : VOAHom R V W) : VOAHom R V U where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_Y := by
    intro a b n
    calc
      (g.toLinearMap.comp f.toLinearMap) ((VertexAlgebra.Y (R := R) a) n b)
          = g.toLinearMap (f.toLinearMap ((VertexAlgebra.Y (R := R) a) n b)) := rfl
      _ = g.toLinearMap ((VertexAlgebra.Y (R := R) (f.toLinearMap a)) n (f.toLinearMap b)) := by
            simpa using congrArg g.toLinearMap (f.map_Y a b n)
      _ = (VertexAlgebra.Y (R := R) (g.toLinearMap (f.toLinearMap a))) n
            (g.toLinearMap (f.toLinearMap b)) := by
              simpa using g.map_Y (f.toLinearMap a) (f.toLinearMap b) n
  map_vacuum := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (VertexAlgebra.vacuum (R := R))
          = g.toLinearMap (f.toLinearMap (VertexAlgebra.vacuum (R := R))) := rfl
      _ = g.toLinearMap (VertexAlgebra.vacuum (R := R)) := by
            simpa using congrArg g.toLinearMap f.map_vacuum
      _ = VertexAlgebra.vacuum (R := R) := g.map_vacuum
  map_conformal := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))
          = g.toLinearMap (f.toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) := rfl
      _ = g.toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := W)) := by
            simpa using congrArg g.toLinearMap f.map_conformal
      _ = ConformalVertexAlgebra.conformalVector (R := R) (V := U) := g.map_conformal

@[simp] theorem idHom_toLinearMap (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] :
    (idHom (R := R) V).toLinearMap = LinearMap.id := rfl

@[simp] theorem compHom_toLinearMap (g : VOAHom R W U) (f : VOAHom R V W) :
    (compHom (R := R) g f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

@[simp] theorem compHom_apply (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap a = g.toLinearMap (f.toLinearMap a) := rfl

@[simp] theorem idHom_apply (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (a : V) :
    (idHom (R := R) V).toLinearMap a = a := rfl

@[simp] theorem compHom_id_right_apply (f : VOAHom R V W) (a : V) :
    (compHom (R := R) f (idHom (R := R) V)).toLinearMap a = f.toLinearMap a := by
  rfl

@[simp] theorem compHom_id_left_apply (f : VOAHom R V W) (a : V) :
    (compHom (R := R) (idHom (R := R) W) f).toLinearMap a = f.toLinearMap a := by
  rfl

theorem compHom_assoc_apply
    {X : Type*} [AddCommGroup X] [Module R X] [VertexOperatorAlgebra R X]
    (h : VOAHom R U X) (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) h (compHom (R := R) g f)).toLinearMap a =
      (compHom (R := R) (compHom (R := R) h g) f).toLinearMap a := rfl

@[simp] theorem compHom_id_right (f : VOAHom R V W) :
    compHom (R := R) f (idHom (R := R) V) = f := by
  cases f
  rfl

@[simp] theorem compHom_id_left (f : VOAHom R V W) :
    compHom (R := R) (idHom (R := R) W) f = f := by
  cases f
  rfl

@[simp] theorem compHom_assoc
    {X : Type*} [AddCommGroup X] [Module R X] [VertexOperatorAlgebra R X]
    (h : VOAHom R U X) (g : VOAHom R W U) (f : VOAHom R V W) :
    compHom (R := R) h (compHom (R := R) g f) =
      compHom (R := R) (compHom (R := R) h g) f := by
  cases h
  cases g
  cases f
  rfl

theorem map_L (f : VOAHom R V W) (n : ℤ) (a : V) :
    f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) n a) =
      ConformalVertexAlgebra.L (R := R) (V := W) n (f.toLinearMap a) := by
  change f.toLinearMap
      ((VertexAlgebra.Y (R := R)
        (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) (n + 1) a) =
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := W))) (n + 1) (f.toLinearMap a)
  simpa [f.map_conformal] using
    f.map_Y (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) a (n + 1)

theorem map_translation (f : VOAHom R V W) (a : V) :
    f.toLinearMap (VertexAlgebra.translation (R := R) a) =
      VertexAlgebra.translation (R := R) (f.toLinearMap a) := by
  simpa [ConformalVertexAlgebra.L_minus1 (R := R) (V := V),
      ConformalVertexAlgebra.L_minus1 (R := R) (V := W)] using
    f.map_L (-1) a

theorem map_L_compHom (g : VOAHom R W U) (f : VOAHom R V W) (n : ℤ) (a : V) :
    (compHom (R := R) g f).toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) n a) =
      ConformalVertexAlgebra.L (R := R) (V := U) n
        ((compHom (R := R) g f).toLinearMap a) := by
  simpa using (compHom (R := R) g f).map_L n a

theorem map_translation_compHom (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap (VertexAlgebra.translation (R := R) a) =
      VertexAlgebra.translation (R := R) ((compHom (R := R) g f).toLinearMap a) := by
  simpa using (compHom (R := R) g f).map_translation a

def mapPrimaryState (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ConformalVertexAlgebra.PrimaryState (R := R) (V := W) where
  state := f.toLinearMap p.state
  weight := p.weight
  is_primary := by
    intro n hn
    calc
      ConformalVertexAlgebra.L (R := R) (V := W) (n : ℤ) (f.toLinearMap p.state)
          = f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) (n : ℤ) p.state) := by
              simpa using (f.map_L (n : ℤ) p.state).symm
      _ = f.toLinearMap 0 := by
            simpa using congrArg f.toLinearMap (p.is_primary n hn)
      _ = 0 := by simp
  weight_condition := by
    calc
      ConformalVertexAlgebra.L (R := R) (V := W) 0 (f.toLinearMap p.state)
          = f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) 0 p.state) := by
              simpa using (f.map_L 0 p.state).symm
      _ = f.toLinearMap ((p.weight : ℤ) • p.state) := by
            simpa using congrArg f.toLinearMap p.weight_condition
      _ = (p.weight : ℤ) • f.toLinearMap p.state := by simp

@[simp] theorem mapPrimaryState_state (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    (f.mapPrimaryState p).state = f.toLinearMap p.state := rfl

@[simp] theorem mapPrimaryState_weight (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    (f.mapPrimaryState p).weight = p.weight := rfl

@[simp] theorem mapPrimaryState_comp_state
    (g : VOAHom R W U) (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ((compHom (R := R) g f).mapPrimaryState p).state = g.toLinearMap (f.toLinearMap p.state) := rfl

@[simp] theorem mapPrimaryState_comp_weight
    (g : VOAHom R W U) (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ((compHom (R := R) g f).mapPrimaryState p).weight = p.weight := rfl

end VOAHom

end StringAlgebra.VOA
