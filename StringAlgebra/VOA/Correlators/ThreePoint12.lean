/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Correlators.Basics

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-- Three-point commutator in the first two insertions:
    `⟨c(k)(b(n)a(m) - a(m)b(n))⟩`. -/
def threePointCommutator12
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k - threePointModes (R := R) ω b a c n m k

/-- Three-point anticommutator in the first two insertions:
    `⟨c(k)(b(n)a(m) + a(m)b(n))⟩`. -/
def threePointAnticommutator12
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k + threePointModes (R := R) ω b a c n m k

/-- Three-point commutator in the first two insertions, with state inputs. -/
def threePointStateCommutator12
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointCommutator12 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

/-- Three-point anticommutator in the first two insertions, with state inputs. -/
def threePointStateAnticommutator12
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointAnticommutator12 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointCommutator12_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((c k) (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) -
          (a m) ((b n) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointCommutator12, threePointModes_eq, map_sub]

@[simp] theorem threePointAnticommutator12_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((c k) (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) +
          (a m) ((b n) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointAnticommutator12, threePointModes_eq, map_add]

@[simp] theorem threePointStateCommutator12_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k -
        threePointStateModes (R := R) ω b a c n m k := by
  rfl

@[simp] theorem threePointStateAnticommutator12_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k +
        threePointStateModes (R := R) ω b a c n m k := by
  rfl

@[simp] theorem threePointStateCommutator12_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) -
            (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateCommutator12
  exact threePointCommutator12_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointStateAnticommutator12_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) +
            (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateAnticommutator12
  exact threePointAnticommutator12_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

/-- `(1,2)` commutator is additive in the first field slot. -/
theorem threePointCommutator12_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω (a + b) c d m n k =
      threePointCommutator12 (R := R) ω a c d m n k +
        threePointCommutator12 (R := R) ω b c d m n k := by
  unfold threePointCommutator12
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) c a b d n m k]
  abel_nf

/-- `(1,2)` commutator is additive in the second field slot. -/
theorem threePointCommutator12_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a (b + c) d m n k =
      threePointCommutator12 (R := R) ω a b d m n k +
        threePointCommutator12 (R := R) ω a c d m n k := by
  unfold threePointCommutator12
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) b c a d n m k]
  abel_nf

/-- `(1,2)` commutator is additive in the third field slot. -/
theorem threePointCommutator12_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b (c + d) m n k =
      threePointCommutator12 (R := R) ω a b c m n k +
        threePointCommutator12 (R := R) ω a b d m n k := by
  unfold threePointCommutator12
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) b a c d n m k]
  abel_nf

/-- `(1,2)` commutator is linear under scalar multiplication in the first slot. -/
theorem threePointCommutator12_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω (r • a) b c m n k =
      r • threePointCommutator12 (R := R) ω a b c m n k := by
  unfold threePointCommutator12
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r b a c n m k]
  simp [mul_sub]

/-- `(1,2)` commutator is linear under scalar multiplication in the middle slot. -/
theorem threePointCommutator12_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a (r • b) c m n k =
      r • threePointCommutator12 (R := R) ω a b c m n k := by
  unfold threePointCommutator12
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r b a c n m k]
  simp [mul_sub]

/-- `(1,2)` commutator is linear under scalar multiplication in the third slot. -/
theorem threePointCommutator12_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b (r • c) m n k =
      r • threePointCommutator12 (R := R) ω a b c m n k := by
  unfold threePointCommutator12
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r b a c n m k]
  simp [mul_sub]

/-- `(1,2)` anticommutator is additive in the first field slot. -/
theorem threePointAnticommutator12_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω (a + b) c d m n k =
      threePointAnticommutator12 (R := R) ω a c d m n k +
        threePointAnticommutator12 (R := R) ω b c d m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) c a b d n m k]
  abel_nf

/-- `(1,2)` anticommutator is additive in the second field slot. -/
theorem threePointAnticommutator12_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a (b + c) d m n k =
      threePointAnticommutator12 (R := R) ω a b d m n k +
        threePointAnticommutator12 (R := R) ω a c d m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) b c a d n m k]
  abel_nf

/-- `(1,2)` anticommutator is additive in the third field slot. -/
theorem threePointAnticommutator12_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b (c + d) m n k =
      threePointAnticommutator12 (R := R) ω a b c m n k +
        threePointAnticommutator12 (R := R) ω a b d m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) b a c d n m k]
  abel_nf

/-- `(1,2)` anticommutator is linear under scalar multiplication in the first slot. -/
theorem threePointAnticommutator12_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω (r • a) b c m n k =
      r • threePointAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r b a c n m k]
  simp [mul_add]

/-- `(1,2)` anticommutator is linear under scalar multiplication in the middle slot. -/
theorem threePointAnticommutator12_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a (r • b) c m n k =
      r • threePointAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r b a c n m k]
  simp [mul_add]

/-- `(1,2)` anticommutator is linear under scalar multiplication in the third slot. -/
theorem threePointAnticommutator12_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b (r • c) m n k =
      r • threePointAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator12
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r b a c n m k]
  simp [mul_add]

/-- `(1,2)` commutator is negation-linear in the first field slot. -/
theorem threePointCommutator12_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω (-a) b c m n k =
      -threePointCommutator12 (R := R) ω a b c m n k := by
  simpa using threePointCommutator12_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` commutator is negation-linear in the middle field slot. -/
theorem threePointCommutator12_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a (-b) c m n k =
      -threePointCommutator12 (R := R) ω a b c m n k := by
  simpa using threePointCommutator12_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` commutator is negation-linear in the third field slot. -/
theorem threePointCommutator12_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b (-c) m n k =
      -threePointCommutator12 (R := R) ω a b c m n k := by
  simpa using threePointCommutator12_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` anticommutator is negation-linear in the first field slot. -/
theorem threePointAnticommutator12_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω (-a) b c m n k =
      -threePointAnticommutator12 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator12_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` anticommutator is negation-linear in the middle field slot. -/
theorem threePointAnticommutator12_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a (-b) c m n k =
      -threePointAnticommutator12 (R := R) ω a b c m n k := by
  simpa using
    threePointAnticommutator12_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` anticommutator is negation-linear in the third field slot. -/
theorem threePointAnticommutator12_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b (-c) m n k =
      -threePointAnticommutator12 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator12_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,2)` commutator is subtraction-linear in the first field slot. -/
theorem threePointCommutator12_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω (a - b) c d m n k =
      threePointCommutator12 (R := R) ω a c d m n k -
        threePointCommutator12 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator12_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointCommutator12_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,2)` commutator is subtraction-linear in the middle field slot. -/
theorem threePointCommutator12_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a (b - c) d m n k =
      threePointCommutator12 (R := R) ω a b d m n k -
        threePointCommutator12 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator12_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointCommutator12_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,2)` commutator is subtraction-linear in the third field slot. -/
theorem threePointCommutator12_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b (c - d) m n k =
      threePointCommutator12 (R := R) ω a b c m n k -
        threePointCommutator12 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator12_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointCommutator12_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- `(1,2)` anticommutator is subtraction-linear in the first field slot. -/
theorem threePointAnticommutator12_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω (a - b) c d m n k =
      threePointAnticommutator12 (R := R) ω a c d m n k -
        threePointAnticommutator12 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator12_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointAnticommutator12_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,2)` anticommutator is subtraction-linear in the middle field slot. -/
theorem threePointAnticommutator12_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a (b - c) d m n k =
      threePointAnticommutator12 (R := R) ω a b d m n k -
        threePointAnticommutator12 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator12_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointAnticommutator12_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,2)` anticommutator is subtraction-linear in the third field slot. -/
theorem threePointAnticommutator12_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b (c - d) m n k =
      threePointAnticommutator12 (R := R) ω a b c m n k -
        threePointAnticommutator12 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator12_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointAnticommutator12_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- State-level `(1,2)` commutator is additive in the first field slot. -/
theorem threePointStateCommutator12_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω (a + b) c d m n k =
      threePointStateCommutator12 (R := R) ω a c d m n k +
        threePointStateCommutator12 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator12
  simpa [hYadd] using
    (threePointCommutator12_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` commutator is additive in the second field slot. -/
theorem threePointStateCommutator12_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a (b + c) d m n k =
      threePointStateCommutator12 (R := R) ω a b d m n k +
        threePointStateCommutator12 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator12
  simpa [hYadd] using
    (threePointCommutator12_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` commutator is additive in the third field slot. -/
theorem threePointStateCommutator12_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b (c + d) m n k =
      threePointStateCommutator12 (R := R) ω a b c m n k +
        threePointStateCommutator12 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator12
  simpa [hYadd] using
    (threePointCommutator12_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` commutator is linear under scalar multiplication in the
    first slot. -/
theorem threePointStateCommutator12_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω (r • a) b c m n k =
      r • threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYsmul] using
    (threePointCommutator12_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is linear under scalar multiplication in the
    middle slot. -/
theorem threePointStateCommutator12_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a (r • b) c m n k =
      r • threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYsmul] using
    (threePointCommutator12_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is linear under scalar multiplication in the
    third slot. -/
theorem threePointStateCommutator12_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b (r • c) m n k =
      r • threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYsmul] using
    (threePointCommutator12_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is negation-linear in the first slot. -/
theorem threePointStateCommutator12_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω (-a) b c m n k =
      -threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYneg] using
    (threePointCommutator12_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is negation-linear in the middle slot. -/
theorem threePointStateCommutator12_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a (-b) c m n k =
      -threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYneg] using
    (threePointCommutator12_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is negation-linear in the third slot. -/
theorem threePointStateCommutator12_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b (-c) m n k =
      -threePointStateCommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator12
  simpa [hYneg] using
    (threePointCommutator12_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` commutator is subtraction-linear in the first slot. -/
theorem threePointStateCommutator12_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω (a - b) c d m n k =
      threePointStateCommutator12 (R := R) ω a c d m n k -
        threePointStateCommutator12 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator12
  simpa [hYsub] using
    (threePointCommutator12_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` commutator is subtraction-linear in the middle slot. -/
theorem threePointStateCommutator12_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a (b - c) d m n k =
      threePointStateCommutator12 (R := R) ω a b d m n k -
        threePointStateCommutator12 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator12
  simpa [hYsub] using
    (threePointCommutator12_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` commutator is subtraction-linear in the third slot. -/
theorem threePointStateCommutator12_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b (c - d) m n k =
      threePointStateCommutator12 (R := R) ω a b c m n k -
        threePointStateCommutator12 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator12
  simpa [hYsub] using
    (threePointCommutator12_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is additive in the first field slot. -/
theorem threePointStateAnticommutator12_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω (a + b) c d m n k =
      threePointStateAnticommutator12 (R := R) ω a c d m n k +
        threePointStateAnticommutator12 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYadd] using
    (threePointAnticommutator12_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is additive in the middle field slot. -/
theorem threePointStateAnticommutator12_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a (b + c) d m n k =
      threePointStateAnticommutator12 (R := R) ω a b d m n k +
        threePointStateAnticommutator12 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYadd] using
    (threePointAnticommutator12_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is additive in the third field slot. -/
theorem threePointStateAnticommutator12_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b (c + d) m n k =
      threePointStateAnticommutator12 (R := R) ω a b c m n k +
        threePointStateAnticommutator12 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYadd] using
    (threePointAnticommutator12_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is linear under scalar multiplication in
    the first slot. -/
theorem threePointStateAnticommutator12_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω (r • a) b c m n k =
      r • threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsmul] using
    (threePointAnticommutator12_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is linear under scalar multiplication in
    the middle slot. -/
theorem threePointStateAnticommutator12_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a (r • b) c m n k =
      r • threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsmul] using
    (threePointAnticommutator12_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is linear under scalar multiplication in
    the third slot. -/
theorem threePointStateAnticommutator12_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b (r • c) m n k =
      r • threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsmul] using
    (threePointAnticommutator12_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is negation-linear in the first slot. -/
theorem threePointStateAnticommutator12_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω (-a) b c m n k =
      -threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYneg] using
    (threePointAnticommutator12_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is negation-linear in the middle slot. -/
theorem threePointStateAnticommutator12_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a (-b) c m n k =
      -threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYneg] using
    (threePointAnticommutator12_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is negation-linear in the third slot. -/
theorem threePointStateAnticommutator12_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b (-c) m n k =
      -threePointStateAnticommutator12 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYneg] using
    (threePointAnticommutator12_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator is subtraction-linear in the first slot. -/
theorem threePointStateAnticommutator12_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω (a - b) c d m n k =
      threePointStateAnticommutator12 (R := R) ω a c d m n k -
        threePointStateAnticommutator12 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsub] using
    (threePointAnticommutator12_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is subtraction-linear in the middle slot. -/
theorem threePointStateAnticommutator12_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a (b - c) d m n k =
      threePointStateAnticommutator12 (R := R) ω a b d m n k -
        threePointStateAnticommutator12 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsub] using
    (threePointAnticommutator12_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,2)` anticommutator is subtraction-linear in the third slot. -/
theorem threePointStateAnticommutator12_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b (c - d) m n k =
      threePointStateAnticommutator12 (R := R) ω a b c m n k -
        threePointStateAnticommutator12 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator12
  simpa [hYsub] using
    (threePointAnticommutator12_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- Three-point commutator (first two insertions) expressed by `nthProduct` difference. -/
theorem threePointCommutator12_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((c k) (((nthProduct R V b a n - nthProduct R V a b m) (m + n))
          (VertexAlgebra.vacuum (R := R)))) := by
  have hvec :=
    mode_commutator_eq_nthProduct_sub_apply (R := R) (V := V)
      b a n m (VertexAlgebra.vacuum (R := R))
  calc
    threePointCommutator12 (R := R) ω a b c m n k =
        ω.epsilon
          ((c k) (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) -
            (a m) ((b n) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointCommutator12_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          ((c k) (((nthProduct R V b a n - nthProduct R V a b m) (m + n))
            (VertexAlgebra.vacuum (R := R)))) := by
          simpa [add_comm] using congrArg (fun v => ω.epsilon ((c k) v)) hvec

/-- Three-point anticommutator (first two insertions) expressed by `nthProduct` sum. -/
theorem threePointAnticommutator12_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((c k) (((nthProduct R V b a n + nthProduct R V a b m) (m + n))
          (VertexAlgebra.vacuum (R := R)))) := by
  have hvec :=
    mode_anticommutator_eq_nthProduct_add_apply (R := R) (V := V)
      b a n m (VertexAlgebra.vacuum (R := R))
  calc
    threePointAnticommutator12 (R := R) ω a b c m n k =
        ω.epsilon
          ((c k) (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) +
            (a m) ((b n) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointAnticommutator12_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          ((c k) (((nthProduct R V b a n + nthProduct R V a b m) (m + n))
            (VertexAlgebra.vacuum (R := R)))) := by
          simpa [add_comm] using congrArg (fun v => ω.epsilon ((c k) v)) hvec

/-- State-level `(1,2)` commutator via `nthProduct` difference. -/
theorem threePointStateCommutator12_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n -
              nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m) (m + n))
            (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_nthProduct_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,2)` anticommutator via `nthProduct` sum. -/
theorem threePointStateAnticommutator12_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c m n k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n +
              nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m) (m + n))
            (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_nthProduct_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- Three-point commutator (first two insertions), with finite-order OPE data in both
    orientations, expressed through `coefficientOrZero` fields. -/
theorem threePointCommutator12_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
      ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
      ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))
  have hcomp1 :
      (b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := a) Fba n (m : ℤ) (VertexAlgebra.vacuum (R := R))
  have hcomp2 :
      (a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := a) (b := b) Fab m (n : ℤ) (VertexAlgebra.vacuum (R := R))
  have h1 :
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon ((c k) t1) := by
    calc
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t1) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp1
  have h2 :
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
        ω.epsilon ((c k) t2) := by
    calc
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
          ω.epsilon ((c k) ((a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t2) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp2
  calc
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k -
          threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k := by
          rfl
    _ = ω.epsilon ((c k) t1) - ω.epsilon ((c k) t2) := by rw [h1, h2]
    _ = ω.epsilon (((c k) t1) - ((c k) t2)) := by rw [map_sub]
    _ = ω.epsilon ((c k) (t1 - t2)) := by simp [map_sub]
    _ = ω.epsilon
        ((c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
          simp [t1, t2]

/-- Three-point anticommutator (first two insertions), with finite-order OPE data in both
    orientations, expressed through `coefficientOrZero` fields. -/
theorem threePointAnticommutator12_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
      ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
      ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))
  have hcomp1 :
      (b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := a) Fba n (m : ℤ) (VertexAlgebra.vacuum (R := R))
  have hcomp2 :
      (a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := a) (b := b) Fab m (n : ℤ) (VertexAlgebra.vacuum (R := R))
  have h1 :
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon ((c k) t1) := by
    calc
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t1) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp1
  have h2 :
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
        ω.epsilon ((c k) t2) := by
    calc
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
          ω.epsilon ((c k) ((a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t2) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp2
  calc
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k +
          threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k := by
          rfl
    _ = ω.epsilon ((c k) t1) + ω.epsilon ((c k) t2) := by rw [h1, h2]
    _ = ω.epsilon (((c k) t1) + ((c k) t2)) := by rw [map_add]
    _ = ω.epsilon ((c k) (t1 + t2)) := by simp [map_add]
    _ = ω.epsilon
        ((c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
          simp [t1, t2]

/-- If both natural mode indices are above OPE orders in both orientations, the
    three-point commutator (first two insertions) vanishes. -/
theorem threePointCommutator12_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
  have hzero1 :
      (b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := a) Fba hn (m : ℤ) (VertexAlgebra.vacuum (R := R))
  have hzero2 :
      (a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := a) (b := b) Fab hm (n : ℤ) (VertexAlgebra.vacuum (R := R))
  have h1 : threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
          ω.epsilon ((c k) ((a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointCommutator12
  rw [h1, h2]
  simp

/-- If both natural mode indices are above OPE orders in both orientations, the
    three-point anticommutator (first two insertions) vanishes. -/
theorem threePointAnticommutator12_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
  have hzero1 :
      (b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := a) Fba hn (m : ℤ) (VertexAlgebra.vacuum (R := R))
  have hzero2 :
      (a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := a) (b := b) Fab hm (n : ℤ) (VertexAlgebra.vacuum (R := R))
  have h1 : threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω a b c (m : ℤ) (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a (m : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω b a c (n : ℤ) (m : ℤ) k =
          ω.epsilon ((c k) ((a (m : ℤ)) ((b (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointAnticommutator12
  rw [h1, h2]
  simp

/-- If both mode indices are strictly below OPE orders in both orientations, the
    three-point commutator (first two insertions) is the difference of OPE
    coefficient correlators. -/
theorem threePointCommutator12_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k)
          ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := a) (b := b) Fab hm]
  calc
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator12_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = ω.epsilon
          ((c k)
            ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
              (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- If both mode indices are strictly below OPE orders in both orientations, the
    three-point anticommutator (first two insertions) is the sum of OPE
    coefficient correlators. -/
theorem threePointAnticommutator12_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k)
          ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := a) (b := b) Fab hm]
  calc
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator12_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = ω.epsilon
          ((c k)
            ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
              (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- Mixed regime: the first index is at/above OPE order for `(a,b)` while the
    second index is below OPE order for `(b,a)`. The three-point commutator
    reduces to the right-oriented coefficient term. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := a) (b := b) Fab hm]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  calc
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator12_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = ω.epsilon
          ((c k) (Fba.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: the first index is at/above OPE order for `(a,b)` while the
    second index is below OPE order for `(b,a)`. The three-point anticommutator
    reduces to the right-oriented coefficient term. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := a) (b := b) Fab hm]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  calc
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator12_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = ω.epsilon
          ((c k) (Fba.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: the first index is below OPE order for `(a,b)` while the second
    index is at/above OPE order for `(b,a)`. The three-point commutator is minus
    the left-oriented coefficient term. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      -ω.epsilon
        ((c k) (Fab.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := a) Fba hn]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := a) (b := b) Fab hm]
  calc
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator12_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = -ω.epsilon
          ((c k) (Fab.data.coefficients ⟨m, hm⟩
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: the first index is below OPE order for `(a,b)` while the second
    index is at/above OPE order for `(b,a)`. The three-point anticommutator
    reduces to the left-oriented coefficient term. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fab.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := a) Fba hn]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
        ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) =
        Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := a) (b := b) Fab hm]
  calc
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
        ω.epsilon
          ((c k)
            (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
                ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator12_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba m n k
    _ = ω.epsilon
          ((c k) (Fab.data.coefficients ⟨m, hm⟩
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- State-level `12` commutator with coefficient-or-zero extraction. -/
theorem threePointStateCommutator12_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_coefficientOrZero_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba m n k)

/-- State-level `12` anticommutator with coefficient-or-zero extraction. -/
theorem threePointStateAnticommutator12_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_coefficientOrZero_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba m n k)

/-- State-level `12` commutator vanishing in the above-order regime. -/
theorem threePointStateCommutator12_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` anticommutator vanishing in the above-order regime. -/
theorem threePointStateAnticommutator12_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k = 0 := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` commutator extraction in the strict-below regime. -/
theorem threePointStateCommutator12_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_opeCoefficient_sub_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` anticommutator extraction in the strict-below regime. -/
theorem threePointStateAnticommutator12_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          ((Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_opeCoefficient_add_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` commutator in mixed regime `(ge left, lt right)`. -/
theorem threePointStateCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` anticommutator in mixed regime `(ge left, lt right)`. -/
theorem threePointStateAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` commutator in mixed regime `(lt left, ge right)`. -/
theorem threePointStateCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      -ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fab.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator12] using
    (threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- State-level `12` anticommutator in mixed regime `(lt left, ge right)`. -/
theorem threePointStateAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fab.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator12] using
    (threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fab Fba hm hn k)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba hmLeft hnRight k)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba hmLeft hnRight k)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) (k : ℤ) :
    threePointCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      -ω.epsilon
        ((c k) (Fab.data.coefficients ⟨m, hmLeft⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba hmLeft hnRight k)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) (k : ℤ) :
    threePointAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((c k) (Fab.data.coefficients ⟨m, hmLeft⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fab Fba hmLeft hnRight k)

/-- State-level alias with explicit orientation naming for mixed regime `(ge ab, lt ba)`. -/
theorem threePointStateCommutator12_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b c Fab Fba hmLeft hnRight k)

/-- State-level alias with explicit orientation naming for mixed regime `(ge ab, lt ba)`. -/
theorem threePointStateAnticommutator12_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b c Fab Fba hmLeft hnRight k)

/-- State-level alias with explicit orientation naming for mixed regime `(lt ab, ge ba)`. -/
theorem threePointStateCommutator12_eq_neg_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateCommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      -ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fab.data.coefficients ⟨m, hmLeft⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b c Fab Fba hmLeft hnRight k)

/-- State-level alias with explicit orientation naming for mixed regime `(lt ab, ge ba)`. -/
theorem threePointStateAnticommutator12_eq_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) (k : ℤ) :
    threePointStateAnticommutator12 (R := R) ω a b c (m : ℤ) (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fab.data.coefficients ⟨m, hmLeft⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b c Fab Fba hmLeft hnRight k)


end StringAlgebra.VOA
