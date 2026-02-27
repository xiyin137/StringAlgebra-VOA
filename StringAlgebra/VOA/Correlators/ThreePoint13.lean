/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Correlators.Basics

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-- Three-point commutator in the first and third insertions:
    `⟨c(k)b(n)a(m) - a(m)b(n)c(k)⟩`. -/
def threePointCommutator13
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k - threePointModes (R := R) ω c b a k n m

/-- Three-point anticommutator in the first and third insertions:
    `⟨c(k)b(n)a(m) + a(m)b(n)c(k)⟩`. -/
def threePointAnticommutator13
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k + threePointModes (R := R) ω c b a k n m

/-- Three-point commutator in the first and third insertions, with state inputs. -/
def threePointStateCommutator13
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointCommutator13 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

/-- Three-point anticommutator in the first and third insertions, with state inputs. -/
def threePointStateAnticommutator13
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointAnticommutator13 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointCommutator13_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) -
          (a m) ((b n) ((c k) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointCommutator13, threePointModes_eq, map_sub]

@[simp] theorem threePointAnticommutator13_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) +
          (a m) ((b n) ((c k) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointAnticommutator13, threePointModes_eq, map_add]

@[simp] theorem threePointStateCommutator13_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k -
        threePointStateModes (R := R) ω c b a k n m := by
  rfl

@[simp] theorem threePointStateAnticommutator13_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k +
        threePointStateModes (R := R) ω c b a k n m := by
  rfl

@[simp] theorem threePointStateCommutator13_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) -
          (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) c k) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateCommutator13
  exact threePointCommutator13_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointStateAnticommutator13_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) +
          (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) c k) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateAnticommutator13
  exact threePointAnticommutator13_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

/-- `(1,3)` commutator is additive in the first field slot. -/
theorem threePointCommutator13_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω (a + b) c d m n k =
      threePointCommutator13 (R := R) ω a c d m n k +
        threePointCommutator13 (R := R) ω b c d m n k := by
  unfold threePointCommutator13
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) d c a b k n m]
  abel_nf

/-- `(1,3)` commutator is additive in the middle field slot. -/
theorem threePointCommutator13_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a (b + c) d m n k =
      threePointCommutator13 (R := R) ω a b d m n k +
        threePointCommutator13 (R := R) ω a c d m n k := by
  unfold threePointCommutator13
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) d b c a k n m]
  abel_nf

/-- `(1,3)` commutator is additive in the third field slot. -/
theorem threePointCommutator13_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b (c + d) m n k =
      threePointCommutator13 (R := R) ω a b c m n k +
        threePointCommutator13 (R := R) ω a b d m n k := by
  unfold threePointCommutator13
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) c d b a k n m]
  abel_nf

/-- `(1,3)` commutator is linear under scalar multiplication in the first slot. -/
theorem threePointCommutator13_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω (r • a) b c m n k =
      r • threePointCommutator13 (R := R) ω a b c m n k := by
  unfold threePointCommutator13
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r c b a k n m]
  simp [mul_sub]

/-- `(1,3)` commutator is linear under scalar multiplication in the middle slot. -/
theorem threePointCommutator13_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a (r • b) c m n k =
      r • threePointCommutator13 (R := R) ω a b c m n k := by
  unfold threePointCommutator13
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r c b a k n m]
  simp [mul_sub]

/-- `(1,3)` commutator is linear under scalar multiplication in the third slot. -/
theorem threePointCommutator13_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b (r • c) m n k =
      r • threePointCommutator13 (R := R) ω a b c m n k := by
  unfold threePointCommutator13
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r c b a k n m]
  simp [mul_sub]

/-- `(1,3)` anticommutator is additive in the first field slot. -/
theorem threePointAnticommutator13_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω (a + b) c d m n k =
      threePointAnticommutator13 (R := R) ω a c d m n k +
        threePointAnticommutator13 (R := R) ω b c d m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) d c a b k n m]
  abel_nf

/-- `(1,3)` anticommutator is additive in the middle field slot. -/
theorem threePointAnticommutator13_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a (b + c) d m n k =
      threePointAnticommutator13 (R := R) ω a b d m n k +
        threePointAnticommutator13 (R := R) ω a c d m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) d b c a k n m]
  abel_nf

/-- `(1,3)` anticommutator is additive in the third field slot. -/
theorem threePointAnticommutator13_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b (c + d) m n k =
      threePointAnticommutator13 (R := R) ω a b c m n k +
        threePointAnticommutator13 (R := R) ω a b d m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) c d b a k n m]
  abel_nf

/-- `(1,3)` anticommutator is linear under scalar multiplication in the first slot. -/
theorem threePointAnticommutator13_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω (r • a) b c m n k =
      r • threePointAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r c b a k n m]
  simp [mul_add]

/-- `(1,3)` anticommutator is linear under scalar multiplication in the middle slot. -/
theorem threePointAnticommutator13_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a (r • b) c m n k =
      r • threePointAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r c b a k n m]
  simp [mul_add]

/-- `(1,3)` anticommutator is linear under scalar multiplication in the third slot. -/
theorem threePointAnticommutator13_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b (r • c) m n k =
      r • threePointAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator13
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r c b a k n m]
  simp [mul_add]

/-- State-level `(1,3)` commutator is additive in the first field slot. -/
theorem threePointStateCommutator13_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω (a + b) c d m n k =
      threePointStateCommutator13 (R := R) ω a c d m n k +
        threePointStateCommutator13 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator13
  simpa [hYadd] using
    (threePointCommutator13_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` commutator is additive in the middle field slot. -/
theorem threePointStateCommutator13_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a (b + c) d m n k =
      threePointStateCommutator13 (R := R) ω a b d m n k +
        threePointStateCommutator13 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator13
  simpa [hYadd] using
    (threePointCommutator13_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` commutator is additive in the third field slot. -/
theorem threePointStateCommutator13_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b (c + d) m n k =
      threePointStateCommutator13 (R := R) ω a b c m n k +
        threePointStateCommutator13 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator13
  simpa [hYadd] using
    (threePointCommutator13_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` commutator is linear under scalar multiplication in the
    first slot. -/
theorem threePointStateCommutator13_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω (r • a) b c m n k =
      r • threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYsmul] using
    (threePointCommutator13_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` commutator is linear under scalar multiplication in the
    middle slot. -/
theorem threePointStateCommutator13_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a (r • b) c m n k =
      r • threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYsmul] using
    (threePointCommutator13_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` commutator is linear under scalar multiplication in the
    third slot. -/
theorem threePointStateCommutator13_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b (r • c) m n k =
      r • threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYsmul] using
    (threePointCommutator13_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is additive in the first field slot. -/
theorem threePointStateAnticommutator13_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω (a + b) c d m n k =
      threePointStateAnticommutator13 (R := R) ω a c d m n k +
        threePointStateAnticommutator13 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYadd] using
    (threePointAnticommutator13_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is additive in the middle field slot. -/
theorem threePointStateAnticommutator13_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a (b + c) d m n k =
      threePointStateAnticommutator13 (R := R) ω a b d m n k +
        threePointStateAnticommutator13 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYadd] using
    (threePointAnticommutator13_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is additive in the third field slot. -/
theorem threePointStateAnticommutator13_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b (c + d) m n k =
      threePointStateAnticommutator13 (R := R) ω a b c m n k +
        threePointStateAnticommutator13 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYadd] using
    (threePointAnticommutator13_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is linear under scalar multiplication in
    the first slot. -/
theorem threePointStateAnticommutator13_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω (r • a) b c m n k =
      r • threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsmul] using
    (threePointAnticommutator13_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is linear under scalar multiplication in
    the middle slot. -/
theorem threePointStateAnticommutator13_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a (r • b) c m n k =
      r • threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsmul] using
    (threePointAnticommutator13_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is linear under scalar multiplication in
    the third slot. -/
theorem threePointStateAnticommutator13_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b (r • c) m n k =
      r • threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsmul] using
    (threePointAnticommutator13_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- `(1,3)` commutator is negation-linear in the first field slot. -/
theorem threePointCommutator13_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω (-a) b c m n k =
      -threePointCommutator13 (R := R) ω a b c m n k := by
  simpa using threePointCommutator13_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` commutator is negation-linear in the middle field slot. -/
theorem threePointCommutator13_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a (-b) c m n k =
      -threePointCommutator13 (R := R) ω a b c m n k := by
  simpa using threePointCommutator13_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` commutator is negation-linear in the third field slot. -/
theorem threePointCommutator13_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b (-c) m n k =
      -threePointCommutator13 (R := R) ω a b c m n k := by
  simpa using threePointCommutator13_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` commutator is subtraction-linear in the first field slot. -/
theorem threePointCommutator13_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω (a - b) c d m n k =
      threePointCommutator13 (R := R) ω a c d m n k -
        threePointCommutator13 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator13_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointCommutator13_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,3)` commutator is subtraction-linear in the middle field slot. -/
theorem threePointCommutator13_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a (b - c) d m n k =
      threePointCommutator13 (R := R) ω a b d m n k -
        threePointCommutator13 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator13_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointCommutator13_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,3)` commutator is subtraction-linear in the third field slot. -/
theorem threePointCommutator13_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b (c - d) m n k =
      threePointCommutator13 (R := R) ω a b c m n k -
        threePointCommutator13 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator13_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointCommutator13_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- `(1,3)` anticommutator is negation-linear in the first field slot. -/
theorem threePointAnticommutator13_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω (-a) b c m n k =
      -threePointAnticommutator13 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator13_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` anticommutator is negation-linear in the middle field slot. -/
theorem threePointAnticommutator13_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a (-b) c m n k =
      -threePointAnticommutator13 (R := R) ω a b c m n k := by
  simpa using
    threePointAnticommutator13_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` anticommutator is negation-linear in the third field slot. -/
theorem threePointAnticommutator13_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b (-c) m n k =
      -threePointAnticommutator13 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator13_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(1,3)` anticommutator is subtraction-linear in the first field slot. -/
theorem threePointAnticommutator13_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω (a - b) c d m n k =
      threePointAnticommutator13 (R := R) ω a c d m n k -
        threePointAnticommutator13 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator13_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointAnticommutator13_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,3)` anticommutator is subtraction-linear in the middle field slot. -/
theorem threePointAnticommutator13_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a (b - c) d m n k =
      threePointAnticommutator13 (R := R) ω a b d m n k -
        threePointAnticommutator13 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator13_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointAnticommutator13_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(1,3)` anticommutator is subtraction-linear in the third field slot. -/
theorem threePointAnticommutator13_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b (c - d) m n k =
      threePointAnticommutator13 (R := R) ω a b c m n k -
        threePointAnticommutator13 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator13_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointAnticommutator13_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- State-level `(1,3)` commutator is negation-linear in the first slot. -/
theorem threePointStateCommutator13_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω (-a) b c m n k =
      -threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYneg] using
    (threePointCommutator13_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` commutator is negation-linear in the middle slot. -/
theorem threePointStateCommutator13_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a (-b) c m n k =
      -threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYneg] using
    (threePointCommutator13_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` commutator is negation-linear in the third slot. -/
theorem threePointStateCommutator13_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b (-c) m n k =
      -threePointStateCommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator13
  simpa [hYneg] using
    (threePointCommutator13_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` commutator is subtraction-linear in the first slot. -/
theorem threePointStateCommutator13_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω (a - b) c d m n k =
      threePointStateCommutator13 (R := R) ω a c d m n k -
        threePointStateCommutator13 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator13
  simpa [hYsub] using
    (threePointCommutator13_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` commutator is subtraction-linear in the middle slot. -/
theorem threePointStateCommutator13_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a (b - c) d m n k =
      threePointStateCommutator13 (R := R) ω a b d m n k -
        threePointStateCommutator13 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator13
  simpa [hYsub] using
    (threePointCommutator13_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` commutator is subtraction-linear in the third slot. -/
theorem threePointStateCommutator13_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b (c - d) m n k =
      threePointStateCommutator13 (R := R) ω a b c m n k -
        threePointStateCommutator13 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator13
  simpa [hYsub] using
    (threePointCommutator13_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is negation-linear in the first slot. -/
theorem threePointStateAnticommutator13_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω (-a) b c m n k =
      -threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYneg] using
    (threePointAnticommutator13_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is negation-linear in the middle slot. -/
theorem threePointStateAnticommutator13_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a (-b) c m n k =
      -threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYneg] using
    (threePointAnticommutator13_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is negation-linear in the third slot. -/
theorem threePointStateAnticommutator13_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b (-c) m n k =
      -threePointStateAnticommutator13 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYneg] using
    (threePointAnticommutator13_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(1,3)` anticommutator is subtraction-linear in the first slot. -/
theorem threePointStateAnticommutator13_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω (a - b) c d m n k =
      threePointStateAnticommutator13 (R := R) ω a c d m n k -
        threePointStateAnticommutator13 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsub] using
    (threePointAnticommutator13_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is subtraction-linear in the middle slot. -/
theorem threePointStateAnticommutator13_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a (b - c) d m n k =
      threePointStateAnticommutator13 (R := R) ω a b d m n k -
        threePointStateAnticommutator13 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsub] using
    (threePointAnticommutator13_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(1,3)` anticommutator is subtraction-linear in the third slot. -/
theorem threePointStateAnticommutator13_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b (c - d) m n k =
      threePointStateAnticommutator13 (R := R) ω a b c m n k -
        threePointStateAnticommutator13 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator13
  simpa [hYsub] using
    (threePointAnticommutator13_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- Three-point commutator (first and third insertions) expressed by
    `nthProduct` difference in the middle insertion. -/
theorem threePointCommutator13_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) (((nthProduct R V b a n) (n + m)) (VertexAlgebra.vacuum (R := R))) -
          (a m) (((nthProduct R V b c n) (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
  calc
    threePointCommutator13 (R := R) ω a b c m n k =
        ω.epsilon
          (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) -
            (a m) ((b n) ((c k) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointCommutator13_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          (((c k) (((nthProduct R V b a n) (n + m)) (VertexAlgebra.vacuum (R := R))) -
            (a m) (((nthProduct R V b c n) (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
          simp [nthProduct]

/-- Three-point anticommutator (first and third insertions) expressed by
    `nthProduct` sum in the middle insertion. -/
theorem threePointAnticommutator13_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) (((nthProduct R V b a n) (n + m)) (VertexAlgebra.vacuum (R := R))) +
          (a m) (((nthProduct R V b c n) (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
  calc
    threePointAnticommutator13 (R := R) ω a b c m n k =
        ω.epsilon
          (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) +
            (a m) ((b n) ((c k) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointAnticommutator13_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          (((c k) (((nthProduct R V b a n) (n + m)) (VertexAlgebra.vacuum (R := R))) +
            (a m) (((nthProduct R V b c n) (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
          simp [nthProduct]

/-- State-level `(1,3)` commutator via middle-insertion `nthProduct` difference. -/
theorem threePointStateCommutator13_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n)
              (n + m)) (VertexAlgebra.vacuum (R := R))) -
          (VertexAlgebra.Y (R := R) a m)
            (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) n)
              (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold threePointStateCommutator13
  exact threePointCommutator13_eq_nthProduct_sub (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

/-- State-level `(1,3)` anticommutator via middle-insertion `nthProduct` sum. -/
theorem threePointStateAnticommutator13_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n)
              (n + m)) (VertexAlgebra.vacuum (R := R))) +
          (VertexAlgebra.Y (R := R) a m)
            (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) n)
              (n + k)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold threePointStateAnticommutator13
  exact threePointAnticommutator13_eq_nthProduct_add (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

/-- Three-point commutator (first and third insertions), with finite-order OPE data
    for `(b,a)` and `(b,c)`, expressed through `coefficientOrZero` fields. -/
theorem threePointCommutator13_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
      ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
      ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))
  have hcomp1 :
      (b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := a) Fba n m (VertexAlgebra.vacuum (R := R))
  have hcomp2 :
      (b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := c) Fbc n k (VertexAlgebra.vacuum (R := R))
  have h1 :
      threePointModes (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon ((c k) t1) := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t1) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp1
  have h2 :
      threePointModes (R := R) ω c b a k (n : ℤ) m =
        ω.epsilon ((a m) t2) := by
    calc
      threePointModes (R := R) ω c b a k (n : ℤ) m =
          ω.epsilon ((a m) ((b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((a m) t2) := by
            simpa using congrArg (fun v => ω.epsilon ((a m) v)) hcomp2
  calc
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
        threePointModes (R := R) ω a b c m (n : ℤ) k -
          threePointModes (R := R) ω c b a k (n : ℤ) m := by
          rfl
    _ = ω.epsilon ((c k) t1) - ω.epsilon ((a m) t2) := by rw [h1, h2]
    _ = ω.epsilon (((c k) t1) - ((a m) t2)) := by rw [map_sub]
    _ = ω.epsilon
        (((c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
          simp [t1, t2]

/-- Three-point anticommutator (first and third insertions), with finite-order OPE
    data for `(b,a)` and `(b,c)`, expressed through `coefficientOrZero` fields. -/
theorem threePointAnticommutator13_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
      ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
      ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))
  have hcomp1 :
      (b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := a) Fba n m (VertexAlgebra.vacuum (R := R))
  have hcomp2 :
      (b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := c) Fbc n k (VertexAlgebra.vacuum (R := R))
  have h1 :
      threePointModes (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon ((c k) t1) := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((c k) t1) := by
            simpa using congrArg (fun v => ω.epsilon ((c k) v)) hcomp1
  have h2 :
      threePointModes (R := R) ω c b a k (n : ℤ) m =
        ω.epsilon ((a m) t2) := by
    calc
      threePointModes (R := R) ω c b a k (n : ℤ) m =
          ω.epsilon ((a m) ((b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon ((a m) t2) := by
            simpa using congrArg (fun v => ω.epsilon ((a m) v)) hcomp2
  calc
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
        threePointModes (R := R) ω a b c m (n : ℤ) k +
          threePointModes (R := R) ω c b a k (n : ℤ) m := by
          rfl
    _ = ω.epsilon ((c k) t1) + ω.epsilon ((a m) t2) := by rw [h1, h2]
    _ = ω.epsilon (((c k) t1) + ((a m) t2)) := by rw [map_add]
    _ = ω.epsilon
        (((c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
          simp [t1, t2]

/-- If the middle mode index is above OPE orders for both `(b,a)` and `(b,c)`,
    the three-point commutator (first and third insertions) vanishes. -/
theorem threePointCommutator13_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : Fbc.data.order ≤ n) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k = 0 := by
  have hzero1 :
      (b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := a) Fba hn1 m (VertexAlgebra.vacuum (R := R))
  have hzero2 :
      (b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := c) Fbc hn2 k (VertexAlgebra.vacuum (R := R))
  have h1 : threePointModes (R := R) ω a b c m (n : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω c b a k (n : ℤ) m = 0 := by
    calc
      threePointModes (R := R) ω c b a k (n : ℤ) m =
          ω.epsilon ((a m) ((b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointCommutator13
  rw [h1, h2]
  simp

/-- If the middle mode index is above OPE orders for both `(b,a)` and `(b,c)`,
    the three-point anticommutator (first and third insertions) vanishes. -/
theorem threePointAnticommutator13_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : Fbc.data.order ≤ n) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k = 0 := by
  have hzero1 :
      (b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := a) Fba hn1 m (VertexAlgebra.vacuum (R := R))
  have hzero2 :
      (b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := c) Fbc hn2 k (VertexAlgebra.vacuum (R := R))
  have h1 : threePointModes (R := R) ω a b c m (n : ℤ) k = 0 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) k =
          ω.epsilon ((c k) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω c b a k (n : ℤ) m = 0 := by
    calc
      threePointModes (R := R) ω c b a k (n : ℤ) m =
          ω.epsilon ((a m) ((b (n : ℤ)) ((c k) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointAnticommutator13
  rw [h1, h2]
  simp

/-- If the middle mode index is strictly below OPE orders for both `(b,a)` and `(b,c)`,
    the three-point commutator (first and third insertions) is the difference of
    corresponding OPE coefficient correlators. -/
theorem threePointCommutator13_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : n < Fbc.data.order) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (a m)
            (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) =
        Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
  calc
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator13_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = ω.epsilon
          (((c k)
              (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
            (a m)
              (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- If the middle mode index is strictly below OPE orders for both `(b,a)` and `(b,c)`,
    the three-point anticommutator (first and third insertions) is the sum of
    corresponding OPE coefficient correlators. -/
theorem threePointAnticommutator13_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : n < Fbc.data.order) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (a m)
            (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) =
        Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
  calc
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator13_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = ω.epsilon
          (((c k)
              (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
            (a m)
              (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- Alias with explicit orientation naming for strict-below extraction:
    both `(b,a)` and `(b,c)` are below cutoff. -/
theorem threePointCommutator13_eq_opeCoefficient_sub_of_lt_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnBA : n < Fba.data.order) (hnBC : n < Fbc.data.order) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            (Fba.data.coefficients ⟨n, hnBA⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (a m)
            (Fbc.data.coefficients ⟨n, hnBC⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    (threePointCommutator13_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnBA hnBC)

/-- Alias with explicit orientation naming for strict-below extraction:
    both `(b,a)` and `(b,c)` are below cutoff. -/
theorem threePointAnticommutator13_eq_opeCoefficient_add_of_lt_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnBA : n < Fba.data.order) (hnBC : n < Fbc.data.order) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((c k)
            (Fba.data.coefficients ⟨n, hnBA⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (a m)
            (Fbc.data.coefficients ⟨n, hnBC⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    (threePointAnticommutator13_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnBA hnBC)

/-- Mixed regime: `n` is at/above OPE order for `(b,a)` but below OPE order for `(b,c)`.
    The three-point commutator (first and third insertions) is minus the
    `(b,c)` coefficient term. -/
theorem threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : n < Fbc.data.order) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      -ω.epsilon
        ((a m) (Fbc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) =
        Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
  calc
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator13_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = -ω.epsilon
          ((a m) (Fbc.data.coefficients ⟨n, hn2⟩
            ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is at/above OPE order for `(b,a)` but below OPE order for `(b,c)`.
    The three-point anticommutator (first and third insertions) is the `(b,c)`
    coefficient term. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : n < Fbc.data.order) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((a m) (Fbc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) =
        Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
  calc
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator13_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = ω.epsilon
          ((a m) (Fbc.data.coefficients ⟨n, hn2⟩
            ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is below OPE order for `(b,a)` but at/above OPE order for `(b,c)`.
    The three-point commutator (first and third insertions) is the `(b,a)`
    coefficient term. -/
theorem threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : Fbc.data.order ≤ n) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  calc
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointCommutator13_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = ω.epsilon
          ((c k) (Fba.data.coefficients ⟨n, hn1⟩
            ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is below OPE order for `(b,a)` but at/above OPE order for `(b,c)`.
    The three-point anticommutator (first and third insertions) is the `(b,a)`
    coefficient term. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : Fbc.data.order ≤ n) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
        ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) =
        Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := a) Fba hn1]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := c) Fbc hn2]
    change ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
    simp
  calc
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
        ω.epsilon
          (((c k)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
                ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
            (a m)
              ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
                ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) :=
      threePointAnticommutator13_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m n k
    _ = ω.epsilon
          ((c k) (Fba.data.coefficients ⟨n, hn1⟩
            ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- State-level `(1,3)` commutator with coefficient-or-zero extraction. -/
theorem threePointStateCommutator13_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m : ℤ) (n : ℕ) (k : ℤ) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (VertexAlgebra.Y (R := R) a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator13] using
    (threePointCommutator13_eq_coefficientOrZero_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m n k)

/-- State-level `(1,3)` anticommutator with coefficient-or-zero extraction. -/
theorem threePointStateAnticommutator13_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m : ℤ) (n : ℕ) (k : ℤ) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (VertexAlgebra.Y (R := R) a m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
                (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) c) Fbc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator13] using
    (threePointAnticommutator13_eq_coefficientOrZero_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m n k)

/-- State-level `(1,3)` commutator vanishing in the above-order regime. -/
theorem threePointStateCommutator13_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : Fbc.data.order ≤ n) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k = 0 := by
  simpa [threePointStateCommutator13] using
    (threePointCommutator13_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` anticommutator vanishing in the above-order regime. -/
theorem threePointStateAnticommutator13_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : Fbc.data.order ≤ n) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k = 0 := by
  simpa [threePointStateAnticommutator13] using
    (threePointAnticommutator13_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` commutator extraction in the strict-below regime. -/
theorem threePointStateCommutator13_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : n < Fbc.data.order) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (VertexAlgebra.Y (R := R) a m)
            (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator13] using
    (threePointCommutator13_eq_opeCoefficient_sub_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` anticommutator extraction in the strict-below regime. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : n < Fbc.data.order) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (Fba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (VertexAlgebra.Y (R := R) a m)
            (Fbc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator13] using
    (threePointAnticommutator13_eq_opeCoefficient_add_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level alias with explicit orientation naming for strict-below extraction:
    both `(b,a)` and `(b,c)` are below cutoff. -/
theorem threePointStateCommutator13_eq_opeCoefficient_sub_of_lt_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnBA : n < Fba.data.order) (hnBC : n < Fbc.data.order) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (Fba.data.coefficients ⟨n, hnBA⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (VertexAlgebra.Y (R := R) a m)
            (Fbc.data.coefficients ⟨n, hnBC⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    (threePointStateCommutator13_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω) a b c Fba Fbc m k hnBA hnBC)

/-- State-level alias with explicit orientation naming for strict-below extraction:
    both `(b,a)` and `(b,c)` are below cutoff. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_add_of_lt_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnBA : n < Fba.data.order) (hnBC : n < Fbc.data.order) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k)
            (Fba.data.coefficients ⟨n, hnBA⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (VertexAlgebra.Y (R := R) a m)
            (Fbc.data.coefficients ⟨n, hnBC⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    (threePointStateAnticommutator13_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω) a b c Fba Fbc m k hnBA hnBC)

/-- State-level `(1,3)` commutator in mixed regime `(ge ba, lt bc)`. -/
theorem threePointStateCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : n < Fbc.data.order) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      -ω.epsilon
        ((VertexAlgebra.Y (R := R) a m) (Fbc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator13] using
    (threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` anticommutator in mixed regime `(ge ba, lt bc)`. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : Fba.data.order ≤ n) (hn2 : n < Fbc.data.order) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) a m) (Fbc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator13] using
    (threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` commutator in mixed regime `(lt ba, ge bc)`. -/
theorem threePointStateCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : Fbc.data.order ≤ n) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator13] using
    (threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- State-level `(1,3)` anticommutator in mixed regime `(lt ba, ge bc)`. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Fba.data.order) (hn2 : Fbc.data.order ≤ n) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator13] using
    (threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fba Fbc m k hn1 hn2)

/-- Alias with `left/right` naming:
    left orientation is `(b,a)`, right orientation is `(b,c)`. -/
theorem threePointCommutator13_eq_neg_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnLeft : Fba.data.order ≤ n) (hnRight : n < Fbc.data.order) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      -ω.epsilon
        ((a m) (Fbc.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnLeft hnRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,a)`, right orientation is `(b,c)`. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnLeft : Fba.data.order ≤ n) (hnRight : n < Fbc.data.order) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((a m) (Fbc.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnLeft hnRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,a)`, right orientation is `(b,c)`. -/
theorem threePointCommutator13_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnLeft : n < Fba.data.order) (hnRight : Fbc.data.order ≤ n) :
    threePointCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnLeft hnRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,a)`, right orientation is `(b,c)`. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (m k : ℤ) {n : ℕ}
    (hnLeft : n < Fba.data.order) (hnRight : Fbc.data.order ≤ n) :
    threePointAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((c k) (Fba.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fba Fbc m k hnLeft hnRight)

/-- State-level alias with `left/right` naming for mixed regime `(ge left, lt right)`. -/
theorem threePointStateCommutator13_eq_neg_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnLeft : Fba.data.order ≤ n) (hnRight : n < Fbc.data.order) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      -ω.epsilon
        ((VertexAlgebra.Y (R := R) a m) (Fbc.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω) a b c Fba Fbc m k hnLeft hnRight)

/-- State-level alias with `left/right` naming for mixed regime `(ge left, lt right)`. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnLeft : Fba.data.order ≤ n) (hnRight : n < Fbc.data.order) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) a m) (Fbc.data.coefficients ⟨n, hnRight⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω) a b c Fba Fbc m k hnLeft hnRight)

/-- State-level alias with `left/right` naming for mixed regime `(lt left, ge right)`. -/
theorem threePointStateCommutator13_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnLeft : n < Fba.data.order) (hnRight : Fbc.data.order ≤ n) :
    threePointStateCommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω) a b c Fba Fbc m k hnLeft hnRight)

/-- State-level alias with `left/right` naming for mixed regime `(lt left, ge right)`. -/
theorem threePointStateAnticommutator13_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (m k : ℤ) {n : ℕ}
    (hnLeft : n < Fba.data.order) (hnRight : Fbc.data.order ≤ n) :
    threePointStateAnticommutator13 (R := R) ω a b c m (n : ℤ) k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k) (Fba.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω) a b c Fba Fbc m k hnLeft hnRight)


end StringAlgebra.VOA
