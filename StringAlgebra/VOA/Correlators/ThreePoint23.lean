/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Correlators.Basics

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-- Three-point commutator in the last two insertions:
    `⟨c(k)b(n)a(m) - b(n)c(k)a(m)⟩`. -/
def threePointCommutator23
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k - threePointModes (R := R) ω a c b m k n

/-- Three-point anticommutator in the last two insertions:
    `⟨c(k)b(n)a(m) + b(n)c(k)a(m)⟩`. -/
def threePointAnticommutator23
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω a b c m n k + threePointModes (R := R) ω a c b m k n

/-- Three-point commutator in the last two insertions, with state inputs. -/
def threePointStateCommutator23
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointCommutator23 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

/-- Three-point anticommutator in the last two insertions, with state inputs. -/
def threePointStateAnticommutator23
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointAnticommutator23 (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointCommutator23_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) -
          (b n) ((c k) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointCommutator23, threePointModes_eq, map_sub]

@[simp] theorem threePointAnticommutator23_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) +
          (b n) ((c k) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
  simp [threePointAnticommutator23, threePointModes_eq, map_add]

@[simp] theorem threePointStateCommutator23_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k -
        threePointStateModes (R := R) ω a c b m k n := by
  rfl

@[simp] theorem threePointStateAnticommutator23_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b c m n k =
      threePointStateModes (R := R) ω a b c m n k +
        threePointStateModes (R := R) ω a c b m k n := by
  rfl

@[simp] theorem threePointStateCommutator23_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) -
          (VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateCommutator23
  exact threePointCommutator23_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem threePointStateAnticommutator23_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) +
          (VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) c k) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold threePointStateAnticommutator23
  exact threePointAnticommutator23_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
    (c := VertexAlgebra.Y (R := R) c) m n k

/-- `(2,3)` commutator is additive in the first field slot. -/
theorem threePointCommutator23_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω (a + b) c d m n k =
      threePointCommutator23 (R := R) ω a c d m n k +
        threePointCommutator23 (R := R) ω b c d m n k := by
  unfold threePointCommutator23
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) a b d c m k n]
  abel_nf

/-- `(2,3)` commutator is additive in the second field slot. -/
theorem threePointCommutator23_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a (b + c) d m n k =
      threePointCommutator23 (R := R) ω a b d m n k +
        threePointCommutator23 (R := R) ω a c d m n k := by
  unfold threePointCommutator23
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) a d b c m k n]
  abel_nf

/-- `(2,3)` commutator is additive in the third field slot. -/
theorem threePointCommutator23_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b (c + d) m n k =
      threePointCommutator23 (R := R) ω a b c m n k +
        threePointCommutator23 (R := R) ω a b d m n k := by
  unfold threePointCommutator23
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) a c d b m k n]
  abel_nf

/-- `(2,3)` commutator is linear under scalar multiplication in the first slot. -/
theorem threePointCommutator23_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω (r • a) b c m n k =
      r • threePointCommutator23 (R := R) ω a b c m n k := by
  unfold threePointCommutator23
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r a c b m k n]
  simp [mul_sub]

/-- `(2,3)` commutator is linear under scalar multiplication in the middle slot. -/
theorem threePointCommutator23_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a (r • b) c m n k =
      r • threePointCommutator23 (R := R) ω a b c m n k := by
  unfold threePointCommutator23
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r a c b m k n]
  simp [mul_sub]

/-- `(2,3)` commutator is linear under scalar multiplication in the third slot. -/
theorem threePointCommutator23_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b (r • c) m n k =
      r • threePointCommutator23 (R := R) ω a b c m n k := by
  unfold threePointCommutator23
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a c b m k n]
  simp [mul_sub]

/-- `(2,3)` anticommutator is additive in the first field slot. -/
theorem threePointAnticommutator23_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω (a + b) c d m n k =
      threePointAnticommutator23 (R := R) ω a c d m n k +
        threePointAnticommutator23 (R := R) ω b c d m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_add_left (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_left (R := R) (ω := ω) a b d c m k n]
  abel_nf

/-- `(2,3)` anticommutator is additive in the second field slot. -/
theorem threePointAnticommutator23_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a (b + c) d m n k =
      threePointAnticommutator23 (R := R) ω a b d m n k +
        threePointAnticommutator23 (R := R) ω a c d m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_add_middle (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_right (R := R) (ω := ω) a d b c m k n]
  abel_nf

/-- `(2,3)` anticommutator is additive in the third field slot. -/
theorem threePointAnticommutator23_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b (c + d) m n k =
      threePointAnticommutator23 (R := R) ω a b c m n k +
        threePointAnticommutator23 (R := R) ω a b d m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_add_right (R := R) (ω := ω) a b c d m n k]
  rw [threePointModes_add_middle (R := R) (ω := ω) a c d b m k n]
  abel_nf

/-- `(2,3)` anticommutator is linear under scalar multiplication in the first slot. -/
theorem threePointAnticommutator23_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω (r • a) b c m n k =
      r • threePointAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_smul_left (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_left (R := R) (ω := ω) r a c b m k n]
  simp [mul_add]

/-- `(2,3)` anticommutator is linear under scalar multiplication in the middle slot. -/
theorem threePointAnticommutator23_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a (r • b) c m n k =
      r • threePointAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_right (R := R) (ω := ω) r a c b m k n]
  simp [mul_add]

/-- `(2,3)` anticommutator is linear under scalar multiplication in the third slot. -/
theorem threePointAnticommutator23_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b (r • c) m n k =
      r • threePointAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointAnticommutator23
  rw [threePointModes_smul_right (R := R) (ω := ω) r a b c m n k]
  rw [threePointModes_smul_middle (R := R) (ω := ω) r a c b m k n]
  simp [mul_add]

/-- State-level `(2,3)` commutator is additive in the first field slot. -/
theorem threePointStateCommutator23_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω (a + b) c d m n k =
      threePointStateCommutator23 (R := R) ω a c d m n k +
        threePointStateCommutator23 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator23
  simpa [hYadd] using
    (threePointCommutator23_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` commutator is additive in the second field slot. -/
theorem threePointStateCommutator23_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a (b + c) d m n k =
      threePointStateCommutator23 (R := R) ω a b d m n k +
        threePointStateCommutator23 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator23
  simpa [hYadd] using
    (threePointCommutator23_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` commutator is additive in the third field slot. -/
theorem threePointStateCommutator23_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b (c + d) m n k =
      threePointStateCommutator23 (R := R) ω a b c m n k +
        threePointStateCommutator23 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator23
  simpa [hYadd] using
    (threePointCommutator23_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` commutator is linear under scalar multiplication in the
    first slot. -/
theorem threePointStateCommutator23_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω (r • a) b c m n k =
      r • threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYsmul] using
    (threePointCommutator23_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` commutator is linear under scalar multiplication in the
    middle slot. -/
theorem threePointStateCommutator23_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a (r • b) c m n k =
      r • threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYsmul] using
    (threePointCommutator23_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` commutator is linear under scalar multiplication in the
    third slot. -/
theorem threePointStateCommutator23_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b (r • c) m n k =
      r • threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYsmul] using
    (threePointCommutator23_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is additive in the first field slot. -/
theorem threePointStateAnticommutator23_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω (a + b) c d m n k =
      threePointStateAnticommutator23 (R := R) ω a c d m n k +
        threePointStateAnticommutator23 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYadd] using
    (threePointAnticommutator23_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is additive in the second field slot. -/
theorem threePointStateAnticommutator23_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a (b + c) d m n k =
      threePointStateAnticommutator23 (R := R) ω a b d m n k +
        threePointStateAnticommutator23 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYadd] using
    (threePointAnticommutator23_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is additive in the third field slot. -/
theorem threePointStateAnticommutator23_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b (c + d) m n k =
      threePointStateAnticommutator23 (R := R) ω a b c m n k +
        threePointStateAnticommutator23 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYadd] using
    (threePointAnticommutator23_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is linear under scalar multiplication in
    the first slot. -/
theorem threePointStateAnticommutator23_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω (r • a) b c m n k =
      r • threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsmul] using
    (threePointAnticommutator23_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is linear under scalar multiplication in
    the middle slot. -/
theorem threePointStateAnticommutator23_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a (r • b) c m n k =
      r • threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsmul] using
    (threePointAnticommutator23_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is linear under scalar multiplication in
    the third slot. -/
theorem threePointStateAnticommutator23_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b (r • c) m n k =
      r • threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsmul] using
    (threePointAnticommutator23_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- `(2,3)` commutator is negation-linear in the first field slot. -/
theorem threePointCommutator23_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω (-a) b c m n k =
      -threePointCommutator23 (R := R) ω a b c m n k := by
  simpa using threePointCommutator23_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` commutator is negation-linear in the middle field slot. -/
theorem threePointCommutator23_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a (-b) c m n k =
      -threePointCommutator23 (R := R) ω a b c m n k := by
  simpa using threePointCommutator23_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` commutator is negation-linear in the third field slot. -/
theorem threePointCommutator23_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b (-c) m n k =
      -threePointCommutator23 (R := R) ω a b c m n k := by
  simpa using threePointCommutator23_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` commutator is subtraction-linear in the first field slot. -/
theorem threePointCommutator23_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω (a - b) c d m n k =
      threePointCommutator23 (R := R) ω a c d m n k -
        threePointCommutator23 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator23_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointCommutator23_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(2,3)` commutator is subtraction-linear in the middle field slot. -/
theorem threePointCommutator23_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a (b - c) d m n k =
      threePointCommutator23 (R := R) ω a b d m n k -
        threePointCommutator23 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator23_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointCommutator23_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(2,3)` commutator is subtraction-linear in the third field slot. -/
theorem threePointCommutator23_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b (c - d) m n k =
      threePointCommutator23 (R := R) ω a b c m n k -
        threePointCommutator23 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointCommutator23_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointCommutator23_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- `(2,3)` anticommutator is negation-linear in the first field slot. -/
theorem threePointAnticommutator23_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω (-a) b c m n k =
      -threePointAnticommutator23 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator23_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` anticommutator is negation-linear in the middle field slot. -/
theorem threePointAnticommutator23_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a (-b) c m n k =
      -threePointAnticommutator23 (R := R) ω a b c m n k := by
  simpa using
    threePointAnticommutator23_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` anticommutator is negation-linear in the third field slot. -/
theorem threePointAnticommutator23_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b (-c) m n k =
      -threePointAnticommutator23 (R := R) ω a b c m n k := by
  simpa using threePointAnticommutator23_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- `(2,3)` anticommutator is subtraction-linear in the first field slot. -/
theorem threePointAnticommutator23_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω (a - b) c d m n k =
      threePointAnticommutator23 (R := R) ω a c d m n k -
        threePointAnticommutator23 (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator23_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointAnticommutator23_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- `(2,3)` anticommutator is subtraction-linear in the middle field slot. -/
theorem threePointAnticommutator23_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a (b - c) d m n k =
      threePointAnticommutator23 (R := R) ω a b d m n k -
        threePointAnticommutator23 (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator23_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointAnticommutator23_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- `(2,3)` anticommutator is subtraction-linear in the third field slot. -/
theorem threePointAnticommutator23_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b (c - d) m n k =
      threePointAnticommutator23 (R := R) ω a b c m n k -
        threePointAnticommutator23 (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointAnticommutator23_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointAnticommutator23_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

/-- State-level `(2,3)` commutator is negation-linear in the first slot. -/
theorem threePointStateCommutator23_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω (-a) b c m n k =
      -threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYneg] using
    (threePointCommutator23_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` commutator is negation-linear in the middle slot. -/
theorem threePointStateCommutator23_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a (-b) c m n k =
      -threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYneg] using
    (threePointCommutator23_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` commutator is negation-linear in the third slot. -/
theorem threePointStateCommutator23_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b (-c) m n k =
      -threePointStateCommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateCommutator23
  simpa [hYneg] using
    (threePointCommutator23_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` commutator is subtraction-linear in the first slot. -/
theorem threePointStateCommutator23_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω (a - b) c d m n k =
      threePointStateCommutator23 (R := R) ω a c d m n k -
        threePointStateCommutator23 (R := R) ω b c d m n k := by
  unfold threePointStateCommutator23
  simpa [hYsub] using
    (threePointCommutator23_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` commutator is subtraction-linear in the middle slot. -/
theorem threePointStateCommutator23_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a (b - c) d m n k =
      threePointStateCommutator23 (R := R) ω a b d m n k -
        threePointStateCommutator23 (R := R) ω a c d m n k := by
  unfold threePointStateCommutator23
  simpa [hYsub] using
    (threePointCommutator23_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` commutator is subtraction-linear in the third slot. -/
theorem threePointStateCommutator23_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b (c - d) m n k =
      threePointStateCommutator23 (R := R) ω a b c m n k -
        threePointStateCommutator23 (R := R) ω a b d m n k := by
  unfold threePointStateCommutator23
  simpa [hYsub] using
    (threePointCommutator23_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is negation-linear in the first slot. -/
theorem threePointStateAnticommutator23_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω (-a) b c m n k =
      -threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYneg] using
    (threePointAnticommutator23_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is negation-linear in the middle slot. -/
theorem threePointStateAnticommutator23_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a (-b) c m n k =
      -threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYneg] using
    (threePointAnticommutator23_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is negation-linear in the third slot. -/
theorem threePointStateAnticommutator23_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b (-c) m n k =
      -threePointStateAnticommutator23 (R := R) ω a b c m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYneg] using
    (threePointAnticommutator23_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator is subtraction-linear in the first slot. -/
theorem threePointStateAnticommutator23_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω (a - b) c d m n k =
      threePointStateAnticommutator23 (R := R) ω a c d m n k -
        threePointStateAnticommutator23 (R := R) ω b c d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsub] using
    (threePointAnticommutator23_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is subtraction-linear in the middle slot. -/
theorem threePointStateAnticommutator23_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a (b - c) d m n k =
      threePointStateAnticommutator23 (R := R) ω a b d m n k -
        threePointStateAnticommutator23 (R := R) ω a c d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsub] using
    (threePointAnticommutator23_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level `(2,3)` anticommutator is subtraction-linear in the third slot. -/
theorem threePointStateAnticommutator23_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b (c - d) m n k =
      threePointStateAnticommutator23 (R := R) ω a b c m n k -
        threePointStateAnticommutator23 (R := R) ω a b d m n k := by
  unfold threePointStateAnticommutator23
  simpa [hYsub] using
    (threePointAnticommutator23_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- Three-point commutator (last two insertions) expressed by `nthProduct` difference. -/
theorem threePointCommutator23_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointCommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        ((((nthProduct R V c b k - nthProduct R V b c n) (k + n))
          ((a m) (VertexAlgebra.vacuum (R := R))))) := by
  have hvec :=
    mode_commutator_eq_nthProduct_sub_apply (R := R) (V := V)
      c b k n ((a m) (VertexAlgebra.vacuum (R := R)))
  calc
    threePointCommutator23 (R := R) ω a b c m n k =
        ω.epsilon
          (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) -
            (b n) ((c k) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointCommutator23_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          ((((nthProduct R V c b k - nthProduct R V b c n) (k + n))
            ((a m) (VertexAlgebra.vacuum (R := R))))) := by
          simpa [add_comm] using congrArg ω.epsilon hvec

/-- Three-point anticommutator (last two insertions) expressed by `nthProduct` sum. -/
theorem threePointAnticommutator23_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointAnticommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        ((((nthProduct R V c b k + nthProduct R V b c n) (k + n))
          ((a m) (VertexAlgebra.vacuum (R := R))))) := by
  have hvec :=
    mode_anticommutator_eq_nthProduct_add_apply (R := R) (V := V)
      c b k n ((a m) (VertexAlgebra.vacuum (R := R)))
  calc
    threePointAnticommutator23 (R := R) ω a b c m n k =
        ω.epsilon
          (((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) +
            (b n) ((c k) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
          exact threePointAnticommutator23_eq (R := R) (ω := ω) a b c m n k
    _ = ω.epsilon
          ((((nthProduct R V c b k + nthProduct R V b c n) (k + n))
            ((a m) (VertexAlgebra.vacuum (R := R))))) := by
          simpa [add_comm] using congrArg ω.epsilon hvec

/-- State-level `(2,3)` commutator via `nthProduct` difference. -/
theorem threePointStateCommutator23_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateCommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        ((((nthProduct R V (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b) k -
            nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) n) (k + n))
          ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_nthProduct_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level `(2,3)` anticommutator via `nthProduct` sum. -/
theorem threePointStateAnticommutator23_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateAnticommutator23 (R := R) ω a b c m n k =
      ω.epsilon
        ((((nthProduct R V (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b) k +
            nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) n) (k + n))
          ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_nthProduct_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- Three-point commutator (last two insertions), with finite-order OPE data in both
    orientations, expressed through `coefficientOrZero` fields. -/
theorem threePointCommutator23_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) (n k : ℕ) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
      ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))
    )
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
      ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))
    )
  have hcomp1 :
      (c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := c) (b := b) Fcb k (n : ℤ)
          ((a m) (VertexAlgebra.vacuum (R := R)))
  have hcomp2 :
      (b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := c) Fbc n (k : ℤ)
          ((a m) (VertexAlgebra.vacuum (R := R))
        )
  have h1 :
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon t1 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
          ω.epsilon ((c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon t1 := by
            simpa using congrArg ω.epsilon hcomp1
  have h2 :
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
        ω.epsilon t2 := by
    calc
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
          ω.epsilon ((b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon t2 := by
            simpa using congrArg ω.epsilon hcomp2
  calc
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) -
          threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) := by
          rfl
    _ = ω.epsilon t1 - ω.epsilon t2 := by rw [h1, h2]
    _ = ω.epsilon (t1 - t2) := by rw [map_sub]
    _ = ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
          simp [t1, t2]

/-- Three-point anticommutator (last two insertions), with finite-order OPE data in
    both orientations, expressed through `coefficientOrZero` fields. -/
theorem threePointAnticommutator23_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) (n k : ℕ) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
  let t1 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
      ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))
    )
  let t2 : V :=
    (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
      ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))
    )
  have hcomp1 :
      (c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = t1 := by
    simpa [t1] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := c) (b := b) Fcb k (n : ℤ)
          ((a m) (VertexAlgebra.vacuum (R := R)))
  have hcomp2 :
      (b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = t2 := by
    simpa [t2] using
      OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
        (R := R) (V := V) (a := b) (b := c) Fbc n (k : ℤ)
          ((a m) (VertexAlgebra.vacuum (R := R))
        )
  have h1 :
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon t1 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
          ω.epsilon ((c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon t1 := by
            simpa using congrArg ω.epsilon hcomp1
  have h2 :
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
        ω.epsilon t2 := by
    calc
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
          ω.epsilon ((b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = ω.epsilon t2 := by
            simpa using congrArg ω.epsilon hcomp2
  calc
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) +
          threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) := by
          rfl
    _ = ω.epsilon t1 + ω.epsilon t2 := by rw [h1, h2]
    _ = ω.epsilon (t1 + t2) := by rw [map_add]
    _ = ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) := by
          simp [t1, t2]

/-- If both natural mode indices are above OPE orders in both orientations, the
    three-point commutator (last two insertions) vanishes. -/
theorem threePointCommutator23_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : Fcb.data.order ≤ k) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
  have hzero1 :
      (c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := c) (b := b) Fcb hk (n : ℤ)
        ((a m) (VertexAlgebra.vacuum (R := R)))
  have hzero2 :
      (b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := c) Fbc hn (k : ℤ)
        ((a m) (VertexAlgebra.vacuum (R := R)))
  have h1 : threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
          ω.epsilon ((c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) = 0 := by
    calc
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
          ω.epsilon ((b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointCommutator23
  rw [h1, h2]
  simp

/-- If both natural mode indices are above OPE orders in both orientations, the
    three-point anticommutator (last two insertions) vanishes. -/
theorem threePointAnticommutator23_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : Fcb.data.order ≤ k) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
  have hzero1 :
      (c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := c) (b := b) Fcb hk (n : ℤ)
        ((a m) (VertexAlgebra.vacuum (R := R)))
  have hzero2 :
      (b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0 :=
    OPEFiniteOrder.mode_comp_eq_zero_of_ge_apply
      (R := R) (V := V) (a := b) (b := c) Fbc hn (k : ℤ)
        ((a m) (VertexAlgebra.vacuum (R := R)))
  have h1 : threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
    calc
      threePointModes (R := R) ω a b c m (n : ℤ) (k : ℤ) =
          ω.epsilon ((c (k : ℤ)) ((b (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero1]
            simp
  have h2 : threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) = 0 := by
    calc
      threePointModes (R := R) ω a c b m (k : ℤ) (n : ℤ) =
          ω.epsilon ((b (n : ℤ)) ((c (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
            simp [threePointModes_eq]
      _ = 0 := by
            rw [hzero2]
            simp
  unfold threePointAnticommutator23
  rw [h1, h2]
  simp

/-- If both mode indices are strictly below OPE orders in both orientations, the
    three-point commutator (last two insertions) is the difference of OPE
    coefficient correlators. -/
theorem threePointCommutator23_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : k < Fcb.data.order) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
  calc
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointCommutator23_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- If both mode indices are strictly below OPE orders in both orientations, the
    three-point anticommutator (last two insertions) is the sum of OPE
    coefficient correlators. -/
theorem threePointAnticommutator23_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : k < Fcb.data.order) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
  calc
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointAnticommutator23_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
          rw [hleft, hright]

/-- Mixed regime: `n` is at/above OPE order for `(b,c)` and `k` is below OPE
    order for `(c,b)`. The three-point commutator (last two insertions)
    reduces to the `k`-oriented coefficient term. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : k < Fcb.data.order) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
    change ((0 : Module.End R V) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0
    simp
  calc
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointCommutator23_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is at/above OPE order for `(b,c)` and `k` is below OPE
    order for `(c,b)`. The three-point anticommutator (last two insertions)
    reduces to the `k`-oriented coefficient term. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : k < Fcb.data.order) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
    change ((0 : Module.End R V) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0
    simp
  calc
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointAnticommutator23_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is below OPE order for `(b,c)` and `k` is at/above OPE
    order for `(c,b)`. The three-point commutator (last two insertions) is minus
    the `n`-oriented coefficient term. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : Fcb.data.order ≤ k) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
    change ((0 : Module.End R V) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
  calc
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointCommutator23_eq_coefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = -ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: `n` is below OPE order for `(b,c)` and `k` is at/above OPE
    order for `(c,b)`. The three-point anticommutator (last two insertions)
    reduces to the `n`-oriented coefficient term. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : Fcb.data.order ≤ k) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  have hleft :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
        ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) = 0 := by
    rw [OPEFiniteOrder.coefficientOrZero_of_ge
      (R := R) (V := V) (a := c) (b := b) Fcb hk]
    change ((0 : Module.End R V) ((a m) (VertexAlgebra.vacuum (R := R)))) = 0
    simp
  have hright :
      (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
        ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) =
        Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) := by
    simp [OPEFiniteOrder.coefficientOrZero_of_lt
      (R := R) (V := V) (a := b) (b := c) Fbc hn]
  calc
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
        ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := c) (b := b) Fcb k)
              ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := c) Fbc n)
              ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))))) :=
      threePointAnticommutator23_eq_coefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m n k
    _ = ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
          rw [hleft, hright]
          simp

/-- State-level `(2,3)` commutator with coefficient-or-zero extraction. -/
theorem threePointStateCommutator23_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) (n k : ℕ) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) c) (b := VertexAlgebra.Y (R := R) b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_coefficientOrZero_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m n k)

/-- State-level `(2,3)` anticommutator with coefficient-or-zero extraction. -/
theorem threePointStateAnticommutator23_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) (n k : ℕ) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) c) (b := VertexAlgebra.Y (R := R) b) Fcb k)
            ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) c) Fbc n)
            ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_coefficientOrZero_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m n k)

/-- State-level `(2,3)` commutator vanishing in the above-order regime. -/
theorem threePointStateCommutator23_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : Fcb.data.order ≤ k) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` anticommutator vanishing in the above-order regime. -/
theorem threePointStateAnticommutator23_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : Fcb.data.order ≤ k) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) = 0 := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` commutator extraction in the strict-below regime. -/
theorem threePointStateCommutator23_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : k < Fcb.data.order) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) -
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_opeCoefficient_sub_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` anticommutator extraction in the strict-below regime. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : k < Fcb.data.order) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        ((Fcb.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) +
          Fbc.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_opeCoefficient_add_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` commutator in mixed regime `(ge n, lt k)`. -/
theorem threePointStateCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : k < Fcb.data.order) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` anticommutator in mixed regime `(ge n, lt k)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : Fbc.data.order ≤ n) (hk : k < Fcb.data.order) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` commutator in mixed regime `(lt n, ge k)`. -/
theorem threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : Fcb.data.order ≤ k) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateCommutator23] using
    (threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- State-level `(2,3)` anticommutator in mixed regime `(lt n, ge k)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hn : n < Fbc.data.order) (hk : Fcb.data.order ≤ k) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa [threePointStateAnticommutator23] using
    (threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) Fbc Fcb m hn hk)

/-- Alias with `left/right` naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnLeft : Fbc.data.order ≤ n) (hkRight : k < Fcb.data.order) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkRight⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnLeft hkRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnLeft : Fbc.data.order ≤ n) (hkRight : k < Fcb.data.order) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkRight⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnLeft hkRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnLeft : n < Fbc.data.order) (hkRight : Fcb.data.order ≤ k) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnLeft hkRight)

/-- Alias with `left/right` naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnLeft : n < Fbc.data.order) (hkRight : Fcb.data.order ≤ k) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnLeft hkRight)

/-- State-level alias with `left/right` naming for mixed regime `(ge left, lt right)`. -/
theorem threePointStateCommutator23_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnLeft : Fbc.data.order ≤ n) (hkRight : k < Fcb.data.order) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkRight⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω) a b c Fbc Fcb m hnLeft hkRight)

/-- State-level alias with `left/right` naming for mixed regime `(ge left, lt right)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnLeft : Fbc.data.order ≤ n) (hkRight : k < Fcb.data.order) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkRight⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω) a b c Fbc Fcb m hnLeft hkRight)

/-- State-level alias with `left/right` naming for mixed regime `(lt left, ge right)`. -/
theorem threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnLeft : n < Fbc.data.order) (hkRight : Fcb.data.order ≤ k) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω) a b c Fbc Fcb m hnLeft hkRight)

/-- State-level alias with `left/right` naming for mixed regime `(lt left, ge right)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnLeft : n < Fbc.data.order) (hkRight : Fcb.data.order ≤ k) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hnLeft⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω) a b c Fbc Fcb m hnLeft hkRight)

/-- Alias with explicit orientation naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_bc_lt_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnBC : Fbc.data.order ≤ n) (hkCB : k < Fcb.data.order) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkCB⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator23_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnBC hkCB)

/-- Alias with explicit orientation naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_bc_lt_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnBC : Fbc.data.order ≤ n) (hkCB : k < Fcb.data.order) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkCB⟩
          ((k : ℤ) + (n : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator23_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnBC hkCB)

/-- Alias with explicit orientation naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_bc_ge_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnBC : n < Fbc.data.order) (hkCB : Fcb.data.order ≤ k) :
    threePointCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hnBC⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointCommutator23_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnBC hkCB)

/-- Alias with explicit orientation naming:
    left orientation is `(b,c)`, right orientation is `(c,b)`. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_bc_ge_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b c : FormalDistribution R V}
    (Fbc : OPEFiniteOrder (R := R) (V := V) b c)
    (Fcb : OPEFiniteOrder (R := R) (V := V) c b)
    (m : ℤ) {n k : ℕ}
    (hnBC : n < Fbc.data.order) (hkCB : Fcb.data.order ≤ k) :
    threePointAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hnBC⟩
          ((n : ℤ) + (k : ℤ)) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointAnticommutator23_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) (c := c) Fbc Fcb m hnBC hkCB)

/-- State-level alias with explicit orientation naming for mixed regime `(ge bc, lt cb)`. -/
theorem threePointStateCommutator23_eq_opeCoefficient_of_ge_bc_lt_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnBC : Fbc.data.order ≤ n) (hkCB : k < Fcb.data.order) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkCB⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator23_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b c Fbc Fcb m hnBC hkCB)

/-- State-level alias with explicit orientation naming for mixed regime `(ge bc, lt cb)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_ge_bc_lt_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnBC : Fbc.data.order ≤ n) (hkCB : k < Fcb.data.order) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fcb.data.coefficients ⟨k, hkCB⟩
          ((k : ℤ) + (n : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator23_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b c Fbc Fcb m hnBC hkCB)

/-- State-level alias with explicit orientation naming for mixed regime `(lt bc, ge cb)`. -/
theorem threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_bc_ge_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnBC : n < Fbc.data.order) (hkCB : Fcb.data.order ≤ k) :
    threePointStateCommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      -ω.epsilon
        (Fbc.data.coefficients ⟨n, hnBC⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateCommutator23_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b c Fbc Fcb m hnBC hkCB)

/-- State-level alias with explicit orientation naming for mixed regime `(lt bc, ge cb)`. -/
theorem threePointStateAnticommutator23_eq_opeCoefficient_of_lt_bc_ge_cb
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (Fbc : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c))
    (Fcb : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) c) (VertexAlgebra.Y (R := R) b))
    (m : ℤ) {n k : ℕ}
    (hnBC : n < Fbc.data.order) (hkCB : Fcb.data.order ≤ k) :
    threePointStateAnticommutator23 (R := R) ω a b c m (n : ℤ) (k : ℤ) =
      ω.epsilon
        (Fbc.data.coefficients ⟨n, hnBC⟩
          ((n : ℤ) + (k : ℤ)) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    (threePointStateAnticommutator23_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b c Fbc Fcb m hnBC hkCB)


end StringAlgebra.VOA
