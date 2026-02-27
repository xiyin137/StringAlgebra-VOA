/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Correlators.Basics

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-- Two-point commutator combination:
    `⟨b(n)a(m)⟩ - ⟨a(m)b(n)⟩` in mode-order convention. -/
def twoPointCommutator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) : R :=
  twoPointModes (R := R) ω a b m n - twoPointModes (R := R) ω b a n m

/-- Two-point anticommutator combination:
    `⟨b(n)a(m)⟩ + ⟨a(m)b(n)⟩` in mode-order convention. -/
def twoPointAnticommutator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) : R :=
  twoPointModes (R := R) ω a b m n + twoPointModes (R := R) ω b a n m

/-- Two-point commutator with state insertions via the state-field map. -/
def twoPointStateCommutator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) : R :=
  twoPointCommutator (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m n

/-- Two-point anticommutator with state insertions via the state-field map. -/
def twoPointStateAnticommutator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) : R :=
  twoPointAnticommutator (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m n

@[simp] theorem twoPointCommutator_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a b m n =
      ω.epsilon
        (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) -
          (a m) ((b n) (VertexAlgebra.vacuum (R := R))))) := by
  simp [twoPointCommutator, twoPointModes_eq, map_sub]

@[simp] theorem twoPointAnticommutator_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a b m n =
      ω.epsilon
        (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) +
          (a m) ((b n) (VertexAlgebra.vacuum (R := R))))) := by
  simp [twoPointAnticommutator, twoPointModes_eq, map_add]

@[simp] theorem twoPointStateCommutator_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a b m n =
      twoPointStateModes (R := R) ω a b m n - twoPointStateModes (R := R) ω b a n m := by
  rfl

@[simp] theorem twoPointStateAnticommutator_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a b m n =
      twoPointStateModes (R := R) ω a b m n + twoPointStateModes (R := R) ω b a n m := by
  rfl

@[simp] theorem twoPointStateCommutator_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a b m n =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) -
          (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) (VertexAlgebra.vacuum (R := R))))) := by
  unfold twoPointStateCommutator
  exact twoPointCommutator_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n

@[simp] theorem twoPointStateAnticommutator_eq_apply
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a b m n =
      ω.epsilon
        (((VertexAlgebra.Y (R := R) b n) ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))) +
          (VertexAlgebra.Y (R := R) a m) ((VertexAlgebra.Y (R := R) b n) (VertexAlgebra.vacuum (R := R))))) := by
  unfold twoPointStateAnticommutator
  exact twoPointAnticommutator_eq (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n

/-- Two-point commutator expressed through `nthProduct` difference at mode `m+n`. -/
theorem twoPointCommutator_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a b m n =
      ω.epsilon
        (((nthProduct R V b a n - nthProduct R V a b m) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  have hvec :=
    mode_commutator_eq_nthProduct_sub_apply (R := R) (V := V)
      b a n m (VertexAlgebra.vacuum (R := R))
  calc
    twoPointCommutator (R := R) ω a b m n =
        ω.epsilon
          (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) -
            (a m) ((b n) (VertexAlgebra.vacuum (R := R))))) := by
          exact twoPointCommutator_eq (R := R) (ω := ω) a b m n
    _ = ω.epsilon
          (((nthProduct R V b a n - nthProduct R V a b m) (m + n))
            (VertexAlgebra.vacuum (R := R))) := by
          simpa [add_comm] using congrArg ω.epsilon hvec

/-- Two-point anticommutator expressed through `nthProduct` sum at mode `m+n`. -/
theorem twoPointAnticommutator_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a b m n =
      ω.epsilon
        (((nthProduct R V b a n + nthProduct R V a b m) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  have hvec :=
    mode_anticommutator_eq_nthProduct_add_apply (R := R) (V := V)
      b a n m (VertexAlgebra.vacuum (R := R))
  calc
    twoPointAnticommutator (R := R) ω a b m n =
        ω.epsilon
          (((b n) ((a m) (VertexAlgebra.vacuum (R := R))) +
            (a m) ((b n) (VertexAlgebra.vacuum (R := R))))) := by
          exact twoPointAnticommutator_eq (R := R) (ω := ω) a b m n
    _ = ω.epsilon
          (((nthProduct R V b a n + nthProduct R V a b m) (m + n))
            (VertexAlgebra.vacuum (R := R))) := by
          simpa [add_comm] using congrArg ω.epsilon hvec

/-- State-level two-point commutator via `nthProduct` difference. -/
theorem twoPointStateCommutator_eq_nthProduct_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a b m n =
      ω.epsilon
        (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n -
            nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_nthProduct_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level two-point anticommutator via `nthProduct` sum. -/
theorem twoPointStateAnticommutator_eq_nthProduct_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a b m n =
      ω.epsilon
        (((nthProduct R V (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a) n +
            nthProduct R V (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_nthProduct_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- Two-point mode correlator extracted from an OPE coefficient field. -/
theorem twoPointModes_eq_opeCoefficient
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : Fin F.data.order) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon (F.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  have hcoef :
      (a (j : ℤ)) ((b n) (VertexAlgebra.vacuum (R := R))) =
        F.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)) :=
    OPEFiniteOrder.mode_comp_eq_coefficient_apply_mode_sum
      (R := R) (V := V) (a := a) (b := b) F j n (VertexAlgebra.vacuum (R := R))
  calc
    twoPointModes (R := R) ω b a n (j : ℤ) =
        ω.epsilon ((a (j : ℤ)) ((b n) (VertexAlgebra.vacuum (R := R)))) := by
          simp
    _ = ω.epsilon (F.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
          simpa using congrArg (fun v => ω.epsilon v) hcoef

/-- Two-point mode correlator vanishes for natural mode indices `j ≥ order`. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) = 0 := by
  have hzero : nthProduct R V a b (j : ℤ) = 0 :=
    OPEFiniteOrder.nthProduct_eq_zero_of_ge (R := R) (V := V) (a := a) (b := b) F hj
  calc
    twoPointModes (R := R) ω b a n (j : ℤ) =
        ω.epsilon (((nthProduct R V a b (j : ℤ)) ((j : ℤ) + n))
          (VertexAlgebra.vacuum (R := R))) := by
          simp [twoPointModes_eq, nthProduct]
    _ = 0 := by
          rw [hzero]
          change ω.epsilon ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
          simp

/-- Piecewise finite-order OPE extraction for two-point mode correlators:
    coefficient below OPE order, zero at/above OPE order. -/
theorem twoPointModes_eq_opeCoefficient_or_zero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) =
      if h : j < F.data.order then
        ω.epsilon (F.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  by_cases hlt : j < F.data.order
  · simpa [hlt] using
      twoPointModes_eq_opeCoefficient (R := R) (ω := ω) (a := a) (b := b) F ⟨j, hlt⟩ n
  · have hge : F.data.order ≤ j := Nat.le_of_not_gt hlt
    simpa [hlt] using
      twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω) (a := a) (b := b) F
        (j := j) hge n

/-- Canonical two-point coefficient value at natural index `j`, using
    `coefficientOrZero` evaluated at mode `j+n`. -/
def twoPointCoefficientOrZero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) : R :=
  ω.epsilon
    ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
      ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))

/-- Two-point mode correlator in terms of the extended OPE coefficient field
    (`coefficientOrZero`) evaluated at mode `j+n`. -/
theorem twoPointModes_eq_coefficientOrZero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  have hcomp :
      (a (j : ℤ)) ((b n) (VertexAlgebra.vacuum (R := R))) =
        (OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)) :=
    OPEFiniteOrder.mode_comp_eq_coefficientOrZero_apply_mode_sum
      (R := R) (V := V) (a := a) (b := b) F j n (VertexAlgebra.vacuum (R := R))
  calc
    twoPointModes (R := R) ω b a n (j : ℤ) =
        ω.epsilon ((a (j : ℤ)) ((b n) (VertexAlgebra.vacuum (R := R)))) := by
          simp
    _ = ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
            ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
          simpa using congrArg (fun v => ω.epsilon v) hcomp

/-- Two-point mode correlator equals the canonical coefficient-or-zero value. -/
theorem twoPointModes_eq_twoPointCoefficientOrZero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n := by
  simpa [twoPointCoefficientOrZero] using
    twoPointModes_eq_coefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n

/-- Strict-below-order coefficient extraction for `twoPointCoefficientOrZero`. -/
theorem twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : j < F.data.order) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n =
      ω.epsilon (F.data.coefficients ⟨j, hj⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  unfold twoPointCoefficientOrZero
  simp [OPEFiniteOrder.coefficientOrZero_of_lt (R := R) (V := V) (a := a) (b := b) F hj]

/-- At/above-order vanishing for `twoPointCoefficientOrZero`. -/
theorem twoPointCoefficientOrZero_eq_zero_of_ge
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n = 0 := by
  unfold twoPointCoefficientOrZero
  rw [OPEFiniteOrder.coefficientOrZero_of_ge (R := R) (V := V) (a := a) (b := b) F hj]
  change ω.epsilon ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
  simp

/-- Piecewise form of `twoPointCoefficientOrZero` by OPE order cutoff. -/
theorem twoPointCoefficientOrZero_eq_opeCoefficient_or_zero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n =
      if h : j < F.data.order then
        ω.epsilon (F.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  by_cases hlt : j < F.data.order
  · simpa [hlt] using
      twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
        (R := R) (ω := ω) (a := a) (b := b) F hlt n
  · have hge : F.data.order ≤ j := Nat.le_of_not_gt hlt
    simpa [hlt] using
      twoPointCoefficientOrZero_eq_zero_of_ge
        (R := R) (ω := ω) (a := a) (b := b) F hge n

/-- Strict-below-order extraction through `coefficientOrZero`. -/
theorem twoPointModes_eq_opeCoefficient_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : j < F.data.order) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon (F.data.coefficients ⟨j, hj⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  calc
    twoPointModes (R := R) ω b a n (j : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
            ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) :=
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n
    _ = ω.epsilon (F.data.coefficients ⟨j, hj⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
          simp [OPEFiniteOrder.coefficientOrZero_of_lt (R := R) (V := V) (a := a) (b := b) F hj]

/-- At/above-order vanishing through `coefficientOrZero`. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder'
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) ω b a n (j : ℤ) = 0 := by
  calc
    twoPointModes (R := R) ω b a n (j : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j)
            ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) :=
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω) (a := a) (b := b) F j n
    _ = 0 := by
          rw [OPEFiniteOrder.coefficientOrZero_of_ge
            (R := R) (V := V) (a := a) (b := b) F hj]
          change ω.epsilon ((0 : Module.End R V) (VertexAlgebra.vacuum (R := R))) = 0
          simp

/-- State-level two-point mode correlator extracted from an OPE coefficient field. -/
theorem twoPointStateModes_eq_opeCoefficient
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (j : Fin F.data.order) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon (F.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  unfold twoPointStateModes
  exact twoPointModes_eq_opeCoefficient (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j n

/-- State-level two-point mode correlator vanishes for natural mode indices
    `j ≥ order`. -/
theorem twoPointStateModes_eq_zero_of_ge_opeOrder
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) = 0 := by
  unfold twoPointStateModes
  exact twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F (j := j) hj n

/-- State-level piecewise finite-order OPE extraction for two-point mode correlators:
    coefficient below OPE order, zero at/above OPE order. -/
theorem twoPointStateModes_eq_opeCoefficient_or_zero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (j : ℕ) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) =
      if h : j < F.data.order then
        ω.epsilon (F.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  unfold twoPointStateModes
  exact twoPointModes_eq_opeCoefficient_or_zero (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j n

/-- State-level two-point mode correlator in terms of the extended OPE coefficient
    field (`coefficientOrZero`) evaluated at mode `j+n`. -/
theorem twoPointStateModes_eq_coefficientOrZero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (j : ℕ) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
            (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  unfold twoPointStateModes
  exact twoPointModes_eq_coefficientOrZero (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j n

/-- State-level two-point mode correlator equals the canonical coefficient-or-zero
    value. -/
theorem twoPointStateModes_eq_twoPointCoefficientOrZero
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (j : ℕ) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω)
        (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j n := by
  unfold twoPointStateModes
  exact twoPointModes_eq_twoPointCoefficientOrZero (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F j n

/-- State-level strict-below-order extraction through `coefficientOrZero`. -/
theorem twoPointStateModes_eq_opeCoefficient_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    {j : ℕ} (hj : j < F.data.order) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) =
      ω.epsilon (F.data.coefficients ⟨j, hj⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  unfold twoPointStateModes
  exact twoPointModes_eq_opeCoefficient_of_lt (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F hj n

/-- State-level at/above-order vanishing through `coefficientOrZero`. -/
theorem twoPointStateModes_eq_zero_of_ge_opeOrder'
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (F : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    twoPointStateModes (R := R) ω b a n (j : ℤ) = 0 := by
  unfold twoPointStateModes
  exact twoPointModes_eq_zero_of_ge_opeOrder' (R := R) (ω := ω)
    (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) F (j := j) hj n

/-- If both mode indices are above OPE orders in both orientations, the two-point
    commutator correlator vanishes. -/
theorem twoPointCommutator_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
  have h₁ : twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
    simpa using
      twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω)
        (a := b) (b := a) Fba (j := n) hn (m : ℤ)
  have h₂ : twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) = 0 := by
    simpa using
      twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω)
        (a := a) (b := b) Fab (j := m) hm (n : ℤ)
  unfold twoPointCommutator
  rw [h₁, h₂]
  simp

/-- If both mode indices are above OPE orders in both orientations, the two-point
    anticommutator correlator vanishes. -/
theorem twoPointAnticommutator_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
  have h₁ : twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
    simpa using
      twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω)
        (a := b) (b := a) Fba (j := n) hn (m : ℤ)
  have h₂ : twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) = 0 := by
    simpa using
      twoPointModes_eq_zero_of_ge_opeOrder (R := R) (ω := ω)
        (a := a) (b := b) Fab (j := m) hm (n : ℤ)
  unfold twoPointAnticommutator
  rw [h₁, h₂]
  simp

/-- Two-point commutator correlator for natural mode indices, expressed through
    extended coefficient fields in both OPE orientations. -/
theorem twoPointCommutator_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have h₁ :
      twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
    simpa using
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω)
        (a := b) (b := a) Fba n (m : ℤ)
  have h₂ :
      twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
    simpa using
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω)
        (a := a) (b := b) Fab m (n : ℤ)
  calc
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) -
          twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) := by
          rfl
    _ = ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [h₁, h₂]
    _ = ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [map_sub]

/-- Commutator correlator in terms of canonical `twoPointCoefficientOrZero` values
    in both OPE orientations. -/
theorem twoPointCommutator_eq_twoPointCoefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) -
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) := by
  unfold twoPointCoefficientOrZero
  simpa [sub_eq_add_neg] using
    twoPointCommutator_eq_coefficientOrZero_sub
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n

/-- Two-point anticommutator correlator for natural mode indices, expressed through
    extended coefficient fields in both OPE orientations. -/
theorem twoPointAnticommutator_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  have h₁ :
      twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
    simpa using
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω)
        (a := b) (b := a) Fba n (m : ℤ)
  have h₂ :
      twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) =
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
    simpa using
      twoPointModes_eq_coefficientOrZero (R := R) (ω := ω)
        (a := a) (b := b) Fab m (n : ℤ)
  calc
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointModes (R := R) ω a b (m : ℤ) (n : ℤ) +
          twoPointModes (R := R) ω b a (n : ℤ) (m : ℤ) := by
          rfl
    _ = ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
        ω.epsilon
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [h₁, h₂]
    _ = ω.epsilon
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := b) (b := a) Fba n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V) (a := a) (b := b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
          rw [map_add]

/-- Anticommutator correlator in terms of canonical `twoPointCoefficientOrZero` values
    in both OPE orientations. -/
theorem twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    (m n : ℕ) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) +
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) := by
  unfold twoPointCoefficientOrZero
  simpa using
    twoPointAnticommutator_eq_coefficientOrZero_add
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n

/-- If both mode indices are strictly below their OPE orders, commutator correlator
    is the difference of corresponding OPE coefficient correlators. -/
theorem twoPointCommutator_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) =
        ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) =
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) -
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointCommutator_eq_twoPointCoefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]

/-- If both mode indices are strictly below their OPE orders, anticommutator correlator
    is the sum of corresponding OPE coefficient correlators. -/
theorem twoPointAnticommutator_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) =
        ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) =
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) +
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]

/-- Mixed regime: left index above OPE order for `(a,b)` and right index below OPE order
    for `(b,a)`. The commutator correlator is the right-oriented coefficient term. -/
theorem twoPointCommutator_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) =
        ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) = 0 :=
    twoPointCoefficientOrZero_eq_zero_of_ge
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) -
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointCommutator_eq_twoPointCoefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: left index above OPE order for `(a,b)` and right index below OPE order
    for `(b,a)`. The anticommutator correlator is the right-oriented coefficient term. -/
theorem twoPointAnticommutator_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) =
        ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) = 0 :=
    twoPointCoefficientOrZero_eq_zero_of_ge
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) +
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: left index below OPE order for `(a,b)` and right index above OPE order
    for `(b,a)`. The commutator correlator is minus the left-oriented coefficient term. -/
theorem twoPointCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      -ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) = 0 :=
    twoPointCoefficientOrZero_eq_zero_of_ge
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) =
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) -
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointCommutator_eq_twoPointCoefficientOrZero_sub
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = -ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]
          simp

/-- Mixed regime: left index below OPE order for `(a,b)` and right index above OPE order
    for `(b,a)`. The anticommutator correlator is the left-oriented coefficient term. -/
theorem twoPointAnticommutator_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  have hleft :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) = 0 :=
    twoPointCoefficientOrZero_eq_zero_of_ge
      (R := R) (ω := ω) (a := b) (b := a) Fba hn (m : ℤ)
  have hright :
      twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) =
        ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) :=
    twoPointCoefficientOrZero_eq_opeCoefficient_of_lt
      (R := R) (ω := ω) (a := a) (b := b) Fab hm (n : ℤ)
  calc
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
        twoPointCoefficientOrZero (R := R) (ω := ω) (a := b) (b := a) Fba n (m : ℤ) +
          twoPointCoefficientOrZero (R := R) (ω := ω) (a := a) (b := b) Fab m (n : ℤ) :=
      twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
        (R := R) (ω := ω) (a := a) (b := b) Fab Fba m n
    _ = ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
          rw [hleft, hright]
          simp

/-- State-level two-point commutator vanishes when both mode indices are at/above
    OPE orders in both orientations. -/
theorem twoPointStateCommutator_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- State-level two-point anticommutator vanishes when both mode indices are
    at/above OPE orders in both orientations. -/
theorem twoPointStateAnticommutator_eq_zero_of_ge_opeOrders
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : Fba.data.order ≤ n) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) = 0 := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_zero_of_ge_opeOrders (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- State-level two-point commutator in terms of extended `coefficientOrZero`
    fields in both OPE orientations. -/
theorem twoPointStateCommutator_eq_coefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon
        ((((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_coefficientOrZero_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba m n)

/-- State-level two-point anticommutator in terms of extended `coefficientOrZero`
    fields in both OPE orientations. -/
theorem twoPointStateAnticommutator_eq_coefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon
        ((((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := V)
              (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_coefficientOrZero_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba m n)

/-- State-level two-point commutator in terms of canonical coefficient-or-zero
    values in both OPE orientations. -/
theorem twoPointStateCommutator_eq_twoPointCoefficientOrZero_sub
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω)
        (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n (m : ℤ) -
      twoPointCoefficientOrZero (R := R) (ω := ω)
        (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m (n : ℤ) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_twoPointCoefficientOrZero_sub (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba m n)

/-- State-level two-point anticommutator in terms of canonical coefficient-or-zero
    values in both OPE orientations. -/
theorem twoPointStateAnticommutator_eq_twoPointCoefficientOrZero_add
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    (m n : ℕ) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) (ω := ω)
        (a := VertexAlgebra.Y (R := R) b) (b := VertexAlgebra.Y (R := R) a) Fba n (m : ℤ) +
      twoPointCoefficientOrZero (R := R) (ω := ω)
        (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab m (n : ℤ) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_twoPointCoefficientOrZero_add (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba m n)

/-- Strict-below-order state-level commutator extraction by OPE coefficients. -/
theorem twoPointStateCommutator_eq_opeCoefficient_sub_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_opeCoefficient_sub_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Strict-below-order state-level anticommutator extraction by OPE coefficients. -/
theorem twoPointStateAnticommutator_eq_opeCoefficient_add_of_lt
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : n < Fba.data.order) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_opeCoefficient_add_of_lt (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Mixed regime (left above, right below): state-level commutator is the
    right-oriented coefficient term. -/
theorem twoPointStateCommutator_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_opeCoefficient_of_ge_left_lt_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Mixed regime (left above, right below): state-level anticommutator is the
    right-oriented coefficient term. -/
theorem twoPointStateAnticommutator_eq_opeCoefficient_of_ge_left_lt_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : Fab.data.order ≤ m) (hn : n < Fba.data.order) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_opeCoefficient_of_ge_left_lt_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Mixed regime (left below, right above): state-level commutator is minus the
    left-oriented coefficient term. -/
theorem twoPointStateCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      -ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateCommutator] using
    (twoPointCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Mixed regime (left below, right above): state-level anticommutator is the
    left-oriented coefficient term. -/
theorem twoPointStateAnticommutator_eq_opeCoefficient_of_lt_left_ge_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hm : m < Fab.data.order) (hn : Fba.data.order ≤ n) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fab.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPointStateAnticommutator] using
    (twoPointAnticommutator_eq_opeCoefficient_of_lt_left_ge_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) Fab Fba hm hn)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem twoPointCommutator_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hnRight⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointCommutator_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba hmLeft hnRight)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem twoPointAnticommutator_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hnRight⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointAnticommutator_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba hmLeft hnRight)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem twoPointCommutator_eq_neg_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) :
    twoPointCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      -ω.epsilon (Fab.data.coefficients ⟨m, hmLeft⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba hmLeft hnRight)

/-- Alias with explicit orientation naming:
    left orientation is `(a,b)`, right orientation is `(b,a)`. -/
theorem twoPointAnticommutator_eq_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    {a b : FormalDistribution R V}
    (Fab : OPEFiniteOrder (R := R) (V := V) a b)
    (Fba : OPEFiniteOrder (R := R) (V := V) b a)
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) :
    twoPointAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fab.data.coefficients ⟨m, hmLeft⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointAnticommutator_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) (a := a) (b := b) Fab Fba hmLeft hnRight)

/-- State-level alias with explicit orientation naming for mixed regime `(ge ab, lt ba)`. -/
theorem twoPointStateCommutator_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hnRight⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointStateCommutator_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b Fab Fba hmLeft hnRight)

/-- State-level alias with explicit orientation naming for mixed regime `(ge ab, lt ba)`. -/
theorem twoPointStateAnticommutator_eq_opeCoefficient_of_ge_ab_lt_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : Fab.data.order ≤ m) (hnRight : n < Fba.data.order) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fba.data.coefficients ⟨n, hnRight⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointStateAnticommutator_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω) a b Fab Fba hmLeft hnRight)

/-- State-level alias with explicit orientation naming for mixed regime `(lt ab, ge ba)`. -/
theorem twoPointStateCommutator_eq_neg_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) :
    twoPointStateCommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      -ω.epsilon (Fab.data.coefficients ⟨m, hmLeft⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointStateCommutator_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b Fab Fba hmLeft hnRight)

/-- State-level alias with explicit orientation naming for mixed regime `(lt ab, ge ba)`. -/
theorem twoPointStateAnticommutator_eq_opeCoefficient_of_lt_ab_ge_ba
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (Fab : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b))
    (Fba : OPEFiniteOrder (R := R) (V := V) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) a))
    {m n : ℕ}
    (hmLeft : m < Fab.data.order) (hnRight : Fba.data.order ≤ n) :
    twoPointStateAnticommutator (R := R) ω a b (m : ℤ) (n : ℤ) =
      ω.epsilon (Fab.data.coefficients ⟨m, hmLeft⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))) := by
  simpa using
    (twoPointStateAnticommutator_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω) a b Fab Fba hmLeft hnRight)

/-- Correlator linearity in the first inserted field mode. -/
theorem twoPointModes_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω (a + b) c m n =
      twoPointModes (R := R) ω a c m n + twoPointModes (R := R) ω b c m n := by
  have hmode : (a + b) m = a m + b m := rfl
  simp [twoPointModes_eq, hmode, LinearMap.map_add]

/-- Correlator linearity in the second inserted field mode. -/
theorem twoPointModes_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a (b + c) m n =
      twoPointModes (R := R) ω a b m n + twoPointModes (R := R) ω a c m n := by
  have hmode : (b + c) n = b n + c n := rfl
  simp [twoPointModes_eq, hmode, LinearMap.map_add]

/-- Correlator linearity under scalar multiplication in the first field slot. -/
theorem twoPointModes_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω (r • a) b m n =
      r • twoPointModes (R := R) ω a b m n := by
  have hmode : (r • a) m = r • a m := rfl
  simp [twoPointModes_eq, hmode]

/-- Correlator linearity under scalar multiplication in the second field slot. -/
theorem twoPointModes_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a (r • b) m n =
      r • twoPointModes (R := R) ω a b m n := by
  have hmode : (r • b) n = r • b n := rfl
  simp [twoPointModes_eq, hmode]

/-- Negation linearity in the first field slot. -/
theorem twoPointModes_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω (-a) b m n =
      -twoPointModes (R := R) ω a b m n := by
  simpa using twoPointModes_smul_left (R := R) (ω := ω) (-1 : R) a b m n

/-- Negation linearity in the second field slot. -/
theorem twoPointModes_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a (-b) m n =
      -twoPointModes (R := R) ω a b m n := by
  simpa using twoPointModes_smul_right (R := R) (ω := ω) (-1 : R) a b m n

/-- Subtraction linearity in the first field slot. -/
theorem twoPointModes_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω (a - b) c m n =
      twoPointModes (R := R) ω a c m n - twoPointModes (R := R) ω b c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointModes_add_left (R := R) (ω := ω) a (-b) c m n]
  rw [twoPointModes_neg_left (R := R) (ω := ω) b c m n]
  simp [sub_eq_add_neg]

/-- Subtraction linearity in the second field slot. -/
theorem twoPointModes_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a (b - c) m n =
      twoPointModes (R := R) ω a b m n - twoPointModes (R := R) ω a c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointModes_add_right (R := R) (ω := ω) a b (-c) m n]
  rw [twoPointModes_neg_right (R := R) (ω := ω) a c m n]
  simp [sub_eq_add_neg]

/-- State-level two-point correlator linearity in the first inserted mode. -/
theorem twoPointStateModes_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω (a + b) c m n =
      twoPointStateModes (R := R) ω a c m n +
        twoPointStateModes (R := R) ω b c m n := by
  unfold twoPointStateModes
  simpa [hYadd] using
    (twoPointModes_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level two-point correlator linearity in the second inserted mode. -/
theorem twoPointStateModes_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω a (b + c) m n =
      twoPointStateModes (R := R) ω a b m n +
        twoPointStateModes (R := R) ω a c m n := by
  unfold twoPointStateModes
  simpa [hYadd] using
    (twoPointModes_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level two-point correlator linearity under scalar multiplication in
    the first field slot. -/
theorem twoPointStateModes_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω (r • a) b m n =
      r • twoPointStateModes (R := R) ω a b m n := by
  unfold twoPointStateModes
  simpa [hYsmul] using
    (twoPointModes_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level two-point correlator linearity under scalar multiplication in
    the second field slot. -/
theorem twoPointStateModes_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω a (r • b) m n =
      r • twoPointStateModes (R := R) ω a b m n := by
  unfold twoPointStateModes
  simpa [hYsmul] using
    (twoPointModes_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level negation linearity in the first field slot. -/
theorem twoPointStateModes_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω (-a) b m n =
      -twoPointStateModes (R := R) ω a b m n := by
  unfold twoPointStateModes
  simpa [hYneg] using
    (twoPointModes_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level negation linearity in the second field slot. -/
theorem twoPointStateModes_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω a (-b) m n =
      -twoPointStateModes (R := R) ω a b m n := by
  unfold twoPointStateModes
  simpa [hYneg] using
    (twoPointModes_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level subtraction linearity in the first field slot. -/
theorem twoPointStateModes_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω (a - b) c m n =
      twoPointStateModes (R := R) ω a c m n -
        twoPointStateModes (R := R) ω b c m n := by
  unfold twoPointStateModes
  simpa [hYsub] using
    (twoPointModes_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level subtraction linearity in the second field slot. -/
theorem twoPointStateModes_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateModes (R := R) ω a (b - c) m n =
      twoPointStateModes (R := R) ω a b m n -
        twoPointStateModes (R := R) ω a c m n := by
  unfold twoPointStateModes
  simpa [hYsub] using
    (twoPointModes_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- Commutator correlator is additive in the first field slot. -/
theorem twoPointCommutator_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω (a + b) c m n =
      twoPointCommutator (R := R) ω a c m n +
        twoPointCommutator (R := R) ω b c m n := by
  unfold twoPointCommutator
  rw [twoPointModes_add_left (R := R) (ω := ω) a b c m n]
  rw [twoPointModes_add_right (R := R) (ω := ω) c a b n m]
  abel_nf

/-- Commutator correlator is additive in the second field slot. -/
theorem twoPointCommutator_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a (b + c) m n =
      twoPointCommutator (R := R) ω a b m n +
        twoPointCommutator (R := R) ω a c m n := by
  unfold twoPointCommutator
  rw [twoPointModes_add_right (R := R) (ω := ω) a b c m n]
  rw [twoPointModes_add_left (R := R) (ω := ω) b c a n m]
  abel_nf

/-- Commutator correlator is linear under scalar multiplication in the first slot. -/
theorem twoPointCommutator_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω (r • a) b m n =
      r • twoPointCommutator (R := R) ω a b m n := by
  unfold twoPointCommutator
  rw [twoPointModes_smul_left (R := R) (ω := ω) r a b m n]
  rw [twoPointModes_smul_right (R := R) (ω := ω) r b a n m]
  simp [mul_sub]

/-- Commutator correlator is linear under scalar multiplication in the second slot. -/
theorem twoPointCommutator_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a (r • b) m n =
      r • twoPointCommutator (R := R) ω a b m n := by
  unfold twoPointCommutator
  rw [twoPointModes_smul_right (R := R) (ω := ω) r a b m n]
  rw [twoPointModes_smul_left (R := R) (ω := ω) r b a n m]
  simp [mul_sub]

/-- Anticommutator correlator is additive in the first field slot. -/
theorem twoPointAnticommutator_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω (a + b) c m n =
      twoPointAnticommutator (R := R) ω a c m n +
        twoPointAnticommutator (R := R) ω b c m n := by
  unfold twoPointAnticommutator
  rw [twoPointModes_add_left (R := R) (ω := ω) a b c m n]
  rw [twoPointModes_add_right (R := R) (ω := ω) c a b n m]
  abel_nf

/-- Anticommutator correlator is additive in the second field slot. -/
theorem twoPointAnticommutator_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a (b + c) m n =
      twoPointAnticommutator (R := R) ω a b m n +
        twoPointAnticommutator (R := R) ω a c m n := by
  unfold twoPointAnticommutator
  rw [twoPointModes_add_right (R := R) (ω := ω) a b c m n]
  rw [twoPointModes_add_left (R := R) (ω := ω) b c a n m]
  abel_nf

/-- Anticommutator correlator is linear under scalar multiplication in the first slot. -/
theorem twoPointAnticommutator_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω (r • a) b m n =
      r • twoPointAnticommutator (R := R) ω a b m n := by
  unfold twoPointAnticommutator
  rw [twoPointModes_smul_left (R := R) (ω := ω) r a b m n]
  rw [twoPointModes_smul_right (R := R) (ω := ω) r b a n m]
  simp [mul_add]

/-- Anticommutator correlator is linear under scalar multiplication in the second slot. -/
theorem twoPointAnticommutator_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a (r • b) m n =
      r • twoPointAnticommutator (R := R) ω a b m n := by
  unfold twoPointAnticommutator
  rw [twoPointModes_smul_right (R := R) (ω := ω) r a b m n]
  rw [twoPointModes_smul_left (R := R) (ω := ω) r b a n m]
  simp [mul_add]

/-- Commutator correlator is negation-linear in the first field slot. -/
theorem twoPointCommutator_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω (-a) b m n =
      -twoPointCommutator (R := R) ω a b m n := by
  simpa using twoPointCommutator_smul_left (R := R) (ω := ω) (-1 : R) a b m n

/-- Commutator correlator is negation-linear in the second field slot. -/
theorem twoPointCommutator_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a (-b) m n =
      -twoPointCommutator (R := R) ω a b m n := by
  simpa using twoPointCommutator_smul_right (R := R) (ω := ω) (-1 : R) a b m n

/-- Commutator correlator is subtraction-linear in the first field slot. -/
theorem twoPointCommutator_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω (a - b) c m n =
      twoPointCommutator (R := R) ω a c m n -
        twoPointCommutator (R := R) ω b c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointCommutator_add_left (R := R) (ω := ω) a (-b) c m n]
  rw [twoPointCommutator_neg_left (R := R) (ω := ω) b c m n]
  simp [sub_eq_add_neg]

/-- Commutator correlator is subtraction-linear in the second field slot. -/
theorem twoPointCommutator_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointCommutator (R := R) ω a (b - c) m n =
      twoPointCommutator (R := R) ω a b m n -
        twoPointCommutator (R := R) ω a c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointCommutator_add_right (R := R) (ω := ω) a b (-c) m n]
  rw [twoPointCommutator_neg_right (R := R) (ω := ω) a c m n]
  simp [sub_eq_add_neg]

/-- Anticommutator correlator is negation-linear in the first field slot. -/
theorem twoPointAnticommutator_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω (-a) b m n =
      -twoPointAnticommutator (R := R) ω a b m n := by
  simpa using twoPointAnticommutator_smul_left (R := R) (ω := ω) (-1 : R) a b m n

/-- Anticommutator correlator is negation-linear in the second field slot. -/
theorem twoPointAnticommutator_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a (-b) m n =
      -twoPointAnticommutator (R := R) ω a b m n := by
  simpa using twoPointAnticommutator_smul_right (R := R) (ω := ω) (-1 : R) a b m n

/-- Anticommutator correlator is subtraction-linear in the first field slot. -/
theorem twoPointAnticommutator_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω (a - b) c m n =
      twoPointAnticommutator (R := R) ω a c m n -
        twoPointAnticommutator (R := R) ω b c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointAnticommutator_add_left (R := R) (ω := ω) a (-b) c m n]
  rw [twoPointAnticommutator_neg_left (R := R) (ω := ω) b c m n]
  simp [sub_eq_add_neg]

/-- Anticommutator correlator is subtraction-linear in the second field slot. -/
theorem twoPointAnticommutator_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n : ℤ) :
    twoPointAnticommutator (R := R) ω a (b - c) m n =
      twoPointAnticommutator (R := R) ω a b m n -
        twoPointAnticommutator (R := R) ω a c m n := by
  rw [sub_eq_add_neg]
  rw [twoPointAnticommutator_add_right (R := R) (ω := ω) a b (-c) m n]
  rw [twoPointAnticommutator_neg_right (R := R) (ω := ω) a c m n]
  simp [sub_eq_add_neg]

/-- State-level commutator correlator is additive in the first field slot. -/
theorem twoPointStateCommutator_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω (a + b) c m n =
      twoPointStateCommutator (R := R) ω a c m n +
        twoPointStateCommutator (R := R) ω b c m n := by
  unfold twoPointStateCommutator
  simpa [hYadd] using
    (twoPointCommutator_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level commutator correlator is additive in the second field slot. -/
theorem twoPointStateCommutator_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a (b + c) m n =
      twoPointStateCommutator (R := R) ω a b m n +
        twoPointStateCommutator (R := R) ω a c m n := by
  unfold twoPointStateCommutator
  simpa [hYadd] using
    (twoPointCommutator_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level commutator correlator is linear under scalar multiplication in
    the first slot. -/
theorem twoPointStateCommutator_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω (r • a) b m n =
      r • twoPointStateCommutator (R := R) ω a b m n := by
  unfold twoPointStateCommutator
  simpa [hYsmul] using
    (twoPointCommutator_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level commutator correlator is linear under scalar multiplication in
    the second slot. -/
theorem twoPointStateCommutator_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a (r • b) m n =
      r • twoPointStateCommutator (R := R) ω a b m n := by
  unfold twoPointStateCommutator
  simpa [hYsmul] using
    (twoPointCommutator_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level commutator correlator is negation-linear in the first field
    slot. -/
theorem twoPointStateCommutator_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω (-a) b m n =
      -twoPointStateCommutator (R := R) ω a b m n := by
  unfold twoPointStateCommutator
  simpa [hYneg] using
    (twoPointCommutator_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level commutator correlator is negation-linear in the second field
    slot. -/
theorem twoPointStateCommutator_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a (-b) m n =
      -twoPointStateCommutator (R := R) ω a b m n := by
  unfold twoPointStateCommutator
  simpa [hYneg] using
    (twoPointCommutator_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level commutator correlator is subtraction-linear in the first field
    slot. -/
theorem twoPointStateCommutator_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω (a - b) c m n =
      twoPointStateCommutator (R := R) ω a c m n -
        twoPointStateCommutator (R := R) ω b c m n := by
  unfold twoPointStateCommutator
  simpa [hYsub] using
    (twoPointCommutator_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level commutator correlator is subtraction-linear in the second field
    slot. -/
theorem twoPointStateCommutator_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateCommutator (R := R) ω a (b - c) m n =
      twoPointStateCommutator (R := R) ω a b m n -
        twoPointStateCommutator (R := R) ω a c m n := by
  unfold twoPointStateCommutator
  simpa [hYsub] using
    (twoPointCommutator_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level anticommutator correlator is additive in the first field slot. -/
theorem twoPointStateAnticommutator_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω (a + b) c m n =
      twoPointStateAnticommutator (R := R) ω a c m n +
        twoPointStateAnticommutator (R := R) ω b c m n := by
  unfold twoPointStateAnticommutator
  simpa [hYadd] using
    (twoPointAnticommutator_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level anticommutator correlator is additive in the second field slot. -/
theorem twoPointStateAnticommutator_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a (b + c) m n =
      twoPointStateAnticommutator (R := R) ω a b m n +
        twoPointStateAnticommutator (R := R) ω a c m n := by
  unfold twoPointStateAnticommutator
  simpa [hYadd] using
    (twoPointAnticommutator_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level anticommutator correlator is linear under scalar multiplication in
    the first slot. -/
theorem twoPointStateAnticommutator_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω (r • a) b m n =
      r • twoPointStateAnticommutator (R := R) ω a b m n := by
  unfold twoPointStateAnticommutator
  simpa [hYsmul] using
    (twoPointAnticommutator_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level anticommutator correlator is linear under scalar multiplication in
    the second slot. -/
theorem twoPointStateAnticommutator_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a (r • b) m n =
      r • twoPointStateAnticommutator (R := R) ω a b m n := by
  unfold twoPointStateAnticommutator
  simpa [hYsmul] using
    (twoPointAnticommutator_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level anticommutator correlator is negation-linear in the first field
    slot. -/
theorem twoPointStateAnticommutator_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω (-a) b m n =
      -twoPointStateAnticommutator (R := R) ω a b m n := by
  unfold twoPointStateAnticommutator
  simpa [hYneg] using
    (twoPointAnticommutator_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level anticommutator correlator is negation-linear in the second field
    slot. -/
theorem twoPointStateAnticommutator_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a (-b) m n =
      -twoPointStateAnticommutator (R := R) ω a b m n := by
  unfold twoPointStateAnticommutator
  simpa [hYneg] using
    (twoPointAnticommutator_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n)

/-- State-level anticommutator correlator is subtraction-linear in the first
    field slot. -/
theorem twoPointStateAnticommutator_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω (a - b) c m n =
      twoPointStateAnticommutator (R := R) ω a c m n -
        twoPointStateAnticommutator (R := R) ω b c m n := by
  unfold twoPointStateAnticommutator
  simpa [hYsub] using
    (twoPointAnticommutator_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)

/-- State-level anticommutator correlator is subtraction-linear in the second
    field slot. -/
theorem twoPointStateAnticommutator_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n : ℤ) :
    twoPointStateAnticommutator (R := R) ω a (b - c) m n =
      twoPointStateAnticommutator (R := R) ω a b m n -
        twoPointStateAnticommutator (R := R) ω a c m n := by
  unfold twoPointStateAnticommutator
  simpa [hYsub] using
    (twoPointAnticommutator_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n)


end StringAlgebra.VOA
