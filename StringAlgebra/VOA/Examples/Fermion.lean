/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Examples.Boson

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

namespace CARFamily

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Algebraic two-point function from CAR modes and a vacuum package. -/
def twoPoint (F : CARFamily (R := R) (V := V)) (ω : ModeVacuumData R V) (m n : ℤ) : R :=
  ω.epsilon ((F.psi m) ((F.psi n) ω.vacuum))

/-- CAR anticommutator gives the two-point anticommutator identity. -/
theorem twoPoint_anticommutator
    (F : CARFamily (R := R) (V := V)) (ω : ModeVacuumData R V) (m n : ℤ) :
    twoPoint F ω m n + twoPoint F ω n m =
      if m + n = 0 then F.normalization else 0 := by
  have hanti := F.anticommutator_spec m n
  have happly :
      ω.epsilon ((antiComm (R := R) (F.psi m) (F.psi n)) ω.vacuum) =
        ω.epsilon ((if m + n = 0
          then F.normalization • (LinearMap.id : Module.End R V)
          else 0) ω.vacuum) := by
    exact congrArg (fun T : Module.End R V => ω.epsilon (T ω.vacuum)) hanti
  calc
    twoPoint F ω m n + twoPoint F ω n m
        = ω.epsilon ((antiComm (R := R) (F.psi m) (F.psi n)) ω.vacuum) := by
          simp [twoPoint, antiComm, Module.End.mul_apply, map_add]
    _ = ω.epsilon ((if m + n = 0
          then F.normalization • (LinearMap.id : Module.End R V)
          else 0) ω.vacuum) := happly
    _ = if m + n = 0 then F.normalization else 0 := by
          by_cases h : m + n = 0 <;> simp [h, ω.vacuum_norm]

/-- Off-diagonal two-point anticommutator vanishes when `m + n ≠ 0`. -/
theorem twoPoint_anticommutator_offdiag
    (F : CARFamily (R := R) (V := V)) (ω : ModeVacuumData R V)
    {m n : ℤ} (h : m + n ≠ 0) :
    twoPoint F ω m n + twoPoint F ω n m = 0 := by
  simp [twoPoint_anticommutator (F := F) (ω := ω), h]

end CARFamily

/-! ## Free Fermion VOA (super-CAR skeleton)

An algebraic free-fermion model is packaged by a carrier and CAR mode family.
-/

/-- Algebraic data for a free-fermion model based on CAR modes. -/
structure FreeFermionVOA (R : Type*) [CommRing R] where
  /-- State-space carrier. -/
  Carrier : Type*
  [addCommGroup : AddCommGroup Carrier]
  [module : Module R Carrier]
  /-- Fermionic modes satisfying CAR. -/
  carModes : CARFamily (R := R) (V := Carrier)

attribute [instance] FreeFermionVOA.addCommGroup FreeFermionVOA.module

namespace FreeFermionVOA

variable {R : Type*} [CommRing R]

/-- The formal fermion field extracted from the CAR mode family. -/
def fermionField (F : FreeFermionVOA R) : FormalDistribution R F.Carrier :=
  F.carModes.toFormalDistribution

/-- The fermion field viewed as an odd super field. -/
def fermionSuperField (F : FreeFermionVOA R) : SuperFormalDistribution R F.Carrier :=
  SuperFormalDistribution.odd (R := R) (V := F.Carrier) F.fermionField

/-- CAR implies odd super-locality of the fermion field. -/
theorem fermion_superLocal (F : FreeFermionVOA R) :
    SuperFormalDistribution.superMutuallyLocal (R := R) (V := F.Carrier)
      F.fermionSuperField F.fermionSuperField := by
  simpa [fermionSuperField, fermionField] using
    CARFamily.superMutuallyLocal_odd_self (R := R) (V := F.Carrier) F.carModes

/-- CAR also yields eventual mode anticommutativity of the fermion field. -/
theorem fermion_modes_eventually_anticommute (F : FreeFermionVOA R) :
    ∃ N : ℤ, ∀ v : F.Carrier, ∀ m n : ℤ, m + n ≥ N →
      (F.fermionField m) ((F.fermionField n) v) +
        (F.fermionField n) ((F.fermionField m) v) = 0 := by
  exact
    (SuperFormalDistribution.superMutuallyLocal_odd_odd_iff
      (R := R) (V := F.Carrier) F.fermionField F.fermionField).mp F.fermion_superLocal

/-- Two-point fermionic mode correlator in a chosen vacuum package. -/
def twoPoint (F : FreeFermionVOA R) (ω : ModeVacuumData R F.Carrier) (m n : ℤ) : R :=
  CARFamily.twoPoint (R := R) (V := F.Carrier) F.carModes ω m n

/-- The fermionic mode correlator matches `twoPointModes` with reversed mode-index order. -/
theorem twoPoint_eq_twoPointModes_swapped
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
  (m n : ℤ) :
  F.twoPoint ω m n =
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m := by
  simp [twoPoint, fermionField, CARFamily.twoPoint,
    ModeVacuumData.toVacuumFunctional, hVac]

/-- Two-point fermionic anticommutator identity from CAR. -/
theorem twoPoint_anticommutator
    (F : FreeFermionVOA R) (ω : ModeVacuumData R F.Carrier) (m n : ℤ) :
    F.twoPoint ω m n + F.twoPoint ω n m =
      if m + n = 0 then F.carModes.normalization else 0 := by
  simpa [twoPoint] using
    CARFamily.twoPoint_anticommutator (R := R) (V := F.Carrier) F.carModes ω m n

/-- Off-diagonal fermionic two-point anticommutator vanishes. -/
theorem twoPoint_anticommutator_offdiag
    (F : FreeFermionVOA R) (ω : ModeVacuumData R F.Carrier)
    {m n : ℤ} (h : m + n ≠ 0) :
    F.twoPoint ω m n + F.twoPoint ω n m = 0 := by
  simp [twoPoint_anticommutator (F := F) (ω := ω), h]

/-- Diagonal fermionic two-point anticommutator specialization. -/
theorem twoPoint_anticommutator_diag
    (F : FreeFermionVOA R) (ω : ModeVacuumData R F.Carrier) (m : ℤ) :
    F.twoPoint ω m (-m) + F.twoPoint ω (-m) m =
      F.carModes.normalization := by
  simp [twoPoint_anticommutator (F := F) (ω := ω) (m := m) (n := -m)]

/-- Correlator-form fermionic anticommutator identity in the `twoPointModes` API. -/
theorem twoPointModes_anticommutator
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m +
      twoPointModes (R := R) (ω.toVacuumFunctional hVac)
        F.fermionField F.fermionField m n =
      if m + n = 0 then F.carModes.normalization else 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)] using
    F.twoPoint_anticommutator ω m n

/-- Correlator-form fermionic anticommutator identity via `twoPointAnticommutator`. -/
theorem twoPointAnticommutator_primitive
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m =
      if m + n = 0 then F.carModes.normalization else 0 := by
  simpa [StringAlgebra.VOA.twoPointAnticommutator] using
    F.twoPointModes_anticommutator (ω := ω) (hVac := hVac) m n

/-- Primitive fermionic anticommutator in explicit `nthProduct`-sum form. -/
theorem twoPointAnticommutator_primitive_eq_nthProduct_add
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m =
      (ω.toVacuumFunctional hVac).epsilon
        (((nthProduct R F.Carrier F.fermionField F.fermionField m +
          nthProduct R F.Carrier F.fermionField F.fermionField n) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  simpa [add_comm] using
    twoPointAnticommutator_eq_nthProduct_add (R := R) (ω := ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m

/-- CAR two-point anticommutator identity in explicit `nthProduct`-sum form. -/
theorem twoPoint_nthProduct_add_evaluation
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    (ω.toVacuumFunctional hVac).epsilon
      (((nthProduct R F.Carrier F.fermionField F.fermionField m +
        nthProduct R F.Carrier F.fermionField F.fermionField n) (m + n))
        (VertexAlgebra.vacuum (R := R))) =
      if m + n = 0 then F.carModes.normalization else 0 := by
  calc
    (ω.toVacuumFunctional hVac).epsilon
      (((nthProduct R F.Carrier F.fermionField F.fermionField m +
        nthProduct R F.Carrier F.fermionField F.fermionField n) (m + n))
        (VertexAlgebra.vacuum (R := R))) =
      StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
        F.fermionField F.fermionField n m := by
          symm
          exact twoPointAnticommutator_primitive_eq_nthProduct_add
            (F := F) (ω := ω) (hVac := hVac) m n
    _ = if m + n = 0 then F.carModes.normalization else 0 :=
      twoPointAnticommutator_primitive (F := F) (ω := ω) (hVac := hVac) m n

/-- Off-diagonal fermionic correlator anticommutator vanishing in primitive form. -/
theorem twoPointAnticommutator_primitive_offdiag
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    {m n : ℤ} (h : m + n ≠ 0) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n m = 0 := by
  have hmain := twoPointAnticommutator_primitive (F := F) (ω := ω) (hVac := hVac) m n
  simpa [h] using hmain

/-- Diagonal fermionic correlator anticommutator specialization in primitive form. -/
theorem twoPointAnticommutator_primitive_diag
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m : ℤ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField (-m) m =
      F.carModes.normalization := by
  have hmain := twoPointAnticommutator_primitive (F := F) (ω := ω) (hVac := hVac) m (-m)
  simpa using hmain

/-- OPE coefficient extraction for fermionic two-point mode correlators. -/
theorem twoPointModes_eq_opeCoefficient
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : Fin O.data.order) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n (j : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  exact StringAlgebra.VOA.twoPointModes_eq_opeCoefficient
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O j n

/-- Fermionic two-point mode correlators vanish above the OPE singular order. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    {j : ℕ} (hj : O.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n (j : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointModes_eq_zero_of_ge_opeOrder
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O (j := j) hj n

/-- OPE coefficient extraction in model-level fermionic two-point notation. -/
theorem twoPoint_eq_opeCoefficient_leftMode
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : Fin O.data.order) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_opeCoefficient (F := F) (ω := ω) (hVac := hVac) O j n

/-- Model-level fermionic two-point correlators vanish above the OPE singular order. -/
theorem twoPoint_eq_zero_of_ge_opeOrder_leftMode
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    {j : ℕ} (hj : O.data.order ≤ j) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n = 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_zero_of_ge_opeOrder (F := F) (ω := ω) (hVac := hVac)
      O (j := j) hj n

/-- Piecewise finite-order OPE extraction for fermionic `twoPointModes`. -/
theorem twoPointModes_eq_opeCoefficient_or_zero
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n (j : ℤ) =
      if h : j < O.data.order then
        (ω.toVacuumFunctional hVac).epsilon
          (O.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  exact StringAlgebra.VOA.twoPointModes_eq_opeCoefficient_or_zero
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O j n

/-- Piecewise finite-order OPE extraction in fermionic model-level `twoPoint` notation. -/
theorem twoPoint_eq_opeCoefficient_or_zero_leftMode
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : ℕ) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      if h : j < O.data.order then
        (ω.toVacuumFunctional hVac).epsilon
          (O.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_opeCoefficient_or_zero (F := F) (ω := ω) (hVac := hVac) O j n

/-- Fermionic correlator in terms of the extended coefficient field `coefficientOrZero`. -/
theorem twoPointModes_eq_coefficientOrZero
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField n (j : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
          (a := F.fermionField) (b := F.fermionField) O j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  exact StringAlgebra.VOA.twoPointModes_eq_coefficientOrZero
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O j n

/-- Model-level fermionic correlator in extended-coefficient form. -/
theorem twoPoint_eq_coefficientOrZero_leftMode
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (j : ℕ) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      (ω.toVacuumFunctional hVac).epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
          (a := F.fermionField) (b := F.fermionField) O j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_coefficientOrZero (F := F) (ω := ω) (hVac := hVac) O j n

/-- Above OPE order in both mode indices, fermionic two-point commutator correlator vanishes. -/
theorem twoPointCommutator_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointCommutator_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O O hm hn

/-- Above OPE order in both mode indices, fermionic two-point anticommutator correlator vanishes. -/
theorem twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointAnticommutator_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) O O hm hn

/-- Fermionic commutator correlator via extended coefficients in both OPE orientations. -/
theorem twoPointCommutator_eq_coefficientOrZero_sub
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (m n : ℕ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.twoPointCommutator_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) O O m n

/-- Fermionic anticommutator correlator via extended coefficients in both OPE orientations. -/
theorem twoPointAnticommutator_eq_coefficientOrZero_add
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (m n : ℕ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.twoPointAnticommutator_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) O O m n

/-- Fermionic three-point commutator (first two insertions) via extended coefficients. -/
theorem threePointCommutator12_eq_coefficientOrZero_sub
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) O n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) O m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O m n k

/-- Fermionic three-point anticommutator (first two insertions) via extended coefficients. -/
theorem threePointAnticommutator12_eq_coefficientOrZero_add
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) O n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) O m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O m n k

/-- Above OPE order in both indices, fermionic three-point commutator
    (first two insertions) vanishes. -/
theorem threePointCommutator12_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointCommutator12_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Above OPE order in both indices, fermionic three-point anticommutator
    (first two insertions) vanishes. -/
theorem threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator12_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Below OPE order in both mode indices, fermionic three-point commutator
    (first two insertions) is the difference of OPE coefficient correlators. -/
theorem threePointCommutator12_eq_opeCoefficient_sub_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          ((O.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (O.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Below OPE order in both mode indices, fermionic three-point anticommutator
    (first two insertions) is the sum of OPE coefficient correlators. -/
theorem threePointAnticommutator12_eq_opeCoefficient_add_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          ((O.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (O.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Mixed regime (`m` above OPE order, `n` below OPE order):
    fermionic three-point commutator (first two insertions) reduces to the
    right-oriented OPE coefficient correlator. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Mixed regime (`m` above OPE order, `n` below OPE order):
    fermionic three-point anticommutator (first two insertions) reduces to the
    right-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Mixed regime (`m` below OPE order, `n` above OPE order):
    fermionic three-point commutator (first two insertions) is minus the
    left-oriented OPE coefficient correlator. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      -(ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Mixed regime (`m` below OPE order, `n` above OPE order):
    fermionic three-point anticommutator (first two insertions) reduces to the
    left-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := F.fermionField) (c := x) O O hm hn k

/-- Fermionic three-point commutator (last two insertions) via extended coefficients. -/
theorem threePointCommutator23_eq_coefficientOrZero_sub
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m n k

/-- Fermionic three-point anticommutator (last two insertions) via extended coefficients. -/
theorem threePointAnticommutator23_eq_coefficientOrZero_add
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) O n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m n k

/-- Above OPE order in both indices, fermionic three-point commutator (last two
    insertions) vanishes. -/
theorem threePointCommutator23_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) = 0 := by
  exact StringAlgebra.VOA.threePointCommutator23_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Above OPE order in both indices, fermionic three-point anticommutator (last two
    insertions) vanishes. -/
theorem threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator23_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Below OPE order in both mode indices, fermionic three-point commutator (last two
    insertions) is the difference of OPE coefficient correlators. -/
theorem threePointCommutator23_eq_opeCoefficient_sub_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((O.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          O.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Below OPE order in both mode indices, fermionic three-point anticommutator (last two
    insertions) is the sum of OPE coefficient correlators. -/
theorem threePointAnticommutator23_eq_opeCoefficient_add_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((O.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          O.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Mixed regime (`n` above OPE order, `k` below OPE order):
    fermionic three-point commutator (last two insertions) reduces to the
    `k`-oriented OPE coefficient correlator. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Mixed regime (`n` above OPE order, `k` below OPE order):
    fermionic three-point anticommutator (last two insertions) reduces to the
    `k`-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Mixed regime (`n` below OPE order, `k` above OPE order):
    fermionic three-point commutator (last two insertions) is minus the
    `n`-oriented OPE coefficient correlator. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      -(ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Mixed regime (`n` below OPE order, `k` above OPE order):
    fermionic three-point anticommutator (last two insertions) reduces to the
    `n`-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.fermionField) (c := F.fermionField) O O m hn hk

/-- Fermionic three-point commutator (first and third insertions) via extended coefficients,
    with explicit OPE data for the middle-to-first and middle-to-third channels. -/
theorem threePointCommutator13_eq_coefficientOrZero_sub
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.fermionField k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.fermionField) Oba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (F.fermionField m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.fermionField) Obc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m n k

/-- Fermionic three-point anticommutator (first and third insertions) via extended coefficients,
    with explicit OPE data for the middle-to-first and middle-to-third channels. -/
theorem threePointAnticommutator13_eq_coefficientOrZero_add
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.fermionField k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.fermionField) Oba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (F.fermionField m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.fermionField) Obc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m n k

/-- High-middle-mode vanishing for fermionic first/third three-point commutator,
    with explicit middle-channel OPE assumptions. -/
theorem threePointCommutator13_eq_zero_of_ge_opeOrders
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointCommutator13_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- High-middle-mode vanishing for fermionic first/third three-point anticommutator,
    with explicit middle-channel OPE assumptions. -/
theorem threePointAnticommutator13_eq_zero_of_ge_opeOrders
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator13_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Strict-below-order extraction for fermionic first/third three-point commutator. -/
theorem threePointCommutator13_eq_opeCoefficient_sub_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.fermionField k)
            (Oba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (F.fermionField m)
            (Obc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Strict-below-order extraction for fermionic first/third three-point anticommutator. -/
theorem threePointAnticommutator13_eq_opeCoefficient_add_of_lt
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.fermionField k)
            (Oba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (F.fermionField m)
            (Obc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` at/above order, `(b,c)` below order) for fermionic
    first/third commutator extraction. -/
theorem threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      -(ω.toVacuumFunctional hVac).epsilon
        ((F.fermionField m) (Obc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` at/above order, `(b,c)` below order) for fermionic
    first/third anticommutator extraction. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.fermionField m) (Obc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` below order, `(b,c)` at/above order) for fermionic
    first/third commutator extraction. -/
theorem threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.fermionField k) (Oba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` below order, `(b,c)` at/above order) for fermionic
    first/third anticommutator extraction. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.fermionField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.fermionField x F.fermionField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.fermionField k) (Oba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.fermionField) (b := x) (c := F.fermionField) Oba Obc m k hn1 hn2

/-- Rigorous free-fermion CFT package:
    normalized vacuum data plus finite-order self-OPE for the fermion field. -/
structure CFTData
    (F : FreeFermionVOA R)
    [VertexAlgebra R F.Carrier] where
  vacuumData : ModeVacuumData R F.Carrier
  vacuum_eq : vacuumData.vacuum = VertexAlgebra.vacuum (R := R)
  ope : OPEFiniteOrder (R := R) (V := F.Carrier) F.fermionField F.fermionField

namespace CFTData

variable (F : FreeFermionVOA R)
variable [VertexAlgebra R F.Carrier]

/-- Vacuum functional extracted from the packaged vacuum data. -/
def vacuumFunctional (D : CFTData (R := R) F) : VacuumFunctional (R := R) F.Carrier :=
  D.vacuumData.toVacuumFunctional D.vacuum_eq

/-- OPE-coefficient two-point correlator value in packaged form. -/
def twoPointCoefficient (D : CFTData (R := R) F)
    (j : Fin D.ope.data.order) (n : ℤ) : R :=
  (vacuumFunctional (R := R) F D).epsilon
    (D.ope.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))

/-- Extended-index two-point coefficient value:
    coefficient below order, zero above order. -/
def twoPointCoefficientOrZero (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) : R :=
  (vacuumFunctional (R := R) F D).epsilon
    ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
      (a := F.fermionField) (b := F.fermionField) D.ope j)
      ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))

/-- The packaged fermionic `twoPointCoefficientOrZero` coincides with the generic
    correlator-level definition. -/
theorem twoPointCoefficientOrZero_eq_generic
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n =
      StringAlgebra.VOA.twoPointCoefficientOrZero (R := R)
        (ω := vacuumFunctional (R := R) F D)
        (a := F.fermionField) (b := F.fermionField) D.ope j n := by
  rfl

/-- Below OPE order, `twoPointCoefficientOrZero` equals the packaged coefficient value. -/
theorem twoPointCoefficientOrZero_eq_twoPointCoefficient_of_lt
    (D : CFTData (R := R) F) {j : ℕ} (hj : j < D.ope.data.order) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n =
      twoPointCoefficient (R := R) F D ⟨j, hj⟩ n := by
  unfold twoPointCoefficientOrZero twoPointCoefficient vacuumFunctional
  simp [OPEFiniteOrder.coefficientOrZero_of_lt
    (R := R) (V := F.Carrier) (a := F.fermionField) (b := F.fermionField) D.ope hj]

/-- At/above OPE order, `twoPointCoefficientOrZero` vanishes. -/
theorem twoPointCoefficientOrZero_eq_zero_of_ge
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n = 0 := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  rw [OPEFiniteOrder.coefficientOrZero_of_ge
    (R := R) (V := F.Carrier) (a := F.fermionField) (b := F.fermionField) D.ope hj]
  change (D.vacuumData.toVacuumFunctional D.vacuum_eq).epsilon
      ((0 : Module.End R F.Carrier) (VertexAlgebra.vacuum (R := R))) = 0
  simp

/-- Piecewise form of the extended-index packaged coefficient value. -/
theorem twoPointCoefficientOrZero_eq_opeCoefficient_or_zero
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n =
      if h : j < D.ope.data.order then
        twoPointCoefficient (R := R) F D ⟨j, h⟩ n
      else 0 := by
  by_cases hlt : j < D.ope.data.order
  · simpa [hlt] using
      twoPointCoefficientOrZero_eq_twoPointCoefficient_of_lt
        (R := R) (F := F) D hlt n
  · have hge : D.ope.data.order ≤ j := Nat.le_of_not_gt hlt
    simpa [hlt] using
      twoPointCoefficientOrZero_eq_zero_of_ge
        (R := R) (F := F) D hge n

/-- Packaged OPE coefficient extraction for `twoPointModes`. -/
theorem twoPointModes_eq_twoPointCoefficient
    (D : CFTData (R := R) F) (j : Fin D.ope.data.order) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField n (j : ℤ) =
      twoPointCoefficient (R := R) F D j n := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointModes_eq_opeCoefficient (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged OPE coefficient extraction in model-level `twoPoint` notation. -/
theorem twoPoint_eq_twoPointCoefficient_leftMode
    (D : CFTData (R := R) F) (j : Fin D.ope.data.order) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      twoPointCoefficient (R := R) F D j n := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeFermionVOA.twoPoint_eq_opeCoefficient_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged high-mode vanishing for `twoPointModes`. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField n (j : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointModes_eq_zero_of_ge_opeOrder (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope (j := j) hj n

/-- Packaged high-mode vanishing in model-level `twoPoint` notation. -/
theorem twoPoint_eq_zero_of_ge_opeOrder_leftMode
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n = 0 := by
  simpa using
    FreeFermionVOA.twoPoint_eq_zero_of_ge_opeOrder_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope (j := j) hj n

/-- Piecewise finite-order OPE extraction for packaged fermionic `twoPointModes`. -/
theorem twoPointModes_eq_opeCoefficient_or_zero
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField n (j : ℤ) =
      if h : j < D.ope.data.order then
        twoPointCoefficient (R := R) F D ⟨j, h⟩ n
      else 0 := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointModes_eq_opeCoefficient_or_zero (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Piecewise finite-order OPE extraction for packaged fermionic model-level `twoPoint`. -/
theorem twoPoint_eq_opeCoefficient_or_zero_leftMode
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      if h : j < D.ope.data.order then
        twoPointCoefficient (R := R) F D ⟨j, h⟩ n
      else 0 := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeFermionVOA.twoPoint_eq_opeCoefficient_or_zero_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged fermionic correlator in extended-coefficient form. -/
theorem twoPointModes_eq_twoPointCoefficientOrZero
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField n (j : ℤ) =
      twoPointCoefficientOrZero (R := R) F D j n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointModes_eq_coefficientOrZero (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged model-level fermionic correlator in extended-coefficient form. -/
theorem twoPoint_eq_twoPointCoefficientOrZero_leftMode
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      twoPointCoefficientOrZero (R := R) F D j n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeFermionVOA.twoPoint_eq_coefficientOrZero_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged fermionic commutator correlator vanishing above OPE order in both indices. -/
theorem twoPointCommutator_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F)
    {m n : ℕ}
    (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointCommutator_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope hm hn

/-- Packaged fermionic anticommutator correlator vanishing above OPE order in both indices. -/
theorem twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F)
    {m n : ℕ}
    (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope hm hn

/-- Packaged fermionic commutator correlator via extended coefficients. -/
theorem twoPointCommutator_eq_twoPointCoefficientOrZero_sub
    (D : CFTData (R := R) F) (m n : ℕ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) F D n m -
        twoPointCoefficientOrZero (R := R) F D m n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa [sub_eq_add_neg] using
    FreeFermionVOA.twoPointCommutator_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope m n

/-- Packaged fermionic anticommutator correlator via extended coefficients. -/
theorem twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
    (D : CFTData (R := R) F) (m n : ℕ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) F D n m +
        twoPointCoefficientOrZero (R := R) F D m n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeFermionVOA.twoPointAnticommutator_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope m n

/-- Packaged fermionic three-point commutator (first two insertions)
    via extended coefficients. -/
theorem threePointCommutator12_eq_coefficientOrZero_sub
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) D.ope n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) D.ope m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator12_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged fermionic three-point anticommutator (first two insertions)
    via extended coefficients. -/
theorem threePointAnticommutator12_eq_coefficientOrZero_add
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) D.ope n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.fermionField) (b := F.fermionField) D.ope m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator12_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged fermionic three-point commutator (first two insertions)
    vanishing above OPE order. -/
theorem threePointCommutator12_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator12_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic three-point anticommutator (first two insertions)
    vanishing above OPE order. -/
theorem threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic three-point commutator (first two insertions) below OPE
    order in both indices, as the difference of coefficient correlators. -/
theorem threePointCommutator12_eq_opeCoefficient_sub_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          ((D.ope.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (D.ope.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator12_eq_opeCoefficient_sub_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic three-point anticommutator (first two insertions) below OPE
    order in both indices, as the sum of coefficient correlators. -/
theorem threePointAnticommutator12_eq_opeCoefficient_add_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          ((D.ope.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (D.ope.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator12_eq_opeCoefficient_add_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic mixed regime (`m` above OPE order, `n` below OPE order):
    three-point commutator (first two insertions) as right-oriented coefficient. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic mixed regime (`m` above OPE order, `n` below OPE order):
    three-point anticommutator (first two insertions) as right-oriented coefficient. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic mixed regime (`m` below OPE order, `n` above OPE order):
    three-point commutator (first two insertions) as negative left coefficient. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      -(vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic mixed regime (`m` below OPE order, `n` above OPE order):
    three-point anticommutator (first two insertions) as left-oriented coefficient. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.fermionField F.fermionField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged fermionic three-point commutator (last two insertions) via extended coefficients. -/
theorem threePointCommutator23_eq_coefficientOrZero_sub
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) D.ope k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) D.ope n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator23_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged fermionic three-point anticommutator (last two insertions) via extended coefficients. -/
theorem threePointAnticommutator23_eq_coefficientOrZero_add
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) D.ope k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.fermionField) (b := F.fermionField) D.ope n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator23_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged fermionic three-point commutator (last two insertions) vanishing above OPE order. -/
theorem threePointCommutator23_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator23_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic three-point anticommutator (last two insertions) vanishing above OPE order. -/
theorem threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic three-point commutator (last two insertions) below OPE order
    in both indices, as a difference of coefficient correlators. -/
theorem threePointCommutator23_eq_opeCoefficient_sub_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        ((D.ope.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          D.ope.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator23_eq_opeCoefficient_sub_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic three-point anticommutator (last two insertions) below OPE order
    in both indices, as a sum of coefficient correlators. -/
theorem threePointAnticommutator23_eq_opeCoefficient_add_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        ((D.ope.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          D.ope.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator23_eq_opeCoefficient_add_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic mixed regime (`n` above OPE order, `k` below OPE order):
    three-point commutator (last two insertions) as `k`-oriented coefficient. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic mixed regime (`n` above OPE order, `k` below OPE order):
    three-point anticommutator (last two insertions) as `k`-oriented coefficient. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic mixed regime (`n` below OPE order, `k` above OPE order):
    three-point commutator (last two insertions) as negative `n`-coefficient. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      -(vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged fermionic mixed regime (`n` below OPE order, `k` above OPE order):
    three-point anticommutator (last two insertions) as `n`-oriented coefficient. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.fermionField F.fermionField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeFermionVOA.threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

end CFTData

end FreeFermionVOA


end StringAlgebra.VOA
