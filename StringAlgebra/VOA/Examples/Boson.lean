/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Virasoro
import StringAlgebra.VOA.Modules
import StringAlgebra.VOA.SuperFormalDistributions
import StringAlgebra.VOA.Correlators

/-!
# Examples of Vertex Operator Algebras

This file provides concrete constructions of important VOAs.

## Main Definitions

* `HeisenbergVOA` - The free boson VOA (Fock space)
* `AffineVOA` - VOA from affine Lie algebras at level k
* `LatticeVOA` - VOA from an even lattice
* `VirasoroVOA` - The Virasoro VOA (vacuum module)

## References

* Frenkel, Ben-Zvi, "Vertex Algebras and Algebraic Curves"
* Kac, "Vertex Algebras for Beginners"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## The Heisenberg VOA (Free Boson)

The Heisenberg VOA is the simplest non-trivial example.
It is built from a 1-dimensional abelian Lie algebra h with basis α,
and its affinization ĥ = h[t, t⁻¹] ⊕ ℂK.
-/

/-- The Heisenberg algebra: [α_m, α_n] = m δ_{m,-n} K -/
structure HeisenbergAlgebra (R : Type*) [CommRing R] where
  /-- The normalization (usually 1) -/
  normalization : R

namespace HeisenbergAlgebra

variable {R : Type*} [CommRing R]

/-- The commutation relation [α_m, α_n] = m δ_{m,-n} -/
def commutator (heis : HeisenbergAlgebra R) (m n : ℤ) : R :=
  if m + n = 0 then heis.normalization * m else 0

end HeisenbergAlgebra

/-- The Heisenberg VOA (Fock space) over R. -/
structure HeisenbergVOA (R : Type*) [CommRing R] where
  /-- The Heisenberg algebra -/
  heis : HeisenbergAlgebra R

namespace HeisenbergVOA

variable {R : Type*} [CommRing R]

end HeisenbergVOA

/-- Endomorphism commutator `[f,g] = fg - gf`. -/
def endComm
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    (f g : Module.End R V) : Module.End R V :=
  f * g - g * f

@[simp] theorem endComm_apply
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    (f g : Module.End R V) (v : V) :
    endComm f g v = f (g v) - g (f v) := by
  simp [endComm, Module.End.mul_apply]

/-- A normalized vacuum expectation package for mode-correlator calculations. -/
structure ModeVacuumData
    (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] where
  /-- Distinguished vacuum vector. -/
  vacuum : V
  /-- Linear vacuum expectation functional. -/
  epsilon : V →ₗ[R] R
  /-- Normalization `⟨0|0⟩ = 1`. -/
  vacuum_norm : epsilon vacuum = 1

namespace ModeVacuumData

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

@[simp] theorem epsilon_vacuum (ω : ModeVacuumData R V) :
    ω.epsilon ω.vacuum = 1 :=
  ω.vacuum_norm

variable [VertexAlgebra R V]

/-- Convert mode-level vacuum data to the correlator vacuum functional,
    provided the chosen vacuum is the VOA vacuum. -/
def toVacuumFunctional
    (ω : ModeVacuumData R V)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R)) :
    VacuumFunctional (R := R) V where
  epsilon := ω.epsilon
  vacuum_norm := by simpa [hVac] using ω.vacuum_norm

@[simp] theorem toVacuumFunctional_epsilon
    (ω : ModeVacuumData R V)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R)) (v : V) :
    (ω.toVacuumFunctional hVac).epsilon v = ω.epsilon v := rfl

end ModeVacuumData

/-- A Heisenberg mode family acting on a module. -/
structure HeisenbergModeFamily
    (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] where
  /-- Bosonic modes `α_n`. -/
  alpha : ℤ → Module.End R V
  /-- Normalization constant in `[α_m, α_n]`. -/
  normalization : R := 1
  /-- Heisenberg commutator relation. -/
  commutator_spec :
    ∀ m n : ℤ,
      endComm (alpha m) (alpha n) =
        if m + n = 0 then (normalization * (m : R)) • (LinearMap.id : Module.End R V) else 0

namespace HeisenbergModeFamily

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

theorem commutator_offdiag
    (H : HeisenbergModeFamily R V) {m n : ℤ} (h : m + n ≠ 0) :
    endComm (H.alpha m) (H.alpha n) = 0 := by
  simp [H.commutator_spec, h]

theorem commutator_diag
    (H : HeisenbergModeFamily R V) (m : ℤ) :
    endComm (H.alpha m) (H.alpha (-m)) =
      (H.normalization * (m : R)) • (LinearMap.id : Module.End R V) := by
  simp [H.commutator_spec]

/-- Above total mode index `1`, Heisenberg modes commute on vectors. -/
theorem eventual_commutator_zero
    (H : HeisenbergModeFamily R V) :
    ∀ v : V, ∀ m n : ℤ, m + n ≥ 1 →
      (H.alpha m) ((H.alpha n) v) - (H.alpha n) ((H.alpha m) v) = 0 := by
  intro v m n hmn
  have hne : m + n ≠ 0 := by omega
  have hcomm : endComm (H.alpha m) (H.alpha n) = 0 :=
    H.commutator_offdiag (m := m) (n := n) hne
  have happly : (endComm (H.alpha m) (H.alpha n)) v = 0 := by
    simpa using congrArg (fun T : Module.End R V => T v) hcomm
  simpa [endComm, Module.End.mul_apply] using happly

/-- Algebraic two-point function from Heisenberg modes and a vacuum package. -/
def twoPoint (H : HeisenbergModeFamily R V) (ω : ModeVacuumData R V) (m n : ℤ) : R :=
  ω.epsilon ((H.alpha m) ((H.alpha n) ω.vacuum))

/-- Heisenberg commutator gives the two-point commutator identity. -/
theorem twoPoint_commutator
    (H : HeisenbergModeFamily R V) (ω : ModeVacuumData R V) (m n : ℤ) :
    twoPoint H ω m n - twoPoint H ω n m =
      if m + n = 0 then H.normalization * (m : R) else 0 := by
  have hcomm := H.commutator_spec m n
  have happly :
      ω.epsilon ((endComm (H.alpha m) (H.alpha n)) ω.vacuum) =
        ω.epsilon ((if m + n = 0
          then (H.normalization * (m : R)) • (LinearMap.id : Module.End R V)
          else 0) ω.vacuum) := by
    simpa using congrArg (fun T : Module.End R V => ω.epsilon (T ω.vacuum)) hcomm
  calc
    twoPoint H ω m n - twoPoint H ω n m
        = ω.epsilon ((endComm (H.alpha m) (H.alpha n)) ω.vacuum) := by
          simp [twoPoint, endComm, Module.End.mul_apply, map_sub]
    _ = ω.epsilon ((if m + n = 0
          then (H.normalization * (m : R)) • (LinearMap.id : Module.End R V)
          else 0) ω.vacuum) := happly
    _ = if m + n = 0 then H.normalization * (m : R) else 0 := by
          by_cases h : m + n = 0 <;> simp [h, ω.vacuum_norm]

/-- Off-diagonal two-point commutator vanishes when `m + n ≠ 0`. -/
theorem twoPoint_commutator_offdiag
    (H : HeisenbergModeFamily R V) (ω : ModeVacuumData R V)
    {m n : ℤ} (h : m + n ≠ 0) :
    twoPoint H ω m n - twoPoint H ω n m = 0 := by
  simp [twoPoint_commutator (H := H) (ω := ω), h]

end HeisenbergModeFamily

/-- Algebraic free-boson data from a Heisenberg mode realization. -/
structure FreeBosonVOA (R : Type*) [CommRing R] where
  /-- State-space carrier. -/
  Carrier : Type*
  [addCommGroup : AddCommGroup Carrier]
  [module : Module R Carrier]
  /-- Heisenberg modes on the carrier. -/
  modes : HeisenbergModeFamily R Carrier

attribute [instance] FreeBosonVOA.addCommGroup FreeBosonVOA.module

namespace FreeBosonVOA

variable {R : Type*} [CommRing R]

/-- The bosonic field extracted from Heisenberg modes. -/
def bosonField (F : FreeBosonVOA R) : FormalDistribution R F.Carrier :=
  F.modes.alpha

/-- Two-point bosonic mode correlator in a chosen vacuum package. -/
def twoPoint (F : FreeBosonVOA R) (ω : ModeVacuumData R F.Carrier) (m n : ℤ) : R :=
  HeisenbergModeFamily.twoPoint (R := R) (V := F.Carrier) F.modes ω m n

/-- The bosonic mode correlator matches `twoPointModes` with reversed mode-index order. -/
theorem twoPoint_eq_twoPointModes_swapped
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
  (m n : ℤ) :
  F.twoPoint ω m n =
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m := by
  simp [twoPoint, bosonField, HeisenbergModeFamily.twoPoint,
    ModeVacuumData.toVacuumFunctional, hVac]

/-- Eventual bosonic mode commutativity from Heisenberg commutators. -/
theorem boson_modes_eventually_commute (F : FreeBosonVOA R) :
    ∀ v : F.Carrier, ∀ m n : ℤ, m + n ≥ 1 →
      (F.bosonField m) ((F.bosonField n) v) - (F.bosonField n) ((F.bosonField m) v) = 0 := by
  simpa [bosonField] using
    HeisenbergModeFamily.eventual_commutator_zero (R := R) (V := F.Carrier) F.modes

/-- Two-point bosonic commutator identity from Heisenberg relations. -/
theorem twoPoint_commutator
    (F : FreeBosonVOA R) (ω : ModeVacuumData R F.Carrier) (m n : ℤ) :
    F.twoPoint ω m n - F.twoPoint ω n m =
      if m + n = 0 then F.modes.normalization * (m : R) else 0 := by
  simpa [twoPoint] using
    HeisenbergModeFamily.twoPoint_commutator
      (R := R) (V := F.Carrier) F.modes ω m n

/-- Off-diagonal bosonic two-point commutator vanishes. -/
theorem twoPoint_commutator_offdiag
    (F : FreeBosonVOA R) (ω : ModeVacuumData R F.Carrier)
    {m n : ℤ} (h : m + n ≠ 0) :
    F.twoPoint ω m n - F.twoPoint ω n m = 0 := by
  simp [twoPoint_commutator (F := F) (ω := ω), h]

/-- Diagonal bosonic two-point commutator specialization. -/
theorem twoPoint_commutator_diag
    (F : FreeBosonVOA R) (ω : ModeVacuumData R F.Carrier) (m : ℤ) :
    F.twoPoint ω m (-m) - F.twoPoint ω (-m) m =
      F.modes.normalization * (m : R) := by
  simp [twoPoint_commutator (F := F) (ω := ω) (m := m) (n := -m)]

/-- Correlator-form bosonic commutator identity in the `twoPointModes` API. -/
theorem twoPointModes_commutator
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m -
      twoPointModes (R := R) (ω.toVacuumFunctional hVac)
        F.bosonField F.bosonField m n =
      if m + n = 0 then F.modes.normalization * (m : R) else 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)] using
    F.twoPoint_commutator ω m n

/-- Correlator-form bosonic commutator identity via `twoPointCommutator`. -/
theorem twoPointCommutator_primitive
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m =
      if m + n = 0 then F.modes.normalization * (m : R) else 0 := by
  simpa [StringAlgebra.VOA.twoPointCommutator] using
    F.twoPointModes_commutator (ω := ω) (hVac := hVac) m n

/-- Primitive bosonic commutator in explicit `nthProduct`-difference form. -/
theorem twoPointCommutator_primitive_eq_nthProduct_sub
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m =
      (ω.toVacuumFunctional hVac).epsilon
        (((nthProduct R F.Carrier F.bosonField F.bosonField m -
          nthProduct R F.Carrier F.bosonField F.bosonField n) (m + n))
          (VertexAlgebra.vacuum (R := R))) := by
  simpa [add_comm] using
    twoPointCommutator_eq_nthProduct_sub (R := R) (ω := ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m

/-- Heisenberg two-point commutator identity in explicit `nthProduct`-difference form. -/
theorem twoPoint_nthProduct_sub_evaluation
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m n : ℤ) :
    (ω.toVacuumFunctional hVac).epsilon
      (((nthProduct R F.Carrier F.bosonField F.bosonField m -
        nthProduct R F.Carrier F.bosonField F.bosonField n) (m + n))
        (VertexAlgebra.vacuum (R := R))) =
      if m + n = 0 then F.modes.normalization * (m : R) else 0 := by
  calc
    (ω.toVacuumFunctional hVac).epsilon
      (((nthProduct R F.Carrier F.bosonField F.bosonField m -
        nthProduct R F.Carrier F.bosonField F.bosonField n) (m + n))
        (VertexAlgebra.vacuum (R := R))) =
      StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
        F.bosonField F.bosonField n m := by
          symm
          exact twoPointCommutator_primitive_eq_nthProduct_sub
            (F := F) (ω := ω) (hVac := hVac) m n
    _ = if m + n = 0 then F.modes.normalization * (m : R) else 0 :=
      twoPointCommutator_primitive (F := F) (ω := ω) (hVac := hVac) m n

/-- Off-diagonal bosonic correlator commutator vanishing in primitive form. -/
theorem twoPointCommutator_primitive_offdiag
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    {m n : ℤ} (h : m + n ≠ 0) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n m = 0 := by
  have hmain := twoPointCommutator_primitive (F := F) (ω := ω) (hVac := hVac) m n
  simpa [h] using hmain

/-- Diagonal bosonic correlator commutator specialization in primitive form. -/
theorem twoPointCommutator_primitive_diag
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (m : ℤ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField (-m) m =
      F.modes.normalization * (m : R) := by
  have hmain := twoPointCommutator_primitive (F := F) (ω := ω) (hVac := hVac) m (-m)
  simpa using hmain

/-- OPE coefficient extraction for bosonic two-point mode correlators. -/
theorem twoPointModes_eq_opeCoefficient
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : Fin O.data.order) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n (j : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  exact StringAlgebra.VOA.twoPointModes_eq_opeCoefficient
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O j n

/-- Bosonic two-point mode correlators vanish above the OPE singular order. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    {j : ℕ} (hj : O.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n (j : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointModes_eq_zero_of_ge_opeOrder
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O (j := j) hj n

/-- OPE coefficient extraction in model-level bosonic two-point notation. -/
theorem twoPoint_eq_opeCoefficient_leftMode
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : Fin O.data.order) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients j ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_opeCoefficient (F := F) (ω := ω) (hVac := hVac) O j n

/-- Model-level bosonic two-point correlators vanish above the OPE singular order. -/
theorem twoPoint_eq_zero_of_ge_opeOrder_leftMode
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    {j : ℕ} (hj : O.data.order ≤ j) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n = 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_zero_of_ge_opeOrder (F := F) (ω := ω) (hVac := hVac)
      O (j := j) hj n

/-- Piecewise finite-order OPE extraction for bosonic `twoPointModes`. -/
theorem twoPointModes_eq_opeCoefficient_or_zero
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n (j : ℤ) =
      if h : j < O.data.order then
        (ω.toVacuumFunctional hVac).epsilon
          (O.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  exact StringAlgebra.VOA.twoPointModes_eq_opeCoefficient_or_zero
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O j n

/-- Piecewise finite-order OPE extraction in bosonic model-level `twoPoint` notation. -/
theorem twoPoint_eq_opeCoefficient_or_zero_leftMode
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : ℕ) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      if h : j < O.data.order then
        (ω.toVacuumFunctional hVac).epsilon
          (O.data.coefficients ⟨j, h⟩ ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))
      else 0 := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_opeCoefficient_or_zero (F := F) (ω := ω) (hVac := hVac) O j n

/-- Bosonic correlator in terms of the extended coefficient field `coefficientOrZero`. -/
theorem twoPointModes_eq_coefficientOrZero
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField n (j : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
          (a := F.bosonField) (b := F.bosonField) O j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  exact StringAlgebra.VOA.twoPointModes_eq_coefficientOrZero
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O j n

/-- Model-level bosonic correlator in extended-coefficient form. -/
theorem twoPoint_eq_coefficientOrZero_leftMode
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (j : ℕ) (n : ℤ) :
    F.twoPoint ω (j : ℤ) n =
      (ω.toVacuumFunctional hVac).epsilon
        ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
          (a := F.bosonField) (b := F.bosonField) O j)
          ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R))) := by
  simpa [twoPoint_eq_twoPointModes_swapped (F := F) (ω := ω) (hVac := hVac)
    (m := (j : ℤ)) (n := n)] using
    twoPointModes_eq_coefficientOrZero (F := F) (ω := ω) (hVac := hVac) O j n

/-- Above OPE order in both mode indices, bosonic two-point commutator correlator vanishes. -/
theorem twoPointCommutator_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointCommutator_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O O hm hn

/-- Above OPE order in both mode indices, bosonic two-point anticommutator correlator vanishes. -/
theorem twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) = 0 := by
  exact StringAlgebra.VOA.twoPointAnticommutator_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) O O hm hn

/-- Bosonic commutator correlator via extended coefficients in both OPE orientations. -/
theorem twoPointCommutator_eq_coefficientOrZero_sub
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (m n : ℕ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.twoPointCommutator_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) O O m n

/-- Bosonic anticommutator correlator via extended coefficients in both OPE orientations. -/
theorem twoPointAnticommutator_eq_coefficientOrZero_add
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (m n : ℕ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O n)
            ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O m)
            ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.twoPointAnticommutator_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) O O m n

/-- Bosonic three-point commutator (first two insertions) via extended coefficients. -/
theorem threePointCommutator12_eq_coefficientOrZero_sub
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) O n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) O m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O m n k

/-- Bosonic three-point anticommutator (first two insertions) via extended coefficients. -/
theorem threePointAnticommutator12_eq_coefficientOrZero_add
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) O n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) O m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O m n k

/-- Above OPE order in both indices, bosonic three-point commutator (first two insertions)
    vanishes. -/
theorem threePointCommutator12_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointCommutator12_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Above OPE order in both indices, bosonic three-point anticommutator (first two
    insertions) vanishes. -/
theorem threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator12_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Below OPE order in both mode indices, bosonic three-point commutator
    (first two insertions) is the difference of OPE coefficient correlators. -/
theorem threePointCommutator12_eq_opeCoefficient_sub_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          ((O.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (O.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Below OPE order in both mode indices, bosonic three-point anticommutator
    (first two insertions) is the sum of OPE coefficient correlators. -/
theorem threePointAnticommutator12_eq_opeCoefficient_add_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k)
          ((O.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (O.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Mixed regime (`m` above OPE order, `n` below OPE order):
    bosonic three-point commutator (first two insertions) reduces to the
    right-oriented OPE coefficient correlator. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Mixed regime (`m` above OPE order, `n` below OPE order):
    bosonic three-point anticommutator (first two insertions) reduces to the
    right-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : O.data.order ≤ m) (hn : n < O.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Mixed regime (`m` below OPE order, `n` above OPE order):
    bosonic three-point commutator (first two insertions) is minus the
    left-oriented OPE coefficient correlator. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      -(ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Mixed regime (`m` below OPE order, `n` above OPE order):
    bosonic three-point anticommutator (first two insertions) reduces to the
    left-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) {m n : ℕ}
    (hm : m < O.data.order) (hn : O.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((x k) (O.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := F.bosonField) (c := x) O O hm hn k

/-- Bosonic three-point commutator (last two insertions) via extended coefficients. -/
theorem threePointCommutator23_eq_coefficientOrZero_sub
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m n k

/-- Bosonic three-point anticommutator (last two insertions) via extended coefficients. -/
theorem threePointAnticommutator23_eq_coefficientOrZero_add
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) O n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m n k

/-- Above OPE order in both indices, bosonic three-point commutator (last two
    insertions) vanishes. -/
theorem threePointCommutator23_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) = 0 := by
  exact StringAlgebra.VOA.threePointCommutator23_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Above OPE order in both indices, bosonic three-point anticommutator (last two
    insertions) vanishes. -/
theorem threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator23_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Below OPE order in both mode indices, bosonic three-point commutator (last two
    insertions) is the difference of OPE coefficient correlators. -/
theorem threePointCommutator23_eq_opeCoefficient_sub_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((O.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          O.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Below OPE order in both mode indices, bosonic three-point anticommutator (last two
    insertions) is the sum of OPE coefficient correlators. -/
theorem threePointAnticommutator23_eq_opeCoefficient_add_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        ((O.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          O.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Mixed regime (`n` above OPE order, `k` below OPE order):
    bosonic three-point commutator (last two insertions) reduces to the
    `k`-oriented OPE coefficient correlator. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Mixed regime (`n` above OPE order, `k` below OPE order):
    bosonic three-point anticommutator (last two insertions) reduces to the
    `k`-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : O.data.order ≤ n) (hk : k < O.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Mixed regime (`n` below OPE order, `k` above OPE order):
    bosonic three-point commutator (last two insertions) is minus the
    `n`-oriented OPE coefficient correlator. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      -(ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Mixed regime (`n` below OPE order, `k` above OPE order):
    bosonic three-point anticommutator (last two insertions) reduces to the
    `n`-oriented OPE coefficient correlator. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (O : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField)
    (x : FormalDistribution R F.Carrier) (m : ℤ) {n k : ℕ}
    (hn : n < O.data.order) (hk : O.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (ω.toVacuumFunctional hVac)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (ω.toVacuumFunctional hVac).epsilon
        (O.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := x) (b := F.bosonField) (c := F.bosonField) O O m hn hk

/-- Bosonic three-point commutator (first and third insertions) via extended coefficients,
    with explicit OPE data for the middle-to-first and middle-to-third channels. -/
theorem threePointCommutator13_eq_coefficientOrZero_sub
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.bosonField k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.bosonField) Oba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (F.bosonField m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.bosonField) Obc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_coefficientOrZero_sub
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m n k

/-- Bosonic three-point anticommutator (first and third insertions) via extended coefficients,
    with explicit OPE data for the middle-to-first and middle-to-third channels. -/
theorem threePointAnticommutator13_eq_coefficientOrZero_add
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m : ℤ) (n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.bosonField k)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.bosonField) Oba n)
              ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (F.bosonField m)
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := x) (b := F.bosonField) Obc n)
              ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_coefficientOrZero_add
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m n k

/-- High-middle-mode vanishing for bosonic first/third three-point commutator,
    with explicit middle-channel OPE assumptions. -/
theorem threePointCommutator13_eq_zero_of_ge_opeOrders
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointCommutator13_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- High-middle-mode vanishing for bosonic first/third three-point anticommutator,
    with explicit middle-channel OPE assumptions. -/
theorem threePointAnticommutator13_eq_zero_of_ge_opeOrders
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k = 0 := by
  exact StringAlgebra.VOA.threePointAnticommutator13_eq_zero_of_ge_opeOrders
    (R := R) (ω := ω.toVacuumFunctional hVac)
    (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Strict-below-order extraction for bosonic first/third three-point commutator. -/
theorem threePointCommutator13_eq_opeCoefficient_sub_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.bosonField k)
            (Oba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) -
          (F.bosonField m)
            (Obc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_opeCoefficient_sub_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Strict-below-order extraction for bosonic first/third three-point anticommutator. -/
theorem threePointAnticommutator13_eq_opeCoefficient_add_of_lt
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        (((F.bosonField k)
            (Oba.data.coefficients ⟨n, hn1⟩ ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R))) +
          (F.bosonField m)
            (Obc.data.coefficients ⟨n, hn2⟩ ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R))))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_add_of_lt
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` at/above order, `(b,c)` below order) for bosonic
    first/third commutator extraction. -/
theorem threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      -(ω.toVacuumFunctional hVac).epsilon
        ((F.bosonField m) (Obc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_neg_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` at/above order, `(b,c)` below order) for bosonic
    first/third anticommutator extraction. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : Oba.data.order ≤ n) (hn2 : n < Obc.data.order) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.bosonField m) (Obc.data.coefficients ⟨n, hn2⟩
          ((n : ℤ) + k) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_of_ge_ba_lt_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` below order, `(b,c)` at/above order) for bosonic
    first/third commutator extraction. -/
theorem threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointCommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.bosonField k) (Oba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointCommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Mixed regime (`(b,a)` below order, `(b,c)` at/above order) for bosonic
    first/third anticommutator extraction. -/
theorem threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier]
    (ω : ModeVacuumData R F.Carrier)
    (hVac : ω.vacuum = VertexAlgebra.vacuum (R := R))
    (x : FormalDistribution R F.Carrier)
    (Oba : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (Obc : OPEFiniteOrder (R := R) (V := F.Carrier) x F.bosonField)
    (m k : ℤ) {n : ℕ}
    (hn1 : n < Oba.data.order) (hn2 : Obc.data.order ≤ n) :
    StringAlgebra.VOA.threePointAnticommutator13 (R := R) (ω.toVacuumFunctional hVac)
      F.bosonField x F.bosonField m (n : ℤ) k =
      (ω.toVacuumFunctional hVac).epsilon
        ((F.bosonField k) (Oba.data.coefficients ⟨n, hn1⟩
          ((n : ℤ) + m) (VertexAlgebra.vacuum (R := R)))) := by
  simpa using
    StringAlgebra.VOA.threePointAnticommutator13_eq_opeCoefficient_of_lt_ba_ge_bc
      (R := R) (ω := ω.toVacuumFunctional hVac)
      (a := F.bosonField) (b := x) (c := F.bosonField) Oba Obc m k hn1 hn2

/-- Rigorous free-boson CFT package:
    normalized vacuum data plus finite-order self-OPE for the boson field. -/
structure CFTData
    (F : FreeBosonVOA R)
    [VertexAlgebra R F.Carrier] where
  vacuumData : ModeVacuumData R F.Carrier
  vacuum_eq : vacuumData.vacuum = VertexAlgebra.vacuum (R := R)
  ope : OPEFiniteOrder (R := R) (V := F.Carrier) F.bosonField F.bosonField

namespace CFTData

variable (F : FreeBosonVOA R)
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
      (a := F.bosonField) (b := F.bosonField) D.ope j)
      ((j : ℤ) + n) (VertexAlgebra.vacuum (R := R)))

/-- The packaged bosonic `twoPointCoefficientOrZero` coincides with the generic
    correlator-level definition. -/
theorem twoPointCoefficientOrZero_eq_generic
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n =
      StringAlgebra.VOA.twoPointCoefficientOrZero (R := R)
        (ω := vacuumFunctional (R := R) F D)
        (a := F.bosonField) (b := F.bosonField) D.ope j n := by
  rfl

/-- Below OPE order, `twoPointCoefficientOrZero` equals the packaged coefficient value. -/
theorem twoPointCoefficientOrZero_eq_twoPointCoefficient_of_lt
    (D : CFTData (R := R) F) {j : ℕ} (hj : j < D.ope.data.order) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n =
      twoPointCoefficient (R := R) F D ⟨j, hj⟩ n := by
  unfold twoPointCoefficientOrZero twoPointCoefficient vacuumFunctional
  simp [OPEFiniteOrder.coefficientOrZero_of_lt
    (R := R) (V := F.Carrier) (a := F.bosonField) (b := F.bosonField) D.ope hj]

/-- At/above OPE order, `twoPointCoefficientOrZero` vanishes. -/
theorem twoPointCoefficientOrZero_eq_zero_of_ge
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    twoPointCoefficientOrZero (R := R) F D j n = 0 := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  rw [OPEFiniteOrder.coefficientOrZero_of_ge
    (R := R) (V := F.Carrier) (a := F.bosonField) (b := F.bosonField) D.ope hj]
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
      F.bosonField F.bosonField n (j : ℤ) =
      twoPointCoefficient (R := R) F D j n := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointModes_eq_opeCoefficient (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged OPE coefficient extraction in model-level `twoPoint` notation. -/
theorem twoPoint_eq_twoPointCoefficient_leftMode
    (D : CFTData (R := R) F) (j : Fin D.ope.data.order) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      twoPointCoefficient (R := R) F D j n := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeBosonVOA.twoPoint_eq_opeCoefficient_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged high-mode vanishing for `twoPointModes`. -/
theorem twoPointModes_eq_zero_of_ge_opeOrder
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField n (j : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointModes_eq_zero_of_ge_opeOrder (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope (j := j) hj n

/-- Packaged high-mode vanishing in model-level `twoPoint` notation. -/
theorem twoPoint_eq_zero_of_ge_opeOrder_leftMode
    (D : CFTData (R := R) F) {j : ℕ} (hj : D.ope.data.order ≤ j) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n = 0 := by
  simpa using
    FreeBosonVOA.twoPoint_eq_zero_of_ge_opeOrder_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope (j := j) hj n

/-- Piecewise finite-order OPE extraction for packaged bosonic `twoPointModes`. -/
theorem twoPointModes_eq_opeCoefficient_or_zero
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField n (j : ℤ) =
      if h : j < D.ope.data.order then
        twoPointCoefficient (R := R) F D ⟨j, h⟩ n
      else 0 := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointModes_eq_opeCoefficient_or_zero (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Piecewise finite-order OPE extraction for packaged bosonic model-level `twoPoint`. -/
theorem twoPoint_eq_opeCoefficient_or_zero_leftMode
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      if h : j < D.ope.data.order then
        twoPointCoefficient (R := R) F D ⟨j, h⟩ n
      else 0 := by
  unfold twoPointCoefficient vacuumFunctional
  simpa using
    FreeBosonVOA.twoPoint_eq_opeCoefficient_or_zero_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged bosonic correlator in extended-coefficient form. -/
theorem twoPointModes_eq_twoPointCoefficientOrZero
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    twoPointModes (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField n (j : ℤ) =
      twoPointCoefficientOrZero (R := R) F D j n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointModes_eq_coefficientOrZero (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged model-level bosonic correlator in extended-coefficient form. -/
theorem twoPoint_eq_twoPointCoefficientOrZero_leftMode
    (D : CFTData (R := R) F) (j : ℕ) (n : ℤ) :
    F.twoPoint D.vacuumData (j : ℤ) n =
      twoPointCoefficientOrZero (R := R) F D j n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeBosonVOA.twoPoint_eq_coefficientOrZero_leftMode (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope j n

/-- Packaged bosonic commutator correlator vanishing above OPE order in both indices. -/
theorem twoPointCommutator_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F)
    {m n : ℕ}
    (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointCommutator_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope hm hn

/-- Packaged bosonic anticommutator correlator vanishing above OPE order in both indices. -/
theorem twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F)
    {m n : ℕ}
    (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointAnticommutator_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope hm hn

/-- Packaged bosonic commutator correlator via extended coefficients. -/
theorem twoPointCommutator_eq_twoPointCoefficientOrZero_sub
    (D : CFTData (R := R) F) (m n : ℕ) :
    StringAlgebra.VOA.twoPointCommutator (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) F D n m -
        twoPointCoefficientOrZero (R := R) F D m n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa [sub_eq_add_neg] using
    FreeBosonVOA.twoPointCommutator_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope m n

/-- Packaged bosonic anticommutator correlator via extended coefficients. -/
theorem twoPointAnticommutator_eq_twoPointCoefficientOrZero_add
    (D : CFTData (R := R) F) (m n : ℕ) :
    StringAlgebra.VOA.twoPointAnticommutator (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField (m : ℤ) (n : ℤ) =
      twoPointCoefficientOrZero (R := R) F D n m +
        twoPointCoefficientOrZero (R := R) F D m n := by
  unfold twoPointCoefficientOrZero vacuumFunctional
  simpa using
    FreeBosonVOA.twoPointAnticommutator_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope m n

/-- Packaged bosonic three-point commutator (first two insertions) via extended coefficients. -/
theorem threePointCommutator12_eq_coefficientOrZero_sub
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) D.ope n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) D.ope m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator12_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged bosonic three-point anticommutator (first two insertions)
    via extended coefficients. -/
theorem threePointAnticommutator12_eq_coefficientOrZero_add
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier) (m n : ℕ) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) D.ope n)
              ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
              (a := F.bosonField) (b := F.bosonField) D.ope m)
              ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator12_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged bosonic three-point commutator (first two insertions) vanishing above OPE order. -/
theorem threePointCommutator12_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator12_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic three-point anticommutator (first two insertions)
    vanishing above OPE order. -/
theorem threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator12_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic three-point commutator (first two insertions) below OPE
    order in both indices, as the difference of coefficient correlators. -/
theorem threePointCommutator12_eq_opeCoefficient_sub_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          ((D.ope.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) -
            (D.ope.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator12_eq_opeCoefficient_sub_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic three-point anticommutator (first two insertions) below OPE
    order in both indices, as the sum of coefficient correlators. -/
theorem threePointAnticommutator12_eq_opeCoefficient_add_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k)
          ((D.ope.data.coefficients ⟨n, hn⟩ ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R))) +
            (D.ope.data.coefficients ⟨m, hm⟩ ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator12_eq_opeCoefficient_add_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic mixed regime (`m` above OPE order, `n` below OPE order):
    three-point commutator (first two insertions) as right-oriented coefficient. -/
theorem threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator12_eq_opeCoefficient_of_ge_left_lt_right (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic mixed regime (`m` above OPE order, `n` below OPE order):
    three-point anticommutator (first two insertions) as right-oriented coefficient. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : D.ope.data.order ≤ m) (hn : n < D.ope.data.order) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (m : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator12_eq_opeCoefficient_of_ge_left_lt_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic mixed regime (`m` below OPE order, `n` above OPE order):
    three-point commutator (first two insertions) as negative left coefficient. -/
theorem threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointCommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      -(vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator12_eq_neg_opeCoefficient_of_lt_left_ge_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic mixed regime (`m` below OPE order, `n` above OPE order):
    three-point anticommutator (first two insertions) as left-oriented coefficient. -/
theorem threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    {m n : ℕ} (hm : m < D.ope.data.order) (hn : D.ope.data.order ≤ n) (k : ℤ) :
    StringAlgebra.VOA.threePointAnticommutator12 (R := R) (vacuumFunctional (R := R) F D)
      F.bosonField F.bosonField x (m : ℤ) (n : ℤ) k =
      (vacuumFunctional (R := R) F D).epsilon
        ((x k) (D.ope.data.coefficients ⟨m, hm⟩
          ((m : ℤ) + (n : ℤ)) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator12_eq_opeCoefficient_of_lt_left_ge_right
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x hm hn k

/-- Packaged bosonic three-point commutator (last two insertions) via extended coefficients. -/
theorem threePointCommutator23_eq_coefficientOrZero_sub
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) D.ope k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) D.ope n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator23_eq_coefficientOrZero_sub (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged bosonic three-point anticommutator (last two insertions) via extended coefficients. -/
theorem threePointAnticommutator23_eq_coefficientOrZero_add
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) (n k : ℕ) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) D.ope k)
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          ((OPEFiniteOrder.coefficientOrZero (R := R) (V := F.Carrier)
            (a := F.bosonField) (b := F.bosonField) D.ope n)
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator23_eq_coefficientOrZero_add (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m n k

/-- Packaged bosonic three-point commutator (last two insertions) vanishing above OPE order. -/
theorem threePointCommutator23_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator23_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic three-point anticommutator (last two insertions) vanishing above OPE order. -/
theorem threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) = 0 := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator23_eq_zero_of_ge_opeOrder_pair (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic three-point commutator (last two insertions) below OPE order
    in both indices, as a difference of coefficient correlators. -/
theorem threePointCommutator23_eq_opeCoefficient_sub_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        ((D.ope.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) -
          D.ope.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator23_eq_opeCoefficient_sub_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic three-point anticommutator (last two insertions) below OPE order
    in both indices, as a sum of coefficient correlators. -/
theorem threePointAnticommutator23_eq_opeCoefficient_add_of_lt
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        ((D.ope.data.coefficients ⟨k, hk⟩
            ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))) +
          D.ope.data.coefficients ⟨n, hn⟩
            ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R))))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator23_eq_opeCoefficient_add_of_lt (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic mixed regime (`n` above OPE order, `k` below OPE order):
    three-point commutator (last two insertions) as `k`-oriented coefficient. -/
theorem threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator23_eq_opeCoefficient_of_ge_n_lt_k (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic mixed regime (`n` above OPE order, `k` below OPE order):
    three-point anticommutator (last two insertions) as `k`-oriented coefficient. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : D.ope.data.order ≤ n) (hk : k < D.ope.data.order) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨k, hk⟩
          ((k : ℤ) + (n : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator23_eq_opeCoefficient_of_ge_n_lt_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic mixed regime (`n` below OPE order, `k` above OPE order):
    three-point commutator (last two insertions) as negative `n`-coefficient. -/
theorem threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointCommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      -(vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointCommutator23_eq_neg_opeCoefficient_of_lt_n_ge_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

/-- Packaged bosonic mixed regime (`n` below OPE order, `k` above OPE order):
    three-point anticommutator (last two insertions) as `n`-oriented coefficient. -/
theorem threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
    (D : CFTData (R := R) F) (x : FormalDistribution R F.Carrier)
    (m : ℤ) {n k : ℕ} (hn : n < D.ope.data.order) (hk : D.ope.data.order ≤ k) :
    StringAlgebra.VOA.threePointAnticommutator23 (R := R) (vacuumFunctional (R := R) F D)
      x F.bosonField F.bosonField m (n : ℤ) (k : ℤ) =
      (vacuumFunctional (R := R) F D).epsilon
        (D.ope.data.coefficients ⟨n, hn⟩
          ((n : ℤ) + (k : ℤ)) ((x m) (VertexAlgebra.vacuum (R := R)))) := by
  unfold vacuumFunctional
  simpa using
    FreeBosonVOA.threePointAnticommutator23_eq_opeCoefficient_of_lt_n_ge_k
      (R := R) (F := F)
      (ω := D.vacuumData) (hVac := D.vacuum_eq) D.ope x m hn hk

end CFTData

end FreeBosonVOA


end StringAlgebra.VOA
