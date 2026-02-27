/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra

/-!
# Algebraic Correlators for VOAs

This file introduces algebraic correlator primitives based on mode insertions:

1. a vacuum functional package,
2. ordered words of field modes as endomorphisms,
3. n-point mode correlators built by applying those mode words to the vacuum.

The constructions here are purely algebraic and do not assume analytic convergence.

## References

* Kac, "Vertex Algebras for Beginners" (mode conventions and `j`-products/OPE modes)
* Frenkel, Ben-Zvi, "Vertex Algebras and Algebraic Curves" (formal distributions and OPE coefficients)
* Borcherds, "Vertex algebras, Kac-Moody algebras, and the Monster" (state-field algebraic framework)
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-- A vacuum functional for an algebraic VOA model. -/
structure VacuumFunctional
    (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] where
  /-- Linear vacuum expectation map. -/
  epsilon : V →ₗ[R] R
  /-- Vacuum normalization `⟨|0⟩⟩ = 1`. -/
  vacuum_norm : epsilon (VertexAlgebra.vacuum (R := R)) = 1

namespace VacuumFunctional

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]

@[simp] theorem epsilon_vacuum (ω : VacuumFunctional (R := R) V) :
    ω.epsilon (VertexAlgebra.vacuum (R := R)) = 1 :=
  ω.vacuum_norm

end VacuumFunctional

/-- A mode insertion is a pair `(a, n)` interpreted as the mode operator `a(n)`. -/
abbrev ModeInsertion (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] :=
  FormalDistribution R V × ℤ

/-- Endomorphism represented by an ordered word of mode insertions.
    Order convention: `(a₁,n₁)::...::(aₖ,nₖ)` acts as `aₖ(nₖ) ... a₁(n₁)`. -/
def modeWordEnd
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    List (ModeInsertion (R := R) V) → Module.End R V
  | [] => LinearMap.id
  | (a, n) :: ops => (modeWordEnd ops).comp (a n)

@[simp] theorem modeWordEnd_nil
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    modeWordEnd (R := R) (V := V) [] = (LinearMap.id : Module.End R V) := rfl

@[simp] theorem modeWordEnd_cons
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (a : FormalDistribution R V) (n : ℤ) (ops : List (ModeInsertion (R := R) V)) :
    modeWordEnd (R := R) ((a, n) :: ops) = (modeWordEnd (R := R) ops).comp (a n) := by
  simp [modeWordEnd]

@[simp] theorem modeWordEnd_apply_nil
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V] (v : V) :
    modeWordEnd (R := R) (V := V) [] v = v := rfl

@[simp] theorem modeWordEnd_apply_cons
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (a : FormalDistribution R V) (n : ℤ)
    (ops : List (ModeInsertion (R := R) V)) (v : V) :
    modeWordEnd (R := R) ((a, n) :: ops) v = modeWordEnd (R := R) ops ((a n) v) := by
  simp [modeWordEnd]

/-- Concatenation corresponds to composition of mode-word endomorphisms. -/
theorem modeWordEnd_append
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ops₁ ops₂ : List (ModeInsertion (R := R) V)) :
    modeWordEnd (R := R) (ops₁ ++ ops₂) =
      (modeWordEnd (R := R) ops₂).comp (modeWordEnd (R := R) ops₁) := by
  induction ops₁ with
  | nil =>
      simp [modeWordEnd]
  | cons op ops ih =>
      rcases op with ⟨a, n⟩
      simp [modeWordEnd, ih, LinearMap.comp_assoc]

/-- Algebraic n-point correlator for a list of mode insertions, evaluated on the vacuum. -/
def nPointModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V) (ops : List (ModeInsertion (R := R) V)) : R :=
  ω.epsilon (modeWordEnd (R := R) ops (VertexAlgebra.vacuum (R := R)))

@[simp] theorem nPointModes_nil
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V) :
    nPointModes (R := R) ω [] = 1 := by
  simp [nPointModes, VacuumFunctional.epsilon_vacuum]

@[simp] theorem nPointModes_cons
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (n : ℤ)
    (ops : List (ModeInsertion (R := R) V)) :
    nPointModes (R := R) ω ((a, n) :: ops) =
      ω.epsilon (modeWordEnd (R := R) ops ((a n) (VertexAlgebra.vacuum (R := R)))) := by
  simp [nPointModes, modeWordEnd]

/-- Concatenation formula for mode correlators. -/
theorem nPointModes_append
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (ops₁ ops₂ : List (ModeInsertion (R := R) V)) :
    nPointModes (R := R) ω (ops₁ ++ ops₂) =
      ω.epsilon ((modeWordEnd (R := R) ops₂)
        ((modeWordEnd (R := R) ops₁) (VertexAlgebra.vacuum (R := R)))) := by
  simp [nPointModes, modeWordEnd_append, LinearMap.comp_apply]

/-- One-point mode correlator specialization. -/
def onePointModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (n : ℤ) : R :=
  nPointModes (R := R) ω [(a, n)]

@[simp] theorem onePointModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (n : ℤ) :
    onePointModes (R := R) ω a n =
      ω.epsilon ((a n) (VertexAlgebra.vacuum (R := R))) := by
  simp [onePointModes, nPointModes, modeWordEnd]

/-- One-point correlator with a state insertion via the state-field map. -/
def onePointStateModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (n : ℤ) : R :=
  onePointModes (R := R) ω (VertexAlgebra.Y (R := R) a) n

@[simp] theorem onePointStateModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (n : ℤ) :
    onePointStateModes (R := R) ω a n =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) a n) (VertexAlgebra.vacuum (R := R))) := by
  simp [onePointStateModes, onePointModes_eq]

/-- Positive modes annihilate the vacuum in one-point state correlators. -/
theorem onePointStateModes_eq_zero_of_nat
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (n : ℕ) :
    onePointStateModes (R := R) ω a n = 0 := by
  simp [onePointStateModes, onePointModes_eq, VertexAlgebra.creation_axiom_annihilation]

/-- The `(-1)` one-point state-mode correlator is the vacuum functional on the state. -/
@[simp] theorem onePointStateModes_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) :
    onePointStateModes (R := R) ω a (-1) = ω.epsilon a := by
  simp [onePointStateModes, onePointModes_eq, VertexAlgebra.creation_axiom_value]

/-- One-point correlator of the vacuum state has the identity-field Kronecker form. -/
theorem onePointVacuumModes_eq_ite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (n : ℤ) :
    onePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) n =
      if n = -1 then 1 else 0 := by
  by_cases hn : n = -1
  · subst hn
    simp [onePointStateModes, onePointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [onePointStateModes, onePointModes_eq, VertexAlgebra.vacuum_axiom, hn]

@[simp] theorem onePointVacuumModes_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V) :
    onePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) (-1) = 1 := by
  simpa using onePointVacuumModes_eq_ite (R := R) (ω := ω) (-1)

theorem onePointVacuumModes_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (n : ℤ) (hn : n ≠ -1) :
    onePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) n = 0 := by
  simpa [hn] using onePointVacuumModes_eq_ite (R := R) (ω := ω) n

/-- Two-point mode correlator specialization. -/
def twoPointModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) : R :=
  nPointModes (R := R) ω [(a, m), (b, n)]

/-- Three-point mode correlator specialization. -/
def threePointModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) : R :=
  nPointModes (R := R) ω [(a, m), (b, n), (c, k)]

/-- Two-point correlator with state insertions via the state-field map. -/
def twoPointStateModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) : R :=
  twoPointModes (R := R) ω (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) m n

/-- Three-point correlator with state insertions via the state-field map. -/
def threePointStateModes
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) : R :=
  threePointModes (R := R) ω
    (VertexAlgebra.Y (R := R) a) (VertexAlgebra.Y (R := R) b) (VertexAlgebra.Y (R := R) c) m n k

@[simp] theorem twoPointModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a b m n =
      ω.epsilon ((b n) ((a m) (VertexAlgebra.vacuum (R := R)))) := by
  simp [twoPointModes, nPointModes, modeWordEnd]

@[simp] theorem twoPointStateModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    twoPointStateModes (R := R) ω a b m n =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) b n)
          ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R)))) := by
  simp [twoPointStateModes, twoPointModes_eq]

/-- Positive first mode annihilates the vacuum in two-point state correlators. -/
theorem twoPointStateModes_eq_zero_of_nat_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m : ℕ) (n : ℤ) :
    twoPointStateModes (R := R) ω a b (m : ℤ) n = 0 := by
  simp [twoPointStateModes, twoPointModes_eq, VertexAlgebra.creation_axiom_annihilation]

/-- Two-point correlator with vacuum inserted first, reduced to one-point data. -/
theorem twoPointModes_vacuum_left_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a m n =
      if m = -1 then onePointModes (R := R) ω a n else 0 := by
  by_cases hm : m = -1
  · subst hm
    simp [twoPointModes_eq, onePointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [twoPointModes_eq, VertexAlgebra.vacuum_axiom, hm]

/-- Two-point correlator with vacuum inserted second, reduced to one-point data. -/
theorem twoPointModes_vacuum_right_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (m n : ℤ) :
    twoPointModes (R := R) ω a (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m n =
      if n = -1 then onePointModes (R := R) ω a m else 0 := by
  by_cases hn : n = -1
  · subst hn
    simp [twoPointModes_eq, onePointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [twoPointModes_eq, VertexAlgebra.vacuum_axiom, hn]

@[simp] theorem twoPointModes_vacuum_left_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (n : ℤ) :
    twoPointModes (R := R) ω
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a (-1) n =
        onePointModes (R := R) ω a n := by
  simpa using twoPointModes_vacuum_left_eq (R := R) (ω := ω) a (-1) n

theorem twoPointModes_vacuum_left_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (m n : ℤ) (hm : m ≠ -1) :
    twoPointModes (R := R) ω
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a m n = 0 := by
  simpa [hm] using twoPointModes_vacuum_left_eq (R := R) (ω := ω) a m n

@[simp] theorem twoPointModes_vacuum_right_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (m : ℤ) :
    twoPointModes (R := R) ω a
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m (-1) =
        onePointModes (R := R) ω a m := by
  simpa using twoPointModes_vacuum_right_eq (R := R) (ω := ω) a m (-1)

theorem twoPointModes_vacuum_right_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : FormalDistribution R V) (m n : ℤ) (hn : n ≠ -1) :
    twoPointModes (R := R) ω a
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m n = 0 := by
  simpa [hn] using twoPointModes_vacuum_right_eq (R := R) (ω := ω) a m n

/-- State-level two-point correlator with vacuum in the first slot. -/
theorem twoPointStateModes_vacuum_left_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (m n : ℤ) :
    twoPointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a m n =
      if m = -1 then onePointStateModes (R := R) ω a n else 0 := by
  simpa [twoPointStateModes, onePointStateModes] using
    (twoPointModes_vacuum_left_eq (R := R) (ω := ω) (a := VertexAlgebra.Y (R := R) a) m n)

/-- State-level two-point correlator with vacuum in the second slot. -/
theorem twoPointStateModes_vacuum_right_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (m n : ℤ) :
    twoPointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) m n =
      if n = -1 then onePointStateModes (R := R) ω a m else 0 := by
  simpa [twoPointStateModes, onePointStateModes] using
    (twoPointModes_vacuum_right_eq (R := R) (ω := ω) (a := VertexAlgebra.Y (R := R) a) m n)

@[simp] theorem twoPointStateModes_vacuum_left_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (n : ℤ) :
    twoPointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a (-1) n =
      onePointStateModes (R := R) ω a n := by
  simpa using twoPointStateModes_vacuum_left_eq (R := R) (ω := ω) a (-1) n

theorem twoPointStateModes_vacuum_left_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (m n : ℤ) (hm : m ≠ -1) :
    twoPointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a m n = 0 := by
  simpa [hm] using twoPointStateModes_vacuum_left_eq (R := R) (ω := ω) a m n

@[simp] theorem twoPointStateModes_vacuum_right_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (m : ℤ) :
    twoPointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) m (-1) =
      onePointStateModes (R := R) ω a m := by
  simpa using twoPointStateModes_vacuum_right_eq (R := R) (ω := ω) a m (-1)

theorem twoPointStateModes_vacuum_right_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a : V) (m n : ℤ) (hn : n ≠ -1) :
    twoPointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) m n = 0 := by
  simpa [hn] using twoPointStateModes_vacuum_right_eq (R := R) (ω := ω) a m n

@[simp] theorem threePointModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a b c m n k =
      ω.epsilon ((c k) ((b n) ((a m) (VertexAlgebra.vacuum (R := R))))) := by
  simp [threePointModes, nPointModes, modeWordEnd]

@[simp] theorem threePointStateModes_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m n k : ℤ) :
    threePointStateModes (R := R) ω a b c m n k =
      ω.epsilon
        ((VertexAlgebra.Y (R := R) c k)
          ((VertexAlgebra.Y (R := R) b n)
            ((VertexAlgebra.Y (R := R) a m) (VertexAlgebra.vacuum (R := R))))) := by
  simp [threePointStateModes, threePointModes_eq]

/-- Positive first mode annihilates the vacuum in three-point state correlators. -/
theorem threePointStateModes_eq_zero_of_nat_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V) (m : ℕ) (n k : ℤ) :
    threePointStateModes (R := R) ω a b c (m : ℤ) n k = 0 := by
  simp [threePointStateModes, threePointModes_eq, VertexAlgebra.creation_axiom_annihilation]

/-- Three-point correlator with vacuum inserted first, reduced to a two-point correlator. -/
theorem threePointModes_vacuum_left_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a b m n k =
        if m = -1 then twoPointModes (R := R) ω a b n k else 0 := by
  by_cases hm : m = -1
  · subst hm
    simp [threePointModes_eq, twoPointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [threePointModes_eq, VertexAlgebra.vacuum_axiom, hm]

/-- Three-point correlator with vacuum inserted second, reduced to a two-point correlator. -/
theorem threePointModes_vacuum_middle_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω
      a (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) b m n k =
        if n = -1 then twoPointModes (R := R) ω a b m k else 0 := by
  by_cases hn : n = -1
  · subst hn
    simp [threePointModes_eq, twoPointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [threePointModes_eq, VertexAlgebra.vacuum_axiom, hn]

/-- Three-point correlator with vacuum inserted third, reduced to a two-point correlator. -/
theorem threePointModes_vacuum_right_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω
      a b (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m n k =
        if k = -1 then twoPointModes (R := R) ω a b m n else 0 := by
  by_cases hk : k = -1
  · subst hk
    simp [threePointModes_eq, twoPointModes_eq, VertexAlgebra.vacuum_axiom]
  · simp [threePointModes_eq, VertexAlgebra.vacuum_axiom, hk]

@[simp] theorem threePointModes_vacuum_left_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (n k : ℤ) :
    threePointModes (R := R) ω
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a b (-1) n k =
        twoPointModes (R := R) ω a b n k := by
  simpa using threePointModes_vacuum_left_eq (R := R) (ω := ω) a b (-1) n k

theorem threePointModes_vacuum_left_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) (hm : m ≠ -1) :
    threePointModes (R := R) ω
      (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) a b m n k = 0 := by
  simpa [hm] using threePointModes_vacuum_left_eq (R := R) (ω := ω) a b m n k

@[simp] theorem threePointModes_vacuum_middle_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m k : ℤ) :
    threePointModes (R := R) ω
      a (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) b m (-1) k =
        twoPointModes (R := R) ω a b m k := by
  simpa using threePointModes_vacuum_middle_eq (R := R) (ω := ω) a b m (-1) k

theorem threePointModes_vacuum_middle_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) (hn : n ≠ -1) :
    threePointModes (R := R) ω
      a (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) b m n k = 0 := by
  simpa [hn] using threePointModes_vacuum_middle_eq (R := R) (ω := ω) a b m n k

@[simp] theorem threePointModes_vacuum_right_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n : ℤ) :
    threePointModes (R := R) ω
      a b (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m n (-1) =
        twoPointModes (R := R) ω a b m n := by
  simpa using threePointModes_vacuum_right_eq (R := R) (ω := ω) a b m n (-1)

theorem threePointModes_vacuum_right_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : FormalDistribution R V) (m n k : ℤ) (hk : k ≠ -1) :
    threePointModes (R := R) ω
      a b (VertexAlgebra.Y (R := R) (VertexAlgebra.vacuum (R := R))) m n k = 0 := by
  simpa [hk] using threePointModes_vacuum_right_eq (R := R) (ω := ω) a b m n k

/-- State-level three-point correlator with vacuum in the first slot. -/
theorem threePointStateModes_vacuum_left_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) :
    threePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a b m n k =
      if m = -1 then twoPointStateModes (R := R) ω a b n k else 0 := by
  simpa [threePointStateModes, twoPointStateModes] using
    (threePointModes_vacuum_left_eq (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n k)

/-- State-level three-point correlator with vacuum in the second slot. -/
theorem threePointStateModes_vacuum_middle_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) :
    threePointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) b m n k =
      if n = -1 then twoPointStateModes (R := R) ω a b m k else 0 := by
  simpa [threePointStateModes, twoPointStateModes] using
    (threePointModes_vacuum_middle_eq (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n k)

/-- State-level three-point correlator with vacuum in the third slot. -/
theorem threePointStateModes_vacuum_right_eq
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) :
    threePointStateModes (R := R) ω a b (VertexAlgebra.vacuum (R := R)) m n k =
      if k = -1 then twoPointStateModes (R := R) ω a b m n else 0 := by
  simpa [threePointStateModes, twoPointStateModes] using
    (threePointModes_vacuum_right_eq (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b) m n k)

@[simp] theorem threePointStateModes_vacuum_left_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (n k : ℤ) :
    threePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a b (-1) n k =
      twoPointStateModes (R := R) ω a b n k := by
  simpa using threePointStateModes_vacuum_left_eq (R := R) (ω := ω) a b (-1) n k

theorem threePointStateModes_vacuum_left_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) (hm : m ≠ -1) :
    threePointStateModes (R := R) ω (VertexAlgebra.vacuum (R := R)) a b m n k = 0 := by
  simpa [hm] using threePointStateModes_vacuum_left_eq (R := R) (ω := ω) a b m n k

@[simp] theorem threePointStateModes_vacuum_middle_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m k : ℤ) :
    threePointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) b m (-1) k =
      twoPointStateModes (R := R) ω a b m k := by
  simpa using threePointStateModes_vacuum_middle_eq (R := R) (ω := ω) a b m (-1) k

theorem threePointStateModes_vacuum_middle_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) (hn : n ≠ -1) :
    threePointStateModes (R := R) ω a (VertexAlgebra.vacuum (R := R)) b m n k = 0 := by
  simpa [hn] using threePointStateModes_vacuum_middle_eq (R := R) (ω := ω) a b m n k

@[simp] theorem threePointStateModes_vacuum_right_minus_one
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n : ℤ) :
    threePointStateModes (R := R) ω a b (VertexAlgebra.vacuum (R := R)) m n (-1) =
      twoPointStateModes (R := R) ω a b m n := by
  simpa using threePointStateModes_vacuum_right_eq (R := R) (ω := ω) a b m n (-1)

theorem threePointStateModes_vacuum_right_eq_zero_of_ne
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b : V) (m n k : ℤ) (hk : k ≠ -1) :
    threePointStateModes (R := R) ω a b (VertexAlgebra.vacuum (R := R)) m n k = 0 := by
  simpa [hk] using threePointStateModes_vacuum_right_eq (R := R) (ω := ω) a b m n k

/-- Three-point correlator linearity in the first inserted field mode. -/
theorem threePointModes_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω (a + b) c d m n k =
      threePointModes (R := R) ω a c d m n k + threePointModes (R := R) ω b c d m n k := by
  have hmode : (a + b) m = a m + b m := rfl
  simp [threePointModes_eq, hmode, LinearMap.map_add]

/-- Three-point correlator linearity in the second inserted field mode. -/
theorem threePointModes_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a (b + c) d m n k =
      threePointModes (R := R) ω a b d m n k + threePointModes (R := R) ω a c d m n k := by
  have hmode : (b + c) n = b n + c n := rfl
  simp [threePointModes_eq, hmode, LinearMap.map_add]

/-- Three-point correlator linearity in the third inserted field mode. -/
theorem threePointModes_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a b (c + d) m n k =
      threePointModes (R := R) ω a b c m n k + threePointModes (R := R) ω a b d m n k := by
  have hmode : (c + d) k = c k + d k := rfl
  simp [threePointModes_eq, hmode, LinearMap.map_add]

/-- Three-point correlator linearity under scalar multiplication in the first slot. -/
theorem threePointModes_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω (r • a) b c m n k =
      r • threePointModes (R := R) ω a b c m n k := by
  have hmode : (r • a) m = r • a m := rfl
  simp [threePointModes_eq, hmode]

/-- Three-point correlator linearity under scalar multiplication in the second slot. -/
theorem threePointModes_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a (r • b) c m n k =
      r • threePointModes (R := R) ω a b c m n k := by
  have hmode : (r • b) n = r • b n := rfl
  simp [threePointModes_eq, hmode]

/-- Three-point correlator linearity under scalar multiplication in the third slot. -/
theorem threePointModes_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a b (r • c) m n k =
      r • threePointModes (R := R) ω a b c m n k := by
  have hmode : (r • c) k = r • c k := rfl
  simp [threePointModes_eq, hmode]

/-- Negation linearity for the first field slot of three-point correlators. -/
theorem threePointModes_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω (-a) b c m n k =
      -threePointModes (R := R) ω a b c m n k := by
  simpa using threePointModes_smul_left (R := R) (ω := ω) (-1 : R) a b c m n k

/-- Negation linearity for the second field slot of three-point correlators. -/
theorem threePointModes_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a (-b) c m n k =
      -threePointModes (R := R) ω a b c m n k := by
  simpa using threePointModes_smul_middle (R := R) (ω := ω) (-1 : R) a b c m n k

/-- Negation linearity for the third field slot of three-point correlators. -/
theorem threePointModes_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a b (-c) m n k =
      -threePointModes (R := R) ω a b c m n k := by
  simpa using threePointModes_smul_right (R := R) (ω := ω) (-1 : R) a b c m n k

/-- Subtraction linearity in the first field slot of three-point correlators. -/
theorem threePointModes_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω (a - b) c d m n k =
      threePointModes (R := R) ω a c d m n k - threePointModes (R := R) ω b c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointModes_add_left (R := R) (ω := ω) a (-b) c d m n k]
  rw [threePointModes_neg_left (R := R) (ω := ω) b c d m n k]
  simp [sub_eq_add_neg]

/-- Subtraction linearity in the second field slot of three-point correlators. -/
theorem threePointModes_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a (b - c) d m n k =
      threePointModes (R := R) ω a b d m n k - threePointModes (R := R) ω a c d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointModes_add_middle (R := R) (ω := ω) a b (-c) d m n k]
  rw [threePointModes_neg_middle (R := R) (ω := ω) a c d m n k]
  simp [sub_eq_add_neg]

/-- Subtraction linearity in the third field slot of three-point correlators. -/
theorem threePointModes_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : FormalDistribution R V) (m n k : ℤ) :
    threePointModes (R := R) ω a b (c - d) m n k =
      threePointModes (R := R) ω a b c m n k - threePointModes (R := R) ω a b d m n k := by
  rw [sub_eq_add_neg]
  rw [threePointModes_add_right (R := R) (ω := ω) a b c (-d) m n k]
  rw [threePointModes_neg_right (R := R) (ω := ω) a b d m n k]
  simp [sub_eq_add_neg]

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

end StringAlgebra.VOA
