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

/-- State-level three-point correlator linearity in the first inserted mode. -/
theorem threePointStateModes_add_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (a + b) =
      VertexAlgebra.Y (R := R) a + VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω (a + b) c d m n k =
      threePointStateModes (R := R) ω a c d m n k +
        threePointStateModes (R := R) ω b c d m n k := by
  unfold threePointStateModes
  simpa [hYadd] using
    (threePointModes_add_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level three-point correlator linearity in the middle inserted mode. -/
theorem threePointStateModes_add_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (b + c) =
      VertexAlgebra.Y (R := R) b + VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a (b + c) d m n k =
      threePointStateModes (R := R) ω a b d m n k +
        threePointStateModes (R := R) ω a c d m n k := by
  unfold threePointStateModes
  simpa [hYadd] using
    (threePointModes_add_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level three-point correlator linearity in the third inserted mode. -/
theorem threePointStateModes_add_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYadd : VertexAlgebra.Y (R := R) (c + d) =
      VertexAlgebra.Y (R := R) c + VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a b (c + d) m n k =
      threePointStateModes (R := R) ω a b c m n k +
        threePointStateModes (R := R) ω a b d m n k := by
  unfold threePointStateModes
  simpa [hYadd] using
    (threePointModes_add_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level three-point correlator linearity under scalar multiplication in
    the first slot. -/
theorem threePointStateModes_smul_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • a) = r • VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω (r • a) b c m n k =
      r • threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYsmul] using
    (threePointModes_smul_left (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level three-point correlator linearity under scalar multiplication in
    the middle slot. -/
theorem threePointStateModes_smul_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • b) = r • VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a (r • b) c m n k =
      r • threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYsmul] using
    (threePointModes_smul_middle (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level three-point correlator linearity under scalar multiplication in
    the third slot. -/
theorem threePointStateModes_smul_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (r : R) (a b c : V)
    (hYsmul : VertexAlgebra.Y (R := R) (r • c) = r • VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a b (r • c) m n k =
      r • threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYsmul] using
    (threePointModes_smul_right (R := R) (ω := ω) r
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level negation linearity in the first field slot of three-point
    correlators. -/
theorem threePointStateModes_neg_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-a) = -VertexAlgebra.Y (R := R) a)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω (-a) b c m n k =
      -threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYneg] using
    (threePointModes_neg_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level negation linearity in the second field slot of three-point
    correlators. -/
theorem threePointStateModes_neg_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-b) = -VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a (-b) c m n k =
      -threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYneg] using
    (threePointModes_neg_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level negation linearity in the third field slot of three-point
    correlators. -/
theorem threePointStateModes_neg_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c : V)
    (hYneg : VertexAlgebra.Y (R := R) (-c) = -VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a b (-c) m n k =
      -threePointStateModes (R := R) ω a b c m n k := by
  unfold threePointStateModes
  simpa [hYneg] using
    (threePointModes_neg_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) m n k)

/-- State-level subtraction linearity in the first field slot of three-point
    correlators. -/
theorem threePointStateModes_sub_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (a - b) =
      VertexAlgebra.Y (R := R) a - VertexAlgebra.Y (R := R) b)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω (a - b) c d m n k =
      threePointStateModes (R := R) ω a c d m n k -
        threePointStateModes (R := R) ω b c d m n k := by
  unfold threePointStateModes
  simpa [hYsub] using
    (threePointModes_sub_left (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level subtraction linearity in the middle field slot of three-point
    correlators. -/
theorem threePointStateModes_sub_middle
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (b - c) =
      VertexAlgebra.Y (R := R) b - VertexAlgebra.Y (R := R) c)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a (b - c) d m n k =
      threePointStateModes (R := R) ω a b d m n k -
        threePointStateModes (R := R) ω a c d m n k := by
  unfold threePointStateModes
  simpa [hYsub] using
    (threePointModes_sub_middle (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)

/-- State-level subtraction linearity in the third field slot of three-point
    correlators. -/
theorem threePointStateModes_sub_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (ω : VacuumFunctional (R := R) V)
    (a b c d : V)
    (hYsub : VertexAlgebra.Y (R := R) (c - d) =
      VertexAlgebra.Y (R := R) c - VertexAlgebra.Y (R := R) d)
    (m n k : ℤ) :
    threePointStateModes (R := R) ω a b (c - d) m n k =
      threePointStateModes (R := R) ω a b c m n k -
        threePointStateModes (R := R) ω a b d m n k := by
  unfold threePointStateModes
  simpa [hYsub] using
    (threePointModes_sub_right (R := R) (ω := ω)
      (a := VertexAlgebra.Y (R := R) a) (b := VertexAlgebra.Y (R := R) b)
      (c := VertexAlgebra.Y (R := R) c) (d := VertexAlgebra.Y (R := R) d) m n k)


end StringAlgebra.VOA
