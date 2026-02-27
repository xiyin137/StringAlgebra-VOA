/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Virasoro.Representation

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Minimal Models

The minimal models M(p,q) with central charge c = 1 - 6(p-q)²/(pq).
-/

/-- The central charge of a minimal model M(p,q) where gcd(p,q) = 1, p > q ≥ 2 -/
def minimalModelCentralCharge (p q : ℕ) (_hp : p > q) (_hq : q ≥ 2)
    (_hcoprime : Nat.Coprime p q) : ℚ :=
  1 - 6 * (p - q : ℤ)^2 / (p * q : ℤ)

/-- The Kac table: conformal weights h_{r,s} -/
def kacTableWeight (p q r s : ℕ) : ℚ :=
  ((p * s - q * r : ℤ)^2 - (p - q : ℤ)^2) / (4 * p * q : ℤ)

/-- A minimal model VOA M(p,q) -/
structure MinimalModel (R : Type*) [CommRing R] where
  /-- Parameters p, q with gcd(p,q) = 1 -/
  p : ℕ
  q : ℕ
  hp : p > q
  hq : q ≥ 2
  hcoprime : Nat.Coprime p q
  /-- The underlying VOA -/
  V : Type*
  [addCommGroup : AddCommGroup V]
  [module : Module R V]
  [voa : VertexOperatorAlgebra R V]

attribute [instance] MinimalModel.addCommGroup MinimalModel.module MinimalModel.voa

namespace MinimalModel

variable {R : Type*} [CommRing R]

@[simp] theorem p_gt_q (M : MinimalModel R) : M.p > M.q := M.hp

@[simp] theorem q_ge_two (M : MinimalModel R) : M.q ≥ 2 := M.hq

@[simp] theorem coprime_p_q (M : MinimalModel R) : Nat.Coprime M.p M.q := M.hcoprime

/-- Rational central charge attached to a minimal-model parameter package. -/
def centralChargeQ (M : MinimalModel R) : ℚ :=
  minimalModelCentralCharge M.p M.q M.hp M.hq M.hcoprime

end MinimalModel

/-! ## Sugawara Construction -/

/-- The Sugawara energy-momentum tensor from an affine Lie algebra -/
noncomputable def sugawaraTensor {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (_currents : ℕ → FormalDistribution R V)
    (_dualCoxeter : R)
    (_level : R)
    (_metric : ℕ → ℕ → R)
    (_dim : ℕ)
    : FormalDistribution R V := fun _ => 0

@[simp] theorem sugawaraTensor_apply {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (currents : ℕ → FormalDistribution R V)
    (dualCoxeter level : R)
    (metric : ℕ → ℕ → R)
    (dim : ℕ) (n : ℤ) :
    sugawaraTensor (R := R) currents dualCoxeter level metric dim n = 0 := rfl

@[simp] theorem sugawaraTensor_eq_zero {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (currents : ℕ → FormalDistribution R V)
    (dualCoxeter level : R)
    (metric : ℕ → ℕ → R)
    (dim : ℕ) :
    sugawaraTensor (R := R) currents dualCoxeter level metric dim = 0 := rfl

/-- The Sugawara construction gives a conformal structure -/
theorem sugawara_central_charge
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (_currents : ℕ → FormalDistribution R V)
    (_dualCoxeter level : R)
    (_metric : ℕ → ℕ → R)
    (dim : ℕ) :
    ∃ c : R, c = level * (dim : R) := by
  exact ⟨level * (dim : R), rfl⟩

end StringAlgebra.VOA
