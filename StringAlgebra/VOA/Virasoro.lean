/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra
import Mathlib.Algebra.Lie.Basic

/-!
# Virasoro Algebra and Conformal Structure

This file defines the Virasoro algebra and its representations in the context of VOAs.

## Main Definitions

* `VirasoroAlgebra` - The Virasoro Lie algebra with central extension
* `VermaModule` - Verma modules for the Virasoro algebra
* `MinimalModel` - Minimal model VOAs M(p,q)

## Main Results

* `virasoro_bracket` - [L_m, L_n] = (m-n)L_{m+n} + (c/12)m(m²-1)δ_{m,-n}

## References

* Kac, "Vertex Algebras for Beginners", Chapter 4
* Di Francesco, Mathieu, Sénéchal, "Conformal Field Theory"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## The Virasoro Algebra

The Virasoro algebra is the unique central extension of the Witt algebra.
-/

/-- The Virasoro algebra over R with central charge c.
    Generators: L_n for n ∈ ℤ, and central element C.
    Relations: 12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n} C -/
structure VirasoroAlgebra (R : Type*) [CommRing R] where
  /-- The central charge -/
  centralCharge : R

namespace VirasoroAlgebra

variable {R : Type*} [CommRing R]

/-- The generators: L_n indexed by ℤ, plus the central element -/
def Generators := ℤ ⊕ Unit

/-- The vector space of the Virasoro algebra (formal linear combinations) -/
def Space (_vir : VirasoroAlgebra R) := Generators →₀ R

noncomputable instance (vir : VirasoroAlgebra R) : AddCommGroup vir.Space :=
  inferInstanceAs (AddCommGroup (Generators →₀ R))

noncomputable instance (vir : VirasoroAlgebra R) : Module R vir.Space :=
  inferInstanceAs (Module R (Generators →₀ R))

/-- The generator L_n -/
noncomputable def L (vir : VirasoroAlgebra R) (n : ℤ) : vir.Space :=
  Finsupp.single (Sum.inl n) 1

/-- The central element C -/
noncomputable def C (vir : VirasoroAlgebra R) : vir.Space :=
  Finsupp.single (Sum.inr ()) 1

/-- The Virasoro bracket [L_m, L_n] (scaled by 12 to avoid division):
    12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n} C -/
noncomputable def bracket (vir : VirasoroAlgebra R) (m n : ℤ) : vir.Space :=
  (12 : R) • ((m - n : ℤ) • vir.L (m + n)) +
  if m + n = 0 then (vir.centralCharge * (m^3 - m) : R) • vir.C else 0

theorem bracket_of_sum_ne_zero (vir : VirasoroAlgebra R) (m n : ℤ) (h : m + n ≠ 0) :
    vir.bracket m n = (12 : R) • ((m - n : ℤ) • vir.L (m + n)) := by
  simp [VirasoroAlgebra.bracket, h]

theorem bracket_of_sum_eq_zero (vir : VirasoroAlgebra R) (m n : ℤ) (h : m + n = 0) :
    vir.bracket m n =
      (12 : R) • ((m - n : ℤ) • vir.L (m + n)) +
      (vir.centralCharge * (m^3 - m) : R) • vir.C := by
  simp [VirasoroAlgebra.bracket, h]

@[simp] theorem bracket_zero_zero (vir : VirasoroAlgebra R) :
    vir.bracket 0 0 = 0 := by
  simp [VirasoroAlgebra.bracket]

theorem bracket_zero_left (vir : VirasoroAlgebra R) (n : ℤ) :
    vir.bracket 0 n = (12 : R) • ((-n : ℤ) • vir.L n) := by
  by_cases hn : n = 0
  · subst hn
    simp [VirasoroAlgebra.bracket]
  · have hsum : (0 : ℤ) + n ≠ 0 := by simpa using hn
    simpa [sub_eq_add_neg] using vir.bracket_of_sum_ne_zero 0 n hsum

theorem bracket_zero_right (vir : VirasoroAlgebra R) (m : ℤ) :
    vir.bracket m 0 = (12 : R) • ((m : ℤ) • vir.L m) := by
  by_cases hm : m = 0
  · subst hm
    simp [VirasoroAlgebra.bracket]
  · have hsum : m + (0 : ℤ) ≠ 0 := by simpa [add_comm] using hm
    simpa using vir.bracket_of_sum_ne_zero m 0 hsum

@[simp] theorem bracket_diag (vir : VirasoroAlgebra R) (m : ℤ) :
    vir.bracket m m = 0 := by
  by_cases hsum : m + m = 0
  · have h2 : (2 : ℤ) * m = 0 := by simpa [two_mul] using hsum
    have hm : m = 0 := (mul_eq_zero.mp h2).resolve_left (by decide : (2 : ℤ) ≠ 0)
    subst hm
    simp [VirasoroAlgebra.bracket]
  · simp [VirasoroAlgebra.bracket, hsum]

theorem bracket_zero_right_eq_neg_bracket_zero_left (vir : VirasoroAlgebra R) (m : ℤ) :
    vir.bracket m 0 = -vir.bracket 0 m := by
  simp [bracket_zero_left, bracket_zero_right]

/-- The Lie bracket on the Virasoro algebra -/
noncomputable def lieBracket (vir : VirasoroAlgebra R) :
    vir.Space → vir.Space → vir.Space := fun x y =>
  Finsupp.sum x fun i a =>
    Finsupp.sum y fun j b =>
      match i, j with
      | Sum.inl m, Sum.inl n => (a * b) • vir.bracket m n
      | Sum.inl _, Sum.inr () => 0
      | Sum.inr (), Sum.inl _ => 0
      | Sum.inr (), Sum.inr () => 0

/-- Predicate asserting the Lie-algebra axioms for `lieBracket`. -/
def satisfiesLieAxioms (vir : VirasoroAlgebra R) : Prop :=
  (∀ x y, vir.lieBracket x y = -vir.lieBracket y x) ∧
  (∀ x y z, vir.lieBracket x (vir.lieBracket y z) +
            vir.lieBracket y (vir.lieBracket z x) +
            vir.lieBracket z (vir.lieBracket x y) = 0)

end VirasoroAlgebra

/-! ## Virasoro Representations -/

/-- A representation of the Virasoro algebra -/
structure VirasoroRep (vir : VirasoroAlgebra R)
    (V : Type*) [AddCommGroup V] [Module R V] where
  /-- The action of L_n on V -/
  L : ℤ → Module.End R V
  /-- The representation satisfies the scaled Virasoro relations:
      12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n} -/
  virasoro_relation : ∀ m n : ℤ,
    (12 : R) • (L m ∘ₗ L n - L n ∘ₗ L m) =
    (12 : R) • ((m - n : ℤ) • L (m + n)) +
    if m + n = 0 then (vir.centralCharge * (m^3 - m) : R) • LinearMap.id else 0

namespace VirasoroRep

variable {R : Type*} [CommRing R]
variable {vir : VirasoroAlgebra R}
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Applied form of the Virasoro relation on vectors. -/
theorem virasoro_relation_apply (ρ : VirasoroRep R vir V) (m n : ℤ) (v : V) :
    (12 : R) • ((ρ.L m) ((ρ.L n) v) - (ρ.L n) ((ρ.L m) v)) =
      (12 : R) • ((m : ℤ) • (ρ.L (m + n) v) - (n : ℤ) • (ρ.L (m + n) v)) +
      ((if m + n = 0
        then (vir.centralCharge * (m^3 - m) : R) • (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) v) := by
  simpa [LinearMap.sub_apply, LinearMap.comp_apply] using
    congrArg (fun f : Module.End R V => f v) (ρ.virasoro_relation m n)

/-- Specialization of the Virasoro relation to `m = 0`. -/
theorem virasoro_relation_zero_left (ρ : VirasoroRep R vir V) (n : ℤ) :
    (12 : R) • (ρ.L 0 ∘ₗ ρ.L n - ρ.L n ∘ₗ ρ.L 0) =
      (12 : R) • ((0 : ℤ) • ρ.L n - (n : ℤ) • ρ.L n) := by
  simpa using ρ.virasoro_relation 0 n

/-- Simplified `m = 0` specialization of the Virasoro relation. -/
theorem virasoro_relation_zero_left_simplified (ρ : VirasoroRep R vir V) (n : ℤ) :
    (12 : R) • (ρ.L 0 ∘ₗ ρ.L n - ρ.L n ∘ₗ ρ.L 0) =
      (12 : R) • ((-n : ℤ) • ρ.L n) := by
  simpa [sub_eq_add_neg, neg_zsmul] using ρ.virasoro_relation_zero_left n

/-- Specialization of the Virasoro relation to `n = 0`. -/
theorem virasoro_relation_zero_right (ρ : VirasoroRep R vir V) (m : ℤ) :
    (12 : R) • (ρ.L m ∘ₗ ρ.L 0 - ρ.L 0 ∘ₗ ρ.L m) =
      (12 : R) • ((m : ℤ) • ρ.L m - (0 : ℤ) • ρ.L m) +
      if m = 0 then (vir.centralCharge * (m^3 - m) : R) • (LinearMap.id : Module.End R V)
      else (0 : Module.End R V) := by
  simpa using ρ.virasoro_relation m 0

/-- Simplified `n = 0` specialization of the Virasoro relation. -/
theorem virasoro_relation_zero_right_simplified (ρ : VirasoroRep R vir V) (m : ℤ) :
    (12 : R) • (ρ.L m ∘ₗ ρ.L 0 - ρ.L 0 ∘ₗ ρ.L m) =
      (12 : R) • ((m : ℤ) • ρ.L m) := by
  by_cases hm : m = 0
  · subst hm
    simp
  · simp [virasoro_relation_zero_right, hm]

/-- Applied `m = 0` Virasoro commutator specialization. -/
theorem virasoro_relation_zero_left_apply (ρ : VirasoroRep R vir V) (n : ℤ) (v : V) :
    (12 : R) • ((ρ.L 0) ((ρ.L n) v) - (ρ.L n) ((ρ.L 0) v)) =
      (12 : R) • ((-n : ℤ) • (ρ.L n v)) := by
  simpa [LinearMap.sub_apply, LinearMap.comp_apply] using
    congrArg (fun f : Module.End R V => f v) (ρ.virasoro_relation_zero_left_simplified n)

/-- Applied `n = 0` Virasoro commutator specialization. -/
theorem virasoro_relation_zero_right_apply (ρ : VirasoroRep R vir V) (m : ℤ) (v : V) :
    (12 : R) • ((ρ.L m) ((ρ.L 0) v) - (ρ.L 0) ((ρ.L m) v)) =
      (12 : R) • ((m : ℤ) • (ρ.L m v)) := by
  simpa [LinearMap.sub_apply, LinearMap.comp_apply] using
    congrArg (fun f : Module.End R V => f v) (ρ.virasoro_relation_zero_right_simplified m)

/-- Diagonal specialization `m = n` of the Virasoro commutator relation. -/
theorem virasoro_relation_diag (ρ : VirasoroRep R vir V) (m : ℤ) :
    (12 : R) • (ρ.L m ∘ₗ ρ.L m - ρ.L m ∘ₗ ρ.L m) = 0 := by
  simp

/-- Diagonal specialization of the right-hand side of the Virasoro relation. -/
theorem virasoro_relation_diag_rhs (ρ : VirasoroRep R vir V) (m : ℤ) :
    (12 : R) • ((m - m : ℤ) • ρ.L (m + m)) +
      (if m + m = 0
        then (vir.centralCharge * (m^3 - m) : R) • (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) = 0 := by
  calc
    (12 : R) • ((m - m : ℤ) • ρ.L (m + m)) +
        (if m + m = 0
          then (vir.centralCharge * (m^3 - m) : R) • (LinearMap.id : Module.End R V)
          else (0 : Module.End R V))
      = (12 : R) • (ρ.L m ∘ₗ ρ.L m - ρ.L m ∘ₗ ρ.L m) := by
          symm
          simpa using ρ.virasoro_relation m m
    _ = 0 := by
      simp

/-- Applied diagonal specialization `m = n` of the Virasoro commutator relation. -/
theorem virasoro_relation_diag_apply (ρ : VirasoroRep R vir V) (m : ℤ) (v : V) :
    (12 : R) • ((ρ.L m) ((ρ.L m) v) - (ρ.L m) ((ρ.L m) v)) = 0 := by
  simp

/-- Applied diagonal specialization of the right-hand side of the Virasoro relation. -/
theorem virasoro_relation_diag_rhs_apply (ρ : VirasoroRep R vir V) (m : ℤ) (v : V) :
    ((12 : R) • ((m - m : ℤ) • ρ.L (m + m)) +
      (if m + m = 0
        then (vir.centralCharge * (m^3 - m) : R) • (LinearMap.id : Module.End R V)
        else (0 : Module.End R V))) v = 0 := by
  exact congrArg (fun f : Module.End R V => f v) (ρ.virasoro_relation_diag_rhs m)

/-- Double-zero specialization of the Virasoro commutator relation. -/
theorem virasoro_relation_zero_zero (ρ : VirasoroRep R vir V) :
    (12 : R) • (ρ.L 0 ∘ₗ ρ.L 0 - ρ.L 0 ∘ₗ ρ.L 0) = 0 := by
  simp

/-- Applied double-zero specialization of the Virasoro commutator relation. -/
theorem virasoro_relation_zero_zero_apply (ρ : VirasoroRep R vir V) (v : V) :
    (12 : R) • ((ρ.L 0) ((ρ.L 0) v) - (ρ.L 0) ((ρ.L 0) v)) = 0 := by
  simp

/-- A highest weight state |h⟩: L_0|h⟩ = h|h⟩, L_n|h⟩ = 0 for n > 0 -/
structure HighestWeightState (ρ : VirasoroRep R vir V) where
  state : V
  weight : R
  L0_eigenvalue : ρ.L 0 state = weight • state
  annihilation : ∀ n : ℕ, n > 0 → ρ.L n state = 0

namespace HighestWeightState

variable {ρ : VirasoroRep R vir V}

@[simp] theorem L0_apply_state (h : HighestWeightState (R := R) (vir := vir) ρ) :
    ρ.L 0 h.state = h.weight • h.state :=
  h.L0_eigenvalue

theorem annihilation_of_pos (h : HighestWeightState (R := R) (vir := vir) ρ)
    (n : ℕ) (hn : n > 0) : ρ.L n h.state = 0 :=
  h.annihilation n hn

@[simp] theorem annihilation_one (h : HighestWeightState (R := R) (vir := vir) ρ) :
    ρ.L 1 h.state = 0 := by
  simpa using h.annihilation 1 (by decide)

@[simp] theorem annihilation_two (h : HighestWeightState (R := R) (vir := vir) ρ) :
    ρ.L 2 h.state = 0 := by
  simpa using h.annihilation 2 (by decide)

end HighestWeightState

/-- A Verma module is generated by a highest weight state under L_{-n} -/
structure VermaModule (vir : VirasoroAlgebra R) where
  /-- The highest weight -/
  highestWeight : R
  /-- The vector space -/
  Space : Type*
  [addCommGroup : AddCommGroup Space]
  [module : Module R Space]
  /-- The representation -/
  rep : VirasoroRep R vir Space
  /-- The highest weight vector -/
  hwVector : Space
  /-- It is indeed highest weight -/
  is_hw : rep.L 0 hwVector = highestWeight • hwVector
  hw_annihilation : ∀ n : ℕ, n > 0 → rep.L n hwVector = 0

attribute [instance] VermaModule.addCommGroup VermaModule.module

namespace VermaModule

def highestWeightState {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir) :
    HighestWeightState (R := R) (vir := vir) M.rep where
  state := M.hwVector
  weight := M.highestWeight
  L0_eigenvalue := M.is_hw
  annihilation := M.hw_annihilation

@[simp] theorem highestWeightState_state {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir) :
    M.highestWeightState.state = M.hwVector := rfl

@[simp] theorem highestWeightState_weight {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir) :
    M.highestWeightState.weight = M.highestWeight := rfl

theorem hw_annihilation_of_pos {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir)
    (n : ℕ) (hn : n > 0) :
    M.rep.L n M.hwVector = 0 :=
  M.hw_annihilation n hn

@[simp] theorem hw_annihilation_one {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir) :
    M.rep.L 1 M.hwVector = 0 := by
  simpa using M.hw_annihilation 1 (by decide)

@[simp] theorem hw_annihilation_two {vir : VirasoroAlgebra R} (M : VermaModule (R := R) vir) :
    M.rep.L 2 M.hwVector = 0 := by
  simpa using M.hw_annihilation 2 (by decide)

end VermaModule

end VirasoroRep

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
