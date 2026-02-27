/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.SuperBasic
import StringAlgebra.VOA.FormalDistributions

/-!
# Super Formal Distributions

This file connects parity data with formal distributions:

1. parity-labeled formal fields,
2. super-locality (Koszul-signed mode commutation),
3. odd/odd anticommutator locality reformulation,
4. CAR-family to odd-super-locality bridge.
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V]

/-- A formal distribution equipped with a parity label. -/
structure SuperFormalDistribution where
  /-- Underlying field modes. -/
  field : FormalDistribution R V
  /-- Homogeneous parity of the field. -/
  parity : Parity

namespace SuperFormalDistribution

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The `n`-th mode of a super field. -/
def mode (a : SuperFormalDistribution R V) (n : ℤ) : Module.End R V :=
  a.field n

@[simp] theorem mode_eq_apply (a : SuperFormalDistribution R V) (n : ℤ) :
    a.mode n = a.field n := rfl

/-- Field property inherited from the underlying formal distribution. -/
def hasFieldProperty (a : SuperFormalDistribution R V) : Prop :=
  FormalDistribution.hasFieldProperty a.field

/-- Formal derivative preserving parity. -/
def derivative (a : SuperFormalDistribution R V) : SuperFormalDistribution R V where
  field := FormalDistribution.derivative a.field
  parity := a.parity

@[simp] theorem derivative_field (a : SuperFormalDistribution R V) :
    (a.derivative).field = FormalDistribution.derivative a.field := rfl

@[simp] theorem derivative_parity (a : SuperFormalDistribution R V) :
    (a.derivative).parity = a.parity := rfl

theorem derivative_hasFieldProperty
    (a : SuperFormalDistribution R V) (ha : a.hasFieldProperty) :
    (a.derivative).hasFieldProperty :=
  FormalDistribution.derivative_hasFieldProperty (R := R) (V := V) a.field ha

/-- View an ordinary field as an even super field. -/
def even (a : FormalDistribution R V) : SuperFormalDistribution R V where
  field := a
  parity := Parity.even

/-- View an ordinary field as an odd super field. -/
def odd (a : FormalDistribution R V) : SuperFormalDistribution R V where
  field := a
  parity := Parity.odd

@[simp] theorem even_field (a : FormalDistribution R V) :
    (even (R := R) (V := V) a).field = a := rfl
@[simp] theorem odd_field (a : FormalDistribution R V) :
    (odd (R := R) (V := V) a).field = a := rfl
@[simp] theorem even_parity (a : FormalDistribution R V) :
    (even (R := R) (V := V) a).parity = Parity.even := rfl
@[simp] theorem odd_parity (a : FormalDistribution R V) :
    (odd (R := R) (V := V) a).parity = Parity.odd := rfl

/-- Super-locality: modes commute up to the Koszul sign above a finite truncation order. -/
def superMutuallyLocal (a b : SuperFormalDistribution R V) : Prop :=
  ∃ N : ℤ, ∀ v : V, ∀ m n : ℤ, m + n ≥ N →
    (a.field m) ((b.field n) v) =
      (Parity.koszulSign (R := R) a.parity b.parity) • ((b.field n) ((a.field m) v))

theorem superMutuallyLocal_of_mode_relation
    (a b : SuperFormalDistribution R V)
    (hrel : ∀ v : V, ∀ m n : ℤ,
      (a.field m) ((b.field n) v) =
        (Parity.koszulSign (R := R) a.parity b.parity) • ((b.field n) ((a.field m) v))) :
    superMutuallyLocal (R := R) (V := V) a b := by
  refine ⟨0, ?_⟩
  intro v m n _hmn
  exact hrel v m n

/-- Super-locality is symmetric. -/
theorem superMutuallyLocal_symm (a b : SuperFormalDistribution R V) :
    superMutuallyLocal (R := R) (V := V) a b →
      superMutuallyLocal (R := R) (V := V) b a := by
  intro h
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro v m n hmn
  let s : R := Parity.koszulSign (R := R) a.parity b.parity
  have hs2 : s * s = (1 : R) := by
    simpa [s] using Parity.koszulSign_mul_self (R := R) a.parity b.parity
  have hrel : (a.field n) ((b.field m) v) = s • ((b.field m) ((a.field n) v)) := by
    simpa [s, add_comm] using hN v n m (by simpa [add_comm] using hmn)
  have hsmul0 : s • ((a.field n) ((b.field m) v)) = s • (s • ((b.field m) ((a.field n) v))) := by
    exact congrArg (fun t : V => s • t) hrel
  have hsmul : s • ((a.field n) ((b.field m) v)) = (s * s) • ((b.field m) ((a.field n) v)) := by
    simpa [smul_smul, mul_assoc] using hsmul0
  have hswap : (b.field m) ((a.field n) v) = s • ((a.field n) ((b.field m) v)) := by
    calc
      (b.field m) ((a.field n) v) = (1 : R) • ((b.field m) ((a.field n) v)) := by simp
      _ = (s * s) • ((b.field m) ((a.field n) v)) := by simp [hs2]
      _ = s • ((a.field n) ((b.field m) v)) := by simpa using hsmul.symm
  simpa [s, Parity.koszulSign_symm] using hswap

/-- Even/even super-locality is exactly ordinary locality. -/
theorem superMutuallyLocal_even_even_iff
    (a b : FormalDistribution R V) :
    superMutuallyLocal (R := R) (V := V)
      (even (R := R) (V := V) a) (even (R := R) (V := V) b) ↔
      mutuallyLocal (R := R) (V := V) a b := by
  constructor
  · intro h
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro v m n hmn
    have hrel := hN v m n hmn
    simpa [even, Parity.koszulSign] using hrel
  · intro h
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro v m n hmn
    have hcomm := hN v m n hmn
    simpa [even, Parity.koszulSign] using hcomm

/-- Odd/odd super-locality is equivalent to eventual mode anticommutativity. -/
theorem superMutuallyLocal_odd_odd_iff
    (a b : FormalDistribution R V) :
    superMutuallyLocal (R := R) (V := V)
      (odd (R := R) (V := V) a) (odd (R := R) (V := V) b) ↔
      ∃ N : ℤ, ∀ v : V, ∀ m n : ℤ, m + n ≥ N →
        (a m) ((b n) v) + (b n) ((a m) v) = 0 := by
  constructor
  · intro h
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro v m n hmn
    have hrel := hN v m n hmn
    have hneg : (a m) ((b n) v) = -((b n) ((a m) v)) := by
      simpa [odd, Parity.koszulSign] using hrel
    exact eq_neg_iff_add_eq_zero.mp hneg
  · intro h
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro v m n hmn
    have hsum : (a m) ((b n) v) + (b n) ((a m) v) = 0 := hN v m n hmn
    have hneg : (a m) ((b n) v) = -((b n) ((a m) v)) :=
      eq_neg_iff_add_eq_zero.mpr hsum
    simpa [odd, Parity.koszulSign] using hneg

end SuperFormalDistribution

namespace CARFamily

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The mode family underlying a CAR package, viewed as a formal distribution. -/
def toFormalDistribution (F : CARFamily (R := R) (V := V)) : FormalDistribution R V :=
  F.psi

@[simp] theorem toFormalDistribution_apply
    (F : CARFamily (R := R) (V := V)) (n : ℤ) :
    F.toFormalDistribution n = F.psi n := rfl

/-- CAR implies odd self-super-locality above total mode index `1`. -/
theorem superMutuallyLocal_odd_self
    (F : CARFamily (R := R) (V := V)) :
    SuperFormalDistribution.superMutuallyLocal (R := R) (V := V)
      (SuperFormalDistribution.odd (R := R) (V := V) F.toFormalDistribution)
      (SuperFormalDistribution.odd (R := R) (V := V) F.toFormalDistribution) := by
  refine ⟨1, ?_⟩
  intro v m n hmn
  have hne : m + n ≠ 0 := by omega
  have hanti : antiComm (R := R) (F.psi m) (F.psi n) = 0 :=
    F.anticommutator_offdiag (m := m) (n := n) hne
  have hanti_apply : (antiComm (R := R) (F.psi m) (F.psi n)) v = 0 := by
    simpa using congrArg (fun T : Module.End R V => T v) hanti
  have hsum : (F.psi m) ((F.psi n) v) + (F.psi n) ((F.psi m) v) = 0 := by
    simpa [antiComm, Module.End.mul_apply] using hanti_apply
  have hneg : (F.psi m) ((F.psi n) v) = -((F.psi n) ((F.psi m) v)) :=
    eq_neg_iff_add_eq_zero.mpr hsum
  simpa [SuperFormalDistribution.odd, toFormalDistribution, Parity.koszulSign] using hneg

/-- CAR gives eventual vanishing of the mode anticommutator above total index `1`. -/
theorem eventual_anticommutator_zero
    (F : CARFamily (R := R) (V := V)) :
    ∀ v : V, ∀ m n : ℤ, m + n ≥ 1 →
      (F.psi m) ((F.psi n) v) + (F.psi n) ((F.psi m) v) = 0 := by
  intro v m n hmn
  have hne : m + n ≠ 0 := by omega
  have hanti : antiComm (R := R) (F.psi m) (F.psi n) = 0 :=
    F.anticommutator_offdiag (m := m) (n := n) hne
  have hanti_apply : (antiComm (R := R) (F.psi m) (F.psi n)) v = 0 := by
    simpa using congrArg (fun T : Module.End R V => T v) hanti
  simpa [antiComm, Module.End.mul_apply] using hanti_apply

end CARFamily

end StringAlgebra.VOA
