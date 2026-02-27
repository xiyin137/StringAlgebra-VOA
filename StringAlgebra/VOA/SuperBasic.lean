/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Basic

/-!
# Super VOA Basic Infrastructure

This file introduces minimal super-algebra infrastructure used by free-fermion
formalizations:

1. parity values (`even` / `odd`),
2. Koszul sign conventions,
3. graded commutator/anticommutator operators on endomorphisms,
4. a CAR mode-family interface for fermionic modes.

The layer is purely algebraic and independent of analytic convergence.
-/

namespace StringAlgebra.VOA

/-- A parity value for super-algebra gradings. -/
inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

instance : Inhabited Parity := ⟨even⟩
instance : Zero Parity := ⟨even⟩

/-- Addition of parities (mod 2). -/
def add : Parity → Parity → Parity
  | even, p => p
  | odd, even => odd
  | odd, odd => even

instance : Add Parity := ⟨add⟩

@[simp] theorem even_add (p : Parity) : even + p = p := rfl
@[simp] theorem add_even : ∀ p : Parity, p + even = p
  | even => rfl
  | odd => rfl
@[simp] theorem odd_add_even : odd + even = odd := rfl
@[simp] theorem odd_add_odd : odd + odd = even := rfl

theorem add_assoc (a b c : Parity) : (a + b) + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_comm (a b : Parity) : a + b = b + a := by
  cases a <;> cases b <;> rfl

/-- Multiplication of parities (logical AND), used for Koszul signs. -/
def mul : Parity → Parity → Parity
  | odd, odd => odd
  | _, _ => even

instance : Mul Parity := ⟨mul⟩

@[simp] theorem even_mul (p : Parity) : even * p = even := by
  cases p <;> rfl
@[simp] theorem mul_even (p : Parity) : p * even = even := by
  cases p <;> rfl
@[simp] theorem odd_mul_odd : odd * odd = odd := rfl
@[simp] theorem odd_mul_even : odd * even = even := rfl
@[simp] theorem even_mul_odd : even * odd = even := rfl

theorem mul_comm (a b : Parity) : a * b = b * a := by
  cases a <;> cases b <;> rfl

theorem mul_assoc (a b c : Parity) : (a * b) * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> rfl

variable (R : Type*) [Ring R]

/-- `(-1)^p` for parity `p`. -/
def sign : Parity → R
  | even => 1
  | odd => -1

/-- Koszul sign `(-1)^{pq}` for parities `p,q`. -/
def koszulSign (p q : Parity) : R :=
  sign (R := R) (p * q)

@[simp] theorem sign_even : sign (R := R) even = (1 : R) := rfl
@[simp] theorem sign_odd : sign (R := R) odd = (-1 : R) := rfl

@[simp] theorem koszulSign_even_left (q : Parity) :
    koszulSign (R := R) even q = 1 := by
  cases q <;> rfl

@[simp] theorem koszulSign_even_right (p : Parity) :
    koszulSign (R := R) p even = 1 := by
  cases p <;> rfl

@[simp] theorem koszulSign_odd_odd :
    koszulSign (R := R) odd odd = (-1 : R) := rfl

theorem koszulSign_symm (p q : Parity) :
    koszulSign (R := R) p q = koszulSign (R := R) q p := by
  cases p <;> cases q <;> rfl

theorem koszulSign_mul_self (p q : Parity) :
    koszulSign (R := R) p q * koszulSign (R := R) p q = 1 := by
  cases p <;> cases q <;> simp [koszulSign, sign]

end Parity

/-- A parity grading on a type. -/
class SuperGraded (A : Type*) where
  parity : A → Parity

namespace SuperGraded

variable {A : Type*} [SuperGraded A]

/-- Predicate for even homogeneous parity. -/
def IsEven (a : A) : Prop :=
  SuperGraded.parity a = Parity.even

/-- Predicate for odd homogeneous parity. -/
def IsOdd (a : A) : Prop :=
  SuperGraded.parity a = Parity.odd

theorem isEven_or_isOdd (a : A) : IsEven a ∨ IsOdd a := by
  cases h : SuperGraded.parity a <;> simp [IsEven, IsOdd, h]

theorem not_isEven_iff_isOdd (a : A) : ¬ IsEven a ↔ IsOdd a := by
  cases h : SuperGraded.parity a <;> simp [IsEven, IsOdd, h]

theorem not_isOdd_iff_isEven (a : A) : ¬ IsOdd a ↔ IsEven a := by
  cases h : SuperGraded.parity a <;> simp [IsEven, IsOdd, h]

end SuperGraded

/-- Multiplication-compatible super grading: `|ab| = |a| + |b|`. -/
class SuperMul (A : Type*) [Mul A] extends SuperGraded A where
  parity_mul : ∀ a b : A, parity (a * b) = parity a + parity b

namespace SuperMul

variable {A : Type*} [Mul A] [SuperMul A]

@[simp] theorem parity_mul_eq (a b : A) :
    SuperGraded.parity (a * b) = SuperGraded.parity a + SuperGraded.parity b :=
  SuperMul.parity_mul a b

theorem parity_mul_mul (a b c : A) :
    SuperGraded.parity ((a * b) * c) =
      SuperGraded.parity a + SuperGraded.parity b + SuperGraded.parity c := by
  simp [parity_mul_eq, Parity.add_assoc]

end SuperMul

section Endomorphisms

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The anticommutator `{f,g} = fg + gf` on endomorphisms. -/
def antiComm (f g : Module.End R V) : Module.End R V :=
  f * g + g * f

/-- Graded commutator `[f,g]_± = fg - (-1)^{|f||g|} gf`. -/
def gradedComm (pf pg : Parity) (f g : Module.End R V) : Module.End R V :=
  f * g - (Parity.koszulSign (R := R) pf pg) • (g * f)

@[simp] theorem antiComm_symm (f g : Module.End R V) :
    antiComm (R := R) f g = antiComm (R := R) g f := by
  simp [antiComm, add_comm]

@[simp] theorem gradedComm_even_left (pg : Parity) (f g : Module.End R V) :
    gradedComm (R := R) Parity.even pg f g = f * g - g * f := by
  cases pg <;> simp [gradedComm, Parity.koszulSign]

@[simp] theorem gradedComm_even_right (pf : Parity) (f g : Module.End R V) :
    gradedComm (R := R) pf Parity.even f g = f * g - g * f := by
  cases pf <;> simp [gradedComm, Parity.koszulSign]

@[simp] theorem gradedComm_odd_odd (f g : Module.End R V) :
    gradedComm (R := R) Parity.odd Parity.odd f g = antiComm (R := R) f g := by
  simp [gradedComm, antiComm, Parity.koszulSign]

/-- CAR mode-family package: `{ψ_m, ψ_n} = c δ_{m,-n} Id`. -/
structure CARFamily where
  /-- Fermionic modes `ψ_n`. -/
  psi : ℤ → Module.End R V
  /-- Normalization constant `c` in the CAR relation. -/
  normalization : R := 1
  /-- Canonical anticommutator relation. -/
  anticommutator_spec :
    ∀ m n : ℤ,
      antiComm (R := R) (psi m) (psi n) =
        if m + n = 0 then normalization • (LinearMap.id : Module.End R V) else 0

namespace CARFamily

@[simp] theorem anticommutator
    (F : CARFamily (R := R) (V := V)) (m n : ℤ) :
    antiComm (R := R) (F.psi m) (F.psi n) =
      if m + n = 0 then F.normalization • (LinearMap.id : Module.End R V) else 0 :=
  F.anticommutator_spec m n

theorem anticommutator_offdiag
    (F : CARFamily (R := R) (V := V)) {m n : ℤ} (h : m + n ≠ 0) :
    antiComm (R := R) (F.psi m) (F.psi n) = 0 := by
  simp [F.anticommutator_spec, h]

theorem anticommutator_diag
    (F : CARFamily (R := R) (V := V)) (m : ℤ) :
    antiComm (R := R) (F.psi m) (F.psi (-m)) =
      F.normalization • (LinearMap.id : Module.End R V) := by
  simp [F.anticommutator_spec]

theorem anticommutator_diag_symm
    (F : CARFamily (R := R) (V := V)) (m : ℤ) :
    antiComm (R := R) (F.psi (-m)) (F.psi m) =
      F.normalization • (LinearMap.id : Module.End R V) := by
  simp

end CARFamily

end Endomorphisms

end StringAlgebra.VOA
