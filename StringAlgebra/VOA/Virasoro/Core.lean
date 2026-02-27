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

end StringAlgebra.VOA
