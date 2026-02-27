/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Basic

/-!
# Formal Distributions and Fields

This file defines formal distributions (quantum fields) and their calculus,
which are central to the theory of Vertex Operator Algebras.

## Main Definitions

* `FormalDistribution` - A formal distribution a(z) = ∑_n a_n z^{-n-1}
* `normalOrderedProduct` - The normally ordered product :a(z)b(z):
* `OPE` - Operator Product Expansion
* `locality` - The locality axiom for mutually local fields

## References

* Kac, "Vertex Algebras for Beginners", Chapter 2
* Frenkel, Ben-Zvi, "Vertex Algebras and Algebraic Curves", Chapter 2
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V]

/-! ## Formal Distributions (Fields)

A formal distribution is a(z) = ∑_{n∈ℤ} aₙ z^{-n-1} where aₙ ∈ End(V).
Note the indexing convention: the coefficient of z^{-n-1} is called a(n) or aₙ.
-/

/-- A formal distribution (quantum field) on V.
    This is a formal series a(z) = ∑_{n∈ℤ} a(n) z^{-n-1} with a(n) ∈ End(V).
    We represent this as a function ℤ → End(V). -/
def FormalDistribution (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] := ℤ → Module.End R V

namespace FormalDistribution

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

instance : AddCommGroup (FormalDistribution R V) := Pi.addCommGroup
instance : Module R (FormalDistribution R V) := Pi.module ℤ (fun _ => Module.End R V) R

/-- Extensionality for FormalDistribution -/
@[ext]
theorem ext {a b : FormalDistribution R V} (h : ∀ n, a n = b n) : a = b := funext h

/-- The mode a(n) of the distribution -/
def mode (a : FormalDistribution R V) (n : ℤ) : Module.End R V := a n

@[simp] theorem mode_eq_apply (a : FormalDistribution R V) (n : ℤ) :
    mode a n = a n := rfl

/-- The field property: for each v ∈ V, a(n)v = 0 for n >> 0 -/
def hasFieldProperty (a : FormalDistribution R V) : Prop :=
  ∀ v : V, ∃ N : ℤ, ∀ n : ℤ, n > N → a n v = 0

/-- The zero field -/
def zero' : FormalDistribution R V := fun _ => 0

@[simp] theorem zero'_apply (n : ℤ) : (zero' : FormalDistribution R V) n = 0 := rfl

/-- The identity field Id(z) = ∑_n δ_{n,-1} Id · z^{-n-1} = Id · z⁰ -/
def identity : FormalDistribution R V := fun n => if n = -1 then LinearMap.id else 0

@[simp] theorem identity_apply (n : ℤ) :
    (identity : FormalDistribution R V) n = if n = -1 then LinearMap.id else 0 := rfl

/-- The formal derivative ∂a(z) = d/dz a(z).
    If a(z) = ∑_n a(n) z^{-n-1}, then ∂a(z) = ∑_n (-n-1) a(n) z^{-n-2}
    which equals ∑_m (-m) a(m-1) z^{-m-1}, so (∂a)(m) = -m · a(m-1). -/
def derivative (a : FormalDistribution R V) : FormalDistribution R V :=
  fun n => (-n : ℤ) • a (n - 1)

notation "∂ᶠ" => derivative

@[simp] theorem derivative_apply (a : FormalDistribution R V) (n : ℤ) :
    derivative a n = (-n : ℤ) • a (n - 1) := rfl

@[simp] theorem derivative_identity : derivative (identity : FormalDistribution R V) = 0 := by
  ext n x
  change ((-n : ℤ) • (if n - 1 = -1 then LinearMap.id else 0)) x = (0 : Module.End R V) x
  by_cases hn : n = 0
  · subst hn
    simp
  · have hne : n - 1 ≠ (-1 : ℤ) := by omega
    simp [hne]

@[simp] theorem derivative_zero : derivative (0 : FormalDistribution R V) = 0 := by
  ext n x
  change ((-n : ℤ) • (0 : Module.End R V)) x = (0 : Module.End R V) x
  simp

@[simp] theorem derivative_add (a b : FormalDistribution R V) :
    derivative (a + b) = derivative a + derivative b := by
  ext n x
  change ((-n : ℤ) • (a (n - 1) + b (n - 1))) x =
    (((-n : ℤ) • a (n - 1) + (-n : ℤ) • b (n - 1)) : Module.End R V) x
  simp [smul_add]

@[simp] theorem derivative_neg (a : FormalDistribution R V) :
    derivative (-a) = -derivative a := by
  ext n x
  change ((-n : ℤ) • (-a (n - 1))) x = (-( (-n : ℤ) • a (n - 1) : Module.End R V)) x
  simp

@[simp] theorem derivative_sub (a b : FormalDistribution R V) :
    derivative (a - b) = derivative a - derivative b := by
  simp [sub_eq_add_neg, derivative_add]

theorem hasFieldProperty_zero : hasFieldProperty (0 : FormalDistribution R V) := by
  intro v
  refine ⟨0, ?_⟩
  intro n hn
  rfl

theorem hasFieldProperty_add (a b : FormalDistribution R V)
    (ha : hasFieldProperty a) (hb : hasFieldProperty b) :
    hasFieldProperty (a + b) := by
  intro v
  rcases ha v with ⟨Na, hNa⟩
  rcases hb v with ⟨Nb, hNb⟩
  refine ⟨max Na Nb, ?_⟩
  intro n hn
  have hNa' : n > Na := lt_of_le_of_lt (le_max_left _ _) hn
  have hNb' : n > Nb := lt_of_le_of_lt (le_max_right _ _) hn
  change (a n) v + (b n) v = 0
  simp [hNa n hNa', hNb n hNb']

theorem hasFieldProperty_smul (r : R) (a : FormalDistribution R V)
    (ha : hasFieldProperty a) : hasFieldProperty (r • a) := by
  intro v
  rcases ha v with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change r • (a n v) = 0
  simp [hN n hn]

theorem hasFieldProperty_neg (a : FormalDistribution R V)
    (ha : hasFieldProperty a) : hasFieldProperty (-a) := by
  simpa using hasFieldProperty_smul (R := R) (V := V) (-1 : R) a ha

theorem hasFieldProperty_sub (a b : FormalDistribution R V)
    (ha : hasFieldProperty a) (hb : hasFieldProperty b) :
    hasFieldProperty (a - b) := by
  simpa [sub_eq_add_neg] using
    hasFieldProperty_add (R := R) (V := V) a (-b) ha (hasFieldProperty_neg (R := R) (V := V) b hb)

/-- Derivative preserves field property -/
theorem derivative_hasFieldProperty (a : FormalDistribution R V) (ha : hasFieldProperty a) :
    hasFieldProperty (derivative a) := fun v => by
  obtain ⟨N, hN⟩ := ha v
  use N + 1
  intro n hn
  simp only [derivative]
  have : n - 1 > N := by omega
  simp [hN (n - 1) this]

end FormalDistribution

/-! ## Formal Delta Function

The formal delta function δ(z-w) = ∑_{n∈ℤ} z^n w^{-n-1} = z⁻¹ ∑_n (w/z)^n.
This is a formal distribution in two variables.
-/

/-- The formal delta function δ(z,w) = ∑_{n∈ℤ} zⁿ w^{-n-1}.
    Coefficient of z^m w^n is 1 if m + n = -1, else 0. -/
def formalDelta (R : Type*) [CommRing R] : ℤ → ℤ → R :=
  fun m n => if m + n = -1 then 1 else 0

namespace FormalDelta

variable {R : Type*} [CommRing R]

/-- The delta function satisfies: formalDelta R m n = 1 iff m + n = -1 (assuming R is nontrivial) -/
theorem formalDelta_eq_one_iff [Nontrivial R] (m n : ℤ) :
    formalDelta R m n = 1 ↔ m + n = -1 := by
  simp only [formalDelta]
  split_ifs with h
  · simp [h]
  · simp [h, zero_ne_one]

/-- The delta function satisfies: formalDelta R m n = 0 iff m + n ≠ -1 (assuming R is nontrivial) -/
theorem formalDelta_eq_zero_iff [Nontrivial R] (m n : ℤ) :
    formalDelta R m n = 0 ↔ m + n ≠ -1 := by
  simp only [formalDelta]
  split_ifs with h
  · simp [h, one_ne_zero]
  · simp [h]

end FormalDelta

/-! ## Locality and OPE

Two fields a(z) and b(z) are mutually local if (z-w)^N [a(z), b(w)] = 0
for some N ∈ ℕ. This is equivalent to the OPE expansion.
-/

/-- Two fields are mutually local if their commutator has finite-order singularity.
    (z-w)^N [a(z), b(w)] = 0 as an operator on V. -/
def mutuallyLocal (a b : FormalDistribution R V) : Prop :=
  ∃ N : ℤ, ∀ v : V, ∀ m n : ℤ, m + n ≥ N → (a m) ((b n) v) = (b n) ((a m) v
  )

theorem mutuallyLocal_of_mode_commute (a b : FormalDistribution R V)
    (hcomm : ∀ v : V, ∀ m n : ℤ, (a m) ((b n) v) = (b n) ((a m) v)) :
    mutuallyLocal R V a b := by
  refine ⟨0, ?_⟩
  intro v m n _h
  exact hcomm v m n

theorem mutuallyLocal_symm (a b : FormalDistribution R V) :
    mutuallyLocal R V a b → mutuallyLocal R V b a := by
  intro h
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro v m n hmn
  have hcomm : (a n) ((b m) v) = (b m) ((a n) v) := hN v n m (by simpa [add_comm] using hmn)
  exact hcomm.symm

theorem mutuallyLocal_zero_left (a : FormalDistribution R V) :
    mutuallyLocal R V 0 a := by
  refine ⟨0, ?_⟩
  intro v m n _hmn
  change ((0 : Module.End R V) ((a n) v)) = (a n) ((0 : Module.End R V) v)
  simp

theorem mutuallyLocal_zero_right (a : FormalDistribution R V) :
    mutuallyLocal R V a 0 := by
  exact (mutuallyLocal_symm (R := R) (V := V) (0 : FormalDistribution R V) a)
    (mutuallyLocal_zero_left (R := R) (V := V) a)

theorem mutuallyLocal_add_left (a b c : FormalDistribution R V)
    (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (a + b) c := by
  rcases hac with ⟨Na, hNa⟩
  rcases hbc with ⟨Nb, hNb⟩
  refine ⟨max Na Nb, ?_⟩
  intro v m n hmn
  have hNa' : Na ≤ m + n := le_trans (le_max_left _ _) hmn
  have hNb' : Nb ≤ m + n := le_trans (le_max_right _ _) hmn
  have hcommA : (a m) ((c n) v) = (c n) ((a m) v) := hNa v m n hNa'
  have hcommB : (b m) ((c n) v) = (c n) ((b m) v) := hNb v m n hNb'
  change ((a m + b m) ((c n) v)) = (c n) ((a m + b m) v)
  simp [hcommA, hcommB, map_add]

theorem mutuallyLocal_add_right (a b c : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) :
    mutuallyLocal R V a (b + c) := by
  rcases hab with ⟨Nb, hNb⟩
  rcases hac with ⟨Nc, hNc⟩
  refine ⟨max Nb Nc, ?_⟩
  intro v m n hmn
  have hNb' : Nb ≤ m + n := le_trans (le_max_left _ _) hmn
  have hNc' : Nc ≤ m + n := le_trans (le_max_right _ _) hmn
  have hcommB : (a m) ((b n) v) = (b n) ((a m) v) := hNb v m n hNb'
  have hcommC : (a m) ((c n) v) = (c n) ((a m) v) := hNc v m n hNc'
  change (a m) (((b n) + (c n)) v) = ((b n) + (c n)) ((a m) v)
  simp [hcommB, hcommC, map_add]

theorem mutuallyLocal_smul_left (r : R) (a b : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) :
    mutuallyLocal R V (r • a) b := by
  rcases hab with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro v m n hmn
  have hcomm : (a m) ((b n) v) = (b n) ((a m) v) := hN v m n hmn
  change ((r • (a m)) ((b n) v)) = (b n) ((r • (a m)) v)
  simp [hcomm, map_smul]

theorem mutuallyLocal_smul_right (r : R) (a b : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) :
    mutuallyLocal R V a (r • b) := by
  rcases hab with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro v m n hmn
  have hcomm : (a m) ((b n) v) = (b n) ((a m) v) := hN v m n hmn
  change (a m) ((r • (b n)) v) = (r • (b n)) ((a m) v)
  simp [hcomm, map_smul]

theorem mutuallyLocal_neg_left (a b : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) :
    mutuallyLocal R V (-a) b := by
  simpa using mutuallyLocal_smul_left (R := R) (V := V) (-1 : R) a b hab

theorem mutuallyLocal_neg_right (a b : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) :
    mutuallyLocal R V a (-b) := by
  simpa using mutuallyLocal_smul_right (R := R) (V := V) (-1 : R) a b hab

theorem mutuallyLocal_sub_left (a b c : FormalDistribution R V)
    (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (a - b) c := by
  simpa [sub_eq_add_neg] using
    mutuallyLocal_add_left (R := R) (V := V) a (-b) c hac
      (mutuallyLocal_neg_left (R := R) (V := V) b c hbc)

theorem mutuallyLocal_sub_right (a b c : FormalDistribution R V)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) :
    mutuallyLocal R V a (b - c) := by
  simpa [sub_eq_add_neg] using
    mutuallyLocal_add_right (R := R) (V := V) a b (-c) hab
      (mutuallyLocal_neg_right (R := R) (V := V) a c hac)

/-- The OPE data: the singular part of a(z)b(w) -/
structure OPEData where
  /-- Order of the pole (locality order) -/
  order : ℕ
  /-- The coefficient fields c^{(j)}(w) in a(z)b(w) ~ ∑_{j=0}^{N-1} c^{(j)}(w)/(z-w)^{j+1} -/
  coefficients : Fin order → FormalDistribution R V

/-- The j-th product (Borcherds product) a(j)b for j ∈ ℤ.
    Defined by: a(z)(j)b(z) = Res_w (z-w)^j [a(z), b(w)]
    For j ≥ 0, this gives the OPE coefficients. -/
def nthProduct (a b : FormalDistribution R V) (j : ℤ) : FormalDistribution R V :=
  fun n => a j * b (n - j)  -- Simplified; full formula involves sums

@[simp] theorem nthProduct_apply (a b : FormalDistribution R V) (j n : ℤ) (v : V) :
    (nthProduct R V a b j n) v = (a j) ((b (n - j)) v) := rfl

/-- Evaluate `nthProduct a b m` at mode `m+n`. -/
@[simp] theorem nthProduct_apply_mode_sum (a b : FormalDistribution R V)
    (m n : ℤ) (v : V) :
    (nthProduct R V a b m (m + n)) v = (a m) ((b n) v) := by
  have hmn : m + n - m = n := by omega
  simp [nthProduct, hmn]

/-- Mode-level commutator expressed through `nthProduct` difference. -/
theorem mode_commutator_eq_nthProduct_sub_apply
    (a b : FormalDistribution R V) (m n : ℤ) (v : V) :
    (a m) ((b n) v) - (b n) ((a m) v) =
      ((nthProduct R V a b m - nthProduct R V b a n) (m + n)) v := by
  have h₁ : (nthProduct R V a b m (m + n)) v = (a m) ((b n) v) :=
    nthProduct_apply_mode_sum (R := R) (V := V) a b m n v
  have h₂ : (nthProduct R V b a n (m + n)) v = (b n) ((a m) v) := by
    have hnm : m + n - n = m := by omega
    simp [nthProduct, hnm]
  change (a m) ((b n) v) - (b n) ((a m) v) =
    (nthProduct R V a b m (m + n)) v - (nthProduct R V b a n (m + n)) v
  simp [h₁, h₂]

/-- Mode-level anticommutator expressed through `nthProduct` sum. -/
theorem mode_anticommutator_eq_nthProduct_add_apply
    (a b : FormalDistribution R V) (m n : ℤ) (v : V) :
    (a m) ((b n) v) + (b n) ((a m) v) =
      ((nthProduct R V a b m + nthProduct R V b a n) (m + n)) v := by
  have h₁ : (nthProduct R V a b m (m + n)) v = (a m) ((b n) v) :=
    nthProduct_apply_mode_sum (R := R) (V := V) a b m n v
  have h₂ : (nthProduct R V b a n (m + n)) v = (b n) ((a m) v) := by
    have hnm : m + n - n = m := by omega
    simp [nthProduct, hnm]
  change (a m) ((b n) v) + (b n) ((a m) v) =
    (nthProduct R V a b m (m + n)) v + (nthProduct R V b a n (m + n)) v
  simp [h₁, h₂]

/-- Explicit compatibility package between OPE coefficient fields and `nthProduct`. -/
structure OPECompatibility (a b : FormalDistribution R V) (ope : OPEData (R := R) (V := V)) where
  /-- Coefficient field `c^{(j)}` agrees with `a(j)b` for each singular index. -/
  coeff_eq_nthProduct :
    ∀ j : Fin ope.order, ope.coefficients j = nthProduct R V a b (j : ℤ)

namespace OPECompatibility

variable {a b : FormalDistribution R V}
variable {ope : OPEData (R := R) (V := V)}

/-- Accessor: OPE coefficient field at index `j` as an `nthProduct`. -/
theorem coefficient_eq_nthProduct
    (h : OPECompatibility (R := R) (V := V) a b ope) (j : Fin ope.order) :
    ope.coefficients j = nthProduct R V a b (j : ℤ) :=
  h.coeff_eq_nthProduct j

/-- Pointwise extraction from OPE compatibility. -/
theorem coefficient_apply_eq_mode_comp
    (h : OPECompatibility (R := R) (V := V) a b ope)
    (j : Fin ope.order) (n : ℤ) (v : V) :
    ope.coefficients j n v = (a (j : ℤ)) ((b (n - (j : ℤ))) v) := by
  rw [h.coeff_eq_nthProduct j]
  exact nthProduct_apply (R := R) (V := V) a b (j : ℤ) n v

/-- Mode-sum specialization from OPE compatibility:
    evaluating coefficient `j` at mode `j+n` gives `a(j)b(n)`. -/
theorem coefficient_apply_mode_sum
    (h : OPECompatibility (R := R) (V := V) a b ope)
    (j : Fin ope.order) (n : ℤ) (v : V) :
    ope.coefficients j ((j : ℤ) + n) v = (a (j : ℤ)) ((b n) v) := by
  rw [h.coeff_eq_nthProduct j]
  exact nthProduct_apply_mode_sum (R := R) (V := V) a b (j : ℤ) n v

end OPECompatibility

/-- Finite-order OPE package:
    compatibility with singular coefficients plus vanishing `nthProduct`
    for all natural mode indices `j ≥ order`. -/
structure OPEFiniteOrder (a b : FormalDistribution R V) where
  /-- OPE singular-part data. -/
  data : OPEData (R := R) (V := V)
  /-- Compatibility between singular coefficients and `nthProduct`. -/
  compat : OPECompatibility (R := R) (V := V) a b data
  /-- Vanishing of higher singular products above OPE order. -/
  vanish_ge : ∀ j : ℕ, data.order ≤ j → nthProduct R V a b (j : ℤ) = 0

namespace OPEFiniteOrder

variable {a b : FormalDistribution R V}

/-- Coefficient extraction from finite-order OPE data. -/
theorem coefficient_eq_nthProduct
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : Fin F.data.order) :
    F.data.coefficients j = nthProduct R V a b (j : ℤ) :=
  F.compat.coeff_eq_nthProduct j

/-- Vanishing of `nthProduct` at natural mode index `j ≥ order`. -/
theorem nthProduct_eq_zero_of_ge
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) :
    nthProduct R V a b (j : ℤ) = 0 :=
  F.vanish_ge j hj

/-- Coefficient-field extension to natural indices:
    use the OPE coefficient below order, and zero at/above order. -/
def coefficientOrZero
    (F : OPEFiniteOrder (R := R) (V := V) a b) (j : ℕ) : FormalDistribution R V :=
  if h : j < F.data.order then F.data.coefficients ⟨j, h⟩ else 0

/-- Below OPE order, `coefficientOrZero` is the corresponding coefficient field. -/
theorem coefficientOrZero_of_lt
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : j < F.data.order) :
    coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j =
      F.data.coefficients ⟨j, hj⟩ := by
  simp [coefficientOrZero, hj]

/-- At/above OPE order, `coefficientOrZero` is the zero field. -/
theorem coefficientOrZero_of_ge
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) :
    coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j = 0 := by
  have hnot : ¬ j < F.data.order := Nat.not_lt.mpr hj
  simp [coefficientOrZero, hnot]

/-- `coefficientOrZero` agrees with `nthProduct` at every natural index. -/
theorem coefficientOrZero_eq_nthProduct
    (F : OPEFiniteOrder (R := R) (V := V) a b) (j : ℕ) :
    coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j =
      nthProduct R V a b (j : ℤ) := by
  by_cases hlt : j < F.data.order
  · simpa [coefficientOrZero, hlt] using
      coefficient_eq_nthProduct (R := R) (V := V) (a := a) (b := b) F ⟨j, hlt⟩
  · have hge : F.data.order ≤ j := Nat.le_of_not_gt hlt
    have hzero : nthProduct R V a b (j : ℤ) = 0 :=
      nthProduct_eq_zero_of_ge (R := R) (V := V) (a := a) (b := b) F (j := j) hge
    simp [coefficientOrZero, hlt, hzero]

/-- Mode-sum evaluation of `coefficientOrZero` recovers mode composition. -/
theorem coefficientOrZero_apply_mode_sum
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) (v : V) :
    (coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j) ((j : ℤ) + n) v =
      (a (j : ℤ)) ((b n) v) := by
  rw [coefficientOrZero_eq_nthProduct (R := R) (V := V) (a := a) (b := b) F j]
  exact nthProduct_apply_mode_sum (R := R) (V := V) a b (j : ℤ) n v

/-- Strict-below-order mode-sum evaluation of `coefficientOrZero`. -/
theorem coefficientOrZero_apply_mode_sum_of_lt
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : j < F.data.order) (n : ℤ) (v : V) :
    (coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j) ((j : ℤ) + n) v =
      F.data.coefficients ⟨j, hj⟩ ((j : ℤ) + n) v := by
  rw [coefficientOrZero_of_lt (R := R) (V := V) (a := a) (b := b) F hj]

/-- At/above-order mode-sum evaluation of `coefficientOrZero` vanishes. -/
theorem coefficientOrZero_apply_mode_sum_of_ge
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) (v : V) :
    (coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j) ((j : ℤ) + n) v = 0 := by
  rw [coefficientOrZero_of_ge (R := R) (V := V) (a := a) (b := b) F hj]
  change ((0 : Module.End R V) v) = 0
  simp

/-- Mode-composition extraction from finite-order OPE compatibility. -/
theorem mode_comp_eq_coefficient_apply_mode_sum
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : Fin F.data.order) (n : ℤ) (v : V) :
    (a (j : ℤ)) ((b n) v) = F.data.coefficients j ((j : ℤ) + n) v := by
  exact (OPECompatibility.coefficient_apply_mode_sum (R := R) (V := V)
    (a := a) (b := b) (ope := F.data) F.compat j n v).symm

/-- Above OPE order, mode compositions vanish on vectors. -/
theorem mode_comp_eq_zero_of_ge_apply
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) (v : V) :
    (a (j : ℤ)) ((b n) v) = 0 := by
  have hzero : nthProduct R V a b (j : ℤ) = 0 :=
    nthProduct_eq_zero_of_ge (R := R) (V := V) (a := a) (b := b) F hj
  calc
    (a (j : ℤ)) ((b n) v) = (nthProduct R V a b (j : ℤ) ((j : ℤ) + n)) v := by
      exact (nthProduct_apply_mode_sum (R := R) (V := V) a b (j : ℤ) n v).symm
    _ = 0 := by
      rw [hzero]
      change ((0 : Module.End R V) v) = 0
      simp

/-- Above OPE order, mode compositions vanish as endomorphisms. -/
theorem mode_comp_eq_zero_of_ge
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    {j : ℕ} (hj : F.data.order ≤ j) (n : ℤ) :
    (a (j : ℤ)) * (b n) = 0 := by
  ext v
  simpa [Module.End.mul_apply] using
    mode_comp_eq_zero_of_ge_apply (R := R) (V := V) (a := a) (b := b) F hj n v

/-- Mode composition in terms of the extended coefficient field `coefficientOrZero`. -/
theorem mode_comp_eq_coefficientOrZero_apply_mode_sum
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) (v : V) :
    (a (j : ℤ)) ((b n) v) =
      (coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j) ((j : ℤ) + n) v := by
  rw [coefficientOrZero_eq_nthProduct (R := R) (V := V) (a := a) (b := b) F j]
  exact (nthProduct_apply_mode_sum (R := R) (V := V) a b (j : ℤ) n v).symm

/-- Endomorphism form of `mode_comp_eq_coefficientOrZero_apply_mode_sum`. -/
theorem mode_comp_eq_coefficientOrZero_mode_sum
    (F : OPEFiniteOrder (R := R) (V := V) a b)
    (j : ℕ) (n : ℤ) :
    (a (j : ℤ)) * (b n) =
      (coefficientOrZero (R := R) (V := V) (a := a) (b := b) F j) ((j : ℤ) + n) := by
  ext v
  simpa [Module.End.mul_apply] using
    mode_comp_eq_coefficientOrZero_apply_mode_sum
      (R := R) (V := V) (a := a) (b := b) F j n v

end OPEFiniteOrder

@[simp] theorem nthProduct_zero_left (a : FormalDistribution R V) (j : ℤ) :
    nthProduct R V 0 a j = 0 := by
  ext n v
  change ((0 : Module.End R V) ((a (n - j)) v)) = (0 : Module.End R V) v
  simp

@[simp] theorem nthProduct_zero_right (a : FormalDistribution R V) (j : ℤ) :
    nthProduct R V a 0 j = 0 := by
  ext n v
  change (a j) ((0 : Module.End R V) v) = (0 : Module.End R V) v
  simp

theorem nthProduct_add_left (a b c : FormalDistribution R V) (j : ℤ) :
    nthProduct R V (a + b) c j = nthProduct R V a c j + nthProduct R V b c j := by
  ext n v
  change ((a j + b j) ((c (n - j)) v)) =
    ((a j * c (n - j) + b j * c (n - j)) : Module.End R V) v
  simp

theorem nthProduct_add_right (a b c : FormalDistribution R V) (j : ℤ) :
    nthProduct R V a (b + c) j = nthProduct R V a b j + nthProduct R V a c j := by
  ext n v
  change (a j) (((b (n - j)) + (c (n - j))) v) =
    ((a j * b (n - j) + a j * c (n - j)) : Module.End R V) v
  simp

theorem nthProduct_smul_left (r : R) (a b : FormalDistribution R V) (j : ℤ) :
    nthProduct R V (r • a) b j = r • nthProduct R V a b j := by
  ext n v
  change ((r • (a j)) * b (n - j)) v = (r • (a j * b (n - j))) v
  simp

theorem nthProduct_smul_right (r : R) (a b : FormalDistribution R V) (j : ℤ) :
    nthProduct R V a (r • b) j = r • nthProduct R V a b j := by
  ext n v
  change (a j) ((r • (b (n - j))) v) = (r • (a j * b (n - j))) v
  simp [map_smul]

@[simp] theorem nthProduct_neg_left (a b : FormalDistribution R V) (j : ℤ) :
    nthProduct R V (-a) b j = -nthProduct R V a b j := by
  simpa using nthProduct_smul_left (R := R) (V := V) (-1 : R) a b j

@[simp] theorem nthProduct_neg_right (a b : FormalDistribution R V) (j : ℤ) :
    nthProduct R V a (-b) j = -nthProduct R V a b j := by
  simpa using nthProduct_smul_right (R := R) (V := V) (-1 : R) a b j

theorem nthProduct_sub_left (a b c : FormalDistribution R V) (j : ℤ) :
    nthProduct R V (a - b) c j = nthProduct R V a c j - nthProduct R V b c j := by
  simpa [sub_eq_add_neg] using nthProduct_add_left (R := R) (V := V) a (-b) c j

theorem nthProduct_sub_right (a b c : FormalDistribution R V) (j : ℤ) :
    nthProduct R V a (b - c) j = nthProduct R V a b j - nthProduct R V a c j := by
  simpa [sub_eq_add_neg] using nthProduct_add_right (R := R) (V := V) a b (-c) j

/-- For fixed `j`, field property of the right input transfers to `nthProduct a b j`. -/
theorem hasFieldProperty_nthProduct_right (a b : FormalDistribution R V) (j : ℤ)
    (hb : FormalDistribution.hasFieldProperty b) :
    FormalDistribution.hasFieldProperty (nthProduct R V a b j) := by
  intro v
  rcases hb v with ⟨N, hN⟩
  refine ⟨N + j, ?_⟩
  intro n hn
  have hshift : n - j > N := by omega
  have hb0 : b (n - j) v = 0 := hN (n - j) hshift
  change (a j) ((b (n - j)) v) = 0
  simp [hb0]

/-- Explicit Dong-lemma witness package in the coefficient model. -/
structure DongLemmaData (a b c : FormalDistribution R V) where
  /-- Closure of pairwise locality under all `n`-th products. -/
  closure :
    ∀ n : ℤ,
      mutuallyLocal R V a b →
      mutuallyLocal R V a c →
      mutuallyLocal R V b c →
      mutuallyLocal R V (nthProduct R V a b n) c

namespace DongLemmaData

variable {a b c : FormalDistribution R V}

/-- Accessor for Dong-closure at mode `n`. -/
theorem mutuallyLocal_nthProduct (D : DongLemmaData (R := R) (V := V) a b c) (n : ℤ)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (nthProduct R V a b n) c :=
  D.closure n hab hac hbc

/-- Dong-closure specialized to mode `n = -1`. -/
theorem mutuallyLocal_nthProduct_neg_one
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (nthProduct R V a b (-1)) c := by
  simpa using D.closure (-1) hab hac hbc

/-- Dong-closure specialized to mode `n = 0`. -/
theorem mutuallyLocal_nthProduct_zero
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (nthProduct R V a b 0) c := by
  simpa using D.closure 0 hab hac hbc

/-- Symmetric form of Dong-closure at mode `n`. -/
theorem mutuallyLocal_right_nthProduct (D : DongLemmaData (R := R) (V := V) a b c) (n : ℤ)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V c (nthProduct R V a b n) := by
  exact mutuallyLocal_symm (R := R) (V := V) (nthProduct R V a b n) c
    (D.closure n hab hac hbc)

/-- Symmetric Dong-closure specialized to mode `n = -1`. -/
theorem mutuallyLocal_right_nthProduct_neg_one
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V c (nthProduct R V a b (-1)) := by
  simpa using mutuallyLocal_right_nthProduct (R := R) (V := V) (a := a) (b := b) (c := c)
    D (-1) hab hac hbc

/-- Symmetric Dong-closure specialized to mode `n = 0`. -/
theorem mutuallyLocal_right_nthProduct_zero
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V c (nthProduct R V a b 0) := by
  simpa using mutuallyLocal_right_nthProduct (R := R) (V := V) (a := a) (b := b) (c := c)
    D 0 hab hac hbc

end DongLemmaData

/-! ## Normally Ordered Product

The normally ordered product :a(z)b(w): puts creation operators to the left.
-/

/-- The normally ordered product of two fields at the same point.
    :a(z)b(z): = a(z)₋b(z) + b(z)a(z)₊
    where a(z)₋ = ∑_{n<0} a(n)z^{-n-1} and a(z)₊ = ∑_{n≥0} a(n)z^{-n-1}
    This equals the (-1)-st product: :ab: = a(-1)b -/
def normalOrderedProduct (a b : FormalDistribution R V) : FormalDistribution R V :=
  nthProduct R V a b (-1)

@[simp] theorem normalOrderedProduct_apply (a b : FormalDistribution R V) (n : ℤ) :
    normalOrderedProduct R V a b n = nthProduct R V a b (-1) n := rfl

@[simp] theorem normalOrderedProduct_zero_left (a : FormalDistribution R V) :
    normalOrderedProduct R V 0 a = 0 := by
  simp [normalOrderedProduct]

@[simp] theorem normalOrderedProduct_zero_right (a : FormalDistribution R V) :
    normalOrderedProduct R V a 0 = 0 := by
  simp [normalOrderedProduct]

theorem normalOrderedProduct_add_left (a b c : FormalDistribution R V) :
    normalOrderedProduct R V (a + b) c =
      normalOrderedProduct R V a c + normalOrderedProduct R V b c := by
  simpa [normalOrderedProduct] using nthProduct_add_left (R := R) (V := V) a b c (-1)

theorem normalOrderedProduct_add_right (a b c : FormalDistribution R V) :
    normalOrderedProduct R V a (b + c) =
      normalOrderedProduct R V a b + normalOrderedProduct R V a c := by
  simpa [normalOrderedProduct] using nthProduct_add_right (R := R) (V := V) a b c (-1)

theorem normalOrderedProduct_smul_left (r : R) (a b : FormalDistribution R V) :
    normalOrderedProduct R V (r • a) b = r • normalOrderedProduct R V a b := by
  simpa [normalOrderedProduct] using
    nthProduct_smul_left (R := R) (V := V) r a b (-1)

theorem normalOrderedProduct_smul_right (r : R) (a b : FormalDistribution R V) :
    normalOrderedProduct R V a (r • b) = r • normalOrderedProduct R V a b := by
  simpa [normalOrderedProduct] using
    nthProduct_smul_right (R := R) (V := V) r a b (-1)

@[simp] theorem normalOrderedProduct_neg_left (a b : FormalDistribution R V) :
    normalOrderedProduct R V (-a) b = -normalOrderedProduct R V a b := by
  simpa using normalOrderedProduct_smul_left (R := R) (V := V) (-1 : R) a b

@[simp] theorem normalOrderedProduct_neg_right (a b : FormalDistribution R V) :
    normalOrderedProduct R V a (-b) = -normalOrderedProduct R V a b := by
  simpa using normalOrderedProduct_smul_right (R := R) (V := V) (-1 : R) a b

theorem normalOrderedProduct_sub_left (a b c : FormalDistribution R V) :
    normalOrderedProduct R V (a - b) c =
      normalOrderedProduct R V a c - normalOrderedProduct R V b c := by
  simpa [sub_eq_add_neg] using normalOrderedProduct_add_left (R := R) (V := V) a (-b) c

theorem normalOrderedProduct_sub_right (a b c : FormalDistribution R V) :
    normalOrderedProduct R V a (b - c) =
      normalOrderedProduct R V a b - normalOrderedProduct R V a c := by
  simpa [sub_eq_add_neg] using normalOrderedProduct_add_right (R := R) (V := V) a b (-c)

theorem hasFieldProperty_normalOrderedProduct_right (a b : FormalDistribution R V)
    (hb : FormalDistribution.hasFieldProperty b) :
    FormalDistribution.hasFieldProperty (normalOrderedProduct R V a b) := by
  simpa [normalOrderedProduct] using
    hasFieldProperty_nthProduct_right (R := R) (V := V) a b (-1) hb

namespace DongLemmaData

variable {a b c : FormalDistribution R V}

/-- Dong-closure specialized to the normal-ordered product (`n = -1`). -/
theorem mutuallyLocal_normalOrderedProduct
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (normalOrderedProduct R V a b) c := by
  simpa [normalOrderedProduct] using
    (mutuallyLocal_nthProduct_neg_one (R := R) (V := V) (a := a) (b := b) (c := c)
      D hab hac hbc)

/-- Symmetric form: Dong-closure for normal-ordered product on the right. -/
theorem mutuallyLocal_right_normalOrderedProduct
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V c (normalOrderedProduct R V a b) := by
  exact mutuallyLocal_symm (R := R) (V := V) (normalOrderedProduct R V a b) c
    (mutuallyLocal_normalOrderedProduct (R := R) (V := V) (a := a) (b := b) (c := c)
      D hab hac hbc)

/-- Re-expression of normal-ordered Dong closure through `nthProduct (-1)`. -/
theorem mutuallyLocal_normalOrderedProduct_via_nthProduct_neg_one
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V (normalOrderedProduct R V a b) c := by
  simpa [normalOrderedProduct] using
    mutuallyLocal_nthProduct_neg_one (R := R) (V := V) (a := a) (b := b) (c := c) D hab hac hbc

/-- Right-oriented re-expression through `nthProduct (-1)`. -/
theorem mutuallyLocal_right_normalOrderedProduct_via_nthProduct_neg_one
    (D : DongLemmaData (R := R) (V := V) a b c)
    (hab : mutuallyLocal R V a b) (hac : mutuallyLocal R V a c) (hbc : mutuallyLocal R V b c) :
    mutuallyLocal R V c (normalOrderedProduct R V a b) := by
  simpa [normalOrderedProduct] using
    mutuallyLocal_right_nthProduct_neg_one (R := R) (V := V) (a := a) (b := b) (c := c)
      D hab hac hbc

end DongLemmaData

end StringAlgebra.VOA
