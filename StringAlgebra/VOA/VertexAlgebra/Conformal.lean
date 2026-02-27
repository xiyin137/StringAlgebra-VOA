/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra.Core

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Conformal Vertex Algebra -/

/-- A conformal vertex algebra is a vertex algebra with a conformal vector ω.
    The Virasoro relation is stated in the scaled form:
    12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n}
    to avoid division in a general CommRing. -/
class ConformalVertexAlgebra (V : Type*) [AddCommGroup V] [Module R V]
    extends VertexAlgebra R V where
  /-- The conformal vector ω -/
  conformalVector : V
  /-- The central charge c -/
  centralCharge : R
  /-- L(-1) = T (translation generator) -/
  L_minus1_eq_translation : (Y conformalVector) 0 = translation
  /-- L(0) gives the grading (conformal weight) -/
  L0_grading : ∃ (weight : V → ℤ), ∀ a : V,
    (Y conformalVector) 1 a = (weight a : ℤ) • a
  /-- Virasoro relations (scaled by 12 to avoid division):
      12[L_m, L_n] = 12(m-n)L_{m+n} + c·m(m²-1)δ_{m,-n}
      With L_n = ω(n+1), this becomes a relation on ω modes. -/
  virasoro_relation : ∀ m n : ℤ,
    (12 : R) • ((Y conformalVector) (m + 1) ∘ₗ (Y conformalVector) (n + 1) -
    (Y conformalVector) (n + 1) ∘ₗ (Y conformalVector) (m + 1)) =
    (12 : R) • ((m - n : ℤ) • (Y conformalVector) (m + n + 1)) +
    if m + n = 0 then (centralCharge * (m^3 - m) : R) • LinearMap.id else 0

namespace ConformalVertexAlgebra

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The Virasoro modes L(n).
    With convention Y(ω, z) = ∑_n L_n z^{-n-2} and Y(a, z) = ∑_n a(n) z^{-n-1},
    we have L_n = ω(n+1). -/
def L [ConformalVertexAlgebra R V] (n : ℤ) : Module.End R V :=
  (VertexAlgebra.Y (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) (n + 1)

variable [ConformalVertexAlgebra R V]

/-- L(-1) is the translation operator -/
theorem L_minus1 : L (R := R) (V := V) (-1) = VertexAlgebra.translation (R := R) := by
  unfold L
  exact ConformalVertexAlgebra.L_minus1_eq_translation (R := R) (V := V)

@[simp] theorem L_apply (n : ℤ) (v : V) :
    L (R := R) (V := V) n v =
      (VertexAlgebra.Y (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V)))
        (n + 1) v := rfl

/-- Virasoro relation in terms of the `L` mode notation. -/
theorem virasoro_relation_L (m n : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) m) =
    (12 : R) • ((m - n : ℤ) • L (R := R) (V := V) (m + n)) +
      if m + n = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) • LinearMap.id
      else 0 := by
  simpa [L, add_assoc, add_comm, add_left_comm] using
    ConformalVertexAlgebra.virasoro_relation (R := R) (V := V) m n

/-- Applied vector form of the Virasoro relation in `L` notation. -/
theorem virasoro_relation_L_apply (m n : ℤ) (v : V) :
    ((12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) m)) v =
    ((12 : R) • ((m - n : ℤ) • L (R := R) (V := V) (m + n)) +
      if m + n = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
          (LinearMap.id : Module.End R V)
      else (0 : Module.End R V)) v := by
  exact congrArg (fun f : Module.End R V => f v) (virasoro_relation_L (R := R) (V := V) m n)

/-- Special case `[L(0), L(n)] = -n L(n)` in the scaled convention. -/
theorem virasoro_relation_L_zero_left (n : ℤ) :
    (12 : R) • (L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) n -
      L (R := R) (V := V) n ∘ₗ L (R := R) (V := V) 0) =
    (12 : R) • ((-n : ℤ) • L (R := R) (V := V) n) := by
  simpa using virasoro_relation_L (R := R) (V := V) 0 n

/-- Special case `[L(m), L(0)] = m L(m)` in the scaled convention. -/
theorem virasoro_relation_L_zero_right (m : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) 0 -
      L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) m) =
    (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) := by
  calc
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) 0 -
        L (R := R) (V := V) 0 ∘ₗ L (R := R) (V := V) m) =
      (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) +
        (if m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else 0) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            virasoro_relation_L (R := R) (V := V) m 0
    _ = (12 : R) • ((m : ℤ) • L (R := R) (V := V) m) := by
          by_cases hm : m = 0
          · simp [hm]
          · simp [hm]

/-- Diagonal specialization `m = n` of the scaled Virasoro relation. -/
theorem virasoro_relation_L_diag (m : ℤ) :
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
      L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m) = 0 := by
  have hbase := virasoro_relation_L (R := R) (V := V) m m
  have hcentral :
      (if m + m = 0 then
        (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
          (LinearMap.id : Module.End R V)
      else (0 : Module.End R V)) = 0 := by
    by_cases h2m : m + m = 0
    · have hm : m = 0 := by omega
      subst hm
      simp [h2m]
    · simp [h2m]
  calc
    (12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
        L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m) =
      (12 : R) • ((m - m : ℤ) • L (R := R) (V := V) (m + m)) +
        (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by
          simpa [sub_eq_add_neg] using hbase
    _ = 0 + (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by simp
    _ = (if m + m = 0 then
          (ConformalVertexAlgebra.centralCharge (R := R) (V := V) * (m ^ 3 - m) : R) •
            (LinearMap.id : Module.End R V)
        else (0 : Module.End R V)) := by simp
    _ = 0 := hcentral

/-- Applied form of `[L(m), L(m)] = 0` in the scaled convention. -/
theorem virasoro_relation_L_diag_apply (m : ℤ) (v : V) :
    ((12 : R) • (L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m -
      L (R := R) (V := V) m ∘ₗ L (R := R) (V := V) m)) v = 0 := by
  exact congrArg (fun f : Module.End R V => f v)
    (virasoro_relation_L_diag (R := R) (V := V) m)

/-- Explicit witness of the `L(0)`-grading action. -/
structure L0Grading where
  /-- Weight function on states. -/
  weight : V → ℤ
  /-- `L(0)` acts by the weight on each state. -/
  weight_spec : ∀ a : V,
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 a = (weight a : ℤ) • a

/-- The conformal weight of a state from explicit grading data. -/
def conformalWeight (G : L0Grading (R := R) (V := V)) (a : V) : ℤ :=
  G.weight a

/-- `L(0)`-eigenvalue relation for the explicit conformal weight. -/
theorem conformalWeight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 a =
      (conformalWeight (R := R) (V := V) G a : ℤ) • a :=
  G.weight_spec a

/-- `L(0)`-action in terms of explicit grading witness `G`. -/
theorem L_zero_weight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    L (R := R) (V := V) 0 a = (G.weight a : ℤ) • a := by
  simpa [L] using G.weight_spec a

/-- `L(0)`-action using `conformalWeight` accessor. -/
theorem L_zero_conformalWeight_spec (G : L0Grading (R := R) (V := V)) (a : V) :
    L (R := R) (V := V) 0 a =
      (conformalWeight (R := R) (V := V) G a : ℤ) • a := by
  simpa [conformalWeight] using L_zero_weight_spec (R := R) (V := V) G a

/-- `ConformalVertexAlgebra.L0_grading` packaged as explicit data. -/
theorem exists_L0Grading : Nonempty (L0Grading (R := R) (V := V)) := by
  rcases ConformalVertexAlgebra.L0_grading (R := R) (V := V) with ⟨weight, hweight⟩
  exact ⟨⟨weight, hweight⟩⟩

/-- Existence of an `L(0)` weight function directly in `L`-notation. -/
theorem exists_weight_L0_action : ∃ (weight : V → ℤ), ∀ a : V,
    L (R := R) (V := V) 0 a = (weight a : ℤ) • a := by
  rcases exists_L0Grading (R := R) (V := V) with ⟨G⟩
  exact ⟨G.weight, fun a => by simpa [L] using G.weight_spec a⟩

/-- Existence of explicit conformal-weight grading data in `L`-notation form. -/
theorem exists_conformalWeight_action :
    ∃ G : L0Grading (R := R) (V := V), ∀ a : V,
      L (R := R) (V := V) 0 a = (conformalWeight (R := R) (V := V) G a : ℤ) • a := by
  rcases exists_L0Grading (R := R) (V := V) with ⟨G⟩
  exact ⟨G, fun a => L_zero_conformalWeight_spec (R := R) (V := V) G a⟩

/-- A primary state of weight h: L(n)a = 0 for n > 0, L(0)a = ha -/
structure PrimaryState where
  state : V
  weight : ℤ
  is_primary : ∀ n : ℕ, n > 0 → L (R := R) (V := V) (n : ℤ) state = 0
  weight_condition : L (R := R) (V := V) 0 state = (weight : ℤ) • state

namespace PrimaryState

@[simp] theorem weight_condition_apply (p : PrimaryState (R := R) (V := V)) :
    L (R := R) (V := V) 0 p.state = (p.weight : ℤ) • p.state :=
  p.weight_condition

theorem is_primary_of_pos (p : PrimaryState (R := R) (V := V)) (n : ℕ) (hn : n > 0) :
    L (R := R) (V := V) (n : ℤ) p.state = 0 :=
  p.is_primary n hn

@[simp] theorem is_primary_one (p : PrimaryState (R := R) (V := V)) :
    L (R := R) (V := V) (1 : ℤ) p.state = 0 := by
  simpa using p.is_primary 1 (by decide)

end PrimaryState

end ConformalVertexAlgebra

end StringAlgebra.VOA
