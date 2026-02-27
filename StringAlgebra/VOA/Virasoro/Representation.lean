/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Virasoro.Core

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

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

end StringAlgebra.VOA
