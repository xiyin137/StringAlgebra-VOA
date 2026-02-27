/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra.Conformal

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Vertex Operator Algebra (VOA) -/

/-- A Vertex Operator Algebra (VOA) is a ℤ-graded conformal vertex algebra
    with the grading given by L(0) eigenvalues. -/
class VertexOperatorAlgebra (V : Type*) [AddCommGroup V] [Module R V]
    extends ConformalVertexAlgebra R V where
  /-- The graded components V = ⊕_n V_n -/
  component : ℤ → Submodule R V
  /-- V decomposes as a direct sum -/
  decomposition : ∀ v : V, ∃ (s : Finset ℤ), v ∈ ⨆ n ∈ s, component n
  /-- The grading matches L(0) eigenvalues -/
  grading_matches_L0 : ∀ n : ℤ, ∀ v ∈ component n,
    (Y conformalVector) 1 v = (n : ℤ) • v
  /-- Finite-dimensionality: each V_n is finite-dimensional -/
  finite_dimensional : ∀ n : ℤ, Module.Finite R (component n)
  /-- Lower truncation: V_n = 0 for n << 0 -/
  lower_truncated : ∃ N : ℤ, ∀ n : ℤ, n < N → component n = ⊥
  /-- The vacuum has weight 0: |0⟩ ∈ V_0 -/
  vacuum_weight : vacuum ∈ component 0
  /-- The conformal vector has weight 2: ω ∈ V_2 -/
  conformal_vector_weight : conformalVector ∈ component 2

namespace VertexOperatorAlgebra

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [VertexOperatorAlgebra R V]

theorem exists_decomposition (v : V) :
    ∃ (s : Finset ℤ), v ∈ ⨆ n ∈ s, VertexOperatorAlgebra.component (R := R) (V := V) n :=
  VertexOperatorAlgebra.decomposition (R := R) (V := V) v

theorem finite_component (n : ℤ) :
    Module.Finite R (VertexOperatorAlgebra.component (R := R) (V := V) n) :=
  VertexOperatorAlgebra.finite_dimensional (R := R) (V := V) n

theorem lower_truncated_exists :
    ∃ N : ℤ, ∀ n : ℤ, n < N → VertexOperatorAlgebra.component (R := R) (V := V) n = ⊥ :=
  VertexOperatorAlgebra.lower_truncated (R := R) (V := V)

@[simp] theorem vacuum_mem_component_zero :
    VertexAlgebra.vacuum (R := R) ∈ VertexOperatorAlgebra.component (R := R) (V := V) 0 :=
  VertexOperatorAlgebra.vacuum_weight (R := R) (V := V)

@[simp] theorem conformalVector_mem_component_two :
    ConformalVertexAlgebra.conformalVector (R := R) (V := V) ∈
      VertexOperatorAlgebra.component (R := R) (V := V) 2 :=
  VertexOperatorAlgebra.conformal_vector_weight (R := R) (V := V)

theorem L0_action_on_component (n : ℤ) (v : V)
    (hv : v ∈ VertexOperatorAlgebra.component (R := R) (V := V) n) :
    ConformalVertexAlgebra.L (R := R) (V := V) 0 v = (n : ℤ) • v := by
  simpa [ConformalVertexAlgebra.L] using
    VertexOperatorAlgebra.grading_matches_L0 (R := R) (V := V) n v hv

theorem L0_vacuum :
    ConformalVertexAlgebra.L (R := R) (V := V) 0 (VertexAlgebra.vacuum (R := R)) = 0 := by
  have h :=
    L0_action_on_component (R := R) (V := V) 0 (VertexAlgebra.vacuum (R := R))
      (vacuum_mem_component_zero (R := R) (V := V))
  simpa using h

theorem L0_conformalVector :
    ConformalVertexAlgebra.L (R := R) (V := V) 0
      (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) =
      (2 : ℤ) • (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) :=
  L0_action_on_component (R := R) (V := V) 2
    (ConformalVertexAlgebra.conformalVector (R := R) (V := V))
    (conformalVector_mem_component_two (R := R) (V := V))

end VertexOperatorAlgebra

end StringAlgebra.VOA
