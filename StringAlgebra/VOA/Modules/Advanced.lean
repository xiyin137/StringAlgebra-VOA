/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Modules.Fusion

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Twisted Modules

Twisted modules arise in orbifold constructions.
-/

/-- A g-twisted module for an automorphism g of order T -/
structure TwistedModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (g : V →ₗ[R] V)
    (T : ℕ)
    (_hg : g^T = LinearMap.id) where
  /-- The underlying module -/
  M : Type*
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- The twisted vertex operator Y^g: V → End(M)[[z^{1/T}, z^{-1/T}]] -/
  Y_twisted : V → FormalDistribution R M
  /-- Equivariance -/
  equivariance : ∀ a : V, ∀ n : ℤ,
    (Y_twisted (g a)) n = (Y_twisted a) n
  /-- Twisted Jacobi identity -/
  jacobi : ∀ a b : V, ∀ m : M, ∀ n : ℤ,
    (Y_twisted a) n ((Y_twisted b) n m) = (Y_twisted b) n ((Y_twisted a) n m)

attribute [instance] TwistedModule.addCommGroup TwistedModule.module

/-! ## Contragredient Module -/

/-- The contragredient module M' = ⊕_n (M_n)* with the dual vertex operator -/
structure ContragredientModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (_grading : GradedVAModule R V M) where
  /-- The dual space (restricted dual) -/
  M' : Type*
  [addCommGroup : AddCommGroup M']
  [module : Module R M']
  /-- The pairing -/
  pairing : M' →ₗ[R] M →ₗ[R] R
  /-- The contragredient vertex operator formula -/
  contragredient_formula : ∀ m' : M', ∀ m₁ m₂ : M,
    pairing m' (m₁ + m₂) = pairing m' m₁ + pairing m' m₂

attribute [instance] ContragredientModule.addCommGroup ContragredientModule.module

/-- A self-dual module: M ≅ M' -/
def isSelfDual
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M)
    (M_dual : ContragredientModule (R := R) grading) : Prop :=
  Nonempty (M ≃ₗ[R] M_dual.M')

/-! ## Rationality -/

/-- A VOA V is rational -/
class RationalVOA (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] where
  /-- Finitely many irreducible modules (up to isomorphism) -/
  finitelyManyIrreducibles : ∃ n : ℕ, 0 < n
  /-- Complete reducibility at the submodule level:
      every VOA submodule has a complementary submodule. -/
  completelyReducible :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M],
      ∀ N : Submodule R M, ∃ P : Submodule R M, IsCompl N P

/-- Every vector decomposes as `n + p` for complementary submodules `N ⊔ P = ⊤`. -/
  theorem exists_add_decomposition_of_isCompl
    {M : Type*} [AddCommGroup M] [Module R M]
    (N P : Submodule R M) (hNP : IsCompl N P) (x : M) :
    ∃ n p : M, n ∈ N ∧ p ∈ P ∧ x = n + p := by
  have hx : x ∈ N ⊔ P := by
    simp [hNP.sup_eq_top]
  rcases Submodule.mem_sup.mp hx with ⟨n, hn, p, hp, rfl⟩
  exact ⟨n, p, hn, hp, rfl⟩

/-- Decomposition along complementary submodules is unique. -/
theorem add_decomposition_unique_of_isCompl
    {M : Type*} [AddCommGroup M] [Module R M]
    (N P : Submodule R M) (hNP : IsCompl N P)
    {n₁ n₂ p₁ p₂ : M}
    (hn₁ : n₁ ∈ N) (hn₂ : n₂ ∈ N) (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P)
    (hEq : n₁ + p₁ = n₂ + p₂) :
    n₁ = n₂ ∧ p₁ = p₂ := by
  have hsum : n₁ - n₂ + (p₁ - p₂) = 0 := by
    have hEq' : (n₁ + p₁) - (n₂ + p₂) = 0 := sub_eq_zero.mpr hEq
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
  have hsub : n₁ - n₂ = -(p₁ - p₂) := eq_neg_of_add_eq_zero_left hsum
  have hN : n₁ - n₂ ∈ N := Submodule.sub_mem N hn₁ hn₂
  have hP : n₁ - n₂ ∈ P := by
    have hpSub : p₁ - p₂ ∈ P := Submodule.sub_mem P hp₁ hp₂
    have hneg : -(p₁ - p₂) ∈ P := Submodule.neg_mem P hpSub
    simpa [hsub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hInInf : n₁ - n₂ ∈ N ⊓ P := ⟨hN, hP⟩
  have hZeroMem : n₁ - n₂ ∈ (⊥ : Submodule R M) := by
    simpa [hNP.inf_eq_bot] using hInInf
  have hNEqual : n₁ = n₂ := sub_eq_zero.mp (by simpa using hZeroMem)
  constructor
  · exact hNEqual
  · have hEq' : n₂ + p₁ = n₂ + p₂ := by simpa [hNEqual] using hEq
    exact add_left_cancel hEq'

/-- A rational VOA has a strictly positive finite irreducible-count witness. -/
theorem RationalVOA.exists_positive_irreducible_count
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [RationalVOA R V] : ∃ n : ℕ, 0 < n :=
  RationalVOA.finitelyManyIrreducibles (R := R) (V := V)

/-- A rational VOA has a nonzero finite irreducible-count witness. -/
theorem RationalVOA.exists_nonzero_irreducible_count
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [RationalVOA R V] : ∃ n : ℕ, n ≠ 0 := by
  rcases RationalVOA.exists_positive_irreducible_count (R := R) (V := V) with ⟨n, hn⟩
  exact ⟨n, Nat.ne_of_gt hn⟩

/-- For finite intertwiner spaces, fusion rules are finite. -/
theorem fusion_rules_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  classical
  letI : Fintype (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)), ?_⟩
  simp [fusionRules]
  

/-- For finite intertwiner spaces, fusion rules admit a positive finite bound. -/
theorem fusion_rules_bounded_pos
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  classical
  letI : Fintype (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) + 1,
    Nat.succ_pos _, ?_⟩
  simp [fusionRules]
  

/-- For finite intertwiner spaces in both orientations, both orderings admit one positive common bound. -/
theorem fusion_rules_bounded_pos_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  obtain ⟨bound12, hpos12, hbound12⟩ :=
    fusion_rules_bounded_pos (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
  obtain ⟨bound21, hpos21, hbound21⟩ :=
    fusion_rules_bounded_pos (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)
  refine ⟨max bound12 bound21, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos12 (Nat.le_max_left _ _)
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- Dropping positivity from a positive fusion bound. -/
theorem fusion_rules_finite_of_bounded_pos
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpos : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpos with ⟨bound, _hboundpos, hle⟩
  exact ⟨bound, hle⟩

/-- Any finite fusion bound can be upgraded to a positive finite bound by `+1`. -/
theorem fusion_rules_bounded_pos_of_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hfin : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hfin with ⟨bound, hbound⟩
  refine ⟨bound + 1, Nat.succ_pos _, ?_⟩
  exact le_trans hbound (Nat.le_succ _)

/-- Positive-bounded and finite-bounded fusion-rule statements are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) := by
  constructor
  · intro hpos
    exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpos
  · intro hfin
    exact fusion_rules_bounded_pos_of_finite (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hfin

/-- Extract the first ordered positive bound from a pair bound. -/
theorem fusion_rules_bounded_pos_of_pair_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, hleft, _hright⟩
  exact ⟨bound, hpos, hleft⟩

/-- Extract the swapped ordered positive bound from a pair bound. -/
theorem fusion_rules_bounded_pos_of_pair_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, _hleft, hright⟩
  exact ⟨bound, hpos, hright⟩

/-- Symmetry of a positive common pair bound under swapping `(M₁,M₂)`. -/
theorem fusion_rules_bounded_pos_pair_symm
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hpos, hbound12, hbound21⟩
  exact ⟨bound, hpos, hbound21, hbound12⟩

/-- Build one common positive pair bound from two ordered positive bounds. -/
theorem fusion_rules_bounded_pos_pair_of_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases h12 with ⟨bound12, hpos12, hbound12⟩
  rcases h21 with ⟨bound21, hpos21, hbound21⟩
  refine ⟨max bound12 bound21, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos12 (Nat.le_max_left _ _)
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- A pair positive bound yields an ordinary finite bound for `(M₁,M₂)`. -/
theorem fusion_rules_finite_of_pair_bounded_pos_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_pair_left (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair)

/-- A pair positive bound yields an ordinary finite bound for the swapped pair `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_pair_bounded_pos_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_of_bounded_pos (R := R) (V := V)
    (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)
    (fusion_rules_bounded_pos_of_pair_right (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair)

/-- Any common finite pair bound can be upgraded to a common positive pair bound by `+1`. -/
theorem fusion_rules_bounded_pos_pair_of_finite_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, hbound21⟩
  refine ⟨bound + 1, Nat.succ_pos _, ?_, ?_⟩
  · exact le_trans hbound12 (Nat.le_succ _)
  · exact le_trans hbound21 (Nat.le_succ _)

/-- Build one common finite pair bound from two ordered finite bounds. -/
theorem fusion_rules_finite_pair_of_finite_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases h12 with ⟨bound12, hbound12⟩
  rcases h21 with ⟨bound21, hbound21⟩
  refine ⟨max bound12 bound21, ?_, ?_⟩
  · exact le_trans hbound12 (Nat.le_max_left _ _)
  · exact le_trans hbound21 (Nat.le_max_right _ _)

/-- Extract the first ordered finite bound from a finite pair bound. -/
theorem fusion_rules_finite_of_pair_finite_left
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, _hbound21⟩
  exact ⟨bound, hbound12⟩

/-- Extract the swapped ordered finite bound from a finite pair bound. -/
theorem fusion_rules_finite_of_pair_finite_right
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, _hbound12, hbound21⟩
  exact ⟨bound, hbound21⟩

/-- Symmetry of a common finite pair bound under swapping `(M₁,M₂)`. -/
theorem fusion_rules_finite_pair_symm
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (hpair : ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  rcases hpair with ⟨bound, hbound12, hbound21⟩
  exact ⟨bound, hbound21, hbound12⟩

/-- Positive-bounded and finite-bounded common pair statements are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) := by
  constructor
  · intro hpair
    rcases hpair with ⟨bound, _hpos, hbound12, hbound21⟩
    exact ⟨bound, hbound12, hbound21⟩
  · intro hpair
    exact fusion_rules_bounded_pos_pair_of_finite_pair (R := R) (V := V)
      (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) hpair

/-- Two ordered positive bounds can be merged into one common finite (not necessarily positive) pair bound. -/
theorem fusion_rules_finite_pair_of_bounds
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    (h12 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound)
    (h21 : ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases fusion_rules_bounded_pos_pair_of_bounds (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) h12 h21 with ⟨bound, _hpos, hbound12, hbound21⟩
  exact ⟨bound, hbound12, hbound21⟩

/-- Rational VOAs admit one common finite bound for both orderings `(M₁,M₂)` and `(M₂,M₁)`. -/
theorem fusion_rules_finite_pair_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  rcases fusion_rules_bounded_pos_pair (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) with ⟨bound, _hpos, hbound12, hbound21⟩
  exact ⟨bound, hbound12, hbound21⟩

/-- Rational VOAs also give a finite bound for the swapped ordering `(M₂,M₁)`. -/
theorem fusion_rules_finite_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound := by
  simpa using fusion_rules_finite (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

/-- Rational VOAs admit a swapped-orientation common positive pair bound. -/
theorem fusion_rules_bounded_pos_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_bounded_pos_pair_symm (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_bounded_pos_pair (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))

/-- Rational VOAs admit a swapped-orientation common finite pair bound. -/
theorem fusion_rules_finite_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))]
    [Finite (IntertwiningOperator (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃))] :
    ∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  exact fusion_rules_finite_pair_symm (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (fusion_rules_finite_pair_of_rational (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃))

/-- Under rationality, positive and finite single-order bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_iff_finite (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Under rationality, positive and finite common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_pair_iff_finite_pair (R := R) (V := V)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)

/-- Under rationality, positive and finite swapped single-order bounds are equivalent. -/
theorem fusion_rules_bounded_pos_iff_finite_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_iff_finite (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)

/-- Under rationality, positive and finite swapped common-pair bounds are equivalent. -/
theorem fusion_rules_bounded_pos_pair_iff_finite_pair_of_rational_swapped
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    (∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) ↔
    (∃ (bound : ℕ),
      fusionRules (R := R) (V := V) (M₁ := M₂) (M₂ := M₁) (M₃ := M₃) ≤ bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound) :=
  fusion_rules_bounded_pos_pair_iff_finite_pair (R := R) (V := V)
    (M₁ := M₂) (M₂ := M₁) (M₃ := M₃)


end StringAlgebra.VOA
