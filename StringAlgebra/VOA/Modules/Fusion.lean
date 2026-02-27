/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Modules.Intertwining

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Universal Fusion Tensor Product

This packages the universal property for the tensor/fusion product `M₁ ⊠ M₂`.
-/

universe uV uM1 uM2 uC

/-- A realization of the fusion tensor product by universal mapping property. -/
structure FusionTensorProduct
    {V : Type uV} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M₁ : Type uM1) (M₂ : Type uM2)
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂] where
  /-- Carrier module for the tensor/fusion product. -/
  carrier : Type uC
  /-- Additive structure on the carrier. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Scalar action on the carrier. -/
  [module : Module R carrier]
  /-- Vertex algebra module structure on the carrier. -/
  [vaModule : VAModule R V carrier]
  /-- Universal intertwining operator `M₁ × M₂ → carrier`. -/
  incl : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := carrier)
  /-- Universal factorization map. -/
  lift :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W],
      IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W) →
      carrier →ₗ[R] W
  /-- Factorization compatibility with the universal intertwiner. -/
  fac :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W]
      (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W))
      (m₁ : M₁) (m₂ : M₂) (n : ℤ),
      (lift I) ((incl.Y_int m₁ n) m₂) = (I.Y_int m₁ n) m₂
  /-- Uniqueness of factorization map. -/
  uniq :
    ∀ {W : Type uC} [AddCommGroup W] [Module R W] [VAModule R V W]
      (I : IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := W))
      (f : carrier →ₗ[R] W),
      (∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ, f ((incl.Y_int m₁ n) m₂) = (I.Y_int m₁ n) m₂) →
      f = lift I

attribute [instance] FusionTensorProduct.addCommGroup FusionTensorProduct.module
  FusionTensorProduct.vaModule

namespace FusionTensorProduct

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable {M₁ M₂ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
variable [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]

/-- Canonical map between two realizations of the same tensor product object. -/
noncomputable def hom (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    P.carrier →ₗ[R] Q.carrier :=
  P.lift (W := Q.carrier) Q.incl

theorem hom_fac (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (hom P Q) ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂ := by
  simpa [hom] using P.fac (W := Q.carrier) Q.incl m₁ m₂ n

/-- Uniqueness principle: a map matching the universal intertwiner equals `hom`. -/
theorem hom_unique (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (f : P.carrier →ₗ[R] Q.carrier)
    (hfac : ∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ,
      f ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂) :
    f = hom P Q := by
  simpa [hom] using P.uniq (I := Q.incl) f hfac

/-- Canonical maps between fusion-product realizations compose transitively. -/
theorem hom_comp (P Q S : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q S).comp (hom P Q) = hom P S := by
  apply hom_unique (P := P) (Q := S)
  intro m₁ m₂ n
  calc
    ((hom Q S).comp (hom P Q)) ((P.incl.Y_int m₁ n) m₂)
        = (hom Q S) ((hom P Q) ((P.incl.Y_int m₁ n) m₂)) := by
            rfl
    _ = (hom Q S) ((Q.incl.Y_int m₁ n) m₂) := by
          exact congrArg (hom Q S) (hom_fac (P := P) (Q := Q) m₁ m₂ n)
    _ = (S.incl.Y_int m₁ n) m₂ := by
          simpa using hom_fac (P := Q) (Q := S) m₁ m₂ n

/-- Associative composition form of canonical fusion maps across four realizations. -/
theorem hom_comp_assoc (P Q S T : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((hom S T).comp (hom Q S)).comp (hom P Q) = hom P T := by
  calc
    ((hom S T).comp (hom Q S)).comp (hom P Q)
        = (hom Q T).comp (hom P Q) := by
            simpa using congrArg (fun f : Q.carrier →ₗ[R] T.carrier => f.comp (hom P Q))
              (hom_comp (P := Q) (Q := S) (S := T))
    _ = hom P T := by
          simpa using hom_comp (P := P) (Q := Q) (S := T)

@[simp] theorem hom_comp_self_left (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom P Q).comp (hom P P) = hom P Q := by
  simpa using (hom_comp (P := P) (Q := P) (S := Q))

@[simp] theorem hom_comp_self_right (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q Q).comp (hom P Q) = hom P Q := by
  simpa using (hom_comp (P := P) (Q := Q) (S := Q))

theorem hom_comp_hom_eq_id (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom P Q).comp (hom Q P) = (LinearMap.id : Q.carrier →ₗ[R] Q.carrier) := by
  have hcomp_lift : (hom P Q).comp (hom Q P) = Q.lift Q.incl := by
    apply Q.uniq (I := Q.incl)
    intro m₁ m₂ n
    calc
      ((hom P Q).comp (hom Q P)) ((Q.incl.Y_int m₁ n) m₂)
          = (hom P Q) ((hom Q P) ((Q.incl.Y_int m₁ n) m₂)) := by
              rfl
      _ = (hom P Q) ((P.incl.Y_int m₁ n) m₂) := by
            have hfacQ :
                (hom Q P) ((Q.incl.Y_int m₁ n) m₂) = (P.incl.Y_int m₁ n) m₂ := by
              simpa [hom] using Q.fac (W := P.carrier) P.incl m₁ m₂ n
            exact congrArg (hom P Q) hfacQ
      _ = (Q.incl.Y_int m₁ n) m₂ := by
            simpa [hom] using P.fac (W := Q.carrier) Q.incl m₁ m₂ n
  have hid_lift : (LinearMap.id : Q.carrier →ₗ[R] Q.carrier) = Q.lift Q.incl := by
    apply Q.uniq (I := Q.incl)
    intro m₁ m₂ n
    rfl
  exact hcomp_lift.trans hid_lift.symm

theorem hom_comp_hom_eq_id_left (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (hom Q P).comp (hom P Q) = (LinearMap.id : P.carrier →ₗ[R] P.carrier) := by
  simpa using hom_comp_hom_eq_id (P := Q) (Q := P)

@[simp] theorem hom_self_eq_id (P : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    hom P P = (LinearMap.id : P.carrier →ₗ[R] P.carrier) := by
  have hid_lift : (LinearMap.id : P.carrier →ₗ[R] P.carrier) = P.lift P.incl := by
    apply P.uniq (I := P.incl)
    intro m₁ m₂ n
    rfl
  simpa [hom] using hid_lift.symm

/-- Any two universal realizations of `M₁ ⊠ M₂` are canonically isomorphic. -/
noncomputable def iso (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    P.carrier ≃ₗ[R] Q.carrier :=
  LinearEquiv.ofLinear (hom P Q) (hom Q P)
    (hom_comp_hom_eq_id (P := P) (Q := Q))
    (hom_comp_hom_eq_id (P := Q) (Q := P))

@[simp] theorem iso_toLinearMap (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((iso P Q : P.carrier ≃ₗ[R] Q.carrier) : P.carrier →ₗ[R] Q.carrier) = hom P Q := rfl

@[simp] theorem iso_symm_toLinearMap (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    ((iso P Q).symm : Q.carrier →ₗ[R] P.carrier) = hom Q P := by
  simp [iso]

@[simp] theorem iso_symm_eq_iso (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (iso P Q).symm = iso Q P := by
  ext x
  change (((iso P Q).symm : Q.carrier →ₗ[R] P.carrier) x) =
      (((iso Q P : Q.carrier ≃ₗ[R] P.carrier) : Q.carrier →ₗ[R] P.carrier) x)
  simp

theorem iso_apply_incl (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (iso P Q) ((P.incl.Y_int m₁ n) m₂) = (Q.incl.Y_int m₁ n) m₂ := by
  simpa [iso_toLinearMap] using hom_fac (P := P) (Q := Q) m₁ m₂ n

theorem iso_symm_apply_incl (P Q : FusionTensorProduct (R := R) (V := V) M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (n : ℤ) :
    (iso P Q).symm ((Q.incl.Y_int m₁ n) m₂) = (P.incl.Y_int m₁ n) m₂ := by
  simpa [iso_symm_toLinearMap] using hom_fac (P := Q) (Q := P) m₁ m₂ n

@[simp] theorem iso_trans (P Q S : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    (iso P Q).trans (iso Q S) = iso P S := by
  ext x
  change (iso Q S) ((iso P Q) x) = (iso P S) x
  have hcomp := hom_comp (P := P) (Q := Q) (S := S)
  exact congrArg (fun f : P.carrier →ₗ[R] S.carrier => f x) hcomp

@[simp] theorem iso_refl (P : FusionTensorProduct (R := R) (V := V) M₁ M₂) :
    iso P P = LinearEquiv.refl R P.carrier := by
  ext x
  simp [iso, hom_self_eq_id]

end FusionTensorProduct


end StringAlgebra.VOA
