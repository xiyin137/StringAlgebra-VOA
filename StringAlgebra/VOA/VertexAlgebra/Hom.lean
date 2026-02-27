/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra.VOA

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Morphisms of Vertex Algebras -/

/-- A morphism of vertex algebras preserving all structure -/
structure VertexAlgebraHom (V W : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    [AddCommGroup W] [Module R W] [VertexAlgebra R W] where
  /-- The underlying linear map -/
  toLinearMap : V →ₗ[R] W
  /-- Preserves the vertex operator: φ(Y(a,z)b) = Y(φ(a),z)φ(b) -/
  map_Y : ∀ a b : V, ∀ n : ℤ,
    toLinearMap ((VertexAlgebra.Y (R := R) a) n b) =
    (VertexAlgebra.Y (R := R) (toLinearMap a)) n (toLinearMap b)
  /-- Preserves the vacuum -/
  map_vacuum : toLinearMap (VertexAlgebra.vacuum (R := R)) =
               VertexAlgebra.vacuum (R := R)

/-- A VOA homomorphism also preserves the conformal vector -/
structure VOAHom (V W : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    [AddCommGroup W] [Module R W] [VertexOperatorAlgebra R W]
    extends VertexAlgebraHom R V W where
  /-- Preserves the conformal vector -/
  map_conformal : toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) =
                  ConformalVertexAlgebra.conformalVector (R := R) (V := W)

namespace VertexAlgebraHom

variable {R : Type*} [CommRing R]
variable {V W U : Type*}
variable [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable [AddCommGroup W] [Module R W] [VertexAlgebra R W]
variable [AddCommGroup U] [Module R U] [VertexAlgebra R U]

/-- Identity vertex-algebra homomorphism. -/
def idHom (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    VertexAlgebraHom R V V where
  toLinearMap := LinearMap.id
  map_Y := by intro a b n; rfl
  map_vacuum := rfl

/-- Composition of vertex-algebra homomorphisms. -/
def compHom (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    VertexAlgebraHom R V U where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_Y := by
    intro a b n
    calc
      (g.toLinearMap.comp f.toLinearMap) ((VertexAlgebra.Y (R := R) a) n b)
          = g.toLinearMap (f.toLinearMap ((VertexAlgebra.Y (R := R) a) n b)) := rfl
      _ = g.toLinearMap ((VertexAlgebra.Y (R := R) (f.toLinearMap a)) n (f.toLinearMap b)) := by
            simpa using congrArg g.toLinearMap (f.map_Y a b n)
      _ = (VertexAlgebra.Y (R := R) (g.toLinearMap (f.toLinearMap a))) n
            (g.toLinearMap (f.toLinearMap b)) := by
              simpa using g.map_Y (f.toLinearMap a) (f.toLinearMap b) n
  map_vacuum := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (VertexAlgebra.vacuum (R := R))
          = g.toLinearMap (f.toLinearMap (VertexAlgebra.vacuum (R := R))) := rfl
      _ = g.toLinearMap (VertexAlgebra.vacuum (R := R)) := by simpa using congrArg g.toLinearMap f.map_vacuum
      _ = VertexAlgebra.vacuum (R := R) := g.map_vacuum

@[simp] theorem idHom_toLinearMap (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] :
    (idHom (R := R) V).toLinearMap = LinearMap.id := rfl

@[simp] theorem compHom_toLinearMap (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    (compHom (R := R) g f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

@[simp] theorem compHom_apply (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap a = g.toLinearMap (f.toLinearMap a) := rfl

@[ext] theorem ext {f g : VertexAlgebraHom R V W} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  simp

@[simp] theorem idHom_apply (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V] (a : V) :
    (idHom (R := R) V).toLinearMap a = a := rfl

@[simp] theorem compHom_id_right_apply (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) f (idHom (R := R) V)).toLinearMap a = f.toLinearMap a := by
  rfl

@[simp] theorem compHom_id_left_apply (f : VertexAlgebraHom R V W) (a : V) :
    (compHom (R := R) (idHom (R := R) W) f).toLinearMap a = f.toLinearMap a := by
  rfl

theorem compHom_assoc_apply
    {X : Type*} [AddCommGroup X] [Module R X] [VertexAlgebra R X]
    (h : VertexAlgebraHom R U X) (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W)
    (a : V) :
    (compHom (R := R) h (compHom (R := R) g f)).toLinearMap a =
      (compHom (R := R) (compHom (R := R) h g) f).toLinearMap a := rfl

@[simp] theorem compHom_id_right (f : VertexAlgebraHom R V W) :
    compHom (R := R) f (idHom (R := R) V) = f := by
  ext a
  rfl

@[simp] theorem compHom_id_left (f : VertexAlgebraHom R V W) :
    compHom (R := R) (idHom (R := R) W) f = f := by
  ext a
  rfl

@[simp] theorem compHom_assoc
    {X : Type*} [AddCommGroup X] [Module R X] [VertexAlgebra R X]
    (h : VertexAlgebraHom R U X) (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W) :
    compHom (R := R) h (compHom (R := R) g f) =
      compHom (R := R) (compHom (R := R) h g) f := by
  ext a
  rfl

theorem map_nProduct_compHom
    (g : VertexAlgebraHom R W U) (f : VertexAlgebraHom R V W)
    (a b : V) (n : ℤ) :
    (compHom (R := R) g f).toLinearMap (VertexAlgebra.nProduct (R := R) (V := V) a n b) =
      VertexAlgebra.nProduct (R := R) (V := U)
        ((compHom (R := R) g f).toLinearMap a)
        n
        ((compHom (R := R) g f).toLinearMap b) := by
  simpa [VertexAlgebra.nProduct] using (compHom (R := R) g f).map_Y a b n

@[simp] theorem map_nProduct (f : VertexAlgebraHom R V W) (a b : V) (n : ℤ) :
    f.toLinearMap (VertexAlgebra.nProduct (R := R) (V := V) a n b) =
      VertexAlgebra.nProduct (R := R) (V := W) (f.toLinearMap a) n (f.toLinearMap b) := by
  simpa [VertexAlgebra.nProduct] using f.map_Y a b n

theorem map_nProduct_vacuum_left (f : VertexAlgebraHom R V W) (a : V) (n : ℤ) :
    f.toLinearMap
      (VertexAlgebra.nProduct (R := R) (V := V) (VertexAlgebra.vacuum (R := R)) n a) =
      VertexAlgebra.nProduct (R := R) (V := W) (VertexAlgebra.vacuum (R := R)) n (f.toLinearMap a) := by
  have h := f.map_nProduct (a := VertexAlgebra.vacuum (R := R)) (b := a) (n := n)
  rw [f.map_vacuum] at h
  exact h

theorem map_vacuum_minus1_action (f : VertexAlgebraHom R V W) (a : V) :
    f.toLinearMap
      (VertexAlgebra.nProduct (R := R) (V := V) (VertexAlgebra.vacuum (R := R)) (-1) a) =
      VertexAlgebra.nProduct (R := R) (V := W) (VertexAlgebra.vacuum (R := R)) (-1)
        (f.toLinearMap a) := by
  simpa using f.map_nProduct_vacuum_left (a := a) (-1)

end VertexAlgebraHom

namespace VOAHom

variable {R : Type*} [CommRing R]
variable {V W U : Type*}
variable [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
variable [AddCommGroup W] [Module R W] [VertexOperatorAlgebra R W]
variable [AddCommGroup U] [Module R U] [VertexOperatorAlgebra R U]

/-- Identity VOA homomorphism. -/
def idHom (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] :
    VOAHom R V V where
  toLinearMap := LinearMap.id
  map_Y := by intro a b n; rfl
  map_vacuum := rfl
  map_conformal := rfl

/-- Composition of VOA homomorphisms. -/
def compHom (g : VOAHom R W U) (f : VOAHom R V W) : VOAHom R V U where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_Y := by
    intro a b n
    calc
      (g.toLinearMap.comp f.toLinearMap) ((VertexAlgebra.Y (R := R) a) n b)
          = g.toLinearMap (f.toLinearMap ((VertexAlgebra.Y (R := R) a) n b)) := rfl
      _ = g.toLinearMap ((VertexAlgebra.Y (R := R) (f.toLinearMap a)) n (f.toLinearMap b)) := by
            simpa using congrArg g.toLinearMap (f.map_Y a b n)
      _ = (VertexAlgebra.Y (R := R) (g.toLinearMap (f.toLinearMap a))) n
            (g.toLinearMap (f.toLinearMap b)) := by
              simpa using g.map_Y (f.toLinearMap a) (f.toLinearMap b) n
  map_vacuum := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (VertexAlgebra.vacuum (R := R))
          = g.toLinearMap (f.toLinearMap (VertexAlgebra.vacuum (R := R))) := rfl
      _ = g.toLinearMap (VertexAlgebra.vacuum (R := R)) := by
            simpa using congrArg g.toLinearMap f.map_vacuum
      _ = VertexAlgebra.vacuum (R := R) := g.map_vacuum
  map_conformal := by
    calc
      (g.toLinearMap.comp f.toLinearMap) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))
          = g.toLinearMap (f.toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) := rfl
      _ = g.toLinearMap (ConformalVertexAlgebra.conformalVector (R := R) (V := W)) := by
            simpa using congrArg g.toLinearMap f.map_conformal
      _ = ConformalVertexAlgebra.conformalVector (R := R) (V := U) := g.map_conformal

@[simp] theorem idHom_toLinearMap (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] :
    (idHom (R := R) V).toLinearMap = LinearMap.id := rfl

@[simp] theorem compHom_toLinearMap (g : VOAHom R W U) (f : VOAHom R V W) :
    (compHom (R := R) g f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

@[simp] theorem compHom_apply (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap a = g.toLinearMap (f.toLinearMap a) := rfl

@[simp] theorem idHom_apply (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (a : V) :
    (idHom (R := R) V).toLinearMap a = a := rfl

@[simp] theorem compHom_id_right_apply (f : VOAHom R V W) (a : V) :
    (compHom (R := R) f (idHom (R := R) V)).toLinearMap a = f.toLinearMap a := by
  rfl

@[simp] theorem compHom_id_left_apply (f : VOAHom R V W) (a : V) :
    (compHom (R := R) (idHom (R := R) W) f).toLinearMap a = f.toLinearMap a := by
  rfl

theorem compHom_assoc_apply
    {X : Type*} [AddCommGroup X] [Module R X] [VertexOperatorAlgebra R X]
    (h : VOAHom R U X) (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) h (compHom (R := R) g f)).toLinearMap a =
      (compHom (R := R) (compHom (R := R) h g) f).toLinearMap a := rfl

@[simp] theorem compHom_id_right (f : VOAHom R V W) :
    compHom (R := R) f (idHom (R := R) V) = f := by
  cases f
  rfl

@[simp] theorem compHom_id_left (f : VOAHom R V W) :
    compHom (R := R) (idHom (R := R) W) f = f := by
  cases f
  rfl

@[simp] theorem compHom_assoc
    {X : Type*} [AddCommGroup X] [Module R X] [VertexOperatorAlgebra R X]
    (h : VOAHom R U X) (g : VOAHom R W U) (f : VOAHom R V W) :
    compHom (R := R) h (compHom (R := R) g f) =
      compHom (R := R) (compHom (R := R) h g) f := by
  cases h
  cases g
  cases f
  rfl

theorem map_L (f : VOAHom R V W) (n : ℤ) (a : V) :
    f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) n a) =
      ConformalVertexAlgebra.L (R := R) (V := W) n (f.toLinearMap a) := by
  change f.toLinearMap
      ((VertexAlgebra.Y (R := R)
        (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) (n + 1) a) =
    (VertexAlgebra.Y (R := R)
      (ConformalVertexAlgebra.conformalVector (R := R) (V := W))) (n + 1) (f.toLinearMap a)
  simpa [f.map_conformal] using
    f.map_Y (ConformalVertexAlgebra.conformalVector (R := R) (V := V)) a (n + 1)

theorem map_translation (f : VOAHom R V W) (a : V) :
    f.toLinearMap (VertexAlgebra.translation (R := R) a) =
      VertexAlgebra.translation (R := R) (f.toLinearMap a) := by
  simpa [ConformalVertexAlgebra.L_minus1 (R := R) (V := V),
      ConformalVertexAlgebra.L_minus1 (R := R) (V := W)] using
    f.map_L (-1) a

theorem map_L_compHom (g : VOAHom R W U) (f : VOAHom R V W) (n : ℤ) (a : V) :
    (compHom (R := R) g f).toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) n a) =
      ConformalVertexAlgebra.L (R := R) (V := U) n
        ((compHom (R := R) g f).toLinearMap a) := by
  simpa using (compHom (R := R) g f).map_L n a

theorem map_translation_compHom (g : VOAHom R W U) (f : VOAHom R V W) (a : V) :
    (compHom (R := R) g f).toLinearMap (VertexAlgebra.translation (R := R) a) =
      VertexAlgebra.translation (R := R) ((compHom (R := R) g f).toLinearMap a) := by
  simpa using (compHom (R := R) g f).map_translation a

def mapPrimaryState (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ConformalVertexAlgebra.PrimaryState (R := R) (V := W) where
  state := f.toLinearMap p.state
  weight := p.weight
  is_primary := by
    intro n hn
    calc
      ConformalVertexAlgebra.L (R := R) (V := W) (n : ℤ) (f.toLinearMap p.state)
          = f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) (n : ℤ) p.state) := by
              simpa using (f.map_L (n : ℤ) p.state).symm
      _ = f.toLinearMap 0 := by
            simpa using congrArg f.toLinearMap (p.is_primary n hn)
      _ = 0 := by simp
  weight_condition := by
    calc
      ConformalVertexAlgebra.L (R := R) (V := W) 0 (f.toLinearMap p.state)
          = f.toLinearMap (ConformalVertexAlgebra.L (R := R) (V := V) 0 p.state) := by
              simpa using (f.map_L 0 p.state).symm
      _ = f.toLinearMap ((p.weight : ℤ) • p.state) := by
            simpa using congrArg f.toLinearMap p.weight_condition
      _ = (p.weight : ℤ) • f.toLinearMap p.state := by simp

@[simp] theorem mapPrimaryState_state (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    (f.mapPrimaryState p).state = f.toLinearMap p.state := rfl

@[simp] theorem mapPrimaryState_weight (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    (f.mapPrimaryState p).weight = p.weight := rfl

@[simp] theorem mapPrimaryState_comp_state
    (g : VOAHom R W U) (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ((compHom (R := R) g f).mapPrimaryState p).state = g.toLinearMap (f.toLinearMap p.state) := rfl

@[simp] theorem mapPrimaryState_comp_weight
    (g : VOAHom R W U) (f : VOAHom R V W)
    (p : ConformalVertexAlgebra.PrimaryState (R := R) (V := V)) :
    ((compHom (R := R) g f).mapPrimaryState p).weight = p.weight := rfl

end VOAHom

end StringAlgebra.VOA
