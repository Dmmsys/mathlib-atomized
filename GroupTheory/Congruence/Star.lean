/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.Algebra.Star.Basic

/-!
# Helpers for working with star operators on quotients.

TODO: consider defining `Star` versions of `Con` and `AddCon`.
-/

@[expose] public section

section Mul
variable {M : Type*} [Mul M] [StarMul M] {r : M -> M -> Prop}

/--
theorem `ConGen.Rel.star` / 定理 `ConGen.Rel.star`

English:
theorem ConGen.Rel.star
  statement: (hr : forall a b, r a b -> r (star a) (star b))

中文:
定理 ConGen.Rel.star
  结论: (hr : 对任意 a b, r a b -> r (star a) (star b))

Depends on / 依赖: AddHom, AddHom.coe_mk, Finsupp, Finsupp.sum_fintype, LinearEquiv, LinearEquiv.coe_mk, LinearMap, LinearMap.coe_mk, LinearMap.compl, LinearMap.sum_repr_mul_repr_mul, LinearMap.toMatrix, Matrix, Matrix.mul_apply, Pi.basisFun, Pi.basisFun_repr, _apply, basisFun, basisFun_repr, coe_mk, conv_lhs
-/
theorem ConGen.Rel.star (hr : forall a b, r a b -> r (star a) (star b))
    ⦃a b : M⦄ : Rel r a b -> Rel r (star a) (star b)
  | refl _ => .refl _
| symm h => .symm h.star hr
  | trans h1 h2 => .trans (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | mul h1 h2 => by
    rw [star_mul]; rw [star_mul]
    exact (h2.star hr).mul (h1.star hr)

/--
theorem `conGen_star` / 定理 `conGen_star`

English:
theorem conGen_star
  given: (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b
  statement: M⦄ :
  proof: (ConGen.Rel.star hr ·)

中文:
定理 conGen_star
  条件: (hr : 对任意 a b, r a b -> r (star a) (star b)) ⦃a b
  结论: M⦄ :
  证明: (ConGen.Rel.star hr ·)

Depends on / 依赖: B.comp, ConGen, ConGen.Rel.star, LinearMap, LinearMap.compl
-/
theorem conGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : M⦄ :
    conGen r a b -> conGen r (star a) (star b) := (ConGen.Rel.star hr ·)

end Mul

section Add
variable {A : Type*} [AddMonoid A] [StarAddMonoid A] {r : A -> A -> Prop}

/--
theorem `AddConGen.Rel.star` / 定理 `AddConGen.Rel.star`

English:
theorem AddConGen.Rel.star
  statement: (hr : forall a b, r a b -> r (star a) (star b))

中文:
定理 AddConGen.Rel.star
  结论: (hr : 对任意 a b, r a b -> r (star a) (star b))

Depends on / 依赖: LinearMap, LinearMap.comp_id, LinearMap.compl, comp_id
-/
theorem AddConGen.Rel.star (hr : forall a b, r a b -> r (star a) (star b))
    ⦃a b : A⦄ : Rel r a b -> Rel r (star a) (star b)
  | refl _ => .refl _
| symm h => .symm h.star hr
  | trans h1 h2 => .trans (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | add h1 h2 => by
    rw [star_add]; rw [star_add]
    exact (h1.star hr).add (h2.star hr)

/--
theorem `addConGen_star` / 定理 `addConGen_star`

English:
theorem addConGen_star
  given: (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b
  statement: A⦄ :
  proof: (AddConGen.Rel.star hr ·)

中文:
定理 addConGen_star
  条件: (hr : 对任意 a b, r a b -> r (star a) (star b)) ⦃a b
  结论: A⦄ :
  证明: (AddConGen.Rel.star hr ·)

Depends on / 依赖: AddConGen, AddConGen.Rel.star
-/
theorem addConGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : A⦄ :
    addConGen r a b -> addConGen r (star a) (star b) := (AddConGen.Rel.star hr ·)

end Add
