/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Free rings

The theory of the free ring over a type.

## Main definitions

* `FreeRing α` : the free (not commutative in general) ring over a type.
* `lift (f : α → R)` : the ring hom `FreeRing α →+* R` induced by `f`.
* `map (f : α → β)` : the ring hom `FreeRing α →+* FreeRing β` induced by `f`.

## Implementation details

`FreeRing α` is implemented as the free abelian group over the free monoid on `α`.

## Tags

free ring

-/

@[expose] public section


universe u v

/--
Definition of `FreeRing` / `FreeRing` 的定义

English:
definition FreeRing
  signature: (α : Type u)
  body: FreeAbelianGroup FreeMonoid α
deriving Ring, Inhabited, Nontrivial

中文:
定义 FreeRing
  签名: (α : 类型u)
  定义体: FreeAbelianGroup FreeMonoid α
deriving Ring, Inhabited, Nontrivial

Depends on / 依赖: FreeAbelianGroup, FreeMonoid
-/
def FreeRing (α : Type u) : Type u :=
FreeAbelianGroup FreeMonoid α
deriving Ring, Inhabited, Nontrivial

namespace FreeRing

variable {α : Type u}

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (x : α)
  body: FreeAbelianGroup.of (FreeMonoid.of x)

中文:
定义 of
  签名: (x : α)
  定义体: FreeAbelianGroup.of (FreeMonoid.of x)

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.of, FreeMonoid, FreeMonoid.of
-/
def of (x : α) : FreeRing α :=
  FreeAbelianGroup.of (FreeMonoid.of x)

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: Function.Injective (of : α -> FreeRing α)
  proof: FreeAbelianGroup.of_injective.comp FreeMonoid.of_injective

@[simp]

中文:
定理 of_injective
  结论: 函数.单射 (of : α -> FreeRing α)
  证明: FreeAbelianGroup.of_injective.comp FreeMonoid.of_injective

@[simp]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.of_injective.comp, FreeMonoid, FreeMonoid.of_injective, of_injective
-/
theorem of_injective : Function.Injective (of : α -> FreeRing α) :=
  FreeAbelianGroup.of_injective.comp FreeMonoid.of_injective

@[simp]
/--
theorem `of_ne_zero` / 定理 `of_ne_zero`

English:
theorem of_ne_zero
  given: (x : α)
  statement: of x != 0
  proof: FreeAbelianGroup.of_ne_zero _

@[simp]

中文:
定理 of_ne_zero
  条件: (x : α)
  结论: of x != 0
  证明: FreeAbelianGroup.of_ne_zero _

@[simp]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.of_ne_zero, of_ne_zero
-/
theorem of_ne_zero (x : α) : of x != 0 := FreeAbelianGroup.of_ne_zero _

@[simp]
/--
theorem `zero_ne_of` / 定理 `zero_ne_of`

English:
theorem zero_ne_of
  given: (x : α)
  statement: 0 != of x
  proof: FreeAbelianGroup.zero_ne_of _

@[simp]

中文:
定理 zero_ne_of
  条件: (x : α)
  结论: 0 != of x
  证明: FreeAbelianGroup.zero_ne_of _

@[simp]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.zero_ne_of, zero_ne_of
-/
theorem zero_ne_of (x : α) : 0 != of x := FreeAbelianGroup.zero_ne_of _

@[simp]
/--
theorem `of_ne_one` / 定理 `of_ne_one`

English:
theorem of_ne_one
  given: (x : α)
  statement: of x != 1
  proof: FreeAbelianGroup.of_injective.ne FreeMonoid.of_ne_one _

@[simp]

中文:
定理 of_ne_one
  条件: (x : α)
  结论: of x != 1
  证明: FreeAbelianGroup.of_injective.ne FreeMonoid.of_ne_one _

@[simp]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.of_injective.ne, FreeMonoid, FreeMonoid.of_ne_one, of_injective, of_ne_one
-/
theorem of_ne_one (x : α) : of x != 1 := FreeAbelianGroup.of_injective.ne FreeMonoid.of_ne_one _

@[simp]
/--
theorem `one_ne_of` / 定理 `one_ne_of`

English:
theorem one_ne_of
  given: (x : α)
  statement: 1 != of x
  proof: FreeAbelianGroup.of_injective.ne FreeMonoid.one_ne_of _

@[elab_as_elim, induction_eliminator]

中文:
定理 one_ne_of
  条件: (x : α)
  结论: 1 != of x
  证明: FreeAbelianGroup.of_injective.ne FreeMonoid.one_ne_of _

@[elab_as_elim, induction_eliminator]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.of_injective.ne, FreeMonoid, FreeMonoid.one_ne_of, of_injective, one_ne_of
-/
theorem one_ne_of (x : α) : 1 != of x := FreeAbelianGroup.of_injective.ne FreeMonoid.one_ne_of _

@[elab_as_elim, induction_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {C : FreeRing α -> Prop} (z : FreeRing α) (hn1 : C (-1))
  proof: have hn : forall x, C x -> C (-x) := fun x ih => neg_one_mul x ▸ hm _ _ hn1 ih
  have h1 : C 1 := neg_neg (1 : FreeRing α) ▸ hn _ hn1
  FreeAbelianGroup.induction_on z (neg_add_cancel (1 : FreeRing α) ▸ ha _ _ hn1 h1)
    (fun m => List.recOn m h1 fun a _ ih => hm _ _ (hb a) ih)
    (fun _ ih => hn 

中文:
定理 induction_on
  结论: {C : FreeRing α -> 命题} (z : FreeRing α) (hn1 : C (-1))
  证明: have hn : forall x, C x -> C (-x) := fun x ih => neg_one_mul x ▸ hm _ _ hn1 ih
  have h1 : C 1 := neg_neg (1 : FreeRing α) ▸ hn _ hn1
  FreeAbelianGroup.induction_on z (neg_add_cancel (1 : FreeRing α) ▸ ha _ _ hn1 h1)
    (fun m => List.recOn m h1 fun a _ ih => hm _ _ (hb a) ih)
    (fun _ ih => hn 
-/
protected theorem induction_on {C : FreeRing α -> Prop} (z : FreeRing α) (hn1 : C (-1))
    (hb : forall b, C (of b)) (ha : forall x y, C x -> C y -> C (x + y)) (hm : forall x y, C x -> C y -> C (x * y)) :
    C z :=
  have hn : forall x, C x -> C (-x) := fun x ih => neg_one_mul x ▸ hm _ _ hn1 ih
  have h1 : C 1 := neg_neg (1 : FreeRing α) ▸ hn _ hn1
  FreeAbelianGroup.induction_on z (neg_add_cancel (1 : FreeRing α) ▸ ha _ _ hn1 h1)
    (fun m => List.recOn m h1 fun a _ ih => hm _ _ (hb a) ih)
    (fun _ ih => hn _ ih) ha

section lift

variable {R : Type v} [Ring R] (f : α -> R)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (α -> R) ≃ (FreeRing α ->+* R)
  body: FreeMonoid.lift.trans FreeAbelianGroup.liftMonoid

@[simp]

中文:
定义 lift
  签名: : (α -> R) ≃ (FreeRing α ->+* R)
  定义体: FreeMonoid.lift.trans FreeAbelianGroup.liftMonoid

@[simp]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.liftMonoid, FreeMonoid, FreeMonoid.lift.trans, liftMonoid
-/
def lift : (α -> R) ≃ (FreeRing α ->+* R) :=
  FreeMonoid.lift.trans FreeAbelianGroup.liftMonoid

@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (x : α)
  statement: lift f (of x) = f x
  proof: congr_fun (lift.left_inv f) x

@[simp]

中文:
定理 lift_of
  条件: (x : α)
  结论: lift f (of x) = f x
  证明: congr_fun (lift.left_inv f) x

@[simp]

Depends on / 依赖: congr_fun, left_inv, lift.left_inv
-/
theorem lift_of (x : α) : lift f (of x) = f x :=
  congr_fun (lift.left_inv f) x

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (f : FreeRing α ->+* R)
  statement: lift (f ∘ of) = f
  proof: lift.right_inv f

@[ext]

中文:
定理 lift_comp_of
  条件: (f : FreeRing α ->+* R)
  结论: lift (f ∘ of) = f
  证明: lift.right_inv f

@[ext]

Depends on / 依赖: lift.right_inv, right_inv
-/
theorem lift_comp_of (f : FreeRing α ->+* R) : lift (f ∘ of) = f :=
  lift.right_inv f

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: ⦃f g
  statement: FreeRing α ->+* R⦄ (h : forall x, f (of x) = g (of x)) : f = g
  proof: lift.symm.injective (funext h)

中文:
定理 hom_ext
  条件: ⦃f g
  结论: FreeRing α ->+* R⦄ (h : 对任意 x, f (of x) = g (of x)) : f = g
  证明: lift.symm.injective (funext h)

Depends on / 依赖: injective, lift.symm.injective
-/
theorem hom_ext ⦃f g : FreeRing α ->+* R⦄ (h : forall x, f (of x) = g (of x)) : f = g :=
  lift.symm.injective (funext h)

end lift

variable {β : Type v} (f : α -> β)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : FreeRing α ->+* FreeRing β
  body: lift of ∘ f

@[simp]

中文:
定义 map
  签名: : FreeRing α ->+* FreeRing β
  定义体: lift of ∘ f

@[simp]
-/
def map : FreeRing α ->+* FreeRing β :=
lift of ∘ f

@[simp]
/--
theorem `map_of` / 定理 `map_of`

English:
theorem map_of
  given: (x : α)
  statement: map f (of x) = of (f x)
  proof: lift_of _ _

中文:
定理 map_of
  条件: (x : α)
  结论: map f (of x) = of (f x)
  证明: lift_of _ _

Depends on / 依赖: lift_of
-/
theorem map_of (x : α) : map f (of x) = of (f x) :=
  lift_of _ _

end FreeRing
