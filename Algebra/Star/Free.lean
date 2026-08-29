/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.FreeAlgebra

/-!
# A \*-algebra structure on the free algebra.

Reversing words gives a \*-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `Algebra.FreeMonoid` and `Algebra.FreeAlgebra`,
to avoid importing `Algebra.Star.Basic` into the entire hierarchy.
-/

@[expose] public section


namespace FreeMonoid

variable {α : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (FreeMonoid α)
  body: List.reverse
  star_involutive := List.reverse_reverse
  star_mul := fun _ _ => List.reverse_append

@[simp]

中文:
实例 :
  签名: StarMul (FreeMonoid α)
  定义体: List.reverse
  star_involutive := List.reverse_reverse
  star_mul := fun _ _ => List.reverse_append

@[simp]

Depends on / 依赖: List.reverse, reverse
-/
instance : StarMul (FreeMonoid α) where
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := fun _ _ => List.reverse_append

@[simp]
/--
theorem `star_of` / 定理 `star_of`

English:
theorem star_of
  given: (x : α)
  statement: star (of x) = of x
  proof: rfl

中文:
定理 star_of
  条件: (x : α)
  结论: star (of x) = of x
  证明: rfl
-/
theorem star_of (x : α) : star (of x) = of x :=
  rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
/--
theorem `star_one` / 定理 `star_one`

English:
theorem star_one
  statement: star (1 : FreeMonoid α) = 1
  proof: rfl

中文:
定理 star_one
  结论: star (1 : FreeMonoid α) = 1
  证明: rfl
-/
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl

end FreeMonoid

namespace FreeAlgebra

variable {R : Type*} [CommSemiring R] {X : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (FreeAlgebra R X)
  body: MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    simp only [Function.comp_apply]
    let y := lift R (X := X) (MulOpposite.op ∘ ι R)
    refine induction (motive := fun x => (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
    · intros
      simp only [AlgHom.commutes, MulOpp

中文:
实例 :
  签名: StarRing (FreeAlgebra R X)
  定义体: MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    simp only [Function.comp_apply]
    let y := lift R (X := X) (MulOpposite.op ∘ ι R)
    refine induction (motive := fun x => (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
    · intros
      simp only [AlgHom.commutes, MulOpp

Depends on / 依赖: MulOpposite, MulOpposite.op, MulOpposite.unop
-/
instance : StarRing (FreeAlgebra R X) where
  star := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    simp only [Function.comp_apply]
    let y := lift R (X := X) (MulOpposite.op ∘ ι R)
    refine induction (motive := fun x => (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
    · intros
      simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    · intros
      simp only [y, lift_ι_apply, Function.comp_apply, MulOpposite.unop_op]
    · intros
      simp only [*, map_mul, MulOpposite.unop_mul]
    · intros
      simp only [*, map_add, MulOpposite.unop_add]
  star_mul a b := by simp only [Function.comp_apply, map_mul, MulOpposite.unop_mul]
  star_add a b := by simp only [Function.comp_apply, map_add, MulOpposite.unop_add]

@[simp]
/--
theorem `star_ι` / 定理 `star_ι`

English:
theorem star_ι
  given: (x : X)
  statement: star (ι R x) = ι R x
  proof: by simp [star, Star.star]

@[simp]

中文:
定理 star_ι
  条件: (x : X)
  结论: star (ι R x) = ι R x
  证明: by simp [star, Star.star]

@[simp]

Depends on / 依赖: Star.star
-/
theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]

@[simp]
/--
theorem `star_algebraMap` / 定理 `star_algebraMap`

English:
theorem star_algebraMap
  given: (r : R)
  statement: star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r
  proof: by
  simp [star, Star.star]

中文:
定理 star_algebraMap
  条件: (r : R)
  结论: star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r
  证明: by
  simp [star, Star.star]

Depends on / 依赖: Star.star
-/
theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]

/--
Definition of `starHom` / `starHom` 的定义

English:
definition starHom
  signature: : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ
  body: { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }

中文:
定义 starHom
  签名: : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ
  定义体: { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }

Depends on / 依赖: commutes, starRingEquiv, star_algebraMap
-/
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }

end FreeAlgebra
