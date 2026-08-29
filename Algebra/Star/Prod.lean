/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Star.Basic

/-!
# Basic Results about Star on Product Type

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Prod.lean`.

-/

public section


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [Star S] [TrivialStar R] [TrivialStar S] : TrivialStar (R × S) where
  body: Prod.ext (star_trivial _) (star_trivial _)

中文:
实例 [对合
  签名: R] [对合 S] [TrivialStar R] [TrivialStar S] : TrivialStar (R × S) where
  定义体: Prod.ext (star_trivial _) (star_trivial _)

Depends on / 依赖: Prod.ext, star_trivial
-/
instance [Star R] [Star S] [TrivialStar R] [TrivialStar S] : TrivialStar (R × S) where
  star_trivial _ := Prod.ext (star_trivial _) (star_trivial _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: R] [InvolutiveStar S] : InvolutiveStar (R × S) where
  body: Prod.ext (star_star _) (star_star _)

中文:
实例 [InvolutiveStar
  签名: R] [InvolutiveStar S] : InvolutiveStar (R × S) where
  定义体: Prod.ext (star_star _) (star_star _)

Depends on / 依赖: Prod.ext, star_star
-/
instance [InvolutiveStar R] [InvolutiveStar S] : InvolutiveStar (R × S) where
  star_involutive _ := Prod.ext (star_star _) (star_star _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Mul S] [StarMul R] [StarMul S] : StarMul (R × S) where
  body: Prod.ext (star_mul _ _) (star_mul _ _)

中文:
实例 [乘法
  签名: R] [乘法 S] [StarMul R] [StarMul S] : StarMul (R × S) where
  定义体: Prod.ext (star_mul _ _) (star_mul _ _)

Depends on / 依赖: Prod.ext, star_mul
-/
instance [Mul R] [Mul S] [StarMul R] [StarMul S] : StarMul (R × S) where
  star_mul _ _ := Prod.ext (star_mul _ _) (star_mul _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] [AddMonoid S] [StarAddMonoid R] [StarAddMonoid S] :
  body: Prod.ext (star_add _ _) (star_add _ _)

中文:
实例 [加法幺半群
  签名: R] [加法幺半群 S] [StarAdd幺半群 R] [StarAdd幺半群 S] :
  定义体: Prod.ext (star_add _ _) (star_add _ _)
-/
instance [AddMonoid R] [AddMonoid S] [StarAddMonoid R] [StarAddMonoid S] :
    StarAddMonoid (R × S) where
  star_add _ _ := Prod.ext (star_add _ _) (star_add _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [NonUnitalNonAssocSemiring S] [StarRing R] [StarRing S] :
  body: { (inferInstance : StarAddMonoid (R × S)),
    (inferInstance : StarMul (R × S)) with }

中文:
实例 [非幺非结合半环
  签名: R] [非幺非结合半环 S] [对合环 R] [对合环 S] :
  定义体: { (inferInstance : StarAddMonoid (R × S)),
    (inferInstance : StarMul (R × S)) with }

Depends on / 依赖: StarAddMonoid, StarMul
-/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [StarRing R] [StarRing S] :
    StarRing (R × S) :=
  { (inferInstance : StarAddMonoid (R × S)),
    (inferInstance : StarMul (R × S)) with }

instance {α : Type w} [SMul α R] [SMul α S] [Star α] [Star R] [Star S]
    [StarModule α R] [StarModule α S] : StarModule α (R × S) where
  star_smul _ _ := Prod.ext (star_smul _ _) (star_smul _ _)

end Prod

/--
theorem `Units.embed_product_star` / 定理 `Units.embed_product_star`

English:
theorem Units.embed_product_star
  given: [Monoid R] [StarMul R] (u : Rˣ)
  proof: rfl

中文:
定理 单位群.embed_product_star
  条件: [幺半群 R] [StarMul R] (u : Rˣ)
  证明: rfl
-/
theorem Units.embed_product_star [Monoid R] [StarMul R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) :=
  rfl
