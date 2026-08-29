/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Basic Results about Star on Pi Types

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Pi/Defs.lean`.
-/

public section


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I -> Type v}

-- The family of types already equipped with instances
namespace Pi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Star (f i)] [forall i, TrivialStar (f i)] : TrivialStar (forall i, f i) where
  body: funext fun _ => star_trivial _

中文:
实例 [对任意
  签名: i, 对合 (f i)] [对任意 i, TrivialStar (f i)] : TrivialStar (对任意 i, f i) where
  定义体: funext fun _ => star_trivial _

Depends on / 依赖: star_trivial
-/
instance [forall i, Star (f i)] [forall i, TrivialStar (f i)] : TrivialStar (forall i, f i) where
  star_trivial _ := funext fun _ => star_trivial _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, InvolutiveStar (f i)] : InvolutiveStar (forall i, f i) where
  body: funext fun _ => star_star _

中文:
实例 [对任意
  签名: i, InvolutiveStar (f i)] : InvolutiveStar (对任意 i, f i) where
  定义体: funext fun _ => star_star _

Depends on / 依赖: star_star
-/
instance [forall i, InvolutiveStar (f i)] : InvolutiveStar (forall i, f i) where
  star_involutive _ := funext fun _ => star_star _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Mul (f i)] [forall i, StarMul (f i)] : StarMul (forall i, f i) where
  body: funext fun _ => star_mul _ _

中文:
实例 [对任意
  签名: i, 乘法 (f i)] [对任意 i, StarMul (f i)] : StarMul (对任意 i, f i) where
  定义体: funext fun _ => star_mul _ _

Depends on / 依赖: star_mul
-/
instance [forall i, Mul (f i)] [forall i, StarMul (f i)] : StarMul (forall i, f i) where
  star_mul _ _ := funext fun _ => star_mul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddMonoid (f i)] [forall i, StarAddMonoid (f i)] : StarAddMonoid (forall i, f i) where
  body: funext fun _ => star_add _ _

中文:
实例 [对任意
  签名: i, 加法幺半群 (f i)] [对任意 i, StarAdd幺半群 (f i)] : StarAdd幺半群 (对任意 i, f i) where
  定义体: funext fun _ => star_add _ _

Depends on / 依赖: star_add
-/
instance [forall i, AddMonoid (f i)] [forall i, StarAddMonoid (f i)] : StarAddMonoid (forall i, f i) where
  star_add _ _ := funext fun _ => star_add _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalSemiring (f i)] [forall i, StarRing (f i)] : StarRing (forall i, f i)
  body: funext fun _ => star_add _ _

中文:
实例 [对任意
  签名: i, 非幺半环 (f i)] [对任意 i, 对合环 (f i)] : 对合环 (对任意 i, f i)
  定义体: funext fun _ => star_add _ _

Depends on / 依赖: star_add
-/
instance [forall i, NonUnitalSemiring (f i)] [forall i, StarRing (f i)] : StarRing (forall i, f i)
  where star_add _ _ := funext fun _ => star_add _ _

instance {R : Type w} [forall i, SMul R (f i)] [Star R] [forall i, Star (f i)]
    [forall i, StarModule R (f i)] : StarModule R (forall i, f i) where
  star_smul r x := funext fun i => star_smul r (x i)

/--
theorem `single_star` / 定理 `single_star`

English:
theorem single_star
  statement: [forall i, AddMonoid (f i)] [forall i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
  proof: single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

中文:
定理 single_star
  结论: [对任意 i, 加法幺半群 (f i)] [对任意 i, StarAdd幺半群 (f i)] [DecidableEq I] (i : I)
  证明: single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

Depends on / 依赖: single_op, star_zero
-/
theorem single_star [forall i, AddMonoid (f i)] [forall i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

open scoped ComplexConjugate

@[simp]
/--
lemma `conj_apply` / 引理 `conj_apply`

English:
lemma conj_apply
  statement: {ι : Type*} {α : ι -> Type*} [forall i, CommSemiring (α i)] [forall i, StarRing (α i)]
  proof: rfl

中文:
引理 conj_apply
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, 交换半环 (α i)] [对任意 i, 对合环 (α i)]
  证明: rfl
-/
lemma conj_apply {ι : Type*} {α : ι -> Type*} [forall i, CommSemiring (α i)] [forall i, StarRing (α i)]
    (f : forall i, α i) (i : ι) : conj f i = conj (f i) := rfl

end Pi

namespace Function

/--
theorem `update_star` / 定理 `update_star`

English:
theorem update_star
  given: [forall i, Star (f i)] [DecidableEq I] (h : forall i : I, f i) (i : I) (a : f i)
  proof: funext fun j => (apply_update (fun _ => star) h i a j).symm

中文:
定理 update_star
  条件: [对任意 i, 对合 (f i)] [DecidableEq I] (h : 对任意 i : I, f i) (i : I) (a : f i)
  证明: funext fun j => (apply_update (fun _ => star) h i a j).symm

Depends on / 依赖: apply_update
-/
theorem update_star [forall i, Star (f i)] [DecidableEq I] (h : forall i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun _ => star) h i a j).symm

/--
theorem `star_sumElim` / 定理 `star_sumElim`

English:
theorem star_sumElim
  given: {I J α : Type*} (x : I -> α) (y : J -> α) [Star α]
  proof: by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

中文:
定理 star_sumElim
  条件: {I J α : 类型} (x : I -> α) (y : J -> α) [对合 α]
  证明: by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

Depends on / 依赖: Pi.star_apply, Sum.elim_inl, Sum.elim_inr, elim_inl, elim_inr, star_apply
-/
theorem star_sumElim {I J α : Type*} (x : I -> α) (y : J -> α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

end Function
