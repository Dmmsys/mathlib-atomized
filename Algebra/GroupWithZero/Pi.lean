/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# Pi instances for groups with zero

This file defines monoid with zero, group with zero, and related structure instances for pi types.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {ι : Type*} {α : ι -> Type*}

namespace Pi

section MulZeroClass
variable [forall i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : forall i, α i}

/--
Instance `mulZeroClass` / 实例 `mulZeroClass`

English:
instance mulZeroClass
  signature: : MulZeroClass (forall i, α i) where
  body: by intros; ext; exact zero_mul _
  mul_zero := by intros; ext; exact mul_zero _

中文:
实例 mulZeroClass
  签名: : 乘零类 (对任意 i, α i) where
  定义体: by intros; ext; exact zero_mul _
  mul_zero := by intros; ext; exact mul_zero _

Depends on / 依赖: intros, mul_zero, nullHomotopicMap, nullHomotopicMap_f_of_not_rel_left, split_ifs, zero_mul
-/
instance mulZeroClass : MulZeroClass (forall i, α i) where
  zero_mul := by intros; ext; exact zero_mul _
  mul_zero := by intros; ext; exact mul_zero _

/-- The multiplicative homomorphism including a single `MulZeroClass`
into a dependent family of `MulZeroClass`es, as functions supported at a point.

This is the `MulHom` version of `Pi.single`. -/
@[simps]
/--
Definition of `_root_.MulHom.single` / `_root_.MulHom.single` 的定义

English:
definition _root_.MulHom.single
  signature: (i : ι)
  body: Pi.single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _

中文:
定义 _root_.乘法半群态射.single
  签名: (i : ι)
  定义体: Pi.single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _

Depends on / 依赖: Pi.single, single
-/
def _root_.MulHom.single (i : ι) : α i ->ₙ* forall i, α i where
  toFun := Pi.single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _

/--
lemma `single_mul` / 引理 `single_mul`

English:
lemma single_mul
  given: (i : ι) (x y : α i)
  statement: single i (x * y) = single i x * single i y
  proof: (MulHom.single _).map_mul _ _

中文:
引理 single_mul
  条件: (i : ι) (x y : α i)
  结论: single i (x * y) = single i x * single i y
  证明: (MulHom.single _).map_mul _ _

Depends on / 依赖: MulHom, MulHom.single, map_mul, nullHomotopicMap, nullHomotopicMap_f_of_not_rel_right, single, split_ifs
-/
lemma single_mul (i : ι) (x y : α i) : single i (x * y) = single i x * single i y :=
  (MulHom.single _).map_mul _ _

/--
lemma `single_mul_left_apply` / 引理 `single_mul_left_apply`

English:
lemma single_mul_left_apply
  given: (i j : ι) (a : α i) (f : forall i, α i)
  proof: (apply_single (fun i => (· * f i)) (fun _ => zero_mul _) _ _ _).symm

中文:
引理 single_mul_left_apply
  条件: (i j : ι) (a : α i) (f : 对任意 i, α i)
  证明: (apply_single (fun i => (· * f i)) (fun _ => zero_mul _) _ _ _).symm

Depends on / 依赖: apply_single, zero_mul
-/
lemma single_mul_left_apply (i j : ι) (a : α i) (f : forall i, α i) :
    single i (a * f i) j = single i a j * f j :=
  (apply_single (fun i => (· * f i)) (fun _ => zero_mul _) _ _ _).symm

/--
lemma `single_mul_right_apply` / 引理 `single_mul_right_apply`

English:
lemma single_mul_right_apply
  given: (i j : ι) (f : forall i, α i) (a : α i)
  proof: (apply_single (f · * ·) (fun _ => mul_zero _) _ _ _).symm

中文:
引理 single_mul_right_apply
  条件: (i j : ι) (f : 对任意 i, α i) (a : α i)
  证明: (apply_single (f · * ·) (fun _ => mul_zero _) _ _ _).symm

Depends on / 依赖: apply_single, mul_zero, nullHomotopicMap, nullHomotopicMap_f_eq_zero
-/
lemma single_mul_right_apply (i j : ι) (f : forall i, α i) (a : α i) :
    single i (f i * a) j = f j * single i a j :=
  (apply_single (f · * ·) (fun _ => mul_zero _) _ _ _).symm

/--
lemma `single_mul_left` / 引理 `single_mul_left`

English:
lemma single_mul_left
  given: (a : α i)
  statement: single i (a * f i) = single i a * f
  proof: funext fun _ => single_mul_left_apply _ _ _ _

中文:
引理 single_mul_left
  条件: (a : α i)
  结论: single i (a * f i) = single i a * f
  证明: funext fun _ => single_mul_left_apply _ _ _ _

Depends on / 依赖: single_mul_left_apply
-/
lemma single_mul_left (a : α i) : single i (a * f i) = single i a * f :=
  funext fun _ => single_mul_left_apply _ _ _ _

/--
lemma `single_mul_right` / 引理 `single_mul_right`

English:
lemma single_mul_right
  given: (a : α i)
  statement: single i (f i * a) = f * single i a
  proof: funext fun _ => single_mul_right_apply _ _ _ _

中文:
引理 single_mul_right
  条件: (a : α i)
  结论: single i (f i * a) = f * single i a
  证明: funext fun _ => single_mul_right_apply _ _ _ _

Depends on / 依赖: single_mul_right_apply
-/
lemma single_mul_right (a : α i) : single i (f i * a) = f * single i a :=
  funext fun _ => single_mul_right_apply _ _ _ _

end MulZeroClass

/--
Instance `mulZeroOneClass` / 实例 `mulZeroOneClass`

English:
instance mulZeroOneClass
  signature: [forall i, MulZeroOneClass (α i)]
  body: mulZeroClass
  __ := mulOneClass

中文:
实例 mulZeroOneClass
  签名: [对任意 i, 乘零幺类 (α i)]
  定义体: mulZeroClass
  __ := mulOneClass

Depends on / 依赖: mulZeroClass
-/
instance mulZeroOneClass [forall i, MulZeroOneClass (α i)] : MulZeroOneClass (forall i, α i) where
  __ := mulZeroClass
  __ := mulOneClass

/--
Instance `monoidWithZero` / 实例 `monoidWithZero`

English:
instance monoidWithZero
  signature: [forall i, MonoidWithZero (α i)]
  body: monoid
  __ := mulZeroClass

中文:
实例 monoidWithZero
  签名: [对任意 i, 带零幺半群 (α i)]
  定义体: monoid
  __ := mulZeroClass

Depends on / 依赖: monoid
-/
instance monoidWithZero [forall i, MonoidWithZero (α i)] : MonoidWithZero (forall i, α i) where
  __ := monoid
  __ := mulZeroClass

/--
Instance `commMonoidWithZero` / 实例 `commMonoidWithZero`

English:
instance commMonoidWithZero
  signature: [forall i, CommMonoidWithZero (α i)]
  body: monoidWithZero
  __ := commMonoid

中文:
实例 commMonoidWithZero
  签名: [对任意 i, 带零交换幺半群 (α i)]
  定义体: monoidWithZero
  __ := commMonoid

Depends on / 依赖: monoidWithZero
-/
instance commMonoidWithZero [forall i, CommMonoidWithZero (α i)] : CommMonoidWithZero (forall i, α i) where
  __ := monoidWithZero
  __ := commMonoid

/--
Instance `semigroupWithZero` / 实例 `semigroupWithZero`

English:
instance semigroupWithZero
  signature: [forall i, SemigroupWithZero (α i)]
  body: semigroup
  __ := mulZeroClass

中文:
实例 semigroupWithZero
  签名: [对任意 i, 带零半群 (α i)]
  定义体: semigroup
  __ := mulZeroClass

Depends on / 依赖: semigroup
-/
instance semigroupWithZero [forall i, SemigroupWithZero (α i)] : SemigroupWithZero (forall i, α i) where
  __ := semigroup
  __ := mulZeroClass

end Pi
