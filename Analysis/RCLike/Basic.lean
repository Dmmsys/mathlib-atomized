/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.BigOperators.Balance
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# `RCLike`: a typeclass for ℝ or ℂ

This file defines the typeclass `RCLike` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Applications include defining inner products and Hilbert spaces for both the real and
complex case. One typically produces the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `Mathlib/Analysis/Complex/Basic.lean`.

## Implementation notes

The coercion from reals into an `RCLike` field is done by registering `RCLike.ofReal` as
a `CoeTC`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `Coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `Mathlib/Data/Nat/Cast/Defs.lean`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `Mathlib/Analysis/Complex/Basic.lean` (which causes linter errors).

A few lemmas requiring heavier imports are in `Mathlib/Analysis/RCLike/Lemmas.lean`.
-/

@[expose] public section

open Fintype
open scoped BigOperators ComplexConjugate

section

local notation "𝓚" => algebraMap Real _

/--
Definition of `RCLike` / `RCLike` 的定义

English:
class RCLike
  parameters: (K : semiOutParam Type*)
  extends: DenselyNormedField K, StarRing K, 
  axioms and operations (18):
    - re : K ->+ Real
    - im : K ->+ Real
    - I : K
    - I_re_ax : re I = 0
    - I_mul_I_ax : I = 0 ∨ I * I = -1
    - re_add_im_ax : forall z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
    - ofReal_re_ax : forall r : Real, re (𝓚 r) = r
    - ofReal_im_ax : forall r : Real, im (𝓚 r) = 0
    - mul_re_ax : forall z w : K, re (z * w) = re z * re w - im z * im w
    - mul_im_ax : forall z w : K, im (z * w) = re z * im w + im z * re w
    - conj_re_ax : forall z : K, re (conj z) = re z
    - conj_im_ax : forall z : K, im (conj z) = -im z
    - conj_I_ax : conj I = -I
    - norm_sq_eq_def_ax : forall z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
    - mul_im_I_ax : forall z : K, im z * im I = im z
    - [toPartialOrder : PartialOrder K]
    - le_iff_re_im({z w : K}) : z <= w ↔ re z <= re w ∧ im z = im w
    - [toDecidableEq : DecidableEq K]

中文:
类 RCLike
  参数: (K : semiOutParam 类型)
  继承: DenselyNormedField K, 对合环 K, 
  公理与运算 (18 个):
    - re : K ->+ 实数
    - im : K ->+ 实数
    - I : K
    - I_re_ax : re I = 0
    - I_mul_I_ax : I = 0 ∨ I * I = -1
    - re_add_im_ax : 对任意 z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
    - ofReal_re_ax : 对任意 r : 实数, re (𝓚 r) = r
    - ofReal_im_ax : 对任意 r : 实数, im (𝓚 r) = 0
    - mul_re_ax : 对任意 z w : K, re (z * w) = re z * re w - im z * im w
    - mul_im_ax : 对任意 z w : K, im (z * w) = re z * im w + im z * re w
    - conj_re_ax : 对任意 z : K, re (conj z) = re z
    - conj_im_ax : 对任意 z : K, im (conj z) = -im z
    - conj_I_ax : conj I = -I
    - norm_sq_eq_def_ax : 对任意 z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
    - mul_im_I_ax : 对任意 z : K, im z * im I = im z
    - [toPartialOrder : 偏序 K]
    - le_iff_re_im({z w : K}) : z <= w ↔ re z <= re w ∧ im z = im w
    - [toDecidableEq : DecidableEq K]
-/
class RCLike (K : semiOutParam Type*) extends DenselyNormedField K, StarRing K,
    NormedAlgebra Real K, CompleteSpace K where
  /-- The real part as an additive monoid homomorphism -/
  re : K ->+ Real
  /-- The imaginary part as an additive monoid homomorphism -/
  im : K ->+ Real
  /-- Imaginary unit in `K`. Meant to be set to `0` for `K = ℝ`. -/
  I : K
  I_re_ax : re I = 0
  I_mul_I_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : forall z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
  ofReal_re_ax : forall r : Real, re (𝓚 r) = r
  ofReal_im_ax : forall r : Real, im (𝓚 r) = 0
  mul_re_ax : forall z w : K, re (z * w) = re z * re w - im z * im w
  mul_im_ax : forall z w : K, im (z * w) = re z * im w + im z * re w
  conj_re_ax : forall z : K, re (conj z) = re z
  conj_im_ax : forall z : K, im (conj z) = -im z
  conj_I_ax : conj I = -I
  norm_sq_eq_def_ax : forall z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
  mul_im_I_ax : forall z : K, im z * im I = im z
  /-- only an instance in the `ComplexOrder` scope -/
  [toPartialOrder : PartialOrder K]
  le_iff_re_im {z w : K} : z <= w ↔ re z <= re w ∧ im z = im w
  -- note we cannot put this in the `extends` clause
  [toDecidableEq : DecidableEq K]

attribute [instance_reducible] RCLike.toPartialOrder RCLike.toDecidableEq
scoped[ComplexOrder] attribute [instance 100] RCLike.toPartialOrder
attribute [instance 100] RCLike.toDecidableEq

end

variable {K E : Type*} [RCLike K]

namespace RCLike

/--
Definition of `ofReal` / `ofReal` 的定义

English:
abbreviation ofReal
  signature: : Real -> K
  body: Algebra.cast

中文:
缩写 of实数
  签名: : 实数 -> K
  定义体: Algebra.cast
-/
@[coe] abbrev ofReal : Real -> K := Algebra.cast

/-- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `Mathlib/Data/Nat/Cast/Basic.lean` for more details. -/
noncomputable instance (priority := 900) algebraMapCoe : CoeTC Real K :=
  ⟨ofReal⟩

/--
theorem `ofReal_alg` / 定理 `ofReal_alg`

English:
theorem ofReal_alg
  given: (x : Real)
  statement: (x : K) = x • (1 : K)
  proof: Algebra.algebraMap_eq_smul_one x

中文:
定理 of实数_alg
  条件: (x : 实数)
  结论: (x : K) = x • (1 : K)
  证明: Algebra.algebraMap_eq_smul_one x

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
theorem ofReal_alg (x : Real) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x

/--
theorem `real_smul_eq_coe_mul` / 定理 `real_smul_eq_coe_mul`

English:
theorem real_smul_eq_coe_mul
  given: (r : Real) (z : K)
  statement: r • z = (r : K) * z
  proof: Algebra.smul_def r z

中文:
定理 real_smul_eq_coe_mul
  条件: (r : 实数) (z : K)
  结论: r • z = (r : K) * z
  证明: Algebra.smul_def r z

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
theorem real_smul_eq_coe_mul (r : Real) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z

/--
theorem `real_smul_eq_coe_smul` / 定理 `real_smul_eq_coe_smul`

English:
theorem real_smul_eq_coe_smul
  statement: [AddCommGroup E] [Module K E] [Module Real E] [IsScalarTower Real K E]
  proof: by rw [RCLike.ofReal_alg, smul_one_smul]

中文:
定理 real_smul_eq_coe_smul
  结论: [加法交换群 E] [模 K E] [模 实数 E] [标量塔 实数 K E]
  证明: by rw [RCLike.ofReal_alg, smul_one_smul]

Depends on / 依赖: RCLike, RCLike.ofReal_alg, ofReal_alg, smul_one_smul
-/
theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module Real E] [IsScalarTower Real K E]
    (r : Real) (x : E) : r • x = (r : K) • x := by rw [RCLike.ofReal_alg, smul_one_smul]

/--
theorem `algebraMap_eq_ofReal` / 定理 `algebraMap_eq_ofReal`

English:
theorem algebraMap_eq_ofReal
  statement: ⇑(algebraMap Real K) = ofReal
  proof: rfl

@[simp, rclike_simps]

中文:
定理 algebraMap_eq_of实数
  结论: ⇑(algebraMap 实数 K) = of实数
  证明: rfl

@[simp, rclike_simps]
-/
theorem algebraMap_eq_ofReal : ⇑(algebraMap Real K) = ofReal :=
  rfl

@[simp, rclike_simps]
/--
theorem `re_add_im` / 定理 `re_add_im`

English:
theorem re_add_im
  given: (z : K)
  statement: (re z : K) + im z * I = z
  proof: RCLike.re_add_im_ax z

@[simp, norm_cast, rclike_simps]

中文:
定理 re_add_im
  条件: (z : K)
  结论: (re z : K) + im z * I = z
  证明: RCLike.re_add_im_ax z

@[simp, norm_cast, rclike_simps]

Depends on / 依赖: RCLike, RCLike.re_add_im_ax, re_add_im_ax
-/
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  RCLike.re_add_im_ax z

@[simp, norm_cast, rclike_simps]
/--
theorem `ofReal_re` / 定理 `ofReal_re`

English:
theorem ofReal_re
  statement: forall r : Real, re (r : K) = r
  proof: RCLike.ofReal_re_ax

@[simp, norm_cast, rclike_simps]

中文:
定理 of实数_re
  结论: 对任意 r : 实数, re (r : K) = r
  证明: RCLike.ofReal_re_ax

@[simp, norm_cast, rclike_simps]

Depends on / 依赖: RCLike, RCLike.ofReal_re_ax, ofReal_re_ax
-/
theorem ofReal_re : forall r : Real, re (r : K) = r :=
  RCLike.ofReal_re_ax

@[simp, norm_cast, rclike_simps]
/--
theorem `ofReal_im` / 定理 `ofReal_im`

English:
theorem ofReal_im
  statement: forall r : Real, im (r : K) = 0
  proof: RCLike.ofReal_im_ax

@[simp, rclike_simps]

中文:
定理 of实数_im
  结论: 对任意 r : 实数, im (r : K) = 0
  证明: RCLike.ofReal_im_ax

@[simp, rclike_simps]

Depends on / 依赖: RCLike, RCLike.ofReal_im_ax, ofReal_im_ax
-/
theorem ofReal_im : forall r : Real, im (r : K) = 0 :=
  RCLike.ofReal_im_ax

@[simp, rclike_simps]
/--
theorem `mul_re` / 定理 `mul_re`

English:
theorem mul_re
  statement: forall z w : K, re (z * w) = re z * re w - im z * im w
  proof: RCLike.mul_re_ax

@[simp, rclike_simps]

中文:
定理 mul_re
  结论: 对任意 z w : K, re (z * w) = re z * re w - im z * im w
  证明: RCLike.mul_re_ax

@[simp, rclike_simps]

Depends on / 依赖: RCLike, RCLike.mul_re_ax, mul_re_ax
-/
theorem mul_re : forall z w : K, re (z * w) = re z * re w - im z * im w :=
  RCLike.mul_re_ax

@[simp, rclike_simps]
/--
theorem `mul_im` / 定理 `mul_im`

English:
theorem mul_im
  statement: forall z w : K, im (z * w) = re z * im w + im z * re w
  proof: RCLike.mul_im_ax

中文:
定理 mul_im
  结论: 对任意 z w : K, im (z * w) = re z * im w + im z * re w
  证明: RCLike.mul_im_ax

Depends on / 依赖: RCLike, RCLike.mul_im_ax, mul_im_ax
-/
theorem mul_im : forall z w : K, im (z * w) = re z * im w + im z * re w :=
  RCLike.mul_im_ax

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {z w : K}
  statement: z = w ↔ re z = re w ∧ im z = im w
  proof: ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

中文:
定理 ext_iff
  条件: {z w : K}
  结论: z = w ↔ re z = re w ∧ im z = im w
  证明: ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

Depends on / 依赖: X.property, property, re_add_im
-/
theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {z w : K} (hre : re z = re w) (him : im z = im w)
  statement: z = w
  proof: ext_iff.2 ⟨hre, him⟩

@[norm_cast]

中文:
定理 ext
  条件: {z w : K} (hre : re z = re w) (him : im z = im w)
  结论: z = w
  证明: ext_iff.2 ⟨hre, him⟩

@[norm_cast]

Depends on / 依赖: ext_iff
-/
theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩

@[norm_cast]
/--
theorem `ofReal_zero` / 定理 `ofReal_zero`

English:
theorem ofReal_zero
  statement: ((0 : Real) : K) = 0
  proof: algebraMap.coe_zero

@[rclike_simps]

中文:
定理 of实数_zero
  结论: ((0 : 实数) : K) = 0
  证明: algebraMap.coe_zero

@[rclike_simps]

Depends on / 依赖: algebraMap, algebraMap.coe_zero, coe_zero
-/
theorem ofReal_zero : ((0 : Real) : K) = 0 :=
  algebraMap.coe_zero

@[rclike_simps]
/--
theorem `zero_re` / 定理 `zero_re`

English:
theorem zero_re
  statement: re (0 : K) = (0 : Real)
  proof: map_zero re

@[rclike_simps]

中文:
定理 zero_re
  结论: re (0 : K) = (0 : 实数)
  证明: map_zero re

@[rclike_simps]

Depends on / 依赖: map_zero
-/
theorem zero_re : re (0 : K) = (0 : Real) :=
  map_zero re

@[rclike_simps]
/--
theorem `zero_im` / 定理 `zero_im`

English:
theorem zero_im
  statement: im (0 : K) = (0 : Real)
  proof: map_zero im

@[norm_cast]

中文:
定理 zero_im
  结论: im (0 : K) = (0 : 实数)
  证明: map_zero im

@[norm_cast]

Depends on / 依赖: map_zero
-/
theorem zero_im : im (0 : K) = (0 : Real) :=
  map_zero im

@[norm_cast]
/--
theorem `ofReal_one` / 定理 `ofReal_one`

English:
theorem ofReal_one
  statement: ((1 : Real) : K) = 1
  proof: map_one (algebraMap Real K)

@[simp, rclike_simps]

中文:
定理 of实数_one
  结论: ((1 : 实数) : K) = 1
  证明: map_one (algebraMap Real K)

@[simp, rclike_simps]

Depends on / 依赖: algebraMap, map_one
-/
theorem ofReal_one : ((1 : Real) : K) = 1 :=
  map_one (algebraMap Real K)

@[simp, rclike_simps]
/--
theorem `one_re` / 定理 `one_re`

English:
theorem one_re
  statement: re (1 : K) = 1
  proof: by rw [← ofReal_one, ofReal_re]

@[simp, rclike_simps]

中文:
定理 one_re
  结论: re (1 : K) = 1
  证明: by rw [← ofReal_one, ofReal_re]

@[simp, rclike_simps]

Depends on / 依赖: ofReal_one, ofReal_re
-/
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]

@[simp, rclike_simps]
/--
theorem `one_im` / 定理 `one_im`

English:
theorem one_im
  statement: im (1 : K) = 0
  proof: by rw [← ofReal_one, ofReal_im]

中文:
定理 one_im
  结论: im (1 : K) = 0
  证明: by rw [← ofReal_one, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_one
-/
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]

/--
theorem `ofReal_injective` / 定理 `ofReal_injective`

English:
theorem ofReal_injective
  statement: Function.Injective ((↑) : Real -> K)
  proof: (algebraMap Real K).injective

@[norm_cast]

中文:
定理 of实数_injective
  结论: 函数.单射 ((↑) : 实数 -> K)
  证明: (algebraMap Real K).injective

@[norm_cast]

Depends on / 依赖: algebraMap, injective
-/
theorem ofReal_injective : Function.Injective ((↑) : Real -> K) :=
  (algebraMap Real K).injective

@[norm_cast]
/--
theorem `ofReal_inj` / 定理 `ofReal_inj`

English:
theorem ofReal_inj
  given: {z w : Real}
  statement: (z : K) = (w : K) ↔ z = w
  proof: algebraMap.coe_inj _ _

中文:
定理 of实数_inj
  条件: {z w : 实数}
  结论: (z : K) = (w : K) ↔ z = w
  证明: algebraMap.coe_inj _ _

Depends on / 依赖: algebraMap, algebraMap.coe_inj, coe_inj
-/
theorem ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj _ _

/--
theorem `ofReal_eq_zero` / 定理 `ofReal_eq_zero`

English:
theorem ofReal_eq_zero
  given: {x : Real}
  statement: (x : K) = 0 ↔ x = 0
  proof: algebraMap.coe_eq_zero_iff _ _ _

中文:
定理 of实数_eq_zero
  条件: {x : 实数}
  结论: (x : K) = 0 ↔ x = 0
  证明: algebraMap.coe_eq_zero_iff _ _ _

Depends on / 依赖: algebraMap, algebraMap.coe_eq_zero_iff, coe_eq_zero_iff
-/
theorem ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.coe_eq_zero_iff _ _ _

/--
theorem `ofReal_ne_zero` / 定理 `ofReal_ne_zero`

English:
theorem ofReal_ne_zero
  given: {x : Real}
  statement: (x : K) != 0 ↔ x != 0
  proof: ofReal_eq_zero.not

@[rclike_simps, norm_cast]

中文:
定理 of实数_ne_zero
  条件: {x : 实数}
  结论: (x : K) != 0 ↔ x != 0
  证明: ofReal_eq_zero.not

@[rclike_simps, norm_cast]

Depends on / 依赖: ofReal_eq_zero, ofReal_eq_zero.not
-/
theorem ofReal_ne_zero {x : Real} : (x : K) != 0 ↔ x != 0 :=
  ofReal_eq_zero.not

@[rclike_simps, norm_cast]
/--
theorem `ofReal_add` / 定理 `ofReal_add`

English:
theorem ofReal_add
  given: (r s : Real)
  statement: ((r + s : Real) : K) = r + s
  proof: algebraMap.coe_add _ _

@[rclike_simps, norm_cast]

中文:
定理 of实数_add
  条件: (r s : 实数)
  结论: ((r + s : 实数) : K) = r + s
  证明: algebraMap.coe_add _ _

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, algebraMap.coe_add, coe_add
-/
theorem ofReal_add (r s : Real) : ((r + s : Real) : K) = r + s :=
  algebraMap.coe_add _ _

@[rclike_simps, norm_cast]
/--
theorem `ofReal_neg` / 定理 `ofReal_neg`

English:
theorem ofReal_neg
  given: (r : Real)
  statement: ((-r : Real) : K) = -r
  proof: algebraMap.coe_neg r

@[rclike_simps, norm_cast]

中文:
定理 of实数_neg
  条件: (r : 实数)
  结论: ((-r : 实数) : K) = -r
  证明: algebraMap.coe_neg r

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, algebraMap.coe_neg, coe_neg
-/
theorem ofReal_neg (r : Real) : ((-r : Real) : K) = -r :=
  algebraMap.coe_neg r

@[rclike_simps, norm_cast]
/--
theorem `ofReal_sub` / 定理 `ofReal_sub`

English:
theorem ofReal_sub
  given: (r s : Real)
  statement: ((r - s : Real) : K) = r - s
  proof: map_sub (algebraMap Real K) r s

@[rclike_simps, norm_cast]

中文:
定理 of实数_sub
  条件: (r s : 实数)
  结论: ((r - s : 实数) : K) = r - s
  证明: map_sub (algebraMap Real K) r s

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, map_sub
-/
theorem ofReal_sub (r s : Real) : ((r - s : Real) : K) = r - s :=
  map_sub (algebraMap Real K) r s

@[rclike_simps, norm_cast]
/--
theorem `ofReal_sum` / 定理 `ofReal_sum`

English:
theorem ofReal_sum
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  proof: map_sum (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]

中文:
定理 of实数_sum
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  证明: map_sum (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, map_sum
-/
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α -> Real) :
    ((∑ i in s, f i : Real) : K) = ∑ i in s, (f i : K) :=
  map_sum (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]
/--
theorem `ofReal_finsupp_sum` / 定理 `ofReal_finsupp_sum`

English:
theorem ofReal_finsupp_sum
  given: {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Real)
  proof: map_finsuppSum (algebraMap Real K) f g

@[rclike_simps, norm_cast]

中文:
定理 of实数_finsupp_sum
  条件: {α M : 类型} [零 M] (f : α ->₀ M) (g : α -> M -> 实数)
  证明: map_finsuppSum (algebraMap Real K) f g

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, map_finsuppSum
-/
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Real) :
    ((f.sum fun a b => g a b : Real) : K) = f.sum fun a b => (g a b : K) :=
  map_finsuppSum (algebraMap Real K) f g

@[rclike_simps, norm_cast]
/--
theorem `ofReal_mul` / 定理 `ofReal_mul`

English:
theorem ofReal_mul
  given: (r s : Real)
  statement: ((r * s : Real) : K) = r * s
  proof: algebraMap.coe_mul _ _

@[rclike_simps, norm_cast]

中文:
定理 of实数_mul
  条件: (r s : 实数)
  结论: ((r * s : 实数) : K) = r * s
  证明: algebraMap.coe_mul _ _

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, algebraMap.coe_mul, coe_mul
-/
theorem ofReal_mul (r s : Real) : ((r * s : Real) : K) = r * s :=
  algebraMap.coe_mul _ _

@[rclike_simps, norm_cast]
/--
theorem `ofReal_pow` / 定理 `ofReal_pow`

English:
theorem ofReal_pow
  given: (r : Real) (n : Nat)
  statement: ((r ^ n : Real) : K) = (r : K) ^ n
  proof: map_pow (algebraMap Real K) r n

@[rclike_simps, norm_cast]

中文:
定理 of实数_pow
  条件: (r : 实数) (n : 自然数)
  结论: ((r ^ n : 实数) : K) = (r : K) ^ n
  证明: map_pow (algebraMap Real K) r n

@[rclike_simps, norm_cast]

Depends on / 依赖: algebraMap, map_pow
-/
theorem ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K) = (r : K) ^ n :=
  map_pow (algebraMap Real K) r n

@[rclike_simps, norm_cast]
/--
theorem `ofReal_prod` / 定理 `ofReal_prod`

English:
theorem ofReal_prod
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  proof: map_prod (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]

中文:
定理 of实数_prod
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  证明: map_prod (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: Finite, Finite.of_equiv, InducedCategory, InducedCategory.homEquiv.trans, TypeCat, TypeCat.homEquiv, algebraMap, homEquiv, map_prod, of_equiv
-/
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α -> Real) :
    ((∏ i in s, f i : Real) : K) = ∏ i in s, (f i : K) :=
  map_prod (algebraMap Real K) _ _

@[simp, rclike_simps, norm_cast]
/--
theorem `ofReal_finsuppProd` / 定理 `ofReal_finsuppProd`

English:
theorem ofReal_finsuppProd
  given: {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Real)
  proof: map_finsuppProd _ f g

@[simp, norm_cast, rclike_simps]

中文:
定理 of实数_finsuppProd
  条件: {α M : 类型} [零 M] (f : α ->₀ M) (g : α -> M -> 实数)
  证明: map_finsuppProd _ f g

@[simp, norm_cast, rclike_simps]

Depends on / 依赖: Finite, Finite.of_injective, Iso.ext, map_finsuppProd, of_injective
-/
theorem ofReal_finsuppProd {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Real) :
    ((f.prod fun a b => g a b : Real) : K) = f.prod fun a b => (g a b : K) :=
  map_finsuppProd _ f g

@[simp, norm_cast, rclike_simps]
/--
theorem `real_smul_ofReal` / 定理 `real_smul_ofReal`

English:
theorem real_smul_ofReal
  given: (r x : Real)
  statement: r • (x : K) = (r : K) * (x : K)
  proof: real_smul_eq_coe_mul _ _

@[rclike_simps]

中文:
定理 real_smul_of实数
  条件: (r x : 实数)
  结论: r • (x : K) = (r : K) * (x : K)
  证明: real_smul_eq_coe_mul _ _

@[rclike_simps]

Depends on / 依赖: Finite, real_smul_eq_coe_mul
-/
theorem real_smul_ofReal (r x : Real) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _

@[rclike_simps]
/--
theorem `re_ofReal_mul` / 定理 `re_ofReal_mul`

English:
theorem re_ofReal_mul
  given: (r : Real) (z : K)
  statement: re (↑r * z) = r * re z
  proof: by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[rclike_simps]

中文:
定理 re_of实数_mul
  条件: (r : 实数) (z : K)
  结论: re (↑r * z) = r * re z
  证明: by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[rclike_simps]

Depends on / 依赖: mul_re, ofReal_im, ofReal_re, sub_zero, zero_mul
-/
theorem re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[rclike_simps]
/--
theorem `re_mul_ofReal` / 定理 `re_mul_ofReal`

English:
theorem re_mul_ofReal
  given: (z : K) (r : Real)
  statement: re (z * ↑r) = re z * r
  proof: by
  rw [mul_comm]; rw [re_ofReal_mul]; rw [mul_comm]

@[rclike_simps]

中文:
定理 re_mul_of实数
  条件: (z : K) (r : 实数)
  结论: re (z * ↑r) = re z * r
  证明: by
  rw [mul_comm]; rw [re_ofReal_mul]; rw [mul_comm]

@[rclike_simps]

Depends on / 依赖: mul_comm, re_ofReal_mul
-/
theorem re_mul_ofReal (z : K) (r : Real) : re (z * ↑r) = re z * r := by
  rw [mul_comm]; rw [re_ofReal_mul]; rw [mul_comm]

@[rclike_simps]
/--
theorem `im_ofReal_mul` / 定理 `im_ofReal_mul`

English:
theorem im_ofReal_mul
  given: (r : Real) (z : K)
  statement: im (↑r * z) = r * im z
  proof: by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[rclike_simps]

中文:
定理 im_of实数_mul
  条件: (r : 实数) (z : K)
  结论: im (↑r * z) = r * im z
  证明: by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[rclike_simps]

Depends on / 依赖: add_zero, mul_im, ofReal_im, ofReal_re, zero_mul
-/
theorem im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[rclike_simps]
/--
theorem `im_mul_ofReal` / 定理 `im_mul_ofReal`

English:
theorem im_mul_ofReal
  given: (z : K) (r : Real)
  statement: im (z * ↑r) = im z * r
  proof: by
  rw [mul_comm]; rw [im_ofReal_mul]; rw [mul_comm]

@[rclike_simps]

中文:
定理 im_mul_of实数
  条件: (z : K) (r : 实数)
  结论: im (z * ↑r) = im z * r
  证明: by
  rw [mul_comm]; rw [im_ofReal_mul]; rw [mul_comm]

@[rclike_simps]

Depends on / 依赖: im_ofReal_mul, mul_comm
-/
theorem im_mul_ofReal (z : K) (r : Real) : im (z * ↑r) = im z * r := by
  rw [mul_comm]; rw [im_ofReal_mul]; rw [mul_comm]

@[rclike_simps]
/--
theorem `smul_re` / 定理 `smul_re`

English:
theorem smul_re
  given: (r : Real) (z : K)
  statement: re (r • z) = r * re z
  proof: by
  rw [real_smul_eq_coe_mul]; rw [re_ofReal_mul]

@[rclike_simps]

中文:
定理 smul_re
  条件: (r : 实数) (z : K)
  结论: re (r • z) = r * re z
  证明: by
  rw [real_smul_eq_coe_mul]; rw [re_ofReal_mul]

@[rclike_simps]

Depends on / 依赖: re_ofReal_mul, real_smul_eq_coe_mul
-/
theorem smul_re (r : Real) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul]; rw [re_ofReal_mul]

@[rclike_simps]
/--
theorem `smul_im` / 定理 `smul_im`

English:
theorem smul_im
  given: (r : Real) (z : K)
  statement: im (r • z) = r * im z
  proof: by
  rw [real_smul_eq_coe_mul]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]

中文:
定理 smul_im
  条件: (r : 实数) (z : K)
  结论: im (r • z) = r * im z
  证明: by
  rw [real_smul_eq_coe_mul]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]

Depends on / 依赖: im_ofReal_mul, real_smul_eq_coe_mul
-/
theorem smul_im (r : Real) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]
/--
theorem `norm_ofReal` / 定理 `norm_ofReal`

English:
theorem norm_ofReal
  given: (r : Real)
  statement: ‖(r : K)‖ = |r|
  proof: norm_algebraMap' K r

@[simp]

中文:
定理 norm_of实数
  条件: (r : 实数)
  结论: ‖(r : K)‖ = |r|
  证明: norm_algebraMap' K r

@[simp]

Depends on / 依赖: norm_algebraMap
-/
theorem norm_ofReal (r : Real) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r

@[simp]
/--
theorem `re_ofReal_pow` / 定理 `re_ofReal_pow`

English:
theorem re_ofReal_pow
  given: (a : Real) (n : Nat)
  statement: re ((a : K) ^ n) = a ^ n
  proof: by
  rw [← ofReal_pow]; rw [@ofReal_re]

@[simp]

中文:
定理 re_of实数_pow
  条件: (a : 实数) (n : 自然数)
  结论: re ((a : K) ^ n) = a ^ n
  证明: by
  rw [← ofReal_pow]; rw [@ofReal_re]

@[simp]

Depends on / 依赖: ofReal_pow, ofReal_re
-/
theorem re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^ n) = a ^ n := by
  rw [← ofReal_pow]; rw [@ofReal_re]

@[simp]
/--
theorem `im_ofReal_pow` / 定理 `im_ofReal_pow`

English:
theorem im_ofReal_pow
  given: (a : Real) (n : Nat)
  statement: im ((a : K) ^ n) = 0
  proof: by
  rw [← @ofReal_pow]; rw [@ofReal_im_ax]

中文:
定理 im_of实数_pow
  条件: (a : 实数) (n : 自然数)
  结论: im ((a : K) ^ n) = 0
  证明: by
  rw [← @ofReal_pow]; rw [@ofReal_im_ax]

Depends on / 依赖: ofReal_im_ax, ofReal_pow
-/
theorem im_ofReal_pow (a : Real) (n : Nat) : im ((a : K) ^ n) = 0 := by
  rw [← @ofReal_pow]; rw [@ofReal_im_ax]

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero. -/
instance (priority := 100) charZero_rclike : CharZero K :=
  (RingHom.charZero_iff (algebraMap Real K).injective).1 inferInstance

@[rclike_simps, norm_cast]
/--
lemma `ofReal_expect` / 引理 `ofReal_expect`

English:
lemma ofReal_expect
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  statement: 𝔼 i in s, f i = 𝔼 i in s, (f i : K)
  proof: map_expect (algebraMap ..) ..

@[norm_cast]

中文:
引理 of实数_expect
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  结论: 𝔼 i in s, f i = 𝔼 i in s, (f i : K)
  证明: map_expect (algebraMap ..) ..

@[norm_cast]

Depends on / 依赖: algebraMap, map_expect
-/
lemma ofReal_expect {α : Type*} (s : Finset α) (f : α -> Real) : 𝔼 i in s, f i = 𝔼 i in s, (f i : K) :=
  map_expect (algebraMap ..) ..

@[norm_cast]
/--
lemma `ofReal_balance` / 引理 `ofReal_balance`

English:
lemma ofReal_balance
  given: {ι : Type*} [Fintype ι] (f : ι -> Real) (i : ι)
  proof: map_balance (algebraMap ..) ..

中文:
引理 of实数_balance
  条件: {ι : 类型} [有限类型 ι] (f : ι -> 实数) (i : ι)
  证明: map_balance (algebraMap ..) ..

Depends on / 依赖: algebraMap, map_balance
-/
lemma ofReal_balance {ι : Type*} [Fintype ι] (f : ι -> Real) (i : ι) :
    ((balance f i : Real) : K) = balance ((↑) ∘ f) i := map_balance (algebraMap ..) ..

/--
lemma `ofReal_comp_balance` / 引理 `ofReal_comp_balance`

English:
lemma ofReal_comp_balance
  given: {ι : Type*} [Fintype ι] (f : ι -> Real)
  proof: funext ofReal_balance _

中文:
引理 of实数_comp_balance
  条件: {ι : 类型} [有限类型 ι] (f : ι -> 实数)
  证明: funext ofReal_balance _
-/
@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι -> Real) :
ofReal ∘ balance f = balance (ofReal ∘ f : ι -> K) := funext ofReal_balance _

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, rclike_simps]
/--
theorem `I_re` / 定理 `I_re`

English:
theorem I_re
  statement: re (I : K) = 0
  proof: I_re_ax

@[simp, rclike_simps]

中文:
定理 I_re
  结论: re (I : K) = 0
  证明: I_re_ax

@[simp, rclike_simps]

Depends on / 依赖: I_re_ax
-/
theorem I_re : re (I : K) = 0 :=
  I_re_ax

@[simp, rclike_simps]
/--
theorem `I_im` / 定理 `I_im`

English:
theorem I_im
  given: (z : K)
  statement: im z * im (I : K) = im z
  proof: mul_im_I_ax z

@[simp, rclike_simps]

中文:
定理 I_im
  条件: (z : K)
  结论: im z * im (I : K) = im z
  证明: mul_im_I_ax z

@[simp, rclike_simps]

Depends on / 依赖: mul_im_I_ax
-/
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z

@[simp, rclike_simps]
/--
theorem `I_im'` / 定理 `I_im'`

English:
theorem I_im'
  given: (z : K)
  statement: im (I : K) * im z = im z
  proof: by rw [mul_comm, I_im]

中文:
定理 I_im'
  条件: (z : K)
  结论: im (I : K) * im z = im z
  证明: by rw [mul_comm, I_im]

Depends on / 依赖: I_im, mul_comm
-/
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/--
theorem `I_mul_re` / 定理 `I_mul_re`

English:
theorem I_mul_re
  given: (z : K)
  statement: re (I * z) = -im z
  proof: by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

中文:
定理 I_mul_re
  条件: (z : K)
  结论: re (I * z) = -im z
  证明: by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

Depends on / 依赖: I_im, I_re, mul_re, zero_mul, zero_sub
-/
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

/--
theorem `I_mul_I` / 定理 `I_mul_I`

English:
theorem I_mul_I
  statement: (I : K) = 0 ∨ (I : K) * I = -1
  proof: I_mul_I_ax

中文:
定理 I_mul_I
  结论: (I : K) = 0 ∨ (I : K) * I = -1
  证明: I_mul_I_ax

Depends on / 依赖: I_mul_I_ax
-/
theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax

variable (𝕜) in
/--
lemma `I_eq_zero_or_im_I_eq_one` / 引理 `I_eq_zero_or_im_I_eq_one`

English:
lemma I_eq_zero_or_im_I_eq_one
  statement: (I : K) = 0 ∨ im (I : K) = 1
  proof: .imp_right fun h => by simpa [h] using (I_mul_re (I : K)).symm I_mul_I (K := K)

@[simp, rclike_simps]

中文:
引理 I_eq_zero_or_im_I_eq_one
  结论: (I : K) = 0 ∨ im (I : K) = 1
  证明: .imp_right fun h => by simpa [h] using (I_mul_re (I : K)).symm I_mul_I (K := K)

@[simp, rclike_simps]

Depends on / 依赖: I_mul_I, I_mul_re, imp_right
-/
lemma I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1 :=
.imp_right fun h => by simpa [h] using (I_mul_re (I : K)).symm I_mul_I (K := K)

@[simp, rclike_simps]
/--
theorem `conj_re` / 定理 `conj_re`

English:
theorem conj_re
  given: (z : K)
  statement: re (conj z) = re z
  proof: RCLike.conj_re_ax z

@[simp, rclike_simps]

中文:
定理 conj_re
  条件: (z : K)
  结论: re (conj z) = re z
  证明: RCLike.conj_re_ax z

@[simp, rclike_simps]

Depends on / 依赖: RCLike, RCLike.conj_re_ax, conj_re_ax
-/
theorem conj_re (z : K) : re (conj z) = re z :=
  RCLike.conj_re_ax z

@[simp, rclike_simps]
/--
theorem `conj_im` / 定理 `conj_im`

English:
theorem conj_im
  given: (z : K)
  statement: im (conj z) = -im z
  proof: RCLike.conj_im_ax z

@[simp, rclike_simps]

中文:
定理 conj_im
  条件: (z : K)
  结论: im (conj z) = -im z
  证明: RCLike.conj_im_ax z

@[simp, rclike_simps]

Depends on / 依赖: RCLike, RCLike.conj_im_ax, conj_im_ax
-/
theorem conj_im (z : K) : im (conj z) = -im z :=
  RCLike.conj_im_ax z

@[simp, rclike_simps]
/--
theorem `conj_I` / 定理 `conj_I`

English:
theorem conj_I
  statement: conj (I : K) = -I
  proof: RCLike.conj_I_ax

@[simp, rclike_simps]

中文:
定理 conj_I
  结论: conj (I : K) = -I
  证明: RCLike.conj_I_ax

@[simp, rclike_simps]

Depends on / 依赖: RCLike, RCLike.conj_I_ax, conj_I_ax
-/
theorem conj_I : conj (I : K) = -I :=
  RCLike.conj_I_ax

@[simp, rclike_simps]
/--
theorem `conj_ofReal` / 定理 `conj_ofReal`

English:
theorem conj_ofReal
  given: (r : Real)
  statement: conj (r : K) = (r : K)
  proof: by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, conj_re, and_self_iff, neg_zero]

中文:
定理 conj_of实数
  条件: (r : 实数)
  结论: conj (r : K) = (r : K)
  证明: by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, conj_re, and_self_iff, neg_zero]

Depends on / 依赖: and_self_iff, conj_im, conj_re, ext_iff, neg_zero, ofReal_im
-/
theorem conj_ofReal (r : Real) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, conj_re, and_self_iff, neg_zero]

/--
theorem `conj_nat_cast` / 定理 `conj_nat_cast`

English:
theorem conj_nat_cast
  given: (n : Nat)
  statement: conj (n : K) = n
  proof: map_natCast _ _

中文:
定理 conj_nat_cast
  条件: (n : 自然数)
  结论: conj (n : K) = n
  证明: map_natCast _ _

Depends on / 依赖: map_natCast
-/
theorem conj_nat_cast (n : Nat) : conj (n : K) = n := map_natCast _ _

/--
theorem `conj_ofNat` / 定理 `conj_ofNat`

English:
theorem conj_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: conj (ofNat(n) : K) = ofNat(n)
  proof: map_ofNat _ _

@[rclike_simps, simp]

中文:
定理 conj_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: conj (of自然数(n) : K) = of自然数(n)
  证明: map_ofNat _ _

@[rclike_simps, simp]

Depends on / 依赖: map_ofNat
-/
theorem conj_ofNat (n : Nat) [n.AtLeastTwo] : conj (ofNat(n) : K) = ofNat(n) :=
  map_ofNat _ _

@[rclike_simps, simp]
/--
theorem `conj_neg_I` / 定理 `conj_neg_I`

English:
theorem conj_neg_I
  statement: conj (-I) = (I : K)
  proof: by rw [map_neg, conj_I, neg_neg]

中文:
定理 conj_neg_I
  结论: conj (-I) = (I : K)
  证明: by rw [map_neg, conj_I, neg_neg]

Depends on / 依赖: Category, Category.assoc, D.t_fac, conj_I, map_neg, neg_neg, t_fac
-/
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]

/--
theorem `conj_eq_re_sub_im` / 定理 `conj_eq_re_sub_im`

English:
theorem conj_eq_re_sub_im
  given: (z : K)
  statement: conj z = re z - im z * I
  proof: (congr_arg conj (re_add_im z).symm).trans by
    rw [map_add]; rw [map_mul]; rw [conj_I]; rw [conj_ofReal]; rw [conj_ofReal]; rw [mul_neg]; rw [sub_eq_add_neg]

中文:
定理 conj_eq_re_sub_im
  条件: (z : K)
  结论: conj z = re z - im z * I
  证明: (congr_arg conj (re_add_im z).symm).trans by
    rw [map_add]; rw [map_mul]; rw [conj_I]; rw [conj_ofReal]; rw [conj_ofReal]; rw [mul_neg]; rw [sub_eq_add_neg]

Depends on / 依赖: Category, Category.assoc, D.t_fac, congr_arg, conj_I, conj_ofReal, map_add, map_mul, mul_neg, re_add_im, sub_eq_add_neg, t_fac
-/
theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
(congr_arg conj (re_add_im z).symm).trans by
    rw [map_add]; rw [map_mul]; rw [conj_I]; rw [conj_ofReal]; rw [conj_ofReal]; rw [mul_neg]; rw [sub_eq_add_neg]

/--
theorem `sub_conj` / 定理 `sub_conj`

English:
theorem sub_conj
  given: (z : K)
  statement: z - conj z = 2 * im z * I
  proof: calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[rclike_simps]

中文:
定理 sub_conj
  条件: (z : K)
  结论: z - conj z = 2 * im z * I
  证明: calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[rclike_simps]

Depends on / 依赖: add_sub_sub_cancel, conj_eq_re_sub_im, mul_assoc, re_add_im, two_mul
-/
theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[rclike_simps]
/--
theorem `conj_smul` / 定理 `conj_smul`

English:
theorem conj_smul
  given: (r : Real) (z : K)
  statement: conj (r • z) = r • conj z
  proof: by
  rw [conj_eq_re_sub_im]; rw [conj_eq_re_sub_im]; rw [smul_re]; rw [smul_im]; rw [ofReal_mul]; rw [ofReal_mul]; rw [real_smul_eq_coe_mul r (_ - _)]; rw [mul_sub]; rw [mul_assoc]

中文:
定理 conj_smul
  条件: (r : 实数) (z : K)
  结论: conj (r • z) = r • conj z
  证明: by
  rw [conj_eq_re_sub_im]; rw [conj_eq_re_sub_im]; rw [smul_re]; rw [smul_im]; rw [ofReal_mul]; rw [ofReal_mul]; rw [real_smul_eq_coe_mul r (_ - _)]; rw [mul_sub]; rw [mul_assoc]

Depends on / 依赖: cancel_mono, conj_eq_re_sub_im, mul_assoc, mul_sub, ofReal_mul, pullback, pullback.fst, real_smul_eq_coe_mul, smul_im, smul_re, t_fac, t_fac_assoc
-/
theorem conj_smul (r : Real) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im]; rw [conj_eq_re_sub_im]; rw [smul_re]; rw [smul_im]; rw [ofReal_mul]; rw [ofReal_mul]; rw [real_smul_eq_coe_mul r (_ - _)]; rw [mul_sub]; rw [mul_assoc]

/--
theorem `add_conj` / 定理 `add_conj`

English:
theorem add_conj
  given: (z : K)
  statement: z + conj z = 2 * re z
  proof: calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]

中文:
定理 add_conj
  条件: (z : K)
  结论: z + conj z = 2 * re z
  证明: calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]

Depends on / 依赖: add_add_sub_cancel, conj_eq_re_sub_im, re_add_im, two_mul
-/
theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]

/--
theorem `re_eq_add_conj` / 定理 `re_eq_add_conj`

English:
theorem re_eq_add_conj
  given: (z : K)
  statement: ↑(re z) = (z + conj z) / 2
  proof: by
  rw [add_conj]; rw [mul_div_cancel_left₀ (re z : K) two_ne_zero]

中文:
定理 re_eq_add_conj
  条件: (z : K)
  结论: ↑(re z) = (z + conj z) / 2
  证明: by
  rw [add_conj]; rw [mul_div_cancel_left₀ (re z : K) two_ne_zero]

Depends on / 依赖: D.cocycle, add_conj, cocycle, two_ne_zero
-/
theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj]; rw [mul_div_cancel_left₀ (re z : K) two_ne_zero]

/--
theorem `im_eq_conj_sub` / 定理 `im_eq_conj_sub`

English:
theorem im_eq_conj_sub
  given: (z : K)
  statement: ↑(im z) = I * (conj z - z) / 2
  proof: by
  rw [← neg_inj]; rw [← ofReal_neg]; rw [← I_mul_re]; rw [re_eq_add_conj]; rw [map_mul]; rw [conj_I]; rw [← neg_div]; rw [← mul_neg]; rw [neg_sub]; rw [mul_sub]; rw [neg_mul]; rw [sub_eq_add_neg]

中文:
定理 im_eq_conj_sub
  条件: (z : K)
  结论: ↑(im z) = I * (conj z - z) / 2
  证明: by
  rw [← neg_inj]; rw [← ofReal_neg]; rw [← I_mul_re]; rw [re_eq_add_conj]; rw [map_mul]; rw [conj_I]; rw [← neg_div]; rw [← mul_neg]; rw [neg_sub]; rw [mul_sub]; rw [neg_mul]; rw [sub_eq_add_neg]

Depends on / 依赖: D.cocycle, I_mul_re, IsIso.eq_inv_of_hom_inv_id, cancel_mono, cocycle, conj_I, eq_inv_of_hom_inv_id, map_mul, mul_neg, mul_sub, neg_div, neg_inj, neg_mul, neg_sub, ofReal_neg, pullback, pullback.fst, re_eq_add_conj, sub_eq_add_neg, t_fac
-/
theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj]; rw [← ofReal_neg]; rw [← I_mul_re]; rw [re_eq_add_conj]; rw [map_mul]; rw [conj_I]; rw [← neg_div]; rw [← mul_neg]; rw [neg_sub]; rw [mul_sub]; rw [neg_mul]; rw [sub_eq_add_neg]

open List in
/--
theorem `is_real_TFAE` / 定理 `is_real_TFAE`

English:
theorem is_real_TFAE
  given: (z : K)
  proof: by
  tfae_have 1 -> 4
  | h => by
    rw [← @ofReal_inj K]; rw [im_eq_conj_sub]; rw [h]; rw [sub_self]; rw [mul_zero]; rw [zero_div]; rw [ofReal_zero]
  tfae_have 4 -> 3
  | h => by
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 -> 2 := fun h => ⟨_, h⟩
  tfae_ha

中文:
定理 is_real_TFAE
  条件: (z : K)
  证明: by
  tfae_have 1 -> 4
  | h => by
    rw [← @ofReal_inj K]; rw [im_eq_conj_sub]; rw [h]; rw [sub_self]; rw [mul_zero]; rw [zero_div]; rw [ofReal_zero]
  tfae_have 4 -> 3
  | h => by
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 -> 2 := fun h => ⟨_, h⟩
  tfae_ha

Depends on / 依赖: add_zero, conj_ofReal, conv_rhs, im_eq_conj_sub, isSelfAdjoint_iff, mul_zero, ofReal_inj, ofReal_zero, re_add_im, sub_self, tfae_finish, tfae_have, zero_div, zero_mul
-/
theorem is_real_TFAE (z : K) :
    TFAE [conj z = z, exists r : Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z] := by
  tfae_have 1 -> 4
  | h => by
    rw [← @ofReal_inj K]; rw [im_eq_conj_sub]; rw [h]; rw [sub_self]; rw [mul_zero]; rw [zero_div]; rw [ofReal_zero]
  tfae_have 4 -> 3
  | h => by
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 -> 2 := fun h => ⟨_, h⟩
  tfae_have 2 -> 1 := fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  tfae_have 1 -> 5 := fun _ => by rwa [isSelfAdjoint_iff]
  tfae_have 5 -> 1 := fun hz => by rwa [isSelfAdjoint_iff] at hz
  tfae_finish

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `conj_eq_iff_real` / 定理 `conj_eq_iff_real`

English:
theorem conj_eq_iff_real
  given: {z : K}
  statement: conj z = z ↔ exists r : Real, z = (r : K)
  proof: calc
    _ ↔ exists r : Real, (r : K) = z := (is_real_TFAE z).out 0 1
    _ ↔ _ := by simp only [eq_comm]

中文:
定理 conj_eq_iff_real
  条件: {z : K}
  结论: conj z = z ↔ 存在 r : 实数, z = (r : K)
  证明: calc
    _ ↔ exists r : Real, (r : K) = z := (is_real_TFAE z).out 0 1
    _ ↔ _ := by simp only [eq_comm]

Depends on / 依赖: eq_comm, is_real_TFAE
-/
theorem conj_eq_iff_real {z : K} : conj z = z ↔ exists r : Real, z = (r : K) :=
  calc
    _ ↔ exists r : Real, (r : K) = z := (is_real_TFAE z).out 0 1
    _ ↔ _ := by simp only [eq_comm]

/--
theorem `conj_eq_iff_re` / 定理 `conj_eq_iff_re`

English:
theorem conj_eq_iff_re
  given: {z : K}
  statement: conj z = z ↔ (re z : K) = z
  proof: (is_real_TFAE z).out 0 2

中文:
定理 conj_eq_iff_re
  条件: {z : K}
  结论: conj z = z ↔ (re z : K) = z
  证明: (is_real_TFAE z).out 0 2

Depends on / 依赖: is_real_TFAE
-/
theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2

/--
theorem `conj_eq_iff_im` / 定理 `conj_eq_iff_im`

English:
theorem conj_eq_iff_im
  given: {z : K}
  statement: conj z = z ↔ im z = 0
  proof: (is_real_TFAE z).out 0 3

@[simp]

中文:
定理 conj_eq_iff_im
  条件: {z : K}
  结论: conj z = z ↔ im z = 0
  证明: (is_real_TFAE z).out 0 3

@[simp]

Depends on / 依赖: is_real_TFAE
-/
theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3

@[simp]
/--
theorem `star_def` / 定理 `star_def`

English:
theorem star_def
  statement: (Star.star : K -> K) = conj
  proof: rfl

中文:
定理 star_def
  结论: (对合.star : K -> K) = conj
  证明: rfl
-/
theorem star_def : (Star.star : K -> K) = conj :=
  rfl

/--
lemma `im_eq_zero_iff_isSelfAdjoint` / 引理 `im_eq_zero_iff_isSelfAdjoint`

English:
lemma im_eq_zero_iff_isSelfAdjoint
  given: {x : K}
  statement: im x = 0 ↔ IsSelfAdjoint x
  proof: .out 3 4 is_real_TFAE x

中文:
引理 im_eq_zero_iff_isSelfAdjoint
  条件: {x : K}
  结论: im x = 0 ↔ IsSelfAdjoint x
  证明: .out 3 4 is_real_TFAE x

Depends on / 依赖: is_real_TFAE
-/
lemma im_eq_zero_iff_isSelfAdjoint {x : K} : im x = 0 ↔ IsSelfAdjoint x :=
.out 3 4 is_real_TFAE x

/--
lemma `re_eq_ofReal_of_isSelfAdjoint` / 引理 `re_eq_ofReal_of_isSelfAdjoint`

English:
lemma re_eq_ofReal_of_isSelfAdjoint
  given: {x : K} {y : Real} (hx : IsSelfAdjoint x)
  proof: by
  simp [RCLike.ext_iff (K := K), hx, im_eq_zero_iff_isSelfAdjoint]

中文:
引理 re_eq_of实数_of_isSelfAdjoint
  条件: {x : K} {y : 实数} (hx : IsSelfAdjoint x)
  证明: by
  simp [RCLike.ext_iff (K := K), hx, im_eq_zero_iff_isSelfAdjoint]

Depends on / 依赖: RCLike, RCLike.ext_iff, ext_iff, im_eq_zero_iff_isSelfAdjoint
-/
lemma re_eq_ofReal_of_isSelfAdjoint {x : K} {y : Real} (hx : IsSelfAdjoint x) :
    re x = y ↔ x = y := by
  simp [RCLike.ext_iff (K := K), hx, im_eq_zero_iff_isSelfAdjoint]

/--
lemma `ofReal_eq_re_of_isSelfAdjoint` / 引理 `ofReal_eq_re_of_isSelfAdjoint`

English:
lemma ofReal_eq_re_of_isSelfAdjoint
  given: {x : K} {y : Real} (hx : IsSelfAdjoint x)
  proof: by
  simpa [eq_comm] using re_eq_ofReal_of_isSelfAdjoint hx

中文:
引理 of实数_eq_re_of_isSelfAdjoint
  条件: {x : K} {y : 实数} (hx : IsSelfAdjoint x)
  证明: by
  simpa [eq_comm] using re_eq_ofReal_of_isSelfAdjoint hx

Depends on / 依赖: eq_comm, re_eq_ofReal_of_isSelfAdjoint
-/
lemma ofReal_eq_re_of_isSelfAdjoint {x : K} {y : Real} (hx : IsSelfAdjoint x) :
    y = re x ↔ y = x := by
  simpa [eq_comm] using re_eq_ofReal_of_isSelfAdjoint hx

variable (K)

/--
Definition of `conjToRingEquiv` / `conjToRingEquiv` 的定义

English:
abbreviation conjToRingEquiv
  signature: : K ≃+* Kᵐᵒᵖ
  body: starRingEquiv

中文:
缩写 conjToRingEquiv
  签名: : K ≃+* Kᵐᵒᵖ
  定义体: starRingEquiv

Depends on / 依赖: starRingEquiv
-/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv

variable {K} {z : K}

/--
Definition of `normSq` / `normSq` 的定义

English:
definition normSq
  signature: : K ->*₀ Real where
  body: re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring

中文:
定义 normSq
  签名: : K ->*₀ 实数 where
  定义体: re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring
-/
def normSq : K ->*₀ Real where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring

/--
theorem `normSq_apply` / 定理 `normSq_apply`

English:
theorem normSq_apply
  given: (z : K)
  statement: normSq z = re z * re z + im z * im z
  proof: rfl

中文:
定理 normSq_apply
  条件: (z : K)
  结论: normSq z = re z * re z + im z * im z
  证明: rfl
-/
theorem normSq_apply (z : K) : normSq z = re z * re z + im z * im z :=
  rfl

/--
theorem `norm_sq_eq_def` / 定理 `norm_sq_eq_def`

English:
theorem norm_sq_eq_def
  given: {z : K}
  statement: ‖z‖ ^ 2 = re z * re z + im z * im z
  proof: norm_sq_eq_def_ax z

中文:
定理 norm_sq_eq_def
  条件: {z : K}
  结论: ‖z‖ ^ 2 = re z * re z + im z * im z
  证明: norm_sq_eq_def_ax z

Depends on / 依赖: norm_sq_eq_def_ax
-/
theorem norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z

/--
theorem `normSq_eq_def'` / 定理 `normSq_eq_def'`

English:
theorem normSq_eq_def'
  given: (z : K)
  statement: normSq z = ‖z‖ ^ 2
  proof: norm_sq_eq_def.symm

@[rclike_simps]

中文:
定理 normSq_eq_def'
  条件: (z : K)
  结论: normSq z = ‖z‖ ^ 2
  证明: norm_sq_eq_def.symm

@[rclike_simps]

Depends on / 依赖: norm_sq_eq_def, norm_sq_eq_def.symm
-/
theorem normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2 :=
  norm_sq_eq_def.symm

@[rclike_simps]
/--
theorem `normSq_zero` / 定理 `normSq_zero`

English:
theorem normSq_zero
  statement: normSq (0 : K) = 0
  proof: normSq.map_zero

@[rclike_simps]

中文:
定理 normSq_zero
  结论: normSq (0 : K) = 0
  证明: normSq.map_zero

@[rclike_simps]

Depends on / 依赖: map_zero, normSq, normSq.map_zero
-/
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero

@[rclike_simps]
/--
theorem `normSq_one` / 定理 `normSq_one`

English:
theorem normSq_one
  statement: normSq (1 : K) = 1
  proof: normSq.map_one

中文:
定理 normSq_one
  结论: normSq (1 : K) = 1
  证明: normSq.map_one

Depends on / 依赖: isLimitOfHasPullbackOfPreservesLimit, map_one, normSq, normSq.map_one
-/
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one

/--
theorem `normSq_nonneg` / 定理 `normSq_nonneg`

English:
theorem normSq_nonneg
  given: (z : K)
  statement: 0 <= normSq z
  proof: add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

中文:
定理 normSq_nonneg
  条件: (z : K)
  结论: 0 <= normSq z
  证明: add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

Depends on / 依赖: add_nonneg, mul_self_nonneg
-/
theorem normSq_nonneg (z : K) : 0 <= normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/--
theorem `normSq_eq_zero` / 定理 `normSq_eq_zero`

English:
theorem normSq_eq_zero
  given: {z : K}
  statement: normSq z = 0 ↔ z = 0
  proof: map_eq_zero _

@[simp, rclike_simps]

中文:
定理 normSq_eq_zero
  条件: {z : K}
  结论: normSq z = 0 ↔ z = 0
  证明: map_eq_zero _

@[simp, rclike_simps]

Depends on / 依赖: map_eq_zero
-/
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _

@[simp, rclike_simps]
/--
theorem `normSq_pos` / 定理 `normSq_pos`

English:
theorem normSq_pos
  given: {z : K}
  statement: 0 < normSq z ↔ z != 0
  proof: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; simp [normSq_nonneg]

@[simp, rclike_simps]

中文:
定理 normSq_pos
  条件: {z : K}
  结论: 0 < normSq z ↔ z != 0
  证明: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; simp [normSq_nonneg]

@[simp, rclike_simps]

Depends on / 依赖: eq_comm, lt_iff_le_and_ne, normSq_nonneg
-/
theorem normSq_pos {z : K} : 0 < normSq z ↔ z != 0 := by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [eq_comm]; simp [normSq_nonneg]

@[simp, rclike_simps]
/--
theorem `normSq_neg` / 定理 `normSq_neg`

English:
theorem normSq_neg
  given: (z : K)
  statement: normSq (-z) = normSq z
  proof: by simp only [normSq_eq_def', norm_neg]

@[simp, rclike_simps]

中文:
定理 normSq_neg
  条件: (z : K)
  结论: normSq (-z) = normSq z
  证明: by simp only [normSq_eq_def', norm_neg]

@[simp, rclike_simps]

Depends on / 依赖: normSq_eq_def, norm_neg
-/
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]

@[simp, rclike_simps]
/--
theorem `normSq_conj` / 定理 `normSq_conj`

English:
theorem normSq_conj
  given: (z : K)
  statement: normSq (conj z) = normSq z
  proof: by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]

中文:
定理 normSq_conj
  条件: (z : K)
  结论: normSq (conj z) = normSq z
  证明: by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]

Depends on / 依赖: mul_neg, neg_mul, neg_neg, normSq_apply, rclike_simps
-/
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/--
theorem `normSq_mul` / 定理 `normSq_mul`

English:
theorem normSq_mul
  given: (z w : K)
  statement: normSq (z * w) = normSq z * normSq w
  proof: map_mul _ z w

中文:
定理 normSq_mul
  条件: (z w : K)
  结论: normSq (z * w) = normSq z * normSq w
  证明: map_mul _ z w

Depends on / 依赖: map_mul
-/
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w

/--
theorem `normSq_add` / 定理 `normSq_add`

English:
theorem normSq_add
  given: (z w : K)
  statement: normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w)
  proof: by
  simp only [normSq_apply, map_add, rclike_simps]
  ring

中文:
定理 normSq_add
  条件: (z w : K)
  结论: normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w)
  证明: by
  simp only [normSq_apply, map_add, rclike_simps]
  ring

Depends on / 依赖: map_add, normSq_apply, rclike_simps
-/
theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, rclike_simps]
  ring

/--
theorem `re_sq_le_normSq` / 定理 `re_sq_le_normSq`

English:
theorem re_sq_le_normSq
  given: (z : K)
  statement: re z * re z <= normSq z
  proof: le_add_of_nonneg_right (mul_self_nonneg _)

中文:
定理 re_sq_le_normSq
  条件: (z : K)
  结论: re z * re z <= normSq z
  证明: le_add_of_nonneg_right (mul_self_nonneg _)

Depends on / 依赖: le_add_of_nonneg_right, mul_self_nonneg
-/
theorem re_sq_le_normSq (z : K) : re z * re z <= normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

/--
theorem `im_sq_le_normSq` / 定理 `im_sq_le_normSq`

English:
theorem im_sq_le_normSq
  given: (z : K)
  statement: im z * im z <= normSq z
  proof: le_add_of_nonneg_left (mul_self_nonneg _)

中文:
定理 im_sq_le_normSq
  条件: (z : K)
  结论: im z * im z <= normSq z
  证明: le_add_of_nonneg_left (mul_self_nonneg _)

Depends on / 依赖: le_add_of_nonneg_left, mul_self_nonneg
-/
theorem im_sq_le_normSq (z : K) : im z * im z <= normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

/--
theorem `mul_conj` / 定理 `mul_conj`

English:
theorem mul_conj
  given: (z : K)
  statement: z * conj z = ‖z‖ ^ 2
  proof: by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]

中文:
定理 mul_conj
  条件: (z : K)
  结论: z * conj z = ‖z‖ ^ 2
  证明: by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]

Depends on / 依赖: mul_comm, norm_sq_eq_def, ofReal_pow
-/
theorem mul_conj (z : K) : z * conj z = ‖z‖ ^ 2 := by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]

/--
theorem `conj_mul` / 定理 `conj_mul`

English:
theorem conj_mul
  given: (z : K)
  statement: conj z * z = ‖z‖ ^ 2
  proof: by rw [mul_comm, mul_conj]

中文:
定理 conj_mul
  条件: (z : K)
  结论: conj z * z = ‖z‖ ^ 2
  证明: by rw [mul_comm, mul_conj]

Depends on / 依赖: mul_comm, mul_conj
-/
theorem conj_mul (z : K) : conj z * z = ‖z‖ ^ 2 := by rw [mul_comm, mul_conj]

/--
lemma `inv_eq_conj` / 引理 `inv_eq_conj`

English:
lemma inv_eq_conj
  given: (hz : ‖z‖ = 1)
  statement: z⁻¹ = conj z
  proof: inv_eq_of_mul_eq_one_left by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]

中文:
引理 inv_eq_conj
  条件: (hz : ‖z‖ = 1)
  结论: z⁻¹ = conj z
  证明: inv_eq_of_mul_eq_one_left by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]

Depends on / 依赖: algebraMap, algebraMap.coe_one, coe_one, conj_mul, inv_eq_of_mul_eq_one_left, one_pow, simp_rw
-/
lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z :=
inv_eq_of_mul_eq_one_left by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]

/--
theorem `normSq_sub` / 定理 `normSq_sub`

English:
theorem normSq_sub
  given: (z w : K)
  statement: normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w)
  proof: by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]

中文:
定理 normSq_sub
  条件: (z w : K)
  结论: normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w)
  证明: by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]

Depends on / 依赖: map_neg, mul_neg, normSq_add, normSq_neg, sub_eq_add_neg
-/
theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]

/--
theorem `sqrt_normSq_eq_norm` / 定理 `sqrt_normSq_eq_norm`

English:
theorem sqrt_normSq_eq_norm
  given: {z : K}
  statement: √(normSq z) = ‖z‖
  proof: by
  rw [normSq_eq_def']; rw [Real.sqrt_sq (norm_nonneg _)]

中文:
定理 sqrt_normSq_eq_norm
  条件: {z : K}
  结论: √(normSq z) = ‖z‖
  证明: by
  rw [normSq_eq_def']; rw [Real.sqrt_sq (norm_nonneg _)]

Depends on / 依赖: Real.sqrt_sq, normSq_eq_def, norm_nonneg, sqrt_sq
-/
theorem sqrt_normSq_eq_norm {z : K} : √(normSq z) = ‖z‖ := by
  rw [normSq_eq_def']; rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### Inversion -/

@[rclike_simps, norm_cast]
/--
theorem `ofReal_inv` / 定理 `ofReal_inv`

English:
theorem ofReal_inv
  given: (r : Real)
  statement: ((r⁻¹ : Real) : K) = (r : K)⁻¹
  proof: map_inv₀ _ r

中文:
定理 of实数_inv
  条件: (r : 实数)
  结论: ((r⁻¹ : 实数) : K) = (r : K)⁻¹
  证明: map_inv₀ _ r
-/
theorem ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (z : K)
  statement: z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : Real)
  proof: by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc]; rw [mul_conj]; rw [ofReal_inv]; rw [ofReal_pow]; rw [mul_inv_cancel₀]
    simpa

@[simp, rclike_simps]

中文:
定理 inv_def
  条件: (z : K)
  结论: z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : 实数)
  证明: by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc]; rw [mul_conj]; rw [ofReal_inv]; rw [ofReal_pow]; rw [mul_inv_cancel₀]
    simpa

@[simp, rclike_simps]

Depends on / 依赖: eq_or_ne, inv_eq_of_mul_eq_one_right, mul_assoc, mul_conj, ofReal_inv, ofReal_pow
-/
theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : Real) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc]; rw [mul_conj]; rw [ofReal_inv]; rw [ofReal_pow]; rw [mul_inv_cancel₀]
    simpa

@[simp, rclike_simps]
/--
theorem `inv_re` / 定理 `inv_re`

English:
theorem inv_re
  given: (z : K)
  statement: re z⁻¹ = re z / normSq z
  proof: by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [re_ofReal_mul]; rw [conj_re]; rw [div_eq_inv_mul]

@[simp, rclike_simps]

中文:
定理 inv_re
  条件: (z : K)
  结论: re z⁻¹ = re z / normSq z
  证明: by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [re_ofReal_mul]; rw [conj_re]; rw [div_eq_inv_mul]

@[simp, rclike_simps]

Depends on / 依赖: conj_re, dif_neg, dif_pos, div_eq_inv_mul, eqToHom, inv_def, mul_comm, normSq_eq_def, re_ofReal_mul
-/
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [re_ofReal_mul]; rw [conj_re]; rw [div_eq_inv_mul]

@[simp, rclike_simps]
/--
theorem `inv_im` / 定理 `inv_im`

English:
theorem inv_im
  given: (z : K)
  statement: im z⁻¹ = -im z / normSq z
  proof: by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [im_ofReal_mul]; rw [conj_im]; rw [div_eq_inv_mul]

中文:
定理 inv_im
  条件: (z : K)
  结论: im z⁻¹ = -im z / normSq z
  证明: by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [im_ofReal_mul]; rw [conj_im]; rw [div_eq_inv_mul]

Depends on / 依赖: GlueData, conj_im, div_eq_inv_mul, im_ofReal_mul, infer_instance, inv_def, mul_comm, normSq_eq_def, split_ifs
-/
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def]; rw [normSq_eq_def']; rw [mul_comm]; rw [im_ofReal_mul]; rw [conj_im]; rw [div_eq_inv_mul]

/--
theorem `div_re` / 定理 `div_re`

English:
theorem div_re
  given: (z w : K)
  statement: re (z / w) = re z * re w / normSq w + im z * im w / normSq w
  proof: by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg,
    rclike_simps]

中文:
定理 div_re
  条件: (z w : K)
  结论: re (z / w) = re z * re w / normSq w + im z * im w / normSq w
  证明: by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg,
    rclike_simps]

Depends on / 依赖: GlueData, div_eq_mul_inv, infer_instance, mul_assoc, mul_neg, neg_mul, neg_neg, rclike_simps, reduceDIte, sub_eq_add_neg
-/
theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg,
    rclike_simps]

/--
theorem `div_im` / 定理 `div_im`

English:
theorem div_im
  given: (z w : K)
  statement: im (z / w) = im z * re w / normSq w - re z * im w / normSq w
  proof: by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg,
    rclike_simps]

中文:
定理 div_im
  条件: (z w : K)
  结论: im (z / w) = im z * re w / normSq w - re z * im w / normSq w
  证明: by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg,
    rclike_simps]

Depends on / 依赖: D.f_hasPullback, GlueData, add_comm, allowSynthFailures, convert, dif_pos, div_eq_mul_inv, eqToHom, f_hasPullback, hasPullback_of_left_iso, hasPullback_of_right_iso, infer_instance, mul_assoc, mul_neg, neg_mul, rclike_simps, sub_eq_add_neg
-/
theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg,
    rclike_simps]

-- Not `@[simp]` since `simp` can prove this
@[rclike_simps]
/--
theorem `conj_inv` / 定理 `conj_inv`

English:
theorem conj_inv
  given: (x : K)
  statement: conj x⁻¹ = (conj x)⁻¹
  proof: star_inv₀ _

中文:
定理 conj_inv
  条件: (x : K)
  结论: conj x⁻¹ = (conj x)⁻¹
  证明: star_inv₀ _

Depends on / 依赖: Ne.symm, allowSynthFailures, dif_neg, eqToHom, infer_instance, pullback, pullback.fst, pullback.map, pullback.snd, pullbackSymmetry, pullback_snd_i
-/
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

/--
lemma `conj_div` / 引理 `conj_div`

English:
lemma conj_div
  given: (x y : K)
  statement: conj (x / y) = conj x / conj y
  proof: map_div' conj conj_inv _ _

中文:
引理 conj_div
  条件: (x y : K)
  结论: conj (x / y) = conj x / conj y
  证明: map_div' conj conj_inv _ _

Depends on / 依赖: conj_inv, map_div
-/
lemma conj_div (x y : K) : conj (x / y) = conj x / conj y := map_div' conj conj_inv _ _

--TODO: Do we rather want the map as an explicit definition?
/--
lemma `exists_norm_eq_mul_self` / 引理 `exists_norm_eq_mul_self`

English:
lemma exists_norm_eq_mul_self
  given: (x : K)
  statement: exists c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

中文:
引理 存在_norm_eq_mul_self
  条件: (x : K)
  结论: 存在 c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

Depends on / 依赖: eq_or_ne, norm_ne_zero_iff
-/
lemma exists_norm_eq_mul_self (x : K) : exists c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

/--
lemma `exists_norm_mul_eq_self` / 引理 `exists_norm_mul_eq_self`

English:
lemma exists_norm_mul_eq_self
  given: (x : K)
  statement: exists c, ‖c‖ = 1 ∧ c * ‖x‖ = x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

@[rclike_simps, norm_cast]

中文:
引理 存在_norm_mul_eq_self
  条件: (x : K)
  结论: 存在 c, ‖c‖ = 1 ∧ c * ‖x‖ = x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

@[rclike_simps, norm_cast]

Depends on / 依赖: eq_or_ne, norm_ne_zero_iff
-/
lemma exists_norm_mul_eq_self (x : K) : exists c, ‖c‖ = 1 ∧ c * ‖x‖ = x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

@[rclike_simps, norm_cast]
/--
theorem `ofReal_div` / 定理 `ofReal_div`

English:
theorem ofReal_div
  given: (r s : Real)
  statement: ((r / s : Real) : K) = r / s
  proof: map_div₀ (algebraMap Real K) r s

中文:
定理 of实数_div
  条件: (r s : 实数)
  结论: ((r / s : 实数) : K) = r / s
  证明: map_div₀ (algebraMap Real K) r s

Depends on / 依赖: algebraMap
-/
theorem ofReal_div (r s : Real) : ((r / s : Real) : K) = r / s :=
  map_div₀ (algebraMap Real K) r s

/--
theorem `div_re_ofReal` / 定理 `div_re_ofReal`

English:
theorem div_re_ofReal
  given: {z : K} {r : Real}
  statement: re (z / r) = re z / r
  proof: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [← ofReal_inv]; rw [re_ofReal_mul]

@[rclike_simps, norm_cast]

中文:
定理 div_re_of实数
  条件: {z : K} {r : 实数}
  结论: re (z / r) = re z / r
  证明: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [← ofReal_inv]; rw [re_ofReal_mul]

@[rclike_simps, norm_cast]

Depends on / 依赖: div_eq_inv_mul, ofReal_inv, re_ofReal_mul
-/
theorem div_re_ofReal {z : K} {r : Real} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [← ofReal_inv]; rw [re_ofReal_mul]

@[rclike_simps, norm_cast]
/--
theorem `ofReal_zpow` / 定理 `ofReal_zpow`

English:
theorem ofReal_zpow
  given: (r : Real) (n : Int)
  statement: ((r ^ n : Real) : K) = (r : K) ^ n
  proof: map_zpow₀ (algebraMap Real K) r n

中文:
定理 of实数_zpow
  条件: (r : 实数) (n : 整数)
  结论: ((r ^ n : 实数) : K) = (r : K) ^ n
  证明: map_zpow₀ (algebraMap Real K) r n

Depends on / 依赖: algebraMap
-/
theorem ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap Real K) r n

/--
theorem `I_mul_I_of_nonzero` / 定理 `I_mul_I_of_nonzero`

English:
theorem I_mul_I_of_nonzero
  statement: (I : K) != 0 -> (I : K) * I = -1
  proof: I_mul_I_ax.resolve_left

@[simp, rclike_simps]

中文:
定理 I_mul_I_of_nonzero
  结论: (I : K) != 0 -> (I : K) * I = -1
  证明: I_mul_I_ax.resolve_left

@[simp, rclike_simps]

Depends on / 依赖: I_mul_I_ax, I_mul_I_ax.resolve_left, resolve_left
-/
theorem I_mul_I_of_nonzero : (I : K) != 0 -> (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left

@[simp, rclike_simps]
/--
theorem `inv_I` / 定理 `inv_I`

English:
theorem inv_I
  statement: (I : K)⁻¹ = -I
  proof: by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp
    linear_combination I_mul_I_of_nonzero h

@[simp, rclike_simps]

中文:
定理 inv_I
  结论: (I : K)⁻¹ = -I
  证明: by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp
    linear_combination I_mul_I_of_nonzero h

@[simp, rclike_simps]

Depends on / 依赖: I_mul_I_of_nonzero, linear_combination
-/
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp
    linear_combination I_mul_I_of_nonzero h

@[simp, rclike_simps]
/--
theorem `div_I` / 定理 `div_I`

English:
theorem div_I
  given: (z : K)
  statement: z / I = -(z * I)
  proof: by rw [div_eq_mul_inv, inv_I, mul_neg]

中文:
定理 div_I
  条件: (z : K)
  结论: z / I = -(z * I)
  证明: by rw [div_eq_mul_inv, inv_I, mul_neg]

Depends on / 依赖: div_eq_mul_inv, inv_I, mul_neg
-/
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/--
theorem `normSq_inv` / 定理 `normSq_inv`

English:
theorem normSq_inv
  given: (z : K)
  statement: normSq z⁻¹ = (normSq z)⁻¹
  proof: map_inv₀ normSq z

中文:
定理 normSq_inv
  条件: (z : K)
  结论: normSq z⁻¹ = (normSq z)⁻¹
  证明: map_inv₀ normSq z

Depends on / 依赖: normSq
-/
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/--
theorem `normSq_div` / 定理 `normSq_div`

English:
theorem normSq_div
  given: (z w : K)
  statement: normSq (z / w) = normSq z / normSq w
  proof: map_div₀ normSq z w

@[simp 1100, rclike_simps]

中文:
定理 normSq_div
  条件: (z w : K)
  结论: normSq (z / w) = normSq z / normSq w
  证明: map_div₀ normSq z w

@[simp 1100, rclike_simps]

Depends on / 依赖: normSq
-/
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

@[simp 1100, rclike_simps]
/--
theorem `norm_conj` / 定理 `norm_conj`

English:
theorem norm_conj
  given: (z : K)
  statement: ‖conj z‖ = ‖z‖
  proof: by simp only [← sqrt_normSq_eq_norm, normSq_conj]

中文:
定理 norm_conj
  条件: (z : K)
  结论: ‖conj z‖ = ‖z‖
  证明: by simp only [← sqrt_normSq_eq_norm, normSq_conj]

Depends on / 依赖: normSq_conj, sqrt_normSq_eq_norm
-/
theorem norm_conj (z : K) : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]

/--
lemma `nnnorm_conj` / 引理 `nnnorm_conj`

English:
lemma nnnorm_conj
  given: (z : K)
  statement: ‖conj z‖₊ = ‖z‖₊
  proof: by simp [nnnorm]

中文:
引理 nnnorm_conj
  条件: (z : K)
  结论: ‖conj z‖₊ = ‖z‖₊
  证明: by simp [nnnorm]
-/
@[simp 1100, rclike_simps] lemma nnnorm_conj (z : K) : ‖conj z‖₊ = ‖z‖₊ := by simp [nnnorm]

/--
lemma `enorm_conj` / 引理 `enorm_conj`

English:
lemma enorm_conj
  given: (z : K)
  statement: ‖conj z‖ₑ = ‖z‖ₑ
  proof: by simp [enorm]

中文:
引理 enorm_conj
  条件: (z : K)
  结论: ‖conj z‖ₑ = ‖z‖ₑ
  证明: by simp [enorm]
-/
@[simp 1100, rclike_simps] lemma enorm_conj (z : K) : ‖conj z‖ₑ = ‖z‖ₑ := by simp [enorm]

instance (priority := 100) : CStarRing K where
norm_mul_self_le x := le_of_eq ((norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_conj _)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule Real K
  body: by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

中文:
实例 :
  签名: 对合模 实数 K
  定义体: by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

Depends on / 依赖: RCLike, RCLike.ext, RCLike.smul_im, RCLike.smul_re, smul_im, smul_re
-/
instance : StarModule Real K where
  star_smul r a := by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

/-! ### Cast lemmas -/

@[rclike_simps, norm_cast]
/--
theorem `ofReal_natCast` / 定理 `ofReal_natCast`

English:
theorem ofReal_natCast
  given: (n : Nat)
  statement: ((n : Real) : K) = n
  proof: map_natCast (algebraMap Real K) n

@[simp, rclike_simps]

中文:
定理 of实数_natCast
  条件: (n : 自然数)
  结论: ((n : 实数) : K) = n
  证明: map_natCast (algebraMap Real K) n

@[simp, rclike_simps]

Depends on / 依赖: algebraMap, map_natCast
-/
theorem ofReal_natCast (n : Nat) : ((n : Real) : K) = n :=
  map_natCast (algebraMap Real K) n

@[simp, rclike_simps]
/--
theorem `natCast_re` / 定理 `natCast_re`

English:
theorem natCast_re
  given: (n : Nat)
  statement: re (n : K) = n
  proof: by rw [← ofReal_natCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

中文:
定理 natCast_re
  条件: (n : 自然数)
  结论: re (n : K) = n
  证明: by rw [← ofReal_natCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: ofReal_natCast, ofReal_re
-/
theorem natCast_re (n : Nat) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/--
theorem `natCast_im` / 定理 `natCast_im`

English:
theorem natCast_im
  given: (n : Nat)
  statement: im (n : K) = 0
  proof: by rw [← ofReal_natCast, ofReal_im]
@[simp, rclike_simps]

中文:
定理 natCast_im
  条件: (n : 自然数)
  结论: im (n : K) = 0
  证明: by rw [← ofReal_natCast, ofReal_im]
@[simp, rclike_simps]

Depends on / 依赖: ofReal_im, ofReal_natCast, rclike_simps
-/
theorem natCast_im (n : Nat) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]
@[simp, rclike_simps]
/--
theorem `ofNat_re` / 定理 `ofNat_re`

English:
theorem ofNat_re
  given: (n : Nat) [n.AtLeastTwo]
  statement: re (ofNat(n) : K) = ofNat(n)
  proof: natCast_re n
@[simp, rclike_simps]

中文:
定理 of自然数_re
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: re (of自然数(n) : K) = of自然数(n)
  证明: natCast_re n
@[simp, rclike_simps]

Depends on / 依赖: natCast_re, rclike_simps
-/
theorem ofNat_re (n : Nat) [n.AtLeastTwo] : re (ofNat(n) : K) = ofNat(n) :=
  natCast_re n
@[simp, rclike_simps]
/--
theorem `ofNat_im` / 定理 `ofNat_im`

English:
theorem ofNat_im
  given: (n : Nat) [n.AtLeastTwo]
  statement: im (ofNat(n) : K) = 0
  proof: natCast_im n

@[rclike_simps, norm_cast]

中文:
定理 of自然数_im
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: im (of自然数(n) : K) = 0
  证明: natCast_im n

@[rclike_simps, norm_cast]

Depends on / 依赖: natCast_im
-/
theorem ofNat_im (n : Nat) [n.AtLeastTwo] : im (ofNat(n) : K) = 0 :=
  natCast_im n

@[rclike_simps, norm_cast]
/--
theorem `ofReal_ofNat` / 定理 `ofReal_ofNat`

English:
theorem ofReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ((ofNat(n) : Real) : K) = ofNat(n)
  proof: ofReal_natCast n

中文:
定理 of实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ((of自然数(n) : 实数) : K) = of自然数(n)
  证明: ofReal_natCast n

Depends on / 依赖: ofReal_natCast
-/
theorem ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real) : K) = ofNat(n) :=
  ofReal_natCast n

/--
theorem `ofNat_mul_re` / 定理 `ofNat_mul_re`

English:
theorem ofNat_mul_re
  given: (n : Nat) [n.AtLeastTwo] (z : K)
  proof: by
  rw [← ofReal_ofNat]; rw [re_ofReal_mul]

中文:
定理 of自然数_mul_re
  条件: (n : 自然数) [n.AtLeastTwo] (z : K)
  证明: by
  rw [← ofReal_ofNat]; rw [re_ofReal_mul]

Depends on / 依赖: ofReal_ofNat, re_ofReal_mul
-/
theorem ofNat_mul_re (n : Nat) [n.AtLeastTwo] (z : K) :
    re (ofNat(n) * z) = ofNat(n) * re z := by
  rw [← ofReal_ofNat]; rw [re_ofReal_mul]

/--
theorem `ofNat_mul_im` / 定理 `ofNat_mul_im`

English:
theorem ofNat_mul_im
  given: (n : Nat) [n.AtLeastTwo] (z : K)
  proof: by
  rw [← ofReal_ofNat]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]

中文:
定理 of自然数_mul_im
  条件: (n : 自然数) [n.AtLeastTwo] (z : K)
  证明: by
  rw [← ofReal_ofNat]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]

Depends on / 依赖: im_ofReal_mul, ofReal_ofNat
-/
theorem ofNat_mul_im (n : Nat) [n.AtLeastTwo] (z : K) :
    im (ofNat(n) * z) = ofNat(n) * im z := by
  rw [← ofReal_ofNat]; rw [im_ofReal_mul]

@[rclike_simps, norm_cast]
/--
theorem `ofReal_intCast` / 定理 `ofReal_intCast`

English:
theorem ofReal_intCast
  given: (n : Int)
  statement: ((n : Real) : K) = n
  proof: map_intCast _ n

@[simp, rclike_simps]

中文:
定理 of实数_intCast
  条件: (n : 整数)
  结论: ((n : 实数) : K) = n
  证明: map_intCast _ n

@[simp, rclike_simps]

Depends on / 依赖: map_intCast
-/
theorem ofReal_intCast (n : Int) : ((n : Real) : K) = n :=
  map_intCast _ n

@[simp, rclike_simps]
/--
theorem `intCast_re` / 定理 `intCast_re`

English:
theorem intCast_re
  given: (n : Int)
  statement: re (n : K) = n
  proof: by rw [← ofReal_intCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

中文:
定理 intCast_re
  条件: (n : 整数)
  结论: re (n : K) = n
  证明: by rw [← ofReal_intCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: ofReal_intCast, ofReal_re
-/
theorem intCast_re (n : Int) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/--
theorem `intCast_im` / 定理 `intCast_im`

English:
theorem intCast_im
  given: (n : Int)
  statement: im (n : K) = 0
  proof: by rw [← ofReal_intCast, ofReal_im]

@[rclike_simps, norm_cast]

中文:
定理 intCast_im
  条件: (n : 整数)
  结论: im (n : K) = 0
  证明: by rw [← ofReal_intCast, ofReal_im]

@[rclike_simps, norm_cast]

Depends on / 依赖: ofReal_im, ofReal_intCast
-/
theorem intCast_im (n : Int) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]

@[rclike_simps, norm_cast]
/--
theorem `ofReal_nnratCast` / 定理 `ofReal_nnratCast`

English:
theorem ofReal_nnratCast
  given: (n : Rat>=0)
  statement: ((n : Real) : K) = n
  proof: map_nnratCast _ n

@[simp, rclike_simps]

中文:
定理 of实数_nnratCast
  条件: (n : 有理数>=0)
  结论: ((n : 实数) : K) = n
  证明: map_nnratCast _ n

@[simp, rclike_simps]

Depends on / 依赖: map_nnratCast
-/
theorem ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K) = n :=
  map_nnratCast _ n

@[simp, rclike_simps]
/--
theorem `nnratCast_re` / 定理 `nnratCast_re`

English:
theorem nnratCast_re
  given: (q : Rat>=0)
  statement: re (q : K) = q
  proof: by rw [← ofReal_nnratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

中文:
定理 nnratCast_re
  条件: (q : 有理数>=0)
  结论: re (q : K) = q
  证明: by rw [← ofReal_nnratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: ofReal_nnratCast, ofReal_re
-/
theorem nnratCast_re (q : Rat>=0) : re (q : K) = q := by rw [← ofReal_nnratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/--
theorem `nnratCast_im` / 定理 `nnratCast_im`

English:
theorem nnratCast_im
  given: (q : Rat>=0)
  statement: im (q : K) = 0
  proof: by rw [← ofReal_nnratCast, ofReal_im]

@[rclike_simps, norm_cast]

中文:
定理 nnratCast_im
  条件: (q : 有理数>=0)
  结论: im (q : K) = 0
  证明: by rw [← ofReal_nnratCast, ofReal_im]

@[rclike_simps, norm_cast]

Depends on / 依赖: ofReal_im, ofReal_nnratCast
-/
theorem nnratCast_im (q : Rat>=0) : im (q : K) = 0 := by rw [← ofReal_nnratCast, ofReal_im]

@[rclike_simps, norm_cast]
/--
theorem `ofReal_ratCast` / 定理 `ofReal_ratCast`

English:
theorem ofReal_ratCast
  given: (n : Rat)
  statement: ((n : Real) : K) = n
  proof: map_ratCast _ n

@[simp, rclike_simps]

中文:
定理 of实数_ratCast
  条件: (n : 有理数)
  结论: ((n : 实数) : K) = n
  证明: map_ratCast _ n

@[simp, rclike_simps]

Depends on / 依赖: map_ratCast
-/
theorem ofReal_ratCast (n : Rat) : ((n : Real) : K) = n :=
  map_ratCast _ n

@[simp, rclike_simps]
/--
theorem `ratCast_re` / 定理 `ratCast_re`

English:
theorem ratCast_re
  given: (q : Rat)
  statement: re (q : K) = q
  proof: by rw [← ofReal_ratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

中文:
定理 ratCast_re
  条件: (q : 有理数)
  结论: re (q : K) = q
  证明: by rw [← ofReal_ratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: ofReal_ratCast, ofReal_re
-/
theorem ratCast_re (q : Rat) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/--
theorem `ratCast_im` / 定理 `ratCast_im`

English:
theorem ratCast_im
  given: (q : Rat)
  statement: im (q : K) = 0
  proof: by rw [← ofReal_ratCast, ofReal_im]

中文:
定理 ratCast_im
  条件: (q : 有理数)
  结论: im (q : K) = 0
  证明: by rw [← ofReal_ratCast, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_ratCast
-/
theorem ratCast_im (q : Rat) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]

open OfScientific (ofScientific)

@[rclike_simps, norm_cast]
/--
theorem `ofReal_ofScientific` / 定理 `ofReal_ofScientific`

English:
theorem ofReal_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: ofReal_nnratCast _

@[simp, rclike_simps]

中文:
定理 of实数_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: ofReal_nnratCast _

@[simp, rclike_simps]

Depends on / 依赖: ofReal_nnratCast
-/
theorem ofReal_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    ((ofScientific m s e : Real) : K) = ofScientific m s e := ofReal_nnratCast _

@[simp, rclike_simps]
/--
theorem `ofScientific_re` / 定理 `ofScientific_re`

English:
theorem ofScientific_re
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: by rw [← ofReal_ofScientific, ofReal_re]

@[simp, rclike_simps, norm_cast]

中文:
定理 ofScientific_re
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: by rw [← ofReal_ofScientific, ofReal_re]

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: ofReal_ofScientific, ofReal_re
-/
theorem ofScientific_re (m : Nat) (s : Bool) (e : Nat) :
    re (ofScientific m s e : K) = ofScientific m s e := by rw [← ofReal_ofScientific, ofReal_re]

@[simp, rclike_simps, norm_cast]
/--
theorem `ofScientific_im` / 定理 `ofScientific_im`

English:
theorem ofScientific_im
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: by rw [← ofReal_ofScientific, ofReal_im]

中文:
定理 ofScientific_im
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: by rw [← ofReal_ofScientific, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_ofScientific
-/
theorem ofScientific_im (m : Nat) (s : Bool) (e : Nat) :
    im (ofScientific m s e : K) = 0 := by rw [← ofReal_ofScientific, ofReal_im]


/--
theorem `norm_of_nonneg` / 定理 `norm_of_nonneg`

English:
theorem norm_of_nonneg
  given: {r : Real} (h : 0 <= r)
  statement: ‖(r : K)‖ = r
  proof: (norm_ofReal _).trans (abs_of_nonneg h)

@[simp 1100, rclike_simps, norm_cast]

中文:
定理 norm_of_nonneg
  条件: {r : 实数} (h : 0 <= r)
  结论: ‖(r : K)‖ = r
  证明: (norm_ofReal _).trans (abs_of_nonneg h)

@[simp 1100, rclike_simps, norm_cast]

Depends on / 依赖: abs_of_nonneg, norm_ofReal
-/
theorem norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)

@[simp 1100, rclike_simps, norm_cast]
/--
theorem `norm_natCast` / 定理 `norm_natCast`

English:
theorem norm_natCast
  given: (n : Nat)
  statement: ‖(n : K)‖ = n
  proof: by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)

中文:
定理 norm_natCast
  条件: (n : 自然数)
  结论: ‖(n : K)‖ = n
  证明: by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)

Depends on / 依赖: Nat.cast_nonneg, cast_nonneg, norm_of_nonneg, ofReal_natCast
-/
theorem norm_natCast (n : Nat) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)

/--
lemma `nnnorm_natCast` / 引理 `nnnorm_natCast`

English:
lemma nnnorm_natCast
  given: (n : Nat)
  statement: ‖(n : K)‖₊ = n
  proof: by simp [nnnorm]

@[simp, rclike_simps]

中文:
引理 nnnorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : K)‖₊ = n
  证明: by simp [nnnorm]

@[simp, rclike_simps]
-/
@[simp, rclike_simps, norm_cast] lemma nnnorm_natCast (n : Nat) : ‖(n : K)‖₊ = n := by simp [nnnorm]

@[simp, rclike_simps]
/--
theorem `norm_ofNat` / 定理 `norm_ofNat`

English:
theorem norm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ‖(ofNat(n) : K)‖ = ofNat(n)
  proof: norm_natCast n

@[simp, rclike_simps]

中文:
定理 norm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ‖(of自然数(n) : K)‖ = of自然数(n)
  证明: norm_natCast n

@[simp, rclike_simps]

Depends on / 依赖: norm_natCast
-/
theorem norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖ = ofNat(n) :=
  norm_natCast n

@[simp, rclike_simps]
/--
lemma `nnnorm_ofNat` / 引理 `nnnorm_ofNat`

English:
lemma nnnorm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ‖(ofNat(n) : K)‖₊ = ofNat(n)
  proof: nnnorm_natCast n

中文:
引理 nnnorm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ‖(of自然数(n) : K)‖₊ = of自然数(n)
  证明: nnnorm_natCast n

Depends on / 依赖: nnnorm_natCast
-/
lemma nnnorm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖₊ = ofNat(n) :=
  nnnorm_natCast n

/--
lemma `norm_two` / 引理 `norm_two`

English:
lemma norm_two
  statement: ‖(2 : K)‖ = 2
  proof: norm_ofNat 2

中文:
引理 norm_two
  结论: ‖(2 : K)‖ = 2
  证明: norm_ofNat 2

Depends on / 依赖: norm_ofNat
-/
lemma norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2
/--
lemma `nnnorm_two` / 引理 `nnnorm_two`

English:
lemma nnnorm_two
  statement: ‖(2 : K)‖₊ = 2
  proof: nnnorm_ofNat 2

@[simp, rclike_simps, norm_cast]

中文:
引理 nnnorm_two
  结论: ‖(2 : K)‖₊ = 2
  证明: nnnorm_ofNat 2

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: nnnorm_ofNat
-/
lemma nnnorm_two : ‖(2 : K)‖₊ = 2 := nnnorm_ofNat 2

@[simp, rclike_simps, norm_cast]
/--
lemma `norm_nnratCast` / 引理 `norm_nnratCast`

English:
lemma norm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : K)‖ = q
  proof: by
  rw [← ofReal_nnratCast]; exact norm_of_nonneg q.cast_nonneg

@[simp, rclike_simps, norm_cast]

中文:
引理 norm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : K)‖ = q
  证明: by
  rw [← ofReal_nnratCast]; exact norm_of_nonneg q.cast_nonneg

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: cast_nonneg, norm_of_nonneg, ofReal_nnratCast, q.cast_nonneg
-/
lemma norm_nnratCast (q : Rat>=0) : ‖(q : K)‖ = q := by
  rw [← ofReal_nnratCast]; exact norm_of_nonneg q.cast_nonneg

@[simp, rclike_simps, norm_cast]
/--
lemma `nnnorm_nnratCast` / 引理 `nnnorm_nnratCast`

English:
lemma nnnorm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : K)‖₊ = q
  proof: by simp [nnnorm]; rfl

中文:
引理 nnnorm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : K)‖₊ = q
  证明: by simp [nnnorm]; rfl

Depends on / 依赖: nnnorm
-/
lemma nnnorm_nnratCast (q : Rat>=0) : ‖(q : K)‖₊ = q := by simp [nnnorm]; rfl

variable (K) in
/--
lemma `norm_nsmul` / 引理 `norm_nsmul`

English:
lemma norm_nsmul
  given: [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E)
  statement: ‖n • x‖ = n • ‖x‖
  proof: by
  simpa [Nat.cast_smul_eq_nsmul] using norm_smul (n : K) x

中文:
引理 norm_nsmul
  条件: [赋范交换加群 E] [赋范空间 K E] (n : 自然数) (x : E)
  结论: ‖n • x‖ = n • ‖x‖
  证明: by
  simpa [Nat.cast_smul_eq_nsmul] using norm_smul (n : K) x

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, norm_smul
-/
lemma norm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E) : ‖n • x‖ = n • ‖x‖ := by
  simpa [Nat.cast_smul_eq_nsmul] using norm_smul (n : K) x

variable (K) in
/--
lemma `nnnorm_nsmul` / 引理 `nnnorm_nsmul`

English:
lemma nnnorm_nsmul
  given: [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E)
  proof: by simpa [Nat.cast_smul_eq_nsmul] using nnnorm_smul (n : K) x

中文:
引理 nnnorm_nsmul
  条件: [赋范交换加群 E] [赋范空间 K E] (n : 自然数) (x : E)
  证明: by simpa [Nat.cast_smul_eq_nsmul] using nnnorm_smul (n : K) x

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, nnnorm_smul
-/
lemma nnnorm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E) :
    ‖n • x‖₊ = n • ‖x‖₊ := by simpa [Nat.cast_smul_eq_nsmul] using nnnorm_smul (n : K) x

/--
theorem `mul_self_norm` / 定理 `mul_self_norm`

English:
theorem mul_self_norm
  given: (z : K)
  statement: ‖z‖ * ‖z‖ = normSq z
  proof: by rw [normSq_eq_def', sq]

中文:
定理 mul_self_norm
  条件: (z : K)
  结论: ‖z‖ * ‖z‖ = normSq z
  证明: by rw [normSq_eq_def', sq]

Depends on / 依赖: normSq_eq_def
-/
theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]

attribute [rclike_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

/--
theorem `abs_re_le_norm` / 定理 `abs_re_le_norm`

English:
theorem abs_re_le_norm
  given: (z : K)
  statement: |re z| <= ‖z‖
  proof: by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply re_sq_le_normSq

中文:
定理 abs_re_le_norm
  条件: (z : K)
  结论: |re z| <= ‖z‖
  证明: by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply re_sq_le_normSq

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, mul_self_le_mul_self_iff, mul_self_norm, norm_nonneg, re_sq_le_normSq
-/
theorem abs_re_le_norm (z : K) : |re z| <= ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply re_sq_le_normSq

/--
theorem `abs_im_le_norm` / 定理 `abs_im_le_norm`

English:
theorem abs_im_le_norm
  given: (z : K)
  statement: |im z| <= ‖z‖
  proof: by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply im_sq_le_normSq

中文:
定理 abs_im_le_norm
  条件: (z : K)
  结论: |im z| <= ‖z‖
  证明: by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply im_sq_le_normSq

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, im_sq_le_normSq, mul_self_le_mul_self_iff, mul_self_norm, norm_nonneg
-/
theorem abs_im_le_norm (z : K) : |im z| <= ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _)]; rw [abs_mul_abs_self]; rw [mul_self_norm]
  apply im_sq_le_normSq

/--
theorem `norm_re_le_norm` / 定理 `norm_re_le_norm`

English:
theorem norm_re_le_norm
  given: (z : K)
  statement: ‖re z‖ <= ‖z‖
  proof: abs_re_le_norm z

中文:
定理 norm_re_le_norm
  条件: (z : K)
  结论: ‖re z‖ <= ‖z‖
  证明: abs_re_le_norm z

Depends on / 依赖: abs_re_le_norm
-/
theorem norm_re_le_norm (z : K) : ‖re z‖ <= ‖z‖ :=
  abs_re_le_norm z

/--
theorem `norm_im_le_norm` / 定理 `norm_im_le_norm`

English:
theorem norm_im_le_norm
  given: (z : K)
  statement: ‖im z‖ <= ‖z‖
  proof: abs_im_le_norm z

中文:
定理 norm_im_le_norm
  条件: (z : K)
  结论: ‖im z‖ <= ‖z‖
  证明: abs_im_le_norm z

Depends on / 依赖: abs_im_le_norm
-/
theorem norm_im_le_norm (z : K) : ‖im z‖ <= ‖z‖ :=
  abs_im_le_norm z

/--
theorem `re_le_norm` / 定理 `re_le_norm`

English:
theorem re_le_norm
  given: (z : K)
  statement: re z <= ‖z‖
  proof: (abs_le.1 (abs_re_le_norm z)).2

中文:
定理 re_le_norm
  条件: (z : K)
  结论: re z <= ‖z‖
  证明: (abs_le.1 (abs_re_le_norm z)).2

Depends on / 依赖: abs_le, abs_re_le_norm
-/
theorem re_le_norm (z : K) : re z <= ‖z‖ :=
  (abs_le.1 (abs_re_le_norm z)).2

/--
theorem `im_le_norm` / 定理 `im_le_norm`

English:
theorem im_le_norm
  given: (z : K)
  statement: im z <= ‖z‖
  proof: (abs_le.1 (abs_im_le_norm _)).2

中文:
定理 im_le_norm
  条件: (z : K)
  结论: im z <= ‖z‖
  证明: (abs_le.1 (abs_im_le_norm _)).2

Depends on / 依赖: abs_im_le_norm, abs_le
-/
theorem im_le_norm (z : K) : im z <= ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

/--
theorem `im_eq_zero_of_le` / 定理 `im_eq_zero_of_le`

English:
theorem im_eq_zero_of_le
  given: {a : K} (h : ‖a‖ <= re a)
  statement: im a = 0
  proof: by
  simpa only [mul_self_norm a, normSq_apply, left_eq_add, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)

中文:
定理 im_eq_zero_of_le
  条件: {a : K} (h : ‖a‖ <= re a)
  结论: im a = 0
  证明: by
  simpa only [mul_self_norm a, normSq_apply, left_eq_add, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)

Depends on / 依赖: antisymm, congr_arg, left_eq_add, mul_self_eq_zero, mul_self_norm, normSq_apply, re_le_norm
-/
theorem im_eq_zero_of_le {a : K} (h : ‖a‖ <= re a) : im a = 0 := by
  simpa only [mul_self_norm a, normSq_apply, left_eq_add, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)

/--
theorem `re_eq_self_of_le` / 定理 `re_eq_self_of_le`

English:
theorem re_eq_self_of_le
  given: {a : K} (h : ‖a‖ <= re a)
  statement: (re a : K) = a
  proof: by
  rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [im_eq_zero_of_le h]

中文:
定理 re_eq_self_of_le
  条件: {a : K} (h : ‖a‖ <= re a)
  结论: (re a : K) = a
  证明: by
  rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [im_eq_zero_of_le h]

Depends on / 依赖: conj_eq_iff_im, conj_eq_iff_re, im_eq_zero_of_le
-/
theorem re_eq_self_of_le {a : K} (h : ‖a‖ <= re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [im_eq_zero_of_le h]

open IsAbsoluteValue

/--
theorem `abs_re_div_norm_le_one` / 定理 `abs_re_div_norm_le_one`

English:
theorem abs_re_div_norm_le_one
  given: (z : K)
  statement: |re z / ‖z‖| <= 1
  proof: by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_re_le_norm _) (norm_nonneg _)

中文:
定理 abs_re_div_norm_le_one
  条件: (z : K)
  结论: |re z / ‖z‖| <= 1
  证明: by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_re_le_norm _) (norm_nonneg _)

Depends on / 依赖: abs_div, abs_norm, abs_re_le_norm, norm_nonneg
-/
theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| <= 1 := by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_re_le_norm _) (norm_nonneg _)

/--
theorem `abs_im_div_norm_le_one` / 定理 `abs_im_div_norm_le_one`

English:
theorem abs_im_div_norm_le_one
  given: (z : K)
  statement: |im z / ‖z‖| <= 1
  proof: by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_im_le_norm _) (norm_nonneg _)

中文:
定理 abs_im_div_norm_le_one
  条件: (z : K)
  结论: |im z / ‖z‖| <= 1
  证明: by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_im_le_norm _) (norm_nonneg _)

Depends on / 依赖: abs_div, abs_im_le_norm, abs_norm, norm_nonneg
-/
theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| <= 1 := by
  rw [abs_div]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_im_le_norm _) (norm_nonneg _)

/--
theorem `norm_I_of_ne_zero` / 定理 `norm_I_of_ne_zero`

English:
theorem norm_I_of_ne_zero
  given: (hI : (I : K) != 0)
  statement: ‖(I : K)‖ = 1
  proof: by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one]; rw [one_mul]; rw [← norm_mul]; rw [I_mul_I_of_nonzero hI]; rw [norm_neg]; rw [norm_one]

中文:
定理 norm_I_of_ne_zero
  条件: (hI : (I : K) != 0)
  结论: ‖(I : K)‖ = 1
  证明: by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one]; rw [one_mul]; rw [← norm_mul]; rw [I_mul_I_of_nonzero hI]; rw [norm_neg]; rw [norm_one]

Depends on / 依赖: I_mul_I_of_nonzero, mul_self_inj_of_nonneg, norm_mul, norm_neg, norm_nonneg, norm_one, one_mul, zero_le_one
-/
theorem norm_I_of_ne_zero (hI : (I : K) != 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one]; rw [one_mul]; rw [← norm_mul]; rw [I_mul_I_of_nonzero hI]; rw [norm_neg]; rw [norm_one]

/--
theorem `norm_I` / 定理 `norm_I`

English:
theorem norm_I
  statement: ‖(I : K)‖ = if (I : K) = 0 then 0 else 1
  proof: by
  grind [norm_I_of_ne_zero, norm_eq_zero]

中文:
定理 norm_I
  结论: ‖(I : K)‖ = if (I : K) = 0 then 0 else 1
  证明: by
  grind [norm_I_of_ne_zero, norm_eq_zero]

Depends on / 依赖: norm_I_of_ne_zero, norm_eq_zero
-/
theorem norm_I : ‖(I : K)‖ = if (I : K) = 0 then 0 else 1 := by
  grind [norm_I_of_ne_zero, norm_eq_zero]

/--
theorem `re_eq_norm_of_mul_conj` / 定理 `re_eq_norm_of_mul_conj`

English:
theorem re_eq_norm_of_mul_conj
  given: (x : K)
  statement: re (x * conj x) = ‖x * conj x‖
  proof: by
  rw [mul_conj]; rw [← ofReal_pow]; simp [-map_pow]

中文:
定理 re_eq_norm_of_mul_conj
  条件: (x : K)
  结论: re (x * conj x) = ‖x * conj x‖
  证明: by
  rw [mul_conj]; rw [← ofReal_pow]; simp [-map_pow]

Depends on / 依赖: map_pow, mul_conj, ofReal_pow
-/
theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj]; rw [← ofReal_pow]; simp [-map_pow]

/--
theorem `norm_sq_re_add_conj` / 定理 `norm_sq_re_add_conj`

English:
theorem norm_sq_re_add_conj
  given: (x : K)
  statement: ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2
  proof: by
  rw [add_conj]; rw [← ofReal_ofNat]; rw [← ofReal_mul]; rw [norm_ofReal]; rw [sq_abs]; rw [ofReal_re]

中文:
定理 norm_sq_re_add_conj
  条件: (x : K)
  结论: ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2
  证明: by
  rw [add_conj]; rw [← ofReal_ofNat]; rw [← ofReal_mul]; rw [norm_ofReal]; rw [sq_abs]; rw [ofReal_re]

Depends on / 依赖: add_conj, norm_ofReal, ofReal_mul, ofReal_ofNat, ofReal_re, sq_abs
-/
theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj]; rw [← ofReal_ofNat]; rw [← ofReal_mul]; rw [norm_ofReal]; rw [sq_abs]; rw [ofReal_re]

/--
theorem `norm_sq_re_conj_add` / 定理 `norm_sq_re_conj_add`

English:
theorem norm_sq_re_conj_add
  given: (x : K)
  statement: ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2
  proof: by
  rw [add_comm]; rw [norm_sq_re_add_conj]

中文:
定理 norm_sq_re_conj_add
  条件: (x : K)
  结论: ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2
  证明: by
  rw [add_comm]; rw [norm_sq_re_add_conj]

Depends on / 依赖: add_comm, norm_sq_re_add_conj
-/
theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm]; rw [norm_sq_re_add_conj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormSMulClass Int K
  body: by
    rw [zsmul_eq_mul]; rw [norm_mul]; rw [← ofReal_intCast]; rw [norm_ofReal]; rw [Int.norm_eq_abs]

中文:
实例 :
  签名: NormSMul类 整数 K
  定义体: by
    rw [zsmul_eq_mul]; rw [norm_mul]; rw [← ofReal_intCast]; rw [norm_ofReal]; rw [Int.norm_eq_abs]

Depends on / 依赖: Int.norm_eq_abs, norm_eq_abs, norm_mul, norm_ofReal, ofReal_intCast, zsmul_eq_mul
-/
instance : NormSMulClass Int K where
  norm_smul r x := by
    rw [zsmul_eq_mul]; rw [norm_mul]; rw [← ofReal_intCast]; rw [norm_ofReal]; rw [Int.norm_eq_abs]


/--
theorem `isCauSeq_re` / 定理 `isCauSeq_re`

English:
theorem isCauSeq_re
  given: (f : CauSeq K norm)
  statement: IsCauSeq abs fun n => re (f n)
  proof: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

中文:
定理 isCauSeq_re
  条件: (f : CauSeq K norm)
  结论: IsCauSeq abs fun n => re (f n)
  证明: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)
-/
theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

/--
theorem `isCauSeq_im` / 定理 `isCauSeq_im`

English:
theorem isCauSeq_im
  given: (f : CauSeq K norm)
  statement: IsCauSeq abs fun n => im (f n)
  proof: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)

中文:
定理 isCauSeq_im
  条件: (f : CauSeq K norm)
  结论: IsCauSeq abs fun n => im (f n)
  证明: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)
-/
theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)

/--
Definition of `cauSeqRe` / `cauSeqRe` 的定义

English:
definition cauSeqRe
  signature: (f : CauSeq K norm)
  body: ⟨_, isCauSeq_re f⟩

中文:
定义 cauSeqRe
  签名: (f : CauSeq K norm)
  定义体: ⟨_, isCauSeq_re f⟩

Depends on / 依赖: isCauSeq_re
-/
noncomputable def cauSeqRe (f : CauSeq K norm) : CauSeq Real abs :=
  ⟨_, isCauSeq_re f⟩

/--
Definition of `cauSeqIm` / `cauSeqIm` 的定义

English:
definition cauSeqIm
  signature: (f : CauSeq K norm)
  body: ⟨_, isCauSeq_im f⟩

中文:
定义 cauSeqIm
  签名: (f : CauSeq K norm)
  定义体: ⟨_, isCauSeq_im f⟩

Depends on / 依赖: isCauSeq_im
-/
noncomputable def cauSeqIm (f : CauSeq K norm) : CauSeq Real abs :=
  ⟨_, isCauSeq_im f⟩

/--
theorem `isCauSeq_norm` / 定理 `isCauSeq_norm`

English:
theorem isCauSeq_norm
  given: {f : Nat -> K} (hf : IsCauSeq norm f)
  statement: IsCauSeq abs (norm ∘ f)
  proof: fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

中文:
定理 isCauSeq_norm
  条件: {f : 自然数 -> K} (hf : IsCauSeq norm f)
  结论: IsCauSeq abs (norm ∘ f)
  证明: fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
-/
theorem isCauSeq_norm {f : Nat -> K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/--
lemma `I_mem_skewAdjoint` / 引理 `I_mem_skewAdjoint`

English:
lemma I_mem_skewAdjoint
  statement: I in skewAdjoint K
  proof: by simp [skewAdjoint.mem_iff]

中文:
引理 I_mem_skewAdjoint
  结论: I in skewAdjoint K
  证明: by simp [skewAdjoint.mem_iff]

Depends on / 依赖: mem_iff, skewAdjoint, skewAdjoint.mem_iff
-/
lemma I_mem_skewAdjoint : I in skewAdjoint K := by simp [skewAdjoint.mem_iff]

end RCLike

section
variable {A : Type*} [AddCommGroup A] [StarAddMonoid A] [Module K A] [StarModule K A] {a : A}

open RCLike

/--
lemma `IsSelfAdjoint.I_smul_mem_skewAdjoint` / 引理 `IsSelfAdjoint.I_smul_mem_skewAdjoint`

English:
lemma IsSelfAdjoint.I_smul_mem_skewAdjoint
  given: (h : IsSelfAdjoint a)
  proof: h.smul_mem_skewAdjoint I_mem_skewAdjoint

中文:
引理 IsSelfAdjoint.I_smul_mem_skewAdjoint
  条件: (h : IsSelfAdjoint a)
  证明: h.smul_mem_skewAdjoint I_mem_skewAdjoint

Depends on / 依赖: I_mem_skewAdjoint, h.smul_mem_skewAdjoint, smul_mem_skewAdjoint
-/
lemma IsSelfAdjoint.I_smul_mem_skewAdjoint (h : IsSelfAdjoint a) :
    (I : K) • a in skewAdjoint A := h.smul_mem_skewAdjoint I_mem_skewAdjoint

/--
lemma `IsSelfAdjoint.I_smul_of_mem_skewAdjoint` / 引理 `IsSelfAdjoint.I_smul_of_mem_skewAdjoint`

English:
lemma IsSelfAdjoint.I_smul_of_mem_skewAdjoint
  given: (h : a in skewAdjoint A)
  proof: isSelfAdjoint_smul_of_mem_skewAdjoint I_mem_skewAdjoint h

中文:
引理 IsSelfAdjoint.I_smul_of_mem_skewAdjoint
  条件: (h : a in skewAdjoint A)
  证明: isSelfAdjoint_smul_of_mem_skewAdjoint I_mem_skewAdjoint h

Depends on / 依赖: I_mem_skewAdjoint, isSelfAdjoint_smul_of_mem_skewAdjoint
-/
lemma IsSelfAdjoint.I_smul_of_mem_skewAdjoint (h : a in skewAdjoint A) :
    IsSelfAdjoint ((I : K) • a) := isSelfAdjoint_smul_of_mem_skewAdjoint I_mem_skewAdjoint h

end

section Instances

/--
Instance `Real.instRCLike` / 实例 `Real.instRCLike`

English:
instance Real.instRCLike
  signature: : RCLike Real where
  body: AddMonoidHom.id Real
  im := 0
  I := 0
  I_re_ax := by simp only [map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax _ := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w

中文:
实例 实数.instRCLike
  签名: : RCLike 实数 where
  定义体: AddMonoidHom.id Real
  im := 0
  I := 0
  I_re_ax := by simp only [map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax _ := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id
-/
noncomputable instance Real.instRCLike : RCLike Real where
  re := AddMonoidHom.id Real
  im := 0
  I := 0
  I_re_ax := by simp only [map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax _ := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w := by simp only [sub_zero, mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_ax z w := by simp only [add_zero, zero_mul, mul_zero, AddMonoidHom.zero_apply]
  conj_re_ax z := by simp only [starRingEnd_apply, star_id_of_comm]
  conj_im_ax _ := by simp only [neg_zero, AddMonoidHom.zero_apply]
  conj_I_ax := by simp only [map_zero, neg_zero]
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax _ := by simp only [mul_zero, AddMonoidHom.zero_apply]
  le_iff_re_im := (and_iff_left rfl).symm

end Instances

namespace RCLike

section NormedField
variable [NormedField E] [CharZero E] [NormedSpace K E]
include K

variable (K) in
/--
lemma `norm_nnqsmul` / 引理 `norm_nnqsmul`

English:
lemma norm_nnqsmul
  given: (q : Rat>=0) (x : E)
  statement: ‖q • x‖ = q • ‖x‖
  proof: by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! norm_smul (q : K) x

中文:
引理 norm_nnqsmul
  条件: (q : 有理数>=0) (x : E)
  结论: ‖q • x‖ = q • ‖x‖
  证明: by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! norm_smul (q : K) x

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, norm_smul
-/
lemma norm_nnqsmul (q : Rat>=0) (x : E) : ‖q • x‖ = q • ‖x‖ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! norm_smul (q : K) x

variable (K) in
/--
lemma `nnnorm_nnqsmul` / 引理 `nnnorm_nnqsmul`

English:
lemma nnnorm_nnqsmul
  given: (q : Rat>=0) (x : E)
  statement: ‖q • x‖₊ = q • ‖x‖₊
  proof: by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! nnnorm_smul (q : K) x

@[bound]

中文:
引理 nnnorm_nnqsmul
  条件: (q : 有理数>=0) (x : E)
  结论: ‖q • x‖₊ = q • ‖x‖₊
  证明: by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! nnnorm_smul (q : K) x

@[bound]

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, nnnorm_smul
-/
lemma nnnorm_nnqsmul (q : Rat>=0) (x : E) : ‖q • x‖₊ = q • ‖x‖₊ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! nnnorm_smul (q : K) x

@[bound]
/--
lemma `norm_expect_le` / 引理 `norm_expect_le`

English:
lemma norm_expect_le
  given: {ι : Type*} {s : Finset ι} {f : ι -> E}
  statement: ‖𝔼 i in s, f i‖ <= 𝔼 i in s, ‖f i‖
  proof: Finset.le_expect_of_subadditive norm_zero norm_add_le fun _ _ => by rw [norm_nnqsmul K]

中文:
引理 norm_expect_le
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> E}
  结论: ‖𝔼 i in s, f i‖ <= 𝔼 i in s, ‖f i‖
  证明: Finset.le_expect_of_subadditive norm_zero norm_add_le fun _ _ => by rw [norm_nnqsmul K]

Depends on / 依赖: Finset, Finset.le_expect_of_subadditive, le_expect_of_subadditive, norm_add_le, norm_nnqsmul, norm_zero
-/
lemma norm_expect_le {ι : Type*} {s : Finset ι} {f : ι -> E} : ‖𝔼 i in s, f i‖ <= 𝔼 i in s, ‖f i‖ :=
  Finset.le_expect_of_subadditive norm_zero norm_add_le fun _ _ => by rw [norm_nnqsmul K]

end NormedField

section Order

open scoped ComplexOrder
variable {z w : K}

/--
theorem `lt_iff_re_im` / 定理 `lt_iff_re_im`

English:
theorem lt_iff_re_im
  statement: z < w ↔ re z < re w ∧ im z = im w
  proof: by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

中文:
定理 lt_iff_re_im
  结论: z < w ↔ re z < re w ∧ im z = im w
  证明: by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, le_iff_re_im, lt_iff_le_and_ne, ne_of_apply_ne, simp_rw
-/
theorem lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

/--
theorem `nonneg_iff` / 定理 `nonneg_iff`

English:
theorem nonneg_iff
  statement: 0 <= z ↔ 0 <= re z ∧ im z = 0
  proof: by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

中文:
定理 nonneg_iff
  结论: 0 <= z ↔ 0 <= re z ∧ im z = 0
  证明: by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

Depends on / 依赖: eq_comm, le_iff_re_im, map_zero
-/
theorem nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  statement: 0 < z ↔ 0 < re z ∧ im z = 0
  proof: by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

中文:
定理 pos_iff
  结论: 0 < z ↔ 0 < re z ∧ im z = 0
  证明: by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

Depends on / 依赖: eq_comm, lt_iff_re_im, map_zero
-/
theorem pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

/--
theorem `nonpos_iff` / 定理 `nonpos_iff`

English:
theorem nonpos_iff
  statement: z <= 0 ↔ re z <= 0 ∧ im z = 0
  proof: by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

中文:
定理 nonpos_iff
  结论: z <= 0 ↔ re z <= 0 ∧ im z = 0
  证明: by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

Depends on / 依赖: le_iff_re_im, map_zero
-/
theorem nonpos_iff : z <= 0 ↔ re z <= 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

/--
theorem `neg_iff` / 定理 `neg_iff`

English:
theorem neg_iff
  statement: z < 0 ↔ re z < 0 ∧ im z = 0
  proof: by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

中文:
定理 neg_iff
  结论: z < 0 ↔ re z < 0 ∧ im z = 0
  证明: by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

Depends on / 依赖: lt_iff_re_im, map_zero
-/
theorem neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

/--
lemma `nonneg_iff_exists_ofReal` / 引理 `nonneg_iff_exists_ofReal`

English:
lemma nonneg_iff_exists_ofReal
  statement: 0 <= z ↔ exists x >= (0 : Real), x = z
  proof: by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop

中文:
引理 nonneg_iff_存在_of实数
  结论: 0 <= z ↔ 存在 x >= (0 : 实数), x = z
  证明: by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop

Depends on / 依赖: ext_iff, nonneg_iff, simp_rw
-/
lemma nonneg_iff_exists_ofReal : 0 <= z ↔ exists x >= (0 : Real), x = z := by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop

/--
lemma `pos_iff_exists_ofReal` / 引理 `pos_iff_exists_ofReal`

English:
lemma pos_iff_exists_ofReal
  statement: 0 < z ↔ exists x > (0 : Real), x = z
  proof: by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop

中文:
引理 pos_iff_存在_of实数
  结论: 0 < z ↔ 存在 x > (0 : 实数), x = z
  证明: by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop

Depends on / 依赖: ext_iff, pos_iff, simp_rw
-/
lemma pos_iff_exists_ofReal : 0 < z ↔ exists x > (0 : Real), x = z := by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop

/--
lemma `nonpos_iff_exists_ofReal` / 引理 `nonpos_iff_exists_ofReal`

English:
lemma nonpos_iff_exists_ofReal
  statement: z <= 0 ↔ exists x <= (0 : Real), x = z
  proof: by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop

中文:
引理 nonpos_iff_存在_of实数
  结论: z <= 0 ↔ 存在 x <= (0 : 实数), x = z
  证明: by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop

Depends on / 依赖: ext_iff, nonpos_iff, simp_rw
-/
lemma nonpos_iff_exists_ofReal : z <= 0 ↔ exists x <= (0 : Real), x = z := by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop

/--
lemma `neg_iff_exists_ofReal` / 引理 `neg_iff_exists_ofReal`

English:
lemma neg_iff_exists_ofReal
  statement: z < 0 ↔ exists x < (0 : Real), x = z
  proof: by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]

中文:
引理 neg_iff_存在_of实数
  结论: z < 0 ↔ 存在 x < (0 : 实数), x = z
  证明: by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]

Depends on / 依赖: ext_iff, neg_iff, simp_rw
-/
lemma neg_iff_exists_ofReal : z < 0 ↔ exists x < (0 : Real), x = z := by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]
/--
lemma `ofReal_le_ofReal` / 引理 `ofReal_le_ofReal`

English:
lemma ofReal_le_ofReal
  given: {x y : Real}
  statement: (x : K) <= (y : K) ↔ x <= y
  proof: by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]

中文:
引理 of实数_le_of实数
  条件: {x y : 实数}
  结论: (x : K) <= (y : K) ↔ x <= y
  证明: by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]

Depends on / 依赖: le_iff_re_im
-/
lemma ofReal_le_ofReal {x y : Real} : (x : K) <= (y : K) ↔ x <= y := by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]
/--
lemma `ofReal_lt_ofReal` / 引理 `ofReal_lt_ofReal`

English:
lemma ofReal_lt_ofReal
  given: {x y : Real}
  statement: (x : K) < (y : K) ↔ x < y
  proof: by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]

中文:
引理 of实数_lt_of实数
  条件: {x y : 实数}
  结论: (x : K) < (y : K) ↔ x < y
  证明: by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]

Depends on / 依赖: lt_iff_re_im
-/
lemma ofReal_lt_ofReal {x y : Real} : (x : K) < (y : K) ↔ x < y := by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]
/--
lemma `ofReal_nonneg` / 引理 `ofReal_nonneg`

English:
lemma ofReal_nonneg
  given: {x : Real}
  statement: 0 <= (x : K) ↔ 0 <= x
  proof: by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]

中文:
引理 of实数_nonneg
  条件: {x : 实数}
  结论: 0 <= (x : K) ↔ 0 <= x
  证明: by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]

Depends on / 依赖: ofReal_le_ofReal, ofReal_zero
-/
lemma ofReal_nonneg {x : Real} : 0 <= (x : K) ↔ 0 <= x := by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]
/--
lemma `ofReal_nonpos` / 引理 `ofReal_nonpos`

English:
lemma ofReal_nonpos
  given: {x : Real}
  statement: (x : K) <= 0 ↔ x <= 0
  proof: by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]

中文:
引理 of实数_nonpos
  条件: {x : 实数}
  结论: (x : K) <= 0 ↔ x <= 0
  证明: by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]

Depends on / 依赖: ofReal_le_ofReal, ofReal_zero
-/
lemma ofReal_nonpos {x : Real} : (x : K) <= 0 ↔ x <= 0 := by
  rw [← ofReal_zero]; rw [ofReal_le_ofReal]

@[simp, norm_cast]
/--
lemma `ofReal_pos` / 引理 `ofReal_pos`

English:
lemma ofReal_pos
  given: {x : Real}
  statement: 0 < (x : K) ↔ 0 < x
  proof: by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

@[simp, norm_cast]

中文:
引理 of实数_pos
  条件: {x : 实数}
  结论: 0 < (x : K) ↔ 0 < x
  证明: by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

@[simp, norm_cast]

Depends on / 依赖: ofReal_lt_ofReal, ofReal_zero
-/
lemma ofReal_pos {x : Real} : 0 < (x : K) ↔ 0 < x := by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

@[simp, norm_cast]
/--
lemma `ofReal_lt_zero` / 引理 `ofReal_lt_zero`

English:
lemma ofReal_lt_zero
  given: {x : Real}
  statement: (x : K) < 0 ↔ x < 0
  proof: by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

中文:
引理 of实数_lt_zero
  条件: {x : 实数}
  结论: (x : K) < 0 ↔ x < 0
  证明: by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

Depends on / 依赖: ofReal_lt_ofReal, ofReal_zero
-/
lemma ofReal_lt_zero {x : Real} : (x : K) < 0 ↔ x < 0 := by
  rw [← ofReal_zero]; rw [ofReal_lt_ofReal]

/--
lemma `norm_le_re_iff_eq_norm` / 引理 `norm_le_re_iff_eq_norm`

English:
lemma norm_le_re_iff_eq_norm
  given: {z : K}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h']; rw [re_eq_self_of_le h]
  · rw [h]
    simp

中文:
引理 norm_le_re_iff_eq_norm
  条件: {z : K}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h']; rw [re_eq_self_of_le h]
  · rw [h]
    simp

Depends on / 依赖: le_antisymm, re_eq_self_of_le, re_le_norm
-/
lemma norm_le_re_iff_eq_norm {z : K} :
    ‖z‖ <= re z ↔ z = ‖z‖ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h']; rw [re_eq_self_of_le h]
  · rw [h]
    simp

/--
lemma `re_le_neg_norm_iff_eq_neg_norm` / 引理 `re_le_neg_norm_iff_eq_neg_norm`

English:
lemma re_le_neg_norm_iff_eq_neg_norm
  given: {z : K}
  proof: by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

中文:
引理 re_le_neg_norm_iff_eq_neg_norm
  条件: {z : K}
  证明: by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

Depends on / 依赖: le_neg, neg_eq_iff_eq_neg, norm_le_re_iff_eq_norm
-/
lemma re_le_neg_norm_iff_eq_neg_norm {z : K} :
    re z <= -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

/--
lemma `norm_of_nonneg'` / 引理 `norm_of_nonneg'`

English:
lemma norm_of_nonneg'
  given: {x : K} (hx : 0 <= x)
  statement: ‖x‖ = x
  proof: by
  rw [eq_comm]; rw [← norm_le_re_iff_eq_norm]; rw [← sqrt_normSq_eq_norm]; rw [normSq_apply]
  simp [nonneg_iff.mp hx]

中文:
引理 norm_of_nonneg'
  条件: {x : K} (hx : 0 <= x)
  结论: ‖x‖ = x
  证明: by
  rw [eq_comm]; rw [← norm_le_re_iff_eq_norm]; rw [← sqrt_normSq_eq_norm]; rw [normSq_apply]
  simp [nonneg_iff.mp hx]

Depends on / 依赖: eq_comm, nonneg_iff, nonneg_iff.mp, normSq_apply, norm_le_re_iff_eq_norm, sqrt_normSq_eq_norm
-/
lemma norm_of_nonneg' {x : K} (hx : 0 <= x) : ‖x‖ = x := by
  rw [eq_comm]; rw [← norm_le_re_iff_eq_norm]; rw [← sqrt_normSq_eq_norm]; rw [normSq_apply]
  simp [nonneg_iff.mp hx]

/--
lemma `re_nonneg_of_nonneg` / 引理 `re_nonneg_of_nonneg`

English:
lemma re_nonneg_of_nonneg
  given: {x : K} (hx : IsSelfAdjoint x)
  statement: 0 <= re x ↔ 0 <= x
  proof: by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]

中文:
引理 re_nonneg_of_nonneg
  条件: {x : K} (hx : IsSelfAdjoint x)
  结论: 0 <= re x ↔ 0 <= x
  证明: by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]

Depends on / 依赖: conj_eq_iff_im, conj_eq_iff_im.mp, nonneg_iff
-/
lemma re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjoint x) : 0 <= re x ↔ 0 <= x := by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]
/--
lemma `re_le_re` / 引理 `re_le_re`

English:
lemma re_le_re
  given: {x y : K} (h : x <= y)
  statement: re x <= re y
  proof: by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

中文:
引理 re_le_re
  条件: {x y : K} (h : x <= y)
  结论: re x <= re y
  证明: by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, le_iff_re_im
-/
lemma re_le_re {x y : K} (h : x <= y) : re x <= re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

/--
lemma `re_monotone` / 引理 `re_monotone`

English:
lemma re_monotone
  statement: Monotone (re : K -> Real)
  proof: fun _ _ => re_le_re

中文:
引理 re_monotone
  结论: 递增 (re : K -> 实数)
  证明: fun _ _ => re_le_re

Depends on / 依赖: re_le_re
-/
lemma re_monotone : Monotone (re : K -> Real) :=
  fun _ _ => re_le_re

/--
lemma `inv_pos_of_pos` / 引理 `inv_pos_of_pos`

English:
lemma inv_pos_of_pos
  given: (hz : 0 < z)
  statement: 0 < z⁻¹
  proof: by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx']; rw [← ofReal_inv]; rw [ofReal_pos]
  exact inv_pos_of_pos hx

中文:
引理 inv_pos_of_pos
  条件: (hz : 0 < z)
  结论: 0 < z⁻¹
  证明: by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx']; rw [← ofReal_inv]; rw [ofReal_pos]
  exact inv_pos_of_pos hx
-/
protected lemma inv_pos_of_pos (hz : 0 < z) : 0 < z⁻¹ := by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx']; rw [← ofReal_inv]; rw [ofReal_pos]
  exact inv_pos_of_pos hx

/--
lemma `inv_pos` / 引理 `inv_pos`

English:
lemma inv_pos
  statement: 0 < z⁻¹ ↔ 0 < z
  proof: by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h

中文:
引理 inv_pos
  结论: 0 < z⁻¹ ↔ 0 < z
  证明: by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h
-/
protected lemma inv_pos : 0 < z⁻¹ ↔ 0 < z := by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h

/--
lemma `toStarOrderedRing` / 引理 `toStarOrderedRing`

English:
lemma toStarOrderedRing
  statement: StarOrderedRing K
  proof: StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h => ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?

中文:
引理 toStarOrderedRing
  结论: StarOrdered环 K
  证明: StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h => ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, StarOrderedRing, StarOrderedRing.of_nonneg_iff, add_le_add_iff_left, add_nonneg, add_right_inj, ext_iff, h_add, h_nonneg_iff, le_iff_re_im, map_add, mul_comm, mul_self_nonneg, nonneg_iff, of_nonneg_iff
-/
lemma toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h => ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?_⟩
      rintro ⟨s, rfl⟩
      simp [mul_comm, mul_self_nonneg, add_nonneg])

scoped[ComplexOrder] attribute [instance] RCLike.toStarOrderedRing

/--
lemma `toZeroLEOneClass` / 引理 `toZeroLEOneClass`

English:
lemma toZeroLEOneClass
  statement: ZeroLEOneClass K where
  proof: by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass

中文:
引理 toZeroLEOneClass
  结论: ZeroLEOne类 K where
  证明: by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, le_iff_re_im
-/
lemma toZeroLEOneClass : ZeroLEOneClass K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass

/--
lemma `toIsOrderedAddMonoid` / 引理 `toIsOrderedAddMonoid`

English:
lemma toIsOrderedAddMonoid
  statement: IsOrderedAddMonoid K where
  proof: add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

中文:
引理 toIsOrderedAddMonoid
  结论: 是OrderedAdd幺半群 K where
  证明: add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

Depends on / 依赖: add_le_add_left
-/
lemma toIsOrderedAddMonoid : IsOrderedAddMonoid K where
  add_le_add_left _ _ := add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

/--
lemma `toIsStrictOrderedRing` / 引理 `toIsStrictOrderedRing`

English:
lemma toIsStrictOrderedRing
  statement: IsStrictOrderedRing K
  proof: .of_mul_pos fun z w hz hw => by
    rw [lt_iff_re_im]; rw [map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing

中文:
引理 toIsStrictOrderedRing
  结论: 是StrictOrdered环 K
  证明: .of_mul_pos fun z w hz hw => by
    rw [lt_iff_re_im]; rw [map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing

Depends on / 依赖: lt_iff_re_im, map_zero, mul_im, mul_pos, mul_re, of_mul_pos
-/
lemma toIsStrictOrderedRing : IsStrictOrderedRing K :=
  .of_mul_pos fun z w hz hw => by
    rw [lt_iff_re_im]; rw [map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing

/--
lemma `toPosMulReflectLT` / 引理 `toPosMulReflectLT`

English:
lemma toPosMulReflectLT
  statement: PosMulReflectLT K where
  proof: by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im]; rw [map_zero]; rw [map_zero]; rw [eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, 

中文:
引理 toPosMulReflectLT
  结论: 正乘反映严格偏序 K where
  证明: by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im]; rw [map_zero]; rw [map_zero]; rw [eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, 

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, RCLike.lt_iff_re_im, add_zero, eq_comm, is_real_TFAE, le_iff_re_im, lt_iff_re_im, lt_of_mul_lt_mul_of_nonneg_left, map_zero, mul_eq_mul_left_iff, mul_im, mul_re, ofReal_im, ofReal_re, resolve_right, sub_zero, zero_mul
-/
lemma toPosMulReflectLT : PosMulReflectLT K where
  elim := by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im]; rw [map_zero]; rw [map_zero]; rw [eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, mul_eq_mul_left_iff] at hyz ⊢
refine ⟨lt_of_mul_lt_mul_of_nonneg_left hyz.1 by simpa using hx, hyz.2.resolve_right ?_⟩
    rintro rfl
    simp at hyz

scoped[ComplexOrder] attribute [instance] RCLike.toPosMulReflectLT

/--
theorem `toIsStrictOrderedModule` / 定理 `toIsStrictOrderedModule`

English:
theorem toIsStrictOrderedModule
  statement: IsStrictOrderedModule Real K where
  proof: by
    simpa [RCLike.lt_iff_re_im (K := K), smul_re, smul_im, hr, hr.ne'] using hab
  smul_lt_smul_of_pos_right a ha r₁ r₂ hr := by
    obtain ⟨hare, haim⟩ := RCLike.lt_iff_re_im.1 ha
    simp_all [RCLike.lt_iff_re_im (K := K), smul_re, smul_im]

scoped[ComplexOrder] attribute [instance] RCLike.toIs

中文:
定理 toIsStrictOrderedModule
  结论: 是StrictOrdered模 实数 K where
  证明: by
    simpa [RCLike.lt_iff_re_im (K := K), smul_re, smul_im, hr, hr.ne'] using hab
  smul_lt_smul_of_pos_right a ha r₁ r₂ hr := by
    obtain ⟨hare, haim⟩ := RCLike.lt_iff_re_im.1 ha
    simp_all [RCLike.lt_iff_re_im (K := K), smul_re, smul_im]

scoped[ComplexOrder] attribute [instance] RCLike.toIs

Depends on / 依赖: RCLike, RCLike.lt_iff_re_im, hr.ne, lt_iff_re_im, smul_im, smul_lt_smul_of_pos_right, smul_re
-/
theorem toIsStrictOrderedModule : IsStrictOrderedModule Real K where
  smul_lt_smul_of_pos_left r hr a b hab := by
    simpa [RCLike.lt_iff_re_im (K := K), smul_re, smul_im, hr, hr.ne'] using hab
  smul_lt_smul_of_pos_right a ha r₁ r₂ hr := by
    obtain ⟨hare, haim⟩ := RCLike.lt_iff_re_im.1 ha
    simp_all [RCLike.lt_iff_re_im (K := K), smul_re, smul_im]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedModule

/--
theorem `ofReal_mul_pos_iff` / 定理 `ofReal_mul_pos_iff`

English:
theorem ofReal_mul_pos_iff
  given: (x : Real) (z : K)
  proof: by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, 

中文:
定理 of实数_mul_pos_iff
  条件: (x : 实数) (z : K)
  证明: by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, 

Depends on / 依赖: false_and, false_or, hx.ne, im_ofReal_mul, lt_self_iff_false, lt_trichotomy, mul_eq_zero, mul_pos_iff, neg_iff, not_lt_of_gt, or_false, pos_iff, re_ofReal_mul, true_and, zero_mul
-/
theorem ofReal_mul_pos_iff (x : Real) (z : K) :
    0 < x * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z) := by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, false_or]
  · simp only [mul_pos_iff, hx, true_and, not_lt_of_gt hx, false_and, or_false, mul_eq_zero,
      hx.ne', false_or]

/--
theorem `ofReal_mul_neg_iff` / 定理 `ofReal_mul_neg_iff`

English:
theorem ofReal_mul_neg_iff
  given: (x : Real) (z : K)
  proof: by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)

中文:
定理 of实数_mul_neg_iff
  条件: (x : 实数) (z : K)
  证明: by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)

Depends on / 依赖: mul_neg, neg_neg_iff_pos, neg_pos, ofReal_mul_pos_iff
-/
theorem ofReal_mul_neg_iff (x : Real) (z : K) :
    x * z < 0 ↔ (x < 0 ∧ 0 < z) ∨ (0 < x ∧ z < 0) := by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)

/--
lemma `instPosMulReflectLE` / 引理 `instPosMulReflectLE`

English:
lemma instPosMulReflectLE
  statement: PosMulReflectLE K where
  proof: by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for https://github.com/leanprover/lean4/issues/7717 -/
    beta_reduce at h
    rw [← ha2]; rw [← sub_nonneg]; rw [← mul_sub]; rw [le_iff_lt_or_eq] at h
    rcases 

中文:
引理 instPosMulReflectLE
  结论: 正乘反映偏序 K where
  证明: by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for https://github.com/leanprover/lean4/issues/7717 -/
    beta_reduce at h
    rw [← ha2]; rw [← sub_nonneg]; rw [← mul_sub]; rw [le_iff_lt_or_eq] at h
    rcases 

Depends on / 依赖: False.elim, adaptation_note, beta_reduce, github, github.com, h.rec, h.symm, ha1.ne, issues, le_iff_lt_or_eq, le_of_lt, leanprover, mul_eq_zero_iff_left, mul_sub, not_lt_of_gt, ofReal_mul_pos_iff, ofReal_ne_zero, ofReal_ne_zero.mpr, pos_iff_exists_ofReal, pos_iff_exists_ofReal.mp
-/
lemma instPosMulReflectLE : PosMulReflectLE K where
  elim a b c h := by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for https://github.com/leanprover/lean4/issues/7717 -/
    beta_reduce at h
    rw [← ha2]; rw [← sub_nonneg]; rw [← mul_sub]; rw [le_iff_lt_or_eq] at h
    rcases h with h | h
    · rw [ofReal_mul_pos_iff] at h
exact le_of_lt h.rec (False.elim <| not_lt_of_gt ·.1 ha1) (·.2)
    · exact ((mul_eq_zero_iff_left <| ofReal_ne_zero.mpr ha1.ne').mp h.symm).ge

scoped[ComplexOrder] attribute [instance] RCLike.instPosMulReflectLE

/--
lemma `instMulPosReflectLE` / 引理 `instMulPosReflectLE`

English:
lemma instMulPosReflectLE
  statement: MulPosReflectLE K
  proof: PosMulReflectLE.toMulPosReflectLE

scoped[ComplexOrder] attribute [instance] RCLike.instMulPosReflectLE

中文:
引理 instMulPosReflectLE
  结论: 乘正反映偏序 K
  证明: PosMulReflectLE.toMulPosReflectLE

scoped[ComplexOrder] attribute [instance] RCLike.instMulPosReflectLE

Depends on / 依赖: PosMulReflectLE, PosMulReflectLE.toMulPosReflectLE, toMulPosReflectLE
-/
lemma instMulPosReflectLE : MulPosReflectLE K := PosMulReflectLE.toMulPosReflectLE

scoped[ComplexOrder] attribute [instance] RCLike.instMulPosReflectLE

end Order

section CleanupLemmas

local notation "reR" => @RCLike.re Real _
local notation "imR" => @RCLike.im Real _
local notation "IR" => @RCLike.I Real _
local notation "normSqR" => @RCLike.normSq Real _

@[simp, rclike_simps]
/--
theorem `re_to_real` / 定理 `re_to_real`

English:
theorem re_to_real
  given: {x : Real}
  statement: reR x = x
  proof: rfl

@[simp, rclike_simps]

中文:
定理 re_to_real
  条件: {x : 实数}
  结论: reR x = x
  证明: rfl

@[simp, rclike_simps]
-/
theorem re_to_real {x : Real} : reR x = x :=
  rfl

@[simp, rclike_simps]
/--
theorem `im_to_real` / 定理 `im_to_real`

English:
theorem im_to_real
  given: {x : Real}
  statement: imR x = 0
  proof: rfl

@[rclike_simps]

中文:
定理 im_to_real
  条件: {x : 实数}
  结论: imR x = 0
  证明: rfl

@[rclike_simps]
-/
theorem im_to_real {x : Real} : imR x = 0 :=
  rfl

@[rclike_simps]
/--
theorem `conj_to_real` / 定理 `conj_to_real`

English:
theorem conj_to_real
  given: {x : Real}
  statement: conj x = x
  proof: rfl

@[simp, rclike_simps]

中文:
定理 conj_to_real
  条件: {x : 实数}
  结论: conj x = x
  证明: rfl

@[simp, rclike_simps]
-/
theorem conj_to_real {x : Real} : conj x = x :=
  rfl

@[simp, rclike_simps]
/--
theorem `I_to_real` / 定理 `I_to_real`

English:
theorem I_to_real
  statement: IR = 0
  proof: rfl

@[simp, rclike_simps]

中文:
定理 I_to_real
  结论: IR = 0
  证明: rfl

@[simp, rclike_simps]
-/
theorem I_to_real : IR = 0 :=
  rfl

@[simp, rclike_simps]
/--
theorem `normSq_to_real` / 定理 `normSq_to_real`

English:
theorem normSq_to_real
  given: {x : Real}
  statement: normSq x = x * x
  proof: by simp [RCLike.normSq]

@[simp]

中文:
定理 normSq_to_real
  条件: {x : 实数}
  结论: normSq x = x * x
  证明: by simp [RCLike.normSq]

@[simp]

Depends on / 依赖: RCLike, RCLike.normSq, normSq
-/
theorem normSq_to_real {x : Real} : normSq x = x * x := by simp [RCLike.normSq]

@[simp]
/--
theorem `ofReal_real_eq_id` / 定理 `ofReal_real_eq_id`

English:
theorem ofReal_real_eq_id
  statement: @ofReal Real _ = id
  proof: rfl

中文:
定理 of实数_real_eq_id
  结论: @of实数 实数 _ = id
  证明: rfl

Depends on / 依赖: IsIso.of_groupoid, of_groupoid
-/
theorem ofReal_real_eq_id : @ofReal Real _ = id :=
  rfl

end CleanupLemmas

section LinearMaps

/--
Definition of `reLm` / `reLm` 的定义

English:
definition reLm
  signature: : K ->ₗ[Real] Real
  body: { re with map_smul' := smul_re }

@[simp, rclike_simps]

中文:
定义 reLm
  签名: : K ->ₗ[实数] 实数
  定义体: { re with map_smul' := smul_re }

@[simp, rclike_simps]

Depends on / 依赖: map_smul, smul_re
-/
noncomputable def reLm : K ->ₗ[Real] Real :=
  { re with map_smul' := smul_re }

@[simp, rclike_simps]
/--
theorem `reLm_coe` / 定理 `reLm_coe`

English:
theorem reLm_coe
  statement: (reLm : K -> Real) = re
  proof: rfl

中文:
定理 reLm_coe
  结论: (reLm : K -> 实数) = re
  证明: rfl
-/
theorem reLm_coe : (reLm : K -> Real) = re :=
  rfl

/--
Definition of `reCLM` / `reCLM` 的定义

English:
definition reCLM
  signature: : StrongDual Real K
  body: reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]

中文:
定义 reCLM
  签名: : StrongDual 实数 K
  定义体: reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: HasInvolutiveReverse, Quiver, Quiver.HasInvolutiveReverse, abs_re_le_norm, groupoidHasInvolutiveReverse, mkContinuous, one_mul, reLm.mkContinuous
-/
noncomputable def reCLM : StrongDual Real K :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]
/--
theorem `reCLM_coe` / 定理 `reCLM_coe`

English:
theorem reCLM_coe
  statement: ((reCLM : StrongDual Real K) : K ->ₗ[Real] Real) = reLm
  proof: rfl

@[simp, rclike_simps]

中文:
定理 reCLM_coe
  结论: ((reCLM : StrongDual 实数 K) : K ->ₗ[实数] 实数) = reLm
  证明: rfl

@[simp, rclike_simps]
-/
theorem reCLM_coe : ((reCLM : StrongDual Real K) : K ->ₗ[Real] Real) = reLm :=
  rfl

@[simp, rclike_simps]
/--
theorem `reCLM_apply` / 定理 `reCLM_apply`

English:
theorem reCLM_apply
  statement: ((reCLM : StrongDual Real K) : K -> Real) = re
  proof: rfl

@[continuity, fun_prop]

中文:
定理 reCLM_apply
  结论: ((reCLM : StrongDual 实数 K) : K -> 实数) = re
  证明: rfl

@[continuity, fun_prop]
-/
theorem reCLM_apply : ((reCLM : StrongDual Real K) : K -> Real) = re :=
  rfl

@[continuity, fun_prop]
/--
theorem `continuous_re` / 定理 `continuous_re`

English:
theorem continuous_re
  statement: Continuous (re : K -> Real)
  proof: reCLM.continuous

中文:
定理 continuous_re
  结论: 连续 (re : K -> 实数)
  证明: reCLM.continuous

Depends on / 依赖: continuous, reCLM.continuous
-/
theorem continuous_re : Continuous (re : K -> Real) :=
  reCLM.continuous

/--
Definition of `imLm` / `imLm` 的定义

English:
definition imLm
  signature: : K ->ₗ[Real] Real
  body: { im with map_smul' := smul_im }

@[simp, rclike_simps]

中文:
定义 imLm
  签名: : K ->ₗ[实数] 实数
  定义体: { im with map_smul' := smul_im }

@[simp, rclike_simps]

Depends on / 依赖: map_smul, smul_im
-/
noncomputable def imLm : K ->ₗ[Real] Real :=
  { im with map_smul' := smul_im }

@[simp, rclike_simps]
/--
theorem `imLm_coe` / 定理 `imLm_coe`

English:
theorem imLm_coe
  statement: (imLm : K -> Real) = im
  proof: rfl

中文:
定理 imLm_coe
  结论: (imLm : K -> 实数) = im
  证明: rfl
-/
theorem imLm_coe : (imLm : K -> Real) = im :=
  rfl

/--
Definition of `imCLM` / `imCLM` 的定义

English:
definition imCLM
  signature: : StrongDual Real K
  body: imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]

中文:
定义 imCLM
  签名: : StrongDual 实数 K
  定义体: imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]

Depends on / 依赖: abs_im_le_norm, imLm.mkContinuous, mkContinuous, one_mul
-/
noncomputable def imCLM : StrongDual Real K :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]
/--
theorem `imCLM_coe` / 定理 `imCLM_coe`

English:
theorem imCLM_coe
  statement: ((imCLM : StrongDual Real K) : K ->ₗ[Real] Real) = imLm
  proof: rfl

@[simp, rclike_simps]

中文:
定理 imCLM_coe
  结论: ((imCLM : StrongDual 实数 K) : K ->ₗ[实数] 实数) = imLm
  证明: rfl

@[simp, rclike_simps]
-/
theorem imCLM_coe : ((imCLM : StrongDual Real K) : K ->ₗ[Real] Real) = imLm :=
  rfl

@[simp, rclike_simps]
/--
theorem `imCLM_apply` / 定理 `imCLM_apply`

English:
theorem imCLM_apply
  statement: ((imCLM : StrongDual Real K) : K -> Real) = im
  proof: rfl

@[continuity, fun_prop]

中文:
定理 imCLM_apply
  结论: ((imCLM : StrongDual 实数 K) : K -> 实数) = im
  证明: rfl

@[continuity, fun_prop]
-/
theorem imCLM_apply : ((imCLM : StrongDual Real K) : K -> Real) = im :=
  rfl

@[continuity, fun_prop]
/--
theorem `continuous_im` / 定理 `continuous_im`

English:
theorem continuous_im
  statement: Continuous (im : K -> Real)
  proof: imCLM.continuous

中文:
定理 continuous_im
  结论: 连续 (im : K -> 实数)
  证明: imCLM.continuous

Depends on / 依赖: continuous, imCLM.continuous
-/
theorem continuous_im : Continuous (im : K -> Real) :=
  imCLM.continuous

/--
Definition of `conjAe` / `conjAe` 的定义

English:
definition conjAe
  signature: : K ≃ₐ[Real] K
  body: { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, rclike_simps]

中文:
定义 conjAe
  签名: : K ≃ₐ[实数] K
  定义体: { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, rclike_simps]

Depends on / 依赖: commutes, conj_conj, conj_ofReal, invFun, left_inv, right_inv
-/
def conjAe : K ≃ₐ[Real] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, rclike_simps]
/--
theorem `conjAe_coe` / 定理 `conjAe_coe`

English:
theorem conjAe_coe
  statement: (conjAe : K -> K) = conj
  proof: rfl

中文:
定理 conjAe_coe
  结论: (conjAe : K -> K) = conj
  证明: rfl
-/
theorem conjAe_coe : (conjAe : K -> K) = conj :=
  rfl

/--
Definition of `conjLIE` / `conjLIE` 的定义

English:
definition conjLIE
  signature: : K ≃ₗᵢ[Real] K
  body: ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]

中文:
定义 conjLIE
  签名: : K ≃ₗᵢ[实数] K
  定义体: ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]

Depends on / 依赖: conjAe, conjAe.toLinearEquiv, norm_conj, toLinearEquiv
-/
noncomputable def conjLIE : K ≃ₗᵢ[Real] K :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]
/--
theorem `conjLIE_apply` / 定理 `conjLIE_apply`

English:
theorem conjLIE_apply
  statement: (conjLIE : K -> K) = conj
  proof: rfl

中文:
定理 conjLIE_apply
  结论: (conjLIE : K -> K) = conj
  证明: rfl
-/
theorem conjLIE_apply : (conjLIE : K -> K) = conj :=
  rfl

/--
Definition of `conjCLE` / `conjCLE` 的定义

English:
definition conjCLE
  signature: : K ≃L[Real] K
  body: @conjLIE K _

@[simp, rclike_simps]

中文:
定义 conjCLE
  签名: : K ≃L[实数] K
  定义体: @conjLIE K _

@[simp, rclike_simps]

Depends on / 依赖: conjLIE
-/
noncomputable def conjCLE : K ≃L[Real] K :=
  @conjLIE K _

@[simp, rclike_simps]
/--
theorem `conjCLE_coe` / 定理 `conjCLE_coe`

English:
theorem conjCLE_coe
  statement: (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv
  proof: rfl

@[simp, rclike_simps]

中文:
定理 conjCLE_coe
  结论: (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv
  证明: rfl

@[simp, rclike_simps]
-/
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, rclike_simps]
/--
theorem `conjCLE_apply` / 定理 `conjCLE_apply`

English:
theorem conjCLE_apply
  statement: (conjCLE : K -> K) = conj
  proof: rfl

中文:
定理 conjCLE_apply
  结论: (conjCLE : K -> K) = conj
  证明: rfl
-/
theorem conjCLE_apply : (conjCLE : K -> K) = conj :=
  rfl

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity]
/--
theorem `continuous_conj` / 定理 `continuous_conj`

English:
theorem continuous_conj
  statement: Continuous (conj : K -> K)
  proof: continuous_star

中文:
定理 continuous_conj
  结论: 连续 (conj : K -> K)
  证明: continuous_star

Depends on / 依赖: continuous_star
-/
theorem continuous_conj : Continuous (conj : K -> K) :=
  continuous_star

/--
Definition of `ofRealAm` / `ofRealAm` 的定义

English:
definition ofRealAm
  signature: : Real ->ₐ[Real] K
  body: Algebra.ofId Real K

@[simp, rclike_simps]

中文:
定义 of实数Am
  签名: : 实数 ->ₐ[实数] K
  定义体: Algebra.ofId Real K

@[simp, rclike_simps]

Depends on / 依赖: Algebra, Algebra.ofId
-/
noncomputable def ofRealAm : Real ->ₐ[Real] K :=
  Algebra.ofId Real K

@[simp, rclike_simps]
/--
theorem `ofRealAm_coe` / 定理 `ofRealAm_coe`

English:
theorem ofRealAm_coe
  statement: (ofRealAm : Real -> K) = ofReal
  proof: rfl

中文:
定理 of实数Am_coe
  结论: (of实数Am : 实数 -> K) = of实数
  证明: rfl
-/
theorem ofRealAm_coe : (ofRealAm : Real -> K) = ofReal :=
  rfl

variable (K) in
/--
Definition of `ofRealStarAlgHom` / `ofRealStarAlgHom` 的定义

English:
definition ofRealStarAlgHom
  signature: : Real ->⋆ₐ[Real] K
  body: .ofId Real K

中文:
定义 of实数StarAlgHom
  签名: : 实数 ->⋆ₐ[实数] K
  定义体: .ofId Real K
-/
noncomputable def ofRealStarAlgHom : Real ->⋆ₐ[Real] K := .ofId Real K

/--
theorem `coe_ofRealStarAlgHom` / 定理 `coe_ofRealStarAlgHom`

English:
theorem coe_ofRealStarAlgHom
  statement: (ofRealStarAlgHom K : Real -> K) = ofReal
  proof: rfl

中文:
定理 coe_of实数StarAlgHom
  结论: (of实数StarAlgHom K : 实数 -> K) = of实数
  证明: rfl
-/
@[simp] theorem coe_ofRealStarAlgHom : (ofRealStarAlgHom K : Real -> K) = ofReal := rfl
/--
lemma `toAlgHom_ofRealStarAlgHom` / 引理 `toAlgHom_ofRealStarAlgHom`

English:
lemma toAlgHom_ofRealStarAlgHom
  statement: (ofRealStarAlgHom K).toAlgHom = ofRealAm
  proof: rfl

中文:
引理 toAlgHom_of实数StarAlgHom
  结论: (of实数StarAlgHom K).toAlgHom = of实数Am
  证明: rfl
-/
@[simp] lemma toAlgHom_ofRealStarAlgHom : (ofRealStarAlgHom K).toAlgHom = ofRealAm := rfl

/--
Definition of `ofRealLI` / `ofRealLI` 的定义

English:
definition ofRealLI
  signature: : Real ->ₗᵢ[Real] K where
  body: ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]

中文:
定义 of实数LI
  签名: : 实数 ->ₗᵢ[实数] K where
  定义体: ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]

Depends on / 依赖: ofRealAm, ofRealAm.toLinearMap, toLinearMap
-/
noncomputable def ofRealLI : Real ->ₗᵢ[Real] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]
/--
theorem `ofRealLI_apply` / 定理 `ofRealLI_apply`

English:
theorem ofRealLI_apply
  statement: (ofRealLI : Real -> K) = ofReal
  proof: rfl

中文:
定理 of实数LI_apply
  结论: (of实数LI : 实数 -> K) = of实数
  证明: rfl
-/
theorem ofRealLI_apply : (ofRealLI : Real -> K) = ofReal :=
  rfl

/--
Definition of `ofRealCLM` / `ofRealCLM` 的定义

English:
definition ofRealCLM
  signature: : Real ->L[Real] K
  body: ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]

中文:
定义 of实数CLM
  签名: : 实数 ->L[实数] K
  定义体: ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]

Depends on / 依赖: ofRealLI, ofRealLI.toContinuousLinearMap, toContinuousLinearMap
-/
noncomputable def ofRealCLM : Real ->L[Real] K :=
  ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]
/--
theorem `ofRealCLM_coe` / 定理 `ofRealCLM_coe`

English:
theorem ofRealCLM_coe
  statement: (@ofRealCLM K _ : Real ->ₗ[Real] K) = ofRealAm.toLinearMap
  proof: rfl

@[simp, rclike_simps]

中文:
定理 of实数CLM_coe
  结论: (@of实数CLM K _ : 实数 ->ₗ[实数] K) = of实数Am.toLinearMap
  证明: rfl

@[simp, rclike_simps]
-/
theorem ofRealCLM_coe : (@ofRealCLM K _ : Real ->ₗ[Real] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, rclike_simps]
/--
theorem `ofRealCLM_apply` / 定理 `ofRealCLM_apply`

English:
theorem ofRealCLM_apply
  statement: (ofRealCLM : Real -> K) = ofReal
  proof: rfl

@[continuity, fun_prop]

中文:
定理 of实数CLM_apply
  结论: (of实数CLM : 实数 -> K) = of实数
  证明: rfl

@[continuity, fun_prop]
-/
theorem ofRealCLM_apply : (ofRealCLM : Real -> K) = ofReal :=
  rfl

@[continuity, fun_prop]
/--
theorem `continuous_ofReal` / 定理 `continuous_ofReal`

English:
theorem continuous_ofReal
  statement: Continuous (ofReal : Real -> K)
  proof: ofRealLI.continuous

@[continuity]

中文:
定理 continuous_of实数
  结论: 连续 (of实数 : 实数 -> K)
  证明: ofRealLI.continuous

@[continuity]

Depends on / 依赖: continuous, ofRealLI, ofRealLI.continuous
-/
theorem continuous_ofReal : Continuous (ofReal : Real -> K) :=
  ofRealLI.continuous

@[continuity]
/--
theorem `continuous_normSq` / 定理 `continuous_normSq`

English:
theorem continuous_normSq
  statement: Continuous (normSq : K -> Real)
  proof: (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

中文:
定理 continuous_normSq
  结论: 连续 (normSq : K -> 实数)
  证明: (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

Depends on / 依赖: continuous_im, continuous_im.mul, continuous_re, continuous_re.mul
-/
theorem continuous_normSq : Continuous (normSq : K -> Real) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

/--
theorem `lipschitzWith_ofReal` / 定理 `lipschitzWith_ofReal`

English:
theorem lipschitzWith_ofReal
  statement: LipschitzWith 1 (ofReal : Real -> K)
  proof: ofRealLI.lipschitz

中文:
定理 lipschitzWith_of实数
  结论: LipschitzWith 1 (of实数 : 实数 -> K)
  证明: ofRealLI.lipschitz

Depends on / 依赖: lipschitz, ofRealLI, ofRealLI.lipschitz
-/
theorem lipschitzWith_ofReal : LipschitzWith 1 (ofReal : Real -> K) :=
  ofRealLI.lipschitz

/--
lemma `lipschitzWith_re` / 引理 `lipschitzWith_re`

English:
lemma lipschitzWith_re
  statement: LipschitzWith 1 (re (K := K))
  proof: by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [map_sub re x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

中文:
引理 lipschitzWith_re
  结论: LipschitzWith 1 (re (K := K))
  证明: by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [map_sub re x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

Depends on / 依赖: ENNReal, ENNReal.coe_one, coe_one, edist_eq_enorm_sub, enorm_le_iff_norm_le, map_sub, norm_re_le_norm, one_mul
-/
lemma lipschitzWith_re : LipschitzWith 1 (re (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [map_sub re x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

/--
lemma `lipschitzWith_im` / 引理 `lipschitzWith_im`

English:
lemma lipschitzWith_im
  statement: LipschitzWith 1 (im (K := K))
  proof: by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

中文:
引理 lipschitzWith_im
  结论: LipschitzWith 1 (im (K := K))
  证明: by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

Depends on / 依赖: ENNReal, ENNReal.coe_one, coe_one, edist_eq_enorm_sub, enorm_le_iff_norm_le, map_sub, norm_im_le_norm, one_mul
-/
lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
  _ <= ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (𝕜 𝕜' : Type*) [RCLike 𝕜] [RCLike 𝕜']
  body: re x + im x * (I : 𝕜')
  map_add' _ _ := by simp only [map_add, add_mul]; ring
  map_smul' _ _ := by simp [real_smul_eq_coe_mul, mul_assoc]

中文:
定义 map
  签名: (𝕜 𝕜' : 类型) [RCLike 𝕜] [RCLike 𝕜']
  定义体: re x + im x * (I : 𝕜')
  map_add' _ _ := by simp only [map_add, add_mul]; ring
  map_smul' _ _ := by simp [real_smul_eq_coe_mul, mul_assoc]
-/
@[simps] def map (𝕜 𝕜' : Type*) [RCLike 𝕜] [RCLike 𝕜'] : 𝕜 ->L[Real] 𝕜' where
  toFun x := re x + im x * (I : 𝕜')
  map_add' _ _ := by simp only [map_add, add_mul]; ring
  map_smul' _ _ := by simp [real_smul_eq_coe_mul, mul_assoc]

/--
theorem `map_same_eq_id` / 定理 `map_same_eq_id`

English:
theorem map_same_eq_id
  statement: map K K = .id Real K
  proof: by ext; simp

中文:
定理 map_same_eq_id
  结论: map K K = .id 实数 K
  证明: by ext; simp
-/
@[simp] theorem map_same_eq_id : map K K = .id Real K := by ext; simp

/--
theorem `map_to_real` / 定理 `map_to_real`

English:
theorem map_to_real
  statement: map K Real = reCLM
  proof: by
  ext; simp only [map_apply, I, mul_zero, add_zero]; rfl

中文:
定理 map_to_real
  结论: map K 实数 = reCLM
  证明: by
  ext; simp only [map_apply, I, mul_zero, add_zero]; rfl
-/
@[simp] theorem map_to_real : map K Real = reCLM := by
  ext; simp only [map_apply, I, mul_zero, add_zero]; rfl

/--
theorem `map_from_real` / 定理 `map_from_real`

English:
theorem map_from_real
  statement: map Real K = ofRealCLM
  proof: by ext; simp

中文:
定理 map_from_real
  结论: map 实数 K = of实数CLM
  证明: by ext; simp
-/
@[simp] theorem map_from_real : map Real K = ofRealCLM := by ext; simp

open scoped ComplexOrder in
/--
lemma `instOrderClosedTopology` / 引理 `instOrderClosedTopology`

English:
lemma instOrderClosedTopology
  statement: OrderClosedTopology K where
  proof: by
    conv in _ <= _ => rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> fun_prop

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosedTopology

中文:
引理 instOrderClosedTopology
  结论: OrderClosed拓扑 K where
  证明: by
    conv in _ <= _ => rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> fun_prop

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosedTopology

Depends on / 依赖: IsClosed, IsClosed.inter, RCLike, RCLike.le_iff_re_im, Set.ofPred_and, fun_prop, isClosed_eq, isClosed_le, le_iff_re_im, ofPred_and, simp_rw
-/
lemma instOrderClosedTopology : OrderClosedTopology K where
  isClosed_le' := by
    conv in _ <= _ => rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> fun_prop

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosedTopology

end LinearMaps

/-!
### ℝ-dependent results

Here we gather results that depend on whether `K` is `ℝ`.
-/
section CaseSpecific

/--
lemma `im_eq_zero` / 引理 `im_eq_zero`

English:
lemma im_eq_zero
  given: (h : I = (0 : K)) (z : K)
  statement: im z = 0
  proof: by
  rw [← re_add_im z]; rw [h]
  simp

中文:
引理 im_eq_zero
  条件: (h : I = (0 : K)) (z : K)
  结论: im z = 0
  证明: by
  rw [← re_add_im z]; rw [h]
  simp

Depends on / 依赖: re_add_im
-/
lemma im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0 := by
  rw [← re_add_im z]; rw [h]
  simp

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when `RCLike.I = 0`. -/
@[simps]
/--
Definition of `realRingEquiv` / `realRingEquiv` 的定义

English:
definition realRingEquiv
  signature: (h : I = (0 : K))
  body: re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]

中文:
定义 realRingEquiv
  签名: (h : I = (0 : K))
  定义体: re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]
-/
def realRingEquiv (h : I = (0 : K)) : K ≃+* Real where
  toFun := re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when
`RCLike.I = 0`. -/
@[simps]
/--
Definition of `realLinearIsometryEquiv` / `realLinearIsometryEquiv` 的定义

English:
definition realLinearIsometryEquiv
  signature: (h : I = (0 : K))
  body: smul_re
  norm_map' z := by rw [← re_add_im z]; simp [-re_add_im, h]
  __ := realRingEquiv h

中文:
定义 realLinearIsometryEquiv
  签名: (h : I = (0 : K))
  定义体: smul_re
  norm_map' z := by rw [← re_add_im z]; simp [-re_add_im, h]
  __ := realRingEquiv h

Depends on / 依赖: smul_re
-/
noncomputable def realLinearIsometryEquiv (h : I = (0 : K)) : K ≃ₗᵢ[Real] Real where
  map_smul' := smul_re
  norm_map' z := by rw [← re_add_im z]; simp [-re_add_im, h]
  __ := realRingEquiv h

end CaseSpecific

/--
lemma `norm_le_im_iff_eq_I_mul_norm` / 引理 `norm_le_im_iff_eq_I_mul_norm`

English:
lemma norm_le_im_iff_eq_I_mul_norm
  given: {z : K}
  proof: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) != 0 := fun _ => by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert! norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero th

中文:
引理 norm_le_im_iff_eq_I_mul_norm
  条件: {z : K}
  证明: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) != 0 := fun _ => by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert! norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero th

Depends on / 依赖: I_eq_zero_or_im_I_eq_one, I_mul_I_of_nonzero, all_goals, convert, im_eq_zero, mul_assoc, mul_right_inj, neg_mul, neg_ne_zero, neg_ne_zero.mpr, norm_I_of_ne_zero, norm_le_re_iff_eq_norm
-/
lemma norm_le_im_iff_eq_I_mul_norm {z : K} :
    ‖z‖ <= im z ↔ z = I * ‖z‖ := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) != 0 := fun _ => by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert! norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero this, norm_I_of_ne_zero this]

/--
lemma `im_le_neg_norm_iff_eq_neg_I_mul_norm` / 引理 `im_le_neg_norm_iff_eq_neg_I_mul_norm`

English:
lemma im_le_neg_norm_iff_eq_neg_I_mul_norm
  given: {z : K}
  proof: by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

中文:
引理 im_le_neg_norm_iff_eq_neg_I_mul_norm
  条件: {z : K}
  证明: by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

Depends on / 依赖: le_neg, neg_eq_iff_eq_neg, norm_le_im_iff_eq_I_mul_norm
-/
lemma im_le_neg_norm_iff_eq_neg_I_mul_norm {z : K} :
    im z <= -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

end RCLike

namespace AddChar
variable {G : Type*} [Finite G]

/--
lemma `inv_apply_eq_conj` / 引理 `inv_apply_eq_conj`

English:
lemma inv_apply_eq_conj
  given: [AddLeftCancelMonoid G] (ψ : AddChar G K) (x : G)
  statement: (ψ x)⁻¹ = conj (ψ x)
  proof: RCLike.inv_eq_conj norm_apply _ _

中文:
引理 inv_apply_eq_conj
  条件: [加法左消去幺半群 G] (ψ : 加法特征 G K) (x : G)
  结论: (ψ x)⁻¹ = conj (ψ x)
  证明: RCLike.inv_eq_conj norm_apply _ _

Depends on / 依赖: RCLike, RCLike.inv_eq_conj, inv_eq_conj, norm_apply
-/
lemma inv_apply_eq_conj [AddLeftCancelMonoid G] (ψ : AddChar G K) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
RCLike.inv_eq_conj norm_apply _ _

/--
lemma `map_neg_eq_conj` / 引理 `map_neg_eq_conj`

English:
lemma map_neg_eq_conj
  given: [AddCommGroup G] (ψ : AddChar G K) (x : G)
  statement: ψ (-x) = conj (ψ x)
  proof: by
  rw [map_neg_eq_inv]; rw [inv_apply_eq_conj]

中文:
引理 map_neg_eq_conj
  条件: [加法交换群 G] (ψ : 加法特征 G K) (x : G)
  结论: ψ (-x) = conj (ψ x)
  证明: by
  rw [map_neg_eq_inv]; rw [inv_apply_eq_conj]

Depends on / 依赖: inv_apply_eq_conj, map_neg_eq_inv
-/
lemma map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv]; rw [inv_apply_eq_conj]

end AddChar

section

/--
Definition of `IsRCLikeNormedField` / `IsRCLikeNormedField` 的定义

English:
class IsRCLikeNormedField
  parameters: (𝕜 : Type*) [hk : NormedField 𝕜]
  axioms and operations (1):
    - out : exists h : RCLike 𝕜, hk = h.toNormedField

中文:
类 是RCLikeNormedField
  参数: (𝕜 : 类型) [hk : 赋范域 𝕜]
  公理与运算 (1 个):
    - out : 存在 h : RCLike 𝕜, hk = h.toNormedField
-/
class IsRCLikeNormedField (𝕜 : Type*) [hk : NormedField 𝕜] : Prop where
  out : exists h : RCLike 𝕜, hk = h.toNormedField

instance (priority := 100) (𝕜 : Type*) [h : RCLike 𝕜] : IsRCLikeNormedField 𝕜 := ⟨⟨h, rfl⟩⟩

/-- A copy of an `RCLike` field in which the `NormedField` field is adjusted to be become defeq
to a propeq one. -/
@[instance_reducible]
/--
Definition of `RCLike.copy_of_normedField` / `RCLike.copy_of_normedField` 的定义

English:
definition RCLike.copy_of_normedField
  signature: {𝕜 : Type*} (h : RCLike 𝕜) (hk : NormedField 𝕜)
  body: hk
  toPartialOrder := h.toPartialOrder
  toDecidableEq := h.toDecidableEq
  complete := by subst h''; exact h.complete
  lt_norm_lt := by subst h''; exact h.lt_norm_lt
  -- star fields
  star := (@StarMul.toInvolutiveStar _ (_) (@StarRing.toStarMul _ (_) h.toStarRing)).star
  star_involutive := by 

中文:
定义 RCLike.copy_of_normedField
  签名: {𝕜 : 类型} (h : RCLike 𝕜) (hk : 赋范域 𝕜)
  定义体: hk
  toPartialOrder := h.toPartialOrder
  toDecidableEq := h.toDecidableEq
  complete := by subst h''; exact h.complete
  lt_norm_lt := by subst h''; exact h.lt_norm_lt
  -- star fields
  star := (@StarMul.toInvolutiveStar _ (_) (@StarRing.toStarMul _ (_) h.toStarRing)).star
  star_involutive := by 
-/
noncomputable def RCLike.copy_of_normedField {𝕜 : Type*} (h : RCLike 𝕜) (hk : NormedField 𝕜)
    (h'' : hk = h.toNormedField) : RCLike 𝕜 where
  __ := hk
  toPartialOrder := h.toPartialOrder
  toDecidableEq := h.toDecidableEq
  complete := by subst h''; exact h.complete
  lt_norm_lt := by subst h''; exact h.lt_norm_lt
  -- star fields
  star := (@StarMul.toInvolutiveStar _ (_) (@StarRing.toStarMul _ (_) h.toStarRing)).star
  star_involutive := by subst h''; exact h.star_involutive
  star_mul := by subst h''; exact h.star_mul
  star_add := by subst h''; exact h.star_add
  -- algebra fields
  smul := (@Algebra.toSMul _ _ _ (_) (@NormedAlgebra.toAlgebra _ _ _ (_) h.toNormedAlgebra)).smul
  algebraMap :=
  { toFun := @Algebra.algebraMap _ _ _ (_) (@NormedAlgebra.toAlgebra _ _ _ (_) h.toNormedAlgebra)
    map_one' := by subst h''; exact h.algebraMap.map_one'
    map_mul' := by subst h''; exact h.algebraMap.map_mul'
    map_zero' := by subst h''; exact h.algebraMap.map_zero'
    map_add' := by subst h''; exact h.algebraMap.map_add' }
  commutes' := by subst h''; exact h.commutes'
  smul_def' := by subst h''; exact h.smul_def'
  norm_smul_le := by subst h''; exact h.norm_smul_le
  -- RCLike fields
  re := by subst h''; exact h.re
  im := by subst h''; exact h.im
  I := h.I
  I_re_ax := by subst h''; exact h.I_re_ax
  I_mul_I_ax := by subst h''; exact h.I_mul_I_ax
  re_add_im_ax := by subst h''; exact h.re_add_im_ax
  ofReal_re_ax := by subst h''; exact h.ofReal_re_ax
  ofReal_im_ax := by subst h''; exact h.ofReal_im_ax
  mul_re_ax := by subst h''; exact h.mul_re_ax
  mul_im_ax := by subst h''; exact h.mul_im_ax
  conj_re_ax := by subst h''; exact h.conj_re_ax
  conj_im_ax := by subst h''; exact h.conj_im_ax
  conj_I_ax := by subst h''; exact h.conj_I_ax
  norm_sq_eq_def_ax := by subst h''; exact h.norm_sq_eq_def_ax
  mul_im_I_ax := by subst h''; exact h.mul_im_I_ax
  le_iff_re_im := by subst h''; exact h.le_iff_re_im

/-- Given a normed field `𝕜` satisfying `IsRCLikeNormedField 𝕜`, build an associated `RCLike 𝕜`
structure on `𝕜` which is definitionally compatible with the given normed field structure. -/
@[instance_reducible]
/--
Definition of `IsRCLikeNormedField.rclike` / `IsRCLikeNormedField.rclike` 的定义

English:
definition IsRCLikeNormedField.rclike
  signature: (𝕜 : Type*)
  body: by
  choose p hp using h.out
  exact p.copy_of_normedField hk hp

中文:
定义 是RCLikeNormedField.rclike
  签名: (𝕜 : 类型)
  定义体: by
  choose p hp using h.out
  exact p.copy_of_normedField hk hp

Depends on / 依赖: copy_of_normedField, h.out, p.copy_of_normedField
-/
noncomputable def IsRCLikeNormedField.rclike (𝕜 : Type*)
    [hk : NormedField 𝕜] [h : IsRCLikeNormedField 𝕜] : RCLike 𝕜 := by
  choose p hp using h.out
  exact p.copy_of_normedField hk hp

end

namespace LinearIsometryEquiv
variable {𝕜 V W G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [Module 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (unitary 𝕜) (V ≃ₗᵢ[𝕜] W)
  body: { __ := Unitary.toUnits α • e.toLinearEquiv
    norm_map' _ := by simp [norm_smul] }

中文:
实例 :
  签名: 标量乘法 (unitary 𝕜) (V ≃ₗᵢ[𝕜] W)
  定义体: { __ := Unitary.toUnits α • e.toLinearEquiv
    norm_map' _ := by simp [norm_smul] }

Depends on / 依赖: Unitary, Unitary.toUnits, e.toLinearEquiv, norm_map, norm_smul, toLinearEquiv, toUnits
-/
instance : SMul (unitary 𝕜) (V ≃ₗᵢ[𝕜] W) where smul α e :=
  { __ := Unitary.toUnits α • e.toLinearEquiv
    norm_map' _ := by simp [norm_smul] }

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V)
  proof: rfl

中文:
定理 smul_apply
  条件: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V)
  证明: rfl
-/
@[simp] theorem smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V) :
    (α • e) x = (α : 𝕜) • e x := rfl

/--
theorem `symm_smul_apply` / 定理 `symm_smul_apply`

English:
theorem symm_smul_apply
  given: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : W)
  proof: rfl

中文:
定理 symm_smul_apply
  条件: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : W)
  证明: rfl
-/
theorem symm_smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : W) :
    (α • e).symm x = (↑α⁻¹ : 𝕜) • e.symm x := rfl

/--
theorem `symm_units_smul` / 定理 `symm_units_smul`

English:
theorem symm_units_smul
  given: (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  proof: by ext; simp [symm_smul_apply]

中文:
定理 symm_units_smul
  条件: (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  证明: by ext; simp [symm_smul_apply]
-/
@[simp] theorem symm_units_smul (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).symm = α⁻¹ • e.symm := by ext; simp [symm_smul_apply]

/--
theorem `toLinearEquiv_smul` / 定理 `toLinearEquiv_smul`

English:
theorem toLinearEquiv_smul
  given: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  proof: rfl

中文:
定理 toLinearEquiv_smul
  条件: (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  证明: rfl
-/
@[simp] theorem toLinearEquiv_smul (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).toLinearEquiv = Unitary.toUnits α • e.toLinearEquiv := rfl

/--
theorem `toContinuousLinearEquiv_smul` / 定理 `toContinuousLinearEquiv_smul`

English:
theorem toContinuousLinearEquiv_smul
  given: (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  proof: rfl

中文:
定理 toContinuousLinearEquiv_smul
  条件: (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜)
  证明: rfl
-/
@[simp] theorem toContinuousLinearEquiv_smul (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).toContinuousLinearEquiv = Unitary.toUnits α • e.toContinuousLinearEquiv := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_trans` / 定理 `smul_trans`

English:
theorem smul_trans
  given: (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W)
  proof: by ext; simp

中文:
定理 smul_trans
  条件: (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W)
  证明: by ext; simp
-/
theorem smul_trans (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) :
    (α • e).trans f = α • (e.trans f) := by ext; simp

/--
theorem `trans_smul` / 定理 `trans_smul`

English:
theorem trans_smul
  given: (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W)
  proof: by ext; simp

中文:
定理 trans_smul
  条件: (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W)
  证明: by ext; simp
-/
theorem trans_smul (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

end LinearIsometryEquiv
