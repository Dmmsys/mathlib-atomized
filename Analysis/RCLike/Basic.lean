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

local notation "𝓚" => algebraMap ℝ _

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
/-
**RCLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：semiOutParam (Type u_1) → Type u_1
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This typeclass captures properties shared by ℝ and ℂ, with an API that closely m
atches that of ℂ.
-/
class RCLike (K : semiOutParam Type*) extends DenselyNormedField K, StarRing K,
    NormedAlgebra ℝ K, CompleteSpace K where
  /-- The real part as an additive monoid homomorphism -/
  re : K →+ ℝ
  /-- The imaginary part as an additive monoid homomorphism -/
  im : K →+ ℝ
  /-- Imaginary unit in `K`. Meant to be set to `0` for `K = ℝ`. -/
  I : K
  I_re_ax : re I = 0
  I_mul_I_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : ∀ z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
  ofReal_re_ax : ∀ r : ℝ, re (𝓚 r) = r
  ofReal_im_ax : ∀ r : ℝ, im (𝓚 r) = 0
  mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w
  mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w
  conj_re_ax : ∀ z : K, re (conj z) = re z
  conj_im_ax : ∀ z : K, im (conj z) = -im z
  conj_I_ax : conj I = -I
  norm_sq_eq_def_ax : ∀ z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
  mul_im_I_ax : ∀ z : K, im z * im I = im z
  /-- only an instance in the `ComplexOrder` scope -/
  [toPartialOrder : PartialOrder K]
  le_iff_re_im {z w : K} : z ≤ w ↔ re z ≤ re w ∧ im z = im w
  -- note we cannot put this in the `extends` clause
  [toDecidableEq : DecidableEq K]

attribute [instance_reducible] RCLike.toPartialOrder RCLike.toDecidableEq
scoped[ComplexOrder] attribute [instance 100] RCLike.toPartialOrder
attribute [instance 100] RCLike.toDecidableEq

end

variable {K E : Type*} [RCLike K]

namespace RCLike

/-- Coercion from `ℝ` to an `RCLike` field. -/
/-
**RCLike.ofReal** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：{K : Type u_1} → [RCLike K] → ℝ → K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℝ` to an `RCLike` field.
-/
@[coe] abbrev ofReal : ℝ → K := Algebra.cast

/-- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `Mathlib/Data/Nat/Cast/Basic.lean` for more details. -/
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The priority must be set at 900 to ensure that coercions are tried in the right 
order.
See Note [coercion into rings], or `Mathlib/Data/Nat/Cast/Basic.lean` for more d
etails.
-/
noncomputable instance (priority := 900) algebraMapCoe : CoeTC ℝ K :=
  ⟨ofReal⟩
/-
**RCLike.ofReal_alg** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_alg (x : Real) : (x : K) = x • (1 : K)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem ofReal_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x
/-
**RCLike.real_smul_eq_coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：real_smul_eq_coe_mul (r : Real) (z : K) : r • z = (r : K) * z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z
/-
**RCLike.real_smul_eq_coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module Real E] [IsSca
larTower Real K E] (r : Real) (x : E) : r • x = (r : K) • x
参数：r : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ofReal_alg`：ofReal_alg (x : Real) : (x : K) = x • (1 : K)
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [RCLike.ofReal_alg, smul_one_smul]
/-
**RCLike.algebraMap_eq_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：algebraMap_eq_ofReal : ⇑(algebraMap Real K) = ofReal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_ofReal : ⇑(algebraMap ℝ K) = ofReal :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.re_add_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_add_im (z : K) : (re z : K) + im z * I = z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.re_add_im_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (
z : K),   (algebraMap ℝ K) (RCLike.re z) + (algebraMap ℝ K) (RCLike.im z) * RCLi
ke.I = z
-/
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  RCLike.re_add_im_ax z

@[simp, norm_cast, rclike_simps]
/-
**RCLike.ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_re : forall r : Real, re (r : K) = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_re_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (
r : ℝ), RCLike.re ((algebraMap ℝ K) r) = r
-/
theorem ofReal_re : ∀ r : ℝ, re (r : K) = r :=
  RCLike.ofReal_re_ax

@[simp, norm_cast, rclike_simps]
/-
**RCLike.ofReal_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_im : forall r : Real, im (r : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_im_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (
r : ℝ), RCLike.im ((algebraMap ℝ K) r) = 0
-/
theorem ofReal_im : ∀ r : ℝ, im (r : K) = 0 :=
  RCLike.ofReal_im_ax

@[simp, rclike_simps]
/-
**RCLike.mul_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：mul_re : forall z w : K, re (z * w) = re z * re w - im z * im w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.mul_re_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (z w
 : K),   RCLike.re (z * w) = RCLike.re z * RCLike.re w - RCLike.im z * RCLike.im
 w
-/
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  RCLike.mul_re_ax

@[simp, rclike_simps]
/-
**RCLike.mul_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：mul_im : forall z w : K, im (z * w) = re z * im w + im z * re w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.mul_im_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (z w
 : K),   RCLike.im (z * w) = RCLike.re z * RCLike.im w + RCLike.im z * RCLike.re
 w
-/
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  RCLike.mul_im_ax
/-
**RCLike.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
-/
theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩
/-
**RCLike.ext** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w
参数：hre : re z = re w；him : im z = im w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
-/
theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩

@[norm_cast]
/-
**RCLike.ofReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_zero : ((0 : Real) : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
-/
theorem ofReal_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero

@[rclike_simps]
/-
**RCLike.zero_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：zero_re : re (0 : K) = (0 : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem zero_re : re (0 : K) = (0 : ℝ) :=
  map_zero re

@[rclike_simps]
/-
**RCLike.zero_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：zero_im : im (0 : K) = (0 : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem zero_im : im (0 : K) = (0 : ℝ) :=
  map_zero im

@[norm_cast]
/-
**RCLike.ofReal_one** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_one : ((1 : Real) : K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)

@[simp, rclike_simps]
/-
**RCLike.one_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：one_re : re (1 : K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_one`：ofReal_one : ((1 : Real) : K) = 1
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]

@[simp, rclike_simps]
/-
**RCLike.one_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：one_im : im (1 : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_one`：ofReal_one : ((1 : Real) : K) = 1
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]
/-
**RCLike.ofReal_injective** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_injective : Function.Injective ((↑) : Real -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem ofReal_injective : Function.Injective ((↑) : ℝ → K) :=
  (algebraMap ℝ K).injective

@[norm_cast]
/-
**RCLike.ofReal_inj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_inj`：coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem ofReal_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj _ _
/-
**RCLike.ofReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_eq_zero_iff`：coe_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a =
 0
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem ofReal_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.coe_eq_zero_iff _ _ _
/-
**RCLike.ofReal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_ne_zero {x : Real} : (x : K) != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `RCLike.ofReal_eq_zero`：ofReal_eq_zero {x : Real} : (x : K) = 0 ↔ x = 0
-/
theorem ofReal_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  ofReal_eq_zero.not

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_add** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_add (r s : Real) : ((r + s : Real) : K) = r + s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_add`：coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b
-/
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_neg** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_neg (r : Real) : ((-r : Real) : K) = -r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_neg`：coe_neg (x : R) : (↑(-x : R) : A) = -↑x
-/
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_sub (r s : Real) : ((r - s : Real) : K) = r - s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_sum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_sum {α : Type*} (s : Finset α) (f : α -> Real) : ((∑ i in s, f i : 
Real) : K) = ∑ i in s, (f i : K)
参数：s : Finset α；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : K) = ∑ i ∈ s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _

@[simp, rclike_simps, norm_cast]
/-
**RCLike.ofReal_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Rea
l) : ((f.sum fun a b => g a b : Real) : K) = f.sum fun a b => (g a b : K)
参数：f : α ->₀ M；g : α -> M -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.sum fun a b => g a b : ℝ) : K) = f.sum fun a b => (g a b : K) :=
  map_finsuppSum (algebraMap ℝ K) f g

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_mul (r s : Real) : ((r * s : Real) : K) = r * s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
-/
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K) = (r : K) ^ n
参数：r : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_pow (algebraMap ℝ K) r n

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_prod** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_prod {α : Type*} (s : Finset α) (f : α -> Real) : ((∏ i in s, f i :
 Real) : K) = ∏ i in s, (f i : K)
参数：s : Finset α；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ i ∈ s, f i : ℝ) : K) = ∏ i ∈ s, (f i : K) :=
  map_prod (algebraMap ℝ K) _ _

@[simp, rclike_simps, norm_cast]
/-
**RCLike.ofReal_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_finsuppProd {α M : Type*} [Zero M] (f : α ->₀ M) (g : α -> M -> Rea
l) : ((f.prod fun a b => g a b : Real) : K) = f.prod fun a b => (g a b : K)
参数：f : α ->₀ M；g : α -> M -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_finsuppProd {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.prod fun a b => g a b : ℝ) : K) = f.prod fun a b => (g a b : K) :=
  map_finsuppProd _ f g

@[simp, norm_cast, rclike_simps]
/-
**RCLike.real_smul_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：real_smul_ofReal (r x : Real) : r • (x : K) = (r : K) * (x : K)
参数：r x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
-/
theorem real_smul_ofReal (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _

@[rclike_simps]
/-
**RCLike.re_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r * re z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_ofReal_mul (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[rclike_simps]
/-
**RCLike.re_mul_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_mul_ofReal (z : K) (r : Real) : re (z * ↑r) = re z * r
参数：z : K；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
-/
theorem re_mul_ofReal (z : K) (r : ℝ) : re (z * ↑r) = re z * r := by
  rw [mul_comm, re_ofReal_mul, mul_comm]

@[rclike_simps]
/-
**RCLike.im_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r * im z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_ofReal_mul (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[rclike_simps]
/-
**RCLike.im_mul_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_mul_ofReal (z : K) (r : Real) : im (z * ↑r) = im z * r
参数：z : K；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r
 * im z
-/
theorem im_mul_ofReal (z : K) (r : ℝ) : im (z * ↑r) = im z * r := by
  rw [mul_comm, im_ofReal_mul, mul_comm]

@[rclike_simps]
/-
**RCLike.smul_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：smul_re (r : Real) (z : K) : re (r • z) = r * re z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
-/
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, re_ofReal_mul]

@[rclike_simps]
/-
**RCLike.smul_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：smul_im (r : Real) (z : K) : im (r • z) = r * im z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
· 使用定理 `RCLike.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r
 * im z
-/
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, im_ofReal_mul]

@[rclike_simps, norm_cast]
/-
**RCLike.norm_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem norm_ofReal (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r

@[simp]
/-
**RCLike.re_ofReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^ n) = a ^ n
参数：a : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem re_ofReal_pow (a : ℝ) (n : ℕ) : re ((a : K) ^ n) = a ^ n := by
  rw [← ofReal_pow, @ofReal_re]

@[simp]
/-
**RCLike.im_ofReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_ofReal_pow (a : Real) (n : Nat) : im ((a : K) ^ n) = 0
参数：a : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用定理 `RCLike.ofReal_im_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (
r : ℝ), RCLike.im ((algebraMap ℝ K) r) = 0
-/
theorem im_ofReal_pow (a : ℝ) (n : ℕ) : im ((a : K) ^ n) = 0 := by
  rw [← @ofReal_pow, @ofReal_im_ax]

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero. -/
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ℝ and ℂ are both of characteristic zero.
-/
instance (priority := 100) charZero_rclike : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).injective).1 inferInstance

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_expect** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_expect {α : Type*} (s : Finset α) (f : α -> Real) : 𝔼 i in s, f i =
 𝔼 i in s, (f i : K)
参数：s : Finset α；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma ofReal_expect {α : Type*} (s : Finset α) (f : α → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : K) :=
  map_expect (algebraMap ..) ..

@[norm_cast]
/-
**RCLike.ofReal_balance** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_balance {ι : Type*} [Fintype ι] (f : ι -> Real) (i : ι) : ((balance
 f i : Real) : K) = balance ((↑) ∘ f) i
参数：f : ι -> Real；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.map_balance`：∀ {ι : Type u_1} {H : Type u_2} {F : Type u_3} {G :
 Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup G]   [inst_2 : _root_.Modul
e ℚ≥0 G] …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma ofReal_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) :
    ((balance f i : ℝ) : K) = balance ((↑) ∘ f) i := map_balance (algebraMap ..) ..
/-
**RCLike.ofReal_comp_balance** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] {ι : Type u_3} [inst_1 : Fintype ι] (f 
: ι → ℝ),   RCLike.ofReal ∘ Fintype.balance f = Fintype.balance (RCLike.ofReal ∘
 f)
参数：f : ι → ℝ；RCLike.ofReal ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用引理 `RCLike.ofReal_balance`：ofReal_balance {ι : Type*} [Fintype ι] (f : ι -> 
Real) (i : ι) : ((balance f i : Real) : K) = balance ((↑) ∘ f) i
-/
@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f : ι → K) := funext <| ofReal_balance _

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, rclike_simps]
/-
**RCLike.I_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_re : re (I : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.I_re_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K], RCLik
e.re RCLike.I = 0

--- 原说明 ---
The imaginary unit.
-/
theorem I_re : re (I : K) = 0 :=
  I_re_ax

@[simp, rclike_simps]
/-
**RCLike.I_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_im (z : K) : im z * im (I : K) = im z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.mul_im_I_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (z
 : K), RCLike.im z * RCLike.im RCLike.I = RCLike.im z
-/
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z

@[simp, rclike_simps]
/-
**RCLike.I_im'** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_im' (z : K) : im (I : K) * im z = im z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.I_im`：I_im (z : K) : im z * im (I : K) = im z
-/
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/-
**RCLike.I_mul_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_mul_re (z : K) : re (I * z) = -im z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.I_im'`：I_im' (z : K) : im (I : K) * im z = im z
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]
/-
**RCLike.I_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.I_mul_I_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K], RC
Like.I = 0 ∨ RCLike.I * RCLike.I = -1
-/
theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax

variable (𝕜) in
/-
**RCLike.I_eq_zero_or_im_I_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.I_mul_re`：I_mul_re (z : K) : re (I * z) = -im z
· 使用定理 `RCLike.I_mul_I`：I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1
-/
lemma I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1 :=
  I_mul_I (K := K) |>.imp_right fun h ↦ by simpa [h] using (I_mul_re (I : K)).symm

@[simp, rclike_simps]
/-
**RCLike.conj_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_re (z : K) : re (conj z) = re z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_re_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (z 
: K), RCLike.re ((starRingEnd K) z) = RCLike.re z
-/
theorem conj_re (z : K) : re (conj z) = re z :=
  RCLike.conj_re_ax z

@[simp, rclike_simps]
/-
**RCLike.conj_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_im (z : K) : im (conj z) = -im z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_im_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] (z 
: K), RCLike.im ((starRingEnd K) z) = -RCLike.im z
-/
theorem conj_im (z : K) : im (conj z) = -im z :=
  RCLike.conj_im_ax z

@[simp, rclike_simps]
/-
**RCLike.conj_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_I : conj (I : K) = -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_I_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K], (st
arRingEnd K) RCLike.I = -RCLike.I
-/
theorem conj_I : conj (I : K) = -I :=
  RCLike.conj_I_ax

@[simp, rclike_simps]
/-
**RCLike.conj_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_ofReal (r : Real) : conj (r : K) = (r : K)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem conj_ofReal (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, conj_re, and_self_iff, neg_zero]
/-
**RCLike.conj_nat_cast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_nat_cast (n : Nat) : conj (n : K) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem conj_nat_cast (n : ℕ) : conj (n : K) = n := map_natCast _ _
/-
**RCLike.conj_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_ofNat (n : Nat) [n.AtLeastTwo] : conj (ofNat(n) : K) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
-/
theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : K) = ofNat(n) :=
  map_ofNat _ _

@[rclike_simps, simp]
/-
**RCLike.conj_neg_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_neg_I : conj (-I) = (I : K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]
/-
**RCLike.conj_eq_re_sub_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_eq_re_sub_im (z : K) : conj z = re z - im z * I
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_ofReal, conj_ofReal, mul_neg, sub_eq_add_neg]
/-
**RCLike.sub_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：sub_conj (z : K) : z - conj z = 2 * im z * I
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.conj_eq_re_sub_im`：conj_eq_re_sub_im (z : K) : conj z = re z - im
 z * I
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[rclike_simps]
/-
**RCLike.conj_smul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_smul (r : Real) (z : K) : conj (r • z) = r • conj z
参数：r : Real；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.conj_eq_re_sub_im`：conj_eq_re_sub_im (z : K) : conj z = re z - im
 z * I
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z
· 使用定理 `RCLike.smul_im`：smul_im (r : Real) (z : K) : im (r • z) = r * im z
· 使用定理 `RCLike.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : K) = r * 
s
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, ofReal_mul, ofReal_mul,
    real_smul_eq_coe_mul r (_ - _), mul_sub, mul_assoc]
/-
**RCLike.add_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：add_conj (z : K) : z + conj z = 2 * re z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `RCLike.conj_eq_re_sub_im`：conj_eq_re_sub_im (z : K) : conj z = re z - im
 z * I
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]
/-
**RCLike.re_eq_add_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.add_conj`：add_conj (z : K) : z + conj z = 2 * re z
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
-/
theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left₀ (re z : K) two_ne_zero]
/-
**RCLike.im_eq_conj_sub** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `RCLike.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : K) = -r
· 使用定理 `RCLike.I_mul_re`：I_mul_re (z : K) : re (I * z) = -im z
· 使用定理 `RCLike.re_eq_add_conj`：re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) /
 2
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← ofReal_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]

open List in
/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
/-
**RCLike.is_real_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：is_real_TFAE (z : K) : TFAE [conj z = z, exists r : Real, (r : K) = z, ↑(r
e z) = z, im z = 0, IsSelfAdjoint z]
参数：z : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RCLike.im_eq_conj_sub`：im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - 
z) / 2
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
There are several equivalent ways to say that a number `z` is in fact a real num
ber.
-/
theorem is_real_TFAE (z : K) :
    TFAE [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z] := by
  tfae_have 1 → 4
  | h => by
    rw [← @ofReal_inj K, im_eq_conj_sub, h, sub_self, mul_zero, zero_div,
      ofReal_zero]
  tfae_have 4 → 3
  | h => by
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 → 2 := fun h => ⟨_, h⟩
  tfae_have 2 → 1 := fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  tfae_have 1 → 5 := fun _ => by rwa [isSelfAdjoint_iff]
  tfae_have 5 → 1 := fun hz => by rwa [isSelfAdjoint_iff] at hz
  tfae_finish

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**RCLike.conj_eq_iff_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_eq_iff_real {z : K} : conj z = z ↔ exists r : Real, z = (r : K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  calc
    _ ↔ ∃ r : ℝ, (r : K) = z := (is_real_TFAE z).out 0 1
    _ ↔ _                    := by simp only [eq_comm]
/-
**RCLike.conj_eq_iff_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
-/
theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2
/-
**RCLike.conj_eq_iff_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
-/
theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3

@[simp]
/-
**RCLike.star_def** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：star_def : (Star.star : K -> K) = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_def : (Star.star : K → K) = conj :=
  rfl
/-
**RCLike.im_eq_zero_iff_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：im_eq_zero_iff_isSelfAdjoint {x : K} : im x = 0 ↔ IsSelfAdjoint x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
-/
lemma im_eq_zero_iff_isSelfAdjoint {x : K} : im x = 0 ↔ IsSelfAdjoint x :=
  is_real_TFAE x |>.out 3 4
/-
**RCLike.re_eq_ofReal_of_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：re_eq_ofReal_of_isSelfAdjoint {x : K} {y : Real} (hx : IsSelfAdjoint x) : 
re x = y ↔ x = y
参数：hx : IsSelfAdjoint x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma re_eq_ofReal_of_isSelfAdjoint {x : K} {y : ℝ} (hx : IsSelfAdjoint x) :
    re x = y ↔ x = y := by
  simp [RCLike.ext_iff (K := K), hx, im_eq_zero_iff_isSelfAdjoint]
/-
**RCLike.ofReal_eq_re_of_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_eq_re_of_isSelfAdjoint {x : K} {y : Real} (hx : IsSelfAdjoint x) : 
y = re x ↔ y = x
参数：hx : IsSelfAdjoint x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.re_eq_ofReal_of_isSelfAdjoint`：re_eq_ofReal_of_isSelfAdjoint {x :
 K} {y : Real} (hx : IsSelfAdjoint x) : re x = y ↔ x = y
-/
lemma ofReal_eq_re_of_isSelfAdjoint {x : K} {y : ℝ} (hx : IsSelfAdjoint x) :
    y = re x ↔ y = x := by
  simpa [eq_comm] using re_eq_ofReal_of_isSelfAdjoint hx

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
/-
**RCLike.conjToRingEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `RCLike`。
形式化陈述：conjToRingEquiv : K ≃+* Kᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation as a ring equivalence. This is used to convert the inner product int
o a
sesquilinear product.
-/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv

variable {K} {z : K}

/-- The norm squared function. -/
/-
**RCLike.normSq** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：normSq : K ->*₀ Real where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm squared function.
-/
def normSq : K →*₀ ℝ where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring
/-
**RCLike.normSq_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_apply (z : K) : normSq z = re z * re z + im z * im z
参数：z : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_apply (z : K) : normSq z = re z * re z + im z * im z :=
  rfl
/-
**RCLike.norm_sq_eq_def** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.norm_sq_eq_def_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike
 K] (z : K),   ‖z‖ ^ 2 = RCLike.re z * RCLike.re z + RCLike.im z * RCLike.im z
-/
theorem norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z
/-
**RCLike.normSq_eq_def'** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.norm_sq_eq_def`：norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + 
im z * im z
-/
theorem normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2 :=
  norm_sq_eq_def.symm

@[rclike_simps]
/-
**RCLike.normSq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_zero : normSq (0 : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 0 = 0
-/
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero

@[rclike_simps]
/-
**RCLike.normSq_one** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_one : normSq (1 : K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_one`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 1 = 1
-/
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one
/-
**RCLike.normSq_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_nonneg (z : K) : 0 <= normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/-
**RCLike.normSq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
-/
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _

@[simp, rclike_simps]
/-
**RCLike.normSq_pos** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_pos {z : K} : 0 < normSq z ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm]; simp [normSq_nonneg]

@[simp, rclike_simps]
/-
**RCLike.normSq_neg** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_neg (z : K) : normSq (-z) = normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.normSq_eq_def'`：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]

@[simp, rclike_simps]
/-
**RCLike.normSq_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_conj (z : K) : normSq (conj z) = normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/-
**RCLike.normSq_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w
/-
**RCLike.normSq_add** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * 
conj w)
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 48 条，此处仅展示前 30 条）
-/
theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, rclike_simps]
  ring
/-
**RCLike.re_sq_le_normSq** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_sq_le_normSq (z : K) : re z * re z <= normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
/-
**RCLike.im_sq_le_normSq** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_sq_le_normSq (z : K) : im z * im z <= normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
/-
**RCLike.mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ext`：ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = 
w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `RCLike.norm_sq_eq_def`：norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + 
im z * im z
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 31 条，此处仅展示前 30 条）
-/
theorem mul_conj (z : K) : z * conj z = ‖z‖ ^ 2 := by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]
/-
**RCLike.conj_mul** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
-/
theorem conj_mul (z : K) : conj z * z = ‖z‖ ^ 2 := by rw [mul_comm, mul_conj]
/-
**RCLike.inv_eq_conj** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z
参数：hz : ‖z‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_left`：inv_eq_of_mul_eq_one_left (h : a * b = 1) : b
⁻¹ = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z :=
  inv_eq_of_mul_eq_one_left <| by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]
/-
**RCLike.normSq_sub** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * 
conj w)
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `RCLike.normSq_add`：normSq_add (z w : K) : normSq (z + w) = normSq z + no
rmSq w + 2 * re (z * conj w)
· 使用定理 `RCLike.normSq_neg`：normSq_neg (z : K) : normSq (-z) = normSq z
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]
/-
**RCLike.sqrt_normSq_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：sqrt_normSq_eq_norm {z : K} : √(normSq z) = ‖z‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.normSq_eq_def'`：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem sqrt_normSq_eq_norm {z : K} : √(normSq z) = ‖z‖ := by
  rw [normSq_eq_def', Real.sqrt_sq (norm_nonneg _)]

/-! ### Inversion -/

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_inv** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻¹
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
### Inversion
-/
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r
/-
**RCLike.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : Real)
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `RCLike.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻
¹
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
-/
theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, ofReal_inv, ofReal_pow, mul_inv_cancel₀]
    simpa

@[simp, rclike_simps]
/-
**RCLike.inv_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：inv_re (z : K) : re z⁻¹ = re z / normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.inv_def`：inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : Real)
· 使用定理 `RCLike.normSq_eq_def'`：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, re_ofReal_mul, conj_re, div_eq_inv_mul]

@[simp, rclike_simps]
/-
**RCLike.inv_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：inv_im (z : K) : im z⁻¹ = -im z / normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.inv_def`：inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : Real)
· 使用定理 `RCLike.normSq_eq_def'`：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r
 * im z
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, im_ofReal_mul, conj_im, div_eq_inv_mul]
/-
**RCLike.div_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / nor
mSq w
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.inv_re`：inv_re (z : K) : re z⁻¹ = re z / normSq z
· 使用定理 `RCLike.inv_im`：inv_im (z : K) : im z⁻¹ = -im z / normSq z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg,
    rclike_simps]
/-
**RCLike.div_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / nor
mSq w
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `RCLike.inv_im`：inv_im (z : K) : im z⁻¹ = -im z / normSq z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `RCLike.inv_re`：inv_re (z : K) : re z⁻¹ = re z / normSq z
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg,
    rclike_simps]

-- Not `@[simp]` since `simp` can prove this
@[rclike_simps]
/-
**RCLike.conj_inv** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_inv₀`：star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = 
(star x)⁻¹
-/
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _
/-
**RCLike.conj_div** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：conj_div (x y : K) : conj (x / y) = conj x / conj y
参数：x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div'`：map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
 (f : F) (hf : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RCLike.conj_inv`：conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹
-/
lemma conj_div (x y : K) : conj (x / y) = conj x / conj y := map_div' conj conj_inv _ _

--TODO: Do we rather want the map as an explicit definition?
/-
**RCLike.exists_norm_eq_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：exists_norm_eq_mul_self (x : K) : exists c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
-/
lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩
/-
**RCLike.exists_norm_mul_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：exists_norm_mul_eq_self (x : K) : exists c, ‖c‖ = 1 ∧ c * ‖x‖ = x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
-/
lemma exists_norm_mul_eq_self (x : K) : ∃ c, ‖c‖ = 1 ∧ c * ‖x‖ = x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_div** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_div (r s : Real) : ((r / s : Real) : K) = r / s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s
/-
**RCLike.div_re_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：div_re_ofReal {z : K} {r : Real} : re (z / r) = re z / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻
¹
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
-/
theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, re_ofReal_mul]

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_zpow** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) : K) = (r : K) ^ n
参数：r : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n
/-
**RCLike.I_mul_I_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_mul_I_of_nonzero : (I : K) != 0 -> (I : K) * I = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `RCLike.I_mul_I_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K], RC
Like.I = 0 ∨ RCLike.I * RCLike.I = -1
-/
theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left

@[simp, rclike_simps]
/-
**RCLike.inv_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：inv_I : (I : K)⁻¹ = -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
（共 73 条，此处仅展示前 30 条）
-/
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp
    linear_combination I_mul_I_of_nonzero h

@[simp, rclike_simps]
/-
**RCLike.div_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：div_I (z : K) : z / I = -(z * I)
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `RCLike.inv_I`：inv_I : (I : K)⁻¹ = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/-
**RCLike.normSq_inv** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
-/
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
/-
**RCLike.normSq_div** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w
参数：z w : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
-/
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

@[simp 1100, rclike_simps]
/-
**RCLike.norm_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_conj (z : K) : ‖conj z‖ = ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.normSq_conj`：normSq_conj (z : K) : normSq (conj z) = normSq z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_conj (z : K) : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]
/-
**RCLike.nnnorm_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] (z : K), ‖(starRingEnd K) z‖₊ = ‖z‖₊
参数：z : K；starRingEnd K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp 1100, rclike_simps] lemma nnnorm_conj (z : K) : ‖conj z‖₊ = ‖z‖₊ := by simp [nnnorm]
/-
**RCLike.enorm_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] (z : K), ‖(starRingEnd K) z‖ₑ = ‖z‖ₑ
参数：z : K；starRingEnd K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.nnnorm_conj`：∀ {K : Type u_1} [inst : RCLike K] (z : K), ‖(starRi
ngEnd K) z‖₊ = ‖z‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp 1100, rclike_simps] lemma enorm_conj (z : K) : ‖conj z‖ₑ = ‖z‖ₑ := by simp [enorm]
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CStarRing K where
  norm_mul_self_le x := le_of_eq <| ((norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_conj _)).symm
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule ℝ K where
  star_smul r a := by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

/-! ### Cast lemmas -/

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_natCast (n : Nat) : ((n : Real) : K) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n

--- 原说明 ---
### Cast lemmas
-/
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n

@[simp, rclike_simps]
/-
**RCLike.natCast_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：natCast_re (n : Nat) : re (n : K) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_natCast`：ofReal_natCast (n : Nat) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem natCast_re (n : ℕ) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/-
**RCLike.natCast_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：natCast_im (n : Nat) : im (n : K) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_natCast`：ofReal_natCast (n : Nat) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem natCast_im (n : ℕ) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]
@[simp, rclike_simps]
/-
**RCLike.ofNat_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofNat_re (n : Nat) [n.AtLeastTwo] : re (ofNat(n) : K) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.natCast_re`：natCast_re (n : Nat) : re (n : K) = n
-/
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : re (ofNat(n) : K) = ofNat(n) :=
  natCast_re n
@[simp, rclike_simps]
/-
**RCLike.ofNat_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofNat_im (n : Nat) [n.AtLeastTwo] : im (ofNat(n) : K) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.natCast_im`：natCast_im (n : Nat) : im (n : K) = 0
-/
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : im (ofNat(n) : K) = 0 :=
  natCast_im n

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real) : K) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_natCast`：ofReal_natCast (n : Nat) : ((n : Real) : K) = n
-/
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℝ) : K) = ofNat(n) :=
  ofReal_natCast n
/-
**RCLike.ofNat_mul_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofNat_mul_re (n : Nat) [n.AtLeastTwo] (z : K) : re (ofNat(n) * z) = ofNat(
n) * re z
参数：n : Nat；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ofNat`：ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) 
: Real) : K) = ofNat(n)
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
-/
theorem ofNat_mul_re (n : ℕ) [n.AtLeastTwo] (z : K) :
    re (ofNat(n) * z) = ofNat(n) * re z := by
  rw [← ofReal_ofNat, re_ofReal_mul]
/-
**RCLike.ofNat_mul_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofNat_mul_im (n : Nat) [n.AtLeastTwo] (z : K) : im (ofNat(n) * z) = ofNat(
n) * im z
参数：n : Nat；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ofNat`：ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) 
: Real) : K) = ofNat(n)
· 使用定理 `RCLike.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r
 * im z
-/
theorem ofNat_mul_im (n : ℕ) [n.AtLeastTwo] (z : K) :
    im (ofNat(n) * z) = ofNat(n) * im z := by
  rw [← ofReal_ofNat, im_ofReal_mul]

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_intCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_intCast (n : Int) : ((n : Real) : K) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
-/
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast _ n

@[simp, rclike_simps]
/-
**RCLike.intCast_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：intCast_re (n : Int) : re (n : K) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_intCast`：ofReal_intCast (n : Int) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem intCast_re (n : ℤ) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/-
**RCLike.intCast_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：intCast_im (n : Int) : im (n : K) = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_intCast`：ofReal_intCast (n : Int) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem intCast_im (n : ℤ) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K) = n
参数：n : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nnratCast`：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Fu
nLike F α β] [inst_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [Ring
Hom…
-/
theorem ofReal_nnratCast (n : ℚ≥0) : ((n : ℝ) : K) = n :=
  map_nnratCast _ n

@[simp, rclike_simps]
/-
**RCLike.nnratCast_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：nnratCast_re (q : Rat>=0) : re (q : K) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_nnratCast`：ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K
) = n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem nnratCast_re (q : ℚ≥0) : re (q : K) = q := by rw [← ofReal_nnratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/-
**RCLike.nnratCast_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：nnratCast_im (q : Rat>=0) : im (q : K) = 0
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_nnratCast`：ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K
) = n
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem nnratCast_im (q : ℚ≥0) : im (q : K) = 0 := by rw [← ofReal_nnratCast, ofReal_im]

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_ratCast (n : Rat) : ((n : Real) : K) = n
参数：n : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
-/
theorem ofReal_ratCast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast _ n

@[simp, rclike_simps]
/-
**RCLike.ratCast_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ratCast_re (q : Rat) : re (q : K) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ratCast`：ofReal_ratCast (n : Rat) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem ratCast_re (q : ℚ) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
/-
**RCLike.ratCast_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ratCast_im (q : Rat) : im (q : K) = 0
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ratCast`：ofReal_ratCast (n : Rat) : ((n : Real) : K) = n
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem ratCast_im (q : ℚ) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]

open OfScientific (ofScientific)

@[rclike_simps, norm_cast]
/-
**RCLike.ofReal_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_ofScientific (m : Nat) (s : Bool) (e : Nat) : ((ofScientific m s e 
: Real) : K) = ofScientific m s e
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_nnratCast`：ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K
) = n
· 使用定理 `Rat.ofScientific_nonneg`：ofScientific_nonneg (m : Nat) (s : Bool) (e : N
at) : 0 <= Rat.ofScientific m s e
-/
theorem ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ((ofScientific m s e : ℝ) : K) = ofScientific m s e := ofReal_nnratCast _

@[simp, rclike_simps]
/-
**RCLike.ofScientific_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofScientific_re (m : Nat) (s : Bool) (e : Nat) : re (ofScientific m s e : 
K) = ofScientific m s e
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ofScientific`：ofReal_ofScientific (m : Nat) (s : Bool) (e 
: Nat) : ((ofScientific m s e : Real) : K) = ofScientific m s e
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem ofScientific_re (m : ℕ) (s : Bool) (e : ℕ) :
    re (ofScientific m s e : K) = ofScientific m s e := by rw [← ofReal_ofScientific, ofReal_re]

@[simp, rclike_simps, norm_cast]
/-
**RCLike.ofScientific_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofScientific_im (m : Nat) (s : Bool) (e : Nat) : im (ofScientific m s e : 
K) = 0
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ofScientific`：ofReal_ofScientific (m : Nat) (s : Bool) (e 
: Nat) : ((ofScientific m s e : Real) : K) = ofScientific m s e
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem ofScientific_im (m : ℕ) (s : Bool) (e : ℕ) :
    im (ofScientific m s e : K) = 0 := by rw [← ofReal_ofScientific, ofReal_im]

/-! ### Norm -/

/-
**RCLike.norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : K)‖ = r
参数：h : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
### Norm
-/
theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)

@[simp 1100, rclike_simps, norm_cast]
/-
**RCLike.norm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_natCast (n : Nat) : ‖(n : K)‖ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_natCast`：ofReal_natCast (n : Nat) : ((n : Real) : K) = n
· 使用定理 `RCLike.norm_of_nonneg`：norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : K)
‖ = r
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)
/-
**RCLike.nnnorm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] (n : ℕ), ‖↑n‖₊ = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `NNReal.mk_natCast`：mk_natCast (n : Nat) : NNReal.mk (n : Real) (n.cast_n
onneg) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, rclike_simps, norm_cast] lemma nnnorm_natCast (n : ℕ) : ‖(n : K)‖₊ = n := by simp [nnnorm]

@[simp, rclike_simps]
/-
**RCLike.norm_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖ = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
-/
theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖ = ofNat(n) :=
  norm_natCast n

@[simp, rclike_simps]
/-
**RCLike.nnnorm_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nnnorm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖₊ = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.nnnorm_natCast`：∀ {K : Type u_1} [inst : RCLike K] (n : ℕ), ‖↑n‖₊
 = ↑n
-/
lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖₊ = ofNat(n) :=
  nnnorm_natCast n
/-
**RCLike.norm_two** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_two : ‖(2 : K)‖ = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.norm_ofNat`：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)
‖ = ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2
/-
**RCLike.nnnorm_two** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nnnorm_two : ‖(2 : K)‖₊ = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.nnnorm_ofNat`：nnnorm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) 
: K)‖₊ = ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma nnnorm_two : ‖(2 : K)‖₊ = 2 := nnnorm_ofNat 2

@[simp, rclike_simps, norm_cast]
/-
**RCLike.norm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_nnratCast (q : Rat>=0) : ‖(q : K)‖ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_nnratCast`：ofReal_nnratCast (n : Rat>=0) : ((n : Real) : K
) = n
· 使用定理 `RCLike.norm_of_nonneg`：norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : K)
‖ = r
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : K)‖ = q := by
  rw [← ofReal_nnratCast]; exact norm_of_nonneg q.cast_nonneg

@[simp, rclike_simps, norm_cast]
/-
**RCLike.nnnorm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nnnorm_nnratCast (q : Rat>=0) : ‖(q : K)‖₊ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `RCLike.norm_nnratCast`：norm_nnratCast (q : Rat>=0) : ‖(q : K)‖ = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
-/
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : K)‖₊ = q := by simp [nnnorm]; rfl

variable (K) in
/-
**RCLike.norm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E) : ‖n
 • x‖ = n • ‖x‖
参数：n : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma norm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ := by
  simpa [Nat.cast_smul_eq_nsmul] using norm_smul (n : K) x

variable (K) in
/-
**RCLike.nnnorm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nnnorm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : Nat) (x : E) : 
‖n • x‖₊ = n • ‖x‖₊
参数：n : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.nnnorm_natCast`：∀ {K : Type u_1} [inst : RCLike K] (n : ℕ), ‖↑n‖₊
 = ↑n
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma nnnorm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : ℕ) (x : E) :
    ‖n • x‖₊ = n • ‖x‖₊ := by simpa [Nat.cast_smul_eq_nsmul] using nnnorm_smul (n : K) x
/-
**RCLike.mul_self_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.normSq_eq_def'`：normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]

attribute [rclike_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div
/-
**RCLike.abs_re_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：abs_re_le_norm (z : K) : |re z| <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `RCLike.mul_self_norm`：mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z
· 使用定理 `RCLike.re_sq_le_normSq`：re_sq_le_normSq (z : K) : re z * re z <= normSq 
z
-/
theorem abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply re_sq_le_normSq
/-
**RCLike.abs_im_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：abs_im_le_norm (z : K) : |im z| <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `RCLike.mul_self_norm`：mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z
· 使用定理 `RCLike.im_sq_le_normSq`：im_sq_le_normSq (z : K) : im z * im z <= normSq 
z
-/
theorem abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply im_sq_le_normSq
/-
**RCLike.norm_re_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_re_le_norm (z : K) : ‖re z‖ <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.abs_re_le_norm`：abs_re_le_norm (z : K) : |re z| <= ‖z‖
-/
theorem norm_re_le_norm (z : K) : ‖re z‖ ≤ ‖z‖ :=
  abs_re_le_norm z
/-
**RCLike.norm_im_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_im_le_norm (z : K) : ‖im z‖ <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.abs_im_le_norm`：abs_im_le_norm (z : K) : |im z| <= ‖z‖
-/
theorem norm_im_le_norm (z : K) : ‖im z‖ ≤ ‖z‖ :=
  abs_im_le_norm z
/-
**RCLike.re_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_le_norm (z : K) : re z <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `RCLike.abs_re_le_norm`：abs_re_le_norm (z : K) : |re z| <= ‖z‖
-/
theorem re_le_norm (z : K) : re z ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm z)).2
/-
**RCLike.im_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_le_norm (z : K) : im z <= ‖z‖
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `RCLike.abs_im_le_norm`：abs_im_le_norm (z : K) : |im z| <= ‖z‖
-/
theorem im_le_norm (z : K) : im z ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2
/-
**RCLike.im_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_eq_zero_of_le {a : K} (h : ‖a‖ <= re a) : im a = 0
参数：h : ‖a‖ <= re a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_self_norm`：mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `RCLike.re_le_norm`：re_le_norm (z : K) : re z <= ‖z‖
-/
theorem im_eq_zero_of_le {a : K} (h : ‖a‖ ≤ re a) : im a = 0 := by
  simpa only [mul_self_norm a, normSq_apply, left_eq_add, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)
/-
**RCLike.re_eq_self_of_le** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_eq_self_of_le {a : K} (h : ‖a‖ <= re a) : (re a : K) = a
参数：h : ‖a‖ <= re a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.conj_eq_iff_re`：conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) 
= z
· 使用定理 `RCLike.conj_eq_iff_im`：conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0
· 使用定理 `RCLike.im_eq_zero_of_le`：im_eq_zero_of_le {a : K} (h : ‖a‖ <= re a) : im
 a = 0
-/
theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re, conj_eq_iff_im, im_eq_zero_of_le h]

open IsAbsoluteValue
/-
**RCLike.abs_re_div_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| <= 1
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `RCLike.abs_re_le_norm`：abs_re_le_norm (z : K) : |re z| <= ‖z‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (abs_re_le_norm _) (norm_nonneg _)
/-
**RCLike.abs_im_div_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| <= 1
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `RCLike.abs_im_le_norm`：abs_im_le_norm (z : K) : |im z| <= ‖z‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (abs_im_le_norm _) (norm_nonneg _)
/-
**RCLike.norm_I_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_I_of_ne_zero (hI : (I : K) != 0) : ‖(I : K)‖ = 1
参数：hI : (I : K) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `RCLike.I_mul_I_of_nonzero`：I_mul_I_of_nonzero : (I : K) != 0 -> (I : K) 
* I = -1
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem norm_I_of_ne_zero (hI : (I : K) ≠ 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
    I_mul_I_of_nonzero hI, norm_neg, norm_one]
/-
**RCLike.norm_I** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_I : ‖(I : K)‖ = if (I : K) = 0 then 0 else 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_I : ‖(I : K)‖ = if (I : K) = 0 then 0 else 1 := by
  grind [norm_I_of_ne_zero, norm_eq_zero]
/-
**RCLike.re_eq_norm_of_mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, ← ofReal_pow]; simp [-map_pow]
/-
**RCLike.norm_sq_re_add_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.add_conj`：add_conj (z : K) : z + conj z = 2 * re z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_ofNat`：ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) 
: Real) : K) = ofNat(n)
· 使用定理 `RCLike.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : K) = r * 
s
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, ← ofReal_ofNat, ← ofReal_mul, norm_ofReal, sq_abs, ofReal_re]
/-
**RCLike.norm_sq_re_conj_add** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `RCLike.norm_sq_re_add_conj`：norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^
 2 = re (x + conj x) ^ 2
-/
theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormSMulClass ℤ K where
  norm_smul r x := by
    rw [zsmul_eq_mul, norm_mul, ← ofReal_intCast, norm_ofReal, Int.norm_eq_abs]

/-! ### Cauchy sequences -/

/-
**RCLike.isCauSeq_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n)
参数：f : CauSeq K norm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.abs_re_le_norm`：abs_re_le_norm (z : K) : |re z| <= ‖z‖
· 使用定理 `CauSeq.cauchy`：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i
, forall j >= i, abv (f j - f i) < ε

--- 原说明 ---
### Cauchy sequences
-/
theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)
/-
**RCLike.isCauSeq_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n)
参数：f : CauSeq K norm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.abs_im_le_norm`：abs_im_le_norm (z : K) : |im z| <= ‖z‖
· 使用定理 `CauSeq.cauchy`：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i
, forall j >= i, abv (f j - f i) < ε
-/
theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
/-
**RCLike.cauSeqRe** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：cauSeqRe (f : CauSeq K norm) : CauSeq Real abs
参数：f : CauSeq K norm。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.isCauSeq_re`：isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n
 => re (f n)

--- 原说明 ---
The real part of a K Cauchy sequence, as a real Cauchy sequence.
-/
noncomputable def cauSeqRe (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
/-
**RCLike.cauSeqIm** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：cauSeqIm (f : CauSeq K norm) : CauSeq Real abs
参数：f : CauSeq K norm。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.isCauSeq_im`：isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n
 => im (f n)

--- 原说明 ---
The imaginary part of a K Cauchy sequence, as a real Cauchy sequence.
-/
noncomputable def cauSeqIm (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩
/-
**RCLike.isCauSeq_norm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：isCauSeq_norm {f : Nat -> K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘
 f)
参数：hf : IsCauSeq norm f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `abs_norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E]
 (a b : E), |‖a‖ - ‖b‖| ≤ ‖a - b‖
-/
theorem isCauSeq_norm {f : ℕ → K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
/-
**RCLike.I_mem_skewAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：I_mem_skewAdjoint : I in skewAdjoint K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma I_mem_skewAdjoint : I ∈ skewAdjoint K := by simp [skewAdjoint.mem_iff]

end RCLike

section
variable {A : Type*} [AddCommGroup A] [StarAddMonoid A] [Module K A] [StarModule K A] {a : A}

open RCLike

/-
**IsSelfAdjoint.I_smul_mem_skewAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.I_smul_mem_skewAdjoint (h : IsSelfAdjoint a) : (I : K) • a i
n skewAdjoint A
参数：h : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.smul_mem_skewAdjoint`：IsSelfAdjoint.smul_mem_skewAdjoint [
Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R] [StarAddMonoid A] [StarM
odule R A] {r : R} (hr :…
· 使用引理 `RCLike.I_mem_skewAdjoint`：I_mem_skewAdjoint : I in skewAdjoint K
-/
lemma IsSelfAdjoint.I_smul_mem_skewAdjoint (h : IsSelfAdjoint a) :
    (I : K) • a ∈ skewAdjoint A := h.smul_mem_skewAdjoint I_mem_skewAdjoint
/-
**IsSelfAdjoint.I_smul_of_mem_skewAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.I_smul_of_mem_skewAdjoint (h : a in skewAdjoint A) : IsSelfA
djoint ((I : K) • a)
参数：h : a in skewAdjoint A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isSelfAdjoint_smul_of_mem_skewAdjoint`：isSelfAdjoint_smul_of_mem_skewAdj
oint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R] [StarAddMonoid A] 
[StarModule R A] {r : R} (h…
· 使用引理 `RCLike.I_mem_skewAdjoint`：I_mem_skewAdjoint : I in skewAdjoint K
-/
lemma IsSelfAdjoint.I_smul_of_mem_skewAdjoint (h : a ∈ skewAdjoint A) :
    IsSelfAdjoint ((I : K) • a) := isSelfAdjoint_smul_of_mem_skewAdjoint I_mem_skewAdjoint h

end

section Instances

/-
**Real.instRCLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instRCLike : RCLike Real where re
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Real.instRCLike : RCLike ℝ where
  re := AddMonoidHom.id ℝ
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
/-
**RCLike.norm_nnqsmul** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_nnqsmul (q : Rat>=0) (x : E) : ‖q • x‖ = q • ‖x‖
参数：q : Rat>=0；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.norm_nnratCast`：norm_nnratCast (q : Rat>=0) : ‖(q : K)‖ = q
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma norm_nnqsmul (q : ℚ≥0) (x : E) : ‖q • x‖ = q • ‖x‖ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! norm_smul (q : K) x

variable (K) in
/-
**RCLike.nnnorm_nnqsmul** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nnnorm_nnqsmul (q : Rat>=0) (x : E) : ‖q • x‖₊ = q • ‖x‖₊
参数：q : Rat>=0；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.nnnorm_nnratCast`：nnnorm_nnratCast (q : Rat>=0) : ‖(q : K)‖₊ = q
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma nnnorm_nnqsmul (q : ℚ≥0) (x : E) : ‖q • x‖₊ = q • ‖x‖₊ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using! nnnorm_smul (q : K) x

@[bound]
/-
**RCLike.norm_expect_le** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_expect_le {ι : Type*} {s : Finset ι} {f : ι -> E} : ‖𝔼 i in s, f i‖ <
= 𝔼 i in s, ‖f i‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_expect_of_subadditive`：le_expect_of_subadditive (h_zero : m 0 
= 0) (h_add : forall a b, m (a + b) <= m a + m b) (h_div : forall (n : Nat) a, m
 (a /Rat n) = m a /Ra…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.norm_nnqsmul`：norm_nnqsmul (q : Rat>=0) (x : E) : ‖q • x‖ = q • ‖
x‖
-/
lemma norm_expect_le {ι : Type*} {s : Finset ι} {f : ι → E} : ‖𝔼 i ∈ s, f i‖ ≤ 𝔼 i ∈ s, ‖f i‖ :=
  Finset.le_expect_of_subadditive norm_zero norm_add_le fun _ _ ↦ by rw [norm_nnqsmul K]

end NormedField

section Order

open scoped ComplexOrder
variable {z w : K}

/-
**RCLike.lt_iff_re_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `RCLike.ext`：ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = 
w
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩
/-
**RCLike.nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
-/
theorem nonneg_iff : 0 ≤ z ↔ 0 ≤ re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)
/-
**RCLike.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
-/
theorem pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)
/-
**RCLike.nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：nonpos_iff : z <= 0 ↔ re z <= 0 ∧ im z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
-/
theorem nonpos_iff : z ≤ 0 ↔ re z ≤ 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)
/-
**RCLike.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
-/
theorem neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)
/-
**RCLike.nonneg_iff_exists_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nonneg_iff_exists_ofReal : 0 <= z ↔ exists x >= (0 : Real), x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma nonneg_iff_exists_ofReal : 0 ≤ z ↔ ∃ x ≥ (0 : ℝ), x = z := by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop
/-
**RCLike.pos_iff_exists_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：pos_iff_exists_ofReal : 0 < z ↔ exists x > (0 : Real), x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.pos_iff`：pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma pos_iff_exists_ofReal : 0 < z ↔ ∃ x > (0 : ℝ), x = z := by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop
/-
**RCLike.nonpos_iff_exists_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：nonpos_iff_exists_ofReal : z <= 0 ↔ exists x <= (0 : Real), x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.nonpos_iff`：nonpos_iff : z <= 0 ↔ re z <= 0 ∧ im z = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma nonpos_iff_exists_ofReal : z ≤ 0 ↔ ∃ x ≤ (0 : ℝ), x = z := by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop
/-
**RCLike.neg_iff_exists_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：neg_iff_exists_ofReal : z < 0 ↔ exists x < (0 : Real), x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.neg_iff`：neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma neg_iff_exists_ofReal : z < 0 ↔ ∃ x < (0 : ℝ), x = z := by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]
/-
**RCLike.ofReal_le_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_le_ofReal {x y : Real} : (x : K) <= (y : K) ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofReal_le_ofReal {x y : ℝ} : (x : K) ≤ (y : K) ↔ x ≤ y := by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]
/-
**RCLike.ofReal_lt_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_lt_ofReal {x y : Real} : (x : K) < (y : K) ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofReal_lt_ofReal {x y : ℝ} : (x : K) < (y : K) ↔ x < y := by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]
/-
**RCLike.ofReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_nonneg {x : Real} : 0 <= (x : K) ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用引理 `RCLike.ofReal_le_ofReal`：ofReal_le_ofReal {x y : Real} : (x : K) <= (y :
 K) ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofReal_nonneg {x : ℝ} : 0 ≤ (x : K) ↔ 0 ≤ x := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
/-
**RCLike.ofReal_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_nonpos {x : Real} : (x : K) <= 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用引理 `RCLike.ofReal_le_ofReal`：ofReal_le_ofReal {x y : Real} : (x : K) <= (y :
 K) ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofReal_nonpos {x : ℝ} : (x : K) ≤ 0 ↔ x ≤ 0 := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
/-
**RCLike.ofReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_pos {x : Real} : 0 < (x : K) ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用引理 `RCLike.ofReal_lt_ofReal`：ofReal_lt_ofReal {x y : Real} : (x : K) < (y : 
K) ↔ x < y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofReal_pos {x : ℝ} : 0 < (x : K) ↔ 0 < x := by
  rw [← ofReal_zero, ofReal_lt_ofReal]

@[simp, norm_cast]
/-
**RCLike.ofReal_lt_zero** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：ofReal_lt_zero {x : Real} : (x : K) < 0 ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用引理 `RCLike.ofReal_lt_ofReal`：ofReal_lt_ofReal {x y : Real} : (x : K) < (y : 
K) ↔ x < y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofReal_lt_zero {x : ℝ} : (x : K) < 0 ↔ x < 0 := by
  rw [← ofReal_zero, ofReal_lt_ofReal]
/-
**RCLike.norm_le_re_iff_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_le_re_iff_eq_norm {z : K} : ‖z‖ <= re z ↔ z = ‖z‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RCLike.re_le_norm`：re_le_norm (z : K) : re z <= ‖z‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.re_eq_self_of_le`：re_eq_self_of_le {a : K} (h : ‖a‖ <= re a) : (r
e a : K) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
-/
lemma norm_le_re_iff_eq_norm {z : K} :
    ‖z‖ ≤ re z ↔ z = ‖z‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h', re_eq_self_of_le h]
  · rw [h]
    simp
/-
**RCLike.re_le_neg_norm_iff_eq_neg_norm** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：re_le_neg_norm_iff_eq_neg_norm {z : K} : re z <= -‖z‖ ↔ z = -‖z‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `RCLike.norm_le_re_iff_eq_norm`：norm_le_re_iff_eq_norm {z : K} : ‖z‖ <= r
e z ↔ z = ‖z‖
-/
lemma re_le_neg_norm_iff_eq_neg_norm {z : K} :
    re z ≤ -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)
/-
**RCLike.norm_of_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_of_nonneg' {x : K} (hx : 0 <= x) : ‖x‖ = x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RCLike.norm_le_re_iff_eq_norm`：norm_le_re_iff_eq_norm {z : K} : ‖z‖ <= r
e z ↔ z = ‖z‖
· 使用定理 `RCLike.sqrt_normSq_eq_norm`：sqrt_normSq_eq_norm {z : K} : √(normSq z) = 
‖z‖
· 使用定理 `RCLike.normSq_apply`：normSq_apply (z : K) : normSq z = re z * re z + im 
z * im z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
-/
lemma norm_of_nonneg' {x : K} (hx : 0 ≤ x) : ‖x‖ = x := by
  rw [eq_comm, ← norm_le_re_iff_eq_norm, ← sqrt_normSq_eq_norm, normSq_apply]
  simp [nonneg_iff.mp hx]
/-
**RCLike.re_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjoint x) : 0 <= re x ↔ 0 <= x
参数：hx : IsSelfAdjoint x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.conj_eq_iff_im`：conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjoint x) : 0 ≤ re x ↔ 0 ≤ x := by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]
/-
**RCLike.re_le_re** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：re_le_re {x y : K} (h : x <= y) : re x <= re y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
-/
lemma re_le_re {x y : K} (h : x ≤ y) : re x ≤ re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1
/-
**RCLike.re_monotone** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：re_monotone : Monotone (re : K -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.re_le_re`：re_le_re {x y : K} (h : x <= y) : re x <= re y
-/
lemma re_monotone : Monotone (re : K → ℝ) :=
  fun _ _ => re_le_re
/-
**RCLike.inv_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] {z : K}, 0 < z → 0 < z⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.pos_iff_exists_ofReal`：pos_iff_exists_ofReal : 0 < z ↔ exists x >
 (0 : Real), x = z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻
¹
· 使用引理 `RCLike.ofReal_pos`：ofReal_pos {x : Real} : 0 < (x : K) ↔ 0 < x
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
protected lemma inv_pos_of_pos (hz : 0 < z) : 0 < z⁻¹ := by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx', ← ofReal_inv, ofReal_pos]
  exact inv_pos_of_pos hx
/-
**RCLike.inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K] {z : K}, 0 < z⁻¹ ↔ 0 < z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `RCLike.inv_pos_of_pos`：∀ {K : Type u_1} [inst : RCLike K] {z : K}, 0 < z
 → 0 < z⁻¹
-/
protected lemma inv_pos : 0 < z⁻¹ ↔ 0 < z := by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered rings.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)

Note this is only an instance with `open scoped ComplexOrder`. -/
/-
**RCLike.toStarOrderedRing** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：toStarOrderedRing : StarOrderedRing K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StarOrderedRing.of_nonneg_iff'`：of_nonneg_iff' [NonUnitalRing R] [Partia
lOrder R] [StarRing R] (h_add : forall {x y : R}, x <= y -> forall z, z + x <= z
 + y) (h_nonneg_iff …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered r
ings.
(That is, a star ring in which the nonnegative elements are those of the form `s
tar z * z`.)

Note this is only an instance with `open scoped ComplexOrder`.
-/
lemma toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h ↦ ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?_⟩
      rintro ⟨s, rfl⟩
      simp [mul_comm, mul_self_nonneg, add_nonneg])

scoped[ComplexOrder] attribute [instance] RCLike.toStarOrderedRing
/-
**RCLike.toZeroLEOneClass** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：toZeroLEOneClass : ZeroLEOneClass K where zero_le_one
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `RCLike.one_im`：one_im : im (1 : K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma toZeroLEOneClass : ZeroLEOneClass K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass
/-
**RCLike.toIsOrderedAddMonoid** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：toIsOrderedAddMonoid : IsOrderedAddMonoid K where add_le_add_left _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
-/
lemma toIsOrderedAddMonoid : IsOrderedAddMonoid K where
  add_le_add_left _ _ := add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
/-
**RCLike.toIsStrictOrderedRing** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：toIsStrictOrderedRing : IsStrictOrderedRing K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictOrderedRing.of_mul_pos`：IsStrictOrderedRing.of_mul_pos [Ring R] 
[PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [Nontrivial R] (mul_p
os : forall a b : R,…
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly order
ed rings.

Note this is only an instance with `open scoped ComplexOrder`.
-/
lemma toIsStrictOrderedRing : IsStrictOrderedRing K :=
  .of_mul_pos fun z w hz hw ↦ by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing
/-
**RCLike.toPosMulReflectLT** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：toPosMulReflectLT : PosMulReflectLT K where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `RCLike.is_real_TFAE`：is_real_TFAE (z : K) : TFAE [conj z = z, exists r :
 Real, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
· 使用定理 `lt_of_mul_lt_mul_of_nonneg_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1
 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLT α],   a * b < a * 
c → 0 ≤ a → b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 34 条，此处仅展示前 30 条）
-/
lemma toPosMulReflectLT : PosMulReflectLT K where
  elim := by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im, map_zero, map_zero, eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, mul_eq_mul_left_iff] at hyz ⊢
    refine ⟨lt_of_mul_lt_mul_of_nonneg_left hyz.1 <| by simpa using hx, hyz.2.resolve_right ?_⟩
    rintro rfl
    simp at hyz

scoped[ComplexOrder] attribute [instance] RCLike.toPosMulReflectLT
/-
**RCLike.toIsStrictOrderedModule** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：toIsStrictOrderedModule : IsStrictOrderedModule Real K where smul_lt_smul_
of_pos_left r hr a b hab
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.lt_iff_re_im`：lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `RCLike.toPosMulReflectLT`：toPosMulReflectLT : PosMulReflectLT K where el
im
· 使用定理 `RCLike.smul_im`：smul_im (r : Real) (z : K) : im (r • z) = r * im z
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem toIsStrictOrderedModule : IsStrictOrderedModule ℝ K where
  smul_lt_smul_of_pos_left r hr a b hab := by
    simpa [RCLike.lt_iff_re_im (K := K), smul_re, smul_im, hr, hr.ne'] using hab
  smul_lt_smul_of_pos_right a ha r₁ r₂ hr := by
    obtain ⟨hare, haim⟩ := RCLike.lt_iff_re_im.1 ha
    simp_all [RCLike.lt_iff_re_im (K := K), smul_re, smul_im]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedModule
/-
**RCLike.ofReal_mul_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_mul_pos_iff (x : Real) (z : K) : 0 < x * z ↔ (x < 0 ∧ z < 0) ∨ (0 <
 x ∧ 0 < z)
参数：x : Real；z : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.pos_iff`：pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : K) : im (↑r * z) = r
 * im z
· 使用定理 `RCLike.neg_iff`：neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
theorem ofReal_mul_pos_iff (x : ℝ) (z : K) :
    0 < x * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z) := by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, false_or]
  · simp only [mul_pos_iff, hx, true_and, not_lt_of_gt hx, false_and, or_false, mul_eq_zero,
      hx.ne', false_or]
/-
**RCLike.ofReal_mul_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_mul_neg_iff (x : Real) (z : K) : x * z < 0 ↔ (x < 0 ∧ 0 < z) ∨ (0 <
 x ∧ z < 0)
参数：x : Real；z : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `RCLike.ofReal_mul_pos_iff`：ofReal_mul_pos_iff (x : Real) (z : K) : 0 < x
 * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z)
-/
theorem ofReal_mul_neg_iff (x : ℝ) (z : K) :
    x * z < 0 ↔ (x < 0 ∧ 0 < z) ∨ (0 < x ∧ z < 0) := by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)
/-
**RCLike.instPosMulReflectLE** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：instPosMulReflectLE : PosMulReflectLE K where elim a b c h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RCLike.pos_iff_exists_ofReal`：pos_iff_exists_ofReal : 0 < z ↔ exists x >
 (0 : Real), x = z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RCLike.ofReal_mul_pos_iff`：ofReal_mul_pos_iff (x : Real) (z : K) : 0 < x
 * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `mul_eq_zero_iff_left`：mul_eq_zero_iff_left (ha : a != 0) : a * b = 0 ↔ b
 = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RCLike.ofReal_ne_zero`：ofReal_ne_zero {x : Real} : (x : K) != 0 ↔ x != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma instPosMulReflectLE : PosMulReflectLE K where
  elim a b c h := by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for https://github.com/leanprover/lean4/issues/7717 -/
    beta_reduce at h
    rw [← ha2, ← sub_nonneg, ← mul_sub, le_iff_lt_or_eq] at h
    rcases h with h | h
    · rw [ofReal_mul_pos_iff] at h
      exact le_of_lt <| h.rec (False.elim <| not_lt_of_gt ·.1 ha1) (·.2)
    · exact ((mul_eq_zero_iff_left <| ofReal_ne_zero.mpr ha1.ne').mp h.symm).ge

scoped[ComplexOrder] attribute [instance] RCLike.instPosMulReflectLE
/-
**RCLike.instMulPosReflectLE** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：instMulPosReflectLE : MulPosReflectLE K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulReflectLE.toMulPosReflectLE`：PosMulReflectLE.toMulPosReflectLE [Po
sMulReflectLE α] : MulPosReflectLE α
· 使用引理 `RCLike.instPosMulReflectLE`：instPosMulReflectLE : PosMulReflectLE K wher
e elim a b c h
-/
lemma instMulPosReflectLE : MulPosReflectLE K := PosMulReflectLE.toMulPosReflectLE

scoped[ComplexOrder] attribute [instance] RCLike.instMulPosReflectLE

end Order

section CleanupLemmas

local notation "reR" => @RCLike.re ℝ _
local notation "imR" => @RCLike.im ℝ _
local notation "IR" => @RCLike.I ℝ _
local notation "normSqR" => @RCLike.normSq ℝ _

@[simp, rclike_simps]
/-
**RCLike.re_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：re_to_real {x : Real} : reR x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.im_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：im_to_real {x : Real} : imR x = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl

@[rclike_simps]
/-
**RCLike.conj_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conj_to_real {x : Real} : conj x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.I_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：I_to_real : IR = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem I_to_real : IR = 0 :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.normSq_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：normSq_to_real {x : Real} : normSq x = x * x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [RCLike.normSq]

@[simp]
/-
**RCLike.ofReal_real_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofReal_real_eq_id : @ofReal Real _ = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl

end CleanupLemmas

section LinearMaps

/-- The real part in an `RCLike` field, as a linear map. -/
/-
**RCLike.reLm** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：reLm : K ->ₗ[Real] Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z

--- 原说明 ---
The real part in an `RCLike` field, as a linear map.
-/
noncomputable def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }

@[simp, rclike_simps]
/-
**RCLike.reLm_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：reLm_coe : (reLm : K -> Real) = re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl

/-- The real part in an `RCLike` field, as a continuous linear map. -/
/-
**RCLike.reCLM** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：reCLM : StrongDual Real K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real part in an `RCLike` field, as a continuous linear map.
-/
noncomputable def reCLM : StrongDual ℝ K :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]
/-
**RCLike.reCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：reCLM_coe : ((reCLM : StrongDual Real K) : K ->ₗ[Real] Real) = reLm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reCLM_coe : ((reCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.reCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：reCLM_apply : ((reCLM : StrongDual Real K) : K -> Real) = re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reCLM_apply : ((reCLM : StrongDual ℝ K) : K → ℝ) = re :=
  rfl

@[continuity, fun_prop]
/-
**RCLike.continuous_re** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：continuous_re : Continuous (re : K -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_re : Continuous (re : K → ℝ) :=
  reCLM.continuous

/-- The imaginary part in an `RCLike` field, as a linear map. -/
/-
**RCLike.imLm** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：imLm : K ->ₗ[Real] Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.smul_im`：smul_im (r : Real) (z : K) : im (r • z) = r * im z

--- 原说明 ---
The imaginary part in an `RCLike` field, as a linear map.
-/
noncomputable def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }

@[simp, rclike_simps]
/-
**RCLike.imLm_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：imLm_coe : (imLm : K -> Real) = im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl

/-- The imaginary part in an `RCLike` field, as a continuous linear map. -/
/-
**RCLike.imCLM** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：imCLM : StrongDual Real K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The imaginary part in an `RCLike` field, as a continuous linear map.
-/
noncomputable def imCLM : StrongDual ℝ K :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]
/-
**RCLike.imCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：imCLM_coe : ((imCLM : StrongDual Real K) : K ->ₗ[Real] Real) = imLm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imCLM_coe : ((imCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.imCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：imCLM_apply : ((imCLM : StrongDual Real K) : K -> Real) = im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imCLM_apply : ((imCLM : StrongDual ℝ K) : K → ℝ) = im :=
  rfl

@[continuity, fun_prop]
/-
**RCLike.continuous_im** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：continuous_im : Continuous (im : K -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_im : Continuous (im : K → ℝ) :=
  imCLM.continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
/-
**RCLike.conjAe** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：conjAe : K ≃ₐ[Real] K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)

--- 原说明 ---
Conjugate as an `ℝ`-algebra equivalence
-/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, rclike_simps]
/-
**RCLike.conjAe_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conjAe_coe : (conjAe : K -> K) = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl

/-- Conjugate as a linear isometry -/
/-
**RCLike.conjLIE** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：conjLIE : K ≃ₗᵢ[Real] K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖

--- 原说明 ---
Conjugate as a linear isometry
-/
noncomputable def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]
/-
**RCLike.conjLIE_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conjLIE_apply : (conjLIE : K -> K) = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjLIE_apply : (conjLIE : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
/-
**RCLike.conjCLE** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：conjCLE : K ≃L[Real] K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugate as a continuous linear equivalence
-/
noncomputable def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _

@[simp, rclike_simps]
/-
**RCLike.conjCLE_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.conjCLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：conjCLE_apply : (conjCLE : K -> K) = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjCLE_apply : (conjCLE : K → K) = conj :=
  rfl
/-
**RCLike.** 是 Mathlib 中的一个实例，位于命名空间 `RCLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity]
/-
**RCLike.continuous_conj** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：continuous_conj : Continuous (conj : K -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
-/
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The `ℝ → K` coercion, as an algebra map. -/
/-
**RCLike.ofRealAm** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：ofRealAm : Real ->ₐ[Real] K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ → K` coercion, as an algebra map.
-/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K

@[simp, rclike_simps]
/-
**RCLike.ofRealAm_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofRealAm_coe : (ofRealAm : Real -> K) = ofReal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = ofReal :=
  rfl

variable (K) in
/-- The `ℝ → K` coercion, as a ⋆-algebra map. -/
/-
**RCLike.ofRealStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：ofRealStarAlgHom : Real ->⋆ₐ[Real] K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K

--- 原说明 ---
The `ℝ → K` coercion, as a ⋆-algebra map.
-/
noncomputable def ofRealStarAlgHom : ℝ →⋆ₐ[ℝ] K := .ofId ℝ K
/-
**RCLike.coe_ofRealStarAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K], ⇑(RCLike.ofRealStarAlgHom K) = RCLike.
ofReal
参数：RCLike.ofRealStarAlgHom K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_ofRealStarAlgHom : (ofRealStarAlgHom K : ℝ → K) = ofReal := rfl
/-
**RCLike.toAlgHom_ofRealStarAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K], ↑(RCLike.ofRealStarAlgHom K) = RCLike.
ofRealAm
参数：RCLike.ofRealStarAlgHom K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAlgHom_ofRealStarAlgHom : (ofRealStarAlgHom K).toAlgHom = ofRealAm := rfl

/-- The ℝ → K coercion, as a linear isometry -/
/-
**RCLike.ofRealLI** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：ofRealLI : Real ->ₗᵢ[Real] K where toLinearMap
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|

--- 原说明 ---
The ℝ → K coercion, as a linear isometry
-/
noncomputable def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]
/-
**RCLike.ofRealLI_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofRealLI_apply : (ofRealLI : Real -> K) = ofReal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealLI_apply : (ofRealLI : ℝ → K) = ofReal :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
/-
**RCLike.ofRealCLM** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：ofRealCLM : Real ->L[Real] K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ → K` coercion, as a continuous linear map
-/
noncomputable def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]
/-
**RCLike.ofRealCLM_coe** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofRealCLM_coe : (@ofRealCLM K _ : Real ->ₗ[Real] K) = ofRealAm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealCLM_coe : (@ofRealCLM K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, rclike_simps]
/-
**RCLike.ofRealCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：ofRealCLM_apply : (ofRealCLM : Real -> K) = ofReal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRealCLM_apply : (ofRealCLM : ℝ → K) = ofReal :=
  rfl

@[continuity, fun_prop]
/-
**RCLike.continuous_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：continuous_ofReal : Continuous (ofReal : Real -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_
5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂}
 [inst_2 : Semi…
-/
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLI.continuous

@[continuity]
/-
**RCLike.continuous_normSq** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：continuous_normSq : Continuous (normSq : K -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `RCLike.continuous_im`：continuous_im : Continuous (im : K -> Real)
-/
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)
/-
**RCLike.lipschitzWith_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：lipschitzWith_ofReal : LipschitzWith 1 (ofReal : Real -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.lipschitz`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
theorem lipschitzWith_ofReal : LipschitzWith 1 (ofReal : ℝ → K) :=
  ofRealLI.lipschitz
/-
**RCLike.lipschitzWith_re** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：lipschitzWith_re : LipschitzWith 1 (re (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `enorm_le_iff_norm_le`：∀ {E : Type u_5} {F : Type u_6} [inst : Seminormed
AddGroup E] [inst_1 : SeminormedAddGroup F] {x : E} {y : F},   ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖
 ≤ ‖y‖
· 使用定理 `RCLike.norm_re_le_norm`：norm_re_le_norm (z : K) : ‖re z‖ <= ‖z‖
-/
lemma lipschitzWith_re : LipschitzWith 1 (re (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [map_sub re x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)
/-
**RCLike.lipschitzWith_im** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：lipschitzWith_im : LipschitzWith 1 (im (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `enorm_le_iff_norm_le`：∀ {E : Type u_5} {F : Type u_6} [inst : Seminormed
AddGroup E] [inst_1 : SeminormedAddGroup F] {x : E} {y : F},   ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖
 ≤ ‖y‖
· 使用定理 `RCLike.norm_im_le_norm`：norm_im_le_norm (z : K) : ‖im z‖ <= ‖z‖
-/
lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

/-- The canonical map between `RCLike` types. It maps `x : 𝕜` to `re x + im x * I`. -/
/-
**RCLike.map** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：(𝕜 : Type u_3) → (𝕜' : Type u_4) → [inst : RCLike 𝕜] → [inst_1 : RCLike 𝕜'
] → 𝕜 →L[ℝ] 𝕜'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map between `RCLike` types. It maps `x : 𝕜` to `re x + im x * I`.
-/
@[simps] def map (𝕜 𝕜' : Type*) [RCLike 𝕜] [RCLike 𝕜'] : 𝕜 →L[ℝ] 𝕜' where
  toFun x := re x + im x * (I : 𝕜')
  map_add' _ _ := by simp only [map_add, add_mul]; ring
  map_smul' _ _ := by simp [real_smul_eq_coe_mul, mul_assoc]
/-
**RCLike.map_same_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K], RCLike.map K K = ContinuousLinearMap.i
d ℝ K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem map_same_eq_id : map K K = .id ℝ K := by ext; simp
/-
**RCLike.map_to_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K], RCLike.map K ℝ = RCLike.reCLM
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
@[simp] theorem map_to_real : map K ℝ = reCLM := by
  ext; simp only [map_apply, I, mul_zero, add_zero]; rfl
/-
**RCLike.map_from_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {K : Type u_1} [inst : RCLike K], RCLike.map ℝ K = RCLike.ofRealCLM
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.one_im`：one_im : im (1 : K) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem map_from_real : map ℝ K = ofRealCLM := by ext; simp

open scoped ComplexOrder in
/-
**RCLike.instOrderClosedTopology** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：instOrderClosedTopology : OrderClosedTopology K where isClosed_le'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `RCLike.continuous_im`：continuous_im : Continuous (im : K -> Real)
-/
lemma instOrderClosedTopology : OrderClosedTopology K where
  isClosed_le' := by
    conv in _ ≤ _ => rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> fun_prop

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosedTopology

end LinearMaps

/-!
### ℝ-dependent results

Here we gather results that depend on whether `K` is `ℝ`.
-/
section CaseSpecific

/-
**RCLike.im_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0
参数：h : I = (0 : K)；z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0 := by
  rw [← re_add_im z, h]
  simp

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when `RCLike.I = 0`. -/
@[simps]
/-
**RCLike.realRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：realRingEquiv (h : I = (0 : K)) : K ≃+* Real where toFun
参数：h : I = (0 : K)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r

--- 原说明 ---
The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when `RCLike.I
 = 0`.
-/
def realRingEquiv (h : I = (0 : K)) : K ≃+* ℝ where
  toFun := re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when
`RCLike.I = 0`. -/
@[simps]
/-
**RCLike.realLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：realLinearIsometryEquiv (h : I = (0 : K)) : K ≃ₗᵢ[Real] Real where map_smu
l'
参数：h : I = (0 : K)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z

--- 原说明 ---
The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` an
d `ℝ` when
`RCLike.I = 0`.
-/
noncomputable def realLinearIsometryEquiv (h : I = (0 : K)) : K ≃ₗᵢ[ℝ] ℝ where
  map_smul' := smul_re
  norm_map' z := by rw [← re_add_im z]; simp [-re_add_im, h]
  __ := realRingEquiv h

end CaseSpecific

/-
**RCLike.norm_le_im_iff_eq_I_mul_norm** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_le_im_iff_eq_I_mul_norm {z : K} : ‖z‖ <= im z ↔ z = I * ‖z‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.im_eq_zero`：im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `RCLike.norm_I_of_ne_zero`：norm_I_of_ne_zero (hI : (I : K) != 0) : ‖(I : 
K)‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
（共 36 条，此处仅展示前 30 条）
-/
lemma norm_le_im_iff_eq_I_mul_norm {z : K} :
    ‖z‖ ≤ im z ↔ z = I * ‖z‖ := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) ≠ 0 := fun _ ↦ by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert! norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero this, norm_I_of_ne_zero this]
/-
**RCLike.im_le_neg_norm_iff_eq_neg_I_mul_norm** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`
。
形式化陈述：im_le_neg_norm_iff_eq_neg_I_mul_norm {z : K} : im z <= -‖z‖ ↔ z = -(I * ‖z
‖)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `RCLike.norm_le_im_iff_eq_I_mul_norm`：norm_le_im_iff_eq_I_mul_norm {z : K
} : ‖z‖ <= im z ↔ z = I * ‖z‖
-/
lemma im_le_neg_norm_iff_eq_neg_I_mul_norm {z : K} :
    im z ≤ -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

end RCLike

namespace AddChar
variable {G : Type*} [Finite G]

/-
**AddChar.inv_apply_eq_conj** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：inv_apply_eq_conj [AddLeftCancelMonoid G] (ψ : AddChar G K) (x : G) : (ψ x
)⁻¹ = conj (ψ x)
参数：ψ : AddChar G K；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.inv_eq_conj`：inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z
· 使用定理 `AddChar.norm_apply`：∀ {α : Type u_1} [inst : NormedRing α] [NormMulClass
 α] [NormOneClass α] {G : Type u_3} [inst_3 : AddLeftCancelMonoid G]   [Finite G
] (ψ : A…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
lemma inv_apply_eq_conj [AddLeftCancelMonoid G] (ψ : AddChar G K) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  RCLike.inv_eq_conj <| norm_apply _ _
/-
**AddChar.map_neg_eq_conj** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj
 (ψ x)
参数：ψ : AddChar G K；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用引理 `AddChar.inv_apply_eq_conj`：inv_apply_eq_conj [AddLeftCancelMonoid G] (ψ 
: AddChar G K) (x : G) : (ψ x)⁻¹ = conj (ψ x)
-/
lemma map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv, inv_apply_eq_conj]

end AddChar

section

/-- A mixin over a normed field, saying that the norm field structure is the same as `ℝ` or `ℂ`.
To endow such a field with a compatible `RCLike` structure in a proof, use
`letI := IsRCLikeNormedField.rclike 𝕜`. -/
/-
**IsRCLikeNormedField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_3) → [hk : NormedField 𝕜] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin over a normed field, saying that the norm field structure is the same as
 `ℝ` or `ℂ`.
To endow such a field with a compatible `RCLike` structure in a proof, use
`letI := IsRCLikeNormedField.rclike 𝕜`.
-/
class IsRCLikeNormedField (𝕜 : Type*) [hk : NormedField 𝕜] : Prop where
  out : ∃ h : RCLike 𝕜, hk = h.toNormedField
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (𝕜 : Type*) [h : RCLike 𝕜] : IsRCLikeNormedField 𝕜 := ⟨⟨h, rfl⟩⟩

/-- A copy of an `RCLike` field in which the `NormedField` field is adjusted to be become defeq
to a propeq one. -/
@[instance_reducible]
/-
**RCLike.copy_of_normedField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RCLike.copy_of_normedField {𝕜 : Type*} (h : RCLike 𝕜) (hk : NormedField 𝕜)
 (h'' : hk = h.toNormedField) : RCLike 𝕜 where __
参数：h : RCLike 𝕜；hk : NormedField 𝕜；h'' : hk = h.toNormedField。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of an `RCLike` field in which the `NormedField` field is adjusted to be b
ecome defeq
to a propeq one.
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
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `𝕜` which is definitionally compatible with the given normed field structure. -/
@[instance_reducible]
/-
**IsRCLikeNormedField.rclike** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsRCLikeNormedField.rclike (𝕜 : Type*) [hk : NormedField 𝕜] [h : IsRCLikeN
ormedField 𝕜] : RCLike 𝕜
参数：𝕜 : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsRCLikeNormedField.out`：∀ {𝕜 : Type u_3} {hk : NormedField 𝕜} [self : I
sRCLikeNormedField 𝕜], ∃ h, hk = h.toNormedField

--- 原说明 ---
Given a normed field `𝕜` satisfying `IsRCLikeNormedField 𝕜`, build an associated
 `RCLike 𝕜`
structure on `𝕜` which is definitionally compatible with the given normed field 
structure.
-/
noncomputable def IsRCLikeNormedField.rclike (𝕜 : Type*)
    [hk : NormedField 𝕜] [h : IsRCLikeNormedField 𝕜] : RCLike 𝕜 := by
  choose p hp using h.out
  exact p.copy_of_normedField hk hp

end

namespace LinearIsometryEquiv
variable {𝕜 V W G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [Module 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Left scalar multiplication of a unit with norm one and a linear isometric equivalence,
as a linear isometric equivalence. -/
/-
**LinearIsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left scalar multiplication of a unit with norm one and a linear isometric equiva
lence,
as a linear isometric equivalence.
-/
instance : SMul (unitary 𝕜) (V ≃ₗᵢ[𝕜] W) where smul α e :=
  { __ := Unitary.toUnits α • e.toLinearEquiv
    norm_map' _ := by simp [norm_smul] }
/-
**LinearIsometryEquiv.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {𝕜 : Type u_3} {V : Type u_4} {W : Type u_5} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup V]   [inst_2 : _root_.Module 𝕜 V] [inst_3 : SeminormedAd
dCommGroup W] [inst_4 : NormedSpace 𝕜 W] (e : V ≃ₗᵢ[𝕜] W)   (α : ↥(unitary 𝕜)) (
x : V), (α • e) x = ↑α • e x
参数：e : V ≃ₗᵢ[𝕜] W；α : ↥(unitary 𝕜)；x : V；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V) :
    (α • e) x = (α : 𝕜) • e x := rfl
/-
**LinearIsometryEquiv.symm_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：symm_smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : W) : (α • e).symm x 
= (↑α⁻¹ : 𝕜) • e.symm x
参数：e : V ≃ₗᵢ[𝕜] W；α : unitary 𝕜；x : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : W) :
    (α • e).symm x = (↑α⁻¹ : 𝕜) • e.symm x := rfl
/-
**LinearIsometryEquiv.symm_units_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：∀ {𝕜 : Type u_3} {W : Type u_5} {G : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup W]   [inst_2 : NormedSpace 𝕜 W] [inst_3 : SeminormedAddC
ommGroup G] [inst_4 : NormedSpace 𝕜 G] (e : G ≃ₗᵢ[𝕜] W)   (α : ↥(unitary 𝕜)), (α
 • e).symm = α⁻¹ • e.symm
参数：e : G ≃ₗᵢ[𝕜] W；α : ↥(unitary 𝕜)；α • e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem symm_units_smul (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).symm = α⁻¹ • e.symm := by ext; simp [symm_smul_apply]
/-
**LinearIsometryEquiv.toLinearEquiv_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：∀ {𝕜 : Type u_3} {V : Type u_4} {W : Type u_5} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup V]   [inst_2 : _root_.Module 𝕜 V] [inst_3 : SeminormedAd
dCommGroup W] [inst_4 : NormedSpace 𝕜 W] (e : V ≃ₗᵢ[𝕜] W)   (α : ↥(unitary 𝕜)), 
(α • e).toLinearEquiv = Unitary.toUnits α • e.toLinearEquiv
参数：e : V ≃ₗᵢ[𝕜] W；α : ↥(unitary 𝕜)；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearEquiv_smul (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).toLinearEquiv = Unitary.toUnits α • e.toLinearEquiv := rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_3} {W : Type u_5} {G : Type u_6} [inst : RCLike 𝕜] [inst_1 :
 SeminormedAddCommGroup W]   [inst_2 : NormedSpace 𝕜 W] [inst_3 : SeminormedAddC
ommGroup G] [inst_4 : NormedSpace 𝕜 G] (e : G ≃ₗᵢ[𝕜] W)   (α : ↥(unitary 𝕜)), ↑(
α • e) = Unitary.toUnits α • ↑e
参数：e : G ≃ₗᵢ[𝕜] W；α : ↥(unitary 𝕜)；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toContinuousLinearEquiv_smul (e : G ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) :
    (α • e).toContinuousLinearEquiv = Unitary.toUnits α • e.toContinuousLinearEquiv := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**LinearIsometryEquiv.smul_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：smul_trans (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) : (α • e).tra
ns f = α • (e.trans f)
参数：α : unitary 𝕜；e : V ≃ₗᵢ[𝕜] G；f : G ≃ₗᵢ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_trans (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) :
    (α • e).trans f = α • (e.trans f) := by ext; simp
/-
**LinearIsometryEquiv.trans_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：trans_smul (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) : e.trans (α 
• f) = α • (e.trans f)
参数：α : unitary 𝕜；e : V ≃ₗᵢ[𝕜] G；f : G ≃ₗᵢ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_smul (α : unitary 𝕜) (e : V ≃ₗᵢ[𝕜] G) (f : G ≃ₗᵢ[𝕜] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

end LinearIsometryEquiv

