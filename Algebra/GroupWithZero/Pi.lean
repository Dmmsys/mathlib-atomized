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

variable {ι : Type*} {α : ι → Type*}

namespace Pi

section MulZeroClass
variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

/-
**Pi.mulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulZeroClass : MulZeroClass (forall i, α i) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulZeroClass : MulZeroClass (∀ i, α i) where
  zero_mul := by intros; ext; exact zero_mul _
  mul_zero := by intros; ext; exact mul_zero _

/-- The multiplicative homomorphism including a single `MulZeroClass`
into a dependent family of `MulZeroClass`es, as functions supported at a point.

This is the `MulHom` version of `Pi.single`. -/
@[simps]
/-
**Pi._root_.MulHom.single** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative homomorphism including a single `MulZeroClass`
into a dependent family of `MulZeroClass`es, as functions supported at a point.

This is the `MulHom` version of `Pi.single`.
-/
def _root_.MulHom.single (i : ι) : α i →ₙ* ∀ i, α i where
  toFun := Pi.single i
  map_mul' := Pi.single_op₂ (fun _ ↦ (· * ·)) (fun _ ↦ zero_mul _) _
/-
**Pi.single_mul** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：single_mul (i : ι) (x y : α i) : single i (x * y) = single i x * single i 
y
参数：i : ι；x y : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 :
 Mul N] (f : M →ₙ* N) (a b : M), f (a * b) = f a * f b
-/
lemma single_mul (i : ι) (x y : α i) : single i (x * y) = single i x * single i y :=
  (MulHom.single _).map_mul _ _
/-
**Pi.single_mul_left_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：single_mul_left_apply (i j : ι) (a : α i) (f : forall i, α i) : single i (
a * f i) j = single i a j * f j
参数：i j : ι；a : α i；f : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma single_mul_left_apply (i j : ι) (a : α i) (f : ∀ i, α i) :
    single i (a * f i) j = single i a j * f j :=
  (apply_single (fun i ↦ (· * f i)) (fun _ ↦ zero_mul _) _ _ _).symm
/-
**Pi.single_mul_right_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：single_mul_right_apply (i j : ι) (f : forall i, α i) (a : α i) : single i 
(f i * a) j = f j * single i a j
参数：i j : ι；f : forall i, α i；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma single_mul_right_apply (i j : ι) (f : ∀ i, α i) (a : α i) :
    single i (f i * a) j = f j * single i a j :=
  (apply_single (f · * ·) (fun _ ↦ mul_zero _) _ _ _).symm
/-
**Pi.single_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：single_mul_left (a : α i) : single i (a * f i) = single i a * f
参数：a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.single_mul_left_apply`：single_mul_left_apply (i j : ι) (a : α i) (f :
 forall i, α i) : single i (a * f i) j = single i a j * f j
-/
lemma single_mul_left (a : α i) : single i (a * f i) = single i a * f :=
  funext fun _ ↦ single_mul_left_apply _ _ _ _
/-
**Pi.single_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：single_mul_right (a : α i) : single i (f i * a) = f * single i a
参数：a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.single_mul_right_apply`：single_mul_right_apply (i j : ι) (f : forall 
i, α i) (a : α i) : single i (f i * a) j = f j * single i a j
-/
lemma single_mul_right (a : α i) : single i (f i * a) = f * single i a :=
  funext fun _ ↦ single_mul_right_apply _ _ _ _

end MulZeroClass

/-
**Pi.mulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulZeroOneClass [forall i, MulZeroOneClass (α i)] : MulZeroOneClass (foral
l i, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulZeroOneClass [∀ i, MulZeroOneClass (α i)] : MulZeroOneClass (∀ i, α i) where
  __ := mulZeroClass
  __ := mulOneClass
/-
**Pi.monoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：monoidWithZero [forall i, MonoidWithZero (α i)] : MonoidWithZero (forall i
, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidWithZero [∀ i, MonoidWithZero (α i)] : MonoidWithZero (∀ i, α i) where
  __ := monoid
  __ := mulZeroClass
/-
**Pi.commMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：commMonoidWithZero [forall i, CommMonoidWithZero (α i)] : CommMonoidWithZe
ro (forall i, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoidWithZero [∀ i, CommMonoidWithZero (α i)] : CommMonoidWithZero (∀ i, α i) where
  __ := monoidWithZero
  __ := commMonoid
/-
**Pi.semigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：semigroupWithZero [forall i, SemigroupWithZero (α i)] : SemigroupWithZero 
(forall i, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semigroupWithZero [∀ i, SemigroupWithZero (α i)] : SemigroupWithZero (∀ i, α i) where
  __ := semigroup
  __ := mulZeroClass

end Pi

