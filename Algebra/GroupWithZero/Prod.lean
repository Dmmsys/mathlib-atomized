/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Products of monoids with zero, groups with zero

In this file we define `MonoidWithZero`, `GroupWithZero`, etc... instances for `M₀ × N₀`.

## Main declarations

* `mulMonoidWithZeroHom`: Multiplication bundled as a monoid with zero homomorphism.
* `divMonoidWithZeroHom`: Division bundled as a monoid with zero homomorphism.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {M₀ N₀ : Type*}

namespace Prod

/-
**Prod.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMulZeroClass [MulZeroClass M₀] [MulZeroClass N₀] : MulZeroClass (M₀ × 
N₀) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass M₀] [MulZeroClass N₀] : MulZeroClass (M₀ × N₀) where
  zero_mul := by simp [Prod.mul_def]
  mul_zero := by simp [Prod.mul_def]
/-
**Prod.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero M₀] [SemigroupWithZero N₀] : Semi
groupWithZero (M₀ × N₀) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero M₀] [SemigroupWithZero N₀] :
    SemigroupWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp
/-
**Prod.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass M₀] [MulZeroOneClass N₀] : MulZeroOne
Class (M₀ × N₀) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulZeroOneClass M₀] [MulZeroOneClass N₀] :
    MulZeroOneClass (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp
/-
**Prod.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMonoidWithZero [MonoidWithZero M₀] [MonoidWithZero N₀] : MonoidWithZer
o (M₀ × N₀) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [MonoidWithZero M₀] [MonoidWithZero N₀] : MonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp
/-
**Prod.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCommMonoidWithZero [CommMonoidWithZero M₀] [CommMonoidWithZero N₀] : C
ommMonoidWithZero (M₀ × N₀) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero [CommMonoidWithZero M₀] [CommMonoidWithZero N₀] :
    CommMonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

end Prod

variable (M₀) in
@[simp]
/-
**WithZero.ofClass_withZeroUnitsEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithZero.ofClass_withZeroUnitsEquiv [GroupWithZero M₀] [DecidablePred fun 
x : M₀ => x = 0] : .ofClass WithZero.withZeroUnitsEquiv = WithZero.lift' (Units.
coeHom M₀)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma WithZero.ofClass_withZeroUnitsEquiv [GroupWithZero M₀]
    [DecidablePred fun x : M₀ ↦ x = 0] :
    .ofClass WithZero.withZeroUnitsEquiv =
      WithZero.lift' (Units.coeHom M₀) :=
  rfl

/-! ### Multiplication and division as homomorphisms -/

section BundledMulDiv

/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
/-
**mulMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulMonoidWithZeroHom [CommMonoidWithZero M₀] : M₀ × M₀ ->*₀ M₀ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication as a multiplicative homomorphism with zero.
-/
def mulMonoidWithZeroHom [CommMonoidWithZero M₀] : M₀ × M₀ →*₀ M₀ where
  __ := mulMonoidHom
  map_zero' := mul_zero _

/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
/-
**divMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：divMonoidWithZeroHom [CommGroupWithZero M₀] : M₀ × M₀ ->*₀ M₀ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division as a multiplicative homomorphism with zero.
-/
def divMonoidWithZeroHom [CommGroupWithZero M₀] : M₀ × M₀ →*₀ M₀ where
  __ := divMonoidHom
  map_zero' := zero_div _

end BundledMulDiv

