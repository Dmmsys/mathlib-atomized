/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Image of `Zsqrtd` in `ℝ`

This file defines `Zsqrtd.toReal` and related lemmas.
It is in a separate file to avoid pulling in all of `Data.Real` into `Data.Zsqrtd`.
-/

@[expose] public section


namespace Zsqrtd

/-- The image of `Zsqrtd` in `ℝ`, using `Real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `toReal h (star a)`. -/
@[simps!]
/-
**Zsqrtd.toReal** 是 Mathlib 中的一个定义，位于命名空间 `Zsqrtd`。
形式化陈述：toReal {d : Int} (h : 0 <= d) : Int√d ->+* Real
参数：h : 0 <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `Zsqrtd` in `ℝ`, using `Real.sqrt` which takes the positive root of
 `d`.

If the negative root is desired, use `toReal h (star a)`.
-/
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg h)⟩
/-
**Zsqrtd.toReal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Zsqrtd`。
形式化陈述：toReal_injective {d : Int} (h0d : 0 <= d) (hd : forall n : Int, d != n * n
) : Function.Injective (toReal h0d)
参数：h0d : 0 <= d；hd : forall n : Int, d != n * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.lift_injective`：lift_injective [CharZero R] {d : Int} (r : { r : 
R // r * r = ↑d }) (hd : forall n : Int, d != n * n) : Function.Injective (lift 
r)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd

end Zsqrtd

