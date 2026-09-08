/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Emily Riehl, Wrenna Robson
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Equivalences involving `Bool`

This file shows that `not : Bool → Bool` is an equivalence and derives some consequences
-/

@[expose] public section

/-- The boolean negation function `not : Bool → Bool` is an involution and thus an equivalence. -/
@[simps!]
/-
**Equiv.boolNot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.boolNot : Equiv.Perm Bool
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.involutive_not`：Function.Involutive not

--- 原说明 ---
The boolean negation function `not : Bool → Bool` is an involution and thus an e
quivalence.
-/
def Equiv.boolNot : Equiv.Perm Bool := Bool.involutive_not.toPerm

namespace Bool

open Function

/-
**Bool.not_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_bijective : Bijective not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem not_bijective : Bijective not := Equiv.boolNot.bijective
/-
**Bool.not_injective** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_injective : Injective not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem not_injective : Injective not := Equiv.boolNot.injective
/-
**Bool.not_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_surjective : Surjective not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem not_surjective : Surjective not := Equiv.boolNot.surjective
/-
**Bool.not_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_leftInverse : LeftInverse not not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem not_leftInverse : LeftInverse not not := not_not
/-
**Bool.not_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_rightInverse : RightInverse not not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
-/
theorem not_rightInverse : RightInverse not not := not_not
/-
**Bool.not_hasLeftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_hasLeftInverse : HasLeftInverse not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.not_leftInverse`：not_leftInverse : LeftInverse not not
-/
theorem not_hasLeftInverse : HasLeftInverse not := ⟨not, not_leftInverse⟩
/-
**Bool.not_hasRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_hasRightInverse : HasRightInverse not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.not_rightInverse`：not_rightInverse : RightInverse not not
-/
theorem not_hasRightInverse : HasRightInverse not := ⟨not, not_rightInverse⟩

end Bool

