/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Finite.Basic

/-!
# Make `fun_prop` work for finite (multiplicative) support

We define a new predicate `HasFiniteMulSupport` (and its additivized version) on functions
and provide the infrastructure so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support. The relevant API lemmas
are provided in [Mathlib.Algebra.FiniteSupport.Basic](Mathlib/Algebra/FiniteSupport/Basic.lean).
-/

@[expose] public section

namespace Function

variable {α M : Type*} [One M]

/-- The function `f` has finite multiplicative support. -/
@[to_additive (attr := fun_prop) /-- The function `f` has finite support. -/]
/-
**Function.HasFiniteMulSupport** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：HasFiniteMulSupport (f : α -> M) : Prop
参数：f : α -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `f` has finite multiplicative support.
-/
def HasFiniteMulSupport (f : α → M) : Prop := f.mulSupport.Finite

@[to_additive (attr := fun_prop)]
/-
**Function.hasFiniteMulSupport_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：hasFiniteMulSupport_one : HasFiniteMulSupport fun _ : α => (1 : M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
-/
lemma hasFiniteMulSupport_one : HasFiniteMulSupport fun _ : α ↦ (1 : M) := by
  simp [HasFiniteMulSupport]

end Function

end

