/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Small.Defs

/-!
# UnivLE

A proposition expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type u, Small.{v} α`.

This API indirectly provides an instance for `Small.{u, max u v}`, which could not be declared
directly due to https://github.com/leanprover/lean4/issues/2297.

See the doc-string for the comparison with an alternative stronger definition.
-/

public section

universe u v w

noncomputable section

/--
A class expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`.

There used to be a stronger definition `∀ α : Type max u v, Small.{v} α` that immediately implies
`Small.{v} ((α : Type u) → (β : Type v))` which is essential for proving that `Type v` has
`Type u`-indexed limits when `u ≤ v`. However the current weaker condition
`∀ α : Type u, Small.{v} α` also implies the same, so we switched to use it for
its simplicity and transitivity.

The strong definition easily implies the weaker definition (see below),
but we cannot prove the reverse implication.
This is because in Lean's type theory, while `max u v` is at least at big as `u` and `v`,
it could be bigger than both!
See also `Mathlib/CategoryTheory/UnivLE.lean` for the statement that the stronger definition is
equivalent to `EssSurj (uliftFunctor : Type v ⥤ Type max u v)`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, both universe parameters would default to
-- output (since there are no input parameters at all).
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ, mk_iff]
/-
**UnivLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class UnivLE : Prop where
  small (α : Type u) : Small.{v} α

attribute [instance] UnivLE.small


/- This is useless as an instance due to https://github.com/leanprover/lean4/issues/2297 -/
/-
**univLE_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univLE_max : UnivLE.{u, max u v} where small α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `small_max`：small_max (α : Type v) : Small.{max w v} α

--- 原说明 ---
This is useless as an instance due to https://github.com/leanprover/lean4/issues
/2297
-/
theorem univLE_max : UnivLE.{u, max u v} where small α := small_max.{v} α
/-
**Small.trans_univLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Small.trans_univLE (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] : S
mall.{v} α
参数：α : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem Small.trans_univLE (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] :
    Small.{v} α :=
  let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h.small β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩
/-
**UnivLE.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where small α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.trans_univLE`：Small.trans_univLE (α : Type w) [hα : Small.{u} α] [
h : UnivLE.{u, v}] : Small.{v} α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := Small.trans_univLE α
/-
**UnivLE.self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：UnivLE.self : UnivLE.{u, u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UnivLE.self : UnivLE.{u, u} := ⟨inferInstance⟩
/-
**UnivLE.zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：UnivLE.zero : UnivLE.{0, u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UnivLE.zero : UnivLE.{0, u} := ⟨inferInstance⟩

/-- This is redundant as an instance given the below. -/
/-
**UnivLE.succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UnivLE.succ [UnivLE.{u, v}] : UnivLE.{u, v + 1}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.trans`：UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, 
w} where small α
· 使用定理 `small_succ`：∀ (α : Type v), Small.{v + 1, v} α

--- 原说明 ---
This is redundant as an instance given the below.
-/
theorem UnivLE.succ [UnivLE.{u, v}] : UnivLE.{u, v + 1} := @UnivLE.trans _ ⟨inferInstance⟩

/-- This is the crucial instance that subsumes `univLE_max`. -/
/-
**univLE_of_max** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.trans`：UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, 
w} where small α
· 使用定理 `univLE_max`：univLE_max : UnivLE.{u, max u v} where small α

--- 原说明 ---
This is the crucial instance that subsumes `univLE_max`.
-/
instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} := @UnivLE.trans univLE_max ‹_›

-- order doesn't matter
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{v, max v u} := inferInstance
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{v, max u v} := inferInstance
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{u, max v u} := inferInstance
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{u, max u v} := inferInstance
-- `succ` is implied
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{u, u + 1} := inferInstance
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : UnivLE.{2, 5} := inferInstance

/- When `small_Pi` from `Mathlib/Logic/Small/Basic.lean` is imported, we have : -/
-- example (α : Type u) (β : Type v) [UnivLE.{u, v}] : Small.{v} (α → β) := inferInstance

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ¬UnivLE.{u + 1, u} := by
  simp only [univLE_iff, small_iff, not_forall, not_exists]
  exact ⟨Type u, fun α => fun ⟨f⟩ => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩
