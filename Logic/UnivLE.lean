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
/--
Definition of `UnivLE` / `UnivLE` 的定义

English:
class UnivLE
  parameters: : Prop where
  axioms and operations (1):
    - small((α : Type u)) : Small.{v} α

中文:
类 UnivLE
  参数: : 命题 where
  公理与运算 (1 个):
    - small((α : 类型u)) : Small.{v} α
-/
class UnivLE : Prop where
  small (α : Type u) : Small.{v} α

attribute [instance] UnivLE.small


/--
theorem `univLE_max` / 定理 `univLE_max`

English:
theorem univLE_max
  statement: UnivLE.{u, max u v} where small α
  proof: small_max.{v} α

中文:
定理 univLE_max
  结论: UnivLE.{u, max u v} where small α
  证明: small_max.{v} α

Depends on / 依赖: small_max
-/
theorem univLE_max : UnivLE.{u, max u v} where small α := small_max.{v} α

/--
theorem `Small.trans_univLE` / 定理 `Small.trans_univLE`

English:
theorem Small.trans_univLE
  given: (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}]
  proof: let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h.small β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

中文:
定理 Small.trans_univLE
  条件: (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}]
  证明: let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h.small β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

Depends on / 依赖: equiv_small, f.trans, h.small
-/
theorem Small.trans_univLE (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] :
    Small.{v} α :=
  let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h.small β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

/--
theorem `UnivLE.trans` / 定理 `UnivLE.trans`

English:
theorem UnivLE.trans
  given: [UnivLE.{u, v}] [UnivLE.{v, w}]
  statement: UnivLE.{u, w} where
  proof: Small.trans_univLE α

中文:
定理 UnivLE.trans
  条件: [UnivLE.{u, v}] [UnivLE.{v, w}]
  结论: UnivLE.{u, w} where
  证明: Small.trans_univLE α

Depends on / 依赖: Small.trans_univLE, trans_univLE
-/
theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := Small.trans_univLE α

/--
Instance `UnivLE.self` / 实例 `UnivLE.self`

English:
instance UnivLE.self
  signature: : UnivLE.{u, u}
  body: ⟨inferInstance⟩

中文:
实例 UnivLE.self
  签名: : UnivLE.{u, u}
  定义体: ⟨inferInstance⟩
-/
instance UnivLE.self : UnivLE.{u, u} := ⟨inferInstance⟩
/--
Instance `UnivLE.zero` / 实例 `UnivLE.zero`

English:
instance UnivLE.zero
  signature: : UnivLE.{0, u}
  body: ⟨inferInstance⟩

中文:
实例 UnivLE.zero
  签名: : UnivLE.{0, u}
  定义体: ⟨inferInstance⟩
-/
instance UnivLE.zero : UnivLE.{0, u} := ⟨inferInstance⟩

/--
theorem `UnivLE.succ` / 定理 `UnivLE.succ`

English:
theorem UnivLE.succ
  given: [UnivLE.{u, v}]
  statement: UnivLE.{u, v + 1}
  proof: @UnivLE.trans _ ⟨inferInstance⟩

中文:
定理 UnivLE.succ
  条件: [UnivLE.{u, v}]
  结论: UnivLE.{u, v + 1}
  证明: @UnivLE.trans _ ⟨inferInstance⟩

Depends on / 依赖: UnivLE, UnivLE.trans
-/
theorem UnivLE.succ [UnivLE.{u, v}] : UnivLE.{u, v + 1} := @UnivLE.trans _ ⟨inferInstance⟩

/--
Instance `univLE_of_max` / 实例 `univLE_of_max`

English:
instance univLE_of_max
  signature: [UnivLE.{max u v, v}]
  body: @UnivLE.trans univLE_max ‹_›

中文:
实例 univLE_of_max
  签名: [UnivLE.{max u v, v}]
  定义体: @UnivLE.trans univLE_max ‹_›

Depends on / 依赖: UnivLE, UnivLE.trans, univLE_max
-/
instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} := @UnivLE.trans univLE_max ‹_›

-- order doesn't matter
example : UnivLE.{v, max v u} := inferInstance
example : UnivLE.{v, max u v} := inferInstance
example : UnivLE.{u, max v u} := inferInstance
example : UnivLE.{u, max u v} := inferInstance
-- `succ` is implied
example : UnivLE.{u, u + 1} := inferInstance
example : UnivLE.{2, 5} := inferInstance

/- When `small_Pi` from `Mathlib/Logic/Small/Basic.lean` is imported, we have : -/
-- example (α : Type u) (β : Type v) [UnivLE.{u, v}] : Small.{v} (α → β) := inferInstance

example : ¬UnivLE.{u + 1, u} := by
  simp only [univLE_iff, small_iff, not_forall, not_exists]
  exact ⟨Type u, fun α ⟨f⟩ => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩
