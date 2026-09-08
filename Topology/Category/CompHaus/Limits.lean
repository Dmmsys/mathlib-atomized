/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `CompHaus`.
-/

@[expose] public section

namespace CompHaus

universe u w

open CategoryTheory Limits CompHausLike

/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasExplicitPullbacks (fun _ ↦ True) where
  hasProp _ _ := inferInstance
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasExplicitFiniteCoproducts.{w, u} (fun _ ↦ True) where
  hasProp _ := inferInstance
/-
**CompHaus.** 是 Mathlib 中的一个示例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : FinitaryExtensive CompHaus.{u} := inferInstance

/-- A one-element space is terminal in `CompHaus` -/
/-
**CompHaus.isTerminalPUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHaus`。
形式化陈述：isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1})
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X

--- 原说明 ---
A one-element space is terminal in `CompHaus`
-/
abbrev isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

/-- The isomorphism from an arbitrary terminal object of `CompHaus` to a one-element space. -/
/-
**CompHaus.terminalIsoPUnit** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The isomorphism from an arbitrary terminal object of `CompHaus` to a one-element
 space.
-/
noncomputable def terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit
/-
**CompHaus.** 是 Mathlib 中的一个示例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

end CompHaus

