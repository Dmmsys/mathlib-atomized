/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightProfinite`.
-/

public section

namespace LightProfinite

universe u w

open CategoryTheory Limits CompHausLike

/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasExplicitPullbacks
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ _ := {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }
/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasExplicitFiniteCoproducts.{w, u}
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

/-- A one-element space is terminal in `Profinite` -/
/-
**LightProfinite.isTerminalPUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightProfinite`。
形式化陈述：isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A one-element space is terminal in `Profinite`
-/
abbrev isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit
/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) [h : Epi g] :
    Epi (CompHausLike.pullback.fst f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro x
  obtain ⟨y, hy⟩ := h (f x)
  exact ⟨⟨⟨x, y⟩, hy.symm⟩, rfl⟩
/-
**LightProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) [h : Epi f] :
    Epi (CompHausLike.pullback.snd f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro y
  obtain ⟨x, hx⟩ := h (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩
/-
**LightProfinite.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : FinitaryExtensive LightProfinite.{u} := inferInstance
/-
**LightProfinite.** 是 Mathlib 中的一个示例，位于命名空间 `LightProfinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus.{u} := inferInstance

end LightProfinite

