/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Geometry.Manifold.StructureGroupoid

/-!
# Conformal Groupoid

In this file we define the groupoid of conformal maps on normed spaces.

## Main definitions

* `conformalGroupoid`: the groupoid of conformal open partial homeomorphisms.

## Tags

conformal, groupoid
-/

@[expose] public section


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The pregroupoid of conformal maps. -/
/-
**conformalPregroupoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conformalPregroupoid : Pregroupoid X where property f u
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `conformalAt_id`：conformalAt_id (x : X) : ConformalAt _root_.id x

--- 原说明 ---
The pregroupoid of conformal maps.
-/
def conformalPregroupoid : Pregroupoid X where
  property f u := ∀ x, x ∈ u → ConformalAt f x
  comp {f _} _ _ hf hg _ _ _ x hx := (hg (f x) hx.2).comp x (hf x hx.1)
  id_mem x _ := conformalAt_id x
  locality _ h x hx :=
    let ⟨_, _, h₂, h₃⟩ := h x hx
    h₃ x ⟨hx, h₂⟩
  congr hu h hf x hx := (hf x hx).congr hx hu h

/-- The groupoid of conformal maps. -/
/-
**conformalGroupoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conformalGroupoid : StructureGroupoid X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The groupoid of conformal maps.
-/
def conformalGroupoid : StructureGroupoid X :=
  conformalPregroupoid.groupoid
