/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.TotallyDisconnected
/-!

# Separation and (dis)connectedness properties of topological spaces.

This file provides an instance `T2Space X` given `TotallySeparatedSpace X`.

## TODO
* Move the last part of `Topology/Separation` to this file.
-/

public section


variable {X : Type*} [TopologicalSpace X]

section TotallySeparated

/-- A totally separated space is T2. -/
/-
**TotallySeparatedSpace.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TotallySeparatedSpace.t2Space [TotallySeparatedSpace X] : T2Space X where 
t2 x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallySeparatedSpace.isTotallySeparated_univ`：∀ {α : Type u} {inst : To
pologicalSpace α} [self : TotallySeparatedSpace α], IsTotallySeparated Set.univ
· 使用定理 `trivial`：True

--- 原说明 ---
A totally separated space is T2.
-/
instance TotallySeparatedSpace.t2Space [TotallySeparatedSpace X] : T2Space X where
  t2 x y h := by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, _, h₅⟩ := isTotallySeparated_univ trivial trivial h
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩

end TotallySeparated

