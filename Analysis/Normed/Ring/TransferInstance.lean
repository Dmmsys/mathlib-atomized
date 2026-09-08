/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed ring structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

/-- Transfer a `SeminormedRing` across an `Equiv` -/
/-
**Equiv.seminormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [SeminormedRing β] → α ≃ β → SeminormedR
ing α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `SeminormedRing` across an `Equiv`
-/
protected abbrev seminormedRing [SeminormedRing β] (e : α ≃ β) :
    SeminormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv

/-- Transfer a `NormedRing` across an `Equiv` -/
/-
**Equiv.normedRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [NormedRing β] → α ≃ β → NormedRing α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer a `NormedRing` across an `Equiv`
-/
protected abbrev normedRing [NormedRing β] (e : α ≃ β) : NormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv e.injective

end Equiv

