/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Topology.MetricSpace.TransferInstance

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed (additive) commutative group and normed space structures
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer a `SeminormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `SeminormedAddCommGroup` across an `Equiv` -/]
/-
**Equiv.seminormedCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [SeminormedCommGroup β] → α ≃ β → Semino
rmedCommGroup α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedCommGrou
p E] (x y : E), dist x y = ‖x⁻¹ * y‖

--- 原说明 ---
Transfer a `SeminormedCommGroup` across an `Equiv`
-/
protected abbrev seminormedCommGroup [SeminormedCommGroup β] (e : α ≃ β) :
    SeminormedCommGroup α :=
  letI := e.commGroup
  { SeminormedCommGroup.induced _ _ e.mulEquiv with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer a `NormedCommGroup` across an `Equiv` -/
@[to_additive /-- Transfer a `NormedAddCommGroup` across an `Equiv` -/]
/-
**Equiv.normedCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [NormedCommGroup β] → α ≃ β → NormedComm
Group α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `NormedCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedCommGroup E] (x 
y : E), dist x y = ‖x⁻¹ * y‖

--- 原说明 ---
Transfer a `NormedCommGroup` across an `Equiv`
-/
protected abbrev normedCommGroup [NormedCommGroup β] (e : α ≃ β) : NormedCommGroup α :=
  letI := e.commGroup
  { NormedCommGroup.induced _ _ e.mulEquiv e.injective
    with toPseudoMetricSpace := e.pseudometricSpace }

/-- Transfer `NormedSpace` across an `Equiv` -/
/-
**Equiv.normedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     (𝕜 : Type u_3) →       [inst : Nor
medField 𝕜] → [inst_1 : SeminormedAddCommGroup β] → [NormedSpace 𝕜 β] → (e : α ≃
 β) → NormedSpace 𝕜 α
参数：𝕜 : Type u_3；e : α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `NormedSpace` across an `Equiv`
-/
protected abbrev normedSpace (𝕜 : Type*) [NormedField 𝕜]
    [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] (e : α ≃ β) :
    letI := Equiv.seminormedAddCommGroup e
    NormedSpace 𝕜 α :=
  letI := e.seminormedAddCommGroup
  letI := e.module 𝕜
  .induced _ _ _ (e.linearEquiv _)

end Equiv

