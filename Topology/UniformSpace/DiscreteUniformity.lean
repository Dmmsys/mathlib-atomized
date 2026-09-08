/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Topology.UniformSpace.Basic

/-! # Discrete uniformity

The discrete uniformity is the smallest possible uniformity, the one for which
the diagonal is an entourage of itself.

It induces the discrete topology.

It is complete.

-/

public section

open Filter UniformSpace

/-- The discrete uniformity -/
@[mk_iff discreteUniformity_iff_eq_bot]
/-
**DiscreteUniformity** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [u : UniformSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete uniformity
-/
class DiscreteUniformity (X : Type*) [u : UniformSpace X] : Prop where
  eq_bot : u = ⊥

namespace DiscreteUniformity

/-- The bot uniformity is the discrete uniformity. -/
/-
**DiscreteUniformity.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bot uniformity is the discrete uniformity.
-/
instance (X : Type*) : @DiscreteUniformity X ⊥ :=
  @DiscreteUniformity.mk X ⊥ rfl

variable (X : Type*) [u : UniformSpace X] [DiscreteUniformity X]
/-
**DiscreteUniformity._root_.discreteUniformity_iff_eq_principal_setRelId** 是 Mat
hlib 中的一个定理，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.discreteUniformity_iff_eq_principal_setRelId {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ uniformity X = 𝓟 SetRel.id := by
  rw [discreteUniformity_iff_eq_bot, UniformSpace.ext_iff, Filter.ext_iff, bot_uniformity]
/-
**DiscreteUniformity.eq_principal_setRelId** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteUn
iformity`。
形式化陈述：eq_principal_setRelId : uniformity X = 𝓟 SetRel.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `discreteUniformity_iff_eq_principal_setRelId`：∀ {X : Type u_2} [inst : U
niformSpace X], DiscreteUniformity X ↔ uniformity X = Filter.principal SetRel.id
-/
theorem eq_principal_setRelId : uniformity X = 𝓟 SetRel.id :=
  discreteUniformity_iff_eq_principal_setRelId.mp inferInstance

/-- The discrete uniformity induces the discrete topology. -/
/-
**DiscreteUniformity.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete uniformity induces the discrete topology.
-/
instance : DiscreteTopology X where
  eq_bot := by
    rw [DiscreteUniformity.eq_bot (X := X), UniformSpace.toTopologicalSpace_bot]
/-
**DiscreteUniformity._root_.discreteUniformity_iff_setRelId_mem_uniformity** 是 M
athlib 中的一个定理，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.discreteUniformity_iff_setRelId_mem_uniformity {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ SetRel.id ∈ uniformity X := by
  rw [← uniformSpace_eq_bot, discreteUniformity_iff_eq_bot]
/-
**DiscreteUniformity.relId_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteUni
formity`。
形式化陈述：relId_mem_uniformity : SetRel.id in uniformity X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `discreteUniformity_iff_setRelId_mem_uniformity`：∀ {X : Type u_2} [inst :
 UniformSpace X], DiscreteUniformity X ↔ SetRel.id ∈ uniformity X
-/
theorem relId_mem_uniformity : SetRel.id ∈ uniformity X :=
  discreteUniformity_iff_setRelId_mem_uniformity.mp inferInstance
/-
**DiscreteUniformity.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Y : Type*} [Finite Y] [UniformSpace Y] [DiscreteTopology Y] :
    DiscreteUniformity Y := by
  have h : SetRel.id = ⋂ y : Y, {p | p.2 = y → p.1 ∈ ({y} : Set Y)} := by
    ext x
    simp [SetRel.id]
  simp_rw [discreteUniformity_iff_setRelId_mem_uniformity, h, Filter.iInter_mem,
    ← mem_nhds_uniformity_iff_left, nhds_discrete, Filter.mem_pure, Set.mem_singleton_iff,
    implies_true]

variable {X} in
/-- A product of spaces with discrete uniformity has a discrete uniformity. -/
/-
**DiscreteUniformity.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteUniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of spaces with discrete uniformity has a discrete uniformity.
-/
instance {Y : Type*} [UniformSpace Y] [DiscreteUniformity Y] :
    DiscreteUniformity (X × Y) := by
  simp [discreteUniformity_iff_eq_principal_setRelId, uniformity_prod_eq_comap_prod,
    eq_principal_setRelId, SetRel.id, Set.prod_eq, Prod.ext_iff, Set.ofPred_and]

variable {x} in
/-- On a space with a discrete uniformity, any function is uniformly continuous. -/
/-
**DiscreteUniformity.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteUnifor
mity`。
形式化陈述：uniformContinuous {Y : Type*} [UniformSpace Y] (f : X -> Y) : UniformConti
nuous f
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DiscreteUniformity.eq_bot`：∀ {X : Type u_1} {u : UniformSpace X} [self :
 DiscreteUniformity X], u = ⊥

--- 原说明 ---
On a space with a discrete uniformity, any function is uniformly continuous.
-/
theorem uniformContinuous {Y : Type*} [UniformSpace Y] (f : X → Y) :
    UniformContinuous f := by
  simp only [uniformContinuous_iff_le_comap, DiscreteUniformity.eq_bot, bot_le]

end DiscreteUniformity

