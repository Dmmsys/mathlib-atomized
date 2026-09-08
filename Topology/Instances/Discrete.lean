/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Instances related to the discrete topology

We prove that the discrete topology is
* first-countable,
* second-countable for an encodable type,
* equal to the order topology in linear orders which are also `PredOrder` and `SuccOrder`,
* metrizable.

When importing this file and `Data.Nat.SuccPred`, the instances `SecondCountableTopology ℕ`
and `OrderTopology ℕ` become available.

-/

public section


open Order Set TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteTopology.firstCountableTopology [DiscreteTopology α] :
    FirstCountableTopology α where
  nhds_generated_countable := by rw [nhds_discrete]; exact isCountablyGenerated_pure
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable
    [hd : DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (fun _ ↦ isOpen_discrete _)
    (iUnion_of_singleton α)
/-
**LinearOrder.bot_topologicalSpace_eq_preorderTopology** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：LinearOrder.bot_topologicalSpace_eq_preorderTopology {α} [LinearOrder α] [
PredOrder α] [SuccOrder α] : (⊥ : TopologicalSpace α) = Preorder.topology α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
· 使用定理 `DiscreteTopology.of_predOrder_succOrder`：DiscreteTopology.of_predOrder_s
uccOrder [PredOrder α] [SuccOrder α] : DiscreteTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem LinearOrder.bot_topologicalSpace_eq_preorderTopology {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = Preorder.topology α := by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm

@[deprecated (since := "2026-03-22")]
alias LinearOrder.bot_topologicalSpace_eq_generateFrom :=
  LinearOrder.bot_topologicalSpace_eq_preorderTopology
/-
**discreteTopology_iff_orderTopology_of_pred_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder
 α] [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
· 使用定理 `LinearOrder.bot_topologicalSpace_eq_preorderTopology`：LinearOrder.bot_to
pologicalSpace_eq_preorderTopology {α} [LinearOrder α] [PredOrder α] [SuccOrder 
α] : (⊥ : TopologicalSpace α) = Preorder.t…
· 使用定理 `DiscreteTopology.of_predOrder_succOrder`：DiscreteTopology.of_predOrder_s
uccOrder [PredOrder α] [SuccOrder α] : DiscreteTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h ↦ ⟨?_⟩, fun h ↦ .of_predOrder_succOrder⟩
  rw [h.eq_bot, LinearOrder.bot_topologicalSpace_eq_preorderTopology]
/-
**OrderTopology.of_discreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderTopology.of_discreteTopology [LinearOrder α] [PredOrder α] [SuccOrder
 α] [DiscreteTopology α] : OrderTopology α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `discreteTopology_iff_orderTopology_of_pred_succ`：discreteTopology_iff_or
derTopology_of_pred_succ [LinearOrder α] [PredOrder α] [SuccOrder α] : DiscreteT
opology α ↔ OrderTopology α
-/
instance OrderTopology.of_discreteTopology [LinearOrder α] [PredOrder α] [SuccOrder α]
    [DiscreteTopology α] : OrderTopology α :=
  discreteTopology_iff_orderTopology_of_pred_succ.mp ‹_›
/-
**OrderTopology.of_linearLocallyFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderTopology.of_linearLocallyFinite [LinearOrder α] [LocallyFiniteOrder α
] [DiscreteTopology α] : OrderTopology α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderTopology.of_linearLocallyFinite
    [LinearOrder α] [LocallyFiniteOrder α] [DiscreteTopology α] : OrderTopology α :=
  haveI := LinearLocallyFiniteOrder.succOrder α
  haveI := LinearLocallyFiniteOrder.predOrder α
  inferInstance
