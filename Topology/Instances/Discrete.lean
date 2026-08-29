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

instance (priority := 100) DiscreteTopology.firstCountableTopology [DiscreteTopology α] :
    FirstCountableTopology α where
  nhds_generated_countable := by rw [nhds_discrete]; exact isCountablyGenerated_pure

instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable
    [hd : DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  haveI : forall i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (fun _ => isOpen_discrete _)
    (iUnion_of_singleton α)

/--
theorem `LinearOrder.bot_topologicalSpace_eq_preorderTopology` / 定理 `LinearOrder.bot_topologicalSpace_eq_preorderTopology`

English:
theorem LinearOrder.bot_topologicalSpace_eq_preorderTopology
  statement: {α} [LinearOrder α] [PredOrder α]
  proof: by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm

@[deprecated (since := "2026-03-22")]
alias LinearOrder.bot_topologicalSpace_eq_generateFrom :=
  LinearOrder.bot_topologicalSpace_eq_preorderTopology

中文:
定理 线性序.bot_topologicalSpace_eq_preorderTopology
  结论: {α} [线性序 α] [Pred序 α]
  证明: by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm

@[deprecated (since := "2026-03-22")]
alias LinearOrder.bot_topologicalSpace_eq_generateFrom :=
  LinearOrder.bot_topologicalSpace_eq_preorderTopology

Depends on / 依赖: DiscreteTopology, DiscreteTopology.of_predOrder_succOrder.eq_bot.symm, OrderTopology, Preorder, Preorder.topology, eq_bot, of_predOrder_succOrder, topology
-/
theorem LinearOrder.bot_topologicalSpace_eq_preorderTopology {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = Preorder.topology α := by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm

@[deprecated (since := "2026-03-22")]
alias LinearOrder.bot_topologicalSpace_eq_generateFrom :=
  LinearOrder.bot_topologicalSpace_eq_preorderTopology

/--
theorem `discreteTopology_iff_orderTopology_of_pred_succ` / 定理 `discreteTopology_iff_orderTopology_of_pred_succ`

English:
theorem discreteTopology_iff_orderTopology_of_pred_succ
  statement: [LinearOrder α] [PredOrder α]
  proof: by
  refine ⟨fun h => ⟨?_⟩, fun h => .of_predOrder_succOrder⟩
  rw [h.eq_bot]; rw [LinearOrder.bot_topologicalSpace_eq_preorderTopology]

中文:
定理 discreteTopology_iff_orderTopology_of_pred_succ
  结论: [线性序 α] [Pred序 α]
  证明: by
  refine ⟨fun h => ⟨?_⟩, fun h => .of_predOrder_succOrder⟩
  rw [h.eq_bot]; rw [LinearOrder.bot_topologicalSpace_eq_preorderTopology]

Depends on / 依赖: LinearOrder, LinearOrder.bot_topologicalSpace_eq_preorderTopology, bot_topologicalSpace_eq_preorderTopology, eq_bot, h.eq_bot, of_predOrder_succOrder
-/
theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h => ⟨?_⟩, fun h => .of_predOrder_succOrder⟩
  rw [h.eq_bot]; rw [LinearOrder.bot_topologicalSpace_eq_preorderTopology]

/--
Instance `OrderTopology.of_discreteTopology` / 实例 `OrderTopology.of_discreteTopology`

English:
instance OrderTopology.of_discreteTopology
  signature: [LinearOrder α] [PredOrder α] [SuccOrder α]
  body: discreteTopology_iff_orderTopology_of_pred_succ.mp ‹_›

中文:
实例 Order拓扑.of_discreteTopology
  签名: [线性序 α] [Pred序 α] [Succ序 α]
  定义体: discreteTopology_iff_orderTopology_of_pred_succ.mp ‹_›

Depends on / 依赖: discreteTopology_iff_orderTopology_of_pred_succ, discreteTopology_iff_orderTopology_of_pred_succ.mp
-/
instance OrderTopology.of_discreteTopology [LinearOrder α] [PredOrder α] [SuccOrder α]
    [DiscreteTopology α] : OrderTopology α :=
  discreteTopology_iff_orderTopology_of_pred_succ.mp ‹_›

/--
Instance `OrderTopology.of_linearLocallyFinite` / 实例 `OrderTopology.of_linearLocallyFinite`

English:
instance OrderTopology.of_linearLocallyFinite
  body: haveI := LinearLocallyFiniteOrder.succOrder α
  haveI := LinearLocallyFiniteOrder.predOrder α
  inferInstance

中文:
实例 Order拓扑.of_linearLocallyFinite
  定义体: haveI := LinearLocallyFiniteOrder.succOrder α
  haveI := LinearLocallyFiniteOrder.predOrder α
  inferInstance

Depends on / 依赖: LinearLocallyFiniteOrder, LinearLocallyFiniteOrder.predOrder, LinearLocallyFiniteOrder.succOrder, predOrder, succOrder
-/
instance OrderTopology.of_linearLocallyFinite
    [LinearOrder α] [LocallyFiniteOrder α] [DiscreteTopology α] : OrderTopology α :=
  haveI := LinearLocallyFiniteOrder.succOrder α
  haveI := LinearLocallyFiniteOrder.predOrder α
  inferInstance
