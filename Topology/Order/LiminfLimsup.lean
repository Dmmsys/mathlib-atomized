/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Monotone

import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

public section

open Filter TopologicalSpace
open scoped Topology

universe u v

variable {ι α β R S : Type*} {π : ι -> Type*}

/--
Definition of `BoundedLENhdsClass` / `BoundedLENhdsClass` 的定义

English:
class BoundedLENhdsClass
  parameters: (α : Type*) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - isBounded_le_nhds((a : α)) : (𝓝 a).IsBounded (· <= ·)

中文:
类 BoundedLENhds类
  参数: (α : 类型) [预序 α] [拓扑空间 α]
  公理与运算 (1 个):
    - isBounded_le_nhds((a : α)) : (𝓝 a).IsBounded (· <= ·)
-/
class BoundedLENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)

/--
Definition of `BoundedGENhdsClass` / `BoundedGENhdsClass` 的定义

English:
class BoundedGENhdsClass
  parameters: (α : Type*) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - isBounded_ge_nhds((a : α)) : (𝓝 a).IsBounded (· >= ·)

中文:
类 BoundedGENhds类
  参数: (α : 类型) [预序 α] [拓扑空间 α]
  公理与运算 (1 个):
    - isBounded_ge_nhds((a : α)) : (𝓝 a).IsBounded (· >= ·)
-/
class BoundedGENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)

section Preorder
variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]

section BoundedLENhdsClass
variable [BoundedLENhdsClass α] [BoundedLENhdsClass β] {f : Filter ι} {u : ι -> α} {a : α}

/--
theorem `isBounded_le_nhds` / 定理 `isBounded_le_nhds`

English:
theorem isBounded_le_nhds
  given: (a : α)
  statement: (𝓝 a).IsBounded (· <= ·)
  proof: BoundedLENhdsClass.isBounded_le_nhds _

中文:
定理 isBounded_le_nhds
  条件: (a : α)
  结论: (𝓝 a).IsBounded (· <= ·)
  证明: BoundedLENhdsClass.isBounded_le_nhds _

Depends on / 依赖: BoundedLENhdsClass, BoundedLENhdsClass.isBounded_le_nhds, isBounded_le_nhds
-/
theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·) :=
  BoundedLENhdsClass.isBounded_le_nhds _

/--
theorem `Filter.Tendsto.isBoundedUnder_le` / 定理 `Filter.Tendsto.isBoundedUnder_le`

English:
theorem Filter.Tendsto.isBoundedUnder_le
  given: (h : Tendsto u f (𝓝 a))
  statement: f.IsBoundedUnder (· <= ·) u
  proof: (isBounded_le_nhds a).mono h

中文:
定理 滤子.收敛.isBoundedUnder_le
  条件: (h : 收敛 u f (𝓝 a))
  结论: f.IsBoundedUnder (· <= ·) u
  证明: (isBounded_le_nhds a).mono h

Depends on / 依赖: isBounded_le_nhds
-/
theorem Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u :=
  (isBounded_le_nhds a).mono h

/--
theorem `Filter.Tendsto.bddAbove_range_of_cofinite` / 定理 `Filter.Tendsto.bddAbove_range_of_cofinite`

English:
theorem Filter.Tendsto.bddAbove_range_of_cofinite
  statement: [IsDirectedOrder α]
  proof: h.isBoundedUnder_le.bddAbove_range_of_cofinite

中文:
定理 滤子.收敛.bddAbove_range_of_cofinite
  结论: [IsDirectedOrder α]
  证明: h.isBoundedUnder_le.bddAbove_range_of_cofinite

Depends on / 依赖: bddAbove_range_of_cofinite, h.isBoundedUnder_le.bddAbove_range_of_cofinite, isBoundedUnder_le
-/
theorem Filter.Tendsto.bddAbove_range_of_cofinite [IsDirectedOrder α]
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite

/--
theorem `Filter.Tendsto.bddAbove_range` / 定理 `Filter.Tendsto.bddAbove_range`

English:
theorem Filter.Tendsto.bddAbove_range
  statement: [IsDirectedOrder α] {u : Nat -> α}
  proof: h.isBoundedUnder_le.bddAbove_range

中文:
定理 滤子.收敛.bddAbove_range
  结论: [IsDirectedOrder α] {u : 自然数 -> α}
  证明: h.isBoundedUnder_le.bddAbove_range

Depends on / 依赖: bddAbove_range, h.isBoundedUnder_le.bddAbove_range, isBoundedUnder_le
-/
theorem Filter.Tendsto.bddAbove_range [IsDirectedOrder α] {u : Nat -> α}
    (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range

/--
theorem `isCobounded_ge_nhds` / 定理 `isCobounded_ge_nhds`

English:
theorem isCobounded_ge_nhds
  given: (a : α)
  statement: (𝓝 a).IsCobounded (· >= ·)
  proof: (isBounded_le_nhds a).isCobounded_flip

中文:
定理 isCobounded_ge_nhds
  条件: (a : α)
  结论: (𝓝 a).IsCobounded (· >= ·)
  证明: (isBounded_le_nhds a).isCobounded_flip

Depends on / 依赖: isBounded_le_nhds, isCobounded_flip
-/
theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· >= ·) :=
  (isBounded_le_nhds a).isCobounded_flip

/--
theorem `Filter.Tendsto.isCoboundedUnder_ge` / 定理 `Filter.Tendsto.isCoboundedUnder_ge`

English:
theorem Filter.Tendsto.isCoboundedUnder_ge
  given: [NeBot f] (h : Tendsto u f (𝓝 a))
  proof: h.isBoundedUnder_le.isCobounded_flip

中文:
定理 滤子.收敛.isCoboundedUnder_ge
  条件: [NeBot f] (h : 收敛 u f (𝓝 a))
  证明: h.isBoundedUnder_le.isCobounded_flip

Depends on / 依赖: h.isBoundedUnder_le.isCobounded_flip, isBoundedUnder_le, isCobounded_flip
-/
theorem Filter.Tendsto.isCoboundedUnder_ge [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· >= ·) u :=
  h.isBoundedUnder_le.isCobounded_flip

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedGENhdsClass αᵒᵈ
  body: ⟨@isBounded_le_nhds α _ _ _⟩

中文:
实例 :
  签名: BoundedGENhds类 αᵒᵈ
  定义体: ⟨@isBounded_le_nhds α _ _ _⟩

Depends on / 依赖: isBounded_le_nhds
-/
instance : BoundedGENhdsClass αᵒᵈ := ⟨@isBounded_le_nhds α _ _ _⟩

/--
Instance `Prod.instBoundedLENhdsClass` / 实例 `Prod.instBoundedLENhdsClass`

English:
instance Prod.instBoundedLENhdsClass
  signature: : BoundedLENhdsClass (α × β)
  body: by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x]; rw [nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

中文:
实例 积类型.instBoundedLENhdsClass
  签名: : BoundedLENhds类 (α × β)
  定义体: by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x]; rw [nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

Depends on / 依赖: Prod.mk.eta, ha.prod_mk, isBounded_le_nhds, nhds_prod_eq, prod_mk
-/
instance Prod.instBoundedLENhdsClass : BoundedLENhdsClass (α × β) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x]; rw [nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

/--
Instance `Pi.instBoundedLENhdsClass` / 实例 `Pi.instBoundedLENhdsClass`

English:
instance Pi.instBoundedLENhdsClass
  signature: [Finite ι] [forall i, Preorder (π i)] [forall i, TopologicalSpace (π i)]
  body: by
  refine ⟨fun x => ?_⟩
  rw [nhds_pi]
  choose f hf using fun i => isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

中文:
实例 依赖函数类型.instBoundedLENhdsClass
  签名: [有限 ι] [对任意 i, 预序 (π i)] [对任意 i, 拓扑空间 (π i)]
  定义体: by
  refine ⟨fun x => ?_⟩
  rw [nhds_pi]
  choose f hf using fun i => isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

Depends on / 依赖: eventually_pi, isBounded_le_nhds, nhds_pi
-/
instance Pi.instBoundedLENhdsClass [Finite ι] [forall i, Preorder (π i)] [forall i, TopologicalSpace (π i)]
    [forall i, BoundedLENhdsClass (π i)] : BoundedLENhdsClass (forall i, π i) := by
  refine ⟨fun x => ?_⟩
  rw [nhds_pi]
  choose f hf using fun i => isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

end BoundedLENhdsClass

section BoundedGENhdsClass
variable [BoundedGENhdsClass α] [BoundedGENhdsClass β] {f : Filter ι} {u : ι -> α} {a : α}

/--
theorem `isBounded_ge_nhds` / 定理 `isBounded_ge_nhds`

English:
theorem isBounded_ge_nhds
  given: (a : α)
  statement: (𝓝 a).IsBounded (· >= ·)
  proof: BoundedGENhdsClass.isBounded_ge_nhds _

中文:
定理 isBounded_ge_nhds
  条件: (a : α)
  结论: (𝓝 a).IsBounded (· >= ·)
  证明: BoundedGENhdsClass.isBounded_ge_nhds _

Depends on / 依赖: BoundedGENhdsClass, BoundedGENhdsClass.isBounded_ge_nhds, isBounded_ge_nhds
-/
theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·) :=
  BoundedGENhdsClass.isBounded_ge_nhds _

/--
theorem `Filter.Tendsto.isBoundedUnder_ge` / 定理 `Filter.Tendsto.isBoundedUnder_ge`

English:
theorem Filter.Tendsto.isBoundedUnder_ge
  given: (h : Tendsto u f (𝓝 a))
  statement: f.IsBoundedUnder (· >= ·) u
  proof: (isBounded_ge_nhds a).mono h

中文:
定理 滤子.收敛.isBoundedUnder_ge
  条件: (h : 收敛 u f (𝓝 a))
  结论: f.IsBoundedUnder (· >= ·) u
  证明: (isBounded_ge_nhds a).mono h

Depends on / 依赖: isBounded_ge_nhds
-/
theorem Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· >= ·) u :=
  (isBounded_ge_nhds a).mono h

/--
theorem `Filter.Tendsto.bddBelow_range_of_cofinite` / 定理 `Filter.Tendsto.bddBelow_range_of_cofinite`

English:
theorem Filter.Tendsto.bddBelow_range_of_cofinite
  statement: [IsCodirectedOrder α]
  proof: h.isBoundedUnder_ge.bddBelow_range_of_cofinite

中文:
定理 滤子.收敛.bddBelow_range_of_cofinite
  结论: [IsCodirectedOrder α]
  证明: h.isBoundedUnder_ge.bddBelow_range_of_cofinite

Depends on / 依赖: bddBelow_range_of_cofinite, h.isBoundedUnder_ge.bddBelow_range_of_cofinite, isBoundedUnder_ge
-/
theorem Filter.Tendsto.bddBelow_range_of_cofinite [IsCodirectedOrder α]
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite

/--
theorem `Filter.Tendsto.bddBelow_range` / 定理 `Filter.Tendsto.bddBelow_range`

English:
theorem Filter.Tendsto.bddBelow_range
  statement: [IsCodirectedOrder α] {u : Nat -> α}
  proof: h.isBoundedUnder_ge.bddBelow_range

中文:
定理 滤子.收敛.bddBelow_range
  结论: [IsCodirectedOrder α] {u : 自然数 -> α}
  证明: h.isBoundedUnder_ge.bddBelow_range

Depends on / 依赖: bddBelow_range, h.isBoundedUnder_ge.bddBelow_range, isBoundedUnder_ge
-/
theorem Filter.Tendsto.bddBelow_range [IsCodirectedOrder α] {u : Nat -> α}
    (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range

/--
theorem `isCobounded_le_nhds` / 定理 `isCobounded_le_nhds`

English:
theorem isCobounded_le_nhds
  given: (a : α)
  statement: (𝓝 a).IsCobounded (· <= ·)
  proof: (isBounded_ge_nhds a).isCobounded_flip

中文:
定理 isCobounded_le_nhds
  条件: (a : α)
  结论: (𝓝 a).IsCobounded (· <= ·)
  证明: (isBounded_ge_nhds a).isCobounded_flip

Depends on / 依赖: isBounded_ge_nhds, isCobounded_flip
-/
theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· <= ·) :=
  (isBounded_ge_nhds a).isCobounded_flip

/--
theorem `Filter.Tendsto.isCoboundedUnder_le` / 定理 `Filter.Tendsto.isCoboundedUnder_le`

English:
theorem Filter.Tendsto.isCoboundedUnder_le
  given: [NeBot f] (h : Tendsto u f (𝓝 a))
  proof: h.isBoundedUnder_ge.isCobounded_flip

中文:
定理 滤子.收敛.isCoboundedUnder_le
  条件: [NeBot f] (h : 收敛 u f (𝓝 a))
  证明: h.isBoundedUnder_ge.isCobounded_flip

Depends on / 依赖: h.isBoundedUnder_ge.isCobounded_flip, isBoundedUnder_ge, isCobounded_flip
-/
theorem Filter.Tendsto.isCoboundedUnder_le [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· <= ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedLENhdsClass αᵒᵈ
  body: ⟨@isBounded_ge_nhds α _ _ _⟩

中文:
实例 :
  签名: BoundedLENhds类 αᵒᵈ
  定义体: ⟨@isBounded_ge_nhds α _ _ _⟩

Depends on / 依赖: isBounded_ge_nhds
-/
instance : BoundedLENhdsClass αᵒᵈ := ⟨@isBounded_ge_nhds α _ _ _⟩

/--
Instance `Prod.instBoundedGENhdsClass` / 实例 `Prod.instBoundedGENhdsClass`

English:
instance Prod.instBoundedGENhdsClass
  signature: : BoundedGENhdsClass (α × β)
  body: ⟨(Prod.instBoundedLENhdsClass (α := αᵒᵈ) (β := βᵒᵈ)).isBounded_le_nhds⟩

中文:
实例 积类型.instBoundedGENhdsClass
  签名: : BoundedGENhds类 (α × β)
  定义体: ⟨(Prod.instBoundedLENhdsClass (α := αᵒᵈ) (β := βᵒᵈ)).isBounded_le_nhds⟩

Depends on / 依赖: Prod.instBoundedLENhdsClass, instBoundedLENhdsClass, isBounded_le_nhds
-/
instance Prod.instBoundedGENhdsClass : BoundedGENhdsClass (α × β) :=
  ⟨(Prod.instBoundedLENhdsClass (α := αᵒᵈ) (β := βᵒᵈ)).isBounded_le_nhds⟩

/--
Instance `Pi.instBoundedGENhdsClass` / 实例 `Pi.instBoundedGENhdsClass`

English:
instance Pi.instBoundedGENhdsClass
  signature: [Finite ι] [forall i, Preorder (π i)] [forall i, TopologicalSpace (π i)]
  body: ⟨(Pi.instBoundedLENhdsClass (π := fun i => (π i)ᵒᵈ)).isBounded_le_nhds⟩

中文:
实例 依赖函数类型.instBoundedGENhdsClass
  签名: [有限 ι] [对任意 i, 预序 (π i)] [对任意 i, 拓扑空间 (π i)]
  定义体: ⟨(Pi.instBoundedLENhdsClass (π := fun i => (π i)ᵒᵈ)).isBounded_le_nhds⟩

Depends on / 依赖: Pi.instBoundedLENhdsClass, instBoundedLENhdsClass, isBounded_le_nhds
-/
instance Pi.instBoundedGENhdsClass [Finite ι] [forall i, Preorder (π i)] [forall i, TopologicalSpace (π i)]
    [forall i, BoundedGENhdsClass (π i)] : BoundedGENhdsClass (forall i, π i) :=
  ⟨(Pi.instBoundedLENhdsClass (π := fun i => (π i)ᵒᵈ)).isBounded_le_nhds⟩

end BoundedGENhdsClass

-- See note [lower instance priority]
instance (priority := 100) OrderTop.to_BoundedLENhdsClass [OrderTop α] : BoundedLENhdsClass α :=
  ⟨fun _a => isBounded_le_of_top⟩

-- See note [lower instance priority]
instance (priority := 100) OrderBot.to_BoundedGENhdsClass [OrderBot α] : BoundedGENhdsClass α :=
  ⟨fun _a => isBounded_ge_of_bot⟩

end Preorder

-- See note [lower instance priority]
instance (priority := 100) BoundedLENhdsClass.of_closedIciTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] : BoundedLENhdsClass α :=
⟨fun a => ((isTop_or_exists_gt a).elim fun h => ⟨a, Eventually.of_forall h⟩)
    Exists.imp fun _b => eventually_le_nhds⟩

-- See note [lower instance priority]
instance (priority := 100) BoundedGENhdsClass.of_closedIicTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIicTopology α] : BoundedGENhdsClass α :=
inferInstanceAs BoundedGENhdsClass αᵒᵈᵒᵈ

section LiminfLimsup

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/--
theorem `le_nhds_of_limsSup_eq_limsInf` / 定理 `le_nhds_of_limsSup_eq_limsInf`

English:
theorem le_nhds_of_limsSup_eq_limsInf
  statement: {f : Filter α} {a : α} (hl : f.IsBounded (· <= ·))
  proof: tendsto_order.2 ⟨fun _ hb => gt_mem_sets_of_limsInf_gt hg hi.symm ▸ hb,
fun _ hb => lt_mem_sets_of_limsSup_lt hl hs.symm ▸ hb⟩

中文:
定理 le_nhds_of_limsSup_eq_limsInf
  结论: {f : 滤子 α} {a : α} (hl : f.IsBounded (· <= ·))
  证明: tendsto_order.2 ⟨fun _ hb => gt_mem_sets_of_limsInf_gt hg hi.symm ▸ hb,
fun _ hb => lt_mem_sets_of_limsSup_lt hl hs.symm ▸ hb⟩

Depends on / 依赖: gt_mem_sets_of_limsInf_gt, hi.symm, hs.symm, lt_mem_sets_of_limsSup_lt, tendsto_order
-/
theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· <= ·))
    (hg : f.IsBounded (· >= ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f <= 𝓝 a :=
tendsto_order.2 ⟨fun _ hb => gt_mem_sets_of_limsInf_gt hg hi.symm ▸ hb,
fun _ hb => lt_mem_sets_of_limsSup_lt hl hs.symm ▸ hb⟩

/--
theorem `limsSup_nhds` / 定理 `limsSup_nhds`

English:
theorem limsSup_nhds
  given: (a : α)
  statement: limsSup (𝓝 a) = a
  proof: csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n <= a' } in 𝓝 a) => show a <= a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) =>
    show exists c, { n : α | n <= c } in 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

中文:
定理 limsSup_nhds
  条件: (a : α)
  结论: limsSup (𝓝 a) = a
  证明: csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n <= a' } in 𝓝 a) => show a <= a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) =>
    show exists c, { n : α | n <= c } in 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

Depends on / 依赖: Or.inl, Or.inr, csInf_eq_of_forall_ge_of_forall_gt_exists_lt, dense_or_discrete, ge_mem_nhds, gt_mem_nhds, isBounded_le_nhds, mem_of_mem_nhds, sets_of_superset
-/
theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n <= a' } in 𝓝 a) => show a <= a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) =>
    show exists c, { n : α | n <= c } in 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

/--
theorem `limsInf_nhds` / 定理 `limsInf_nhds`

English:
theorem limsInf_nhds
  given: (a : α)
  statement: limsInf (𝓝 a) = a
  proof: limsSup_nhds (α := αᵒᵈ) a

中文:
定理 limsInf_nhds
  条件: (a : α)
  结论: limsInf (𝓝 a) = a
  证明: limsSup_nhds (α := αᵒᵈ) a

Depends on / 依赖: limsSup_nhds
-/
theorem limsInf_nhds (a : α) : limsInf (𝓝 a) = a :=
  limsSup_nhds (α := αᵒᵈ) a

/--
theorem `limsInf_eq_of_le_nhds` / 定理 `limsInf_eq_of_le_nhds`

English:
theorem limsInf_eq_of_le_nhds
  given: {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a)
  statement: f.limsInf = a
  proof: have hb_ge : IsBounded (· >= ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· <= ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf <= f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ <= (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ <= f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)

中文:
定理 limsInf_eq_of_le_nhds
  条件: {f : 滤子 α} {a : α} [NeBot f] (h : f <= 𝓝 a)
  结论: f.limsInf = a
  证明: have hb_ge : IsBounded (· >= ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· <= ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf <= f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ <= (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ <= f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)

Depends on / 依赖: IsBounded, f.limsInf, f.limsSup, hb_ge, hb_ge.isCobounded_flip, hb_le, hb_le.isCobounded_flip, isBounded_ge_nhds, isBounded_le_nhds, isCobounded_flip, le_antisymm, limsInf, limsInf_le_limsInf_of_le, limsInf_le_limsSup, limsInf_nhds, limsSup, limsSup_le_limsSup_of_le, limsSup_nhds
-/
theorem limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a) : f.limsInf = a :=
  have hb_ge : IsBounded (· >= ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· <= ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf <= f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ <= (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ <= f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `limsSup_eq_of_le_nhds` / 定理 `limsSup_eq_of_le_nhds`

English:
theorem limsSup_eq_of_le_nhds
  given: {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a)
  statement: f.limsSup = a
  proof: limsInf_eq_of_le_nhds (α := αᵒᵈ) h

中文:
定理 limsSup_eq_of_le_nhds
  条件: {f : 滤子 α} {a : α} [NeBot f] (h : f <= 𝓝 a)
  结论: f.limsSup = a
  证明: limsInf_eq_of_le_nhds (α := αᵒᵈ) h

Depends on / 依赖: limsInf_eq_of_le_nhds
-/
theorem limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a) : f.limsSup = a :=
  limsInf_eq_of_le_nhds (α := αᵒᵈ) h

/--
theorem `Filter.Tendsto.limsup_eq` / 定理 `Filter.Tendsto.limsup_eq`

English:
theorem Filter.Tendsto.limsup_eq
  statement: {f : Filter β} {u : β -> α} {a : α} [NeBot f]
  proof: limsSup_eq_of_le_nhds h

中文:
定理 滤子.收敛.limsup_eq
  结论: {f : 滤子 β} {u : β -> α} {a : α} [NeBot f]
  证明: limsSup_eq_of_le_nhds h

Depends on / 依赖: limsSup_eq_of_le_nhds
-/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β -> α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h

/--
theorem `Filter.Tendsto.liminf_eq` / 定理 `Filter.Tendsto.liminf_eq`

English:
theorem Filter.Tendsto.liminf_eq
  statement: {f : Filter β} {u : β -> α} {a : α} [NeBot f]
  proof: limsInf_eq_of_le_nhds h

中文:
定理 滤子.收敛.liminf_eq
  结论: {f : 滤子 β} {u : β -> α} {a : α} [NeBot f]
  证明: limsInf_eq_of_le_nhds h

Depends on / 依赖: limsInf_eq_of_le_nhds
-/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β -> α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h

/--
theorem `ClusterPt.limsSup` / 定理 `ClusterPt.limsSup`

English:
theorem ClusterPt.limsSup
  statement: {f : Filter α} [NeBot f]
  proof: by
  by_cases! hn : Nontrivial α
  · by_cases! htop : forall x, x <= f.limsSup
    · let : OrderTop α := { top := f.limsSup, le_top := htop }
.mpr fun a => frequently_lt_of_lt_limsSup hc exact nhds_top_basis.clusterPt_iff_frequently
    · by_cases! hbot : forall x, f.limsSup <= x
      · let : OrderBot α := { bot := f.limsSup, bot_le := hbot }
.mpr fun a h => ?_ refine nhds_bot_basis.clusterPt_iff_frequently
.frequently exact lt_mem_sets_of_limsSup_lt hb h
.mpr fun a ⟨hl, hg⟩ => ?_ · refine (nhds_basis_Ioo' hbot htop).clusterPt_iff_frequently
.and_eventually lt_mem_sets_of_limsSup_lt hb hg exact frequently_lt_of_lt_limsSup hc hl
  · simp_all [ClusterPt, Filter.eq_top_of_neBot]

中文:
定理 ClusterPt.limsSup
  结论: {f : 滤子 α} [NeBot f]
  证明: by
  by_cases! hn : Nontrivial α
  · by_cases! htop : forall x, x <= f.limsSup
    · let : OrderTop α := { top := f.limsSup, le_top := htop }
.mpr fun a => frequently_lt_of_lt_limsSup hc exact nhds_top_basis.clusterPt_iff_frequently
    · by_cases! hbot : forall x, f.limsSup <= x
      · let : OrderBot α := { bot := f.limsSup, bot_le := hbot }
.mpr fun a h => ?_ refine nhds_bot_basis.clusterPt_iff_frequently
.frequently exact lt_mem_sets_of_limsSup_lt hb h
.mpr fun a ⟨hl, hg⟩ => ?_ · refine (nhds_basis_Ioo' hbot htop).clusterPt_iff_frequently
.and_eventually lt_mem_sets_of_limsSup_lt hb hg exact frequently_lt_of_lt_limsSup hc hl
  · simp_all [ClusterPt, Filter.eq_top_of_neBot]

Depends on / 依赖: ClusterPt, IsBounded, Nontrivial, OrderBot, OrderTop, bot_le, clusterPt_iff_frequently, f.IsBounded, f.limsSup, freque, frequently_lt_of_lt_limsSup, isBoundedDefault, le_top, limsSup, nhds_bot_basis, nhds_bot_basis.clusterPt_iff_frequently, nhds_top_basis, nhds_top_basis.clusterPt_iff_frequently
-/
theorem ClusterPt.limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· <= ·) := by isBoundedDefault) : ClusterPt f.limsSup f := by
  by_cases! hn : Nontrivial α
  · by_cases! htop : forall x, x <= f.limsSup
    · let : OrderTop α := { top := f.limsSup, le_top := htop }
.mpr fun a => frequently_lt_of_lt_limsSup hc exact nhds_top_basis.clusterPt_iff_frequently
    · by_cases! hbot : forall x, f.limsSup <= x
      · let : OrderBot α := { bot := f.limsSup, bot_le := hbot }
.mpr fun a h => ?_ refine nhds_bot_basis.clusterPt_iff_frequently
.frequently exact lt_mem_sets_of_limsSup_lt hb h
.mpr fun a ⟨hl, hg⟩ => ?_ · refine (nhds_basis_Ioo' hbot htop).clusterPt_iff_frequently
.and_eventually lt_mem_sets_of_limsSup_lt hb hg exact frequently_lt_of_lt_limsSup hc hl
  · simp_all [ClusterPt, Filter.eq_top_of_neBot]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ClusterPt.limsInf` / 定理 `ClusterPt.limsInf`

English:
theorem ClusterPt.limsInf
  statement: {f : Filter α} [NeBot f]
  proof: ClusterPt.limsSup (α := αᵒᵈ) hc hb

中文:
定理 ClusterPt.limsInf
  结论: {f : 滤子 α} [NeBot f]
  证明: ClusterPt.limsSup (α := αᵒᵈ) hc hb

Depends on / 依赖: ClusterPt, ClusterPt.limsSup, IsBounded, f.IsBounded, f.limsInf, isBoundedDefault, limsInf, limsSup
-/
theorem ClusterPt.limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· >= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· >= ·) := by isBoundedDefault) : ClusterPt f.limsInf f :=
  ClusterPt.limsSup (α := αᵒᵈ) hc hb

/--
theorem `ClusterPt.le_limsSup` / 定理 `ClusterPt.le_limsSup`

English:
theorem ClusterPt.le_limsSup
  statement: {f : Filter α} {x : α} (hx : ClusterPt x f)
  proof: by
  simp only [ClusterPt] at hx
  have : (𝓝 x ⊓ f).limsSup = x := limsSup_eq_of_le_nhds inf_le_left
  refine this ▸ limsSup_le_limsSup_of_le inf_le_right ?_ hb
  exact (IsBounded.mono inf_le_left (isBounded_ge_nhds x)).isCobounded_le

中文:
定理 ClusterPt.le_limsSup
  结论: {f : 滤子 α} {x : α} (hx : ClusterPt x f)
  证明: by
  simp only [ClusterPt] at hx
  have : (𝓝 x ⊓ f).limsSup = x := limsSup_eq_of_le_nhds inf_le_left
  refine this ▸ limsSup_le_limsSup_of_le inf_le_right ?_ hb
  exact (IsBounded.mono inf_le_left (isBounded_ge_nhds x)).isCobounded_le

Depends on / 依赖: ClusterPt, IsBounded, IsBounded.mono, f.limsSup, inf_le_left, inf_le_right, isBoundedDefault, isBounded_ge_nhds, isCobounded_le, limsSup, limsSup_eq_of_le_nhds, limsSup_le_limsSup_of_le
-/
theorem ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· <= ·) := by isBoundedDefault) :
    x <= f.limsSup := by
  simp only [ClusterPt] at hx
  have : (𝓝 x ⊓ f).limsSup = x := limsSup_eq_of_le_nhds inf_le_left
  refine this ▸ limsSup_le_limsSup_of_le inf_le_right ?_ hb
  exact (IsBounded.mono inf_le_left (isBounded_ge_nhds x)).isCobounded_le

/--
theorem `ClusterPt.limsInf_le` / 定理 `ClusterPt.limsInf_le`

English:
theorem ClusterPt.limsInf_le
  statement: {f : Filter α} {x : α} (hx : ClusterPt x f)
  proof: hx.le_limsSup (α := αᵒᵈ)

中文:
定理 ClusterPt.limsInf_le
  结论: {f : 滤子 α} {x : α} (hx : ClusterPt x f)
  证明: hx.le_limsSup (α := αᵒᵈ)

Depends on / 依赖: f.limsInf, hx.le_limsSup, isBoundedDefault, le_limsSup, limsInf
-/
theorem ClusterPt.limsInf_le {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· >= ·) := by isBoundedDefault) :
    f.limsInf <= x :=
  hx.le_limsSup (α := αᵒᵈ)

/--
theorem `isGreatest_clusterPt_limsSup` / 定理 `isGreatest_clusterPt_limsSup`

English:
theorem isGreatest_clusterPt_limsSup
  statement: {f : Filter α} [NeBot f]
  proof: ⟨ClusterPt.limsSup, fun a ha => ha.le_limsSup⟩

中文:
定理 isGreatest_clusterPt_limsSup
  结论: {f : 滤子 α} [NeBot f]
  证明: ⟨ClusterPt.limsSup, fun a ha => ha.le_limsSup⟩

Depends on / 依赖: ClusterPt, ClusterPt.limsSup, IsBounded, IsGreatest, f.IsBounded, f.limsSup, ha.le_limsSup, isBoundedDefault, le_limsSup, limsSup
-/
theorem isGreatest_clusterPt_limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· <= ·) := by isBoundedDefault) :
    IsGreatest {x | ClusterPt x f} f.limsSup :=
  ⟨ClusterPt.limsSup, fun a ha => ha.le_limsSup⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isLeast_clusterPt_limsInf` / 定理 `isLeast_clusterPt_limsInf`

English:
theorem isLeast_clusterPt_limsInf
  statement: {f : Filter α} [NeBot f]
  proof: isGreatest_clusterPt_limsSup (α := αᵒᵈ)

中文:
定理 isLeast_clusterPt_limsInf
  结论: {f : 滤子 α} [NeBot f]
  证明: isGreatest_clusterPt_limsSup (α := αᵒᵈ)

Depends on / 依赖: ClusterPt, IsBounded, IsLeast, f.IsBounded, f.limsInf, isBoundedDefault, isGreatest_clusterPt_limsSup, limsInf
-/
theorem isLeast_clusterPt_limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· >= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· >= ·) := by isBoundedDefault) :
    IsLeast {x | ClusterPt x f} f.limsInf :=
  isGreatest_clusterPt_limsSup (α := αᵒᵈ)

/--
theorem `MapClusterPt.limsup` / 定理 `MapClusterPt.limsup`

English:
theorem MapClusterPt.limsup
  statement: {u : β -> α} {f : Filter β} [NeBot f]
  proof: ClusterPt.limsSup

中文:
定理 MapClusterPt.limsup
  结论: {u : β -> α} {f : 滤子 β} [NeBot f]
  证明: ClusterPt.limsSup

Depends on / 依赖: ClusterPt, ClusterPt.limsSup, IsBoundedUnder, MapClusterPt, f.limsup, isBoundedDefault, limsSup, limsup
-/
theorem MapClusterPt.limsup {u : β -> α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· <= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    MapClusterPt (f.limsup u) f u :=
  ClusterPt.limsSup

/--
theorem `MapClusterPt.liminf` / 定理 `MapClusterPt.liminf`

English:
theorem MapClusterPt.liminf
  statement: {u : β -> α} {f : Filter β} [NeBot f]
  proof: ClusterPt.limsInf

中文:
定理 MapClusterPt.liminf
  结论: {u : β -> α} {f : 滤子 β} [NeBot f]
  证明: ClusterPt.limsInf

Depends on / 依赖: ClusterPt, ClusterPt.limsInf, IsBoundedUnder, MapClusterPt, isBoundedDefault, liminf, limsInf
-/
theorem MapClusterPt.liminf {u : β -> α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· >= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· >= ·) f u := by isBoundedDefault) :
    MapClusterPt (liminf u f) f u :=
  ClusterPt.limsInf

/--
theorem `MapClusterPt.le_limsup` / 定理 `MapClusterPt.le_limsup`

English:
theorem MapClusterPt.le_limsup
  statement: {u : β -> α} {f : Filter β}
  proof: hx.le_limsSup

中文:
定理 MapClusterPt.le_limsup
  结论: {u : β -> α} {f : 滤子 β}
  证明: hx.le_limsSup

Depends on / 依赖: f.limsup, hx.le_limsSup, isBoundedDefault, le_limsSup, limsup
-/
theorem MapClusterPt.le_limsup {u : β -> α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    x <= f.limsup u :=
  hx.le_limsSup

/--
theorem `MapClusterPt.liminf_le` / 定理 `MapClusterPt.liminf_le`

English:
theorem MapClusterPt.liminf_le
  statement: {u : β -> α} {f : Filter β}
  proof: hx.limsInf_le

中文:
定理 MapClusterPt.liminf_le
  结论: {u : β -> α} {f : 滤子 β}
  证明: hx.limsInf_le

Depends on / 依赖: f.liminf, hx.limsInf_le, isBoundedDefault, liminf, limsInf_le
-/
theorem MapClusterPt.liminf_le {u : β -> α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· >= ·) f u := by isBoundedDefault) :
    f.liminf u <= x :=
  hx.limsInf_le

/--
theorem `isGreatest_mapClusterPt_limsup` / 定理 `isGreatest_mapClusterPt_limsup`

English:
theorem isGreatest_mapClusterPt_limsup
  statement: {u : β -> α} {f : Filter β} [NeBot f]
  proof: isGreatest_clusterPt_limsSup

中文:
定理 isGreatest_mapClusterPt_limsup
  结论: {u : β -> α} {f : 滤子 β} [NeBot f]
  证明: isGreatest_clusterPt_limsSup

Depends on / 依赖: IsBoundedUnder, IsGreatest, MapClusterPt, isBoundedDefault, isGreatest_clusterPt_limsSup, limsup
-/
theorem isGreatest_mapClusterPt_limsup {u : β -> α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· <= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    IsGreatest {x | MapClusterPt x f u} (limsup u f) :=
  isGreatest_clusterPt_limsSup

/--
theorem `isLeast_mapClusterPt_liminf` / 定理 `isLeast_mapClusterPt_liminf`

English:
theorem isLeast_mapClusterPt_liminf
  statement: {u : β -> α} {f : Filter β} [NeBot f]
  proof: isLeast_clusterPt_limsInf

中文:
定理 isLeast_mapClusterPt_liminf
  结论: {u : β -> α} {f : 滤子 β} [NeBot f]
  证明: isLeast_clusterPt_limsInf

Depends on / 依赖: IsBoundedUnder, IsLeast, MapClusterPt, isBoundedDefault, isLeast_clusterPt_limsInf, liminf
-/
theorem isLeast_mapClusterPt_liminf {u : β -> α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· >= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· >= ·) f u := by isBoundedDefault) :
    IsLeast {x | MapClusterPt x f u} (liminf u f) :=
  isLeast_clusterPt_limsInf

/--
theorem `tendsto_of_liminf_eq_limsup` / 定理 `tendsto_of_liminf_eq_limsup`

English:
theorem tendsto_of_liminf_eq_limsup
  statement: {f : Filter β} {u : β -> α} {a : α} (hinf : liminf u f = a)
  proof: le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

中文:
定理 tendsto_of_liminf_eq_limsup
  结论: {f : 滤子 β} {u : β -> α} {a : α} (hinf : liminf u f = a)
  证明: le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

Depends on / 依赖: IsBoundedUnder, Tendsto, f.IsBoundedUnder, isBoundedDefault, le_nhds_of_limsSup_eq_limsInf
-/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β -> α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a) (h : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

/--
theorem `tendsto_of_le_liminf_of_limsup_le` / 定理 `tendsto_of_le_liminf_of_limsup_le`

English:
theorem tendsto_of_le_liminf_of_limsup_le
  statement: {f : Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f)
  proof: by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

中文:
定理 tendsto_of_le_liminf_of_limsup_le
  结论: {f : 滤子 β} {u : β -> α} {a : α} (hinf : a <= liminf u f)
  证明: by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

Depends on / 依赖: IsBoundedUnder, Tendsto, eq_or_neBot, f.IsBoundedUnder, f.eq_or_neBot, isBoundedDefault, le_antisymm, le_trans, liminf_le_limsup, tendsto_bot, tendsto_of_liminf_eq_limsup
-/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f)
    (hsup : limsup u f <= a) (h : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) := by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

/--
theorem `tendsto_of_no_upcrossings` / 定理 `tendsto_of_no_upcrossings`

English:
theorem tendsto_of_no_upcrossings
  statement: [DenselyOrdered α] {f : Filter β} {u : β -> α} {s : Set α}
  proof: by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : exists a, (f.liminf u < a ∧ a < f.limsup u) ∧ a in s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : exists b, (a < b ∧ b < f.limsup u) ∧ b in s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : existsᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : existsᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

中文:
定理 tendsto_of_no_upcrossings
  结论: [稠密序 α] {f : 滤子 β} {u : β -> α} {s : 集合 α}
  证明: by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : exists a, (f.liminf u < a ∧ a < f.limsup u) ∧ a in s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : exists b, (a < b ∧ b < f.limsup u) ∧ b in s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : existsᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : existsᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

Depends on / 依赖: IsBoundedUnder, Set.Ioo, Set.nonempty_Ioo, Tendsto, dense_iff_inter_open, eq_or_neBot, f.IsBoundedUnder, f.eq_or_neBot, f.liminf, f.limsup, isBoundedDefault, isOpen_Ioo, le_rfl, liminf, limsup, nonempty_Ioo, tendsto_bot, tendsto_of_le_liminf_of_limsup_le
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β -> α} {s : Set α}
    (hs : Dense s) (H : forall a in s, forall b in s, a < b -> ¬((existsᶠ n in f, u n < a) ∧ existsᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· <= ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· >= ·) u := by isBoundedDefault) :
    exists c : α, Tendsto u f (𝓝 c) := by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : exists a, (f.liminf u < a ∧ a < f.limsup u) ∧ a in s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : exists b, (a < b ∧ b < f.limsup u) ∧ b in s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : existsᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : existsᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

variable [FirstCountableTopology α] {f : Filter α}

/--
theorem `exists_seq_tendsto_limsSup` / 定理 `exists_seq_tendsto_limsSup`

English:
theorem exists_seq_tendsto_limsSup
  statement: [NeBot f] [IsCountablyGenerated f]
  proof: (ClusterPt.limsSup).exists_seq_tendsto

中文:
定理 存在_seq_tendsto_limsSup
  结论: [NeBot f] [是余untablyGenerated f]
  证明: (ClusterPt.limsSup).exists_seq_tendsto

Depends on / 依赖: ClusterPt, ClusterPt.limsSup, IsBounded, Tendsto, exists_seq_tendsto, f.IsBounded, f.limsSup, isBoundedDefault, limsSup
-/
theorem exists_seq_tendsto_limsSup [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· <= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· <= ·) := by isBoundedDefault) :
    exists x : Nat -> α, Tendsto x atTop (𝓝 f.limsSup) ∧ Tendsto x atTop f :=
  (ClusterPt.limsSup).exists_seq_tendsto

/--
theorem `exists_seq_tendsto_limsInf` / 定理 `exists_seq_tendsto_limsInf`

English:
theorem exists_seq_tendsto_limsInf
  statement: [NeBot f] [IsCountablyGenerated f]
  proof: (ClusterPt.limsInf).exists_seq_tendsto

中文:
定理 存在_seq_tendsto_limsInf
  结论: [NeBot f] [是余untablyGenerated f]
  证明: (ClusterPt.limsInf).exists_seq_tendsto

Depends on / 依赖: ClusterPt, ClusterPt.limsInf, IsBounded, Tendsto, exists_seq_tendsto, f.IsBounded, f.limsInf, isBoundedDefault, limsInf
-/
theorem exists_seq_tendsto_limsInf [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· >= ·) := by isBoundedDefault)
    (hb : f.IsBounded (· >= ·) := by isBoundedDefault) :
    exists x : Nat -> α, Tendsto x atTop (𝓝 f.limsInf) ∧ Tendsto x atTop f :=
  (ClusterPt.limsInf).exists_seq_tendsto

variable {f : Filter β}

/--
theorem `exists_seq_tendsto_limsup` / 定理 `exists_seq_tendsto_limsup`

English:
theorem exists_seq_tendsto_limsup
  statement: [NeBot f] [IsCountablyGenerated f] {u : β -> α}
  proof: (MapClusterPt.limsup).exists_seq_tendsto

中文:
定理 存在_seq_tendsto_limsup
  结论: [NeBot f] [是余untablyGenerated f] {u : β -> α}
  证明: (MapClusterPt.limsup).exists_seq_tendsto

Depends on / 依赖: IsBoundedUnder, MapClusterPt, MapClusterPt.limsup, Tendsto, exists_seq_tendsto, isBoundedDefault, limsup
-/
theorem exists_seq_tendsto_limsup [NeBot f] [IsCountablyGenerated f] {u : β -> α}
    (hc : IsCoboundedUnder (· <= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    exists x : Nat -> β, Tendsto (u ∘ x) atTop (𝓝 (limsup u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.limsup).exists_seq_tendsto

/--
theorem `exists_seq_tendsto_liminf` / 定理 `exists_seq_tendsto_liminf`

English:
theorem exists_seq_tendsto_liminf
  statement: [NeBot f] {u : β -> α} [IsCountablyGenerated f]
  proof: (MapClusterPt.liminf).exists_seq_tendsto

中文:
定理 存在_seq_tendsto_liminf
  结论: [NeBot f] {u : β -> α} [是余untablyGenerated f]
  证明: (MapClusterPt.liminf).exists_seq_tendsto

Depends on / 依赖: IsBoundedUnder, MapClusterPt, MapClusterPt.liminf, Tendsto, exists_seq_tendsto, isBoundedDefault, liminf
-/
theorem exists_seq_tendsto_liminf [NeBot f] {u : β -> α} [IsCountablyGenerated f]
    (hc : IsCoboundedUnder (· >= ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· >= ·) f u := by isBoundedDefault) :
    exists x : Nat -> β, Tendsto (u ∘ x) atTop (𝓝 (liminf u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.liminf).exists_seq_tendsto

variable [CountableInterFilter f] {u : β -> α}

/--
theorem `eventually_le_limsup` / 定理 `eventually_le_limsup`

English:
theorem eventually_le_limsup
  given: (hf : IsBoundedUnder (· <= ·) f u := by isBoundedDefault)
  proof: by
  rw [eventually_le_const_iff_forall_gt_eventually_lt_const]
  exact fun _ hc => eventually_lt_of_limsup_lt hc

中文:
定理 eventually_le_limsup
  条件: (hf : IsBoundedUnder (· <= ·) f u := by isBoundedDefault)
  证明: by
  rw [eventually_le_const_iff_forall_gt_eventually_lt_const]
  exact fun _ hc => eventually_lt_of_limsup_lt hc

Depends on / 依赖: eventually_le_const_iff_forall_gt_eventually_lt_const, eventually_lt_of_limsup_lt, f.limsup, isBoundedDefault, limsup
-/
theorem eventually_le_limsup (hf : IsBoundedUnder (· <= ·) f u := by isBoundedDefault) :
    forallᶠ b in f, u b <= f.limsup u := by
  rw [eventually_le_const_iff_forall_gt_eventually_lt_const]
  exact fun _ hc => eventually_lt_of_limsup_lt hc

/--
theorem `eventually_liminf_le` / 定理 `eventually_liminf_le`

English:
theorem eventually_liminf_le
  given: (hf : IsBoundedUnder (· >= ·) f u := by isBoundedDefault)
  proof: eventually_le_limsup (α := αᵒᵈ) hf

中文:
定理 eventually_liminf_le
  条件: (hf : IsBoundedUnder (· >= ·) f u := by isBoundedDefault)
  证明: eventually_le_limsup (α := αᵒᵈ) hf

Depends on / 依赖: eventually_le_limsup, f.liminf, isBoundedDefault, liminf
-/
theorem eventually_liminf_le (hf : IsBoundedUnder (· >= ·) f u := by isBoundedDefault) :
    forallᶠ b in f, f.liminf u <= u b :=
  eventually_le_limsup (α := αᵒᵈ) hf

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β -> α}

@[simp]
/--
theorem `limsup_eq_bot` / 定理 `limsup_eq_bot`

English:
theorem limsup_eq_bot
  statement: f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
  proof: ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| Eventually.of_forall fun _ => h.le).mono fun _ hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩

@[simp]

中文:
定理 limsup_eq_bot
  结论: f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
  证明: ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| Eventually.of_forall fun _ => h.le).mono fun _ hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyLE, EventuallyLE.trans, bot_le, eventually_le_limsup, h.le, le_antisymm, limsup_congr, limsup_const_bot, of_forall
-/
theorem limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥ :=
  ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| Eventually.of_forall fun _ => h.le).mono fun _ hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩

@[simp]
/--
theorem `liminf_eq_top` / 定理 `liminf_eq_top`

English:
theorem liminf_eq_top
  statement: f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤
  proof: limsup_eq_bot (α := αᵒᵈ)

中文:
定理 liminf_eq_top
  结论: f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤
  证明: limsup_eq_bot (α := αᵒᵈ)

Depends on / 依赖: limsup_eq_bot
-/
theorem liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤ :=
  limsup_eq_bot (α := αᵒᵈ)

/--
lemma `tendsto_iSup_of_tendsto_limsup` / 引理 `tendsto_iSup_of_tendsto_limsup`

English:
lemma tendsto_iSup_of_tendsto_limsup
  statement: {α β : Type*} [ConditionallyCompleteLattice α]
  proof: by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n0⟩⟩
  · simpa using! h_limsup
  refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards with r
    have : c <= u n0 r := (h_anti n0).le_of_tendsto (h_all n0) r
    exact hb.trans_le (this.trans (le_iSup_iff.mpr fun b a => a n0))
  -- `⊢ ∀ᶠ (b_1 : α) in atTop, ⨆ i, u i b_1 < b` for `b > c`
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have : forallᶠ r in atTop, limsup (u · r) cofinite <= b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr using hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (u · r) cofinite, h, hr⟩
  obtain ⟨r, hr⟩ : exists r, forall s >= r, limsup (u · s) cofinite <= b' := by simpa using! this
  obtain ⟨b'', hb''b, hb''⟩ : exists b'' in Set.Ico b' b, forallᶠ n in cofinite, u n r <= b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b)
      filter_upwards [h_lt] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩ , ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b'')
      filter_upwards [h_lt] with n hn using hn.le
  have A (n) : exists r, forall s >= r, u n s <= b'' := by
    suffices forallᶠ r in atTop, u n r <= b' by
      simp only [eventually_atTop] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs => (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv => ?_⟩
  -- `⊢ ⨆ i, u i v < b`
  apply lt_of_le_of_lt (iSup_le fun n => ?_) hb''b.2
  -- `⊢ u n v ≤ b''` for `v` such that `r ⊔ (⨆ n, rs n) ≤ v`
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
    _ <= ⨆ n : {n | b'' < u n r}, rs n := by
      refine le_ciSup (f := fun (x : {n | b'' < u n r}) => rs x) ?_
        (⟨n, by simp [hn]⟩ : {n | b'' < u n r})
      have : Finite {n | b'' < u n r} := by simpa using! hb''
      exact Finite.bddAbove_range _
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
    _ <= v := hv
  · refine (h_anti n ?_).trans (not_lt.mp hn)
    calc r
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
    _ <= v := hv

中文:
引理 tendsto_iSup_of_tendsto_limsup
  结论: {α β : 类型} [条件完备格 α]
  证明: by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n0⟩⟩
  · simpa using! h_limsup
  refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards with r
    have : c <= u n0 r := (h_anti n0).le_of_tendsto (h_all n0) r
    exact hb.trans_le (this.trans (le_iSup_iff.mpr fun b a => a n0))
  -- `⊢ ∀ᶠ (b_1 : α) in atTop, ⨆ i, u i b_1 < b` for `b > c`
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have : forallᶠ r in atTop, limsup (u · r) cofinite <= b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr using hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (u · r) cofinite, h, hr⟩
  obtain ⟨r, hr⟩ : exists r, forall s >= r, limsup (u · s) cofinite <= b' := by simpa using! this
  obtain ⟨b'', hb''b, hb''⟩ : exists b'' in Set.Ico b' b, forallᶠ n in cofinite, u n r <= b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b)
      filter_upwards [h_lt] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩ , ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b'')
      filter_upwards [h_lt] with n hn using hn.le
  have A (n) : exists r, forall s >= r, u n s <= b'' := by
    suffices forallᶠ r in atTop, u n r <= b' by
      simp only [eventually_atTop] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs => (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv => ?_⟩
  -- `⊢ ⨆ i, u i v < b`
  apply lt_of_le_of_lt (iSup_le fun n => ?_) hb''b.2
  -- `⊢ u n v ≤ b''` for `v` such that `r ⊔ (⨆ n, rs n) ≤ v`
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
    _ <= ⨆ n : {n | b'' < u n r}, rs n := by
      refine le_ciSup (f := fun (x : {n | b'' < u n r}) => rs x) ?_
        (⟨n, by simp [hn]⟩ : {n | b'' < u n r})
      have : Finite {n | b'' < u n r} := by simpa using! hb''
      exact Finite.bddAbove_range _
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
    _ <= v := hv
  · refine (h_anti n ?_).trans (not_lt.mp hn)
    calc r
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
    _ <= v := hv

Depends on / 依赖: classical, filter_upwards, h_all, h_anti, h_limsup, hb.trans_le, isEmpty_or_nonempty, le_iSup_iff, le_iSup_iff.mpr, le_of_tendsto, tendsto_order, tendsto_order.mpr, this.trans, trans_le
-/
lemma tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLattice α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {u : ι -> α -> β} {c : β}
    (h_all : forall i, Tendsto (u i) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α => limsup (fun i => u i r) cofinite) atTop (𝓝 c))
    (h_anti : forall i, Antitone (u i)) :
    Tendsto (fun r : α => ⨆ i, u i r) atTop (𝓝 c) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n0⟩⟩
  · simpa using! h_limsup
  refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards with r
    have : c <= u n0 r := (h_anti n0).le_of_tendsto (h_all n0) r
    exact hb.trans_le (this.trans (le_iSup_iff.mpr fun b a => a n0))
  -- `⊢ ∀ᶠ (b_1 : α) in atTop, ⨆ i, u i b_1 < b` for `b > c`
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have : forallᶠ r in atTop, limsup (u · r) cofinite <= b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr using hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (u · r) cofinite, h, hr⟩
  obtain ⟨r, hr⟩ : exists r, forall s >= r, limsup (u · s) cofinite <= b' := by simpa using! this
  obtain ⟨b'', hb''b, hb''⟩ : exists b'' in Set.Ico b' b, forallᶠ n in cofinite, u n r <= b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b)
      filter_upwards [h_lt] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩ , ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b'')
      filter_upwards [h_lt] with n hn using hn.le
  have A (n) : exists r, forall s >= r, u n s <= b'' := by
    suffices forallᶠ r in atTop, u n r <= b' by
      simp only [eventually_atTop] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs => (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv => ?_⟩
  -- `⊢ ⨆ i, u i v < b`
  apply lt_of_le_of_lt (iSup_le fun n => ?_) hb''b.2
  -- `⊢ u n v ≤ b''` for `v` such that `r ⊔ (⨆ n, rs n) ≤ v`
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
    _ <= ⨆ n : {n | b'' < u n r}, rs n := by
      refine le_ciSup (f := fun (x : {n | b'' < u n r}) => rs x) ?_
        (⟨n, by simp [hn]⟩ : {n | b'' < u n r})
      have : Finite {n | b'' < u n r} := by simpa using! hb''
      exact Finite.bddAbove_range _
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
    _ <= v := hv
  · refine (h_anti n ?_).trans (not_lt.mp hn)
    calc r
    _ <= r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
    _ <= v := hv

/--
lemma `Nat.tendsto_iSup_of_tendsto_limsup` / 引理 `Nat.tendsto_iSup_of_tendsto_limsup`

English:
lemma Nat.tendsto_iSup_of_tendsto_limsup
  statement: {α β : Type*} [ConditionallyCompleteLattice α]
  proof: by
  rw [← cofinite_eq_atTop] at h_limsup
  exact _root_.tendsto_iSup_of_tendsto_limsup h_all h_limsup h_anti

中文:
引理 自然数.tendsto_iSup_of_tendsto_limsup
  结论: {α β : 类型} [条件完备格 α]
  证明: by
  rw [← cofinite_eq_atTop] at h_limsup
  exact _root_.tendsto_iSup_of_tendsto_limsup h_all h_limsup h_anti

Depends on / 依赖: _root_, _root_.tendsto_iSup_of_tendsto_limsup, cofinite_eq_atTop, h_all, h_anti, h_limsup, tendsto_iSup_of_tendsto_limsup
-/
lemma Nat.tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLattice α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {u : Nat -> α -> β} {c : β}
    (h_all : forall n, Tendsto (u n) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α => limsup (fun n => u n r) atTop) atTop (𝓝 c))
    (h_anti : forall n, Antitone (u n)) :
    Tendsto (fun r : α => ⨆ n, u n r) atTop (𝓝 c) := by
  rw [← cofinite_eq_atTop] at h_limsup
  exact _root_.tendsto_iSup_of_tendsto_limsup h_all h_limsup h_anti

end CompleteLinearOrder

end LiminfLimsup

section Monotone

variable {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/--
theorem `Antitone.map_limsSup_of_continuousAt` / 定理 `Antitone.map_limsSup_of_continuousAt`

English:
theorem Antitone.map_limsSup_of_continuousAt
  statement: {F : Filter R} [NeBot F] {f : R -> S}
  proof: by
  apply le_antisymm
  · rw [limsSup, f_decr.map_csInf_of_continuousAt f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx => ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · simpa only [BddAbove, upperBounds]
        using! Antitone.isCoboundedUnder_ge_of_isCobounded f_decr cobdd
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases! h' : exists c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : existsᶠ n in F, F.limsSup <= n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact B.mono fun x hx => f_decr hx
    by_contra! H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot =>
lt_irrefl (F.liminf f) lt_of_le_of_lt
        (liminf_le_of_frequently_le (Frequently.of_forall (fun r => f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ :
        exists l < F.limsSup, Set.Ioc l F.limsSup subseteq { x : R | f x < F.liminf f } := by
      apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using! not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      exact ⟨l, l_lt, h'⟩
    have B : F.liminf f <= f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx => f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

中文:
定理 递减.map_limsSup_of_continuousAt
  结论: {F : 滤子 R} [NeBot F] {f : R -> S}
  证明: by
  apply le_antisymm
  · rw [limsSup, f_decr.map_csInf_of_continuousAt f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx => ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · simpa only [BddAbove, upperBounds]
        using! Antitone.isCoboundedUnder_ge_of_isCobounded f_decr cobdd
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases! h' : exists c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : existsᶠ n in F, F.limsSup <= n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact B.mono fun x hx => f_decr hx
    by_contra! H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot =>
lt_irrefl (F.liminf f) lt_of_le_of_lt
        (liminf_le_of_frequently_le (Frequently.of_forall (fun r => f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ :
        exists l < F.limsSup, Set.Ioc l F.limsSup subseteq { x : R | f x < F.liminf f } := by
      apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using! not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      exact ⟨l, l_lt, h'⟩
    have B : F.liminf f <= f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx => f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

Depends on / 依赖: Antitone, Antitone.isCoboundedUnder_ge_, BddAbove, F.IsCobounded, F.liminf, F.limsSup, IsCobounded, Set.mem_image_of_mem, bdd_above, bdd_above.recOn, eventually_map, exists_lt_of_lt_csSup, f_cont, f_decr, f_decr.map_csInf_of_continuousAt, isBoundedDefault, isCoboundedUnder_ge_, le_antisymm, le_of_forall_lt, liminf
-/
theorem Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· <= ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· <= ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  apply le_antisymm
  · rw [limsSup, f_decr.map_csInf_of_continuousAt f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx => ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · simpa only [BddAbove, upperBounds]
        using! Antitone.isCoboundedUnder_ge_of_isCobounded f_decr cobdd
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases! h' : exists c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : existsᶠ n in F, F.limsSup <= n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact B.mono fun x hx => f_decr hx
    by_contra! H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot =>
lt_irrefl (F.liminf f) lt_of_le_of_lt
        (liminf_le_of_frequently_le (Frequently.of_forall (fun r => f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ :
        exists l < F.limsSup, Set.Ioc l F.limsSup subseteq { x : R | f x < F.liminf f } := by
      apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using! not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      exact ⟨l, l_lt, h'⟩
    have B : F.liminf f <= f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx => f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

/--
theorem `Antitone.map_limsup_of_continuousAt` / 定理 `Antitone.map_limsup_of_continuousAt`

English:
theorem Antitone.map_limsup_of_continuousAt
  statement: {f : R -> S} (f_decr : Antitone f) (a : ι -> R)
  proof: f_decr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

中文:
定理 递减.map_limsup_of_continuousAt
  结论: {f : R -> S} (f_decr : 递减 f) (a : ι -> R)
  证明: f_decr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

Depends on / 依赖: F.IsCoboundedUnder, F.liminf, F.limsup, IsCoboundedUnder, bdd_above, f_cont, f_decr, f_decr.map_limsSup_of_continuousAt, isBoundedDefault, liminf, limsup, map_limsSup_of_continuousAt
-/
theorem Antitone.map_limsup_of_continuousAt {f : R -> S} (f_decr : Antitone f) (a : ι -> R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· <= ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· <= ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Antitone.map_limsInf_of_continuousAt` / 定理 `Antitone.map_limsInf_of_continuousAt`

English:
theorem Antitone.map_limsInf_of_continuousAt
  statement: {F : Filter R} [NeBot F] {f : R -> S}
  proof: Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below cobdd

中文:
定理 递减.map_limsInf_of_continuousAt
  结论: {F : 滤子 R} [NeBot F] {f : R -> S}
  证明: Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below cobdd

Depends on / 依赖: Antitone, Antitone.map_limsSup_of_continuousAt, F.IsBounded, F.limsInf, F.limsup, IsBounded, bdd_below, f_cont, f_decr, f_decr.dual, isBoundedDefault, limsInf, limsup, map_limsSup_of_continuousAt
-/
theorem Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· >= ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· >= ·) := by isBoundedDefault) : f F.limsInf = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below cobdd

/--
theorem `Antitone.map_liminf_of_continuousAt` / 定理 `Antitone.map_liminf_of_continuousAt`

English:
theorem Antitone.map_liminf_of_continuousAt
  statement: {f : R -> S} (f_decr : Antitone f) (a : ι -> R)
  proof: f_decr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

中文:
定理 递减.map_liminf_of_continuousAt
  结论: {f : R -> S} (f_decr : 递减 f) (a : ι -> R)
  证明: f_decr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

Depends on / 依赖: F.IsBoundedUnder, F.liminf, F.limsup, IsBoundedUnder, bdd_below, f_cont, f_decr, f_decr.map_limsInf_of_continuousAt, isBoundedDefault, liminf, limsup, map_limsInf_of_continuousAt
-/
theorem Antitone.map_liminf_of_continuousAt {f : R -> S} (f_decr : Antitone f) (a : ι -> R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· >= ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· >= ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

/--
theorem `Monotone.map_limsSup_of_continuousAt` / 定理 `Monotone.map_limsSup_of_continuousAt`

English:
theorem Monotone.map_limsSup_of_continuousAt
  statement: {F : Filter R} [NeBot F] {f : R -> S}
  proof: Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above cobdd

中文:
定理 递增.map_limsSup_of_continuousAt
  结论: {F : 滤子 R} [NeBot F] {f : R -> S}
  证明: Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above cobdd

Depends on / 依赖: Antitone, Antitone.map_limsSup_of_continuousAt, F.IsCobounded, F.limsSup, F.limsup, IsCobounded, bdd_above, f_cont, f_incr, isBoundedDefault, limsSup, limsup, map_limsSup_of_continuousAt
-/
theorem Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· <= ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· <= ·) := by isBoundedDefault) : f F.limsSup = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above cobdd

/--
theorem `Monotone.map_limsup_of_continuousAt` / 定理 `Monotone.map_limsup_of_continuousAt`

English:
theorem Monotone.map_limsup_of_continuousAt
  statement: {f : R -> S} (f_incr : Monotone f) (a : ι -> R)
  proof: f_incr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

中文:
定理 递增.map_limsup_of_continuousAt
  结论: {f : R -> S} (f_incr : 递增 f) (a : ι -> R)
  证明: f_incr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

Depends on / 依赖: F.IsCoboundedUnder, F.limsup, IsCoboundedUnder, bdd_above, f_cont, f_incr, f_incr.map_limsSup_of_continuousAt, isBoundedDefault, limsup, map_limsSup_of_continuousAt
-/
theorem Monotone.map_limsup_of_continuousAt {f : R -> S} (f_incr : Monotone f) (a : ι -> R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· <= ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· <= ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Monotone.map_limsInf_of_continuousAt` / 定理 `Monotone.map_limsInf_of_continuousAt`

English:
theorem Monotone.map_limsInf_of_continuousAt
  statement: {F : Filter R} [NeBot F] {f : R -> S}
  proof: Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below cobdd

中文:
定理 递增.map_limsInf_of_continuousAt
  结论: {F : 滤子 R} [NeBot F] {f : R -> S}
  证明: Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below cobdd

Depends on / 依赖: Antitone, Antitone.map_limsSup_of_continuousAt, F.IsBounded, F.liminf, F.limsInf, IsBounded, bdd_below, f_cont, f_incr, f_incr.dual, isBoundedDefault, liminf, limsInf, map_limsSup_of_continuousAt
-/
theorem Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· >= ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· >= ·) := by isBoundedDefault) : f F.limsInf = F.liminf f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below cobdd

/--
theorem `Monotone.map_liminf_of_continuousAt` / 定理 `Monotone.map_liminf_of_continuousAt`

English:
theorem Monotone.map_liminf_of_continuousAt
  statement: {f : R -> S} (f_incr : Monotone f) (a : ι -> R)
  proof: f_incr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

中文:
定理 递增.map_liminf_of_continuousAt
  结论: {f : R -> S} (f_incr : 递增 f) (a : ι -> R)
  证明: f_incr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

Depends on / 依赖: F.IsBoundedUnder, F.liminf, IsBoundedUnder, bdd_below, f_cont, f_incr, f_incr.map_limsInf_of_continuousAt, isBoundedDefault, liminf, map_limsInf_of_continuousAt
-/
theorem Monotone.map_liminf_of_continuousAt {f : R -> S} (f_incr : Monotone f) (a : ι -> R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· >= ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· >= ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

end Monotone

section CompleteLattice

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [CompleteLattice β] {f : α -> β}

/--
lemma `Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt` / 引理 `Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt`

English:
lemma Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt
  given: (hf : Antitone f) (a : α) (hb : exists b, a < b)
  proof: by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, iInf₂_le b hb⟩

中文:
引理 递减.liminf_nhdsGT_eq_iSup₂_of_存在_gt
  条件: (hf : 递减 f) (a : α) (hb : 存在 b, a < b)
  证明: by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, iInf₂_le b hb⟩

Depends on / 依赖: Set.mem_Ioo, exists_between, le_antisymm, liminf_eq_iSup_iInf, mem_Ioo, nhdsGT_basis_of_exists_gt
-/
lemma Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt (hf : Antitone f) (a : α) (hb : exists b, a < b) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r := by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, iInf₂_le b hb⟩

/--
lemma `Antitone.liminf_nhdsGT_eq_iSup₂` / 引理 `Antitone.liminf_nhdsGT_eq_iSup₂`

English:
lemma Antitone.liminf_nhdsGT_eq_iSup₂
  given: [NoMaxOrder α] (hf : Antitone f) (a : α)
  proof: hf.liminf_nhdsGT_eq_iSup₂_of_exists_gt a (exists_gt a)

中文:
引理 递减.liminf_nhdsGT_eq_iSup₂
  条件: [NoMax序 α] (hf : 递减 f) (a : α)
  证明: hf.liminf_nhdsGT_eq_iSup₂_of_exists_gt a (exists_gt a)

Depends on / 依赖: exists_gt, hf.liminf_nhdsGT_eq_iSup
-/
lemma Antitone.liminf_nhdsGT_eq_iSup₂ [NoMaxOrder α] (hf : Antitone f) (a : α) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r :=
  hf.liminf_nhdsGT_eq_iSup₂_of_exists_gt a (exists_gt a)

/--
lemma `Monotone.liminf_nhdsLT_eq_iSup₂_of_exists_lt` / 引理 `Monotone.liminf_nhdsLT_eq_iSup₂_of_exists_lt`

English:
lemma Monotone.liminf_nhdsLT_eq_iSup₂_of_exists_lt
  given: (hf : Monotone f) (a : α) (hb : exists b, b < a)
  proof: by
  rw [(nhdsLT_basis_of_exists_lt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, iInf₂_le b hb⟩

中文:
引理 递增.liminf_nhdsLT_eq_iSup₂_of_存在_lt
  条件: (hf : 递增 f) (a : α) (hb : 存在 b, b < a)
  证明: by
  rw [(nhdsLT_basis_of_exists_lt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, iInf₂_le b hb⟩

Depends on / 依赖: Set.mem_Ioo, exists_between, le_antisymm, liminf_eq_iSup_iInf, mem_Ioo, nhdsLT_basis_of_exists_lt
-/
lemma Monotone.liminf_nhdsLT_eq_iSup₂_of_exists_lt (hf : Monotone f) (a : α) (hb : exists b, b < a) :
    (𝓝[<] a).liminf f = ⨆ r < a, f r := by
  rw [(nhdsLT_basis_of_exists_lt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr => ?_)
    (iSup₂_mono' fun r hr => ⟨r, hr, le_iInf₂ fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, iInf₂_le b hb⟩

/--
lemma `Monotone.liminf_nhdsLT_eq_iSup₂` / 引理 `Monotone.liminf_nhdsLT_eq_iSup₂`

English:
lemma Monotone.liminf_nhdsLT_eq_iSup₂
  given: [NoMinOrder α] (hf : Monotone f) (a : α)
  proof: hf.liminf_nhdsLT_eq_iSup₂_of_exists_lt a (exists_lt a)

中文:
引理 递增.liminf_nhdsLT_eq_iSup₂
  条件: [NoMin序 α] (hf : 递增 f) (a : α)
  证明: hf.liminf_nhdsLT_eq_iSup₂_of_exists_lt a (exists_lt a)

Depends on / 依赖: exists_lt, hf.liminf_nhdsLT_eq_iSup
-/
lemma Monotone.liminf_nhdsLT_eq_iSup₂ [NoMinOrder α] (hf : Monotone f) (a : α) :
    (𝓝[<] a).liminf f = ⨆ r < a, f r :=
  hf.liminf_nhdsLT_eq_iSup₂_of_exists_lt a (exists_lt a)

/--
lemma `Monotone.limsup_nhdsGT_eq_iInf₂_of_exists_gt` / 引理 `Monotone.limsup_nhdsGT_eq_iInf₂_of_exists_gt`

English:
lemma Monotone.limsup_nhdsGT_eq_iInf₂_of_exists_gt
  given: (hf : Monotone f) (a : α) (hb : exists b, a < b)
  proof: by
  rw [(nhdsGT_basis_of_exists_gt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, le_iSup₂_of_le b hb le_rfl⟩

中文:
引理 递增.limsup_nhdsGT_eq_iInf₂_of_存在_gt
  条件: (hf : 递增 f) (a : α) (hb : 存在 b, a < b)
  证明: by
  rw [(nhdsGT_basis_of_exists_gt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, le_iSup₂_of_le b hb le_rfl⟩

Depends on / 依赖: Set.mem_Ioo, exists_between, le_antisymm, le_rfl, limsup_eq_iInf_iSup, mem_Ioo, nhdsGT_basis_of_exists_gt
-/
lemma Monotone.limsup_nhdsGT_eq_iInf₂_of_exists_gt (hf : Monotone f) (a : α) (hb : exists b, a < b) :
    (𝓝[>] a).limsup f = ⨅ r > a, f r := by
  rw [(nhdsGT_basis_of_exists_gt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).2.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, le_iSup₂_of_le b hb le_rfl⟩

/--
lemma `Monotone.limsup_nhdsGT_eq_iInf₂` / 引理 `Monotone.limsup_nhdsGT_eq_iInf₂`

English:
lemma Monotone.limsup_nhdsGT_eq_iInf₂
  given: [NoMaxOrder α] (hf : Monotone f) (a : α)
  proof: hf.limsup_nhdsGT_eq_iInf₂_of_exists_gt a (exists_gt a)

中文:
引理 递增.limsup_nhdsGT_eq_iInf₂
  条件: [NoMax序 α] (hf : 递增 f) (a : α)
  证明: hf.limsup_nhdsGT_eq_iInf₂_of_exists_gt a (exists_gt a)

Depends on / 依赖: exists_gt, hf.limsup_nhdsGT_eq_iInf
-/
lemma Monotone.limsup_nhdsGT_eq_iInf₂ [NoMaxOrder α] (hf : Monotone f) (a : α) :
    (𝓝[>] a).limsup f = ⨅ r > a, f r :=
  hf.limsup_nhdsGT_eq_iInf₂_of_exists_gt a (exists_gt a)

/--
lemma `Antitone.limsup_nhdsLT_eq_iInf₂_of_exists_lt` / 引理 `Antitone.limsup_nhdsLT_eq_iInf₂_of_exists_lt`

English:
lemma Antitone.limsup_nhdsLT_eq_iInf₂_of_exists_lt
  given: (hf : Antitone f) (a : α) (hb : exists b, b < a)
  proof: by
  rw [(nhdsLT_basis_of_exists_lt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, le_iSup₂_of_le b hb le_rfl⟩

中文:
引理 递减.limsup_nhdsLT_eq_iInf₂_of_存在_lt
  条件: (hf : 递减 f) (a : α) (hb : 存在 b, b < a)
  证明: by
  rw [(nhdsLT_basis_of_exists_lt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, le_iSup₂_of_le b hb le_rfl⟩

Depends on / 依赖: Set.mem_Ioo, exists_between, le_antisymm, le_rfl, limsup_eq_iInf_iSup, mem_Ioo, nhdsLT_basis_of_exists_lt
-/
lemma Antitone.limsup_nhdsLT_eq_iInf₂_of_exists_lt (hf : Antitone f) (a : α) (hb : exists b, b < a) :
    (𝓝[<] a).limsup f = ⨅ r < a, f r := by
  rw [(nhdsLT_basis_of_exists_lt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr => ⟨r, hr, iSup₂_le fun i hi => hf (Set.mem_Ioo.1 hi).1.le⟩)
    (iInf₂_mono' fun r hr => ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, le_iSup₂_of_le b hb le_rfl⟩

/--
lemma `Antitone.limsup_nhdsLT_eq_iInf₂` / 引理 `Antitone.limsup_nhdsLT_eq_iInf₂`

English:
lemma Antitone.limsup_nhdsLT_eq_iInf₂
  given: [NoMinOrder α] (hf : Antitone f) (a : α)
  proof: hf.limsup_nhdsLT_eq_iInf₂_of_exists_lt a (exists_lt a)

中文:
引理 递减.limsup_nhdsLT_eq_iInf₂
  条件: [NoMin序 α] (hf : 递减 f) (a : α)
  证明: hf.limsup_nhdsLT_eq_iInf₂_of_exists_lt a (exists_lt a)

Depends on / 依赖: exists_lt, hf.limsup_nhdsLT_eq_iInf
-/
lemma Antitone.limsup_nhdsLT_eq_iInf₂ [NoMinOrder α] (hf : Antitone f) (a : α) :
    (𝓝[<] a).limsup f = ⨅ r < a, f r :=
  hf.limsup_nhdsLT_eq_iInf₂_of_exists_lt a (exists_lt a)

end CompleteLattice
