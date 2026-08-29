/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopology` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopology` vs `ClosedIicTopology`,
`Preorder` vs `PartialOrder` vs `LinearOrder`, etc.)
see their statements.

### Open / closed sets

* `isOpen_lt` : if `f` and `g` are continuous functions, then `{x | f x < g x}` is open;
* `isOpen_Iio`, `isOpen_Ioi`, `isOpen_Ioo` : open intervals are open;
* `isClosed_le` : if `f` and `g` are continuous functions, then `{x | f x ≤ g x}` is closed;
* `isClosed_Iic`, `isClosed_Ici`, `isClosed_Icc` : closed intervals are closed;
* `frontier_le_subset_eq`, `frontier_lt_subset_eq` : frontiers of both `{x | f x ≤ g x}`
  and `{x | f x < g x}` are included by `{x | f x = g x}`;

### Convergence and inequalities

* `le_of_tendsto_of_tendsto` : if `f` converges to `a`, `g` converges to `b`, and eventually
  `f x ≤ g x`, then `a ≤ b`
* `le_of_tendsto`, `ge_of_tendsto` : if `f` converges to `a` and eventually `f x ≤ b`
  (resp., `b ≤ f x`), then `a ≤ b` (resp., `b ≤ a`); we also provide primed versions
  that assume the inequalities to hold for all `x`.
* `monotone_of_frequently_monotone_of_tendsto`, `antitone_of_frequently_antitone_of_tendsto` : the
  pointwise limit of frequently monotone or antitone functions is monotone or antitone.

### Min, max, `sSup` and `sInf`

* `Continuous.min`, `Continuous.max`: pointwise `min`/`max` of two continuous functions is
  continuous.
* `Tendsto.min`, `Tendsto.max` : if `f` tends to `a` and `g` tends to `b`, then their pointwise
  `min`/`max` tend to `min a b` and `max a b`, respectively.
-/

public section

open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/--
Definition of `ClosedIicTopology` / `ClosedIicTopology` 的定义

English:
class ClosedIicTopology
  parameters: (α : Type*) [TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - isClosed_Iic((a : α)) : IsClosed (Iic a)

中文:
类 ClosedIicTopology
  参数: (α : 类型) [TopologicalSpace α] [Preorder α]
  公理与运算 (1 个):
    - isClosed_Iic((a : α)) : IsClosed (Iic a)
-/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)

/-- If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `Ici a` is
closed for all `a : α`. -/
@[to_dual existing]
/--
Definition of `ClosedIciTopology` / `ClosedIciTopology` 的定义

English:
class ClosedIciTopology
  parameters: (α : Type*) [TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - isClosed_Ici((a : α)) : IsClosed (Ici a)

中文:
类 ClosedIciTopology
  参数: (α : 类型) [TopologicalSpace α] [Preorder α]
  公理与运算 (1 个):
    - isClosed_Ici((a : α)) : IsClosed (Ici a)
-/
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `[a, +∞)` is closed. -/
  isClosed_Ici (a : α) : IsClosed (Ici a)

/--
Definition of `OrderClosedTopology` / `OrderClosedTopology` 的定义

English:
class OrderClosedTopology
  parameters: (α : Type*) [TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - isClosed_le' : IsClosed { p : α × α | p.1 <= p.2 }

中文:
类 OrderClosedTopology
  参数: (α : 类型) [TopologicalSpace α] [Preorder α]
  公理与运算 (1 个):
    - isClosed_le' : IsClosed { p : α × α | p.1 <= p.2 }
-/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  protected isClosed_le' : IsClosed { p : α × α | p.1 <= p.2 }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [h
  body: h

中文:
实例 [TopologicalSpace
  签名: α] [h
  定义体: h
-/
instance [TopologicalSpace α] [h : FirstCountableTopology α] : FirstCountableTopology αᵒᵈ := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [h
  body: h

中文:
实例 [TopologicalSpace
  签名: α] [h
  定义体: h
-/
instance [TopologicalSpace α] [h : SecondCountableTopology α] : SecondCountableTopology αᵒᵈ := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [h
  body: h

中文:
实例 [TopologicalSpace
  签名: α] [h
  定义体: h
-/
instance [TopologicalSpace α] [h : SeparableSpace α] : SeparableSpace αᵒᵈ := h

/--
theorem `Dense.orderDual` / 定理 `Dense.orderDual`

English:
theorem Dense.orderDual
  given: [TopologicalSpace α] {s : Set α} (hs : Dense s)
  proof: hs

中文:
定理 Dense.orderDual
  条件: [TopologicalSpace α] {s : Set α} (hs : Dense s)
  证明: hs
-/
theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

@[to_dual]
/--
lemma `BddAbove.of_closure` / 引理 `BddAbove.of_closure`

English:
lemma BddAbove.of_closure
  statement: BddAbove (closure s) -> BddAbove s
  proof: BddAbove.mono subset_closure

中文:
引理 BddAbove.of_closure
  结论: BddAbove (closure s) -> BddAbove s
  证明: BddAbove.mono subset_closure
-/
protected lemma BddAbove.of_closure : BddAbove (closure s) -> BddAbove s :=
  BddAbove.mono subset_closure

end General

section ClosedIicTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {f : β -> α} {a b : α} {s : Set α}

@[to_dual (attr := closedness .)]
/--
theorem `isClosed_Iic` / 定理 `isClosed_Iic`

English:
theorem isClosed_Iic
  statement: IsClosed (Iic a)
  proof: ClosedIicTopology.isClosed_Iic a

@[to_dual]

中文:
定理 isClosed_Iic
  结论: IsClosed (Iic a)
  证明: ClosedIicTopology.isClosed_Iic a

@[to_dual]

Depends on / 依赖: ClosedIicTopology, ClosedIicTopology.isClosed_Iic, isClosed_Iic
-/
theorem isClosed_Iic : IsClosed (Iic a) :=
  ClosedIicTopology.isClosed_Iic a

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ClosedIciTopology αᵒᵈ
  body: isClosed_Iic (α := α)

@[to_dual (attr := simp, closedness =)]

中文:
实例 :
  签名: ClosedIciTopology αᵒᵈ
  定义体: isClosed_Iic (α := α)

@[to_dual (attr := simp, closedness =)]

Depends on / 依赖: isClosed_Iic
-/
instance : ClosedIciTopology αᵒᵈ where
  isClosed_Ici _ := isClosed_Iic (α := α)

@[to_dual (attr := simp, closedness =)]
/--
theorem `closure_Iic` / 定理 `closure_Iic`

English:
theorem closure_Iic
  given: (a : α)
  statement: closure (Iic a) = Iic a
  proof: isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]

中文:
定理 closure_Iic
  条件: (a : α)
  结论: closure (Iic a) = Iic a
  证明: isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]

Depends on / 依赖: closure_eq, isClosed_Iic, isClosed_Iic.closure_eq
-/
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]
/--
theorem `le_of_tendsto_of_frequently` / 定理 `le_of_tendsto_of_frequently`

English:
theorem le_of_tendsto_of_frequently
  statement: {x : Filter β} (lim : Tendsto f x (𝓝 a))
  proof: isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]

中文:
定理 le_of_tendsto_of_frequently
  结论: {x : Filter β} (lim : Tendsto f x (𝓝 a))
  证明: isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]

Depends on / 依赖: isClosed_Iic, isClosed_Iic.mem_of_frequently_of_tendsto, mem_of_frequently_of_tendsto
-/
theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : existsᶠ c in x, f c <= b) : a <= b :=
  isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]
/--
theorem `le_of_tendsto` / 定理 `le_of_tendsto`

English:
theorem le_of_tendsto
  statement: {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
  proof: isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']

中文:
定理 le_of_tendsto
  结论: {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
  证明: isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']

Depends on / 依赖: isClosed_Iic, isClosed_Iic.mem_of_tendsto, mem_of_tendsto
-/
theorem le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : forallᶠ c in x, f c <= b) : a <= b :=
  isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']
/--
theorem `le_of_tendsto'` / 定理 `le_of_tendsto'`

English:
theorem le_of_tendsto'
  statement: {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
  proof: le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]

中文:
定理 le_of_tendsto'
  结论: {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
  证明: le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]

Depends on / 依赖: Eventually, Eventually.of_forall, le_of_tendsto, of_forall
-/
theorem le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : forall c, f c <= b) : a <= b :=
  le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]
/--
lemma `upperBounds_closure` / 引理 `upperBounds_closure`

English:
lemma upperBounds_closure
  given: (s : Set α)
  statement: upperBounds (closure s : Set α) = upperBounds s
  proof: ext fun a => by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]

中文:
引理 upperBounds_closure
  条件: (s : Set α)
  结论: upperBounds (closure s : Set α) = upperBounds s
  证明: ext fun a => by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]

Depends on / 依赖: closure_subset_iff, isClosed_Iic, isClosed_Iic.closure_subset_iff, mem_upperBounds_iff_subset_Iic, simp_rw
-/
lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a => by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]
/--
lemma `bddAbove_closure` / 引理 `bddAbove_closure`

English:
lemma bddAbove_closure
  statement: BddAbove (closure s) ↔ BddAbove s
  proof: by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]

中文:
引理 bddAbove_closure
  结论: BddAbove (closure s) ↔ BddAbove s
  证明: by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]

Depends on / 依赖: BddAbove, simp_rw, upperBounds_closure
-/
lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]
/--
theorem `disjoint_nhds_atBot_iff` / 定理 `disjoint_nhds_atBot_iff`

English:
theorem disjoint_nhds_atBot_iff
  statement: Disjoint (𝓝 a) atBot ↔ ¬IsBot a
  proof: by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq]; rw [disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.

中文:
定理 disjoint_nhds_atBot_iff
  结论: Disjoint (𝓝 a) atBot ↔ ¬IsBot a
  证明: by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq]; rw [disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.

Depends on / 依赖: Iic_mem_atBot, atBot_eq, disjoint_compl_left, disjoint_of_disjoint_of_mem, disjoint_principal_right, hbot.atBot_eq, isClosed_Iic, isClosed_Iic.isOpen_compl.mem_nhds, isOpen_compl, le_rfl, mem_nhds, mem_of_mem_nhds, not_forall
-/
theorem disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a := by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq]; rw [disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.mem_nhds hb

@[to_dual]
/--
theorem `IsLUB.range_of_tendsto` / 定理 `IsLUB.range_of_tendsto`

English:
theorem IsLUB.range_of_tendsto
  statement: {F : Filter β} [F.NeBot] (hle : forall i, f i <= a)
  proof: ⟨forall_mem_range.mpr hle, fun _c hc => le_of_tendsto' hlim fun i => hc mem_range_self i⟩

中文:
定理 IsLUB.range_of_tendsto
  结论: {F : Filter β} [F.NeBot] (hle : 对任意 i, f i <= a)
  证明: ⟨forall_mem_range.mpr hle, fun _c hc => le_of_tendsto' hlim fun i => hc mem_range_self i⟩

Depends on / 依赖: forall_mem_range, forall_mem_range.mpr, le_of_tendsto, mem_range_self
-/
theorem IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : forall i, f i <= a)
    (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a :=
⟨forall_mem_range.mpr hle, fun _c hc => le_of_tendsto' hlim fun i => hc mem_range_self i⟩

end Preorder

section NoBotOrder

variable [Preorder α] [NoBotOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β -> α}

@[to_dual disjoint_nhds_atTop]
/--
theorem `disjoint_nhds_atBot` / 定理 `disjoint_nhds_atBot`

English:
theorem disjoint_nhds_atBot
  given: (a : α)
  statement: Disjoint (𝓝 a) atBot
  proof: by simp

@[to_dual (attr := simp) nhds_inf_atTop]

中文:
定理 disjoint_nhds_atBot
  条件: (a : α)
  结论: Disjoint (𝓝 a) atBot
  证明: by simp

@[to_dual (attr := simp) nhds_inf_atTop]
-/
theorem disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot := by simp

@[to_dual (attr := simp) nhds_inf_atTop]
/--
theorem `nhds_inf_atBot` / 定理 `nhds_inf_atBot`

English:
theorem nhds_inf_atBot
  given: (a : α)
  statement: 𝓝 a ⊓ atBot = ⊥
  proof: (disjoint_nhds_atBot a).eq_bot

@[deprecated (since := "2026-04-07")] alias inf_nhds_atBot := nhds_inf_atBot
@[deprecated (since := "2026-04-07")] alias inf_nhds_atTop := nhds_inf_atTop

@[to_dual]

中文:
定理 nhds_inf_atBot
  条件: (a : α)
  结论: 𝓝 a ⊓ atBot = ⊥
  证明: (disjoint_nhds_atBot a).eq_bot

@[deprecated (since := "2026-04-07")] alias inf_nhds_atBot := nhds_inf_atBot
@[deprecated (since := "2026-04-07")] alias inf_nhds_atTop := nhds_inf_atTop

@[to_dual]

Depends on / 依赖: disjoint_nhds_atBot, eq_bot
-/
theorem nhds_inf_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥ := (disjoint_nhds_atBot a).eq_bot

@[deprecated (since := "2026-04-07")] alias inf_nhds_atBot := nhds_inf_atBot
@[deprecated (since := "2026-04-07")] alias inf_nhds_atTop := nhds_inf_atTop

@[to_dual]
/--
theorem `not_tendsto_nhds_of_tendsto_atBot` / 定理 `not_tendsto_nhds_of_tendsto_atBot`

English:
theorem not_tendsto_nhds_of_tendsto_atBot
  given: (hf : Tendsto f l atBot) (a : α)
  statement: ¬Tendsto f l (𝓝 a)
  proof: hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]

中文:
定理 not_tendsto_nhds_of_tendsto_atBot
  条件: (hf : Tendsto f l atBot) (a : α)
  结论: ¬Tendsto f l (𝓝 a)
  证明: hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]

Depends on / 依赖: disjoint_nhds_atBot, hf.not_tendsto, not_tendsto
-/
theorem not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]
/--
theorem `not_tendsto_atBot_of_tendsto_nhds` / 定理 `not_tendsto_atBot_of_tendsto_nhds`

English:
theorem not_tendsto_atBot_of_tendsto_nhds
  given: (hf : Tendsto f l (𝓝 a))
  statement: ¬Tendsto f l atBot
  proof: hf.not_tendsto (disjoint_nhds_atBot a)

中文:
定理 not_tendsto_atBot_of_tendsto_nhds
  条件: (hf : Tendsto f l (𝓝 a))
  结论: ¬Tendsto f l atBot
  证明: hf.not_tendsto (disjoint_nhds_atBot a)

Depends on / 依赖: disjoint_nhds_atBot, hf.not_tendsto, not_tendsto
-/
theorem not_tendsto_atBot_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l atBot :=
  hf.not_tendsto (disjoint_nhds_atBot a)

end NoBotOrder

/--
theorem `iSup_eq_of_forall_le_of_tendsto` / 定理 `iSup_eq_of_forall_le_of_tendsto`

English:
theorem iSup_eq_of_forall_le_of_tendsto
  statement: {ι : Type*} {F : Filter ι} [Filter.NeBot F]
  proof: have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq

中文:
定理 iSup_eq_of_forall_le_of_tendsto
  结论: {ι : 类型} {F : Filter ι} [Filter.NeBot F]
  证明: have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq

Depends on / 依赖: F.nonempty_of_neBot, IsLUB.range_of_tendsto, ciSup_eq, nonempty_of_neBot, range_of_tendsto
-/
theorem iSup_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [Filter.NeBot F]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι -> α} (hle : forall i, f i <= a) (hlim : Filter.Tendsto f F (𝓝 a)) :
    ⨆ i, f i = a :=
  have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq

/--
theorem `iUnion_Iic_eq_Iio_of_lt_of_tendsto` / 定理 `iUnion_Iic_eq_Iio_of_lt_of_tendsto`

English:
theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto
  statement: {ι : Type*} {F : Filter ι} [F.NeBot]
  proof: by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range]; rw [(IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

中文:
定理 iUnion_Iic_eq_Iio_of_lt_of_tendsto
  结论: {ι : 类型} {F : Filter ι} [F.NeBot]
  证明: by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range]; rw [(IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

Depends on / 依赖: IsLUB.range_of_tendsto, biUnion_Iic_eq_Iio, biUnion_range, le_of_lt, mem_range, range_of_tendsto
-/
theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι -> α} (hlt : forall i, f i < a) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Iic (f i) = Iio a := by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range]; rw [(IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] [TopologicalSpace β]
  {a b c : α} {f : α -> β}

@[to_dual]
/--
theorem `isOpen_Ioi` / 定理 `isOpen_Ioi`

English:
theorem isOpen_Ioi
  statement: IsOpen (Ioi a)
  proof: by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]

中文:
定理 isOpen_Ioi
  结论: IsOpen (Ioi a)
  证明: by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]

Depends on / 依赖: compl_Iic, isClosed_Iic, isClosed_Iic.isOpen_compl, isOpen_compl
-/
theorem isOpen_Ioi : IsOpen (Ioi a) := by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]
/--
theorem `interior_Ioi` / 定理 `interior_Ioi`

English:
theorem interior_Ioi
  statement: interior (Ioi a) = Ioi a
  proof: isOpen_Ioi.interior_eq

@[to_dual]

中文:
定理 interior_Ioi
  结论: interior (Ioi a) = Ioi a
  证明: isOpen_Ioi.interior_eq

@[to_dual]

Depends on / 依赖: interior_eq, isOpen_Ioi, isOpen_Ioi.interior_eq
-/
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq

@[to_dual]
/--
theorem `Ioi_mem_nhds` / 定理 `Ioi_mem_nhds`

English:
theorem Ioi_mem_nhds
  given: (h : a < b)
  statement: Ioi a in 𝓝 b
  proof: IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]

中文:
定理 Ioi_mem_nhds
  条件: (h : a < b)
  结论: Ioi a in 𝓝 b
  证明: IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, isOpen_Ioi, mem_nhds
-/
theorem Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b := IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]
/--
theorem `eventually_gt_nhds` / 定理 `eventually_gt_nhds`

English:
theorem eventually_gt_nhds
  given: (hab : b < a)
  statement: forallᶠ x in 𝓝 a, b < x
  proof: Ioi_mem_nhds hab

@[to_dual]

中文:
定理 eventually_gt_nhds
  条件: (hab : b < a)
  结论: 对任意ᶠ x in 𝓝 a, b < x
  证明: Ioi_mem_nhds hab

@[to_dual]

Depends on / 依赖: Ioi_mem_nhds
-/
theorem eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab

@[to_dual]
/--
theorem `Ici_mem_nhds` / 定理 `Ici_mem_nhds`

English:
theorem Ici_mem_nhds
  given: (h : a < b)
  statement: Ici a in 𝓝 b
  proof: mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]

中文:
定理 Ici_mem_nhds
  条件: (h : a < b)
  结论: Ici a in 𝓝 b
  证明: mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]

Depends on / 依赖: Ioi_mem_nhds, Ioi_subset_Ici_self, mem_of_superset
-/
theorem Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]
/--
theorem `eventually_ge_nhds` / 定理 `eventually_ge_nhds`

English:
theorem eventually_ge_nhds
  given: (hab : b < a)
  statement: forallᶠ x in 𝓝 a, b <= x
  proof: Ici_mem_nhds hab

@[to_dual eventually_lt_const]

中文:
定理 eventually_ge_nhds
  条件: (hab : b < a)
  结论: 对任意ᶠ x in 𝓝 a, b <= x
  证明: Ici_mem_nhds hab

@[to_dual eventually_lt_const]

Depends on / 依赖: Ici_mem_nhds
-/
theorem eventually_ge_nhds (hab : b < a) : forallᶠ x in 𝓝 a, b <= x := Ici_mem_nhds hab

@[to_dual eventually_lt_const]
/--
theorem `Filter.Tendsto.eventually_const_lt` / 定理 `Filter.Tendsto.eventually_const_lt`

English:
theorem Filter.Tendsto.eventually_const_lt
  statement: {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
  proof: h.eventually eventually_gt_nhds hv

@[to_dual eventually_le_const]

中文:
定理 Filter.Tendsto.eventually_const_lt
  结论: {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
  证明: h.eventually eventually_gt_nhds hv

@[to_dual eventually_le_const]

Depends on / 依赖: eventually, eventually_gt_nhds, h.eventually
-/
theorem Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : forallᶠ a in l, u < f a :=
h.eventually eventually_gt_nhds hv

@[to_dual eventually_le_const]
/--
theorem `Filter.Tendsto.eventually_const_le` / 定理 `Filter.Tendsto.eventually_const_le`

English:
theorem Filter.Tendsto.eventually_const_le
  statement: {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
  proof: h.eventually eventually_ge_nhds hv

@[to_dual exists_lt]

中文:
定理 Filter.Tendsto.eventually_const_le
  结论: {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
  证明: h.eventually eventually_ge_nhds hv

@[to_dual exists_lt]

Depends on / 依赖: eventually, eventually_ge_nhds, h.eventually
-/
theorem Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : forallᶠ a in l, u <= f a :=
h.eventually eventually_ge_nhds hv

@[to_dual exists_lt]
/--
theorem `Dense.exists_gt` / 定理 `Dense.exists_gt`

English:
theorem Dense.exists_gt
  given: [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α)
  proof: hs.exists_mem_open isOpen_Ioi (exists_gt x)

@[to_dual exists_le]

中文:
定理 Dense.exists_gt
  条件: [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α)
  证明: hs.exists_mem_open isOpen_Ioi (exists_gt x)

@[to_dual exists_le]
-/
protected theorem Dense.exists_gt [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    exists y in s, x < y :=
  hs.exists_mem_open isOpen_Ioi (exists_gt x)

@[to_dual exists_le]
/--
theorem `Dense.exists_ge` / 定理 `Dense.exists_ge`

English:
theorem Dense.exists_ge
  given: [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α)
  proof: (hs.exists_gt x).imp fun _ h => ⟨h.1, h.2.le⟩

@[to_dual exists_le']

中文:
定理 Dense.exists_ge
  条件: [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α)
  证明: (hs.exists_gt x).imp fun _ h => ⟨h.1, h.2.le⟩

@[to_dual exists_le']
-/
protected theorem Dense.exists_ge [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    exists y in s, x <= y :=
  (hs.exists_gt x).imp fun _ h => ⟨h.1, h.2.le⟩

@[to_dual exists_le']
/--
theorem `Dense.exists_ge'` / 定理 `Dense.exists_ge'`

English:
theorem Dense.exists_ge'
  given: {s : Set α} (hs : Dense s) (htop : forall x, IsTop x -> x in s) (x : α)
  proof: by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

中文:
定理 Dense.exists_ge'
  条件: {s : Set α} (hs : Dense s) (htop : 对任意 x, IsTop x -> x in s) (x : α)
  证明: by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

Depends on / 依赖: exists_mem_open, hs.exists_mem_open, hy.le, isOpen_Ioi, le_rfl, not_forall, not_le
-/
theorem Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : forall x, IsTop x -> x in s) (x : α) :
    exists y in s, x <= y := by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

/-!
### Left neighborhoods on a `ClosedIicTopology`

Limits to the left of real functions are defined in terms of neighborhoods to the left, either open
or closed, i.e., members of `𝓝[<] a` and `𝓝[≤] a`. Here we prove that all left-neighborhoods of a
point are equal, and we prove other useful characterizations which require the stronger hypothesis
`OrderTopology α` in another file.
-/

/-!
#### Point excluded
-/

@[to_dual]
/--
theorem `Ioo_mem_nhdsLT` / 定理 `Ioo_mem_nhdsLT`

English:
theorem Ioo_mem_nhdsLT
  given: (H : a < b)
  statement: Ioo a b in 𝓝[<] b
  proof: by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

@[to_dual]

中文:
定理 Ioo_mem_nhdsLT
  条件: (H : a < b)
  结论: Ioo a b in 𝓝[<] b
  证明: by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

@[to_dual]

Depends on / 依赖: Iio_inter_Ioi, Ioi_mem_nhds, inter_mem_nhdsWithin
-/
theorem Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b := by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

@[to_dual]
/--
theorem `Ioo_mem_nhdsLT_of_mem` / 定理 `Ioo_mem_nhdsLT_of_mem`

English:
theorem Ioo_mem_nhdsLT_of_mem
  given: (H : b in Ioc a c)
  statement: Ioo a c in 𝓝[<] b
  proof: mem_of_superset (Ioo_mem_nhdsLT H.1) Ioo_subset_Ioo_right H.2

@[to_dual]

中文:
定理 Ioo_mem_nhdsLT_of_mem
  条件: (H : b in Ioc a c)
  结论: Ioo a c in 𝓝[<] b
  证明: mem_of_superset (Ioo_mem_nhdsLT H.1) Ioo_subset_Ioo_right H.2

@[to_dual]

Depends on / 依赖: Ioo_mem_nhdsLT, Ioo_subset_Ioo_right, mem_of_superset
-/
theorem Ioo_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioo a c in 𝓝[<] b :=
mem_of_superset (Ioo_mem_nhdsLT H.1) Ioo_subset_Ioo_right H.2

@[to_dual]
/--
theorem `CovBy.nhdsLT` / 定理 `CovBy.nhdsLT`

English:
theorem CovBy.nhdsLT
  given: (h : a ⋖ b)
  statement: 𝓝[<] b = ⊥
  proof: empty_mem_iff_bot.mp h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

@[to_dual]

中文:
定理 CovBy.nhdsLT
  条件: (h : a ⋖ b)
  结论: 𝓝[<] b = ⊥
  证明: empty_mem_iff_bot.mp h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

@[to_dual]
-/
protected theorem CovBy.nhdsLT (h : a ⋖ b) : 𝓝[<] b = ⊥ :=
empty_mem_iff_bot.mp h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

@[to_dual]
/--
theorem `PredOrder.nhdsLT` / 定理 `PredOrder.nhdsLT`

English:
theorem PredOrder.nhdsLT
  given: [PredOrder α]
  statement: 𝓝[<] a = ⊥
  proof: by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

@[to_dual]

中文:
定理 PredOrder.nhdsLT
  条件: [PredOrder α]
  结论: 𝓝[<] a = ⊥
  证明: by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

@[to_dual]
-/
protected theorem PredOrder.nhdsLT [PredOrder α] : 𝓝[<] a = ⊥ := by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

@[to_dual]
/--
theorem `PredOrder.nhdsGT_eq_nhdsNE` / 定理 `PredOrder.nhdsGT_eq_nhdsNE`

English:
theorem PredOrder.nhdsGT_eq_nhdsNE
  given: [PredOrder α] (a : α)
  statement: 𝓝[>] a = 𝓝[!=] a
  proof: by
  rw [← nhdsLT_sup_nhdsGT]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]

中文:
定理 PredOrder.nhdsGT_eq_nhdsNE
  条件: [PredOrder α] (a : α)
  结论: 𝓝[>] a = 𝓝[!=] a
  证明: by
  rw [← nhdsLT_sup_nhdsGT]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]

Depends on / 依赖: PredOrder, PredOrder.nhdsLT, bot_sup_eq, nhdsLT, nhdsLT_sup_nhdsGT
-/
theorem PredOrder.nhdsGT_eq_nhdsNE [PredOrder α] (a : α) : 𝓝[>] a = 𝓝[!=] a := by
  rw [← nhdsLT_sup_nhdsGT]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]
/--
theorem `PredOrder.nhdsGE_eq_nhds` / 定理 `PredOrder.nhdsGE_eq_nhds`

English:
theorem PredOrder.nhdsGE_eq_nhds
  given: [PredOrder α] (a : α)
  statement: 𝓝[>=] a = 𝓝 a
  proof: by
  rw [← nhdsLT_sup_nhdsGE]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]

中文:
定理 PredOrder.nhdsGE_eq_nhds
  条件: [PredOrder α] (a : α)
  结论: 𝓝[>=] a = 𝓝 a
  证明: by
  rw [← nhdsLT_sup_nhdsGE]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]

Depends on / 依赖: PredOrder, PredOrder.nhdsLT, bot_sup_eq, nhdsLT, nhdsLT_sup_nhdsGE
-/
theorem PredOrder.nhdsGE_eq_nhds [PredOrder α] (a : α) : 𝓝[>=] a = 𝓝 a := by
  rw [← nhdsLT_sup_nhdsGE]; rw [PredOrder.nhdsLT]; rw [bot_sup_eq]

@[to_dual]
/--
theorem `Ico_mem_nhdsLT_of_mem` / 定理 `Ico_mem_nhdsLT_of_mem`

English:
theorem Ico_mem_nhdsLT_of_mem
  given: (H : b in Ioc a c)
  statement: Ico a c in 𝓝[<] b
  proof: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

@[to_dual]

中文:
定理 Ico_mem_nhdsLT_of_mem
  条件: (H : b in Ioc a c)
  结论: Ico a c in 𝓝[<] b
  证明: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

@[to_dual]

Depends on / 依赖: Ioo_mem_nhdsLT_of_mem, Ioo_subset_Ico_self, mem_of_superset
-/
theorem Ico_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ico a c in 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

@[to_dual]
/--
theorem `Ico_mem_nhdsLT` / 定理 `Ico_mem_nhdsLT`

English:
theorem Ico_mem_nhdsLT
  given: (H : a < b)
  statement: Ico a b in 𝓝[<] b
  proof: Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]

中文:
定理 Ico_mem_nhdsLT
  条件: (H : a < b)
  结论: Ico a b in 𝓝[<] b
  证明: Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]

Depends on / 依赖: Ico_mem_nhdsLT_of_mem, le_rfl
-/
theorem Ico_mem_nhdsLT (H : a < b) : Ico a b in 𝓝[<] b := Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
/--
theorem `Ioc_mem_nhdsLT_of_mem` / 定理 `Ioc_mem_nhdsLT_of_mem`

English:
theorem Ioc_mem_nhdsLT_of_mem
  given: (H : b in Ioc a c)
  statement: Ioc a c in 𝓝[<] b
  proof: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

@[to_dual]

中文:
定理 Ioc_mem_nhdsLT_of_mem
  条件: (H : b in Ioc a c)
  结论: Ioc a c in 𝓝[<] b
  证明: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

@[to_dual]

Depends on / 依赖: Ioo_mem_nhdsLT_of_mem, Ioo_subset_Ioc_self, mem_of_superset
-/
theorem Ioc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Ioc a c in 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

@[to_dual]
/--
theorem `Ioc_mem_nhdsLT` / 定理 `Ioc_mem_nhdsLT`

English:
theorem Ioc_mem_nhdsLT
  given: (H : a < b)
  statement: Ioc a b in 𝓝[<] b
  proof: Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]

中文:
定理 Ioc_mem_nhdsLT
  条件: (H : a < b)
  结论: Ioc a b in 𝓝[<] b
  证明: Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]

Depends on / 依赖: Ioc_mem_nhdsLT_of_mem, le_rfl
-/
theorem Ioc_mem_nhdsLT (H : a < b) : Ioc a b in 𝓝[<] b := Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
/--
theorem `Icc_mem_nhdsLT_of_mem` / 定理 `Icc_mem_nhdsLT_of_mem`

English:
theorem Icc_mem_nhdsLT_of_mem
  given: (H : b in Ioc a c)
  statement: Icc a c in 𝓝[<] b
  proof: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

@[to_dual]

中文:
定理 Icc_mem_nhdsLT_of_mem
  条件: (H : b in Ioc a c)
  结论: Icc a c in 𝓝[<] b
  证明: mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

@[to_dual]

Depends on / 依赖: Ioo_mem_nhdsLT_of_mem, Ioo_subset_Icc_self, mem_of_superset
-/
theorem Icc_mem_nhdsLT_of_mem (H : b in Ioc a c) : Icc a c in 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

@[to_dual]
/--
theorem `Icc_mem_nhdsLT` / 定理 `Icc_mem_nhdsLT`

English:
theorem Icc_mem_nhdsLT
  given: (H : a < b)
  statement: Icc a b in 𝓝[<] b
  proof: Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]

中文:
定理 Icc_mem_nhdsLT
  条件: (H : a < b)
  结论: Icc a b in 𝓝[<] b
  证明: Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_mem_nhdsLT_of_mem, le_rfl
-/
theorem Icc_mem_nhdsLT (H : a < b) : Icc a b in 𝓝[<] b := Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
/--
theorem `nhdsWithin_Ico_eq_nhdsLT` / 定理 `nhdsWithin_Ico_eq_nhdsLT`

English:
theorem nhdsWithin_Ico_eq_nhdsLT
  given: (h : a < b)
  statement: 𝓝[Ico a b] b = 𝓝[<] b
  proof: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]

中文:
定理 nhdsWithin_Ico_eq_nhdsLT
  条件: (h : a < b)
  结论: 𝓝[Ico a b] b = 𝓝[<] b
  证明: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_mem_nhds, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds
-/
theorem nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b :=
nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]
/--
theorem `nhdsWithin_Ioo_eq_nhdsLT` / 定理 `nhdsWithin_Ioo_eq_nhdsLT`

English:
theorem nhdsWithin_Ioo_eq_nhdsLT
  given: (h : a < b)
  statement: 𝓝[Ioo a b] b = 𝓝[<] b
  proof: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]

中文:
定理 nhdsWithin_Ioo_eq_nhdsLT
  条件: (h : a < b)
  结论: 𝓝[Ioo a b] b = 𝓝[<] b
  证明: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_mem_nhds, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds
-/
theorem nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b :=
nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]
/--
theorem `continuousWithinAt_Ico_iff_Iio` / 定理 `continuousWithinAt_Ico_iff_Iio`

English:
theorem continuousWithinAt_Ico_iff_Iio
  given: (h : a < b)
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[to_dual (attr := simp)]

中文:
定理 continuousWithinAt_Ico_iff_Iio
  条件: (h : a < b)
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[to_dual (attr := simp)]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT
-/
theorem continuousWithinAt_Ico_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ico a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[to_dual (attr := simp)]
/--
theorem `continuousWithinAt_Ioo_iff_Iio` / 定理 `continuousWithinAt_Ioo_iff_Iio`

English:
theorem continuousWithinAt_Ioo_iff_Iio
  given: (h : a < b)
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

中文:
定理 continuousWithinAt_Ioo_iff_Iio
  条件: (h : a < b)
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT
-/
theorem continuousWithinAt_Ioo_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ioo a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

/-!
#### Point included
-/

@[to_dual]
/--
theorem `CovBy.nhdsLE` / 定理 `CovBy.nhdsLE`

English:
theorem CovBy.nhdsLE
  given: (H : a ⋖ b)
  statement: 𝓝[<=] b = pure b
  proof: by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [H.nhdsLT]; rw [sup_bot_eq]

@[to_dual]

中文:
定理 CovBy.nhdsLE
  条件: (H : a ⋖ b)
  结论: 𝓝[<=] b = pure b
  证明: by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [H.nhdsLT]; rw [sup_bot_eq]

@[to_dual]
-/
protected theorem CovBy.nhdsLE (H : a ⋖ b) : 𝓝[<=] b = pure b := by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [H.nhdsLT]; rw [sup_bot_eq]

@[to_dual]
/--
theorem `PredOrder.nhdsLE` / 定理 `PredOrder.nhdsLE`

English:
theorem PredOrder.nhdsLE
  given: [PredOrder α]
  statement: 𝓝[<=] b = pure b
  proof: by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [PredOrder.nhdsLT]; rw [sup_bot_eq]

@[to_dual]

中文:
定理 PredOrder.nhdsLE
  条件: [PredOrder α]
  结论: 𝓝[<=] b = pure b
  证明: by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [PredOrder.nhdsLT]; rw [sup_bot_eq]

@[to_dual]
-/
protected theorem PredOrder.nhdsLE [PredOrder α] : 𝓝[<=] b = pure b := by
  rw [← Iio_insert]; rw [nhdsWithin_insert]; rw [PredOrder.nhdsLT]; rw [sup_bot_eq]

@[to_dual]
/--
theorem `Ioc_mem_nhdsLE` / 定理 `Ioc_mem_nhdsLE`

English:
theorem Ioc_mem_nhdsLE
  given: (H : a < b)
  statement: Ioc a b in 𝓝[<=] b
  proof: inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

@[to_dual]

中文:
定理 Ioc_mem_nhdsLE
  条件: (H : a < b)
  结论: Ioc a b in 𝓝[<=] b
  证明: inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

@[to_dual]

Depends on / 依赖: Ioi_mem_nhds, inter_mem, nhdsWithin_le_nhds, self_mem_nhdsWithin
-/
theorem Ioc_mem_nhdsLE (H : a < b) : Ioc a b in 𝓝[<=] b :=
  inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

@[to_dual]
/--
theorem `Ioo_mem_nhdsLE_of_mem` / 定理 `Ioo_mem_nhdsLE_of_mem`

English:
theorem Ioo_mem_nhdsLE_of_mem
  given: (H : b in Ioo a c)
  statement: Ioo a c in 𝓝[<=] b
  proof: mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioo_right H.2

@[to_dual]

中文:
定理 Ioo_mem_nhdsLE_of_mem
  条件: (H : b in Ioo a c)
  结论: Ioo a c in 𝓝[<=] b
  证明: mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioo_right H.2

@[to_dual]

Depends on / 依赖: Ioc_mem_nhdsLE, Ioc_subset_Ioo_right, mem_of_superset
-/
theorem Ioo_mem_nhdsLE_of_mem (H : b in Ioo a c) : Ioo a c in 𝓝[<=] b :=
mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioo_right H.2

@[to_dual]
/--
theorem `Ico_mem_nhdsLE_of_mem` / 定理 `Ico_mem_nhdsLE_of_mem`

English:
theorem Ico_mem_nhdsLE_of_mem
  given: (H : b in Ioo a c)
  statement: Ico a c in 𝓝[<=] b
  proof: mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

@[to_dual]

中文:
定理 Ico_mem_nhdsLE_of_mem
  条件: (H : b in Ioo a c)
  结论: Ico a c in 𝓝[<=] b
  证明: mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

@[to_dual]

Depends on / 依赖: Ioo_mem_nhdsLE_of_mem, Ioo_subset_Ico_self, mem_of_superset
-/
theorem Ico_mem_nhdsLE_of_mem (H : b in Ioo a c) : Ico a c in 𝓝[<=] b :=
  mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

@[to_dual]
/--
theorem `Ioc_mem_nhdsLE_of_mem` / 定理 `Ioc_mem_nhdsLE_of_mem`

English:
theorem Ioc_mem_nhdsLE_of_mem
  given: (H : b in Ioc a c)
  statement: Ioc a c in 𝓝[<=] b
  proof: mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioc_right H.2

@[to_dual]

中文:
定理 Ioc_mem_nhdsLE_of_mem
  条件: (H : b in Ioc a c)
  结论: Ioc a c in 𝓝[<=] b
  证明: mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioc_right H.2

@[to_dual]

Depends on / 依赖: Ioc_mem_nhdsLE, Ioc_subset_Ioc_right, mem_of_superset
-/
theorem Ioc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Ioc a c in 𝓝[<=] b :=
mem_of_superset (Ioc_mem_nhdsLE H.1) Ioc_subset_Ioc_right H.2

@[to_dual]
/--
theorem `Icc_mem_nhdsLE_of_mem` / 定理 `Icc_mem_nhdsLE_of_mem`

English:
theorem Icc_mem_nhdsLE_of_mem
  given: (H : b in Ioc a c)
  statement: Icc a c in 𝓝[<=] b
  proof: mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

@[to_dual]

中文:
定理 Icc_mem_nhdsLE_of_mem
  条件: (H : b in Ioc a c)
  结论: Icc a c in 𝓝[<=] b
  证明: mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

@[to_dual]

Depends on / 依赖: Ioc_mem_nhdsLE_of_mem, Ioc_subset_Icc_self, mem_of_superset
-/
theorem Icc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Icc a c in 𝓝[<=] b :=
  mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

@[to_dual]
/--
theorem `Icc_mem_nhdsLE` / 定理 `Icc_mem_nhdsLE`

English:
theorem Icc_mem_nhdsLE
  given: (H : a < b)
  statement: Icc a b in 𝓝[<=] b
  proof: Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]

中文:
定理 Icc_mem_nhdsLE
  条件: (H : a < b)
  结论: Icc a b in 𝓝[<=] b
  证明: Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Icc_mem_nhdsLE_of_mem, le_rfl
-/
theorem Icc_mem_nhdsLE (H : a < b) : Icc a b in 𝓝[<=] b := Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
/--
theorem `nhdsWithin_Icc_eq_nhdsLE` / 定理 `nhdsWithin_Icc_eq_nhdsLE`

English:
theorem nhdsWithin_Icc_eq_nhdsLE
  given: (h : a < b)
  statement: 𝓝[Icc a b] b = 𝓝[<=] b
  proof: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]

中文:
定理 nhdsWithin_Icc_eq_nhdsLE
  条件: (h : a < b)
  结论: 𝓝[Icc a b] b = 𝓝[<=] b
  证明: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_mem_nhds, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds
-/
theorem nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a b] b = 𝓝[<=] b :=
nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ici_mem_nhds h

@[to_dual (attr := simp)]
/--
theorem `nhdsWithin_Ioc_eq_nhdsLE` / 定理 `nhdsWithin_Ioc_eq_nhdsLE`

English:
theorem nhdsWithin_Ioc_eq_nhdsLE
  given: (h : a < b)
  statement: 𝓝[Ioc a b] b = 𝓝[<=] b
  proof: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]

中文:
定理 nhdsWithin_Ioc_eq_nhdsLE
  条件: (h : a < b)
  结论: 𝓝[Ioc a b] b = 𝓝[<=] b
  证明: nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_mem_nhds, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds
-/
theorem nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a b] b = 𝓝[<=] b :=
nhdsWithin_inter_of_mem nhdsWithin_le_nhds Ioi_mem_nhds h

@[to_dual (attr := simp)]
/--
theorem `continuousWithinAt_Icc_iff_Iic` / 定理 `continuousWithinAt_Icc_iff_Iic`

English:
theorem continuousWithinAt_Icc_iff_Iic
  given: (h : a < b)
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[to_dual (attr := simp)]

中文:
定理 continuousWithinAt_Icc_iff_Iic
  条件: (h : a < b)
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[to_dual (attr := simp)]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE
-/
theorem continuousWithinAt_Icc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Icc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[to_dual (attr := simp)]
/--
theorem `continuousWithinAt_Ioc_iff_Iic` / 定理 `continuousWithinAt_Ioc_iff_Iic`

English:
theorem continuousWithinAt_Ioc_iff_Iic
  given: (h : a < b)
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

中文:
定理 continuousWithinAt_Ioc_iff_Iic
  条件: (h : a < b)
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE
-/
theorem continuousWithinAt_Ioc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

end LinearOrder

end ClosedIicTopology

section ClosedIciTopology

-- TODO: we're missing some to_dual tags for conditionally complete lattices

@[to_dual existing]
/--
theorem `iInf_eq_of_forall_le_of_tendsto` / 定理 `iInf_eq_of_forall_le_of_tendsto`

English:
theorem iInf_eq_of_forall_le_of_tendsto
  statement: {ι : Type*} {F : Filter ι} [F.NeBot]
  proof: iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle hlim

@[to_dual existing]

中文:
定理 iInf_eq_of_forall_le_of_tendsto
  结论: {ι : 类型} {F : Filter ι} [F.NeBot]
  证明: iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle hlim

@[to_dual existing]

Depends on / 依赖: iSup_eq_of_forall_le_of_tendsto
-/
theorem iInf_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι -> α} (hle : forall i, a <= f i) (hlim : Tendsto f F (𝓝 a)) :
    ⨅ i, f i = a :=
  iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle hlim

@[to_dual existing]
/--
theorem `iUnion_Ici_eq_Ioi_of_lt_of_tendsto` / 定理 `iUnion_Ici_eq_Ioi_of_lt_of_tendsto`

English:
theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto
  statement: {ι : Type*} {F : Filter ι} [F.NeBot]
  proof: iUnion_Iic_eq_Iio_of_lt_of_tendsto (α := αᵒᵈ) hlt hlim

中文:
定理 iUnion_Ici_eq_Ioi_of_lt_of_tendsto
  结论: {ι : 类型} {F : Filter ι} [F.NeBot]
  证明: iUnion_Iic_eq_Iio_of_lt_of_tendsto (α := αᵒᵈ) hlt hlim

Depends on / 依赖: iUnion_Iic_eq_Iio_of_lt_of_tendsto
-/
theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι -> α} (hlt : forall i, a < f i) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Ici (f i) = Ioi a :=
  iUnion_Iic_eq_Iio_of_lt_of_tendsto (α := αᵒᵈ) hlt hlim

section OrderClosedTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

namespace Subtype

-- todo: add `OrderEmbedding.orderClosedTopology`
instance {p : α -> Prop} : OrderClosedTopology (Subtype p) :=
  have : Continuous fun p : Subtype p × Subtype p => ((p.fst : α), (p.snd : α)) :=
    continuous_subtype_val.prodMap continuous_subtype_val
  OrderClosedTopology.mk (t.isClosed_le'.preimage this)

end Subtype

-- The binder info on both theorems is slightly different, see
-- https://github.com/leanprover/lean4/issues/9727
@[closedness .]
/--
theorem `isClosed_le_prod` / 定理 `isClosed_le_prod`

English:
theorem isClosed_le_prod
  statement: IsClosed { p : α × α | p.1 <= p.2 }
  proof: t.isClosed_le'

@[to_dual existing isClosed_le_prod, closedness .]

中文:
定理 isClosed_le_prod
  结论: IsClosed { p : α × α | p.1 <= p.2 }
  证明: t.isClosed_le'

@[to_dual existing isClosed_le_prod, closedness .]

Depends on / 依赖: isClosed_le, t.isClosed_le
-/
theorem isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 } :=
  t.isClosed_le'

@[to_dual existing isClosed_le_prod, closedness .]
/--
theorem `isClosed_le_prod'` / 定理 `isClosed_le_prod'`

English:
theorem isClosed_le_prod'
  statement: IsClosed { p : α × α | p.2 <= p.1 }
  proof: (isClosed_le_prod (α := α)).preimage continuous_swap

@[to_dual self (reorder := f g, hf hg)]

中文:
定理 isClosed_le_prod'
  结论: IsClosed { p : α × α | p.2 <= p.1 }
  证明: (isClosed_le_prod (α := α)).preimage continuous_swap

@[to_dual self (reorder := f g, hf hg)]

Depends on / 依赖: continuous_swap, isClosed_le_prod, preimage
-/
theorem isClosed_le_prod' : IsClosed { p : α × α | p.2 <= p.1 } :=
  (isClosed_le_prod (α := α)).preimage continuous_swap

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `isClosed_le` / 定理 `isClosed_le`

English:
theorem isClosed_le
  given: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]

中文:
定理 isClosed_le
  条件: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  证明: continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]

Depends on / 依赖: continuous_iff_isClosed, continuous_iff_isClosed.mp, hf.prodMk, isClosed_le_prod, prodMk
-/
theorem isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b <= g b } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ClosedIicTopology α
  body: isClosed_le continuous_id continuous_const

中文:
实例 :
  签名: ClosedIicTopology α
  定义体: isClosed_le continuous_id continuous_const

Depends on / 依赖: continuous_const, continuous_id, isClosed_le
-/
instance : ClosedIicTopology α where
  isClosed_Iic _ := isClosed_le continuous_id continuous_const

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderClosedTopology αᵒᵈ
  body: ⟨isClosed_le_prod' (α := α)⟩

@[to_dual self, closedness .]

中文:
实例 :
  签名: OrderClosedTopology αᵒᵈ
  定义体: ⟨isClosed_le_prod' (α := α)⟩

@[to_dual self, closedness .]

Depends on / 依赖: isClosed_le_prod
-/
instance : OrderClosedTopology αᵒᵈ :=
  ⟨isClosed_le_prod' (α := α)⟩

@[to_dual self, closedness .]
/--
theorem `isClosed_Icc` / 定理 `isClosed_Icc`

English:
theorem isClosed_Icc
  given: {a b : α}
  statement: IsClosed (Icc a b)
  proof: IsClosed.inter isClosed_Ici isClosed_Iic

@[to_dual self, simp, closedness =]

中文:
定理 isClosed_Icc
  条件: {a b : α}
  结论: IsClosed (Icc a b)
  证明: IsClosed.inter isClosed_Ici isClosed_Iic

@[to_dual self, simp, closedness =]

Depends on / 依赖: IsClosed, IsClosed.inter, isClosed_Ici, isClosed_Iic
-/
theorem isClosed_Icc {a b : α} : IsClosed (Icc a b) :=
  IsClosed.inter isClosed_Ici isClosed_Iic

@[to_dual self, simp, closedness =]
/--
theorem `closure_Icc` / 定理 `closure_Icc`

English:
theorem closure_Icc
  given: (a b : α)
  statement: closure (Icc a b) = Icc a b
  proof: isClosed_Icc.closure_eq

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

中文:
定理 closure_Icc
  条件: (a b : α)
  结论: closure (Icc a b) = Icc a b
  证明: isClosed_Icc.closure_eq

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

Depends on / 依赖: closure_eq, isClosed_Icc, isClosed_Icc.closure_eq
-/
theorem closure_Icc (a b : α) : closure (Icc a b) = Icc a b :=
  isClosed_Icc.closure_eq

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/--
theorem `le_of_tendsto_of_tendsto_of_frequently` / 定理 `le_of_tendsto_of_tendsto_of_frequently`

English:
theorem le_of_tendsto_of_tendsto_of_frequently
  statement: {f g : β -> α} {b : Filter β} {a₁ a₂ : α}
  proof: t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

中文:
定理 le_of_tendsto_of_tendsto_of_frequently
  结论: {f g : β -> α} {b : Filter β} {a₁ a₂ : α}
  证明: t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

Depends on / 依赖: hf.prodMk_nhds, isClosed_le, mem_of_frequently_of_tendsto, prodMk_nhds, t.isClosed_le
-/
theorem le_of_tendsto_of_tendsto_of_frequently {f g : β -> α} {b : Filter β} {a₁ a₂ : α}
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : existsᶠ x in b, f x <= g x) : a₁ <= a₂ :=
  t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/--
theorem `le_of_tendsto_of_tendsto` / 定理 `le_of_tendsto_of_tendsto`

English:
theorem le_of_tendsto_of_tendsto
  statement: {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
  proof: le_of_tendsto_of_tendsto_of_frequently hf hg Eventually.frequently h

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

中文:
定理 le_of_tendsto_of_tendsto
  结论: {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
  证明: le_of_tendsto_of_tendsto_of_frequently hf hg Eventually.frequently h

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]

Depends on / 依赖: Eventually, Eventually.frequently, frequently, le_of_tendsto_of_tendsto_of_frequently
-/
theorem le_of_tendsto_of_tendsto {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f <=ᶠ[b] g) : a₁ <= a₂ :=
le_of_tendsto_of_tendsto_of_frequently hf hg Eventually.frequently h

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
/--
theorem `le_of_tendsto_of_tendsto'` / 定理 `le_of_tendsto_of_tendsto'`

English:
theorem le_of_tendsto_of_tendsto'
  statement: {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
  proof: le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[to_dual self (reorder := f g, hf hg), simp]

中文:
定理 le_of_tendsto_of_tendsto'
  结论: {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
  证明: le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[to_dual self (reorder := f g, hf hg), simp]

Depends on / 依赖: Eventually, Eventually.of_forall, le_of_tendsto_of_tendsto, of_forall
-/
theorem le_of_tendsto_of_tendsto' {f g : β -> α} {b : Filter β} {a₁ a₂ : α} [hb : NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : forall x, f x <= g x) : a₁ <= a₂ :=
  le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[to_dual self (reorder := f g, hf hg), simp]
/--
theorem `closure_le_eq` / 定理 `closure_le_eq`

English:
theorem closure_le_eq
  given: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  proof: (isClosed_le hf hg).closure_eq

@[to_dual self (reorder := f g, hf hg)]

中文:
定理 closure_le_eq
  条件: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  证明: (isClosed_le hf hg).closure_eq

@[to_dual self (reorder := f g, hf hg)]

Depends on / 依赖: closure_eq, isClosed_le
-/
theorem closure_le_eq [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g) :
    closure { b | f b <= g b } = { b | f b <= g b } :=
  (isClosed_le hf hg).closure_eq

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `closure_lt_subset_le` / 定理 `closure_lt_subset_le`

English:
theorem closure_lt_subset_le
  statement: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  proof: (closure_minimal fun _ => le_of_lt) isClosed_le hf hg

@[to_dual self (reorder := f g, hf hg)]

中文:
定理 closure_lt_subset_le
  结论: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  证明: (closure_minimal fun _ => le_of_lt) isClosed_le hf hg

@[to_dual self (reorder := f g, hf hg)]

Depends on / 依赖: closure_minimal, isClosed_le, le_of_lt
-/
theorem closure_lt_subset_le [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
    (hg : Continuous g) : closure { b | f b < g b } subseteq { b | f b <= g b } :=
(closure_minimal fun _ => le_of_lt) isClosed_le hf hg

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `ContinuousWithinAt.closure_le` / 定理 `ContinuousWithinAt.closure_le`

English:
theorem ContinuousWithinAt.closure_le
  statement: [TopologicalSpace β] {f g : β -> α} {s : Set β} {x : β}
  proof: show (f x, g x) in { p : α × α | p.1 <= p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

中文:
定理 ContinuousWithinAt.closure_le
  结论: [TopologicalSpace β] {f g : β -> α} {s : Set β} {x : β}
  证明: show (f x, g x) in { p : α × α | p.1 <= p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

Depends on / 依赖: OrderClosedTopology, OrderClosedTopology.isClosed_le, closure_subset, hf.prodMk, isClosed_le, mem_closure, prodMk
-/
theorem ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β -> α} {s : Set β} {x : β}
    (hx : x in closure s) (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : forall y in s, f y <= g y) : f x <= g x :=
  show (f x, g x) in { p : α × α | p.1 <= p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

/-- If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set. -/
@[to_dual self (reorder := f g, hf hg)]
/--
theorem `IsClosed.isClosed_le` / 定理 `IsClosed.isClosed_le`

English:
theorem IsClosed.isClosed_le
  statement: [TopologicalSpace β] {f g : β -> α} {s : Set β} (hs : IsClosed s)
  proof: (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

@[to_dual self (reorder := f g, hf hg)]

中文:
定理 IsClosed.isClosed_le
  结论: [TopologicalSpace β] {f g : β -> α} {s : Set β} (hs : IsClosed s)
  证明: (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

@[to_dual self (reorder := f g, hf hg)]

Depends on / 依赖: OrderClosedTopology, OrderClosedTopology.isClosed_le, hf.prodMk, isClosed_le, preimage_isClosed_of_isClosed, prodMk
-/
theorem IsClosed.isClosed_le [TopologicalSpace β] {f g : β -> α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x in s | f x <= g x }) :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `le_on_closure` / 定理 `le_on_closure`

English:
theorem le_on_closure
  statement: [TopologicalSpace β] {f g : β -> α} {s : Set β} (h : forall x in s, f x <= g x)
  proof: have : s subseteq { y in closure s | f y <= g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

@[to_dual]

中文:
定理 le_on_closure
  结论: [TopologicalSpace β] {f g : β -> α} {s : Set β} (h : 对任意 x in s, f x <= g x)
  证明: have : s subseteq { y in closure s | f y <= g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

@[to_dual]

Depends on / 依赖: closure, closure_minimal, isClosed_closure, isClosed_closure.isClosed_le, isClosed_le, subset_closure, subseteq
-/
theorem le_on_closure [TopologicalSpace β] {f g : β -> α} {s : Set β} (h : forall x in s, f x <= g x)
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s)) ⦃x⦄ (hx : x in closure s) :
    f x <= g x :=
  have : s subseteq { y in closure s | f y <= g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

@[to_dual]
/--
theorem `IsClosed.epigraph` / 定理 `IsClosed.epigraph`

English:
theorem IsClosed.epigraph
  statement: [TopologicalSpace β] {f : β -> α} {s : Set β} (hs : IsClosed s)
  proof: (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

中文:
定理 IsClosed.epigraph
  结论: [TopologicalSpace β] {f : β -> α} {s : Set β} (hs : IsClosed s)
  证明: (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

Depends on / 依赖: Subset, Subset.rfl, continuousOn_fst, continuousOn_snd, continuous_fst, hf.comp, hs.preimage, isClosed_le, preimage
-/
theorem IsClosed.epigraph [TopologicalSpace β] {f : β -> α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 in s ∧ f p.1 <= p.2 } :=
  (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

section Tendsto

variable {ι : Type*} {l : Filter ι} [Preorder β] {F : ι -> β -> α} {f : β -> α} {s : Set β}

/--
lemma `monotoneOn_of_frequently_monotoneOn_of_tendsto` / 引理 `monotoneOn_of_frequently_monotoneOn_of_tendsto`

English:
lemma monotoneOn_of_frequently_monotoneOn_of_tendsto
  statement: (hF : existsᶠ i in l, MonotoneOn (F i) s)
  proof: fun a ha b hb hab => le_of_tendsto_of_tendsto_of_frequently (hlim a ha) (hlim b hb)
    hF.mono fun _ hi => hi ha hb hab

中文:
引理 monotoneOn_of_frequently_monotoneOn_of_tendsto
  结论: (hF : 存在ᶠ i in l, MonotoneOn (F i) s)
  证明: fun a ha b hb hab => le_of_tendsto_of_tendsto_of_frequently (hlim a ha) (hlim b hb)
    hF.mono fun _ hi => hi ha hb hab

Depends on / 依赖: hF.mono, le_of_tendsto_of_tendsto_of_frequently
-/
lemma monotoneOn_of_frequently_monotoneOn_of_tendsto (hF : existsᶠ i in l, MonotoneOn (F i) s)
    (hlim : forall x in s, Tendsto (fun i => F i x) l (𝓝 (f x))) : MonotoneOn f s :=
fun a ha b hb hab => le_of_tendsto_of_tendsto_of_frequently (hlim a ha) (hlim b hb)
    hF.mono fun _ hi => hi ha hb hab

/--
lemma `monotone_of_frequently_monotone_of_tendsto` / 引理 `monotone_of_frequently_monotone_of_tendsto`

English:
lemma monotone_of_frequently_monotone_of_tendsto
  statement: (hF : existsᶠ i in l, Monotone (F i))
  proof: monotoneOn_univ.1 monotoneOn_of_frequently_monotoneOn_of_tendsto
    (hF.mono fun _ hi => hi.monotoneOn _) fun x _ => hlim x

中文:
引理 monotone_of_frequently_monotone_of_tendsto
  结论: (hF : 存在ᶠ i in l, Monotone (F i))
  证明: monotoneOn_univ.1 monotoneOn_of_frequently_monotoneOn_of_tendsto
    (hF.mono fun _ hi => hi.monotoneOn _) fun x _ => hlim x

Depends on / 依赖: hF.mono, hi.monotoneOn, monotoneOn, monotoneOn_of_frequently_monotoneOn_of_tendsto, monotoneOn_univ
-/
lemma monotone_of_frequently_monotone_of_tendsto (hF : existsᶠ i in l, Monotone (F i))
    (hlim : forall x, Tendsto (fun i => F i x) l (𝓝 (f x))) : Monotone f :=
monotoneOn_univ.1 monotoneOn_of_frequently_monotoneOn_of_tendsto
    (hF.mono fun _ hi => hi.monotoneOn _) fun x _ => hlim x

/--
lemma `antitoneOn_of_frequently_antitoneOn_of_tendsto` / 引理 `antitoneOn_of_frequently_antitoneOn_of_tendsto`

English:
lemma antitoneOn_of_frequently_antitoneOn_of_tendsto
  statement: (hF : existsᶠ i in l, AntitoneOn (F i) s)
  proof: monotoneOn_of_frequently_monotoneOn_of_tendsto (α := αᵒᵈ) hF hlim

中文:
引理 antitoneOn_of_frequently_antitoneOn_of_tendsto
  结论: (hF : 存在ᶠ i in l, AntitoneOn (F i) s)
  证明: monotoneOn_of_frequently_monotoneOn_of_tendsto (α := αᵒᵈ) hF hlim

Depends on / 依赖: monotoneOn_of_frequently_monotoneOn_of_tendsto
-/
lemma antitoneOn_of_frequently_antitoneOn_of_tendsto (hF : existsᶠ i in l, AntitoneOn (F i) s)
    (hlim : forall x in s, Tendsto (fun i => F i x) l (𝓝 (f x))) : AntitoneOn f s :=
  monotoneOn_of_frequently_monotoneOn_of_tendsto (α := αᵒᵈ) hF hlim

/--
lemma `antitone_of_frequently_antitone_of_tendsto` / 引理 `antitone_of_frequently_antitone_of_tendsto`

English:
lemma antitone_of_frequently_antitone_of_tendsto
  statement: (hF : existsᶠ i in l, Antitone (F i))
  proof: monotone_of_frequently_monotone_of_tendsto (α := αᵒᵈ) hF hlim

中文:
引理 antitone_of_frequently_antitone_of_tendsto
  结论: (hF : 存在ᶠ i in l, Antitone (F i))
  证明: monotone_of_frequently_monotone_of_tendsto (α := αᵒᵈ) hF hlim

Depends on / 依赖: monotone_of_frequently_monotone_of_tendsto
-/
lemma antitone_of_frequently_antitone_of_tendsto (hF : existsᶠ i in l, Antitone (F i))
    (hlim : forall x, Tendsto (fun i => F i x) l (𝓝 (f x))) : Antitone f :=
  monotone_of_frequently_monotone_of_tendsto (α := αᵒᵈ) hF hlim

/--
theorem `isClosed_monotoneOn` / 定理 `isClosed_monotoneOn`

English:
theorem isClosed_monotoneOn
  statement: IsClosed {f : β -> α | MonotoneOn f s}
  proof: by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  exact fun g hg => monotoneOn_of_frequently_monotoneOn_of_tendsto hg
    fun x _ => continuousAt_apply x g

中文:
定理 isClosed_monotoneOn
  结论: IsClosed {f : β -> α | MonotoneOn f s}
  证明: by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  exact fun g hg => monotoneOn_of_frequently_monotoneOn_of_tendsto hg
    fun x _ => continuousAt_apply x g

Depends on / 依赖: clusterPt_principal_iff_frequently, continuousAt_apply, isClosed_iff_clusterPt, monotoneOn_of_frequently_monotoneOn_of_tendsto
-/
theorem isClosed_monotoneOn : IsClosed {f : β -> α | MonotoneOn f s} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  exact fun g hg => monotoneOn_of_frequently_monotoneOn_of_tendsto hg
    fun x _ => continuousAt_apply x g

/--
theorem `isClosed_monotone` / 定理 `isClosed_monotone`

English:
theorem isClosed_monotone
  statement: IsClosed {f : β -> α | Monotone f}
  proof: by
  simp_rw [← monotoneOn_univ]
  exact isClosed_monotoneOn

中文:
定理 isClosed_monotone
  结论: IsClosed {f : β -> α | Monotone f}
  证明: by
  simp_rw [← monotoneOn_univ]
  exact isClosed_monotoneOn

Depends on / 依赖: isClosed_monotoneOn, monotoneOn_univ, simp_rw
-/
theorem isClosed_monotone : IsClosed {f : β -> α | Monotone f} := by
  simp_rw [← monotoneOn_univ]
  exact isClosed_monotoneOn

/--
theorem `isClosed_antitoneOn` / 定理 `isClosed_antitoneOn`

English:
theorem isClosed_antitoneOn
  statement: IsClosed {f : β -> α | AntitoneOn f s}
  proof: isClosed_monotoneOn (α := αᵒᵈ)

中文:
定理 isClosed_antitoneOn
  结论: IsClosed {f : β -> α | AntitoneOn f s}
  证明: isClosed_monotoneOn (α := αᵒᵈ)

Depends on / 依赖: isClosed_monotoneOn
-/
theorem isClosed_antitoneOn : IsClosed {f : β -> α | AntitoneOn f s} :=
  isClosed_monotoneOn (α := αᵒᵈ)

/--
theorem `isClosed_antitone` / 定理 `isClosed_antitone`

English:
theorem isClosed_antitone
  statement: IsClosed {f : β -> α | Antitone f}
  proof: isClosed_monotone (α := αᵒᵈ)

中文:
定理 isClosed_antitone
  结论: IsClosed {f : β -> α | Antitone f}
  证明: isClosed_monotone (α := αᵒᵈ)

Depends on / 依赖: isClosed_monotone
-/
theorem isClosed_antitone : IsClosed {f : β -> α | Antitone f} :=
  isClosed_monotone (α := αᵒᵈ)

end Tendsto

end Preorder

section PartialOrder

variable [TopologicalSpace α] [PartialOrder α] [t : OrderClosedTopology α]

-- see Note [lower instance priority]
instance (priority := 90) OrderClosedTopology.to_t2Space : T2Space α :=
t2_iff_isClosed_diagonal.2 by
    simpa only [diagonal, le_antisymm_iff] using!
      t.isClosed_le'.inter (isClosed_le continuous_snd continuous_fst)

end PartialOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `isOpen_lt` / 定理 `isOpen_lt`

English:
theorem isOpen_lt
  given: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  proof: by
  simpa only [lt_iff_not_ge] using! (isClosed_le hg hf).isOpen_compl

@[to_dual isOpen_lt_prod']

中文:
定理 isOpen_lt
  条件: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g)
  证明: by
  simpa only [lt_iff_not_ge] using! (isClosed_le hg hf).isOpen_compl

@[to_dual isOpen_lt_prod']

Depends on / 依赖: isClosed_le, isOpen_compl, lt_iff_not_ge
-/
theorem isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { b | f b < g b } := by
  simpa only [lt_iff_not_ge] using! (isClosed_le hg hf).isOpen_compl

@[to_dual isOpen_lt_prod']
/--
theorem `isOpen_lt_prod` / 定理 `isOpen_lt_prod`

English:
theorem isOpen_lt_prod
  statement: IsOpen { p : α × α | p.1 < p.2 }
  proof: isOpen_lt continuous_fst continuous_snd

中文:
定理 isOpen_lt_prod
  结论: IsOpen { p : α × α | p.1 < p.2 }
  证明: isOpen_lt continuous_fst continuous_snd

Depends on / 依赖: continuous_fst, continuous_snd, isOpen_lt
-/
theorem isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 } :=
  isOpen_lt continuous_fst continuous_snd

variable {a b : α}

@[to_dual self]
/--
theorem `isOpen_Ioo` / 定理 `isOpen_Ioo`

English:
theorem isOpen_Ioo
  statement: IsOpen (Ioo a b)
  proof: IsOpen.inter isOpen_Ioi isOpen_Iio

@[to_dual self, simp]

中文:
定理 isOpen_Ioo
  结论: IsOpen (Ioo a b)
  证明: IsOpen.inter isOpen_Ioi isOpen_Iio

@[to_dual self, simp]

Depends on / 依赖: IsOpen, IsOpen.inter, isOpen_Iio, isOpen_Ioi
-/
theorem isOpen_Ioo : IsOpen (Ioo a b) :=
  IsOpen.inter isOpen_Ioi isOpen_Iio

@[to_dual self, simp]
/--
theorem `interior_Ioo` / 定理 `interior_Ioo`

English:
theorem interior_Ioo
  statement: interior (Ioo a b) = Ioo a b
  proof: isOpen_Ioo.interior_eq

@[to_dual self]

中文:
定理 interior_Ioo
  结论: interior (Ioo a b) = Ioo a b
  证明: isOpen_Ioo.interior_eq

@[to_dual self]

Depends on / 依赖: interior_eq, isOpen_Ioo, isOpen_Ioo.interior_eq
-/
theorem interior_Ioo : interior (Ioo a b) = Ioo a b :=
  isOpen_Ioo.interior_eq

@[to_dual self]
/--
theorem `Ioo_subset_closure_interior` / 定理 `Ioo_subset_closure_interior`

English:
theorem Ioo_subset_closure_interior
  statement: Ioo a b subseteq closure (interior (Ioo a b))
  proof: by
  simp only [interior_Ioo, subset_closure]

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 Ioo_subset_closure_interior
  结论: Ioo a b subseteq closure (interior (Ioo a b))
  证明: by
  simp only [interior_Ioo, subset_closure]

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: interior_Ioo, subset_closure
-/
theorem Ioo_subset_closure_interior : Ioo a b subseteq closure (interior (Ioo a b)) := by
  simp only [interior_Ioo, subset_closure]

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `Ioo_mem_nhds` / 定理 `Ioo_mem_nhds`

English:
theorem Ioo_mem_nhds
  given: {a b x : α} (ha : a < x) (hb : x < b)
  statement: Ioo a b in 𝓝 x
  proof: IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

@[to_dual (reorder := ha hb)]

中文:
定理 Ioo_mem_nhds
  条件: {a b x : α} (ha : a < x) (hb : x < b)
  结论: Ioo a b in 𝓝 x
  证明: IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

@[to_dual (reorder := ha hb)]

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, isOpen_Ioo, mem_nhds
-/
theorem Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b in 𝓝 x :=
  IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

@[to_dual (reorder := ha hb)]
/--
theorem `Ioc_mem_nhds` / 定理 `Ioc_mem_nhds`

English:
theorem Ioc_mem_nhds
  given: {a b x : α} (ha : a < x) (hb : x < b)
  statement: Ioc a b in 𝓝 x
  proof: mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 Ioc_mem_nhds
  条件: {a b x : α} (ha : a < x) (hb : x < b)
  结论: Ioc a b in 𝓝 x
  证明: mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: Ioo_mem_nhds, Ioo_subset_Ioc_self, mem_of_superset
-/
theorem Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b in 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `Icc_mem_nhds` / 定理 `Icc_mem_nhds`

English:
theorem Icc_mem_nhds
  given: {a b x : α} (ha : a < x) (hb : x < b)
  statement: Icc a b in 𝓝 x
  proof: mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

中文:
定理 Icc_mem_nhds
  条件: {a b x : α} (ha : a < x) (hb : x < b)
  结论: Icc a b in 𝓝 x
  证明: mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

Depends on / 依赖: Ioo_mem_nhds, Ioo_subset_Icc_self, mem_of_superset
-/
theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b in 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

/-- The only order closed topology on a linear order which is a `PredOrder` and a `SuccOrder`
is the discrete topology.

This theorem is not an instance,
because it causes searches for `PredOrder` and `SuccOrder` with their `Preorder` arguments
and very rarely matches. -/
@[to_dual self (reorder := 5 6)]
/--
theorem `DiscreteTopology.of_predOrder_succOrder` / 定理 `DiscreteTopology.of_predOrder_succOrder`

English:
theorem DiscreteTopology.of_predOrder_succOrder
  given: [PredOrder α] [SuccOrder α]
  proof: by
  refine discreteTopology_iff_nhds.mpr fun a => ?_
  rw [← nhdsWithin_univ]; rw [← Iic_union_Ioi]; rw [nhdsWithin_union]; rw [PredOrder.nhdsLE]; rw [SuccOrder.nhdsGT]; rw [sup_bot_eq]

中文:
定理 DiscreteTopology.of_predOrder_succOrder
  条件: [PredOrder α] [SuccOrder α]
  证明: by
  refine discreteTopology_iff_nhds.mpr fun a => ?_
  rw [← nhdsWithin_univ]; rw [← Iic_union_Ioi]; rw [nhdsWithin_union]; rw [PredOrder.nhdsLE]; rw [SuccOrder.nhdsGT]; rw [sup_bot_eq]

Depends on / 依赖: Iic_union_Ioi, PredOrder, PredOrder.nhdsLE, SuccOrder, SuccOrder.nhdsGT, discreteTopology_iff_nhds, discreteTopology_iff_nhds.mpr, nhdsGT, nhdsLE, nhdsWithin_union, nhdsWithin_univ, sup_bot_eq
-/
theorem DiscreteTopology.of_predOrder_succOrder [PredOrder α] [SuccOrder α] :
    DiscreteTopology α := by
  refine discreteTopology_iff_nhds.mpr fun a => ?_
  rw [← nhdsWithin_univ]; rw [← Iic_union_Ioi]; rw [nhdsWithin_union]; rw [PredOrder.nhdsLE]; rw [SuccOrder.nhdsGT]; rw [sup_bot_eq]

end LinearOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {f g : β -> α}

section

variable [TopologicalSpace β]

@[to_dual self (reorder := f g, hf hg)]
/--
theorem `lt_subset_interior_le` / 定理 `lt_subset_interior_le`

English:
theorem lt_subset_interior_le
  given: (hf : Continuous f) (hg : Continuous g)
  proof: (interior_maximal fun _ => le_of_lt) isOpen_lt hf hg

@[to_dual (reorder := f g, hf hg) frontier_ge_subset_eq]

中文:
定理 lt_subset_interior_le
  条件: (hf : Continuous f) (hg : Continuous g)
  证明: (interior_maximal fun _ => le_of_lt) isOpen_lt hf hg

@[to_dual (reorder := f g, hf hg) frontier_ge_subset_eq]

Depends on / 依赖: interior_maximal, isOpen_lt, le_of_lt
-/
theorem lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) :
    { b | f b < g b } subseteq interior { b | f b <= g b } :=
(interior_maximal fun _ => le_of_lt) isOpen_lt hf hg

@[to_dual (reorder := f g, hf hg) frontier_ge_subset_eq]
/--
theorem `frontier_le_subset_eq` / 定理 `frontier_le_subset_eq`

English:
theorem frontier_le_subset_eq
  given: (hf : Continuous f) (hg : Continuous g)
  proof: by
  rw [frontier_eq_closure_inter_closure]; rw [closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert! hb₂ using 2; simp only [not_le.symm]; rfl

@[to_dual]

中文:
定理 frontier_le_subset_eq
  条件: (hf : Continuous f) (hg : Continuous g)
  证明: by
  rw [frontier_eq_closure_inter_closure]; rw [closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert! hb₂ using 2; simp only [not_le.symm]; rfl

@[to_dual]

Depends on / 依赖: closure_le_eq, closure_lt_subset_le, convert, frontier_eq_closure_inter_closure, le_antisymm, not_le, not_le.symm
-/
theorem frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b <= g b } subseteq { b | f b = g b } := by
  rw [frontier_eq_closure_inter_closure]; rw [closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert! hb₂ using 2; simp only [not_le.symm]; rfl

@[to_dual]
/--
theorem `frontier_Iic_subset` / 定理 `frontier_Iic_subset`

English:
theorem frontier_Iic_subset
  given: (a : α)
  statement: frontier (Iic a) subseteq {a}
  proof: frontier_le_subset_eq (@continuous_id α _) continuous_const

@[to_dual (reorder := f g, hf hg) frontier_gt_subset_eq]

中文:
定理 frontier_Iic_subset
  条件: (a : α)
  结论: frontier (Iic a) subseteq {a}
  证明: frontier_le_subset_eq (@continuous_id α _) continuous_const

@[to_dual (reorder := f g, hf hg) frontier_gt_subset_eq]

Depends on / 依赖: continuous_const, continuous_id, frontier_le_subset_eq
-/
theorem frontier_Iic_subset (a : α) : frontier (Iic a) subseteq {a} :=
  frontier_le_subset_eq (@continuous_id α _) continuous_const

@[to_dual (reorder := f g, hf hg) frontier_gt_subset_eq]
/--
theorem `frontier_lt_subset_eq` / 定理 `frontier_lt_subset_eq`

English:
theorem frontier_lt_subset_eq
  given: (hf : Continuous f) (hg : Continuous g)
  proof: by
  simpa only [← not_lt, ← compl_ofPred, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

@[to_dual none]

中文:
定理 frontier_lt_subset_eq
  条件: (hf : Continuous f) (hg : Continuous g)
  证明: by
  simpa only [← not_lt, ← compl_ofPred, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

@[to_dual none]

Depends on / 依赖: compl_ofPred, eq_comm, frontier_compl, frontier_le_subset_eq, not_lt
-/
theorem frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b < g b } subseteq { b | f b = g b } := by
  simpa only [← not_lt, ← compl_ofPred, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

@[to_dual none]
/--
theorem `continuous_if_le` / 定理 `continuous_if_le`

English:
theorem continuous_if_le
  statement: [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {f' g' : β -> γ}
  proof: by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

@[to_dual if_ge]

中文:
定理 continuous_if_le
  结论: [TopologicalSpace γ] [对任意 x, Decidable (f x <= g x)] {f' g' : β -> γ}
  证明: by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

@[to_dual if_ge]

Depends on / 依赖: closure_eq, closure_lt_subset_le, continuous_if, frontier_le_subset_eq, isClosed_le, not_le
-/
theorem continuous_if_le [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {f' g' : β -> γ}
    (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' { x | f x <= g x })
    (hg' : ContinuousOn g' { x | g x <= f x }) (hfg : forall x, f x = g x -> f' x = g' x) :
    Continuous fun x => if f x <= g x then f' x else g' x := by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

@[to_dual if_ge]
/--
theorem `Continuous.if_le` / 定理 `Continuous.if_le`

English:
theorem Continuous.if_le
  statement: [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {f' g' : β -> γ}
  proof: continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

@[to_dual self (reorder := f g, y z, hf hg)]

中文:
定理 Continuous.if_le
  结论: [TopologicalSpace γ] [对任意 x, Decidable (f x <= g x)] {f' g' : β -> γ}
  证明: continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

@[to_dual self (reorder := f g, y z, hf hg)]

Depends on / 依赖: continuousOn, continuous_if_le
-/
theorem Continuous.if_le [TopologicalSpace γ] [forall x, Decidable (f x <= g x)] {f' g' : β -> γ}
    (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g)
    (hfg : forall x, f x = g x -> f' x = g' x) : Continuous fun x => if f x <= g x then f' x else g' x :=
  continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

@[to_dual self (reorder := f g, y z, hf hg)]
/--
theorem `Filter.Tendsto.eventually_lt` / 定理 `Filter.Tendsto.eventually_lt`

English:
theorem Filter.Tendsto.eventually_lt
  statement: {l : Filter γ} {f g : γ -> α} {y z : α} (hf : Tendsto f l (𝓝 y))
  proof: let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
(hg.eventually (Ioi_mem_nhds hb)).mp (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

@[to_dual self (reorder := f g, hf hg)]
nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g 

中文:
定理 Filter.Tendsto.eventually_lt
  结论: {l : Filter γ} {f g : γ -> α} {y z : α} (hf : Tendsto f l (𝓝 y))
  证明: let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
(hg.eventually (Ioi_mem_nhds hb)).mp (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

@[to_dual self (reorder := f g, hf hg)]
nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g 

Depends on / 依赖: Iio_mem_nhds, Ioi_mem_nhds, eventually, exists_disjoint_Iio_Ioi, hf.eventually, hg.eventually, hyz.exists_disjoint_Iio_Ioi
-/
theorem Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ -> α} {y z : α} (hf : Tendsto f l (𝓝 y))
    (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : forallᶠ x in l, f x < g x :=
  let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
(hg.eventually (Ioi_mem_nhds hb)).mp (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

@[to_dual self (reorder := f g, hf hg)]
nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hfg : f x₀ < g x₀) : forallᶠ x in 𝓝 x₀, f x < g x :=
  hf.eventually_lt hg hfg

@[to_dual (attr := continuity, fun_prop)]
/--
theorem `Continuous.max` / 定理 `Continuous.max`

English:
theorem Continuous.max
  given: (hf : Continuous f) (hg : Continuous g)
  proof: by
  simp only [max_def]
  exact hg.if_ge hf hg hf fun x => id

中文:
定理 Continuous.max
  条件: (hf : Continuous f) (hg : Continuous g)
  证明: by
  simp only [max_def]
  exact hg.if_ge hf hg hf fun x => id
-/
protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => max (f b) (g b) := by
  simp only [max_def]
  exact hg.if_ge hf hg hf fun x => id

end

@[to_dual]
/--
theorem `continuous_max` / 定理 `continuous_max`

English:
theorem continuous_max
  statement: Continuous fun p : α × α => max p.1 p.2
  proof: continuous_fst.max continuous_snd

@[to_dual]

中文:
定理 continuous_max
  结论: Continuous fun p : α × α => max p.1 p.2
  证明: continuous_fst.max continuous_snd

@[to_dual]

Depends on / 依赖: continuous_fst, continuous_fst.max, continuous_snd
-/
theorem continuous_max : Continuous fun p : α × α => max p.1 p.2 :=
  continuous_fst.max continuous_snd

@[to_dual]
/--
theorem `Filter.Tendsto.max` / 定理 `Filter.Tendsto.max`

English:
theorem Filter.Tendsto.max
  statement: {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
  proof: (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

@[to_dual]

中文:
定理 Filter.Tendsto.max
  结论: {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
  证明: (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

@[to_dual]
-/
protected theorem Filter.Tendsto.max {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => max (f b) (g b)) b (𝓝 (max a₁ a₂)) :=
  (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

@[to_dual]
/--
theorem `Filter.Tendsto.max_right` / 定理 `Filter.Tendsto.max_right`

English:
theorem Filter.Tendsto.max_right
  given: {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a))
  proof: by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

@[to_dual]

中文:
定理 Filter.Tendsto.max_right
  条件: {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a))
  证明: by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

@[to_dual]
-/
protected theorem Filter.Tendsto.max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max a (f i)) l (𝓝 a) := by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

@[to_dual]
/--
theorem `Filter.Tendsto.max_left` / 定理 `Filter.Tendsto.max_left`

English:
theorem Filter.Tendsto.max_left
  given: {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a))
  proof: by
  simp_rw [max_comm _ a]
  exact h.max_right

@[to_dual]

中文:
定理 Filter.Tendsto.max_left
  条件: {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a))
  证明: by
  simp_rw [max_comm _ a]
  exact h.max_right

@[to_dual]
-/
protected theorem Filter.Tendsto.max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max (f i) a) l (𝓝 a) := by
  simp_rw [max_comm _ a]
  exact h.max_right

@[to_dual]
/--
theorem `Filter.tendsto_nhds_max_right` / 定理 `Filter.tendsto_nhds_max_right`

English:
theorem Filter.tendsto_nhds_max_right
  given: {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a))
  proof: by
  obtain ⟨h₁, h₂⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

@[to_dual]

中文:
定理 Filter.tendsto_nhds_max_right
  条件: {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a))
  证明: by
  obtain ⟨h₁, h₂⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

@[to_dual]

Depends on / 依赖: lt_max_of_lt_right, max_right, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mp, tendsto_nhdsWithin_iff.mpr
-/
theorem Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max a (f i)) l (𝓝[>] a) := by
  obtain ⟨h₁, h₂⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

@[to_dual]
/--
theorem `Filter.tendsto_nhds_max_left` / 定理 `Filter.tendsto_nhds_max_left`

English:
theorem Filter.tendsto_nhds_max_left
  given: {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a))
  proof: by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

@[to_dual self]

中文:
定理 Filter.tendsto_nhds_max_left
  条件: {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a))
  证明: by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

@[to_dual self]

Depends on / 依赖: Filter, Filter.tendsto_nhds_max_right, max_comm, simp_rw, tendsto_nhds_max_right
-/
theorem Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max (f i) a) l (𝓝[>] a) := by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

@[to_dual self]
/--
theorem `Dense.exists_between` / 定理 `Dense.exists_between`

English:
theorem Dense.exists_between
  given: [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y)
  proof: hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

@[to_dual]

中文:
定理 Dense.exists_between
  条件: [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y)
  证明: hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

@[to_dual]

Depends on / 依赖: exists_mem_open, hs.exists_mem_open, isOpen_Ioo, nonempty_Ioo
-/
theorem Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y) :
    exists z in s, z in Ioo x y :=
  hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

@[to_dual]
/--
theorem `Dense.Ioi_eq_biUnion` / 定理 `Dense.Ioi_eq_biUnion`

English:
theorem Dense.Ioi_eq_biUnion
  given: [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α)
  proof: by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun y hy => Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hy⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hy.1⟩, hy.2⟩

中文:
定理 Dense.Ioi_eq_biUnion
  条件: [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α)
  证明: by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun y hy => Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hy⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hy.1⟩, hy.2⟩

Depends on / 依赖: Ioi_subset_Ioi, Subset, Subset.antisymm, antisymm, exists_between, hs.exists_between, le_of_lt
-/
theorem Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Ioi x = ⋃ y in s inter Ioi x, Ioi y := by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun y hy => Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hy⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hy.1⟩, hy.2⟩

end LinearOrder

end OrderClosedTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [TopologicalSpace α] [OrderClosedTopology α] [Preorder β] [TopologicalSpace β]
  body: ⟨(isClosed_le continuous_fst.fst continuous_snd.fst).inter
    (isClosed_le continuous_fst.snd continuous_snd.snd)⟩

中文:
实例 [Preorder
  签名: α] [TopologicalSpace α] [OrderClosedTopology α] [Preorder β] [TopologicalSpace β]
  定义体: ⟨(isClosed_le continuous_fst.fst continuous_snd.fst).inter
    (isClosed_le continuous_fst.snd continuous_snd.snd)⟩

Depends on / 依赖: continuous_fst, continuous_fst.fst, continuous_fst.snd, continuous_snd, continuous_snd.fst, continuous_snd.snd, isClosed_le
-/
instance [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [Preorder β] [TopologicalSpace β]
    [OrderClosedTopology β] : OrderClosedTopology (α × β) :=
  ⟨(isClosed_le continuous_fst.fst continuous_snd.fst).inter
    (isClosed_le continuous_fst.snd continuous_snd.snd)⟩

instance {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] [forall i, TopologicalSpace (α i)]
    [forall i, OrderClosedTopology (α i)] : OrderClosedTopology (forall i, α i) := by
  constructor
  simp only [Pi.le_def, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).fst' (continuous_apply i).snd'

/--
Instance `Pi.orderClosedTopology'` / 实例 `Pi.orderClosedTopology'`

English:
instance Pi.orderClosedTopology'
  signature: [Preorder β] [TopologicalSpace β] [OrderClosedTopology β]
  body: inferInstance

中文:
实例 Pi.orderClosedTopology'
  签名: [Preorder β] [TopologicalSpace β] [OrderClosedTopology β]
  定义体: inferInstance
-/
instance Pi.orderClosedTopology' [Preorder β] [TopologicalSpace β] [OrderClosedTopology β] :
    OrderClosedTopology (α -> β) :=
  inferInstance
