/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Separation.Regular

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/

@[expose] public section


open Set Filter

open Topology

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

/--
Definition of `Function.leftLim` / `Function.leftLim` 的定义

English:
definition Function.leftLim
  signature: (f : α -> β) (a : α)
  body: by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬exists y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

中文:
定义 函数.leftLim
  签名: (f : α -> β) (a : α)
  定义体: by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬exists y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

Depends on / 依赖: Nonempty, Preorder, Preorder.topology, Tendsto, TopologicalSpace, classical, limUnder, topology
-/
noncomputable def Function.leftLim (f : α -> β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬exists y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

/--
Definition of `Function.rightLim` / `Function.rightLim` 的定义

English:
definition Function.rightLim
  signature: (f : α -> β) (a : α)
  body: @Function.leftLim αᵒᵈ β _ _ f a

中文:
定义 函数.rightLim
  签名: (f : α -> β) (a : α)
  定义体: @Function.leftLim αᵒᵈ β _ _ f a

Depends on / 依赖: Function, Function.leftLim, leftLim
-/
noncomputable def Function.rightLim (f : α -> β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a

open Function

/--
theorem `leftLim_eq_of_tendsto` / 定理 `leftLim_eq_of_tendsto`

English:
theorem leftLim_eq_of_tendsto
  statement: [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
  proof: by
  have h'' : exists y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, neBot_iff.mp h, h'', not_true, or_self_iff, if_false]
  exact lim_eq h'

中文:
定理 leftLim_eq_of_tendsto
  结论: [hα : 拓扑空间 α] [h'α : Order拓扑 α] [T2空间 β]
  证明: by
  have h'' : exists y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, neBot_iff.mp h, h'', not_true, or_self_iff, if_false]
  exact lim_eq h'

Depends on / 依赖: Tendsto, if_false, leftLim, lim_eq, neBot_iff, neBot_iff.mp, not_true, or_self_iff, topology_eq_generate_intervals
-/
theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).NeBot] (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : exists y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, neBot_iff.mp h, h'', not_true, or_self_iff, if_false]
  exact lim_eq h'

/--
theorem `rightLim_eq_of_tendsto` / 定理 `rightLim_eq_of_tendsto`

English:
theorem rightLim_eq_of_tendsto
  statement: [TopologicalSpace α] [OrderTopology α] [T2Space β]
  proof: leftLim_eq_of_tendsto (α := αᵒᵈ) (h := h) h'

中文:
定理 rightLim_eq_of_tendsto
  结论: [拓扑空间 α] [Order拓扑 α] [T2空间 β]
  证明: leftLim_eq_of_tendsto (α := αᵒᵈ) (h := h) h'

Depends on / 依赖: leftLim_eq_of_tendsto
-/
theorem rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α -> β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim f a = y :=
  leftLim_eq_of_tendsto (α := αᵒᵈ) (h := h) h'

/--
theorem `leftLim_eq_of_eq_bot` / 定理 `leftLim_eq_of_eq_bot`

English:
theorem leftLim_eq_of_eq_bot
  statement: [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α -> β) {a : α}
  proof: by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

中文:
定理 leftLim_eq_of_eq_bot
  结论: [hα : 拓扑空间 α] [h'α : Order拓扑 α] (f : α -> β) {a : α}
  证明: by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

Depends on / 依赖: leftLim, topology_eq_generate_intervals
-/
theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α -> β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

/--
theorem `rightLim_eq_of_eq_bot` / 定理 `rightLim_eq_of_eq_bot`

English:
theorem rightLim_eq_of_eq_bot
  statement: [TopologicalSpace α] [OrderTopology α] (f : α -> β) {a : α}
  proof: leftLim_eq_of_eq_bot (α := αᵒᵈ) f h

中文:
定理 rightLim_eq_of_eq_bot
  结论: [拓扑空间 α] [Order拓扑 α] (f : α -> β) {a : α}
  证明: leftLim_eq_of_eq_bot (α := αᵒᵈ) f h

Depends on / 依赖: leftLim_eq_of_eq_bot
-/
theorem rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α -> β) {a : α}
    (h : 𝓝[>] a = ⊥) : rightLim f a = f a :=
  leftLim_eq_of_eq_bot (α := αᵒᵈ) f h

/--
theorem `leftLim_eq_of_not_tendsto` / 定理 `leftLim_eq_of_not_tendsto`

English:
theorem leftLim_eq_of_not_tendsto
  proof: by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

中文:
定理 leftLim_eq_of_not_tendsto
  证明: by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

Depends on / 依赖: leftLim, topology_eq_generate_intervals
-/
theorem leftLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α -> β) {a : α}
    (h : ¬ exists y, Tendsto f (𝓝[<] a) (𝓝 y)) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

/--
theorem `rightLim_eq_of_not_tendsto` / 定理 `rightLim_eq_of_not_tendsto`

English:
theorem rightLim_eq_of_not_tendsto
  proof: leftLim_eq_of_not_tendsto (α := αᵒᵈ) f h

中文:
定理 rightLim_eq_of_not_tendsto
  证明: leftLim_eq_of_not_tendsto (α := αᵒᵈ) f h

Depends on / 依赖: leftLim_eq_of_not_tendsto
-/
theorem rightLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α -> β) {a : α}
    (h : ¬ exists y, Tendsto f (𝓝[>] a) (𝓝 y)) : rightLim f a = f a :=
  leftLim_eq_of_not_tendsto (α := αᵒᵈ) f h

/--
theorem `leftLim_eq_of_isBot` / 定理 `leftLim_eq_of_isBot`

English:
theorem leftLim_eq_of_isBot
  given: {f : α -> β} {a : α} (ha : IsBot a)
  proof: by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

中文:
定理 leftLim_eq_of_isBot
  条件: {f : α -> β} {a : α} (ha : IsBot a)
  证明: by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, leftLim_eq_of_eq_bot, topology
-/
theorem leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBot a) :
    leftLim f a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

/--
theorem `rightLim_eq_of_isTop` / 定理 `rightLim_eq_of_isTop`

English:
theorem rightLim_eq_of_isTop
  given: {f : α -> β} {a : α} (ha : IsTop a)
  proof: leftLim_eq_of_isBot (α := αᵒᵈ) ha

中文:
定理 rightLim_eq_of_isTop
  条件: {f : α -> β} {a : α} (ha : IsTop a)
  证明: leftLim_eq_of_isBot (α := αᵒᵈ) ha

Depends on / 依赖: leftLim_eq_of_isBot
-/
theorem rightLim_eq_of_isTop {f : α -> β} {a : α} (ha : IsTop a) :
    rightLim f a = f a :=
  leftLim_eq_of_isBot (α := αᵒᵈ) ha

/--
theorem `ContinuousWithinAt.leftLim_eq` / 定理 `ContinuousWithinAt.leftLim_eq`

English:
theorem ContinuousWithinAt.leftLim_eq
  statement: [TopologicalSpace α] [OrderTopology α] [T2Space β]
  proof: by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

中文:
定理 ContinuousWithinAt.leftLim_eq
  结论: [拓扑空间 α] [Order拓扑 α] [T2空间 β]
  证明: by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

Depends on / 依赖: Iio_subset_Iic_self, eq_or_neBot, hf.tendsto.mono_left, leftLim_eq_of_eq_bot, leftLim_eq_of_tendsto, mono_left, nhdsWithin_mono, tendsto
-/
theorem ContinuousWithinAt.leftLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α -> β} {a : α} (hf : ContinuousWithinAt f (Iic a) a) : leftLim f a = f a := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

/--
theorem `ContinuousWithinAt.rightLim_eq` / 定理 `ContinuousWithinAt.rightLim_eq`

English:
theorem ContinuousWithinAt.rightLim_eq
  statement: [TopologicalSpace α] [OrderTopology α] [T2Space β]
  proof: ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) hf

中文:
定理 ContinuousWithinAt.rightLim_eq
  结论: [拓扑空间 α] [Order拓扑 α] [T2空间 β]
  证明: ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) hf

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.leftLim_eq, leftLim_eq
-/
theorem ContinuousWithinAt.rightLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α -> β} {a : α} (hf : ContinuousWithinAt f (Ici a) a) : rightLim f a = f a :=
  ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) hf

/--
theorem `tendsto_leftLim_of_tendsto` / 定理 `tendsto_leftLim_of_tendsto`

English:
theorem tendsto_leftLim_of_tendsto
  statement: [TopologicalSpace α] [h'α : OrderTopology α]
  proof: by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

中文:
定理 tendsto_leftLim_of_tendsto
  结论: [拓扑空间 α] [h'α : Order拓扑 α]
  证明: by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

Depends on / 依赖: eq_or_neBot, leftLim, neBot_iff, not_true_eq_false, or_self, reduceIte, tendsto_nhds_limUnder, topology_eq_generate_intervals
-/
theorem tendsto_leftLim_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[<] a) (𝓝 y)) :
    Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a)) := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

/--
theorem `tendsto_rightLim_of_tendsto` / 定理 `tendsto_rightLim_of_tendsto`

English:
theorem tendsto_rightLim_of_tendsto
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: tendsto_leftLim_of_tendsto (α := αᵒᵈ) h

中文:
定理 tendsto_rightLim_of_tendsto
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: tendsto_leftLim_of_tendsto (α := αᵒᵈ) h

Depends on / 依赖: tendsto_leftLim_of_tendsto
-/
theorem tendsto_rightLim_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[>] a) (𝓝 y)) :
    Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a)) :=
  tendsto_leftLim_of_tendsto (α := αᵒᵈ) h

/--
theorem `mapClusterPt_leftLim` / 定理 `mapClusterPt_leftLim`

English:
theorem mapClusterPt_leftLim
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: by
  have A : (𝓝 (f a) ⊓ map f (𝓝[<=] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' => ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, 

中文:
定理 mapClusterPt_leftLim
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: by
  have A : (𝓝 (f a) ⊓ map f (𝓝[<=] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' => ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, 

Depends on / 依赖: ClusterPt, MapClusterPt, Tendsto, eq_or_neBot, f.leftLim, inf_neBot_iff, inf_neBot_iff.mpr, leftLim, leftLim_eq_of_eq_bot, leftLim_eq_of_not_tendsto, mem_map, mem_of_mem_nhds, mem_of_mem_nhdsWithin, self_mem_Iic, tendsto_leftLim_
-/
theorem mapClusterPt_leftLim [TopologicalSpace α] [OrderTopology α]
    (f : α -> β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[<=] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[<=] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' => ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLim_eq_of_eq_bot, A]
  by_cases! H : ¬ exists y, Tendsto f (𝓝[<] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLim_eq_of_not_tendsto, A]
  have : MapClusterPt (f.leftLim a) (𝓝[<] a) f := (tendsto_leftLim_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ Iio_subset_Iic_self)

/--
theorem `mapClusterPt_rightLim` / 定理 `mapClusterPt_rightLim`

English:
theorem mapClusterPt_rightLim
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: mapClusterPt_leftLim (α := αᵒᵈ) _ _

中文:
定理 mapClusterPt_rightLim
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: mapClusterPt_leftLim (α := αᵒᵈ) _ _

Depends on / 依赖: mapClusterPt_leftLim
-/
theorem mapClusterPt_rightLim [TopologicalSpace α] [OrderTopology α]
    (f : α -> β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[>=] a) f :=
  mapClusterPt_leftLim (α := αᵒᵈ) _ _

/--
theorem `continuousWithinAt_leftLim_Iic` / 定理 `continuousWithinAt_leftLim_Iic`

English:
theorem continuousWithinAt_leftLim_Iic
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: by
  have : 𝓝[<=] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [nhdsWithin_union]
    simp
  rw [ContinuousWithinAt]; rw [this]; rw [tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_close

中文:
定理 continuousWithinAt_leftLim_Iic
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: by
  have : 𝓝[<=] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [nhdsWithin_union]
    simp
  rw [ContinuousWithinAt]; rw [this]; rw [tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_close

Depends on / 依赖: ContinuousWithinAt, Filter, Filter.nonempty_of_mem, Iio_union_Icc_eq_Iic, Nonempty, and_true, closed_nhds_basis, eq_or_neBot, f.leftLim, le_rfl, leftLim, nhdsWithin_union, nonempty_of_mem, s_closed, s_mem, self_mem_nhdsWithin, subseteq, tendsto_pure_nhds, tendsto_right_iff, tendsto_sup
-/
theorem continuousWithinAt_leftLim_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    ContinuousWithinAt f.leftLim (Iic a) a := by
  have : 𝓝[<=] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [nhdsWithin_union]
    simp
  rw [ContinuousWithinAt]; rw [this]; rw [tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  obtain ⟨u, au, hu⟩ : exists u, u < a ∧ Ioo u a subseteq {x | f x in s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · simpa [h'c, leftLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ exists y, Tendsto f (𝓝[<] c) (𝓝 y)
  · simpa [leftLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd

/--
theorem `leftLim_leftLim` / 定理 `leftLim_leftLim`

English:
theorem leftLim_leftLim
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: (continuousWithinAt_leftLim_Iic h).leftLim_eq

中文:
定理 leftLim_leftLim
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: (continuousWithinAt_leftLim_Iic h).leftLim_eq

Depends on / 依赖: continuousWithinAt_leftLim_Iic, leftLim_eq
-/
theorem leftLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    f.leftLim.leftLim a = f.leftLim a :=
  (continuousWithinAt_leftLim_Iic h).leftLim_eq

/--
theorem `continuousWithinAt_rightLim_Ici` / 定理 `continuousWithinAt_rightLim_Ici`

English:
theorem continuousWithinAt_rightLim_Ici
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: continuousWithinAt_leftLim_Iic (α := αᵒᵈ) h

中文:
定理 continuousWithinAt_rightLim_Ici
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: continuousWithinAt_leftLim_Iic (α := αᵒᵈ) h

Depends on / 依赖: continuousWithinAt_leftLim_Iic
-/
theorem continuousWithinAt_rightLim_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    ContinuousWithinAt f.rightLim (Ici a) a :=
  continuousWithinAt_leftLim_Iic (α := αᵒᵈ) h

/--
theorem `rightLim_rightLim` / 定理 `rightLim_rightLim`

English:
theorem rightLim_rightLim
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: leftLim_leftLim (α := αᵒᵈ) h

中文:
定理 rightLim_rightLim
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: leftLim_leftLim (α := αᵒᵈ) h

Depends on / 依赖: leftLim_leftLim
-/
theorem rightLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    f.rightLim.rightLim a = f.rightLim a :=
  leftLim_leftLim (α := αᵒᵈ) h

/--
theorem `leftLim_rightLim` / 定理 `leftLim_rightLim`

English:
theorem leftLim_rightLim
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : exists u, u < a ∧ Ioo u a subseteq {x | f x in s} := by
    

中文:
定理 leftLim_rightLim
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : exists u, u < a ∧ Ioo u a subseteq {x | f x in s} := by
    

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Ioo_mem_nhdsLT, Nonempty, closed_nhds_basis, eq_or_neBot, f.leftLim, filter_upwards, leftLim, leftLim_eq_of_tendsto, mem_nhdsLT_iff_exists_Ioo_subset, nonempty_of_mem, s_closed, s_mem, self_mem_nhdsWithin, subseteq, tendsto_right_iff
-/
theorem leftLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h' : (𝓝[<] a).NeBot] :
    f.rightLim.leftLim a = f.leftLim a := by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : exists u, u < a ∧ Ioo u a subseteq {x | f x in s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[>] c) with h'c | h'c
  · simpa [h'c, rightLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ exists y, Tendsto f (𝓝[>] c) (𝓝 y)
  · simpa [rightLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_rightLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hu hd

/--
theorem `rightLim_leftLim` / 定理 `rightLim_leftLim`

English:
theorem rightLim_leftLim
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: leftLim_rightLim (α := αᵒᵈ) h (h' := h')

中文:
定理 rightLim_leftLim
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: leftLim_rightLim (α := αᵒᵈ) h (h' := h')

Depends on / 依赖: leftLim_rightLim
-/
theorem rightLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) [h' : (𝓝[>] a).NeBot] :
    f.leftLim.rightLim a = f.rightLim a :=
  leftLim_rightLim (α := αᵒᵈ) h (h' := h')

/--
theorem `tendsto_atTop_of_mapClusterPt` / 定理 `tendsto_atTop_of_mapClusterPt`

English:
theorem tendsto_atTop_of_mapClusterPt
  proof: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : exists a, forall (b : α), a <= b -> MapClusterPt (g b) (𝓝 b) f ∧ f b in s := by
    simpa [eventually_atTop] usin

中文:
定理 tendsto_atTop_of_mapClusterPt
  证明: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : exists a, forall (b : α), a <= b -> MapClusterPt (g b) (𝓝 b) f ∧ f b in s := by
    simpa [eventually_atTop] usin

Depends on / 依赖: Ici_mem_nhds, Ioi_mem_atTop, MapClusterPt, closed_nhds_basis, eventually_atTop, filter_eq_bot_of_isEmpty, filter_upwards, ha.le, isEmpty_or_nonempty, mem_of_mapClusterPt, s_closed, s_closed.mem_of_mapClusterPt, s_mem, tendsto_right_iff
-/
theorem tendsto_atTop_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α -> β} {b : β}
    (h : Tendsto f atTop (𝓝 b)) (h' : forallᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : exists a, forall (b : α), a <= b -> MapClusterPt (g b) (𝓝 b) f ∧ f b in s := by
    simpa [eventually_atTop] using h'.and (h s_mem)
  filter_upwards [Ioi_mem_atTop u] with a (ha : u < a)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Ici_mem_nhds ha] with y hy using (hu y hy).2

/--
theorem `tendsto_atBot_of_mapClusterPt` / 定理 `tendsto_atBot_of_mapClusterPt`

English:
theorem tendsto_atBot_of_mapClusterPt
  proof: tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'

中文:
定理 tendsto_atBot_of_mapClusterPt
  证明: tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'

Depends on / 依赖: tendsto_atTop_of_mapClusterPt
-/
theorem tendsto_atBot_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoBotOrder α] {f g : α -> β} {b : β}
    (h : Tendsto f atBot (𝓝 b)) (h' : forallᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atBot (𝓝 b) :=
  tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'

/--
theorem `tendsto_leftLim_atTop_of_tendsto` / 定理 `tendsto_leftLim_atTop_of_tendsto`

English:
theorem tendsto_leftLim_atTop_of_tendsto
  proof: by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x => ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

中文:
定理 tendsto_leftLim_atTop_of_tendsto
  证明: by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x => ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

Depends on / 依赖: Eventually, Eventually.of_forall, MapClusterPt, MapClusterPt.mono, mapClusterPt_leftLim, nhdsWithin_le_nhds, of_forall, tendsto_atTop_of_mapClusterPt
-/
theorem tendsto_leftLim_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β]
    {f : α -> β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.leftLim atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x => ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

/--
theorem `tendsto_rightLim_atTop_of_tendsto` / 定理 `tendsto_rightLim_atTop_of_tendsto`

English:
theorem tendsto_rightLim_atTop_of_tendsto
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤)]; rw [← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall

中文:
定理 tendsto_rightLim_atTop_of_tendsto
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤)]; rw [← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall

Depends on / 依赖: Eventually, Eventually.of_forall, MapClusterPt, MapClusterPt.mono, OrderTop, OrderTop.atTop_eq, atTop_eq, f.rightLim, isTop_top, mapClusterPt_rightLim, nhdsWithin_le_nhds, of_forall, rightLim, rightLim_eq_of_isTop, tendsto_atTop_of_mapClusterPt, tendsto_nhds_unique, tendsto_pure_nhds, topOrderOrNoTopOrder
-/
theorem tendsto_rightLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.rightLim atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤)]; rw [← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x => ?_))
    exact MapClusterPt.mono (mapClusterPt_rightLim _ _) nhdsWithin_le_nhds

/--
theorem `tendsto_rightLim_atBot_of_tendsto` / 定理 `tendsto_rightLim_atBot_of_tendsto`

English:
theorem tendsto_rightLim_atBot_of_tendsto
  proof: tendsto_leftLim_atTop_of_tendsto (α := αᵒᵈ) h

中文:
定理 tendsto_rightLim_atBot_of_tendsto
  证明: tendsto_leftLim_atTop_of_tendsto (α := αᵒᵈ) h

Depends on / 依赖: tendsto_leftLim_atTop_of_tendsto
-/
theorem tendsto_rightLim_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoBotOrder α] [T3Space β]
    {f : α -> β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.rightLim atBot (𝓝 b) :=
  tendsto_leftLim_atTop_of_tendsto (α := αᵒᵈ) h

/--
theorem `tendsto_leftLim_atBot_of_tendsto` / 定理 `tendsto_leftLim_atBot_of_tendsto`

English:
theorem tendsto_leftLim_atBot_of_tendsto
  statement: [TopologicalSpace α] [OrderTopology α] [T3Space β]
  proof: tendsto_rightLim_atTop_of_tendsto (α := αᵒᵈ) h

中文:
定理 tendsto_leftLim_atBot_of_tendsto
  结论: [拓扑空间 α] [Order拓扑 α] [T3空间 β]
  证明: tendsto_rightLim_atTop_of_tendsto (α := αᵒᵈ) h

Depends on / 依赖: tendsto_rightLim_atTop_of_tendsto
-/
theorem tendsto_leftLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α -> β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.leftLim atBot (𝓝 b) :=
  tendsto_rightLim_atTop_of_tendsto (α := αᵒᵈ) h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α -> β} (hf : Monotone f) {x y : α}
include hf

/--
theorem `leftLim_eq_sSup` / 定理 `leftLim_eq_sSup`

English:
theorem leftLim_eq_sSup
  given: [TopologicalSpace α] [OrderTopology α] [(𝓝[<] x).NeBot]
  proof: leftLim_eq_of_tendsto (hf.tendsto_nhdsLT x)

中文:
定理 leftLim_eq_sSup
  条件: [拓扑空间 α] [Order拓扑 α] [(𝓝[<] x).NeBot]
  证明: leftLim_eq_of_tendsto (hf.tendsto_nhdsLT x)

Depends on / 依赖: hf.tendsto_nhdsLT, leftLim_eq_of_tendsto, tendsto_nhdsLT
-/
theorem leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] [(𝓝[<] x).NeBot] :
    leftLim f x = sSup (f '' Iio x) :=
  leftLim_eq_of_tendsto (hf.tendsto_nhdsLT x)

/--
theorem `rightLim_eq_sInf` / 定理 `rightLim_eq_sInf`

English:
theorem rightLim_eq_sInf
  given: [TopologicalSpace α] [OrderTopology α] [(𝓝[>] x).NeBot]
  proof: rightLim_eq_of_tendsto (hf.tendsto_nhdsGT x)

中文:
定理 rightLim_eq_sInf
  条件: [拓扑空间 α] [Order拓扑 α] [(𝓝[>] x).NeBot]
  证明: rightLim_eq_of_tendsto (hf.tendsto_nhdsGT x)

Depends on / 依赖: hf.tendsto_nhdsGT, rightLim_eq_of_tendsto, tendsto_nhdsGT
-/
theorem rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] [(𝓝[>] x).NeBot] :
    rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto (hf.tendsto_nhdsGT x)

/--
theorem `leftLim_le` / 定理 `leftLim_le`

English:
theorem leftLim_le
  given: (h : x <= y)
  statement: leftLim f x <= f y
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simpa [leftLim, h'] using hf h
  rw [leftLim_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 h') _ self_

中文:
定理 leftLim_le
  条件: (h : x <= y)
  结论: leftLim f x <= f y
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simpa [leftLim, h'] using hf h
  rw [leftLim_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 h') _ self_

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, and_imp, csSup_le, eq_or_neBot, forall_exists_index, forall_mem_nonempty_iff_neBot, hz.le.trans, image_nonempty, leftLim, leftLim_eq_sSup, mem_Iio, mem_image, self_mem_nhdsWithin, topology
-/
theorem leftLim_le (h : x <= y) : leftLim f x <= f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simpa [leftLim, h'] using hf h
  rw [leftLim_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 h') _ self_mem_nhdsWithin
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)

/--
theorem `le_leftLim` / 定理 `le_leftLim`

English:
theorem le_leftLim
  given: (h : x < y)
  statement: f x <= leftLim f y
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with h' | h'
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem

中文:
定理 le_leftLim
  条件: (h : x < y)
  结论: f x <= leftLim f y
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with h' | h'
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, and_imp, eq_or_neBot, forall_exists_index, h.le, hz.le, le_csSup, leftLim_eq_of_eq_bot, leftLim_eq_sSup, mem_Iio, mem_image, mem_image_of_mem, mem_ofPred_eq, topology, upperBounds
-/
theorem le_leftLim (h : x < y) : f x <= leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with h' | h'
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_ofPred_eq]
  intro z hz
  exact hf hz.le

@[gcongr, mono]
/--
theorem `leftLim` / 定理 `leftLim`

English:
theorem leftLim
  statement: Monotone (leftLim f)
  proof: by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)

中文:
定理 leftLim
  结论: 递增 (leftLim f)
  证明: by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)
-/
protected theorem leftLim : Monotone (leftLim f) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)

/--
theorem `le_rightLim` / 定理 `le_rightLim`

English:
theorem le_rightLim
  given: (h : x <= y)
  statement: f x <= rightLim f y
  proof: hf.dual.leftLim_le h

中文:
定理 le_rightLim
  条件: (h : x <= y)
  结论: f x <= rightLim f y
  证明: hf.dual.leftLim_le h

Depends on / 依赖: hf.dual.leftLim_le, leftLim_le
-/
theorem le_rightLim (h : x <= y) : f x <= rightLim f y :=
  hf.dual.leftLim_le h

/--
theorem `rightLim_le` / 定理 `rightLim_le`

English:
theorem rightLim_le
  given: (h : x < y)
  statement: rightLim f x <= f y
  proof: hf.dual.le_leftLim h

@[gcongr, mono]

中文:
定理 rightLim_le
  条件: (h : x < y)
  结论: rightLim f x <= f y
  证明: hf.dual.le_leftLim h

@[gcongr, mono]

Depends on / 依赖: hf.dual.le_leftLim, le_leftLim
-/
theorem rightLim_le (h : x < y) : rightLim f x <= f y :=
  hf.dual.le_leftLim h

@[gcongr, mono]
/--
theorem `rightLim` / 定理 `rightLim`

English:
theorem rightLim
  statement: Monotone (rightLim f)
  proof: fun _ _ h => hf.dual.leftLim h

中文:
定理 rightLim
  结论: 递增 (rightLim f)
  证明: fun _ _ h => hf.dual.leftLim h
-/
protected theorem rightLim : Monotone (rightLim f) := fun _ _ h => hf.dual.leftLim h

/--
theorem `leftLim_le_rightLim` / 定理 `leftLim_le_rightLim`

English:
theorem leftLim_le_rightLim
  given: (h : x <= y)
  statement: leftLim f x <= rightLim f y
  proof: (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)

中文:
定理 leftLim_le_rightLim
  条件: (h : x <= y)
  结论: leftLim f x <= rightLim f y
  证明: (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)

Depends on / 依赖: hf.le_rightLim, hf.leftLim_le, le_rfl, le_rightLim, leftLim_le
-/
theorem leftLim_le_rightLim (h : x <= y) : leftLim f x <= rightLim f y :=
  (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)

/--
theorem `rightLim_le_leftLim` / 定理 `rightLim_le_leftLim`

English:
theorem rightLim_le_leftLim
  given: (h : x < y)
  statement: rightLim f x <= leftLim f y
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with (h' | h')
  · simpa [leftLim, h'] using rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLim f x <= f a := hf.ri

中文:
定理 rightLim_le_leftLim
  条件: (h : x < y)
  结论: rightLim f x <= leftLim f y
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with (h' | h')
  · simpa [leftLim, h'] using rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLim f x <= f a := hf.ri

Depends on / 依赖: Ioo_mem_nhdsLT, Nonempty, OrderTopology, Preorder, Preorder.topology, TopologicalSpace, eq_or_neBot, hf.le_leftLim, hf.rightLim_le, le_leftLim, leftLim, nonempty_of_mem, rightLim, rightLim_le, topology
-/
theorem rightLim_le_leftLim (h : x < y) : rightLim f x <= leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with (h' | h')
  · simpa [leftLim, h'] using rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLim f x <= f a := hf.rightLim_le xa
    _ <= leftLim f y := hf.le_leftLim ay

variable [TopologicalSpace α] [OrderTopology α]

/--
theorem `tendsto_leftLim` / 定理 `tendsto_leftLim`

English:
theorem tendsto_leftLim
  given: (x : α)
  statement: Tendsto f (𝓝[<] x) (𝓝 (leftLim f x))
  proof: tendsto_leftLim_of_tendsto ⟨_, hf.tendsto_nhdsLT x⟩

中文:
定理 tendsto_leftLim
  条件: (x : α)
  结论: 收敛 f (𝓝[<] x) (𝓝 (leftLim f x))
  证明: tendsto_leftLim_of_tendsto ⟨_, hf.tendsto_nhdsLT x⟩

Depends on / 依赖: hf.tendsto_nhdsLT, tendsto_leftLim_of_tendsto, tendsto_nhdsLT
-/
theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  tendsto_leftLim_of_tendsto ⟨_, hf.tendsto_nhdsLT x⟩

/--
theorem `tendsto_leftLim_within` / 定理 `tendsto_leftLim_within`

English:
theorem tendsto_leftLim_within
  given: (x : α)
  statement: Tendsto f (𝓝[<] x) (𝓝[<=] leftLim f x)
  proof: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy

中文:
定理 tendsto_leftLim_within
  条件: (x : α)
  结论: 收敛 f (𝓝[<] x) (𝓝[<=] leftLim f x)
  证明: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy

Depends on / 依赖: filter_upwards, hf.le_leftLim, hf.tendsto_leftLim, le_leftLim, self_mem_nhdsWithin, tendsto_leftLim, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[<=] leftLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy

/--
theorem `tendsto_rightLim` / 定理 `tendsto_rightLim`

English:
theorem tendsto_rightLim
  given: (x : α)
  statement: Tendsto f (𝓝[>] x) (𝓝 (rightLim f x))
  proof: hf.dual.tendsto_leftLim x

中文:
定理 tendsto_rightLim
  条件: (x : α)
  结论: 收敛 f (𝓝[>] x) (𝓝 (rightLim f x))
  证明: hf.dual.tendsto_leftLim x

Depends on / 依赖: hf.dual.tendsto_leftLim, tendsto_leftLim
-/
theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual.tendsto_leftLim x

/--
theorem `tendsto_rightLim_within` / 定理 `tendsto_rightLim_within`

English:
theorem tendsto_rightLim_within
  given: (x : α)
  statement: Tendsto f (𝓝[>] x) (𝓝[>=] rightLim f x)
  proof: hf.dual.tendsto_leftLim_within x

中文:
定理 tendsto_rightLim_within
  条件: (x : α)
  结论: 收敛 f (𝓝[>] x) (𝓝[>=] rightLim f x)
  证明: hf.dual.tendsto_leftLim_within x

Depends on / 依赖: hf.dual.tendsto_leftLim_within, tendsto_leftLim_within
-/
theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[>=] rightLim f x) :=
  hf.dual.tendsto_leftLim_within x

/--
theorem `continuousWithinAt_Iio_iff_leftLim_eq` / 定理 `continuousWithinAt_Iio_iff_leftLim_eq`

English:
theorem continuousWithinAt_Iio_iff_leftLim_eq
  proof: by
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

中文:
定理 continuousWithinAt_Iio_iff_leftLim_eq
  证明: by
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

Depends on / 依赖: ContinuousWithinAt, eq_or_neBot, h.tendsto, hf.tendsto_leftLim, leftLim_eq_of_eq_bot, tendsto, tendsto_leftLim, tendsto_nhds_unique
-/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

/--
theorem `continuousWithinAt_Ioi_iff_rightLim_eq` / 定理 `continuousWithinAt_Ioi_iff_rightLim_eq`

English:
theorem continuousWithinAt_Ioi_iff_rightLim_eq
  proof: hf.dual.continuousWithinAt_Iio_iff_leftLim_eq

中文:
定理 continuousWithinAt_Ioi_iff_rightLim_eq
  证明: hf.dual.continuousWithinAt_Iio_iff_leftLim_eq

Depends on / 依赖: continuousWithinAt_Iio_iff_leftLim_eq, hf.dual.continuousWithinAt_Iio_iff_leftLim_eq
-/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLim_eq

/--
theorem `continuousAt_iff_leftLim_eq_rightLim` / 定理 `continuousAt_iff_leftLim_eq_rightLim`

English:
theorem continuousAt_iff_leftLim_eq_rightLim
  statement: ContinuousAt f x ↔ leftLim f x = rightLim f x
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x 

中文:
定理 continuousAt_iff_leftLim_eq_rightLim
  结论: ContinuousAt f x ↔ leftLim f x = rightLim f x
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x 

Depends on / 依赖: A.trans, B.symm, _right, continuousAt_iff_continuous_left, continuousWithinAt, continuousWithinAt_Iio_iff_leftLim_eq, continuousWithinAt_Ioi_iff_rightLim_eq, h.continuousWithinAt, hf.continuousWithinAt_Iio_iff_leftLim_eq, hf.continuousWithinAt_Ioi_iff_rightLim_eq, le_antisymm, le_refl, le_rightLim, leftLim, leftLim_le, rightLim
-/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x = f x := by
      apply le_antisymm (leftLim_le hf (le_refl _))
      rw [h]
      exact le_rightLim hf (le_refl _)
    refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
    · exact hf.continuousWithinAt_Iio_iff_leftLim_eq.2 h'
    · rw [h] at h'
      exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.2 h'

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α -> β} (hf : Antitone f) {x y : α}
include hf

/--
theorem `le_leftLim` / 定理 `le_leftLim`

English:
theorem le_leftLim
  given: (h : x <= y)
  statement: f y <= leftLim f x
  proof: hf.dual_right.leftLim_le h

中文:
定理 le_leftLim
  条件: (h : x <= y)
  结论: f y <= leftLim f x
  证明: hf.dual_right.leftLim_le h

Depends on / 依赖: dual_right, hf.dual_right.leftLim_le, leftLim_le
-/
theorem le_leftLim (h : x <= y) : f y <= leftLim f x :=
  hf.dual_right.leftLim_le h

/--
theorem `leftLim_le` / 定理 `leftLim_le`

English:
theorem leftLim_le
  given: (h : x < y)
  statement: leftLim f y <= f x
  proof: hf.dual_right.le_leftLim h

@[gcongr, mono]

中文:
定理 leftLim_le
  条件: (h : x < y)
  结论: leftLim f y <= f x
  证明: hf.dual_right.le_leftLim h

@[gcongr, mono]

Depends on / 依赖: dual_right, hf.dual_right.le_leftLim, le_leftLim
-/
theorem leftLim_le (h : x < y) : leftLim f y <= f x :=
  hf.dual_right.le_leftLim h

@[gcongr, mono]
/--
theorem `leftLim` / 定理 `leftLim`

English:
theorem leftLim
  statement: Antitone (leftLim f)
  proof: hf.dual_right.leftLim

中文:
定理 leftLim
  结论: 递减 (leftLim f)
  证明: hf.dual_right.leftLim
-/
protected theorem leftLim : Antitone (leftLim f) :=
  hf.dual_right.leftLim

/--
theorem `rightLim_le` / 定理 `rightLim_le`

English:
theorem rightLim_le
  given: (h : x <= y)
  statement: rightLim f y <= f x
  proof: hf.dual_right.le_rightLim h

中文:
定理 rightLim_le
  条件: (h : x <= y)
  结论: rightLim f y <= f x
  证明: hf.dual_right.le_rightLim h

Depends on / 依赖: dual_right, hf.dual_right.le_rightLim, le_rightLim
-/
theorem rightLim_le (h : x <= y) : rightLim f y <= f x :=
  hf.dual_right.le_rightLim h

/--
theorem `le_rightLim` / 定理 `le_rightLim`

English:
theorem le_rightLim
  given: (h : x < y)
  statement: f y <= rightLim f x
  proof: hf.dual_right.rightLim_le h

@[gcongr, mono]

中文:
定理 le_rightLim
  条件: (h : x < y)
  结论: f y <= rightLim f x
  证明: hf.dual_right.rightLim_le h

@[gcongr, mono]

Depends on / 依赖: dual_right, hf.dual_right.rightLim_le, rightLim_le
-/
theorem le_rightLim (h : x < y) : f y <= rightLim f x :=
  hf.dual_right.rightLim_le h

@[gcongr, mono]
/--
theorem `rightLim` / 定理 `rightLim`

English:
theorem rightLim
  statement: Antitone (rightLim f)
  proof: hf.dual_right.rightLim

中文:
定理 rightLim
  结论: 递减 (rightLim f)
  证明: hf.dual_right.rightLim
-/
protected theorem rightLim : Antitone (rightLim f) :=
  hf.dual_right.rightLim

/--
theorem `rightLim_le_leftLim` / 定理 `rightLim_le_leftLim`

English:
theorem rightLim_le_leftLim
  given: (h : x <= y)
  statement: rightLim f y <= leftLim f x
  proof: hf.dual_right.leftLim_le_rightLim h

中文:
定理 rightLim_le_leftLim
  条件: (h : x <= y)
  结论: rightLim f y <= leftLim f x
  证明: hf.dual_right.leftLim_le_rightLim h

Depends on / 依赖: dual_right, hf.dual_right.leftLim_le_rightLim, leftLim_le_rightLim
-/
theorem rightLim_le_leftLim (h : x <= y) : rightLim f y <= leftLim f x :=
  hf.dual_right.leftLim_le_rightLim h

/--
theorem `leftLim_le_rightLim` / 定理 `leftLim_le_rightLim`

English:
theorem leftLim_le_rightLim
  given: (h : x < y)
  statement: leftLim f y <= rightLim f x
  proof: hf.dual_right.rightLim_le_leftLim h

中文:
定理 leftLim_le_rightLim
  条件: (h : x < y)
  结论: leftLim f y <= rightLim f x
  证明: hf.dual_right.rightLim_le_leftLim h

Depends on / 依赖: dual_right, hf.dual_right.rightLim_le_leftLim, rightLim_le_leftLim
-/
theorem leftLim_le_rightLim (h : x < y) : leftLim f y <= rightLim f x :=
  hf.dual_right.rightLim_le_leftLim h

variable [TopologicalSpace α] [OrderTopology α]

/--
theorem `tendsto_leftLim` / 定理 `tendsto_leftLim`

English:
theorem tendsto_leftLim
  given: (x : α)
  statement: Tendsto f (𝓝[<] x) (𝓝 (leftLim f x))
  proof: hf.dual_right.tendsto_leftLim x

中文:
定理 tendsto_leftLim
  条件: (x : α)
  结论: 收敛 f (𝓝[<] x) (𝓝 (leftLim f x))
  证明: hf.dual_right.tendsto_leftLim x

Depends on / 依赖: dual_right, hf.dual_right.tendsto_leftLim, tendsto_leftLim
-/
theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  hf.dual_right.tendsto_leftLim x

/--
theorem `tendsto_leftLim_within` / 定理 `tendsto_leftLim_within`

English:
theorem tendsto_leftLim_within
  given: (x : α)
  statement: Tendsto f (𝓝[<] x) (𝓝[>=] leftLim f x)
  proof: hf.dual_right.tendsto_leftLim_within x

中文:
定理 tendsto_leftLim_within
  条件: (x : α)
  结论: 收敛 f (𝓝[<] x) (𝓝[>=] leftLim f x)
  证明: hf.dual_right.tendsto_leftLim_within x

Depends on / 依赖: dual_right, hf.dual_right.tendsto_leftLim_within, tendsto_leftLim_within
-/
theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[>=] leftLim f x) :=
  hf.dual_right.tendsto_leftLim_within x

/--
theorem `tendsto_rightLim` / 定理 `tendsto_rightLim`

English:
theorem tendsto_rightLim
  given: (x : α)
  statement: Tendsto f (𝓝[>] x) (𝓝 (rightLim f x))
  proof: hf.dual_right.tendsto_rightLim x

中文:
定理 tendsto_rightLim
  条件: (x : α)
  结论: 收敛 f (𝓝[>] x) (𝓝 (rightLim f x))
  证明: hf.dual_right.tendsto_rightLim x

Depends on / 依赖: dual_right, hf.dual_right.tendsto_rightLim, tendsto_rightLim
-/
theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual_right.tendsto_rightLim x

/--
theorem `tendsto_rightLim_within` / 定理 `tendsto_rightLim_within`

English:
theorem tendsto_rightLim_within
  given: (x : α)
  statement: Tendsto f (𝓝[>] x) (𝓝[<=] rightLim f x)
  proof: hf.dual_right.tendsto_rightLim_within x

中文:
定理 tendsto_rightLim_within
  条件: (x : α)
  结论: 收敛 f (𝓝[>] x) (𝓝[<=] rightLim f x)
  证明: hf.dual_right.tendsto_rightLim_within x

Depends on / 依赖: dual_right, hf.dual_right.tendsto_rightLim_within, tendsto_rightLim_within
-/
theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[<=] rightLim f x) :=
  hf.dual_right.tendsto_rightLim_within x

/--
theorem `continuousWithinAt_Iio_iff_leftLim_eq` / 定理 `continuousWithinAt_Iio_iff_leftLim_eq`

English:
theorem continuousWithinAt_Iio_iff_leftLim_eq
  proof: hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq

中文:
定理 continuousWithinAt_Iio_iff_leftLim_eq
  证明: hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq

Depends on / 依赖: continuousWithinAt_Iio_iff_leftLim_eq, dual_right, hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq
-/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq

/--
theorem `continuousWithinAt_Ioi_iff_rightLim_eq` / 定理 `continuousWithinAt_Ioi_iff_rightLim_eq`

English:
theorem continuousWithinAt_Ioi_iff_rightLim_eq
  proof: hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq

中文:
定理 continuousWithinAt_Ioi_iff_rightLim_eq
  证明: hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq

Depends on / 依赖: continuousWithinAt_Ioi_iff_rightLim_eq, dual_right, hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq
-/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq

/--
theorem `continuousAt_iff_leftLim_eq_rightLim` / 定理 `continuousAt_iff_leftLim_eq_rightLim`

English:
theorem continuousAt_iff_leftLim_eq_rightLim
  statement: ContinuousAt f x ↔ leftLim f x = rightLim f x
  proof: hf.dual_right.continuousAt_iff_leftLim_eq_rightLim

中文:
定理 continuousAt_iff_leftLim_eq_rightLim
  结论: ContinuousAt f x ↔ leftLim f x = rightLim f x
  证明: hf.dual_right.continuousAt_iff_leftLim_eq_rightLim

Depends on / 依赖: continuousAt_iff_leftLim_eq_rightLim, dual_right, hf.dual_right.continuousAt_iff_leftLim_eq_rightLim
-/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x :=
  hf.dual_right.continuousAt_iff_leftLim_eq_rightLim

end Antitone
