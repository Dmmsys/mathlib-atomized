/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Regular

/-!
# Dense embeddings

This file defines three properties of functions:

* `DenseRange f` means `f` has dense image;
* `IsDenseInducing i` means `i` is also inducing, namely it induces the topology on its codomain;
* `IsDenseEmbedding e` means `e` is further an embedding, namely it is injective and `Inducing`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a T₃ space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `IsDenseInducing` (not necessarily injective).

-/

@[expose] public section


noncomputable section

open Filter Set Topology

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/--
Definition of `IsDenseInducing` / `IsDenseInducing` 的定义

English:
structure IsDenseInducing
  parameters: [TopologicalSpace α] [TopologicalSpace β] (i : α -> β)
  extends: IsInducing i
  axioms and operations (1):
    - dense : DenseRange i

中文:
结构 是DenseInducing
  参数: [拓扑空间 α] [拓扑空间 β] (i : α -> β)
  继承: 是Inducing i
  公理与运算 (1 个):
    - dense : DenseRange i
-/
structure IsDenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α -> β) : Prop
    extends IsInducing i where
  /-- The range of a dense inducing map is a dense set. -/
  protected dense : DenseRange i

namespace IsDenseInducing

variable [TopologicalSpace α] [TopologicalSpace β]

/--
theorem `_root_.Dense.isDenseInducing_val` / 定理 `_root_.Dense.isDenseInducing_val`

English:
theorem _root_.Dense.isDenseInducing_val
  given: {s : Set α} (hs : Dense s)
  proof: ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

中文:
定理 _root_.稠密.isDenseInducing_val
  条件: {s : 集合 α} (hs : 稠密 s)
  证明: ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

Depends on / 依赖: IsInducing, IsInducing.subtypeVal, denseRange_val, hs.denseRange_val, subtypeVal
-/
theorem _root_.Dense.isDenseInducing_val {s : Set α} (hs : Dense s) :
    IsDenseInducing ((↑) : s -> α) := ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

variable {i : α -> β}

/--
lemma `isInducing` / 引理 `isInducing`

English:
lemma isInducing
  given: (di : IsDenseInducing i)
  statement: IsInducing i
  proof: di.toIsInducing

中文:
引理 isInducing
  条件: (di : 是DenseInducing i)
  结论: 是Inducing i
  证明: di.toIsInducing

Depends on / 依赖: di.toIsInducing, toIsInducing
-/
lemma isInducing (di : IsDenseInducing i) : IsInducing i := di.toIsInducing

/--
theorem `nhds_eq_comap` / 定理 `nhds_eq_comap`

English:
theorem nhds_eq_comap
  given: (di : IsDenseInducing i)
  statement: forall a : α, 𝓝 a = comap i (𝓝 <| i a)
  proof: di.isInducing.nhds_eq_comap

中文:
定理 nhds_eq_comap
  条件: (di : 是DenseInducing i)
  结论: 对任意 a : α, 𝓝 a = comap i (𝓝 <| i a)
  证明: di.isInducing.nhds_eq_comap

Depends on / 依赖: di.isInducing.nhds_eq_comap, isInducing, nhds_eq_comap
-/
theorem nhds_eq_comap (di : IsDenseInducing i) : forall a : α, 𝓝 a = comap i (𝓝 <| i a) :=
  di.isInducing.nhds_eq_comap

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (di : IsDenseInducing i)
  statement: Continuous i
  proof: di.isInducing.continuous

中文:
定理 continuous
  条件: (di : 是DenseInducing i)
  结论: 连续 i
  证明: di.isInducing.continuous
-/
protected theorem continuous (di : IsDenseInducing i) : Continuous i :=
  di.isInducing.continuous

/--
theorem `closure_range` / 定理 `closure_range`

English:
theorem closure_range
  given: (di : IsDenseInducing i)
  statement: closure (range i) = univ
  proof: di.dense.closure_range

中文:
定理 closure_range
  条件: (di : 是DenseInducing i)
  结论: closure (range i) = univ
  证明: di.dense.closure_range

Depends on / 依赖: closure_range, di.dense.closure_range
-/
theorem closure_range (di : IsDenseInducing i) : closure (range i) = univ :=
  di.dense.closure_range

/--
theorem `preconnectedSpace` / 定理 `preconnectedSpace`

English:
theorem preconnectedSpace
  given: [PreconnectedSpace α] (di : IsDenseInducing i)
  proof: di.dense.preconnectedSpace di.continuous

中文:
定理 preconnectedSpace
  条件: [预连通空间 α] (di : 是DenseInducing i)
  证明: di.dense.preconnectedSpace di.continuous
-/
protected theorem preconnectedSpace [PreconnectedSpace α] (di : IsDenseInducing i) :
    PreconnectedSpace β :=
  di.dense.preconnectedSpace di.continuous

/--
theorem `closure_image_mem_nhds` / 定理 `closure_image_mem_nhds`

English:
theorem closure_image_mem_nhds
  given: {s : Set α} {a : α} (di : IsDenseInducing i) (hs : s in 𝓝 a)
  proof: by
  rw [di.nhds_eq_comap a]; rw [((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U subseteq s⟩
  refine mem_of_superset (hUo.mem_nhds haU) ?_
  calc
    U subseteq closure (i '' i ⁻¹' U) := di.dense.subset_closure_image_preimage_of_isOpen hUo
    _ subsete

中文:
定理 closure_image_mem_nhds
  条件: {s : 集合 α} {a : α} (di : 是DenseInducing i) (hs : s in 𝓝 a)
  证明: by
  rw [di.nhds_eq_comap a]; rw [((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U subseteq s⟩
  refine mem_of_superset (hUo.mem_nhds haU) ?_
  calc
    U subseteq closure (i '' i ⁻¹' U) := di.dense.subset_closure_image_preimage_of_isOpen hUo
    _ subsete

Depends on / 依赖: closure, closure_mono, di.dense.subset_closure_image_preimage_of_isOpen, di.nhds_eq_comap, hUo.mem_nhds, image_mono, mem_iff, mem_nhds, mem_of_superset, nhds_basis_opens, nhds_eq_comap, subset_closure_image_preimage_of_isOpen, subseteq
-/
theorem closure_image_mem_nhds {s : Set α} {a : α} (di : IsDenseInducing i) (hs : s in 𝓝 a) :
    closure (i '' s) in 𝓝 (i a) := by
  rw [di.nhds_eq_comap a]; rw [((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U subseteq s⟩
  refine mem_of_superset (hUo.mem_nhds haU) ?_
  calc
    U subseteq closure (i '' i ⁻¹' U) := di.dense.subset_closure_image_preimage_of_isOpen hUo
    _ subseteq closure (i '' s) := closure_mono (image_mono sub)

/--
theorem `dense_image` / 定理 `dense_image`

English:
theorem dense_image
  given: (di : IsDenseInducing i) {s : Set α}
  statement: Dense (i '' s) ↔ Dense s
  proof: by
  refine ⟨fun H x => ?_, di.dense.dense_image di.continuous⟩
  rw [di.isInducing.closure_eq_preimage_closure_image]; rw [H.closure_eq]; rw [preimage_univ]
  trivial

中文:
定理 dense_image
  条件: (di : 是DenseInducing i) {s : 集合 α}
  结论: 稠密 (i '' s) ↔ 稠密 s
  证明: by
  refine ⟨fun H x => ?_, di.dense.dense_image di.continuous⟩
  rw [di.isInducing.closure_eq_preimage_closure_image]; rw [H.closure_eq]; rw [preimage_univ]
  trivial

Depends on / 依赖: H.closure_eq, closure_eq, closure_eq_preimage_closure_image, continuous, dense_image, di.continuous, di.dense.dense_image, di.isInducing.closure_eq_preimage_closure_image, isInducing, preimage_univ
-/
theorem dense_image (di : IsDenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense s := by
  refine ⟨fun H x => ?_, di.dense.dense_image di.continuous⟩
  rw [di.isInducing.closure_eq_preimage_closure_image]; rw [H.closure_eq]; rw [preimage_univ]
  trivial

/--
theorem `interior_compact_eq_empty` / 定理 `interior_compact_eq_empty`

English:
theorem interior_compact_eq_empty
  statement: [T2Space β] (di : IsDenseInducing i) (hd : Dense (range i)ᶜ)
  proof: by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).isClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

中文:
定理 interior_compact_eq_empty
  结论: [T2空间 β] (di : 是DenseInducing i) (hd : 稠密 (range i)ᶜ)
  证明: by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).isClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

Depends on / 依赖: closure_eq, closure_image_mem_nhds, continuous, di.closure_image_mem_nhds, di.continuous, eq_empty_iff_forall_notMem, hd.inter_nhds_nonempty, hs.image, image_subset_range, inter_nhds_nonempty, isClosed, isClosed.closure_eq, mem_interior_iff_mem_nhds
-/
theorem interior_compact_eq_empty [T2Space β] (di : IsDenseInducing i) (hd : Dense (range i)ᶜ)
    {s : Set α} (hs : IsCompact s) : interior s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).isClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α -> β} {e₂ : γ -> δ}
  proof: de₁.isInducing.prodMap de₂.isInducing
  dense := de₁.dense.prodMap de₂.dense

中文:
定理 prodMap
  结论: [拓扑空间 γ] [拓扑空间 δ] {e₁ : α -> β} {e₂ : γ -> δ}
  证明: de₁.isInducing.prodMap de₂.isInducing
  dense := de₁.dense.prodMap de₂.dense
-/
protected theorem prodMap [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α -> β} {e₂ : γ -> δ}
    (de₁ : IsDenseInducing e₁) (de₂ : IsDenseInducing e₂) :
    IsDenseInducing (Prod.map e₁ e₂) where
  toIsInducing := de₁.isInducing.prodMap de₂.isInducing
  dense := de₁.dense.prodMap de₂.dense

open TopologicalSpace

/--
theorem `separableSpace` / 定理 `separableSpace`

English:
theorem separableSpace
  given: [SeparableSpace α] (di : IsDenseInducing i)
  statement: SeparableSpace β
  proof: di.dense.separableSpace di.continuous

中文:
定理 separableSpace
  条件: [可分空间 α] (di : 是DenseInducing i)
  结论: 可分空间 β
  证明: di.dense.separableSpace di.continuous
-/
protected theorem separableSpace [SeparableSpace α] (di : IsDenseInducing i) : SeparableSpace β :=
  di.dense.separableSpace di.continuous

variable [TopologicalSpace δ] {f : γ -> α} {g : γ -> δ} {h : δ -> β}

/--
theorem `tendsto_comap_nhds_nhds` / 定理 `tendsto_comap_nhds_nhds`

English:
theorem tendsto_comap_nhds_nhds
  statement: {d : δ} {a : α} (di : IsDenseInducing i)
  proof: by
  have lim1 : map g (comap g (𝓝 d)) <= 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) <= map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map]; rw [comm]; rw [← Filter.map_map]; rw [map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) <= comap i (𝓝 (i a)) := comap_mon

中文:
定理 tendsto_comap_nhds_nhds
  结论: {d : δ} {a : α} (di : 是DenseInducing i)
  证明: by
  have lim1 : map g (comap g (𝓝 d)) <= 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) <= map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map]; rw [comm]; rw [← Filter.map_map]; rw [map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) <= comap i (𝓝 (i a)) := comap_mon

Depends on / 依赖: Filter, Filter.map_map, comap_mono, di.nhds_eq_comap, le_trans, map_comap_le, map_le_iff_le_comap, map_map, map_mono, nhds_eq_comap, replace
-/
theorem tendsto_comap_nhds_nhds {d : δ} {a : α} (di : IsDenseInducing i)
    (H : Tendsto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a) := by
  have lim1 : map g (comap g (𝓝 d)) <= 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) <= map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map]; rw [comm]; rw [← Filter.map_map]; rw [map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) <= comap i (𝓝 (i a)) := comap_mono H
  rw [← di.nhds_eq_comap] at lim2
  exact le_trans lim1 lim2

/--
theorem `nhdsWithin_neBot` / 定理 `nhdsWithin_neBot`

English:
theorem nhdsWithin_neBot
  given: (di : IsDenseInducing i) (b : β)
  statement: NeBot (𝓝[range i] b)
  proof: di.dense.nhdsWithin_neBot b

中文:
定理 nhdsWithin_neBot
  条件: (di : 是DenseInducing i) (b : β)
  结论: NeBot (𝓝[range i] b)
  证明: di.dense.nhdsWithin_neBot b
-/
protected theorem nhdsWithin_neBot (di : IsDenseInducing i) (b : β) : NeBot (𝓝[range i] b) :=
  di.dense.nhdsWithin_neBot b

/--
theorem `comap_nhds_neBot` / 定理 `comap_nhds_neBot`

English:
theorem comap_nhds_neBot
  given: (di : IsDenseInducing i) (b : β)
  statement: NeBot (comap i (𝓝 b))
  proof: comap_neBot fun s hs => by
    rcases mem_closure_iff_nhds.1 (di.dense b) s hs with ⟨_, ⟨ha, a, rfl⟩⟩
    exact ⟨a, ha⟩

中文:
定理 comap_nhds_neBot
  条件: (di : 是DenseInducing i) (b : β)
  结论: NeBot (comap i (𝓝 b))
  证明: comap_neBot fun s hs => by
    rcases mem_closure_iff_nhds.1 (di.dense b) s hs with ⟨_, ⟨ha, a, rfl⟩⟩
    exact ⟨a, ha⟩

Depends on / 依赖: comap_neBot, di.dense, mem_closure_iff_nhds
-/
theorem comap_nhds_neBot (di : IsDenseInducing i) (b : β) : NeBot (comap i (𝓝 b)) :=
  comap_neBot fun s hs => by
    rcases mem_closure_iff_nhds.1 (di.dense b) s hs with ⟨_, ⟨ha, a, rfl⟩⟩
    exact ⟨a, ha⟩

/--
theorem `_root_.Dense.comap_val_nhds_neBot` / 定理 `_root_.Dense.comap_val_nhds_neBot`

English:
theorem _root_.Dense.comap_val_nhds_neBot
  given: {s : Set α} (hs : Dense s) (a : α)
  proof: hs.isDenseInducing_val.comap_nhds_neBot _

中文:
定理 _root_.稠密.comap_val_nhds_neBot
  条件: {s : 集合 α} (hs : 稠密 s) (a : α)
  证明: hs.isDenseInducing_val.comap_nhds_neBot _

Depends on / 依赖: comap_nhds_neBot, hs.isDenseInducing_val.comap_nhds_neBot, isDenseInducing_val
-/
theorem _root_.Dense.comap_val_nhds_neBot {s : Set α} (hs : Dense s) (a : α) :
    ((𝓝 a).comap ((↑) : s -> α)).NeBot :=
  hs.isDenseInducing_val.comap_nhds_neBot _

variable [TopologicalSpace γ]

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (di : IsDenseInducing i) (f : α -> γ) (b : β)
  body: @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

中文:
定义 extend
  签名: (di : 是DenseInducing i) (f : α -> γ) (b : β)
  定义体: @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

Depends on / 依赖: di.dense.some, limUnder
-/
def extend (di : IsDenseInducing i) (f : α -> γ) (b : β) : γ :=
  @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

/--
theorem `tendsto_extend` / 定理 `tendsto_extend`

English:
theorem tendsto_extend
  given: (di : IsDenseInducing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a)
  proof: by
  rw [IsDenseInducing.extend]; rw [← di.nhds_eq_comap]
  exact tendsto_nhds_limUnder ⟨_, hf⟩

中文:
定理 tendsto_extend
  条件: (di : 是DenseInducing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a)
  证明: by
  rw [IsDenseInducing.extend]; rw [← di.nhds_eq_comap]
  exact tendsto_nhds_limUnder ⟨_, hf⟩

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend, di.nhds_eq_comap, extend, nhds_eq_comap, tendsto_nhds_limUnder
-/
theorem tendsto_extend (di : IsDenseInducing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) :
    Tendsto f (𝓝 a) (𝓝 (di.extend f (i a))) := by
  rw [IsDenseInducing.extend]; rw [← di.nhds_eq_comap]
  exact tendsto_nhds_limUnder ⟨_, hf⟩

/--
theorem `inseparable_extend` / 定理 `inseparable_extend`

English:
theorem inseparable_extend
  statement: [R1Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α}
  proof: tendsto_nhds_unique_inseparable (di.tendsto_extend hf) hf

中文:
定理 inseparable_extend
  结论: [R1空间 γ] (di : 是DenseInducing i) {f : α -> γ} {a : α}
  证明: tendsto_nhds_unique_inseparable (di.tendsto_extend hf) hf

Depends on / 依赖: di.tendsto_extend, tendsto_extend, tendsto_nhds_unique_inseparable
-/
theorem inseparable_extend [R1Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α}
    (hf : ContinuousAt f a) : Inseparable (di.extend f (i a)) (f a) :=
  tendsto_nhds_unique_inseparable (di.tendsto_extend hf) hf

/--
theorem `extend_eq_of_tendsto` / 定理 `extend_eq_of_tendsto`

English:
theorem extend_eq_of_tendsto
  statement: [T2Space γ] (di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ}
  proof: haveI := di.comap_nhds_neBot
  hf.limUnder_eq

中文:
定理 extend_eq_of_tendsto
  结论: [T2空间 γ] (di : 是DenseInducing i) {b : β} {c : γ} {f : α -> γ}
  证明: haveI := di.comap_nhds_neBot
  hf.limUnder_eq

Depends on / 依赖: comap_nhds_neBot, di.comap_nhds_neBot, hf.limUnder_eq, limUnder_eq
-/
theorem extend_eq_of_tendsto [T2Space γ] (di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ}
    (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) : di.extend f b = c :=
  haveI := di.comap_nhds_neBot
  hf.limUnder_eq

/--
theorem `extend_eq_at` / 定理 `extend_eq_at`

English:
theorem extend_eq_at
  statement: [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α}
  proof: extend_eq_of_tendsto _ di.nhds_eq_comap a ▸ hf

中文:
定理 extend_eq_at
  结论: [T2空间 γ] (di : 是DenseInducing i) {f : α -> γ} {a : α}
  证明: extend_eq_of_tendsto _ di.nhds_eq_comap a ▸ hf

Depends on / 依赖: di.nhds_eq_comap, extend_eq_of_tendsto, nhds_eq_comap
-/
theorem extend_eq_at [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α}
    (hf : ContinuousAt f a) : di.extend f (i a) = f a :=
extend_eq_of_tendsto _ di.nhds_eq_comap a ▸ hf

/--
theorem `extend_eq_at'` / 定理 `extend_eq_at'`

English:
theorem extend_eq_at'
  statement: [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α} (c : γ)
  proof: di.extend_eq_at (continuousAt_of_tendsto_nhds hf)

中文:
定理 extend_eq_at'
  结论: [T2空间 γ] (di : 是DenseInducing i) {f : α -> γ} {a : α} (c : γ)
  证明: di.extend_eq_at (continuousAt_of_tendsto_nhds hf)

Depends on / 依赖: continuousAt_of_tendsto_nhds, di.extend_eq_at, extend_eq_at
-/
theorem extend_eq_at' [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α} (c : γ)
    (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend f (i a) = f a :=
  di.extend_eq_at (continuousAt_of_tendsto_nhds hf)

/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  given: [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} (hf : Continuous f) (a : α)
  proof: di.extend_eq_at hf.continuousAt

中文:
定理 extend_eq
  条件: [T2空间 γ] (di : 是DenseInducing i) {f : α -> γ} (hf : 连续 f) (a : α)
  证明: di.extend_eq_at hf.continuousAt

Depends on / 依赖: continuousAt, di.extend_eq_at, extend_eq_at, hf.continuousAt
-/
theorem extend_eq [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} (hf : Continuous f) (a : α) :
    di.extend f (i a) = f a :=
  di.extend_eq_at hf.continuousAt

/--
theorem `extend_eq'` / 定理 `extend_eq'`

English:
theorem extend_eq'
  statement: [T2Space γ] {f : α -> γ} (di : IsDenseInducing i)
  proof: by
  rcases hf (i a) with ⟨b, hb⟩
  refine di.extend_eq_at' b ?_
  rwa [← di.isInducing.nhds_eq_comap] at hb

中文:
定理 extend_eq'
  结论: [T2空间 γ] {f : α -> γ} (di : 是DenseInducing i)
  证明: by
  rcases hf (i a) with ⟨b, hb⟩
  refine di.extend_eq_at' b ?_
  rwa [← di.isInducing.nhds_eq_comap] at hb

Depends on / 依赖: di.extend_eq_at, di.isInducing.nhds_eq_comap, extend_eq_at, isInducing, nhds_eq_comap
-/
theorem extend_eq' [T2Space γ] {f : α -> γ} (di : IsDenseInducing i)
    (hf : forall b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) (a : α) : di.extend f (i a) = f a := by
  rcases hf (i a) with ⟨b, hb⟩
  refine di.extend_eq_at' b ?_
  rwa [← di.isInducing.nhds_eq_comap] at hb

/--
theorem `extend_unique_at` / 定理 `extend_unique_at`

English:
theorem extend_unique_at
  statement: [T2Space γ] {b : β} {f : α -> γ} {g : β -> γ} (di : IsDenseInducing i)
  proof: by
  refine di.extend_eq_of_tendsto fun s hs => mem_map.2 ?_
  suffices forallᶠ x : α in comap i (𝓝 b), g (i x) in s from
    hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine eventually_comap.2 ((hg.eventually hs).mono ?_)
  rintro _ hxs x rfl
  exact hxs

中文:
定理 extend_unique_at
  结论: [T2空间 γ] {b : β} {f : α -> γ} {g : β -> γ} (di : 是DenseInducing i)
  证明: by
  refine di.extend_eq_of_tendsto fun s hs => mem_map.2 ?_
  suffices forallᶠ x : α in comap i (𝓝 b), g (i x) in s from
    hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine eventually_comap.2 ((hg.eventually hs).mono ?_)
  rintro _ hxs x rfl
  exact hxs

Depends on / 依赖: di.extend_eq_of_tendsto, eventually, eventually_comap, extend_eq_of_tendsto, hf.mp, hg.eventually, mem_map, this.mono
-/
theorem extend_unique_at [T2Space γ] {b : β} {f : α -> γ} {g : β -> γ} (di : IsDenseInducing i)
    (hf : forallᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousAt g b) : di.extend f b = g b := by
  refine di.extend_eq_of_tendsto fun s hs => mem_map.2 ?_
  suffices forallᶠ x : α in comap i (𝓝 b), g (i x) in s from
    hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine eventually_comap.2 ((hg.eventually hs).mono ?_)
  rintro _ hxs x rfl
  exact hxs

/--
theorem `extend_unique` / 定理 `extend_unique`

English:
theorem extend_unique
  statement: [T2Space γ] {f : α -> γ} {g : β -> γ} (di : IsDenseInducing i)
  proof: funext fun _ => extend_unique_at di (Eventually.of_forall hf) hg.continuousAt

中文:
定理 extend_unique
  结论: [T2空间 γ] {f : α -> γ} {g : β -> γ} (di : 是DenseInducing i)
  证明: funext fun _ => extend_unique_at di (Eventually.of_forall hf) hg.continuousAt

Depends on / 依赖: Eventually, Eventually.of_forall, continuousAt, extend_unique_at, hg.continuousAt, of_forall
-/
theorem extend_unique [T2Space γ] {f : α -> γ} {g : β -> γ} (di : IsDenseInducing i)
    (hf : forall x, g (i x) = f x) (hg : Continuous g) : di.extend f = g :=
  funext fun _ => extend_unique_at di (Eventually.of_forall hf) hg.continuousAt

/--
theorem `continuousAt_extend` / 定理 `continuousAt_extend`

English:
theorem continuousAt_extend
  statement: [T3Space γ] {b : β} {f : α -> γ} (di : IsDenseInducing i)
  proof: by
  set φ := di.extend f
  have := di.comap_nhds_neBot
  suffices forall V' in 𝓝 (φ b), IsClosed V' -> φ ⁻¹' V' in 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis (φ b)).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | Tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ in 𝓝

中文:
定理 continuousAt_extend
  结论: [T3空间 γ] {b : β} {f : α -> γ} (di : 是DenseInducing i)
  证明: by
  set φ := di.extend f
  have := di.comap_nhds_neBot
  suffices forall V' in 𝓝 (φ b), IsClosed V' -> φ ⁻¹' V' in 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis (φ b)).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | Tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ in 𝓝

Depends on / 依赖: ContinuousAt, IsClosed, IsOpen, Tendsto, _closed, and_assoc, closed_nhds_basis, comap_nhds_neBot, di.comap_nhds_neBot, di.extend, di.extend_eq_of_tendsto, extend, extend_eq_of_tendsto, filter_upwards, tendsto_right_iff
-/
theorem continuousAt_extend [T3Space γ] {b : β} {f : α -> γ} (di : IsDenseInducing i)
    (hf : forallᶠ x in 𝓝 b, exists c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : ContinuousAt (di.extend f) b := by
  set φ := di.extend f
  have := di.comap_nhds_neBot
  suffices forall V' in 𝓝 (φ b), IsClosed V' -> φ ⁻¹' V' in 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis (φ b)).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | Tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ in 𝓝 b := by
    filter_upwards [hf]
    rintro x ⟨c, hc⟩
    rwa [← di.extend_eq_of_tendsto hc] at hc
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : exists V₂ in 𝓝 b, IsOpen V₂ ∧ forall x in i ⁻¹' V₂, f x in V' := by
    simpa [and_assoc] using!
      ((nhds_basis_opens' b).comap i).tendsto_left_iff.mp (mem_of_mem_nhds V₁_in : b in V₁) V' V'_in
  suffices forall x in V₁ inter V₂, φ x in V' by filter_upwards [inter_mem V₁_in V₂_in] using this
  rintro x ⟨x_in₁, x_in₂⟩
  have hV₂x : V₂ in 𝓝 x := IsOpen.mem_nhds V₂_op x_in₂
  apply V'_closed.mem_of_tendsto x_in₁
  use V₂
  tauto

/--
theorem `continuous_extend` / 定理 `continuous_extend`

English:
theorem continuous_extend
  statement: [T3Space γ] {f : α -> γ} (di : IsDenseInducing i)
  proof: continuous_iff_continuousAt.mpr fun _ => di.continuousAt_extend univ_mem' hf

中文:
定理 continuous_extend
  结论: [T3空间 γ] {f : α -> γ} (di : 是DenseInducing i)
  证明: continuous_iff_continuousAt.mpr fun _ => di.continuousAt_extend univ_mem' hf

Depends on / 依赖: continuousAt_extend, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, di.continuousAt_extend, univ_mem
-/
theorem continuous_extend [T3Space γ] {f : α -> γ} (di : IsDenseInducing i)
    (hf : forall b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f) :=
continuous_iff_continuousAt.mpr fun _ => di.continuousAt_extend univ_mem' hf

/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  statement: (i : α -> β) (c : Continuous i) (dense : forall x, x in closure (range i))
  proof: isInducing_iff_nhds.2 fun a =>
      le_antisymm (c.tendsto _).le_comap (by simpa [Filter.le_def] using! H a)
  dense := dense

中文:
定理 mk'
  结论: (i : α -> β) (c : 连续 i) (dense : 对任意 x, x in closure (range i))
  证明: isInducing_iff_nhds.2 fun a =>
      le_antisymm (c.tendsto _).le_comap (by simpa [Filter.le_def] using! H a)
  dense := dense

Depends on / 依赖: isInducing_iff_nhds
-/
theorem mk' (i : α -> β) (c : Continuous i) (dense : forall x, x in closure (range i))
    (H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 (i a), forall b, i b in t -> b in s) : IsDenseInducing i where
  toIsInducing := isInducing_iff_nhds.2 fun a =>
      le_antisymm (c.tendsto _).le_comap (by simpa [Filter.le_def] using! H a)
  dense := dense

end IsDenseInducing

namespace Dense

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α}

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (hs : Dense s) (f : s -> β)
  body: hs.isDenseInducing_val.extend f

中文:
定义 extend
  签名: (hs : 稠密 s) (f : s -> β)
  定义体: hs.isDenseInducing_val.extend f

Depends on / 依赖: extend, hs.isDenseInducing_val.extend, isDenseInducing_val
-/
noncomputable def extend (hs : Dense s) (f : s -> β) : α -> β :=
    hs.isDenseInducing_val.extend f

variable {f : s -> β}

/--
theorem `extend_eq_of_tendsto` / 定理 `extend_eq_of_tendsto`

English:
theorem extend_eq_of_tendsto
  statement: [T2Space β] (hs : Dense s) {a : α} {b : β}
  proof: hs.isDenseInducing_val.extend_eq_of_tendsto hf

中文:
定理 extend_eq_of_tendsto
  结论: [T2空间 β] (hs : 稠密 s) {a : α} {b : β}
  证明: hs.isDenseInducing_val.extend_eq_of_tendsto hf

Depends on / 依赖: extend_eq_of_tendsto, hs.isDenseInducing_val.extend_eq_of_tendsto, isDenseInducing_val
-/
theorem extend_eq_of_tendsto [T2Space β] (hs : Dense s) {a : α} {b : β}
    (hf : Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : hs.extend f a = b :=
  hs.isDenseInducing_val.extend_eq_of_tendsto hf

/--
theorem `extend_eq_at` / 定理 `extend_eq_at`

English:
theorem extend_eq_at
  statement: [T2Space β] (hs : Dense s) {f : s -> β} {x : s}
  proof: hs.isDenseInducing_val.extend_eq_at hf

中文:
定理 extend_eq_at
  结论: [T2空间 β] (hs : 稠密 s) {f : s -> β} {x : s}
  证明: hs.isDenseInducing_val.extend_eq_at hf

Depends on / 依赖: extend_eq_at, hs.isDenseInducing_val.extend_eq_at, isDenseInducing_val
-/
theorem extend_eq_at [T2Space β] (hs : Dense s) {f : s -> β} {x : s}
    (hf : ContinuousAt f x) : hs.extend f x = f x :=
  hs.isDenseInducing_val.extend_eq_at hf

/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  given: [T2Space β] (hs : Dense s) (hf : Continuous f) (x : s)
  proof: hs.extend_eq_at hf.continuousAt

中文:
定理 extend_eq
  条件: [T2空间 β] (hs : 稠密 s) (hf : 连续 f) (x : s)
  证明: hs.extend_eq_at hf.continuousAt

Depends on / 依赖: continuousAt, extend_eq_at, hf.continuousAt, hs.extend_eq_at
-/
theorem extend_eq [T2Space β] (hs : Dense s) (hf : Continuous f) (x : s) :
    hs.extend f x = f x :=
  hs.extend_eq_at hf.continuousAt

/--
theorem `extend_unique_at` / 定理 `extend_unique_at`

English:
theorem extend_unique_at
  statement: [T2Space β] {a : α} {g : α -> β} (hs : Dense s)
  proof: hs.isDenseInducing_val.extend_unique_at hf hg

中文:
定理 extend_unique_at
  结论: [T2空间 β] {a : α} {g : α -> β} (hs : 稠密 s)
  证明: hs.isDenseInducing_val.extend_unique_at hf hg

Depends on / 依赖: extend_unique_at, hs.isDenseInducing_val.extend_unique_at, isDenseInducing_val
-/
theorem extend_unique_at [T2Space β] {a : α} {g : α -> β} (hs : Dense s)
    (hf : forallᶠ x : s in comap (↑) (𝓝 a), g x = f x) (hg : ContinuousAt g a) :
    hs.extend f a = g a :=
  hs.isDenseInducing_val.extend_unique_at hf hg

/--
theorem `extend_unique` / 定理 `extend_unique`

English:
theorem extend_unique
  statement: [T2Space β] {g : α -> β} (hs : Dense s)
  proof: hs.isDenseInducing_val.extend_unique hf hg

中文:
定理 extend_unique
  结论: [T2空间 β] {g : α -> β} (hs : 稠密 s)
  证明: hs.isDenseInducing_val.extend_unique hf hg

Depends on / 依赖: extend_unique, hs.isDenseInducing_val.extend_unique, isDenseInducing_val
-/
theorem extend_unique [T2Space β] {g : α -> β} (hs : Dense s)
    (hf : forall x : s, g x = f x) (hg : Continuous g) : hs.extend f = g :=
  hs.isDenseInducing_val.extend_unique hf hg

/--
theorem `continuousAt_extend` / 定理 `continuousAt_extend`

English:
theorem continuousAt_extend
  statement: [T3Space β] {a : α} (hs : Dense s)
  proof: hs.isDenseInducing_val.continuousAt_extend hf

中文:
定理 continuousAt_extend
  结论: [T3空间 β] {a : α} (hs : 稠密 s)
  证明: hs.isDenseInducing_val.continuousAt_extend hf

Depends on / 依赖: continuousAt_extend, hs.isDenseInducing_val.continuousAt_extend, isDenseInducing_val
-/
theorem continuousAt_extend [T3Space β] {a : α} (hs : Dense s)
    (hf : forallᶠ x in 𝓝 a, exists b, Tendsto f (comap (↑) <| 𝓝 x) (𝓝 b)) :
    ContinuousAt (hs.extend f) a :=
  hs.isDenseInducing_val.continuousAt_extend hf

/--
theorem `continuous_extend` / 定理 `continuous_extend`

English:
theorem continuous_extend
  statement: [T3Space β] (hs : Dense s)
  proof: hs.isDenseInducing_val.continuous_extend hf

中文:
定理 continuous_extend
  结论: [T3空间 β] (hs : 稠密 s)
  证明: hs.isDenseInducing_val.continuous_extend hf

Depends on / 依赖: continuous_extend, hs.isDenseInducing_val.continuous_extend, isDenseInducing_val
-/
theorem continuous_extend [T3Space β] (hs : Dense s)
    (hf : forall a : α, exists b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : Continuous (hs.extend f) :=
  hs.isDenseInducing_val.continuous_extend hf

end Dense

/--
Definition of `IsDenseEmbedding` / `IsDenseEmbedding` 的定义

English:
structure IsDenseEmbedding
  parameters: [TopologicalSpace α] [TopologicalSpace β] (e : α -> β)
  extends: IsDenseInducing e
  axioms and operations (1):
    - injective : Function.Injective e

中文:
结构 是稠密嵌入
  参数: [拓扑空间 α] [拓扑空间 β] (e : α -> β)
  继承: 是DenseInducing e
  公理与运算 (1 个):
    - injective : 函数.单射 e
-/
structure IsDenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α -> β) : Prop
    extends IsDenseInducing e where
  /-- A dense embedding is injective. -/
  injective : Function.Injective e

/--
lemma `IsDenseEmbedding.mk'` / 引理 `IsDenseEmbedding.mk'`

English:
lemma IsDenseEmbedding.mk'
  statement: [TopologicalSpace α] [TopologicalSpace β] (e : α -> β) (c : Continuous e)
  proof: { IsDenseInducing.mk' e c dense H with injective }

中文:
引理 是稠密嵌入.mk'
  结论: [拓扑空间 α] [拓扑空间 β] (e : α -> β) (c : 连续 e)
  证明: { IsDenseInducing.mk' e c dense H with injective }

Depends on / 依赖: IsDenseInducing, IsDenseInducing.mk, injective
-/
lemma IsDenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α -> β) (c : Continuous e)
    (dense : DenseRange e) (injective : Function.Injective e)
    (H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 (e a), forall b, e b in t -> b in s) : IsDenseEmbedding e :=
  { IsDenseInducing.mk' e c dense H with injective }

namespace IsDenseEmbedding

open TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
variable {e : α -> β}

/--
lemma `isDenseInducing` / 引理 `isDenseInducing`

English:
lemma isDenseInducing
  given: (de : IsDenseEmbedding e)
  statement: IsDenseInducing e
  proof: de.toIsDenseInducing

中文:
引理 isDenseInducing
  条件: (de : 是稠密嵌入 e)
  结论: 是DenseInducing e
  证明: de.toIsDenseInducing

Depends on / 依赖: de.toIsDenseInducing, toIsDenseInducing
-/
lemma isDenseInducing (de : IsDenseEmbedding e) : IsDenseInducing e := de.toIsDenseInducing

/--
theorem `inj_iff` / 定理 `inj_iff`

English:
theorem inj_iff
  given: (de : IsDenseEmbedding e) {x y}
  statement: e x = e y ↔ x = y
  proof: de.injective.eq_iff

中文:
定理 inj_iff
  条件: (de : 是稠密嵌入 e) {x y}
  结论: e x = e y ↔ x = y
  证明: de.injective.eq_iff

Depends on / 依赖: de.injective.eq_iff, eq_iff, injective
-/
theorem inj_iff (de : IsDenseEmbedding e) {x y} : e x = e y ↔ x = y :=
  de.injective.eq_iff

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: (de : IsDenseEmbedding e)
  statement: IsEmbedding e where __
  proof: de

中文:
定理 isEmbedding
  条件: (de : 是稠密嵌入 e)
  结论: 是嵌入 e where __
  证明: de
-/
theorem isEmbedding (de : IsDenseEmbedding e) : IsEmbedding e where __ := de

/--
theorem `separableSpace` / 定理 `separableSpace`

English:
theorem separableSpace
  given: [SeparableSpace α] (de : IsDenseEmbedding e)
  statement: SeparableSpace β
  proof: de.isDenseInducing.separableSpace

中文:
定理 separableSpace
  条件: [可分空间 α] (de : 是稠密嵌入 e)
  结论: 可分空间 β
  证明: de.isDenseInducing.separableSpace
-/
protected theorem separableSpace [SeparableSpace α] (de : IsDenseEmbedding e) : SeparableSpace β :=
  de.isDenseInducing.separableSpace

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {e₁ : α -> β} {e₂ : γ -> δ} (de₁ : IsDenseEmbedding e₁)
  proof: de₁.isDenseInducing.prodMap de₂.isDenseInducing
  injective := de₁.injective.prodMap de₂.injective

中文:
定理 prodMap
  结论: {e₁ : α -> β} {e₂ : γ -> δ} (de₁ : 是稠密嵌入 e₁)
  证明: de₁.isDenseInducing.prodMap de₂.isDenseInducing
  injective := de₁.injective.prodMap de₂.injective
-/
protected theorem prodMap {e₁ : α -> β} {e₂ : γ -> δ} (de₁ : IsDenseEmbedding e₁)
    (de₂ : IsDenseEmbedding e₂) : IsDenseEmbedding fun p : α × γ => (e₁ p.1, e₂ p.2) where
  toIsDenseInducing := de₁.isDenseInducing.prodMap de₂.isDenseInducing
  injective := de₁.injective.prodMap de₂.injective

/-- The dense embedding of a subtype inside its closure. -/
@[simps]
/--
Definition of `subtypeEmb` / `subtypeEmb` 的定义

English:
definition subtypeEmb
  signature: {α : Type*} (p : α -> Prop) (e : α -> β) (x : { x // p x })
  body: ⟨e x, subset_closure mem_image_of_mem e x.prop⟩

中文:
定义 subtypeEmb
  签名: {α : 类型} (p : α -> 命题) (e : α -> β) (x : { x // p x })
  定义体: ⟨e x, subset_closure mem_image_of_mem e x.prop⟩

Depends on / 依赖: mem_image_of_mem, subset_closure, x.prop
-/
def subtypeEmb {α : Type*} (p : α -> Prop) (e : α -> β) (x : { x // p x }) :
    { x // x in closure (e '' { x | p x }) } :=
⟨e x, subset_closure mem_image_of_mem e x.prop⟩

/--
theorem `subtype` / 定理 `subtype`

English:
theorem subtype
  given: (de : IsDenseEmbedding e) (p : α -> Prop)
  proof: dense_iff_closure_eq.2 by
      ext ⟨x, hx⟩
      rw [image_eq_range] at hx
      simpa [closure_subtype, ← range_comp, (· ∘ ·)]
  injective := (de.injective.comp Subtype.coe_injective).codRestrict _
  eq_induced :=
    (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
      simp [subtypeEmb, nhds_subtype

中文:
定理 subtype
  条件: (de : 是稠密嵌入 e) (p : α -> 命题)
  证明: dense_iff_closure_eq.2 by
      ext ⟨x, hx⟩
      rw [image_eq_range] at hx
      simpa [closure_subtype, ← range_comp, (· ∘ ·)]
  injective := (de.injective.comp Subtype.coe_injective).codRestrict _
  eq_induced :=
    (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
      simp [subtypeEmb, nhds_subtype
-/
protected theorem subtype (de : IsDenseEmbedding e) (p : α -> Prop) :
    IsDenseEmbedding (subtypeEmb p e) where
  dense :=
dense_iff_closure_eq.2 by
      ext ⟨x, hx⟩
      rw [image_eq_range] at hx
      simpa [closure_subtype, ← range_comp, (· ∘ ·)]
  injective := (de.injective.comp Subtype.coe_injective).codRestrict _
  eq_induced :=
    (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
      simp [subtypeEmb, nhds_subtype_eq_comap, de.isInducing.nhds_eq_comap, comap_comap,
        Function.comp_def]

/--
theorem `dense_image` / 定理 `dense_image`

English:
theorem dense_image
  given: (de : IsDenseEmbedding e) {s : Set α}
  statement: Dense (e '' s) ↔ Dense s
  proof: de.isDenseInducing.dense_image

中文:
定理 dense_image
  条件: (de : 是稠密嵌入 e) {s : 集合 α}
  结论: 稠密 (e '' s) ↔ 稠密 s
  证明: de.isDenseInducing.dense_image

Depends on / 依赖: de.isDenseInducing.dense_image, dense_image, isDenseInducing
-/
theorem dense_image (de : IsDenseEmbedding e) {s : Set α} : Dense (e '' s) ↔ Dense s :=
  de.isDenseInducing.dense_image

/--
lemma `id` / 引理 `id`

English:
lemma id
  given: {α : Type*} [TopologicalSpace α]
  statement: IsDenseEmbedding (id : α -> α)
  proof: { IsEmbedding.id with dense := denseRange_id }

中文:
引理 id
  条件: {α : 类型} [拓扑空间 α]
  结论: 是稠密嵌入 (id : α -> α)
  证明: { IsEmbedding.id with dense := denseRange_id }
-/
protected lemma id {α : Type*} [TopologicalSpace α] : IsDenseEmbedding (id : α -> α) :=
  { IsEmbedding.id with dense := denseRange_id }

end IsDenseEmbedding

/--
theorem `Dense.isDenseEmbedding_val` / 定理 `Dense.isDenseEmbedding_val`

English:
theorem Dense.isDenseEmbedding_val
  given: [TopologicalSpace α] {s : Set α} (hs : Dense s)
  proof: { IsEmbedding.subtypeVal with dense := hs.denseRange_val }

中文:
定理 稠密.isDenseEmbedding_val
  条件: [拓扑空间 α] {s : 集合 α} (hs : 稠密 s)
  证明: { IsEmbedding.subtypeVal with dense := hs.denseRange_val }

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal, denseRange_val, hs.denseRange_val, subtypeVal
-/
theorem Dense.isDenseEmbedding_val [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    IsDenseEmbedding ((↑) : s -> α) :=
  { IsEmbedding.subtypeVal with dense := hs.denseRange_val }

/--
theorem `isClosed_property` / 定理 `isClosed_property`

English:
theorem isClosed_property
  statement: [TopologicalSpace β] {e : α -> β} {p : β -> Prop} (he : DenseRange e)
  proof: by
  have : univ subseteq { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
_ subseteq closure { b | p b } := closure_mono range_subset_iff.mpr h
      _ = _ := hp.closure_eq
  simpa only [univ_subset_iff, eq_univ_iff_forall, mem_ofPred]

中文:
定理 isClosed_property
  结论: [拓扑空间 β] {e : α -> β} {p : β -> 命题} (he : DenseRange e)
  证明: by
  have : univ subseteq { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
_ subseteq closure { b | p b } := closure_mono range_subset_iff.mpr h
      _ = _ := hp.closure_eq
  simpa only [univ_subset_iff, eq_univ_iff_forall, mem_ofPred]

Depends on / 依赖: closure, closure_eq, closure_mono, closure_range, eq_univ_iff_forall, he.closure_range.symm, hp.closure_eq, mem_ofPred, range_subset_iff, range_subset_iff.mpr, subseteq, univ_subset_iff
-/
theorem isClosed_property [TopologicalSpace β] {e : α -> β} {p : β -> Prop} (he : DenseRange e)
    (hp : IsClosed { x | p x }) (h : forall a, p (e a)) : forall b, p b := by
  have : univ subseteq { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
_ subseteq closure { b | p b } := closure_mono range_subset_iff.mpr h
      _ = _ := hp.closure_eq
  simpa only [univ_subset_iff, eq_univ_iff_forall, mem_ofPred]

/--
theorem `isClosed_property2` / 定理 `isClosed_property2`

English:
theorem isClosed_property2
  statement: [TopologicalSpace β] {e : α -> β} {p : β -> β -> Prop} (he : DenseRange e)
  proof: have : forall q : β × β, p q.1 q.2 := isClosed_property (he.prodMap he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩

中文:
定理 isClosed_property2
  结论: [拓扑空间 β] {e : α -> β} {p : β -> β -> 命题} (he : DenseRange e)
  证明: have : forall q : β × β, p q.1 q.2 := isClosed_property (he.prodMap he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩

Depends on / 依赖: he.prodMap, isClosed_property, prodMap
-/
theorem isClosed_property2 [TopologicalSpace β] {e : α -> β} {p : β -> β -> Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : forall a₁ a₂, p (e a₁) (e a₂)) : forall b₁ b₂, p b₁ b₂ :=
  have : forall q : β × β, p q.1 q.2 := isClosed_property (he.prodMap he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩

/--
theorem `isClosed_property3` / 定理 `isClosed_property3`

English:
theorem isClosed_property3
  statement: [TopologicalSpace β] {e : α -> β} {p : β -> β -> β -> Prop}
  proof: have : forall q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.prodMap <| he.prodMap he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_elim]

中文:
定理 isClosed_property3
  结论: [拓扑空间 β] {e : α -> β} {p : β -> β -> β -> 命题}
  证明: have : forall q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.prodMap <| he.prodMap he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_elim]

Depends on / 依赖: he.prodMap, isClosed_property, prodMap
-/
theorem isClosed_property3 [TopologicalSpace β] {e : α -> β} {p : β -> β -> β -> Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : forall a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) : forall b₁ b₂ b₃, p b₁ b₂ b₃ :=
  have : forall q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.prodMap <| he.prodMap he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_elim]
/--
theorem `DenseRange.induction_on` / 定理 `DenseRange.induction_on`

English:
theorem DenseRange.induction_on
  statement: [TopologicalSpace β] {e : α -> β} (he : DenseRange e) {p : β -> Prop}
  proof: isClosed_property he hp ih b₀

@[elab_as_elim]

中文:
定理 DenseRange.induction_on
  结论: [拓扑空间 β] {e : α -> β} (he : DenseRange e) {p : β -> 命题}
  证明: isClosed_property he hp ih b₀

@[elab_as_elim]

Depends on / 依赖: isClosed_property
-/
theorem DenseRange.induction_on [TopologicalSpace β] {e : α -> β} (he : DenseRange e) {p : β -> Prop}
    (b₀ : β) (hp : IsClosed { b | p b }) (ih : forall a : α, p <| e a) : p b₀ :=
  isClosed_property he hp ih b₀

@[elab_as_elim]
/--
theorem `DenseRange.induction_on₂` / 定理 `DenseRange.induction_on₂`

English:
theorem DenseRange.induction_on₂
  statement: [TopologicalSpace β] {e : α -> β} {p : β -> β -> Prop}
  proof: isClosed_property2 he hp h _ _

@[elab_as_elim]

中文:
定理 DenseRange.induction_on₂
  结论: [拓扑空间 β] {e : α -> β} {p : β -> β -> 命题}
  证明: isClosed_property2 he hp h _ _

@[elab_as_elim]

Depends on / 依赖: isClosed_property2
-/
theorem DenseRange.induction_on₂ [TopologicalSpace β] {e : α -> β} {p : β -> β -> Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : forall a₁ a₂, p (e a₁) (e a₂))
    (b₁ b₂ : β) : p b₁ b₂ :=
  isClosed_property2 he hp h _ _

@[elab_as_elim]
/--
theorem `DenseRange.induction_on₃` / 定理 `DenseRange.induction_on₃`

English:
theorem DenseRange.induction_on₃
  statement: [TopologicalSpace β] {e : α -> β} {p : β -> β -> β -> Prop}
  proof: isClosed_property3 he hp h _ _ _

中文:
定理 DenseRange.induction_on₃
  结论: [拓扑空间 β] {e : α -> β} {p : β -> β -> β -> 命题}
  证明: isClosed_property3 he hp h _ _ _

Depends on / 依赖: isClosed_property3
-/
theorem DenseRange.induction_on₃ [TopologicalSpace β] {e : α -> β} {p : β -> β -> β -> Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : forall a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) (b₁ b₂ b₃ : β) : p b₁ b₂ b₃ :=
  isClosed_property3 he hp h _ _ _

section

variable [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]
variable {f : α -> β}

/--
theorem `DenseRange.equalizer` / 定理 `DenseRange.equalizer`

English:
theorem DenseRange.equalizer
  statement: (hfd : DenseRange f) {g h : β -> γ} (hg : Continuous g)
  proof: funext fun y => hfd.induction_on y (isClosed_eq hg hh) congr_fun H

中文:
定理 DenseRange.equalizer
  结论: (hfd : DenseRange f) {g h : β -> γ} (hg : 连续 g)
  证明: funext fun y => hfd.induction_on y (isClosed_eq hg hh) congr_fun H

Depends on / 依赖: congr_fun, hfd.induction_on, induction_on, isClosed_eq
-/
theorem DenseRange.equalizer (hfd : DenseRange f) {g h : β -> γ} (hg : Continuous g)
    (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h :=
funext fun y => hfd.induction_on y (isClosed_eq hg hh) congr_fun H

end

-- Bourbaki GT III §3 no.4 Proposition 7 (generalised to any dense-inducing map to a regular space)
/--
theorem `Filter.HasBasis.hasBasis_of_isDenseInducing` / 定理 `Filter.HasBasis.hasBasis_of_isDenseInducing`

English:
theorem Filter.HasBasis.hasBasis_of_isDenseInducing
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  rw [Filter.hasBasis_iff] at h ⊢
  intro T
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' in 𝓝 x := by
      rw [hf.isInducing.nhds_eq_comap x]
      exact ⟨T', hT₁, Subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).m

中文:
定理 滤子.有基.hasBasis_of_isDenseInducing
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  rw [Filter.hasBasis_iff] at h ⊢
  intro T
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' in 𝓝 x := by
      rw [hf.isInducing.nhds_eq_comap x]
      exact ⟨T', hT₁, Subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).m

Depends on / 依赖: Filter, Filter.hasBasis_iff, Subset, Subset.rfl, Subset.trans, closure, closure_minimal, closure_mono, exists_mem_nhds_isClosed_subset, filter_upwards, hasBasis_iff, hf.isInducing.nhds_eq_comap, image_mono, image_preimage_subset, isInducing, nhds_eq_comap
-/
theorem Filter.HasBasis.hasBasis_of_isDenseInducing [TopologicalSpace α] [TopologicalSpace β]
    [RegularSpace β] {ι : Type*} {s : ι -> Set α} {p : ι -> Prop} {x : α} (h : (𝓝 x).HasBasis p s)
{f : α -> β} (hf : IsDenseInducing f) : (𝓝 (f x)).HasBasis p fun i => closure f '' s i := by
  rw [Filter.hasBasis_iff] at h ⊢
  intro T
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' in 𝓝 x := by
      rw [hf.isInducing.nhds_eq_comap x]
      exact ⟨T', hT₁, Subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).mp hT₄
    exact
      ⟨i, hi,
        (closure_mono (image_mono hi')).trans
          (Subset.trans (closure_minimal (image_preimage_subset _ _) hT₂) hT₃)⟩
  · obtain ⟨i, hi, hi'⟩ := hT
    suffices closure (f '' s i) in 𝓝 (f x) by filter_upwards [this] using hi'
    replace h := (h (s i)).mpr ⟨i, hi, Subset.rfl⟩
    exact hf.closure_image_mem_nhds h
