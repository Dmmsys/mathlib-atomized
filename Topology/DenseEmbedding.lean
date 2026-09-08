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

* `DenseRange f`       means `f` has dense image;
* `IsDenseInducing i`  means `i` is also inducing, namely it induces the topology on its codomain;
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

/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
/-
**IsDenseInducing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [TopologicalSpace α] → [TopologicalSpace
 β] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`.
-/
structure IsDenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α → β) : Prop
    extends IsInducing i where
  /-- The range of a dense inducing map is a dense set. -/
  protected dense : DenseRange i

namespace IsDenseInducing

variable [TopologicalSpace α] [TopologicalSpace β]

/-
**IsDenseInducing._root_.Dense.isDenseInducing_val** 是 Mathlib 中的一个定理，位于命名空间 `Is
DenseInducing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dense.isDenseInducing_val {s : Set α} (hs : Dense s) :
    IsDenseInducing ((↑) : s → α) := ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

variable {i : α → β}
/-
**IsDenseInducing.isInducing** 是 Mathlib 中的一个引理，位于命名空间 `IsDenseInducing`。
形式化陈述：isInducing (di : IsDenseInducing i) : IsInducing i
参数：di : IsDenseInducing i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.toIsInducing`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i
 → Topology.IsIndu…
-/
lemma isInducing (di : IsDenseInducing i) : IsInducing i := di.toIsInducing
/-
**IsDenseInducing.nhds_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：nhds_eq_comap (di : IsDenseInducing i) : forall a : α, 𝓝 a = comap i (𝓝 <|
 i a)
参数：di : IsDenseInducing i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
-/
theorem nhds_eq_comap (di : IsDenseInducing i) : ∀ a : α, 𝓝 a = comap i (𝓝 <| i a) :=
  di.isInducing.nhds_eq_comap
/-
**IsDenseInducing.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {i : α → β},   IsDenseInducing i → Continuous i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
-/
protected theorem continuous (di : IsDenseInducing i) : Continuous i :=
  di.isInducing.continuous
/-
**IsDenseInducing.closure_range** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：closure_range (di : IsDenseInducing i) : closure (range i) = univ
参数：di : IsDenseInducing i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.closure_range`：DenseRange.closure_range (h : DenseRange f) : 
closure (range f) = univ
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
-/
theorem closure_range (di : IsDenseInducing i) : closure (range i) = univ :=
  di.dense.closure_range
/-
**IsDenseInducing.preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {i : α → β}   [PreconnectedSpace α], IsDenseInducing i → Preconn
ectedSpace β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.preconnectedSpace`：DenseRange.preconnectedSpace [TopologicalS
pace β] [PreconnectedSpace α] {f : α -> β} (hf : DenseRange f) (hc : Continuous 
f) : PreconnectedS…
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseInducing.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i →
 Continuous i
-/
protected theorem preconnectedSpace [PreconnectedSpace α] (di : IsDenseInducing i) :
    PreconnectedSpace β :=
  di.dense.preconnectedSpace di.continuous
/-
**IsDenseInducing.closure_image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInduc
ing`。
形式化陈述：closure_image_mem_nhds {s : Set α} {a : α} (di : IsDenseInducing i) (hs : 
s in 𝓝 a) : closure (i '' s) in 𝓝 (i a)
参数：di : IsDenseInducing i；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `DenseRange.subset_closure_image_preimage_of_isOpen`：DenseRange.subset_cl
osure_image_preimage_of_isOpen (hf : DenseRange f) (hs : IsOpen s) : s subseteq 
closure (f '' f ⁻¹' s)
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem closure_image_mem_nhds {s : Set α} {a : α} (di : IsDenseInducing i) (hs : s ∈ 𝓝 a) :
    closure (i '' s) ∈ 𝓝 (i a) := by
  rw [di.nhds_eq_comap a, ((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U ⊆ s⟩
  refine mem_of_superset (hUo.mem_nhds haU) ?_
  calc
    U ⊆ closure (i '' i ⁻¹' U) := di.dense.subset_closure_image_preimage_of_isOpen hUo
    _ ⊆ closure (i '' s) := closure_mono (image_mono sub)
/-
**IsDenseInducing.dense_image** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：dense_image (di : IsDenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense 
s
参数：di : IsDenseInducing i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `DenseRange.dense_image`：DenseRange.dense_image {f : X -> Y} (hf' : Dense
Range f) (hf : Continuous f) (hs : Dense s) : Dense (f '' s)
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseInducing.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i →
 Continuous i
-/
theorem dense_image (di : IsDenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense s := by
  refine ⟨fun H x => ?_, di.dense.dense_image di.continuous⟩
  rw [di.isInducing.closure_eq_preimage_closure_image, H.closure_eq, preimage_univ]
  trivial

/-- If `i : α → β` is a dense embedding with dense complement of the range, then any compact set in
`α` has empty interior. -/
/-
**IsDenseInducing.interior_compact_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseIn
ducing`。
形式化陈述：interior_compact_eq_empty [T2Space β] (di : IsDenseInducing i) (hd : Dense
 (range i)ᶜ) {s : Set α} (hs : IsCompact s) : interior s = ∅
参数：di : IsDenseInducing i；hd : Dense (range i)ᶜ；hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `IsDenseInducing.closure_image_mem_nhds`：closure_image_mem_nhds {s : Set 
α} {a : α} (di : IsDenseInducing i) (hs : s in 𝓝 a) : closure (i '' s) in 𝓝 (i a
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Dense.inter_nhds_nonempty`：Dense.inter_nhds_nonempty (hs : Dense s) (ht 
: t in 𝓝 x) : (s inter t).Nonempty
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsDenseInducing.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i →
 Continuous i
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f

--- 原说明 ---
If `i : α → β` is a dense embedding with dense complement of the range, then any
 compact set in
`α` has empty interior.
-/
theorem interior_compact_eq_empty [T2Space β] (di : IsDenseInducing i) (hd : Dense (range i)ᶜ)
    {s : Set α} (hs : IsCompact s) : interior s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).isClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

/-- The product of two dense inducings is a dense inducing -/
/-
**IsDenseInducing.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] [i
nst_3 : TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ},   IsDenseInducing e₁ → Is
DenseInducing e₂ → IsDenseInducing (Prod.map e₁ e₂)
参数：Prod.map e₁ e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.prodMap`：Topology.IsInducing.prodMap {f : X -> Y} {g
 : Z -> W} (hf : IsInducing f) (hg : IsInducing g) : IsInducing (Prod.map f g)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `DenseRange.prodMap`：DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι ->
 Y} {g : κ -> Z} (hf : DenseRange f) (hg : DenseRange g) : DenseRange (Prod.map 
f g)
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i

--- 原说明 ---
The product of two dense inducings is a dense inducing
-/
protected theorem prodMap [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ}
    (de₁ : IsDenseInducing e₁) (de₂ : IsDenseInducing e₂) :
    IsDenseInducing (Prod.map e₁ e₂) where
  toIsInducing := de₁.isInducing.prodMap de₂.isInducing
  dense := de₁.dense.prodMap de₂.dense

open TopologicalSpace

/-- If the domain of a `IsDenseInducing` map is a separable space, then so is the codomain. -/
/-
**IsDenseInducing.separableSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {i : α → β}   [TopologicalSpace.SeparableSpace α], IsDenseInduci
ng i → TopologicalSpace.SeparableSpace β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.separableSpace`：∀ {α : Type u} {β : Type u_1} [t : Topologica
lSpace α] [TopologicalSpace.SeparableSpace α] [inst : TopologicalSpace β]   {f :
 α → β}, DenseR…
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseInducing.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i →
 Continuous i

--- 原说明 ---
If the domain of a `IsDenseInducing` map is a separable space, then so is the co
domain.
-/
protected theorem separableSpace [SeparableSpace α] (di : IsDenseInducing i) : SeparableSpace β :=
  di.dense.separableSpace di.continuous

variable [TopologicalSpace δ] {f : γ → α} {g : γ → δ} {h : δ → β}

/--
```
 γ -f→ α
g↓     ↓e
 δ -h→ β
```
-/
/-
**IsDenseInducing.tendsto_comap_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseIndu
cing`。
形式化陈述：tendsto_comap_nhds_nhds {d : δ} {a : α} (di : IsDenseInducing i) (H : Tend
sto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a)
参数：di : IsDenseInducing i；H : Tendsto h (𝓝 d) (𝓝 (i a))；comm : h ∘ g = i ∘ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)

--- 原说明 ---
```
 γ -f→ α
g↓     ↓e
 δ -h→ β
```
-/
theorem tendsto_comap_nhds_nhds {d : δ} {a : α} (di : IsDenseInducing i)
    (H : Tendsto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a) := by
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map, comm, ← Filter.map_map, map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) ≤ comap i (𝓝 (i a)) := comap_mono H
  rw [← di.nhds_eq_comap] at lim2
  exact le_trans lim1 lim2
/-
**IsDenseInducing.nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {i : α → β},   IsDenseInducing i → ∀ (b : β), (nhdsWithin b (Set
.range i)).NeBot
参数：b : β；nhdsWithin b (Set.range i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.nhdsWithin_neBot`：DenseRange.nhdsWithin_neBot {ι : Type*} {f 
: ι -> α} (h : DenseRange f) (x : α) : NeBot (𝓝[range f] x)
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
-/
protected theorem nhdsWithin_neBot (di : IsDenseInducing i) (b : β) : NeBot (𝓝[range i] b) :=
  di.dense.nhdsWithin_neBot b
/-
**IsDenseInducing.comap_nhds_neBot** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：comap_nhds_neBot (di : IsDenseInducing i) (b : β) : NeBot (comap i (𝓝 b))
参数：di : IsDenseInducing i；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_neBot`：comap_neBot {f : Filter β} {m : α -> β} (hm : forall
 t in f, exists a, m a in t) : NeBot (comap m f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
-/
theorem comap_nhds_neBot (di : IsDenseInducing i) (b : β) : NeBot (comap i (𝓝 b)) :=
  comap_neBot fun s hs => by
    rcases mem_closure_iff_nhds.1 (di.dense b) s hs with ⟨_, ⟨ha, a, rfl⟩⟩
    exact ⟨a, ha⟩
/-
**IsDenseInducing._root_.Dense.comap_val_nhds_neBot** 是 Mathlib 中的一个定理，位于命名空间 `I
sDenseInducing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dense.comap_val_nhds_neBot {s : Set α} (hs : Dense s) (a : α) :
    ((𝓝 a).comap ((↑) : s → α)).NeBot :=
  hs.isDenseInducing_val.comap_nhds_neBot _

variable [TopologicalSpace γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends" to a function `g =
  IsDenseInducing.extend di f : β → γ`. If `γ` is Hausdorff and `f` has a continuous extension, then
  `g` is the unique such extension. In general, `g` might not be continuous or even extend `f`. -/
/-
**IsDenseInducing.extend** 是 Mathlib 中的一个定义，位于命名空间 `IsDenseInducing`。
形式化陈述：extend (di : IsDenseInducing i) (f : α -> γ) (b : β) : γ
参数：di : IsDenseInducing i；f : α -> γ；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends" to a
 function `g =
  IsDenseInducing.extend di f : β → γ`. If `γ` is Hausdorff and `f` has a contin
uous extension, then
  `g` is the unique such extension. In general, `g` might not be continuous or e
ven extend `f`.
-/
def extend (di : IsDenseInducing i) (f : α → γ) (b : β) : γ :=
  @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f
/-
**IsDenseInducing.tendsto_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：tendsto_extend (di : IsDenseInducing i) {f : α -> γ} {a : α} (hf : Continu
ousAt f a) : Tendsto f (𝓝 a) (𝓝 (di.extend f (i a)))
参数：di : IsDenseInducing i；hf : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDenseInducing.extend.eq_1`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β}   [ins
t_2 : Topological…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
-/
theorem tendsto_extend (di : IsDenseInducing i) {f : α → γ} {a : α} (hf : ContinuousAt f a) :
    Tendsto f (𝓝 a) (𝓝 (di.extend f (i a))) := by
  rw [IsDenseInducing.extend, ← di.nhds_eq_comap]
  exact tendsto_nhds_limUnder ⟨_, hf⟩
/-
**IsDenseInducing.inseparable_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`
。
形式化陈述：inseparable_extend [R1Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : 
α} (hf : ContinuousAt f a) : Inseparable (di.extend f (i a)) (f a)
参数：di : IsDenseInducing i；hf : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `IsDenseInducing.tendsto_extend`：tendsto_extend (di : IsDenseInducing i) 
{f : α -> γ} {a : α} (hf : ContinuousAt f a) : Tendsto f (𝓝 a) (𝓝 (di.extend f (
i a)))
-/
theorem inseparable_extend [R1Space γ] (di : IsDenseInducing i) {f : α → γ} {a : α}
    (hf : ContinuousAt f a) : Inseparable (di.extend f (i a)) (f a) :=
  tendsto_nhds_unique_inseparable (di.tendsto_extend hf) hf
/-
**IsDenseInducing.extend_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducin
g`。
形式化陈述：extend_eq_of_tendsto [T2Space γ] (di : IsDenseInducing i) {b : β} {c : γ} 
{f : α -> γ} (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) : di.extend f b = c
参数：di : IsDenseInducing i；hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `IsDenseInducing.comap_nhds_neBot`：comap_nhds_neBot (di : IsDenseInducing
 i) (b : β) : NeBot (comap i (𝓝 b))
-/
theorem extend_eq_of_tendsto [T2Space γ] (di : IsDenseInducing i) {b : β} {c : γ} {f : α → γ}
    (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) : di.extend f b = c :=
  haveI := di.comap_nhds_neBot
  hf.limUnder_eq
/-
**IsDenseInducing.extend_eq_at** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_eq_at [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α} (hf
 : ContinuousAt f a) : di.extend f (i a) = f a
参数：di : IsDenseInducing i；hf : ContinuousAt f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
-/
theorem extend_eq_at [T2Space γ] (di : IsDenseInducing i) {f : α → γ} {a : α}
    (hf : ContinuousAt f a) : di.extend f (i a) = f a :=
  extend_eq_of_tendsto _ <| di.nhds_eq_comap a ▸ hf
/-
**IsDenseInducing.extend_eq_at'** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_eq_at' [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} {a : α} (c
 : γ) (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend f (i a) = f a
参数：di : IsDenseInducing i；c : γ；hf : Tendsto f (𝓝 a) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `continuousAt_of_tendsto_nhds`：continuousAt_of_tendsto_nhds [TopologicalS
pace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : C
ontinuousAt f x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
theorem extend_eq_at' [T2Space γ] (di : IsDenseInducing i) {f : α → γ} {a : α} (c : γ)
    (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend f (i a) = f a :=
  di.extend_eq_at (continuousAt_of_tendsto_nhds hf)
/-
**IsDenseInducing.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_eq [T2Space γ] (di : IsDenseInducing i) {f : α -> γ} (hf : Continuo
us f) (a : α) : di.extend f (i a) = f a
参数：di : IsDenseInducing i；hf : Continuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem extend_eq [T2Space γ] (di : IsDenseInducing i) {f : α → γ} (hf : Continuous f) (a : α) :
    di.extend f (i a) = f a :=
  di.extend_eq_at hf.continuousAt

/-- Variation of `extend_eq` where we ask that `f` has a limit along `comap i (𝓝 b)` for each
`b : β`. This is a strictly stronger assumption than continuity of `f`, but in a lot of cases
you'd have to prove it anyway to use `continuous_extend`, so this avoids doing the work twice. -/
/-
**IsDenseInducing.extend_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_eq' [T2Space γ] {f : α -> γ} (di : IsDenseInducing i) (hf : forall 
b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) (a : α) : di.extend f (i a) = f a
参数：di : IsDenseInducing i；hf : forall b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 
c)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at'`：extend_eq_at' [T2Space γ] (di : IsDenseIn
ducing i) {f : α -> γ} {a : α} (c : γ) (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend 
f (i a) = f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i

--- 原说明 ---
Variation of `extend_eq` where we ask that `f` has a limit along `comap i (𝓝 b)`
 for each
`b : β`. This is a strictly stronger assumption than continuity of `f`, but in a
 lot of cases
you'd have to prove it anyway to use `continuous_extend`, so this avoids doing t
he work twice.
-/
theorem extend_eq' [T2Space γ] {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) (a : α) : di.extend f (i a) = f a := by
  rcases hf (i a) with ⟨b, hb⟩
  refine di.extend_eq_at' b ?_
  rwa [← di.isInducing.nhds_eq_comap] at hb
/-
**IsDenseInducing.extend_unique_at** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_unique_at [T2Space γ] {b : β} {f : α -> γ} {g : β -> γ} (di : IsDen
seInducing i) (hf : forallᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousA
t g b) : di.extend f b = g b
参数：di : IsDenseInducing i；hf : forallᶠ x in comap i (𝓝 b), g (i x) = f x；hg : Co
ntinuousAt g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem extend_unique_at [T2Space γ] {b : β} {f : α → γ} {g : β → γ} (di : IsDenseInducing i)
    (hf : ∀ᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousAt g b) : di.extend f b = g b := by
  refine di.extend_eq_of_tendsto fun s hs => mem_map.2 ?_
  suffices ∀ᶠ x : α in comap i (𝓝 b), g (i x) ∈ s from
    hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine eventually_comap.2 ((hg.eventually hs).mono ?_)
  rintro _ hxs x rfl
  exact hxs
/-
**IsDenseInducing.extend_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：extend_unique [T2Space γ] {f : α -> γ} {g : β -> γ} (di : IsDenseInducing 
i) (hf : forall x, g (i x) = f x) (hg : Continuous g) : di.extend f = g
参数：di : IsDenseInducing i；hf : forall x, g (i x) = f x；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsDenseInducing.extend_unique_at`：extend_unique_at [T2Space γ] {b : β} {
f : α -> γ} {g : β -> γ} (di : IsDenseInducing i) (hf : forallᶠ x in comap i (𝓝 
b), g (i x) = f x) (hg…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem extend_unique [T2Space γ] {f : α → γ} {g : β → γ} (di : IsDenseInducing i)
    (hf : ∀ x, g (i x) = f x) (hg : Continuous g) : di.extend f = g :=
  funext fun _ => extend_unique_at di (Eventually.of_forall hf) hg.continuousAt
/-
**IsDenseInducing.continuousAt_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing
`。
形式化陈述：continuousAt_extend [T3Space γ] {b : β} {f : α -> γ} (di : IsDenseInducing
 i) (hf : forallᶠ x in 𝓝 b, exists c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : Contin
uousAt (di.extend f) b
参数：di : IsDenseInducing i；hf : forallᶠ x in 𝓝 b, exists c, Tendsto f (comap i <|
 𝓝 x) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDenseInducing.comap_nhds_neBot`：comap_nhds_neBot (di : IsDenseInducing
 i) (b : β) : NeBot (comap i (𝓝 b))
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_opens'`：nhds_basis_opens' (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsOpen s) fun x => x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
-/
theorem continuousAt_extend [T3Space γ] {b : β} {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ᶠ x in 𝓝 b, ∃ c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : ContinuousAt (di.extend f) b := by
  set φ := di.extend f
  have := di.comap_nhds_neBot
  suffices ∀ V' ∈ 𝓝 (φ b), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis (φ b)).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | Tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ ∈ 𝓝 b := by
    filter_upwards [hf]
    rintro x ⟨c, hc⟩
    rwa [← di.extend_eq_of_tendsto hc] at hc
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : ∃ V₂ ∈ 𝓝 b, IsOpen V₂ ∧ ∀ x ∈ i ⁻¹' V₂, f x ∈ V' := by
    simpa [and_assoc] using!
      ((nhds_basis_opens' b).comap i).tendsto_left_iff.mp (mem_of_mem_nhds V₁_in : b ∈ V₁) V' V'_in
  suffices ∀ x ∈ V₁ ∩ V₂, φ x ∈ V' by filter_upwards [inter_mem V₁_in V₂_in] using this
  rintro x ⟨x_in₁, x_in₂⟩
  have hV₂x : V₂ ∈ 𝓝 x := IsOpen.mem_nhds V₂_op x_in₂
  apply V'_closed.mem_of_tendsto x_in₁
  use V₂
  tauto
/-
**IsDenseInducing.continuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：continuous_extend [T3Space γ] {f : α -> γ} (di : IsDenseInducing i) (hf : 
forall b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f)
参数：di : IsDenseInducing i；hf : forall b, exists c, Tendsto f (comap i (𝓝 b)) (𝓝 
c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `IsDenseInducing.continuousAt_extend`：continuousAt_extend [T3Space γ] {b 
: β} {f : α -> γ} (di : IsDenseInducing i) (hf : forallᶠ x in 𝓝 b, exists c, Ten
dsto f (comap i <| 𝓝 x) (…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem continuous_extend [T3Space γ] {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f) :=
  continuous_iff_continuousAt.mpr fun _ => di.continuousAt_extend <| univ_mem' hf
/-
**IsDenseInducing.mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseInducing`。
形式化陈述：mk' (i : α -> β) (c : Continuous i) (dense : forall x, x in closure (range
 i)) (H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 (i a), forall b, i b in
 t -> b in s) : IsDenseInducing i where toIsInducing
参数：i : α -> β；c : Continuous i；dense : forall x, x in closure (range i)；H : fora
ll (a : α), forall s in 𝓝 a, exists t in 𝓝 (i a), forall b, i b in t -> b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem mk' (i : α → β) (c : Continuous i) (dense : ∀ x, x ∈ closure (range i))
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (i a), ∀ b, i b ∈ t → b ∈ s) : IsDenseInducing i where
  toIsInducing := isInducing_iff_nhds.2 fun a =>
      le_antisymm (c.tendsto _).le_comap (by simpa [Filter.le_def] using! H a)
  dense := dense

end IsDenseInducing

namespace Dense

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α}

/-- This is a shortcut for `hs.isDenseInducing_val.extend f`. It is useful because if `s : Set α`
is dense then the coercion `(↑) : s → α` automatically satisfies `IsUniformInducing` and
`IsDenseInducing` so this gives access to the theorems satisfied by a uniform extension by simply
mentioning the density hypothesis. -/
/-
**Dense.extend** 是 Mathlib 中的一个定义，位于命名空间 `Dense`。
形式化陈述：extend (hs : Dense s) (f : s -> β) : α -> β
参数：hs : Dense s；f : s -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val

--- 原说明 ---
This is a shortcut for `hs.isDenseInducing_val.extend f`. It is useful because i
f `s : Set α`
is dense then the coercion `(↑) : s → α` automatically satisfies `IsUniformInduc
ing` and
`IsDenseInducing` so this gives access to the theorems satisfied by a uniform ex
tension by simply
mentioning the density hypothesis.
-/
noncomputable def extend (hs : Dense s) (f : s → β) : α → β :=
    hs.isDenseInducing_val.extend f

variable {f : s → β}
/-
**Dense.extend_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_eq_of_tendsto [T2Space β] (hs : Dense s) {a : α} {b : β} (hf : Tend
sto f (comap (↑) (𝓝 a)) (𝓝 b)) : hs.extend f a = b
参数：hs : Dense s；hf : Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem extend_eq_of_tendsto [T2Space β] (hs : Dense s) {a : α} {b : β}
    (hf : Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : hs.extend f a = b :=
  hs.isDenseInducing_val.extend_eq_of_tendsto hf
/-
**Dense.extend_eq_at** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_eq_at [T2Space β] (hs : Dense s) {f : s -> β} {x : s} (hf : Continu
ousAt f x) : hs.extend f x = f x
参数：hs : Dense s；hf : ContinuousAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem extend_eq_at [T2Space β] (hs : Dense s) {f : s → β} {x : s}
    (hf : ContinuousAt f x) : hs.extend f x = f x :=
  hs.isDenseInducing_val.extend_eq_at hf
/-
**Dense.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_eq [T2Space β] (hs : Dense s) (hf : Continuous f) (x : s) : hs.exte
nd f x = f x
参数：hs : Dense s；hf : Continuous f；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.extend_eq_at`：extend_eq_at [T2Space β] (hs : Dense s) {f : s -> β}
 {x : s} (hf : ContinuousAt f x) : hs.extend f x = f x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem extend_eq [T2Space β] (hs : Dense s) (hf : Continuous f) (x : s) :
    hs.extend f x = f x :=
  hs.extend_eq_at hf.continuousAt
/-
**Dense.extend_unique_at** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_unique_at [T2Space β] {a : α} {g : α -> β} (hs : Dense s) (hf : for
allᶠ x : s in comap (↑) (𝓝 a), g x = f x) (hg : ContinuousAt g a) : hs.extend f 
a = g a
参数：hs : Dense s；hf : forallᶠ x : s in comap (↑) (𝓝 a), g x = f x；hg : Continuous
At g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_unique_at`：extend_unique_at [T2Space γ] {b : β} {
f : α -> γ} {g : β -> γ} (di : IsDenseInducing i) (hf : forallᶠ x in comap i (𝓝 
b), g (i x) = f x) (hg…
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem extend_unique_at [T2Space β] {a : α} {g : α → β} (hs : Dense s)
    (hf : ∀ᶠ x : s in comap (↑) (𝓝 a), g x = f x) (hg : ContinuousAt g a) :
    hs.extend f a = g a :=
  hs.isDenseInducing_val.extend_unique_at hf hg
/-
**Dense.extend_unique** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：extend_unique [T2Space β] {g : α -> β} (hs : Dense s) (hf : forall x : s, 
g x = f x) (hg : Continuous g) : hs.extend f = g
参数：hs : Dense s；hf : forall x : s, g x = f x；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_unique`：extend_unique [T2Space γ] {f : α -> γ} {g
 : β -> γ} (di : IsDenseInducing i) (hf : forall x, g (i x) = f x) (hg : Continu
ous g) : di.extend …
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem extend_unique [T2Space β] {g : α → β} (hs : Dense s)
    (hf : ∀ x : s, g x = f x) (hg : Continuous g) : hs.extend f = g :=
  hs.isDenseInducing_val.extend_unique hf hg
/-
**Dense.continuousAt_extend** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：continuousAt_extend [T3Space β] {a : α} (hs : Dense s) (hf : forallᶠ x in 
𝓝 a, exists b, Tendsto f (comap (↑) <| 𝓝 x) (𝓝 b)) : ContinuousAt (hs.extend f) 
a
参数：hs : Dense s；hf : forallᶠ x in 𝓝 a, exists b, Tendsto f (comap (↑) <| 𝓝 x) (𝓝
 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.continuousAt_extend`：continuousAt_extend [T3Space γ] {b 
: β} {f : α -> γ} (di : IsDenseInducing i) (hf : forallᶠ x in 𝓝 b, exists c, Ten
dsto f (comap i <| 𝓝 x) (…
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem continuousAt_extend [T3Space β] {a : α} (hs : Dense s)
    (hf : ∀ᶠ x in 𝓝 a, ∃ b, Tendsto f (comap (↑) <| 𝓝 x) (𝓝 b)) :
    ContinuousAt (hs.extend f) a :=
  hs.isDenseInducing_val.continuousAt_extend hf
/-
**Dense.continuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：continuous_extend [T3Space β] (hs : Dense s) (hf : forall a : α, exists b,
 Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : Continuous (hs.extend f)
参数：hs : Dense s；hf : forall a : α, exists b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.continuous_extend`：continuous_extend [T3Space γ] {f : α 
-> γ} (di : IsDenseInducing i) (hf : forall b, exists c, Tendsto f (comap i (𝓝 b
)) (𝓝 c)) : Continuous …
· 使用定理 `Dense.isDenseInducing_val`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, Dense s → IsDenseInducing Subtype.val
-/
theorem continuous_extend [T3Space β] (hs : Dense s)
    (hf : ∀ a : α, ∃ b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : Continuous (hs.extend f) :=
  hs.isDenseInducing_val.continuous_extend hf

end Dense

/-- A dense embedding is an embedding with dense image. -/
/-
**IsDenseEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [TopologicalSpace α] → [TopologicalSpace
 β] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dense embedding is an embedding with dense image.
-/
structure IsDenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α → β) : Prop
    extends IsDenseInducing e where
  /-- A dense embedding is injective. -/
  injective : Function.Injective e
/-
**IsDenseEmbedding.mk'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α -> β
) (c : Continuous e) (dense : DenseRange e) (injective : Function.Injective e) (
H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 (e a), forall b, e b in t -> 
b in s) : IsDenseEmbedding e
参数：e : α -> β；c : Continuous e；dense : DenseRange e；injective : Function.Injecti
ve e；H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 (e a), forall b, e b in 
t -> b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.mk'`：mk' (i : α -> β) (c : Continuous i) (dense : forall
 x, x in closure (range i)) (H : forall (a : α), forall s in 𝓝 a, exists t in 𝓝 
(i a), fo…
-/
lemma IsDenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α → β) (c : Continuous e)
    (dense : DenseRange e) (injective : Function.Injective e)
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) : IsDenseEmbedding e :=
  { IsDenseInducing.mk' e c dense H with injective }

namespace IsDenseEmbedding

open TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
variable {e : α → β}

/-
**IsDenseEmbedding.isDenseInducing** 是 Mathlib 中的一个引理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：isDenseInducing (de : IsDenseEmbedding e) : IsDenseInducing e
参数：de : IsDenseEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
-/
lemma isDenseInducing (de : IsDenseEmbedding e) : IsDenseInducing e := de.toIsDenseInducing
/-
**IsDenseEmbedding.inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：inj_iff (de : IsDenseEmbedding e) {x y} : e x = e y ↔ x = y
参数：de : IsDenseEmbedding e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…
-/
theorem inj_iff (de : IsDenseEmbedding e) {x y} : e x = e y ↔ x = y :=
  de.injective.eq_iff
/-
**IsDenseEmbedding.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：isEmbedding (de : IsDenseEmbedding e) : IsEmbedding e where __
参数：de : IsDenseEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.toIsInducing`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i
 → Topology.IsIndu…
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…
-/
theorem isEmbedding (de : IsDenseEmbedding e) : IsEmbedding e where __ := de

/-- If the domain of a `IsDenseEmbedding` is a separable space, then so is its codomain. -/
/-
**IsDenseEmbedding.separableSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {e : α → β}   [TopologicalSpace.SeparableSpace α], IsDenseEmbedd
ing e → TopologicalSpace.SeparableSpace β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.separableSpace`：∀ {α : Type u_1} {β : Type u_2} [inst : 
TopologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β}   [TopologicalSpac
e.SeparableSpace α],…
· 使用引理 `IsDenseEmbedding.isDenseInducing`：isDenseInducing (de : IsDenseEmbedding
 e) : IsDenseInducing e

--- 原说明 ---
If the domain of a `IsDenseEmbedding` is a separable space, then so is its codom
ain.
-/
protected theorem separableSpace [SeparableSpace α] (de : IsDenseEmbedding e) : SeparableSpace β :=
  de.isDenseInducing.separableSpace

/-- The product of two dense embeddings is a dense embedding. -/
/-
**IsDenseEmbedding.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] [i
nst_3 : TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ},   IsDenseEmbedding e₁ → I
sDenseEmbedding e₂ → IsDenseEmbedding fun p => (e₁ p.1, e₂ p.2)
参数：e₁ p.1, e₂ p.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{δ : Type u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : Topologi…
· 使用引理 `IsDenseEmbedding.isDenseInducing`：isDenseInducing (de : IsDenseEmbedding
 e) : IsDenseInducing e
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…

--- 原说明 ---
The product of two dense embeddings is a dense embedding.
-/
protected theorem prodMap {e₁ : α → β} {e₂ : γ → δ} (de₁ : IsDenseEmbedding e₁)
    (de₂ : IsDenseEmbedding e₂) : IsDenseEmbedding fun p : α × γ => (e₁ p.1, e₂ p.2) where
  toIsDenseInducing := de₁.isDenseInducing.prodMap de₂.isDenseInducing
  injective := de₁.injective.prodMap de₂.injective

/-- The dense embedding of a subtype inside its closure. -/
@[simps]
/-
**IsDenseEmbedding.subtypeEmb** 是 Mathlib 中的一个定义，位于命名空间 `IsDenseEmbedding`。
形式化陈述：subtypeEmb {α : Type*} (p : α -> Prop) (e : α -> β) (x : { x // p x }) : {
 x // x in closure (e '' { x | p x }) }
参数：p : α -> Prop；e : α -> β；x : { x // p x }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dense embedding of a subtype inside its closure.
-/
def subtypeEmb {α : Type*} (p : α → Prop) (e : α → β) (x : { x // p x }) :
    { x // x ∈ closure (e '' { x | p x }) } :=
  ⟨e x, subset_closure <| mem_image_of_mem e x.prop⟩
/-
**IsDenseEmbedding.subtype** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {e : α → β},   IsDenseEmbedding e → ∀ (p : α → Prop), IsDenseEmb
edding (IsDenseEmbedding.subtypeEmb p e)
参数：p : α → Prop；IsDenseEmbedding.subtypeEmb p e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `induced_iff_nhds_eq`：induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ :
 TopologicalSpace β] (f : β -> α) : tβ = tα.induced f ↔ forall b, 𝓝 b = comap f 
(𝓝 <| f b…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_subtype_eq_comap`：nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, 
h⟩ : Subtype p) = comap (↑) (𝓝 x)
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Function.Injective.codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι →
 α} {s : Set α} (h : ∀ (x : ι), f x ∈ s),   Function.Injective f → Function.Inje
ctive (Set.codRestri…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
protected theorem subtype (de : IsDenseEmbedding e) (p : α → Prop) :
    IsDenseEmbedding (subtypeEmb p e) where
  dense :=
    dense_iff_closure_eq.2 <| by
      ext ⟨x, hx⟩
      rw [image_eq_range] at hx
      simpa [closure_subtype, ← range_comp, (· ∘ ·)]
  injective := (de.injective.comp Subtype.coe_injective).codRestrict _
  eq_induced :=
    (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
      simp [subtypeEmb, nhds_subtype_eq_comap, de.isInducing.nhds_eq_comap, comap_comap,
        Function.comp_def]
/-
**IsDenseEmbedding.dense_image** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：dense_image (de : IsDenseEmbedding e) {s : Set α} : Dense (e '' s) ↔ Dense
 s
参数：de : IsDenseEmbedding e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.dense_image`：dense_image (di : IsDenseInducing i) {s : S
et α} : Dense (i '' s) ↔ Dense s
· 使用引理 `IsDenseEmbedding.isDenseInducing`：isDenseInducing (de : IsDenseEmbedding
 e) : IsDenseInducing e
-/
theorem dense_image (de : IsDenseEmbedding e) {s : Set α} : Dense (e '' s) ↔ Dense s :=
  de.isDenseInducing.dense_image
/-
**IsDenseEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `IsDenseEmbedding`。
形式化陈述：∀ {α : Type u_5} [inst : TopologicalSpace α], IsDenseEmbedding id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `denseRange_id`：denseRange_id : DenseRange (id : X -> X)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
protected lemma id {α : Type*} [TopologicalSpace α] : IsDenseEmbedding (id : α → α) :=
  { IsEmbedding.id with dense := denseRange_id }

end IsDenseEmbedding

/-
**Dense.isDenseEmbedding_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.isDenseEmbedding_val [TopologicalSpace α] {s : Set α} (hs : Dense s)
 : IsDenseEmbedding ((↑) : s -> α)
参数：hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Dense.denseRange_val`：Dense.denseRange_val (h : Dense s) : DenseRange ((
↑) : s -> X)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem Dense.isDenseEmbedding_val [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    IsDenseEmbedding ((↑) : s → α) :=
  { IsEmbedding.subtypeVal with dense := hs.denseRange_val }
/-
**isClosed_property** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_property [TopologicalSpace β] {e : α -> β} {p : β -> Prop} (he : 
DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p (e a)) : forall b, p 
b
参数：he : DenseRange e；hp : IsClosed { x | p x }；h : forall a, p (e a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DenseRange.closure_range`：DenseRange.closure_range (h : DenseRange f) : 
closure (range f) = univ
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isClosed_property [TopologicalSpace β] {e : α → β} {p : β → Prop} (he : DenseRange e)
    (hp : IsClosed { x | p x }) (h : ∀ a, p (e a)) : ∀ b, p b := by
  have : univ ⊆ { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
      _ ⊆ closure { b | p b } := closure_mono <| range_subset_iff.mpr h
      _ = _ := hp.closure_eq
  simpa only [univ_subset_iff, eq_univ_iff_forall, mem_ofPred]
/-
**isClosed_property2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_property2 [TopologicalSpace β] {e : α -> β} {p : β -> β -> Prop} 
(he : DenseRange e) (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : forall a₁ a₂,
 p (e a₁) (e a₂)) : forall b₁ b₂, p b₁ b₂
参数：he : DenseRange e；hp : IsClosed { q : β × β | p q.1 q.2 }；h : forall a₁ a₂, p
 (e a₁) (e a₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `DenseRange.prodMap`：DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι ->
 Y} {g : κ -> Z} (hf : DenseRange f) (hg : DenseRange g) : DenseRange (Prod.map 
f g)
-/
theorem isClosed_property2 [TopologicalSpace β] {e : α → β} {p : β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂)) : ∀ b₁ b₂, p b₁ b₂ :=
  have : ∀ q : β × β, p q.1 q.2 := isClosed_property (he.prodMap he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩
/-
**isClosed_property3** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_property3 [TopologicalSpace β] {e : α -> β} {p : β -> β -> β -> P
rop} (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 }) (
h : forall a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) : forall b₁ b₂ b₃, p b₁ b₂ b₃
参数：he : DenseRange e；hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 }；h : for
all a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `DenseRange.prodMap`：DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι ->
 Y} {g : κ -> Z} (hf : DenseRange f) (hg : DenseRange g) : DenseRange (Prod.map 
f g)
-/
theorem isClosed_property3 [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) : ∀ b₁ b₂ b₃, p b₁ b₂ b₃ :=
  have : ∀ q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.prodMap <| he.prodMap he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_elim]
/-
**DenseRange.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.induction_on [TopologicalSpace β] {e : α -> β} (he : DenseRange
 e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b }) (ih : forall a : α, p <
| e a) : p b₀
参数：he : DenseRange e；b₀ : β；hp : IsClosed { b | p b }；ih : forall a : α, p <| e 
a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
-/
theorem DenseRange.induction_on [TopologicalSpace β] {e : α → β} (he : DenseRange e) {p : β → Prop}
    (b₀ : β) (hp : IsClosed { b | p b }) (ih : ∀ a : α, p <| e a) : p b₀ :=
  isClosed_property he hp ih b₀

@[elab_as_elim]
/-
**DenseRange.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.induction_on [TopologicalSpace β] {e : α -> β} (he : DenseRange
 e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b }) (ih : forall a : α, p <
| e a) : p b₀
参数：he : DenseRange e；b₀ : β；hp : IsClosed { b | p b }；ih : forall a : α, p <| e 
a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
-/
theorem DenseRange.induction_on₂ [TopologicalSpace β] {e : α → β} {p : β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂))
    (b₁ b₂ : β) : p b₁ b₂ :=
  isClosed_property2 he hp h _ _

@[elab_as_elim]
/-
**DenseRange.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.induction_on [TopologicalSpace β] {e : α -> β} (he : DenseRange
 e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b }) (ih : forall a : α, p <
| e a) : p b₀
参数：he : DenseRange e；b₀ : β；hp : IsClosed { b | p b }；ih : forall a : α, p <| e 
a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
-/
theorem DenseRange.induction_on₃ [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) (b₁ b₂ b₃ : β) : p b₁ b₂ b₃ :=
  isClosed_property3 he hp h _ _ _

section

variable [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]
variable {f : α → β}

/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
/-
**DenseRange.equalizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.equalizer (hfd : DenseRange f) {g h : β -> γ} (hg : Continuous 
g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
参数：hfd : DenseRange f；hg : Continuous g；hh : Continuous h；H : g ∘ f = h ∘ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DenseRange.induction_on`：DenseRange.induction_on [TopologicalSpace β] {e
 : α -> β} (he : DenseRange e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b
 }) (ih : for…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
Two continuous functions to a t2-space that agree on the dense range of a functi
on are equal.
-/
theorem DenseRange.equalizer (hfd : DenseRange f) {g h : β → γ} (hg : Continuous g)
    (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h :=
  funext fun y => hfd.induction_on y (isClosed_eq hg hh) <| congr_fun H

end

-- Bourbaki GT III §3 no.4 Proposition 7 (generalised to any dense-inducing map to a regular space)
/-
**Filter.HasBasis.hasBasis_of_isDenseInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.hasBasis_of_isDenseInducing [TopologicalSpace α] [Topologi
calSpace β] [RegularSpace β] {ι : Type*} {s : ι -> Set α} {p : ι -> Prop} {x : α
} (h : (𝓝 x).HasBasis p s) {f : α -> β} (hf : IsDenseInducing f) : (𝓝 (f x)).Has
Basis p fun i => closure f '' s i
参数：h : (𝓝 x).HasBasis p s；hf : IsDenseInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hasBasis_iff`：hasBasis_iff : l.HasBasis p s ↔ forall t, t in l ↔ 
exists i, p i ∧ s i subseteq t
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDenseInducing.closure_image_mem_nhds`：closure_image_mem_nhds {s : Set 
α} {a : α} (di : IsDenseInducing i) (hs : s in 𝓝 a) : closure (i '' s) in 𝓝 (i a
)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem Filter.HasBasis.hasBasis_of_isDenseInducing [TopologicalSpace α] [TopologicalSpace β]
    [RegularSpace β] {ι : Type*} {s : ι → Set α} {p : ι → Prop} {x : α} (h : (𝓝 x).HasBasis p s)
    {f : α → β} (hf : IsDenseInducing f) : (𝓝 (f x)).HasBasis p fun i => closure <| f '' s i := by
  rw [Filter.hasBasis_iff] at h ⊢
  intro T
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' ∈ 𝓝 x := by
      rw [hf.isInducing.nhds_eq_comap x]
      exact ⟨T', hT₁, Subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).mp hT₄
    exact
      ⟨i, hi,
        (closure_mono (image_mono hi')).trans
          (Subset.trans (closure_minimal (image_preimage_subset _ _) hT₂) hT₃)⟩
  · obtain ⟨i, hi, hi'⟩ := hT
    suffices closure (f '' s i) ∈ 𝓝 (f x) by filter_upwards [this] using hi'
    replace h := (h (s i)).mpr ⟨i, hi, Subset.rfl⟩
    exact hf.closure_image_mem_nhds h
