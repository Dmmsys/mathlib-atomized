/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Topology.NhdsSet

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `IsInducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `IsCoinducing f` means the topology on `Y` is the one coinduced via `f` from the topology on `X`.
* `IsEmbedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `IsOpenEmbedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `IsClosedEmbedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `IsQuotientMap f` is the dual condition to `IsEmbedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

public section


open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X → Y} {g : Y → Z}

namespace Topology
section IsInducing

variable [TopologicalSpace Y]

/-
**Topology.IsInducing.induced** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace Y] (f : X → Y), T
opology.IsInducing f
参数：f : X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsInducing.induced (f : X → Y) : @IsInducing X Y (induced f ‹_›) _ f :=
  @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

variable [TopologicalSpace X]

@[fun_prop]
/-
**Topology.IsInducing.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsInducing id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_id`：induced_id [t : TopologicalSpace α] : t.induced id = t
-/
protected lemma IsInducing.id : IsInducing (@id X) := ⟨induced_id.symm⟩

variable [TopologicalSpace Z]

@[fun_prop]
/-
**Topology.IsInducing.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace Y]   [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSp
ace Z],   Topology.IsInducing g → Topology.IsInducing f → Topology.IsInducing (g
 ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
-/
protected lemma IsInducing.comp (hg : IsInducing g) (hf : IsInducing f) :
    IsInducing (g ∘ f) :=
  ⟨by rw [hf.eq_induced, hg.eq_induced, induced_compose]⟩
/-
**Topology.IsInducing.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing
`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace Y]   [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSp
ace Z],   Topology.IsInducing g → (Topology.IsInducing (g ∘ f) ↔ Topology.IsIndu
cing f)
参数：Topology.IsInducing (g ∘ f) ↔ Topology.IsInducing f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isInducing_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologic
alSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsInducing f ↔ tX =
 TopologicalS…
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
-/
lemma IsInducing.of_comp_iff (hg : IsInducing g) : IsInducing (g ∘ f) ↔ IsInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [isInducing_iff, hg.eq_induced, induced_compose, h.eq_induced]
/-
**Topology.IsInducing.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace Y]   [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSp
ace Z],   Continuous f → Continuous g → Topology.IsInducing (g ∘ f) → Topology.I
sInducing f
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `induced_mono`：induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g
-/
lemma IsInducing.of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsInducing (g ∘ f)) :
    IsInducing f :=
  ⟨le_antisymm hf.le_induced (by grw [hgf.eq_induced, ← induced_compose, ← hg.le_induced])⟩
/-
**Topology.isInducing_iff_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：isInducing_iff_nhds : IsInducing f ↔ forall x, 𝓝 x = comap f (𝓝 (f x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Topology.isInducing_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologic
alSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsInducing f ↔ tX =
 TopologicalS…
· 使用定理 `induced_iff_nhds_eq`：induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ :
 TopologicalSpace β] (f : β -> α) : tβ = tα.induced f ↔ forall b, 𝓝 b = comap f 
(𝓝 <| f b…
-/
lemma isInducing_iff_nhds : IsInducing f ↔ ∀ x, 𝓝 x = comap f (𝓝 (f x)) :=
  (isInducing_iff _).trans (induced_iff_nhds_eq f)

namespace IsInducing

/-
**Topology.IsInducing.nhds_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInduci
ng`。
形式化陈述：nhds_eq_comap (hf : IsInducing f) : forall x : X, 𝓝 x = comap f (𝓝 <| f x)
参数：hf : IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
-/
lemma nhds_eq_comap (hf : IsInducing f) : ∀ x : X, 𝓝 x = comap f (𝓝 <| f x) :=
  isInducing_iff_nhds.1 hf
/-
**Topology.IsInducing.basis_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInducing`
。
形式化陈述：basis_nhds {p : ι -> Prop} {s : ι -> Set Y} (hf : IsInducing f) {x : X} (h
_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s)
参数：hf : IsInducing f；h_basis : (𝓝 (f x)).HasBasis p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
-/
lemma basis_nhds {p : ι → Prop} {s : ι → Set Y} (hf : IsInducing f) {x : X}
    (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s) :=
  hf.nhds_eq_comap x ▸ h_basis.comap f
/-
**Topology.IsInducing.nhdsSet_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：nhdsSet_eq_comap (hf : IsInducing f) (s : Set X) : 𝓝ˢ s = comap f (𝓝ˢ (f '
' s))
参数：hf : IsInducing f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `Filter.comap_iSup`：comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : com
ap m (iSup f) = ⨆ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhdsSet_eq_comap (hf : IsInducing f) (s : Set X) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]
/-
**Topology.IsInducing.map_nhds_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInducing
`。
形式化陈述：map_nhds_eq (hf : IsInducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x
参数：hf : IsInducing f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nhds_induced_eq`：map_nhds_induced_eq (a : α) : map f (@nhds α (induc
ed f t) a) = 𝓝[range f] f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
-/
lemma map_nhds_eq (hf : IsInducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.eq_induced ▸ map_nhds_induced_eq x
/-
**Topology.IsInducing.map_nhds_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsIndu
cing`。
形式化陈述：map_nhds_of_mem (hf : IsInducing f) (x : X) (h : range f in 𝓝 (f x)) : (𝓝 
x).map f = 𝓝 (f x)
参数：hf : IsInducing f；x : X；h : range f in 𝓝 (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nhds_induced_of_mem`：map_nhds_induced_of_mem {a : α} (h : range f in
 𝓝 (f a)) : map f (@nhds α (induced f t) a) = 𝓝 (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
-/
lemma map_nhds_of_mem (hf : IsInducing f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) := hf.eq_induced ▸ map_nhds_induced_of_mem h
/-
**Topology.IsInducing.mapClusterPt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：mapClusterPt_iff (hf : IsInducing f) {x : X} {l : Filter X} : MapClusterPt
 (f x) l f ↔ ClusterPt x l
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mapClusterPt_iff (hf : IsInducing f) {x : X} {l : Filter X} :
    MapClusterPt (f x) l f ↔ ClusterPt x l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull', ← hf.nhds_eq_comap, map_neBot_iff]
/-
**Topology.IsInducing.image_mem_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 `Topology.I
sInducing`。
形式化陈述：image_mem_nhdsWithin (hf : IsInducing f) {x : X} {s : Set X} (hs : s in 𝓝 
x) : f '' s in 𝓝[range f] f x
参数：hf : IsInducing f；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用引理 `Topology.IsInducing.map_nhds_eq`：map_nhds_eq (hf : IsInducing f) (x : X)
 : (𝓝 x).map f = 𝓝[range f] f x
-/
lemma image_mem_nhdsWithin (hf : IsInducing f) {x : X} {s : Set X} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝[range f] f x :=
  hf.map_nhds_eq x ▸ image_mem_map hs
/-
**Topology.IsInducing.tendsto_nhds_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：tendsto_nhds_iff {f : ι -> Y} {l : Filter ι} {y : Y} (hg : IsInducing g) :
 Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y))
参数：hg : IsInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : IsInducing g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]
/-
**Topology.IsInducing.continuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：continuousAt_iff (hg : IsInducing g) {x : X} : ContinuousAt f x ↔ Continuo
usAt (g ∘ f) x
参数：hg : IsInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
-/
lemma continuousAt_iff (hg : IsInducing g) {x : X} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff
/-
**Topology.IsInducing.continuous_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInduc
ing`。
形式化陈述：continuous_iff (hg : IsInducing g) : Continuous f ↔ Continuous (g ∘ f)
参数：hg : IsInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Topology.IsInducing.continuousAt_iff`：continuousAt_iff (hg : IsInducing 
g) {x : X} : ContinuousAt f x ↔ ContinuousAt (g ∘ f) x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_iff (hg : IsInducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]
/-
**Topology.IsInducing.continuousAt_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsIn
ducing`。
形式化陈述：continuousAt_iff' (hf : IsInducing f) {x : X} (h : range f in 𝓝 (f x)) : C
ontinuousAt (g ∘ f) x ↔ ContinuousAt g (f x)
参数：hf : IsInducing f；h : range f in 𝓝 (f x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.map_nhds_of_mem`：map_nhds_of_mem (hf : IsInducing f)
 (x : X) (h : range f in 𝓝 (f x)) : (𝓝 x).map f = 𝓝 (f x)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuousAt_iff' (hf : IsInducing f) {x : X} (h : range f ∈ 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

@[fun_prop]
/-
**Topology.IsInducing.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`
。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace Y] [i
nst_1 : TopologicalSpace X],   Topology.IsInducing f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
protected lemma continuous (hf : IsInducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id
/-
**Topology.IsInducing.closure_eq_preimage_closure_image** 是 Mathlib 中的一个引理，位于命名空
间 `Topology.IsInducing`。
形式化陈述：closure_eq_preimage_closure_image (hf : IsInducing f) (s : Set X) : closur
e s = f ⁻¹' closure (f '' s)
参数：hf : IsInducing f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_induced`：closure_induced {f : α -> β} {a : α} {s : Set α} : a in
 @closure α (t.induced f) s ↔ f a in closure (f '' s)
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma closure_eq_preimage_closure_image (hf : IsInducing f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.eq_induced]
/-
**Topology.IsInducing.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducin
g`。
形式化陈述：isClosed_iff (hf : IsInducing f) {s : Set X} : IsClosed s ↔ exists t, IsCl
osed t ∧ f ⁻¹' t = s
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `isClosed_induced_iff`：isClosed_induced_iff [t : TopologicalSpace β] {s :
 Set α} {f : α -> β} : IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t 
= s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isClosed_induced_iff]
/-
**Topology.IsInducing.image_eq_isClosed_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.IsInducing`。
形式化陈述：image_eq_isClosed_inter_range (hf : IsInducing f) {s : Set X} (hs : IsClos
ed s) : exists c, IsClosed c ∧ f '' s = c inter range f
参数：hf : IsInducing f；hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem image_eq_isClosed_inter_range (hf : IsInducing f) {s : Set X} (hs : IsClosed s) :
    ∃ c, IsClosed c ∧ f '' s = c ∩ range f := by
  obtain ⟨c, hc, rfl⟩ := hf.isClosed_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩
/-
**Topology.IsInducing.isClosed_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInduci
ng`。
形式化陈述：isClosed_iff' (hf : IsInducing f) {s : Set X} : IsClosed s ↔ forall x, f x
 in closure (f '' s) -> x in s
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `isClosed_induced_iff'`：isClosed_induced_iff' {f : α -> β} {s : Set α} : 
IsClosed[t.induced f] s ↔ forall a, f a in closure (f '' s) -> a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff' (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s := by rw [hf.eq_induced, isClosed_induced_iff']
/-
**Topology.IsInducing.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsIn
ducing`。
形式化陈述：isClosed_preimage (h : IsInducing f) (s : Set Y) (hs : IsClosed s) : IsClo
sed (f ⁻¹' s)
参数：h : IsInducing f；s : Set Y；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
-/
theorem isClosed_preimage (h : IsInducing f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (isClosed_iff h).mpr ⟨s, hs, rfl⟩
/-
**Topology.IsInducing.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`
。
形式化陈述：isOpen_iff (hf : IsInducing f) {s : Set X} : IsOpen s ↔ exists t, IsOpen t
 ∧ f ⁻¹' t = s
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_iff (hf : IsInducing f) {s : Set X} :
    IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isOpen_induced_iff]
/-
**Topology.IsInducing.image_eq_isOpen_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `Top
ology.IsInducing`。
形式化陈述：image_eq_isOpen_inter_range (hf : IsInducing f) {s : Set X} (hs : IsOpen s
) : exists c, IsOpen c ∧ f '' s = c inter range f
参数：hf : IsInducing f；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem image_eq_isOpen_inter_range (hf : IsInducing f) {s : Set X} (hs : IsOpen s) :
    ∃ c, IsOpen c ∧ f '' s = c ∩ range f := by
  obtain ⟨c, hc, rfl⟩ := hf.isOpen_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩
/-
**Topology.IsInducing.setOfPred_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：setOfPred_isOpen (hf : IsInducing f) : {s : Set X | IsOpen s} = preimage f
 '' {t | IsOpen t}
参数：hf : IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
-/
theorem setOfPred_isOpen (hf : IsInducing f) :
    {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ ↦ hf.isOpen_iff

@[deprecated (since := "2026-07-09")] alias setOf_isOpen := setOfPred_isOpen
/-
**Topology.IsInducing.dense_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：dense_iff (hf : IsInducing f) {s : Set X} : Dense s ↔ forall x, f x in clo
sure (f '' s)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dense_iff (hf : IsInducing f) {s : Set X} :
    Dense s ↔ ∀ x, f x ∈ closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]
/-
**Topology.IsInducing.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsIndu
cing`。
形式化陈述：of_subsingleton [Subsingleton X] (f : X -> Y) : IsInducing f
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem of_subsingleton [Subsingleton X] (f : X → Y) : IsInducing f :=
  ⟨Subsingleton.elim _ _⟩
/-
**Topology.IsInducing.indiscreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsI
nducing`。
形式化陈述：indiscreteTopology [IndiscreteTopology Y] {f : X -> Y} (hf : IsInducing f)
 : IndiscreteTopology X where eq_top
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `induced_top`：induced_top : (⊤ : TopologicalSpace α).induced g = ⊤
-/
theorem indiscreteTopology [IndiscreteTopology Y] {f : X → Y} (hf : IsInducing f) :
    IndiscreteTopology X where
  eq_top := by
    cases IndiscreteTopology.eq_top Y
    let : TopologicalSpace Y := ⊤
    rw [hf.eq_induced, induced_top]
/-
**Topology.IsInducing.nontrivialTopology** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsI
nducing`。
形式化陈述：nontrivialTopology [NontrivialTopology X] {f : X -> Y} (hf : IsInducing f)
 : NontrivialTopology Y
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Topology.IsInducing.indiscreteTopology`：indiscreteTopology [IndiscreteTo
pology Y] {f : X -> Y} (hf : IsInducing f) : IndiscreteTopology X where eq_top
-/
theorem nontrivialTopology [NontrivialTopology X] {f : X → Y} (hf : IsInducing f) :
    NontrivialTopology Y :=
  not_imp_not.1
    (by simpa using (fun _ : IndiscreteTopology Y => hf.indiscreteTopology)) ‹NontrivialTopology X›

end IsInducing.IsInducing

namespace IsEmbedding

/-
**Topology.IsEmbedding.induced** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [t : TopologicalSpace Y], Func
tion.Injective f → Topology.IsEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
-/
lemma induced [t : TopologicalSpace Y] (hf : Injective f) :
    @IsEmbedding X Y (t.induced f) t f :=
  @IsEmbedding.mk X Y (t.induced f) t _ (.induced f) hf

alias _root_.Function.Injective.isEmbedding_induced := IsEmbedding.induced

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[fun_prop]
/-
**Topology.IsEmbedding.isInducing** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddin
g`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → Topology.IsInducing f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
lemma isInducing (hf : IsEmbedding f) : IsInducing f := hf.toIsInducing
/-
**Topology.IsEmbedding.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : X → Y),   Function.Injective f → (∀ (x : X), Filter.comap f
 (nhds (f x)) = nhds x) → Topology.IsEmbedding f
参数：f : X → Y；∀ (x : X), Filter.comap f (nhds (f x)) = nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mk' (f : X → Y) (inj : Injective f) (induced : ∀ x, comap f (𝓝 (f x)) = 𝓝 x) :
    IsEmbedding f :=
  ⟨isInducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

@[fun_prop]
/-
**Topology.IsEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsEmbedding id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
-/
protected lemma id : IsEmbedding (@id X) := ⟨.id, fun _ _ h => h⟩

@[fun_prop]
/-
**Topology.IsEmbedding.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsEmbedding g → Topology.IsEmbedding f → Topology.IsEmbedding
 (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
  { hg.isInducing.comp hf.isInducing with injective := fun _ _ h => hf.injective <| hg.injective h }
/-
**Topology.IsEmbedding.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddi
ng`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsEmbedding g → (Topology.IsEmbedding (g ∘ f) ↔ Topology.IsEm
bedding f)
参数：Topology.IsEmbedding (g ∘ f) ↔ Topology.IsEmbedding f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Topology.IsInducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : Topologi
calSpace X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma of_comp_iff (hg : IsEmbedding g) : IsEmbedding (g ∘ f) ↔ IsEmbedding f := by
  simp_rw [isEmbedding_iff, hg.isInducing.of_comp_iff, hg.injective.of_comp_iff f]
/-
**Topology.IsEmbedding.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Continuous f → Continuous g → Topology.IsEmbedding (g ∘ f) → Topology.
IsEmbedding f
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsEmbedding (g ∘ f)) :
    IsEmbedding f where
  toIsInducing := hgf.isInducing.of_comp hf hg
  injective := hgf.injective.of_comp
/-
**Topology.IsEmbedding.of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbe
dding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y} {g : Y → X},   Function.LeftInverse f g → Continuous
 f → Continuous g → Topology.IsEmbedding g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
-/
lemma of_leftInverse {f : X → Y} {g : Y → X} (h : LeftInverse f g) (hf : Continuous f)
    (hg : Continuous g) : IsEmbedding g := .of_comp hg hf <| h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse
/-
**Topology.IsEmbedding.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddi
ng`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → ∀ (x : X), Filter.map f 
(nhds x) = nhdsWithin (f x) (Set.range f)
参数：x : X；nhds x；f x；Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.map_nhds_eq`：map_nhds_eq (hf : IsInducing f) (x : X)
 : (𝓝 x).map f = 𝓝[range f] f x
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
lemma map_nhds_eq (hf : IsEmbedding f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.1.map_nhds_eq x
/-
**Topology.IsEmbedding.map_nhds_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmb
edding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → ∀ (x : X), Set.range f ∈
 nhds (f x) → Filter.map f (nhds x) = nhds (f x)
参数：x : X；f x；nhds x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.map_nhds_of_mem`：map_nhds_of_mem (hf : IsInducing f)
 (x : X) (h : range f in 𝓝 (f x)) : (𝓝 x).map f = 𝓝 (f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
lemma map_nhds_of_mem (hf : IsEmbedding f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.1.map_nhds_of_mem x h
/-
**Topology.IsEmbedding.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEm
bedding`。
形式化陈述：∀ {Y : Type u_2} {Z : Type u_3} {ι : Type u_4} {g : Y → Z} [inst : Topolog
icalSpace Y] [inst_1 : TopologicalSpace Z]   {f : ι → Y} {l : Filter ι} {y : Y},
   Topology.IsEmbedding g → (Filter.Tendsto f l (nhds y) ↔ Filter.Tendsto (g ∘ f
) l (nhds (g y)))
参数：Filter.Tendsto f l (nhds y) ↔ Filter.Tendsto (g ∘ f) l (nhds (g y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : IsEmbedding g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := hg.isInducing.tendsto_nhds_iff
/-
**Topology.IsEmbedding.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbe
dding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsEmbedding g → (Continuous f ↔ Continuous (g ∘ f))
参数：Continuous f ↔ Continuous (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma continuous_iff (hg : IsEmbedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  hg.isInducing.continuous_iff

@[fun_prop]
/-
**Topology.IsEmbedding.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddin
g`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma continuous (hf : IsEmbedding f) : Continuous f := hf.isInducing.continuous
/-
**Topology.IsEmbedding.closure_eq_preimage_closure_image** 是 Mathlib 中的一个定理，位于命名
空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → ∀ (s : Set X), closure s
 = f ⁻¹' closure (f '' s)
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
lemma closure_eq_preimage_closure_image (hf : IsEmbedding f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) :=
  hf.1.closure_eq_preimage_closure_image s

/-- The topology induced under an inclusion `f : X → Y` from a discrete topological space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`. -/
/-
**Topology.IsEmbedding.discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEm
bedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y]   [DiscreteTopology Y], Topology.IsEmbedding f → Dis
creteTopology X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.of_continuous_injective`：DiscreteTopology.of_continuous
_injective {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopolo
gy β] {f : α -> β} (hc : Conti…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…

--- 原说明 ---
The topology induced under an inclusion `f : X → Y` from a discrete topological 
space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`.
-/
lemma discreteTopology [DiscreteTopology Y] (hf : IsEmbedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.injective
/-
**Topology.IsEmbedding.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmb
edding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [Subsingleton X] (f : X → Y),   Topology.IsEmbedding f
参数：f : X → Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_subsingleton`：of_subsingleton [Subsingleton X] (f
 : X -> Y) : IsInducing f
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
-/
lemma of_subsingleton [Subsingleton X] (f : X → Y) : IsEmbedding f :=
  ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

end IsEmbedding

section IsCoinducing

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-
**Topology.isCoinducing_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f ↔ ∀ (s : Set Y), IsOpen (
f ⁻¹' s) ↔ IsOpen s
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Topology.isCoinducing_iff'`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topolo
gicalSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsCoinducing f ↔
 tY = Topologica…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `TopologicalSpace.ext_iff`：∀ {X : Type u} {t t' : TopologicalSpace X}, t 
= t' ↔ ∀ (s : Set X), IsOpen s ↔ IsOpen s
-/
lemma isCoinducing_iff : IsCoinducing f ↔ ∀ s : Set Y, IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  (isCoinducing_iff' _).trans <| eq_comm.trans TopologicalSpace.ext_iff
/-
**Topology.isCoinducing_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Topology`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f ↔ ∀ (s : Set Y), IsClosed
 (f ⁻¹' s) ↔ IsClosed s
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Topology.isCoinducing_iff`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCoinducin
g f ↔ ∀ (s : Se…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCoinducing_iff_isClosed :
    IsCoinducing f ↔ ∀ s : Set Y, IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  isCoinducing_iff.trans <| compl_surjective.forall.trans <| by simp

namespace IsCoinducing

/-
**Topology.IsCoinducing.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCo
inducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f → ∀ {s : Set Y}, IsOpen (
f ⁻¹' s) ↔ IsOpen s
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.isCoinducing_iff`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCoinducin
g f ↔ ∀ (s : Se…
-/
protected lemma isOpen_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  isCoinducing_iff.mp hf _
/-
**Topology.IsCoinducing.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Is
Coinducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f → ∀ {s : Set Y}, IsClosed
 (f ⁻¹' s) ↔ IsClosed s
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.isCoinducing_iff_isClosed`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
Coinducing f ↔ ∀ (s : Se…
-/
protected lemma isClosed_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  isCoinducing_iff_isClosed.mp hf _

alias ⟨_, of_isOpen_preimage_iff_isOpen⟩ := isCoinducing_iff

alias ⟨_, of_isClosed_preimage_iff_isClosed⟩ := isCoinducing_iff_isClosed
/-
**Topology.IsCoinducing.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCoinduc
ing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
-/
protected lemma continuous (hf : IsCoinducing f) : Continuous f where
  isOpen_preimage s hs := by rwa [hf.isOpen_preimage]

variable (X) in
@[fun_prop]
/-
**Topology.IsCoinducing.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCoinducing`。
形式化陈述：∀ (X : Type u_1) [inst : TopologicalSpace X], Topology.IsCoinducing id
参数：X : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coinduced_id`：coinduced_id [t : TopologicalSpace α] : t.coinduced id = t
-/
protected lemma id : IsCoinducing (id (α := X)) where
  eq_coinduced := coinduced_id.symm

@[fun_prop]
/-
**Topology.IsCoinducing.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCoinducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsCoinducing g → Topology.IsCoinducing f → Topology.IsCoinduc
ing (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `coinduced_compose`：coinduced_compose [tα : TopologicalSpace α] {f : α ->
 β} {g : β -> γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f)
-/
protected lemma comp (hg : IsCoinducing g) (hf : IsCoinducing f) : IsCoinducing (g.comp f) where
  eq_coinduced := by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]
/-
**Topology.IsCoinducing.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCoindu
cing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsCoinducing f → (Topology.IsCoinducing (g ∘ f) ↔ Topology.Is
Coinducing g)
参数：Topology.IsCoinducing (g ∘ f) ↔ Topology.IsCoinducing g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Topology.IsCoinducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_
3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSp
ace Y] [inst_2 :…
-/
protected lemma of_comp_iff (hf : IsCoinducing f) :
    IsCoinducing (g ∘ f) ↔ IsCoinducing g := by
  refine ⟨fun hgf ↦ .of_isOpen_preimage_iff_isOpen fun s ↦ ?_, fun hg ↦ hg.comp hf⟩
  rw [← hgf.isOpen_preimage, Set.preimage_comp, hf.isOpen_preimage]
/-
**Topology.IsCoinducing.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCoinducing
`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Continuous f → Continuous g → Topology.IsCoinducing (g ∘ f) → Topology
.IsCoinducing g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coinduced_compose`：coinduced_compose [tα : TopologicalSpace α] {f : α ->
 β} {g : β -> γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `coinduced_mono`：coinduced_mono (h : t₁ <= t₂) : t₁.coinduced f <= t₂.coi
nduced f
· 使用定理 `Continuous.coinduced_le`：Continuous.coinduced_le (h : Continuous[t, t'] 
f) : t.coinduced f <= t'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsCoinducing (g ∘ f)) :
    IsCoinducing g :=
  ⟨le_antisymm (by grw [hgf.eq_coinduced, ← coinduced_compose, hf.coinduced_le]) hg.coinduced_le⟩
/-
**Topology.IsCoinducing.isOpenMap_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.IsCoinducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsCoinducing f → Function.Injective f → 
IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
lemma isOpenMap_of_injective (hf : IsCoinducing f) (hf' : Injective f) : IsOpenMap f := by
  intro s hs
  rwa [← hf.isOpen_preimage, preimage_image_eq _ hf']

end IsCoinducing

end IsCoinducing

section IsQuotientMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-
**Topology.isQuotientMap_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Topology`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsQuotientMap f ↔ Function.Surjective f 
∧ ∀ (s : Set Y), IsClosed s ↔ IsClosed (f ⁻¹' s)
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isQuotientMap_iff_isClosed :
    IsQuotientMap f ↔ Surjective f ∧ ∀ s : Set Y, IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  simp_rw [isQuotientMap_iff, isCoinducing_iff_isClosed, and_comm, iff_comm]

namespace IsQuotientMap

@[fun_prop]
/-
**Topology.IsQuotientMap.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsQuotientMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.id`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
Topology.IsCoinducing id
-/
protected theorem id : IsQuotientMap (@id X) :=
  ⟨.id _, fun x => ⟨x, rfl⟩⟩

@[fun_prop]
/-
**Topology.IsQuotientMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotientMap`
。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsQuotientMap g → Topology.IsQuotientMap f → Topology.IsQuoti
entMap (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_
3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSp
ace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
-/
protected theorem comp (hg : IsQuotientMap g) (hf : IsQuotientMap f) : IsQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, hg.surjective.comp hf.surjective, ⟩
/-
**Topology.IsQuotientMap.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotientM
ap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Continuous f → Continuous g → Topology.IsQuotientMap (g ∘ f) → Topolog
y.IsQuotientMap g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
-/
protected theorem of_comp (hf : Continuous f) (hg : Continuous g)
    (hgf : IsQuotientMap (g ∘ f)) : IsQuotientMap g :=
  ⟨.of_comp hf hg hgf.1, hgf.2.of_comp⟩
/-
**Topology.IsQuotientMap.of_comp_of_isCoinducing** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.IsQuotientMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsQuotientMap (g ∘ f) → Topology.IsCoinducing f → Topology.Is
QuotientMap g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsCoinducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : 
Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolo
gicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
-/
theorem of_comp_of_isCoinducing (hgf : IsQuotientMap (g ∘ f)) (hf : IsCoinducing f) :
    IsQuotientMap g :=
  ⟨hf.of_comp_iff.mp hgf.1, hgf.2.of_comp⟩

@[deprecated (since := "2026-03-21")]
alias of_comp_of_eq_coinduced := of_comp_of_isCoinducing
/-
**Topology.IsQuotientMap.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuoti
entMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsQuotientMap f → (Topology.IsQuotientMap (g ∘ f) ↔ Topology.
IsQuotientMap g)
参数：Topology.IsQuotientMap (g ∘ f) ↔ Topology.IsQuotientMap g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Topology.IsQuotient
Map f ↔ Topology…
· 使用定理 `Topology.IsCoinducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : 
Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolo
gicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem of_comp_iff (hf : IsQuotientMap f) :
    IsQuotientMap (g ∘ f) ↔ IsQuotientMap g := by
  rw [isQuotientMap_iff, isQuotientMap_iff, hf.isCoinducing.of_comp_iff, hf.surjective.of_comp_iff]
/-
**Topology.IsQuotientMap.of_comp_isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.IsQuotientMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsQuotientMap f → Topology.IsQuotientMap (g ∘ f) → Topology.I
sQuotientMap g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.of_comp_of_isCoinducing`：∀ {X : Type u_1} {Y : Ty
pe u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [in
st_1 : TopologicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
-/
theorem of_comp_isQuotientMap (hf : IsQuotientMap f) (hgf : IsQuotientMap (g ∘ f)) :
    IsQuotientMap g := of_comp_of_isCoinducing hgf hf.isCoinducing
/-
**Topology.IsQuotientMap.of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotie
ntMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y] {g : Y → X},   Continuous f → Continuous g → Functio
n.LeftInverse g f → Topology.IsQuotientMap g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Typ
e u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologic
alSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X],
 Topology.IsQuotientMap id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
-/
theorem of_inverse {g : Y → X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
    IsQuotientMap g := .of_comp hf hg <| h.comp_eq_id.symm ▸ IsQuotientMap.id
/-
**Topology.IsQuotientMap.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQu
otientMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsQuotientMap f → (Continuous g ↔ Continuous (g ∘ f))
参数：Continuous g ↔ Continuous (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `coinduced_compose`：coinduced_compose [tα : TopologicalSpace α] {f : α ->
 β} {g : β -> γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem continuous_iff (hf : IsQuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.eq_coinduced, coinduced_compose]

@[fun_prop]
/-
**Topology.IsQuotientMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotie
ntMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsQuotientMap f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
protected theorem continuous (hf : IsQuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

end IsQuotientMap

end Topology.IsQuotientMap

section OpenMap
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsOpenMap

/-
**IsOpenMap.id** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
protected theorem id : IsOpenMap (@id X) := fun s hs => by rwa [image_id]
/-
**IsOpenMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z], IsOpenMap g → IsOpenMap f → IsOpenMap (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
protected theorem comp (hg : IsOpenMap g) (hf : IsOpenMap f) :
    IsOpenMap (g ∘ f) := fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)

/-- If `g ∘ f` is open, where `f` is continuous and surjective, then `g` is open. -/
/-
**IsOpenMap.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Continuous f → Function.Surjective f → IsOpenMap (g ∘ f) → IsOpenMap g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
If `g ∘ f` is open, where `f` is continuous and surjective, then `g` is open.
-/
theorem of_comp (hf : Continuous f) (f_surj : Surjective f) (h : IsOpenMap (g ∘ f)) :
    IsOpenMap g := fun s hs => by
  rw [← f_surj.image_preimage s, ← image_comp]
  exact h _ (hs.preimage hf)
/-
**IsOpenMap.isOpen_range** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (Set.range f)
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem isOpen_range (hf : IsOpenMap f) : IsOpen (range f) := by
  rw [← image_univ]
  exact hf _ isOpen_univ
/-
**IsOpenMap.image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : X} {s : Set X}, s ∈ nhds x →
 f '' s ∈ nhds (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem image_mem_nhds (hf : IsOpenMap f) {x : X} {s : Set X} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_mono hts)
/-
**IsOpenMap.range_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), Set.range f ∈ nhds (f x)
参数：x : X；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem range_mem_nhds (hf : IsOpenMap f) (x : X) : range f ∈ 𝓝 (f x) :=
  hf.isOpen_range.mem_nhds <| mem_range_self _
/-
**IsOpenMap.mapsTo_interior** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s : Set X} {t : Set Y}, Set.Maps
To f s t → Set.MapsTo f (interior s) (interior t)
参数：interior s；interior t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem mapsTo_interior (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
  mapsTo_iff_image_subset.2 <|
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)
/-
**IsOpenMap.image_interior_subset** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (s : Set X), f '' interior s ⊆ in
terior (f '' s)
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `IsOpenMap.mapsTo_interior`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s :
 Set X} {t : Se…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem image_interior_subset (hf : IsOpenMap f) (s : Set X) :
    f '' interior s ⊆ interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset
/-
**IsOpenMap.nhds_le** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhds (f x) ≤ Filter.map 
f (nhds x)
参数：x : X；f x；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
-/
theorem nhds_le (hf : IsOpenMap f) (x : X) : 𝓝 (f x) ≤ map f (𝓝 x) :=
  le_map fun _ => hf.image_mem_nhds
/-
**IsOpenMap.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : X}, ContinuousAt f x → Filte
r.map f (nhds x) = nhds (f x)
参数：nhds x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
-/
theorem map_nhds_eq (hf : IsOpenMap f) {x : X} (hf' : ContinuousAt f x) : map f (𝓝 x) = 𝓝 (f x) :=
  le_antisymm hf' (hf.nhds_le x)
/-
**IsOpenMap.map_nhdsSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → ∀ (s : Set X), Filte
r.map f (nhdsSet s) = nhdsSet (f '' s)
参数：s : Set X；nhdsSet s；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_iSup`：map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, 
map m (f i)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOpenMap.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : X},
 Continuous…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_nhdsSet_eq (hf : IsOpenMap f) (hf' : Continuous f) (s : Set X) :
    map f (𝓝ˢ s) = 𝓝ˢ (f '' s) := by
  rw [← biUnion_of_singleton s]
  simp_rw [image_iUnion, nhdsSet_iUnion, map_iSup, image_singleton, nhdsSet_singleton,
    hf.map_nhds_eq hf'.continuousAt]
/-
**IsOpenMap.of_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ Filter.map f (nhds x)) →
 IsOpenMap f
参数：∀ (x : X), nhds (f x) ≤ Filter.map f (nhds x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem of_nhds_le (hf : ∀ x, 𝓝 (f x) ≤ map f (𝓝 x)) : IsOpenMap f := fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)
/-
**IsOpenMap.of_sections** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   (∀ (x : X), ∃ g, ContinuousAt g (f x) ∧ g (f x) =
 x ∧ Function.RightInverse g f) → IsOpenMap f
参数：∀ (x : X), ∃ g, ContinuousAt g (f x) ∧ g (f x) = x ∧ Function.RightInverse g 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem of_sections
    (h : ∀ x, ∃ g : Y → X, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) : IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ ≤ map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]
/-
**IsOpenMap.of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y] {f' : Y → X},   Continuous f' → Function.LeftInverse
 f f' → Function.RightInverse f f' → IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_sections`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), ∃ g, Continu
ousAt g (f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsOpenMap f :=
  of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩

/-- A continuous surjective open map is a quotient map. -/
/-
**IsOpenMap.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → Function.Surjective 
f → Topology.IsQuotientMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Topology.IsQuotient
Map f ↔ Topology…
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
A continuous surjective open map is a quotient map.
-/
theorem isQuotientMap (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f) :
    IsQuotientMap f := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, surj⟩
  exact ⟨fun h => surj.image_preimage s ▸ open_map _ h, fun h => h.preimage cont⟩
/-
**IsOpenMap.interior_preimage_subset_preimage_interior** 是 Mathlib 中的一个定理，位于命名空间
 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s : Set Y}, interior (f ⁻¹' s) ⊆
 f ⁻¹' interior s
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.mapsTo_interior`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s :
 Set X} {t : Se…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set Y} :
    interior (f ⁻¹' s) ⊆ f ⁻¹' interior s :=
  hf.mapsTo_interior (mapsTo_preimage _ _)
/-
**IsOpenMap.preimage_interior_eq_interior_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Is
OpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → ∀ (s : Set Y), f ⁻¹'
 interior s = interior (f ⁻¹' s)
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `IsOpenMap.interior_preimage_subset_preimage_interior`：∀ {X : Type u_1} {
Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace
 Y],   IsOpenMap f → ∀ {s : Set Y}, interi…
-/
theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
    (s : Set Y) : f ⁻¹' interior s = interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)
/-
**IsOpenMap.preimage_closure_subset_closure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `
IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' closure s ⊆ cl
osure (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsOpenMap.interior_preimage_subset_preimage_interior`：∀ {X : Type u_1} {
Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace
 Y],   IsOpenMap f → ∀ {s : Set Y}, interi…
-/
theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' closure s ⊆ closure (f ⁻¹' s) := by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]
/-
**IsOpenMap.preimage_closure_eq_closure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsOp
enMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → ∀ (s : Set Y), f ⁻¹'
 closure s = closure (f ⁻¹' s)
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsOpenMap.preimage_closure_subset_closure_preimage`：∀ {X : Type u_1} {Y 
: Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y
],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' …
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
-/
theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' closure s = closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)
/-
**IsOpenMap.preimage_closure_image** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Function.Injective f → Continuous f
 → ∀ (s : Set X), IsClosed s → f ⁻¹' closure (f '' s) = s
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
lemma preimage_closure_image (h₁ : IsOpenMap f) (h₂ : Function.Injective f)
    (h₃ : Continuous f) (s : Set X) (hs' : IsClosed s) : f ⁻¹' closure (f '' s) = s := by
  rw [h₁.preimage_closure_eq_closure_preimage h₃, Set.preimage_image_eq _ h₂, hs'.closure_eq]
/-
**IsOpenMap.preimage_frontier_subset_frontier_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' frontier s ⊆ f
rontier (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `IsOpenMap.preimage_closure_subset_closure_preimage`：∀ {X : Type u_1} {Y 
: Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y
],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' …
-/
theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' frontier s ⊆ frontier (f ⁻¹' s) := by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using!
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage
/-
**IsOpenMap.preimage_frontier_eq_frontier_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Is
OpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → ∀ (s : Set Y), f ⁻¹'
 frontier s = frontier (f ⁻¹' s)
参数：s : Set Y；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' frontier s = frontier (f ⁻¹' s) := by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]
/-
**IsOpenMap.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [h : IsEmpty X] (f : X → Y),   IsOpenMap f
参数：f : X → Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
-/
theorem of_isEmpty [h : IsEmpty X] (f : X → Y) : IsOpenMap f := of_nhds_le h.elim
/-
**IsOpenMap.clusterPt_comap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : X} {l : Filter Y}, ClusterPt
 (f x) l → ClusterPt x (Filter.comap f l)
参数：f x；Filter.comap f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `ClusterPt.neBot`：ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : Ne
Bot (𝓝 x ⊓ F)
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
-/
theorem clusterPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : ClusterPt (f x) l) :
    ClusterPt x (comap f l) := by
  rw [ClusterPt, ← map_neBot_iff, Filter.push_pull]
  exact h.neBot.mono <| inf_le_inf_right _ <| hf.nhds_le _
/-
**IsOpenMap.accPt_comap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : X} {l : Filter Y}, AccPt (f 
x) l → AccPt x (Filter.comap f l)
参数：f x；Filter.comap f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `IsOpenMap.clusterPt_comap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x :
 X} {l : Filter…
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem accPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : AccPt (f x) l) :
    AccPt x (comap f l) := by
  rw [accPt_iff_clusterPt] at h ⊢
  apply (hf.clusterPt_comap h).mono
  rw [comap_inf, comap_principal, preimage_compl]
  exact inf_le_inf_right (comap f l) (by simp)
/-
**IsOpenMap.clusterPt_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f → Continuous f → ∀ {x : X} {l : Filte
r Y}, ClusterPt x (Filter.comap f l) ↔ ClusterPt (f x) l
参数：Filter.comap f l；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.map`：ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : Cluste
rPt x lx) (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `IsOpenMap.clusterPt_comap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x :
 X} {l : Filter…
-/
theorem clusterPt_comap_iff (hf : IsOpenMap f) (hfc : Continuous f) {x : X} {l : Filter Y} :
    ClusterPt x (comap f l) ↔ ClusterPt (f x) l :=
  ⟨fun h => h.map hfc.continuousAt tendsto_comap, hf.clusterPt_comap⟩

end IsOpenMap

/-- A map is open if and only if the `Set.kernImage` of every *closed* set is closed.

One way to understand this result is that `f : X → Y` is open if and only if its fibers vary in a
**lower hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y` such that
`(f ⁻¹' {y} ∩ U).Nonempty` is open in `Y`. See `isOpenMap_iff_lowerHemicontinuous`. -/
/-
**isOpenMap_iff_kernImage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ {u : Set X}, IsClosed u → IsClose
d (Set.kernImage f u)
参数：Set.kernImage f u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpenMap.eq_1`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] 
[inst_1 : TopologicalSpace Y] (f : X → Y),   IsOpenMap f = ∀ (U : Set X), IsOpen
 U →…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A map is open if and only if the `Set.kernImage` of every *closed* set is closed
.

One way to understand this result is that `f : X → Y` is open if and only if its
 fibers vary in a
**lower hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y
` such that
`(f ⁻¹' {y} ∩ U).Nonempty` is open in `Y`. See `isOpenMap_iff_lowerHemicontinuou
s`.
-/
lemma isOpenMap_iff_kernImage :
    IsOpenMap f ↔ ∀ {u : Set X}, IsClosed u → IsClosed (kernImage f u) := by
  rw [IsOpenMap, compl_surjective.forall]
  simp [kernImage_eq_compl]
/-
**isOpenMap_iff_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X), nhds (f x) ≤ Filter.map 
f (nhds x)
参数：x : X；f x；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
-/
theorem isOpenMap_iff_nhds_le : IsOpenMap f ↔ ∀ x : X, 𝓝 (f x) ≤ (𝓝 x).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩
/-
**isOpenMap_iff_clusterPt_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X) (l : Filter Y), ClusterPt
 (f x) l → ClusterPt x (Filter.comap f l)
参数：x : X；l : Filter Y；f x；Filter.comap f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.clusterPt_comap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x :
 X} {l : Filter…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `mem_interior_iff_not_clusterPt_compl`：mem_interior_iff_not_clusterPt_com
pl : x in interior s ↔ ¬ClusterPt x (𝓟 sᶜ)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
-/
theorem isOpenMap_iff_clusterPt_comap :
    IsOpenMap f ↔ ∀ x l, ClusterPt (f x) l → ClusterPt x (comap f l) := by
  refine ⟨fun hf _ _ ↦ hf.clusterPt_comap, fun h ↦ ?_⟩
  simp only [isOpenMap_iff_nhds_le, le_map_iff]
  intro x s hs
  contrapose hs
  rw [← mem_interior_iff_mem_nhds, mem_interior_iff_not_clusterPt_compl, not_not] at hs ⊢
  exact (h _ _ hs).mono <| by simp [subset_preimage_image]
/-
**isOpenMap_iff_image_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (s : Set X), f '' interior s ⊆ in
terior (f '' s)
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem isOpenMap_iff_image_interior : IsOpenMap f ↔ ∀ s, f '' interior s ⊆ interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_isOpen.mp <| by simpa only [hu.interior_eq] using hs u⟩

/-- A map is open if and only if the `Set.kernImage` of every *closed* set is closed. -/
/-
**isOpenMap_iff_closure_kernImage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ {s : Set X}, closure (Set.kernIma
ge f s) ⊆ Set.kernImage f (closure s)
参数：Set.kernImage f s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpenMap_iff_image_interior`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y
} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (
s : Set X), f '' i…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A map is open if and only if the `Set.kernImage` of every *closed* set is closed
.
-/
lemma isOpenMap_iff_closure_kernImage :
    IsOpenMap f ↔ ∀ {s : Set X}, closure (kernImage f s) ⊆ kernImage f (closure s) := by
  rw [isOpenMap_iff_image_interior, compl_surjective.forall]
  simp [kernImage_eq_compl]

/-- An inducing map with an open range is an open map. -/
/-
**Topology.IsInducing.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsInducing f → IsOpen (Set.range f) → Is
OpenMap f
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Topology.IsInducing.map_nhds_of_mem`：map_nhds_of_mem (hf : IsInducing f)
 (x : X) (h : range f in 𝓝 (f x)) : (𝓝 x).map f = 𝓝 (f x)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
An inducing map with an open range is an open map.
-/
protected lemma Topology.IsInducing.isOpenMap (hi : IsInducing f) (ho : IsOpen (range f)) :
    IsOpenMap f :=
  IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge

/-- Preimage of a dense set under an open map is dense. -/
/-
**Dense.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Dense`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y] {s : Set Y},   Dense s → IsOpenMap f → Dense (f ⁻¹' 
s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_closure_subset_closure_preimage`：∀ {X : Type u_1} {Y 
: Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y
],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' …

--- 原说明 ---
Preimage of a dense set under an open map is dense.
-/
protected theorem Dense.preimage {s : Set Y} (hs : Dense s) (hf : IsOpenMap f) :
    Dense (f ⁻¹' s) := fun x ↦
  hf.preimage_closure_subset_closure_preimage <| hs (f x)

end OpenMap

section IsClosedMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedMap
open Function

/-
**IsClosedMap.id** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
protected theorem id : IsClosedMap (@id X) := fun s hs => by rwa [image_id]
/-
**IsClosedMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z], IsClosedMap g → IsClosedMap f → IsClosedMap (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
protected theorem comp (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)
/-
**IsClosedMap.of_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Function.Surjective f → Continuous f → IsClosedMap (g ∘ f) → IsClosedM
ap g
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
-/
protected theorem of_comp_surjective (hf : Surjective f) (hf' : Continuous f)
    (hfg : IsClosedMap (g ∘ f)) : IsClosedMap g := by
  intro K hK
  rw [← image_preimage_eq K hf, ← image_comp]
  exact hfg _ (hK.preimage hf')
/-
**IsClosedMap.closure_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f → ∀ (s : Set X), closure (f '' s) ⊆
 f '' closure s
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem closure_image_subset (hf : IsClosedMap f) (s : Set X) :
    closure (f '' s) ⊆ f '' closure s :=
  closure_minimal (image_mono subset_closure) (hf _ isClosed_closure)
/-
**IsClosedMap.of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y] {f' : Y → X},   Continuous f' → Function.LeftInverse
 f f' → Function.RightInverse f f' → IsClosedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
-/
theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsClosedMap f := fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h
/-
**IsClosedMap.of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   (∀ (s : Set X), IsClosed s → s.Nonempty → IsClose
d (f '' s)) → IsClosedMap f
参数：∀ (s : Set X), IsClosed s → s.Nonempty → IsClosed (f '' s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem of_nonempty (h : ∀ s, IsClosed s → s.Nonempty → IsClosed (f '' s)) :
    IsClosedMap f := by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s
/-
**IsClosedMap.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f → IsClosed (Set.range f)
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem isClosed_range (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ isClosed_univ
/-
**IsClosedMap.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f → Continuous f → Function.Surjectiv
e f → Topology.IsQuotientMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isQuotientMap_iff_isClosed`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sQuotientMap f ↔ Function…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
-/
theorem isQuotientMap (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : IsQuotientMap f :=
  isQuotientMap_iff_isClosed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

end IsClosedMap

/-- A map is closed if and only if the `Set.kernImage` of every *open* set is open.

One way to understand this result is that `f : X → Y` is closed if and only if its fibers vary in an
**upper hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y` such that
`f ⁻¹' {y} ⊆ U` is open in `Y`. See `isClosedMap_iff_upperHemicontinuous`. -/
/-
**isClosedMap_iff_kernImage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ {u : Set X}, IsOpen u → IsOpen 
(Set.kernImage f u)
参数：Set.kernImage f u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosedMap.eq_1`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X
] [inst_1 : TopologicalSpace Y] (f : X → Y),   IsClosedMap f = ∀ (U : Set X), Is
Closed…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A map is closed if and only if the `Set.kernImage` of every *open* set is open.

One way to understand this result is that `f : X → Y` is closed if and only if i
ts fibers vary in an
**upper hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y
` such that
`f ⁻¹' {y} ⊆ U` is open in `Y`. See `isClosedMap_iff_upperHemicontinuous`.
-/
lemma isClosedMap_iff_kernImage :
    IsClosedMap f ↔ ∀ {u : Set X}, IsOpen u → IsOpen (kernImage f u) := by
  rw [IsClosedMap, compl_surjective.forall]
  simp [kernImage_eq_compl]
/-
**Topology.IsInducing.isClosedMap** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInducing
`。
形式化陈述：Topology.IsInducing.isClosedMap (hf : IsInducing f) (h : IsClosed (range f
)) : IsClosedMap f
参数：hf : IsInducing f；h : IsClosed (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
-/
lemma Topology.IsInducing.isClosedMap (hf : IsInducing f) (h : IsClosed (range f)) :
    IsClosedMap f := by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h
/-
**isClosedMap_iff_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ (s : Set X), closure (f '' s) ⊆
 f '' closure s
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.closure_image_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → ∀ (s : Set X), clos…
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem isClosedMap_iff_closure_image :
    IsClosedMap f ↔ ∀ s, closure (f '' s) ⊆ f '' closure s :=
  ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
    isClosed_of_closure_subset <|
      calc
        closure (f '' c) ⊆ f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩
/-
**isClosedMap_iff_kernImage_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ {s : Set X}, Set.kernImage f (i
nterior s) ⊆ interior (Set.kernImage f s)
参数：interior s；Set.kernImage f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosedMap_iff_closure_image`：∀ {X : Type u_1} {Y : Type u_2} {f : X → 
Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f ↔ 
∀ (s : Set X), clos…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosedMap_iff_kernImage_interior :
    IsClosedMap f ↔ ∀ {s : Set X}, kernImage f (interior s) ⊆ interior (kernImage f s) := by
  rw [isClosedMap_iff_closure_image, compl_surjective.forall]
  simp [kernImage_eq_compl]

/-- A map `f : X → Y` is closed if and only if for all sets `s`, any cluster point of `f '' s` is
the image by `f` of some cluster point of `s`.
If you require this for all filters instead of just principal filters, and also that `f` is
continuous, you get the notion of **proper map**. See `isProperMap_iff_clusterPt`. -/
/-
**isClosedMap_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔     ∀ (s : Set X) (y : Y), MapClu
sterPt y (Filter.principal s) f → ∃ x, f x = y ∧ ClusterPt x (Filter.principal s
)
参数：s : Set X；y : Y；Filter.principal s；Filter.principal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A map `f : X → Y` is closed if and only if for all sets `s`, any cluster point o
f `f '' s` is
the image by `f` of some cluster point of `s`.
If you require this for all filters instead of just principal filters, and also 
that `f` is
continuous, you get the notion of **proper map**. See `isProperMap_iff_clusterPt
`.
-/
theorem isClosedMap_iff_clusterPt :
    IsClosedMap f ↔ ∀ s y, MapClusterPt y (𝓟 s) f → ∃ x, f x = y ∧ ClusterPt x (𝓟 s) := by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]
/-
**isClosedMap_iff_comap_nhdsSet_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ {s : Set Y}, Filter.comap f (nh
dsSet s) ≤ nhdsSet (f ⁻¹' s)
参数：nhdsSet s；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem isClosedMap_iff_comap_nhdsSet_le :
    IsClosedMap f ↔ ∀ {s : Set Y}, comap f (𝓝ˢ s) ≤ 𝓝ˢ (f ⁻¹' s) := by
  simp_rw [Filter.le_def, mem_comap'', ← subset_interior_iff_mem_nhdsSet,
    ← subset_kernImage_iff, isClosedMap_iff_kernImage_interior]
  exact ⟨fun H s t hst ↦ hst.trans H, fun H s ↦ H _ subset_rfl⟩

alias ⟨IsClosedMap.comap_nhdsSet_le, _⟩ := isClosedMap_iff_comap_nhdsSet_le
/-
**isClosedMap_iff_comap_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f ↔ ∀ {y : Y}, Filter.comap f (nhds y
) ≤ nhdsSet (f ⁻¹' {y})
参数：nhds y；f ⁻¹' {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosedMap_iff_comap_nhdsSet_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 ↔ ∀ {s : Set Y}, Filt…
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.comap_iSup`：comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : com
ap m (iSup f) = ⨆ i, comap m (f i)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
-/
theorem isClosedMap_iff_comap_nhds_le :
    IsClosedMap f ↔ ∀ {y : Y}, comap f (𝓝 y) ≤ 𝓝ˢ (f ⁻¹' {y}) := by
  rw [isClosedMap_iff_comap_nhdsSet_le]
  constructor
  · exact fun H y ↦ nhdsSet_singleton (x := y) ▸ H
  · intro H s
    rw [← Set.biUnion_of_singleton s]
    simp_rw [preimage_iUnion, nhdsSet_iUnion, comap_iSup, nhdsSet_singleton]
    exact iSup₂_mono fun _ _ ↦ H

alias ⟨IsClosedMap.comap_nhds_le, _⟩ := isClosedMap_iff_comap_nhds_le
/-
**IsClosedMap.comap_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：IsClosedMap.comap_nhds_eq (hf : IsClosedMap f) (hf' : Continuous f) (y : Y
) : comap f (𝓝 y) = 𝓝ˢ (f ⁻¹' {y})
参数：hf : IsClosedMap f；hf' : Continuous f；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosedMap_iff_comap_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → 
Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f ↔ 
∀ {y : Y}, Filter.c…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `nhdsSet_le`：nhdsSet_le : 𝓝ˢ s <= f ↔ forall x in s, 𝓝 x <= f
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
theorem IsClosedMap.comap_nhds_eq (hf : IsClosedMap f) (hf' : Continuous f) (y : Y) :
    comap f (𝓝 y) = 𝓝ˢ (f ⁻¹' {y}) :=
  le_antisymm (isClosedMap_iff_comap_nhds_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhds`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx ↦ hx ▸ (hf'.tendsto x).le_comap)
/-
**IsClosedMap.comap_nhdsSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：IsClosedMap.comap_nhdsSet_eq (hf : IsClosedMap f) (hf' : Continuous f) (s 
: Set Y) : comap f (𝓝ˢ s) = 𝓝ˢ (f ⁻¹' s)
参数：hf : IsClosedMap f；hf' : Continuous f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosedMap_iff_comap_nhdsSet_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 ↔ ∀ {s : Set Y}, Filt…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `nhdsSet_le`：nhdsSet_le : 𝓝ˢ s <= f ↔ forall x in s, 𝓝 x <= f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
-/
theorem IsClosedMap.comap_nhdsSet_eq (hf : IsClosedMap f) (hf' : Continuous f) (s : Set Y) :
    comap f (𝓝ˢ s) = 𝓝ˢ (f ⁻¹' s) :=
  le_antisymm (isClosedMap_iff_comap_nhdsSet_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhdsSet`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx ↦ (hf'.tendsto x).le_comap.trans (comap_mono (nhds_le_nhdsSet hx)))

/-- Assume `f` is a closed map. If some property `p` holds around every point in the fiber of `f`
at `y₀`, then for any `y` close enough to `y₀` we have that `p` holds on the fiber at `y`. -/
/-
**IsClosedMap.eventually_nhds_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInduci
ng`。
形式化陈述：IsClosedMap.eventually_nhds_fiber (hf : IsClosedMap f) {p : X -> Prop} (y₀
 : Y) (H : forall x₀ in f ⁻¹' {y₀}, forallᶠ x in 𝓝 x₀, p x) : forallᶠ y in 𝓝 y₀,
 forall x in f ⁻¹' {y}, p x
参数：hf : IsClosedMap f；y₀ : Y；H : forall x₀ in f ⁻¹' {y₀}, forallᶠ x in 𝓝 x₀, p x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `IsClosedMap.comap_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → ∀ {y
 : Y}, Filter.c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a

--- 原说明 ---
Assume `f` is a closed map. If some property `p` holds around every point in the
 fiber of `f`
at `y₀`, then for any `y` close enough to `y₀` we have that `p` holds on the fib
er at `y`.
-/
theorem IsClosedMap.eventually_nhds_fiber (hf : IsClosedMap f) {p : X → Prop} (y₀ : Y)
    (H : ∀ x₀ ∈ f ⁻¹' {y₀}, ∀ᶠ x in 𝓝 x₀, p x) :
    ∀ᶠ y in 𝓝 y₀, ∀ x ∈ f ⁻¹' {y}, p x := by
  rw [← eventually_nhdsSet_iff_forall] at H
  replace H := H.filter_mono hf.comap_nhds_le
  rwa [eventually_comap] at H

/-- Assume `f` is a closed map. If there are points `y` arbitrarily close to `y₀` such that `p`
holds for at least some `x ∈ f ⁻¹' {y}`, then one can find `x₀ ∈ f ⁻¹' {y₀}` such that there
are points `x` arbitrarily close to `x₀` which satisfy `p`. -/
/-
**IsClosedMap.frequently_nhds_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInduci
ng`。
形式化陈述：IsClosedMap.frequently_nhds_fiber (hf : IsClosedMap f) {p : X -> Prop} (y₀
 : Y) (H : existsᶠ y in 𝓝 y₀, exists x in f ⁻¹' {y}, p x) : exists x₀ in f ⁻¹' {
y₀}, existsᶠ x in 𝓝 x₀, p x
参数：hf : IsClosedMap f；y₀ : Y；H : existsᶠ y in 𝓝 y₀, exists x in f ⁻¹' {y}, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosedMap.eventually_nhds_fiber`：IsClosedMap.eventually_nhds_fiber (hf
 : IsClosedMap f) {p : X -> Prop} (y₀ : Y) (H : forall x₀ in f ⁻¹' {y₀}, forallᶠ
 x in 𝓝 x₀, p x) : fora…

--- 原说明 ---
Assume `f` is a closed map. If there are points `y` arbitrarily close to `y₀` su
ch that `p`
holds for at least some `x ∈ f ⁻¹' {y}`, then one can find `x₀ ∈ f ⁻¹' {y₀}` suc
h that there
are points `x` arbitrarily close to `x₀` which satisfy `p`.
-/
theorem IsClosedMap.frequently_nhds_fiber (hf : IsClosedMap f) {p : X → Prop} (y₀ : Y)
    (H : ∃ᶠ y in 𝓝 y₀, ∃ x ∈ f ⁻¹' {y}, p x) :
    ∃ x₀ ∈ f ⁻¹' {y₀}, ∃ᶠ x in 𝓝 x₀, p x := by
  /-
  Note: this result could also be seen as a reformulation of `isClosedMap_iff_clusterPt`.
  One would then be able to deduce the `eventually` statement,
  and then go back to `isClosedMap_iff_comap_nhdsSet_le`.
  Ultimately, this makes no difference.
  -/
  contrapose! H
  exact hf.eventually_nhds_fiber y₀ H
/-
**IsClosedMap.closure_image_eq_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology
.IsInducing`。
形式化陈述：IsClosedMap.closure_image_eq_of_continuous (f_closed : IsClosedMap f) (f_c
ont : Continuous f) (s : Set X) : closure (f '' s) = f '' closure s
参数：f_closed : IsClosedMap f；f_cont : Continuous f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsClosedMap.closure_image_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → ∀ (s : Set X), clos…
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
-/
theorem IsClosedMap.closure_image_eq_of_continuous
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)
/-
**IsClosedMap.lift'_closure_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsClosedMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   IsClosedMap f → Continuous f → ∀ (F : Filter X), 
(Filter.map f F).lift' closure = Filter.map f (F.lift' closure)
参数：F : Filter X；Filter.map f F；F.lift' closure。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_lift'_eq2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f 
: Filter α} {g : Set β → Set γ} {m : α → β},   Monotone g → (Filter.map m f).lif
t' g = f.l…
· 使用定理 `monotone_closure`：monotone_closure (X : Type*) [TopologicalSpace X] : Mo
notone (@closure X _)
· 使用定理 `Filter.map_lift'_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 Filter α} {h : Set α → Set β} {m : β → γ},   Monotone h → Filter.map m (f.lift'
 h) = f.l…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosedMap.closure_image_eq_of_continuous`：IsClosedMap.closure_image_eq
_of_continuous (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) : 
closure (f '' s) = f '' closure …
-/
theorem IsClosedMap.lift'_closure_map_eq
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter X) :
    (map f F).lift' closure = map f (F.lift' closure) := by
  rw [map_lift'_eq2 (monotone_closure Y), map_lift'_eq (monotone_closure X)]
  congr 1
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s
/-
**IsClosedMap.mapClusterPt_iff_lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed
Map`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y] {F : Filter X},   IsClosedMap f → Continuous f → ∀ {
y : Y}, MapClusterPt y F f ↔ (F.lift' closure ⊓ Filter.principal (f ⁻¹' {y})).Ne
Bot
参数：F.lift' closure ⊓ Filter.principal (f ⁻¹' {y})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MapClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] {ι : Typ
e u_3} (x : X) (F : Filter ι) (u : ι → X),   MapClusterPt x F u = ClusterPt x (F
ilter.m…
· 使用定理 `clusterPt_iff_lift'_closure'`：∀ {X : Type u} [inst : TopologicalSpace X]
 {x : X} {F : Filter X}, ClusterPt x F ↔ (F.lift' closure ⊓ pure x).NeBot
· 使用定理 `IsClosedMap.lift'_closure_map_eq`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → Continuous f → ∀ (F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsClosedMap.mapClusterPt_iff_lift'_closure
    {F : Filter X} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : Y} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt, clusterPt_iff_lift'_closure', f_closed.lift'_closure_map_eq f_cont,
      ← comap_principal, ← map_neBot_iff f, Filter.push_pull, principal_singleton]

end IsClosedMap

namespace Topology
section IsOpenEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y]

@[fun_prop]
/-
**Topology.IsOpenEmbedding.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpe
nEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → Topology.IsEmbedding
 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma IsOpenEmbedding.isEmbedding (hf : IsOpenEmbedding f) : IsEmbedding f := hf.toIsEmbedding
/-
**Topology.IsOpenEmbedding.isInducing** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpen
Embedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → Topology.IsInducing 
f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
-/
lemma IsOpenEmbedding.isInducing (hf : IsOpenEmbedding f) : IsInducing f :=
  hf.isEmbedding.isInducing
/-
**Topology.IsOpenEmbedding.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenE
mbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → 
Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsInduc
ing f → IsOpen (Set…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
lemma IsOpenEmbedding.isOpenMap (hf : IsOpenEmbedding f) : IsOpenMap f :=
  hf.isEmbedding.isInducing.isOpenMap hf.isOpen_range
/-
**Topology.IsOpenEmbedding.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpe
nEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → ∀ (x : X), Filter.ma
p f (nhds x) = nhds (f x)
参数：x : X；nhds x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.map_nhds_of_mem`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsEmbedding f → ∀ (x : X),…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem IsOpenEmbedding.map_nhds_eq (hf : IsOpenEmbedding f) (x : X) :
    map f (𝓝 x) = 𝓝 (f x) :=
  hf.isEmbedding.map_nhds_of_mem _ <| hf.isOpen_range.mem_nhds <| mem_range_self _
/-
**Topology.IsOpenEmbedding.isOpen_iff_image_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → ∀ {s : Set X}, IsOpe
n s ↔ IsOpen (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
-/
lemma IsOpenEmbedding.isOpen_iff_image_isOpen (hf : IsOpenEmbedding f) {s : Set X} :
    IsOpen s ↔ IsOpen (f '' s) where
  mp := hf.isOpenMap s
  mpr h := by
    convert! ← h.preimage hf.isEmbedding.continuous
    apply preimage_image_eq _ hf.injective
/-
**Topology.IsOpenEmbedding.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
IsOpenEmbedding`。
形式化陈述：∀ {Y : Type u_2} {Z : Type u_3} {ι : Type u_4} {g : Y → Z} [inst : Topolog
icalSpace Y] [inst_1 : TopologicalSpace Z]   {f : ι → Y} {l : Filter ι} {y : Y},
   Topology.IsOpenEmbedding g → (Filter.Tendsto f l (nhds y) ↔ Filter.Tendsto (g
 ∘ f) l (nhds (g y)))
参数：Filter.Tendsto f l (nhds y) ↔ Filter.Tendsto (g ∘ f) l (nhds (g y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
-/
theorem IsOpenEmbedding.tendsto_nhds_iff [TopologicalSpace Z] {f : ι → Y} {l : Filter ι} {y : Y}
    (hg : IsOpenEmbedding g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.isEmbedding.tendsto_nhds_iff
/-
**Topology.IsOpenEmbedding.tendsto_nhds_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Topology
.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y],   Topology.IsOpenEmbed
ding f →     ∀ {l : Filter Z} {x : X}, Filter.Tendsto (g ∘ f) (nhds x) l ↔ Filte
r.Tendsto g (nhds (f x)) l
参数：g ∘ f；nhds x；nhds (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsOpenEmbedding.tendsto_nhds_iff' (hf : IsOpenEmbedding f) {l : Filter Z} {x : X} :
    Tendsto (g ∘ f) (𝓝 x) l ↔ Tendsto g (𝓝 (f x)) l := by
  rw [Tendsto, ← map_map, hf.map_nhds_eq]; rfl
/-
**Topology.IsOpenEmbedding.continuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsOpenEmbedding f → ∀ {x : X}, ContinuousAt (g ∘ f) x ↔ Conti
nuousAt g (f x)
参数：g ∘ f；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.tendsto_nhds_iff'`：∀ {X : Type u_1} {Y : Type u
_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1
 : TopologicalSpace Y],   Topolo…
-/
theorem IsOpenEmbedding.continuousAt_iff [TopologicalSpace Z] (hf : IsOpenEmbedding f) {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'

@[fun_prop]
/-
**Topology.IsOpenEmbedding.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpen
Embedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
-/
theorem IsOpenEmbedding.continuous (hf : IsOpenEmbedding f) : Continuous f :=
  hf.isEmbedding.continuous
/-
**Topology.IsOpenEmbedding.isOpen_iff_preimage_isOpen** 是 Mathlib 中的一个定理，位于命名空间 
`Topology.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → ∀ {s : Set Y}, s ⊆ S
et.range f → (IsOpen s ↔ IsOpen (f ⁻¹' s))
参数：IsOpen s ↔ IsOpen (f ⁻¹' s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsOpenEmbedding.isOpen_iff_preimage_isOpen (hf : IsOpenEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.isOpen_iff_image_isOpen, image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

@[fun_prop]
/-
**Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → IsOpenMap f → Topology.I
sOpenEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
-/
lemma IsOpenEmbedding.of_isEmbedding_isOpenMap (h₁ : IsEmbedding f) (h₂ : IsOpenMap f) :
    IsOpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩

/-- A surjective embedding is an `IsOpenEmbedding`. -/
/-
**Topology.IsEmbedding.isOpenEmbedding_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → Function.Surjective f → 
Topology.IsOpenEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ

--- 原说明 ---
A surjective embedding is an `IsOpenEmbedding`.
-/
lemma IsEmbedding.isOpenEmbedding_of_surjective (hf : IsEmbedding f) (hsurj : f.Surjective) :
    IsOpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

alias IsOpenEmbedding.of_isEmbedding := IsEmbedding.isOpenEmbedding_of_surjective
/-
**Topology.isOpenEmbedding_iff_isEmbedding_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `
Topology`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f ↔ Topology.IsEmbedding
 f ∧ IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap`：∀ {X : Type u_1} {Y :
 Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
,   Topology.IsEmbedding f → IsOpenMap …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isOpenEmbedding_iff_isEmbedding_isOpenMap : IsOpenEmbedding f ↔ IsEmbedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩
/-
**Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap** 是 Mathlib 中的一个定理，
位于命名空间 `Topology.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Continuous f → Function.Injective f → IsOpenMap f
 → Topology.IsOpenEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
-/
theorem IsOpenEmbedding.of_continuous_injective_isOpenMap
    (h₁ : Continuous f) (h₂ : Injective f) (h₃ : IsOpenMap f) : IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, isInducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))
/-
**Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap** 是 Mathlib 中的一个定理
，位于命名空间 `Topology`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f ↔ Continuous f ∧ Funct
ion.Injective f ∧ IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isOpenEmbedding_iff_continuous_injective_isOpenMap :
    IsOpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.injective, h.isOpenMap⟩, fun h =>
    .of_continuous_injective_isOpenMap h.1 h.2.1 h.2.2⟩

namespace IsOpenEmbedding
variable [TopologicalSpace Z]

@[fun_prop]
/-
**Topology.IsOpenEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmbeddin
g`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsOpenEmbedding id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
protected lemma id : IsOpenEmbedding (@id X) := ⟨.id, IsOpenMap.id.isOpen_range⟩

@[fun_prop]
/-
**Topology.IsOpenEmbedding.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmbedd
ing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsOpenEmbedding g → Topology.IsOpenEmbedding f → Topology.IsO
penEmbedding (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
protected lemma comp (hg : IsOpenEmbedding g)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩
/-
**Topology.IsOpenEmbedding.isOpenMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsO
penEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsOpenEmbedding g → (IsOpenMap f ↔ IsOpenMap (g ∘ f))
参数：IsOpenMap f ↔ IsOpenMap (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.map_le_map_iff`：map_le_map_iff {f g : Filter α} {m : α -> β} (hm 
: Injective m) : map m f <= map m g ↔ f <= g
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpenMap_iff (hg : IsOpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, map_le_map_iff hg.injective]
/-
**Topology.IsOpenEmbedding.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpe
nEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {g : Y → Z} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] (f : 
X → Y),   Topology.IsOpenEmbedding g → (Topology.IsOpenEmbedding (g ∘ f) ↔ Topol
ogy.IsOpenEmbedding f)
参数：f : X → Y；Topology.IsOpenEmbedding (g ∘ f) ↔ Topology.IsOpenEmbedding f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : T
opologicalSpace Y] [inst_2 :…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_comp_iff (f : X → Y) (hg : IsOpenEmbedding g) :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_continuous_injective_isOpenMap, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.injective.of_comp_iff]
/-
**Topology.IsOpenEmbedding.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmb
edding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {g : Y → Z} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] (f : 
X → Y),   Topology.IsOpenEmbedding g → Topology.IsOpenEmbedding (g ∘ f) → Topolo
gy.IsOpenEmbedding f
参数：f : X → Y；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsOpenEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z
 : Type u_3} {g : Y → Z} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y]   [inst_2 : Topological…
-/
lemma of_comp (f : X → Y) (hg : IsOpenEmbedding g) (h : IsOpenEmbedding (g ∘ f)) :
    IsOpenEmbedding f := (IsOpenEmbedding.of_comp_iff f hg).1 h
/-
**Topology.IsOpenEmbedding.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpen
Embedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [IsEmpty X] (f : X → Y),   Topology.IsOpenEmbedding f
参数：f : X → Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap`：∀ {X : Type u_1} {Y :
 Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
,   Topology.IsEmbedding f → IsOpenMap …
· 使用定理 `Topology.IsEmbedding.of_subsingleton`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Subsingleton X] (f : X 
→ Y),   Topology.IsEmbeddi…
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `IsOpenMap.of_isEmpty`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [h : IsEmpty X] (f : X → Y),   IsOpenMap
 f
-/
theorem of_isEmpty [IsEmpty X] (f : X → Y) : IsOpenEmbedding f :=
  of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)
/-
**Topology.IsOpenEmbedding.image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Is
OpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Topology.IsOpenEmbedding f → ∀ {s : Set X} {x : X
}, f '' s ∈ nhds (f x) ↔ s ∈ nhds x
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem image_mem_nhds {f : X → Y} (hf : IsOpenEmbedding f) {s : Set X} {x : X} :
    f '' s ∈ 𝓝 (f x) ↔ s ∈ 𝓝 x := by
  rw [← hf.map_nhds_eq, mem_map, preimage_image_eq _ hf.injective]
/-
**Topology.IsOpenEmbedding.accPt_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.I
sOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsOpenEmbedding f → ∀ {x : X} {l : Filte
r Y}, AccPt x (Filter.comap f l) ↔ AccPt (f x) l
参数：Filter.comap f l；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `IsOpenMap.clusterPt_comap_iff`：∀ {X : Type u_1} {Y : Type u_2} {f : X → 
Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Co
ntinuous f → ∀ {x :…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem accPt_comap_iff
    (hf : IsOpenEmbedding f) {x : X} {l : Filter Y} :
    AccPt x (comap f l) ↔ AccPt (f x) l := by
  rw [accPt_iff_clusterPt, accPt_iff_clusterPt, ← hf.injective.preimage_image {x}, image_singleton,
    ← preimage_compl, ← comap_principal, ← comap_inf,
    hf.isOpenMap.clusterPt_comap_iff hf.continuous]

end IsOpenEmbedding

end IsOpenEmbedding

section IsClosedEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedEmbedding

@[fun_prop]
/-
**Topology.IsClosedEmbedding.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsC
losedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → Topology.IsEmbeddi
ng f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
-/
lemma isEmbedding (hf : IsClosedEmbedding f) : IsEmbedding f := hf.toIsEmbedding
@[fun_prop]
/-
**Topology.IsClosedEmbedding.isInducing** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCl
osedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → Topology.IsInducin
g f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
-/
lemma isInducing (hf : IsClosedEmbedding f) : IsInducing f := hf.isEmbedding.isInducing
@[fun_prop]
/-
**Topology.IsClosedEmbedding.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCl
osedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
-/
lemma continuous (hf : IsClosedEmbedding f) : Continuous f := hf.isEmbedding.continuous
/-
**Topology.IsClosedEmbedding.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {ι : Type u_4} {f : X → Y} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y]   {g : ι → X} {l : Filter ι} {x : X},
   Topology.IsClosedEmbedding f → (Filter.Tendsto g l (nhds x) ↔ Filter.Tendsto 
(f ∘ g) l (nhds (f x)))
参数：Filter.Tendsto g l (nhds x) ↔ Filter.Tendsto (f ∘ g) l (nhds (f x))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
-/
lemma tendsto_nhds_iff {g : ι → X} {l : Filter ι} {x : X} (hf : IsClosedEmbedding f) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) := hf.isEmbedding.tendsto_nhds_iff
/-
**Topology.IsClosedEmbedding.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsC
losedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → IsClosedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.isClosedMap`：Topology.IsInducing.isClosedMap (hf : I
sInducing f) (h : IsClosed (range f)) : IsClosedMap f
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
lemma isClosedMap (hf : IsClosedEmbedding f) : IsClosedMap f :=
  hf.isEmbedding.isInducing.isClosedMap hf.isClosed_range
/-
**Topology.IsClosedEmbedding.isClosed_iff_image_isClosed** 是 Mathlib 中的一个定理，位于命名
空间 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → ∀ {s : Set X}, IsC
losed s ↔ IsClosed (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
-/
lemma isClosed_iff_image_isClosed (hf : IsClosedEmbedding f) {s : Set X} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.injective]
    exact h.preimage hf.continuous⟩
/-
**Topology.IsClosedEmbedding.isClosed_iff_preimage_isClosed** 是 Mathlib 中的一个定理，位
于命名空间 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → ∀ {s : Set Y}, s ⊆
 Set.range f → (IsClosed s ↔ IsClosed (f ⁻¹' s))
参数：IsClosed s ↔ IsClosed (f ⁻¹' s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosed_iff_preimage_isClosed (hf : IsClosedEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.isClosed_iff_image_isClosed, image_preimage_eq_of_subset hs]
/-
**Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap** 是 Mathlib 中的一个定理，位于命名空
间 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsEmbedding f → IsClosedMap f → Topology
.IsClosedEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma of_isEmbedding_isClosedMap (h₁ : IsEmbedding f) (h₂ : IsClosedMap f) :
    IsClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩
/-
**Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap** 是 Mathlib 中的一
个定理，位于命名空间 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Continuous f → Function.Injective f → IsClosedMap
 f → Topology.IsClosedEmbedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap`：∀ {X : Type u_1} 
{Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpac
e Y],   Topology.IsEmbedding f → IsClosedMa…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma of_continuous_injective_isClosedMap (h₁ : Continuous f) (h₂ : Injective f)
    (h₃ : IsClosedMap f) : IsClosedEmbedding f := by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl, preimage_image_eq _ h₂, compl_compl]
/-
**Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosed
Map** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Topology.IsClosedEmbedding f ↔ Continuous f ∧ Fun
ction.Injective f ∧ IsClosedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`：∀ {X : T
ype u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topolo
gicalSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClosedEmbedding_iff_continuous_injective_isClosedMap {f : X → Y} :
    IsClosedEmbedding f ↔ Continuous f ∧ Injective f ∧ IsClosedMap f where
  mp h := ⟨h.continuous, h.injective, h.isClosedMap⟩
  mpr h := .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2

@[fun_prop]
/-
**Topology.IsClosedEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClosedEmbe
dding`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], Topology.IsClosedEmbedding i
d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
protected theorem id : IsClosedEmbedding (@id X) := ⟨.id, IsClosedMap.id.isClosed_range⟩

@[fun_prop]
/-
**Topology.IsClosedEmbedding.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClosedEm
bedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsClosedEmbedding g → Topology.IsClosedEmbedding f → Topology
.IsClosedEmbedding (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
-/
theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (g ∘ f) :=
  ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩
/-
**Topology.IsClosedEmbedding.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsC
losedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsClosedEmbedding g → (Topology.IsClosedEmbedding (g ∘ f) ↔ T
opology.IsClosedEmbedding f)
参数：Topology.IsClosedEmbedding (g ∘ f) ↔ Topology.IsClosedEmbedding f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma of_comp_iff (hg : IsClosedEmbedding g) : IsClosedEmbedding (g ∘ f) ↔ IsClosedEmbedding f := by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.isClosed_iff_image_isClosed]
/-
**Topology.IsClosedEmbedding.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClose
dEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [in
st : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst_2 : TopologicalSp
ace Z],   Topology.IsEmbedding g → Topology.IsClosedEmbedding (g ∘ f) → Topology
.IsClosedEmbedding f
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsInducing.isClosed_preimage`：isClosed_preimage (h : IsInducing
 f) (s : Set Y) (hs : IsClosed s) : IsClosed (f ⁻¹' s)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
protected lemma of_comp (hg : IsEmbedding g) (hgf : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f where
  __ := hg.of_comp_iff.mp hgf.isEmbedding
  isClosed_range := by
    convert! hg.isClosed_preimage _ hgf.isClosed_range
    rw [range_comp, hg.injective.preimage_image]
/-
**Topology.IsClosedEmbedding.closure_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [i
nst_1 : TopologicalSpace Y],   Topology.IsClosedEmbedding f → ∀ (s : Set X), clo
sure (f '' s) = f '' closure s
参数：s : Set X；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.closure_image_eq_of_continuous`：IsClosedMap.closure_image_eq
_of_continuous (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) : 
closure (f '' s) = f '' closure …
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
-/
theorem closure_image_eq (hf : IsClosedEmbedding f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

end Topology.IsClosedEmbedding.IsClosedEmbedding

