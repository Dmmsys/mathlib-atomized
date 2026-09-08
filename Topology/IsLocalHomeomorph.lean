/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.SeparatedMap

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

For a function `f : X → Y ` between topological spaces, we say
* `IsLocalHomeomorphOn f s` if `f` is a local homeomorphism around each point of `s`: for each
  `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.
* `IsLocalHomeomorph f`: `f` is a local homeomorphism, i.e. it's a local homeomorphism on `univ`.

Note that `IsLocalHomeomorph` is a global condition. This is in contrast to
`OpenPartialHomeomorph`, which is a homeomorphism between specific open subsets.

## Main results
* local homeomorphisms are locally injective open maps
* more!

-/

@[expose] public section


open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

/-- A function `f : X → Y` satisfies `IsLocalHomeomorphOn f s` if each `x ∈ s` is contained in
the source of some `e : OpenPartialHomeomorph X Y` with `f = e`. -/
/-
**IsLocalHomeomorphOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalHomeomorphOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` satisfies `IsLocalHomeomorphOn f s` if each `x ∈ s` is co
ntained in
the source of some `e : OpenPartialHomeomorph X Y` with `f = e`.
-/
def IsLocalHomeomorphOn :=
  ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e
/-
**isLocalHomeomorphOn_iff_isOpenEmbedding_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHomeomorphOn_iff_isOpenEmbedding_restrict {f : X -> Y} : IsLocalHom
eomorphOn f s ↔ forall x in s, exists U in 𝓝 x, IsOpenEmbedding (U.domRestrict f
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.isOpenEmbedding_restrict`：isOpenEmbedding_restrict
 : IsOpenEmbedding (e.source.domRestrict e) where toIsEmbedding
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap`：∀ {X : Type
 u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologic
alSpace Y],   Topology.IsOpenEmbedding f ↔ Contin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem isLocalHomeomorphOn_iff_isOpenEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorphOn f s ↔ ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.domRestrict f) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.isOpenEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : IsOpenEmbedding ((interior U).domRestrict f) := by
      refine emb.comp ⟨.inclusion interior_subset, ?_⟩
      rw [Set.range_inclusion]; exact isOpen_induced isOpen_interior
    obtain ⟨cont, inj, openMap⟩ := isOpenEmbedding_iff_continuous_injective_isOpenMap.mp this
    have : Nonempty X := ⟨x⟩
    exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict
      (Set.injOn_iff_injective.mpr inj).toPartialEquiv
      (continuousOn_iff_continuous_domRestrict.mpr cont) openMap isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hU, rfl⟩

namespace IsLocalHomeomorphOn

variable {f s}

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalHomeomorphOn.discreteTopology_of_image** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alHomeomorphOn`。
形式化陈述：discreteTopology_of_image (h : IsLocalHomeomorphOn f s) [DiscreteTopology 
(f '' s)] : DiscreteTopology s
参数：h : IsLocalHomeomorphOn f s；f '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem discreteTopology_of_image (h : IsLocalHomeomorphOn f s)
    [DiscreteTopology (f '' s)] : DiscreteTopology s :=
  discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    obtain ⟨e, hx, rfl⟩ := h x x.2
    have ⟨U, hU, eq⟩ := isOpen_discrete {(⟨_, _, x.2, rfl⟩ : e '' s)}
    refine ⟨e.source ∩ e ⁻¹' U, e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU,
      subset_antisymm (fun x' mem ↦ Subtype.ext <| e.injOn mem.1 hx ?_) ?_⟩
    · simpa using Set.subset_singleton_iff.1 eq.subset ⟨_, x', x'.2, rfl⟩ mem.2
    · rintro x rfl; exact ⟨hx, eq.superset rfl⟩
/-
**IsLocalHomeomorphOn.isDiscrete_of_image** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalHome
omorphOn`。
形式化陈述：isDiscrete_of_image (h : IsLocalHomeomorphOn f s) (hs : IsDiscrete (f '' s
)) : IsDiscrete s
参数：h : IsLocalHomeomorphOn f s；hs : IsDiscrete (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
· 使用定理 `IsLocalHomeomorphOn.discreteTopology_of_image`：discreteTopology_of_image
 (h : IsLocalHomeomorphOn f s) [DiscreteTopology (f '' s)] : DiscreteTopology s
-/
lemma isDiscrete_of_image (h : IsLocalHomeomorphOn f s)
    (hs : IsDiscrete (f '' s)) : IsDiscrete s :=
  have := hs.1; ⟨discreteTopology_of_image h⟩
/-
**IsLocalHomeomorphOn.discreteTopology_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calHomeomorphOn`。
形式化陈述：discreteTopology_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
 DiscreteTopology (f '' s) ↔ DiscreteTopology s
参数：h : IsLocalHomeomorphOn f s；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.discreteTopology_of_image`：discreteTopology_of_image
 (h : IsLocalHomeomorphOn f s) [DiscreteTopology (f '' s)] : DiscreteTopology s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem discreteTopology_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    DiscreteTopology (f '' s) ↔ DiscreteTopology s := by
  refine ⟨fun _ ↦ h.discreteTopology_of_image, ?_⟩
  simp_rw [discreteTopology_iff_isOpen_singleton]
  rintro hX ⟨_, x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := h x hx
  refine ⟨e '' {x}, e.isOpen_image_of_subset_source ?_ (Set.singleton_subset_iff.mpr hxe), ?_⟩
  · simpa using hs.isOpenMap_subtype_val _ (hX ⟨x, hx⟩)
  · ext; simp [Subtype.ext_iff]
/-
**IsLocalHomeomorphOn.isDiscrete_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalHom
eomorphOn`。
形式化陈述：isDiscrete_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) : IsDis
crete (f '' s) ↔ IsDiscrete s
参数：h : IsLocalHomeomorphOn f s；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalHomeomorphOn.isDiscrete_of_image`：isDiscrete_of_image (h : IsLoca
lHomeomorphOn f s) (hs : IsDiscrete (f '' s)) : IsDiscrete s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalHomeomorphOn.discreteTopology_image_iff`：discreteTopology_image_i
ff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) : DiscreteTopology (f '' s) ↔ D
iscreteTopology s
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
-/
lemma isDiscrete_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    IsDiscrete (f '' s) ↔ IsDiscrete s :=
  ⟨h.isDiscrete_of_image, fun hs' ↦ ⟨h.discreteTopology_image_iff hs |>.mpr hs'.to_subtype⟩⟩

variable (f s) in
/-- Proves that `f` satisfies `IsLocalHomeomorphOn f s`. The condition `h` is weaker than the
definition of `IsLocalHomeomorphOn f s`, since it only requires `e : OpenPartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
/-
**IsLocalHomeomorphOn.mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphOn`。
形式化陈述：mk (h : forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source
 ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s
参数：h : forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.
EqOn f e e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
· 使用定理 `PartialEquiv.map_target'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : β⦄, x ∈ self.target → self.invFun x ∈ self.source
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_congr`：continuousOn_congr (h' : EqOn g f s) : ContinuousOn 
g s ↔ ContinuousOn f s
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Proves that `f` satisfies `IsLocalHomeomorphOn f s`. The condition `h` is weaker
 than the
definition of `IsLocalHomeomorphOn f s`, since it only requires `e : OpenPartial
Homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`.
-/
theorem mk (h : ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx ↦ by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx ↦ by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy ↦ by rw [he (e.map_target' hy)]; exact e.right_inv' hy
        continuousOn_toFun := (continuousOn_congr he).mpr e.continuousOn_toFun },
      hx, rfl⟩

/-- A `OpenPartialHomeomorph` is a local homeomorphism on its source. -/
/-
**IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn** 是 Mathlib 中的一个
定理，位于命名空间 `IsLocalHomeomorphOn.OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), IsLocalHomeomorphOn (↑e) e.so
urce
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `OpenPartialHomeomorph` is a local homeomorphism on its source.
-/
lemma OpenPartialHomeomorph.isLocalHomeomorphOn (e : OpenPartialHomeomorph X Y) :
    IsLocalHomeomorphOn e e.source :=
  fun _ hx ↦ ⟨e, hx, rfl⟩

variable {g t}
/-
**IsLocalHomeomorphOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphOn`。
形式化陈述：mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s subseteq t) : IsL
ocalHomeomorphOn f s
参数：hf : IsLocalHomeomorphOn f t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s ⊆ t) : IsLocalHomeomorphOn f s :=
  fun x hx ↦ hf x (hst hx)
/-
**IsLocalHomeomorphOn.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphO
n`。
形式化陈述：of_comp_left (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorph
On g (f '' s)) (cont : forall x in s, ContinuousAt f x) : IsLocalHomeomorphOn f 
s
参数：hgf : IsLocalHomeomorphOn (g ∘ f) s；hg : IsLocalHomeomorphOn g (f '' s)；cont 
: forall x in s, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.mk`：mk (h : forall x in s, exists e : OpenPartialHom
eomorph X Y, x in e.source ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.eq_symm_apply`：eq_symm_apply {x : X} {y : Y} (hx :
 x in e.source) (hy : y in e.target) : x = e.symm y ↔ e x = y
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem of_comp_left (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
    (cont : ∀ x ∈ s, ContinuousAt f x) : IsLocalHomeomorphOn f s := mk f s fun x hx ↦ by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy ↦ ?_⟩
  change f y = g.symm (gf y)
  have : f y ∈ g.source := by apply interior_subset hy.1.2
  rw [← he, g.eq_symm_apply this (by apply g.map_source this), Function.comp_apply]
/-
**IsLocalHomeomorphOn.of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph
On`。
形式化陈述：of_comp_right (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorp
hOn f s) : IsLocalHomeomorphOn g (f '' s)
参数：hgf : IsLocalHomeomorphOn (g ∘ f) s；hf : IsLocalHomeomorphOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.mk`：mk (h : forall x in s, exists e : OpenPartialHom
eomorph X Y, x in e.source ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem of_comp_right (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s) :
    IsLocalHomeomorphOn g (f '' s) := mk g _ <| by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy ↦ ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he, Function.comp_apply, f.right_inv hy.1]
/-
**IsLocalHomeomorphOn.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphOn
`。
形式化陈述：map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s) : (𝓝 x).m
ap f = 𝓝 (f x)
参数：hf : IsLocalHomeomorphOn f s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx
/-
**IsLocalHomeomorphOn.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphO
n`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y} {s : Set X},   IsLocalHomeomorphOn f s → ∀ {x : X}, 
x ∈ s → ContinuousAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsLocalHomeomorphOn.map_nhds_eq`：map_nhds_eq (hf : IsLocalHomeomorphOn f
 s) {x : X} (hx : x in s) : (𝓝 x).map f = 𝓝 (f x)
-/
protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le
/-
**IsLocalHomeomorphOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphO
n`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y} {s : Set X},   IsLocalHomeomorphOn f s → ContinuousO
n f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `IsLocalHomeomorphOn.continuousAt`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X},   I
sLocalHomeomorphOn f s…
-/
protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  continuousOn_of_forall_continuousAt fun _x ↦ hf.continuousAt
/-
**IsLocalHomeomorphOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorphOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {g : Y → Z} {f : 
X → Y} {s : Set X} {t : Set Y},   IsLocalHomeomorphOn g t → IsLocalHomeomorphOn 
f s → Set.MapsTo f s t → IsLocalHomeomorphOn (g ∘ f) s
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

end IsLocalHomeomorphOn

/-- A function `f : X → Y` satisfies `IsLocalHomeomorph f` if each `x : x` is contained in
  the source of some `e : OpenPartialHomeomorph X Y` with `f = e`. -/
/-
**IsLocalHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalHomeomorph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` satisfies `IsLocalHomeomorph f` if each `x : x` is contai
ned in
  the source of some `e : OpenPartialHomeomorph X Y` with `f = e`.
-/
def IsLocalHomeomorph :=
  ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e

/-- A homeomorphism is a local homeomorphism. -/
/-
**Homeomorph.isLocalHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f
参数：f : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
A homeomorphism is a local homeomorphism.
-/
theorem Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f :=
  fun _ ↦ ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

variable {f s}
/-
**isLocalHomeomorph_iff_isLocalHomeomorphOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHomeomorph_iff_isLocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsL
ocalHomeomorphOn f Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ :=
  ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩
/-
**IsLocalHomeomorph.isLocalHomeomorphOn** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeom
orph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y} {s : Set X},   IsLocalHomeomorph f → IsLocalHomeomor
phOn f s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f s := fun x _ ↦ hf x
/-
**isLocalHomeomorph_iff_isOpenEmbedding_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHomeomorph_iff_isOpenEmbedding_restrict {f : X -> Y} : IsLocalHomeo
morph f ↔ forall x : X, exists U in 𝓝 x, IsOpenEmbedding (U.domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLocalHomeomorph_iff_isOpenEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorph f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.domRestrict f) := by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]
/-
**Topology.IsOpenEmbedding.isLocalHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.isLocalHomeomorph (hf : IsOpenEmbedding f) : IsLo
calHomeomorph f
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLocalHomeomorph_iff_isOpenEmbedding_restrict`：isLocalHomeomorph_iff_is
OpenEmbedding_restrict {f : X -> Y} : IsLocalHomeomorph f ↔ forall x : X, exists
 U in 𝓝 x, IsOpenEmbedding (U.domRes…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem Topology.IsOpenEmbedding.isLocalHomeomorph (hf : IsOpenEmbedding f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ ↦
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

namespace IsLocalHomeomorph

/-- A space that admits a local homeomorphism to a discrete space is itself discrete. -/
/-
**IsLocalHomeomorph.comap_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHom
eomorph`。
形式化陈述：comap_discreteTopology (h : IsLocalHomeomorph f) [DiscreteTopology Y] : Di
screteTopology X
参数：h : IsLocalHomeomorph f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Homeomorph.discreteTopology_iff`：discreteTopology_iff (h : X ≃ₜ Y) : Dis
creteTopology X ↔ DiscreteTopology Y
· 使用定理 `IsLocalHomeomorphOn.discreteTopology_of_image`：discreteTopology_of_image
 (h : IsLocalHomeomorphOn f s) [DiscreteTopology (f '' s)] : DiscreteTopology s
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…
· 使用定理 `instDiscreteTopologySubtype`：∀ {X : Type u} {p : X → Prop} [inst : Topol
ogicalSpace X] [DiscreteTopology X], DiscreteTopology (Subtype p)

--- 原说明 ---
A space that admits a local homeomorphism to a discrete space is itself discrete
.
-/
theorem comap_discreteTopology (h : IsLocalHomeomorph f)
    [DiscreteTopology Y] : DiscreteTopology X :=
  (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image
/-
**IsLocalHomeomorph.discreteTopology_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lHomeomorph`。
形式化陈述：discreteTopology_range_iff (h : IsLocalHomeomorph f) : DiscreteTopology (S
et.range f) ↔ DiscreteTopology X
参数：h : IsLocalHomeomorph f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Homeomorph.discreteTopology_iff`：discreteTopology_iff (h : X ≃ₜ Y) : Dis
creteTopology X ↔ DiscreteTopology Y
· 使用定理 `IsLocalHomeomorphOn.discreteTopology_image_iff`：discreteTopology_image_i
ff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) : DiscreteTopology (f '' s) ↔ D
iscreteTopology s
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem discreteTopology_range_iff (h : IsLocalHomeomorph f) :
    DiscreteTopology (Set.range f) ↔ DiscreteTopology X := by
  rw [← Set.image_univ, ← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

/-- If there is a surjective local homeomorphism between two spaces and one of them is discrete,
then both spaces are discrete. -/
/-
**IsLocalHomeomorph.discreteTopology_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间
 `IsLocalHomeomorph`。
形式化陈述：discreteTopology_iff_of_surjective (h : IsLocalHomeomorph f) (hs : Functio
n.Surjective f) : DiscreteTopology X ↔ DiscreteTopology Y
参数：h : IsLocalHomeomorph f；hs : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.discreteTopology_iff`：discreteTopology_iff (h : X ≃ₜ Y) : Dis
creteTopology X ↔ DiscreteTopology Y
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `IsLocalHomeomorph.discreteTopology_range_iff`：discreteTopology_range_iff
 (h : IsLocalHomeomorph f) : DiscreteTopology (Set.range f) ↔ DiscreteTopology X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If there is a surjective local homeomorphism between two spaces and one of them 
is discrete,
then both spaces are discrete.
-/
theorem discreteTopology_iff_of_surjective (h : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    DiscreteTopology X ↔ DiscreteTopology Y := by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff, ← hs.range_eq, h.discreteTopology_range_iff]

variable (f)

/-- Proves that `f` satisfies `IsLocalHomeomorph f`. The condition `h` is weaker than the
definition of `IsLocalHomeomorph f`, since it only requires `e : OpenPartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
/-
**IsLocalHomeomorph.mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：mk (h : forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source 
∧ Set.EqOn f e e.source) : IsLocalHomeomorph f
参数：h : forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.E
qOn f e e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`：isLocalHomeomorph_iff_is
LocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ
· 使用定理 `IsLocalHomeomorphOn.mk`：mk (h : forall x in s, exists e : OpenPartialHom
eomorph X Y, x in e.source ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s

--- 原说明 ---
Proves that `f` satisfies `IsLocalHomeomorph f`. The condition `h` is weaker tha
n the
definition of `IsLocalHomeomorph f`, since it only requires `e : OpenPartialHome
omorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`.
-/
theorem mk (h : ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx ↦ h x)

@[deprecated (since := "2026-06-06")]
alias Homeomorph.isLocalHomeomorph := _root_.Homeomorph.isLocalHomeomorph

variable {g f}
/-
**IsLocalHomeomorph.isLocallyInjective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalHomeomo
rph`。
形式化陈述：isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f
参数：hf : IsLocalHomeomorph f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f :=
  fun x ↦ by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩
/-
**IsLocalHomeomorph.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g) (cont
 : Continuous f) : IsLocalHomeomorph f
参数：hgf : IsLocalHomeomorph (g ∘ f)；hg : IsLocalHomeomorph g；cont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`：isLocalHomeomorph_iff_is
LocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ
· 使用定理 `IsLocalHomeomorphOn.of_comp_left`：of_comp_left (hgf : IsLocalHomeomorphO
n (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s)) (cont : forall x in s, Contin
uousAt f x) : IsLocalH…
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
    (cont : Continuous f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ ↦ cont.continuousAt
/-
**IsLocalHomeomorph.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x)
参数：hf : IsLocalHomeomorph f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.map_nhds_eq`：map_nhds_eq (hf : IsLocalHomeomorphOn f
 s) {x : X} (hx : x in s) : (𝓝 x).map f = 𝓝 (f x)
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

/-- A local homeomorphism is continuous. -/
/-
**IsLocalHomeomorph.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsLocalHomeomorph f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `IsLocalHomeomorphOn.continuousOn`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X},   I
sLocalHomeomorphOn f s…
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…

--- 原说明 ---
A local homeomorphism is continuous.
-/
protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn

/-- A local homeomorphism is an open map. -/
/-
**IsLocalHomeomorph.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsLocalHomeomorph f → IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalHomeomorph.map_nhds_eq`：map_nhds_eq (hf : IsLocalHomeomorph f) (x
 : X) : (𝓝 x).map f = 𝓝 (f x)

--- 原说明 ---
A local homeomorphism is an open map.
-/
protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x ↦ ge_of_eq (hf.map_nhds_eq x)

/-- The composition of local homeomorphisms is a local homeomorphism. -/
/-
**IsLocalHomeomorph.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {g : Y → Z} {f : 
X → Y},   IsLocalHomeomorph g → IsLocalHomeomorph f → IsLocalHomeomorph (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`：isLocalHomeomorph_iff_is
LocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ
· 使用定理 `IsLocalHomeomorphOn.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topologic
alSpace Z] {g …
· 使用定理 `IsLocalHomeomorph.isLocalHomeomorphOn`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}
,   IsLocalHomeomorph f → I…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
The composition of local homeomorphisms is a local homeomorphism.
-/
protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))

/-- An injective local homeomorphism is an open embedding. -/
/-
**IsLocalHomeomorph.isOpenEmbedding_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calHomeomorph`。
形式化陈述：isOpenEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective)
 : IsOpenEmbedding f
参数：hf : IsLocalHomeomorph f；hi : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `IsLocalHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph
 f → Continuous f
· 使用定理 `IsLocalHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph 
f → IsOpenMap f

--- 原说明 ---
An injective local homeomorphism is an open embedding.
-/
theorem isOpenEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective) :
    IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

/-- A bijective local homeomorphism is a homeomorphism. -/
/-
**IsLocalHomeomorph.toHomeomorphOfBijective** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalHo
meomorph`。
形式化陈述：toHomeomorphOfBijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) : X 
≃ₜ Y
参数：hf : IsLocalHomeomorph f；hb : f.Bijective。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph
 f → Continuous f
· 使用定理 `IsLocalHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph 
f → IsOpenMap f

--- 原说明 ---
A bijective local homeomorphism is a homeomorphism.
-/
noncomputable def toHomeomorphOfBijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) :
    X ≃ₜ Y :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap

/-- Continuous local sections of a local homeomorphism are open embeddings. -/
/-
**IsLocalHomeomorph.isOpenEmbedding_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHo
meomorph`。
形式化陈述：isOpenEmbedding_of_comp (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding 
(g ∘ f)) (cont : Continuous f) : IsOpenEmbedding f
参数：hf : IsLocalHomeomorph g；hgf : IsOpenEmbedding (g ∘ f)；cont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorph.isOpenEmbedding_of_injective`：isOpenEmbedding_of_injec
tive (hf : IsLocalHomeomorph f) (hi : f.Injective) : IsOpenEmbedding f
· 使用定理 `IsLocalHomeomorph.of_comp`：of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg
 : IsLocalHomeomorph g) (cont : Continuous f) : IsLocalHomeomorph f
· 使用定理 `Topology.IsOpenEmbedding.isLocalHomeomorph`：Topology.IsOpenEmbedding.isL
ocalHomeomorph (hf : IsOpenEmbedding f) : IsLocalHomeomorph f
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…

--- 原说明 ---
Continuous local sections of a local homeomorphism are open embeddings.
-/
theorem isOpenEmbedding_of_comp (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f))
    (cont : Continuous f) : IsOpenEmbedding f :=
  (hgf.isLocalHomeomorph.of_comp hf cont).isOpenEmbedding_of_injective hgf.injective.of_comp

open TopologicalSpace in
/-- Ranges of continuous local sections of a local homeomorphism
form a basis of the source space. -/
/-
**IsLocalHomeomorph.isTopologicalBasis** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeomo
rph`。
形式化陈述：isTopologicalBasis (hf : IsLocalHomeomorph f) : IsTopologicalBasis {U : Se
t X | exists V : Set Y, IsOpen V ∧ exists s : C(V,X), f ∘ s = (↑) ∧ Set.range s 
= U}
参数：hf : IsLocalHomeomorph f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `IsLocalHomeomorph.isOpenEmbedding_of_comp`：isOpenEmbedding_of_comp (hf :
 IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f)) (cont : Continuous f) : Is
OpenEmbedding f
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage`：isOpen_inter_preimage {s : 
Set Y} (hs : IsOpen s) : IsOpen (e.source inter e ⁻¹' s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `OpenPartialHomeomorph.symm_image_target_inter_eq`：symm_image_target_inte
r_eq (s : Set Y) : e.symm '' (e.target inter s) = e.source inter e ⁻¹' (e.target
 inter s)
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `OpenPartialHomeomorph.source_preimage_target`：source_preimage_target : e
.source subseteq e ⁻¹' e.target
· 使用定理 `OpenPartialHomeomorph.source_inter_preimage_inv_preimage`：source_inter_p
reimage_inv_preimage (s : Set X) : e.source inter e ⁻¹' e.symm ⁻¹' s = e.source 
inter s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Ranges of continuous local sections of a local homeomorphism
form a basis of the source space.
-/
theorem isTopologicalBasis (hf : IsLocalHomeomorph f) : IsTopologicalBasis
    {U : Set X | ∃ V : Set Y, IsOpen V ∧ ∃ s : C(V,X), f ∘ s = (↑) ∧ Set.range s = U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU ↦ ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (isOpenEmbedding_of_comp hf (hs ▸ ⟨IsEmbedding.subtypeVal, ?_⟩)
      s.continuous).isOpen_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source ∩ U, ⟨f.target ∩ f.symm ⁻¹' U, f.symm.isOpen_inter_preimage hU,
      ⟨_, continuousOn_iff_continuous_domRestrict.mp (f.continuousOn_invFun.mono fun _ h ↦ h.1)⟩,
      ?_, (Set.range_domRestrict _ _).trans ?_⟩, ⟨hxf, hx⟩, fun _ h ↦ h.2⟩
    · ext y; exact f.right_inv y.2.1
    · apply (f.symm_image_target_inter_eq _).trans
      rw [Set.preimage_inter, ← Set.inter_assoc, Set.inter_eq_self_of_subset_left
        f.source_preimage_target, f.source_inter_preimage_inv_preimage]

variable (hf : IsLocalHomeomorph f) {x : X}

variable (x) in
/-- A chosen local inverse for a local homeomorphism `f` at a point `x`. -/
/-
**IsLocalHomeomorph.localInverseAt** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalHomeomorph`
。
形式化陈述：localInverseAt : OpenPartialHomeomorph Y X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chosen local inverse for a local homeomorphism `f` at a point `x`.
-/
noncomputable def localInverseAt : OpenPartialHomeomorph Y X := (hf x).choose.symm

/-- The point `x` lies in the target of `localInverseAt x`. -/
/-
**IsLocalHomeomorph.self_mem_localInverseAt_target** 是 Mathlib 中的一个定理，位于命名空间 `Is
LocalHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   (hf : IsLocalHomeomorph f) {x : X}, x ∈ (hf.localI
nverseAt x).target
参数：hf : IsLocalHomeomorph f；hf.localInverseAt x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The point `x` lies in the target of `localInverseAt x`.
-/
@[grind =>, simp] lemma self_mem_localInverseAt_target : x ∈ (hf.localInverseAt x).target :=
  (hf x).choose_spec.1

variable (x) in
/-- The inverse function of `localInverseAt x` coincides with `f`. -/
/-
**IsLocalHomeomorph.localInverseAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHomeom
orph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   (hf : IsLocalHomeomorph f) (x : X), ↑(hf.localInve
rseAt x).symm = f
参数：hf : IsLocalHomeomorph f；x : X；hf.localInverseAt x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The inverse function of `localInverseAt x` coincides with `f`.
-/
@[simp] lemma localInverseAt_symm : (hf.localInverseAt x).symm = f :=
  (hf x).choose_spec.2.symm

/-- The point `f x` lies in the source of `localInverseAt x`. -/
/-
**IsLocalHomeomorph.apply_self_mem_localInverseAt_source** 是 Mathlib 中的一个定理，位于命名
空间 `IsLocalHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   (hf : IsLocalHomeomorph f) {x : X}, f x ∈ (hf.loca
lInverseAt x).source
参数：hf : IsLocalHomeomorph f；hf.localInverseAt x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsLocalHomeomorph.localInverseAt_symm`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y}   (hf : IsL
ocalHomeomorph f) (x : X), …
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `IsLocalHomeomorph.self_mem_localInverseAt_target`：∀ {X : Type u_1} {Y : 
Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} 
  (hf : IsLocalHomeomorph f) {x : X}, …

--- 原说明 ---
The point `f x` lies in the source of `localInverseAt x`.
-/
@[grind =>, simp] lemma apply_self_mem_localInverseAt_source :
    f x ∈ (hf.localInverseAt x).source := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).map_target hf.self_mem_localInverseAt_target

/-- The function `f` is injective on the target of `localInverseAt x`. -/
/-
**IsLocalHomeomorph.injOn_localInverseAt_target** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alHomeomorph`。
形式化陈述：injOn_localInverseAt_target : (hf.localInverseAt x).target.InjOn f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.EqOn.injOn_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ :
 α → β}, Set.EqOn f₁ f₂ s → (Set.InjOn f₁ s ↔ Set.InjOn f₂ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsLocalHomeomorph.localInverseAt_symm`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y}   (hf : IsL
ocalHomeomorph f) (x : X), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …

--- 原说明 ---
The function `f` is injective on the target of `localInverseAt x`.
-/
lemma injOn_localInverseAt_target : (hf.localInverseAt x).target.InjOn f := by
  rw [Set.EqOn.injOn_iff (f₂ := (hf.localInverseAt x).symm) (fun y _ ↦ by simp)]
  exact (hf.localInverseAt x).symm.injOn

/-- If `y` lies in the source of `localInverseAt x`, then `f (localInverseAt x y) = y`. -/
/-
**IsLocalHomeomorph.apply_localInverseAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   (hf : IsLocalHomeomorph f) {x : X} {y : Y}, y ∈ (h
f.localInverseAt x).source → f (↑(hf.localInverseAt x) y) = y
参数：hf : IsLocalHomeomorph f；hf.localInverseAt x；↑(hf.localInverseAt x) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsLocalHomeomorph.localInverseAt_symm`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y}   (hf : IsL
ocalHomeomorph f) (x : X), …
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x

--- 原说明 ---
If `y` lies in the source of `localInverseAt x`, then `f (localInverseAt x y) = 
y`.
-/
@[grind .] lemma apply_localInverseAt_of_mem {y : Y} (hx : y ∈ (hf.localInverseAt x).source) :
    f (hf.localInverseAt x y) = y := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).left_inv hx

/-- The function `localInverseAt x` sends `f x` back to `x`. -/
/-
**IsLocalHomeomorph.localInverseAt_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   (hf : IsLocalHomeomorph f) {x : X}, ↑(hf.localInve
rseAt x) (f x) = x
参数：hf : IsLocalHomeomorph f；hf.localInverseAt x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalHomeomorph.injOn_localInverseAt_target`：injOn_localInverseAt_targ
et : (hf.localInverseAt x).target.InjOn f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLocalHomeomorph.self_mem_localInverseAt_target`：∀ {X : Type u_1} {Y : 
Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} 
  (hf : IsLocalHomeomorph f) {x : X}, …
· 使用定理 `IsLocalHomeomorph.apply_localInverseAt_of_mem`：∀ {X : Type u_1} {Y : Typ
e u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y}   (
hf : IsLocalHomeomorph f) {x : X} {…
· 使用定理 `IsLocalHomeomorph.apply_self_mem_localInverseAt_source`：∀ {X : Type u_1}
 {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X
 → Y}   (hf : IsLocalHomeomorph f) {x : X}, …

--- 原说明 ---
The function `localInverseAt x` sends `f x` back to `x`.
-/
@[simp] lemma localInverseAt_apply_self : hf.localInverseAt x (f x) = x :=
  hf.injOn_localInverseAt_target (by simp) hf.self_mem_localInverseAt_target <|
    hf.apply_localInverseAt_of_mem hf.apply_self_mem_localInverseAt_source

end IsLocalHomeomorph

