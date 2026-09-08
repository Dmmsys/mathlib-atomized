/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Baire.Lemmas

/-!
# Further properties of homeomorphisms

This file proves further properties of homeomorphisms between topological spaces.
Pretty much every topological property is preserved under homeomorphisms.

-/

@[expose] public section

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*}

section

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

namespace Homeomorph

/-
**Homeomorph.secondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [SecondCountableTopology Y]   (h : X ≃ₜ Y), SecondCountableTopol
ogy X
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.secondCountableTopology`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace α] {f : α → β} [inst_1 : TopologicalSpace β]   [Se
condCountableTopology β], Topolog…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
protected theorem secondCountableTopology [SecondCountableTopology Y]
    (h : X ≃ₜ Y) : SecondCountableTopology X :=
  h.isInducing.secondCountableTopology
/-
**Homeomorph.baireSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [BaireSpace X] (f : X ≃ₜ Y),   BaireSpace Y
参数：f : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.baireSpace`：IsOpenQuotientMap.baireSpace {Y : Type*} [
TopologicalSpace Y] {f : X -> Y} (hf : IsOpenQuotientMap f) : BaireSpace Y
· 使用定理 `Homeomorph.isOpenQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   IsOpenQuotientMa
p ⇑h
-/
protected theorem baireSpace [BaireSpace X] (f : X ≃ₜ Y) : BaireSpace Y :=
  f.isOpenQuotientMap.baireSpace

/-- If `h : X → Y` is a homeomorphism, `h(s)` is compact iff `s` is. -/
@[simp]
/-
**Homeomorph.isCompact_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isCompact_image {s : Set X} (h : X ≃ₜ Y) : IsCompact (h '' s) ↔ IsCompact 
s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `h(s)` is compact iff `s` is.
-/
theorem isCompact_image {s : Set X} (h : X ≃ₜ Y) : IsCompact (h '' s) ↔ IsCompact s :=
  h.isEmbedding.isCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is compact iff `s` is. -/
@[simp]
/-
**Homeomorph.isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsCompact (h ⁻¹' s) ↔ IsComp
act s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isCompact_image`：isCompact_image {s : Set X} (h : X ≃ₜ Y) : I
sCompact (h '' s) ↔ IsCompact s

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is compact iff `s` is.
-/
theorem isCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm]; exact h.symm.isCompact_image

/-- If `h : X → Y` is a homeomorphism, `s` is σ-compact iff `h(s)` is. -/
@[simp]
/-
**Homeomorph.isSigmaCompact_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) : IsSigmaCompact (h '' s) ↔ 
IsSigmaCompact s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsEmbedding.isSigmaCompact_iff`：Topology.IsEmbedding.isSigmaCom
pact_iff {f : X -> Y} {s : Set X} (hf : IsEmbedding f) : IsSigmaCompact s ↔ IsSi
gmaCompact (f '' s)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `s` is σ-compact iff `h(s)` is.
-/
theorem isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) :
    IsSigmaCompact (h '' s) ↔ IsSigmaCompact s :=
  h.isEmbedding.isSigmaCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is σ-compact iff `s` is. -/
@[simp]
/-
**Homeomorph.isSigmaCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isSigmaCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsSigmaCompact (h ⁻¹' s
) ↔ IsSigmaCompact s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isSigmaCompact_image`：isSigmaCompact_image {s : Set X} (h : X
 ≃ₜ Y) : IsSigmaCompact (h '' s) ↔ IsSigmaCompact s

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is σ-compact iff `s` is.
-/
theorem isSigmaCompact_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsSigmaCompact (h ⁻¹' s) ↔ IsSigmaCompact s := by
  rw [← image_symm]; exact h.symm.isSigmaCompact_image

@[simp]
/-
**Homeomorph.isPreconnected_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isPreconnected_image {s : Set X} (h : X ≃ₜ Y) : IsPreconnected (h '' s) ↔ 
IsPreconnected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem isPreconnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPreconnected (h '' s) ↔ IsPreconnected s :=
  ⟨fun hs ↦ by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs ↦ hs.image _ h.continuous.continuousOn⟩

@[simp]
/-
**Homeomorph.isPreconnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isPreconnected_preimage {s : Set Y} (h : X ≃ₜ Y) : IsPreconnected (h ⁻¹' s
) ↔ IsPreconnected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isPreconnected_image`：isPreconnected_image {s : Set X} (h : X
 ≃ₜ Y) : IsPreconnected (h '' s) ↔ IsPreconnected s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPreconnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPreconnected (h ⁻¹' s) ↔ IsPreconnected s := by
  rw [← image_symm, isPreconnected_image]

@[simp]
/-
**Homeomorph.isConnected_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isConnected_image {s : Set X} (h : X ≃ₜ Y) : IsConnected (h '' s) ↔ IsConn
ected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Homeomorph.isPreconnected_image`：isPreconnected_image {s : Set X} (h : X
 ≃ₜ Y) : IsPreconnected (h '' s) ↔ IsPreconnected s
-/
theorem isConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsConnected (h '' s) ↔ IsConnected s :=
  image_nonempty.and h.isPreconnected_image

@[simp]
/-
**Homeomorph.isConnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isConnected_preimage {s : Set Y} (h : X ≃ₜ Y) : IsConnected (h ⁻¹' s) ↔ Is
Connected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isConnected_image`：isConnected_image {s : Set X} (h : X ≃ₜ Y)
 : IsConnected (h '' s) ↔ IsConnected s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsConnected (h ⁻¹' s) ↔ IsConnected s := by
  rw [← image_symm, isConnected_image]
/-
**Homeomorph.image_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_connectedComponentIn {s : Set X} (h : X ≃ₜ Y) {x : X} (hx : x in s) 
: h '' connectedComponentIn s x = connectedComponentIn (h '' s) (h x)
参数：h : X ≃ₜ Y；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ContinuousOn.image_connectedComponentIn_subset`：ContinuousOn.image_conne
ctedComponentIn_subset [TopologicalSpace β] {f : α -> β} {s : Set α} {a : α} (hf
 : ContinuousOn f s) (hx : a in s) :…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_connectedComponentIn {s : Set X} (h : X ≃ₜ Y) {x : X} (hx : x ∈ s) :
    h '' connectedComponentIn s x = connectedComponentIn (h '' s) (h x) := by
  refine (h.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  have := h.symm.continuous.continuousOn.image_connectedComponentIn_subset (mem_image_of_mem h hx)
  rwa [image_subset_iff, h.preimage_symm, h.image_symm, h.preimage_image, h.symm_apply_apply]
    at this

@[simp]
/-
**Homeomorph.comap_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comap_cocompact (h : X ≃ₜ Y) : comap h (cocompact Y) = cocompact X
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Homeomorph.isCompact_preimage`：isCompact_preimage {s : Set Y} (h : X ≃ₜ 
Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem comap_cocompact (h : X ≃ₜ Y) : comap h (cocompact Y) = cocompact X :=
  (comap_cocompact_le h.continuous).antisymm <|
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩

@[simp]
/-
**Homeomorph.map_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：map_cocompact (h : X ≃ₜ Y) : map h (cocompact X) = cocompact Y
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.comap_cocompact`：comap_cocompact (h : X ≃ₜ Y) : comap h (coco
mpact Y) = cocompact X
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
theorem map_cocompact (h : X ≃ₜ Y) : map h (cocompact X) = cocompact Y := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]
/-
**Homeomorph.compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   CompactSpace Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isCompact_preimage`：isCompact_preimage {s : Set Y} (h : X ≃ₜ 
Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ
/-
**Homeomorph.isDenseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbedding h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbedding h :=
  { h.isEmbedding with dense := h.surjective.denseRange }
/-
**Homeomorph.totallyDisconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y)   [tdc : TotallyDisconnectedSpace X], TotallyDiscon
nectedSpace Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `totallyDisconnectedSpace_iff`：∀ (α : Type u) [inst : TopologicalSpace α]
, TotallyDisconnectedSpace α ↔ IsTotallyDisconnected Set.univ
· 使用引理 `Topology.IsEmbedding.isTotallyDisconnected_range`：Topology.IsEmbedding.i
sTotallyDisconnected_range [TopologicalSpace β] {f : α -> β} (hf : IsEmbedding f
) : IsTotallyDisconnected (range f) ↔ …
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Homeomorph.range_coe`：range_coe (h : X ≃ₜ Y) : range h = univ
-/
protected lemma totallyDisconnectedSpace (h : X ≃ₜ Y) [tdc : TotallyDisconnectedSpace X] :
    TotallyDisconnectedSpace Y :=
  (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[simp]
/-
**Homeomorph.map_punctured_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[!=] x) = 𝓝[!=] (h x)
参数：h : X ≃ₜ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Homeomorph.image_compl`：image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ)
 = (h '' s)ᶜ
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[≠] x) = 𝓝[≠] (h x) := by
  convert! h.isEmbedding.map_nhdsWithin_eq ({ x }ᶜ) x
  rw [h.image_compl, Set.image_singleton]

@[simp]
/-
**Homeomorph.comap_coclosedCompact** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comap_coclosedCompact (h : X ≃ₜ Y) : comap h (coclosedCompact Y) = coclose
dCompact X
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.HasBasis.comp_surjective`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : S
ort u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {g 
: ι' → ι}, Function.S…
· 使用定理 `Function.Injective.preimage_surjective`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β}, Function.Injective f → Function.Surjective (Set.preimage f)
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
-/
theorem comap_coclosedCompact (h : X ≃ₜ Y) : comap h (coclosedCompact Y) = coclosedCompact X :=
  (hasBasis_coclosedCompact.comap h).eq_of_same_basis <| by
    simpa [comp_def] using hasBasis_coclosedCompact.comp_surjective h.injective.preimage_surjective

@[simp]
/-
**Homeomorph.map_coclosedCompact** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：map_coclosedCompact (h : X ≃ₜ Y) : map h (coclosedCompact X) = coclosedCom
pact Y
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.comap_coclosedCompact`：comap_coclosedCompact (h : X ≃ₜ Y) : c
omap h (coclosedCompact Y) = coclosedCompact X
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
theorem map_coclosedCompact (h : X ≃ₜ Y) : map h (coclosedCompact X) = coclosedCompact Y := by
  rw [← h.comap_coclosedCompact, map_comap_of_surjective h.surjective]

/-- If the codomain of a homeomorphism is a locally connected space, then the domain is also
a locally connected space. -/
/-
**Homeomorph.locallyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：locallyConnectedSpace [i : LocallyConnectedSpace Y] (h : X ≃ₜ Y) : Locally
ConnectedSpace X
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.symm_map_nhds_eq`：symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map
 h.symm (𝓝 (h x)) = 𝓝 x
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
· 使用定理 `locallyConnectedSpace_of_connected_bases`：locallyConnectedSpace_of_conne
cted_bases {ι : Type*} (b : α -> ι -> Set α) (p : α -> ι -> Prop) (hbasis : fora
ll x, (𝓝 x).HasBasis (p x) (b …
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h

--- 原说明 ---
If the codomain of a homeomorphism is a locally connected space, then the domain
 is also
a locally connected space.
-/
theorem locallyConnectedSpace [i : LocallyConnectedSpace Y] (h : X ≃ₜ Y) :
    LocallyConnectedSpace X := by
  have : ∀ x, (𝓝 x).HasBasis (fun s ↦ IsOpen s ∧ h x ∈ s ∧ IsConnected s)
      (h.symm '' ·) := fun x ↦ by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs ↦ ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuousOn

/-- The codomain of a homeomorphism is a locally compact space if and only if
the domain is a locally compact space. -/
/-
**Homeomorph.locallyCompactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：locallyCompactSpace_iff (h : X ≃ₜ Y) : LocallyCompactSpace X ↔ LocallyComp
actSpace Y
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Type
 u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactS
pace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `Topology.IsClosedEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompac
tSpace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h

--- 原说明 ---
The codomain of a homeomorphism is a locally compact space if and only if
the domain is a locally compact space.
-/
theorem locallyCompactSpace_iff (h : X ≃ₜ Y) :
    LocallyCompactSpace X ↔ LocallyCompactSpace Y := by
  exact ⟨fun _ => h.symm.isOpenEmbedding.locallyCompactSpace,
    fun _ => h.isClosedEmbedding.locallyCompactSpace⟩

@[simp]
/-
**Homeomorph.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuousOn_iff (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z) : ContinuousOn
 (h ∘ f) s ↔ ContinuousOn f s
参数：h : X ≃ₜ Y；f : Z -> X；s : Set Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem comp_continuousOn_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.isInducing.continuousOn_iff.symm
/-
**Homeomorph.comp_continuousWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuousWithinAt_iff (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z) (z : Z) 
: ContinuousWithinAt f s z ↔ ContinuousWithinAt (h ∘ f) s z
参数：h : X ≃ₜ Y；f : Z -> X；s : Set Z；z : Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousWithinAt_iff`：Topology.IsInducing.continuo
usWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} {x : α}
 : ContinuousWithinAt f s x ↔ Co…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem comp_continuousWithinAt_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) (z : Z) :
    ContinuousWithinAt f s z ↔ ContinuousWithinAt (h ∘ f) s z :=
  h.isInducing.continuousWithinAt_iff

set_option backward.defeqAttrib.useBackward true in
/-- A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between subtypes corresponding to
predicates `p : X → Prop` and `q : Y → Prop` so long as `p = q ∘ h`. -/
@[simps!]
/-
**Homeomorph.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：subtype {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : forall x, p 
x ↔ q (h x)) : {x // p x} ≃ₜ {y // q y} where __
参数：h : X ≃ₜ Y；h_iff : forall x, p x ↔ q (h x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between subtypes correspon
ding to
predicates `p : X → Prop` and `q : Y → Prop` so long as `p = q ∘ h`.
-/
def subtype {p : X → Prop} {q : Y → Prop} (h : X ≃ₜ Y) (h_iff : ∀ x, p x ↔ q (h x)) :
    {x // p x} ≃ₜ {y // q y} where
  __ := h.subtypeEquiv h_iff

@[simp]
/-
**Homeomorph.subtype_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：subtype_toEquiv {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : fora
ll x, p x ↔ q (h x)) : (h.subtype h_iff).toEquiv = h.toEquiv.subtypeEquiv h_iff
参数：h : X ≃ₜ Y；h_iff : forall x, p x ↔ q (h x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_toEquiv {p : X → Prop} {q : Y → Prop} (h : X ≃ₜ Y) (h_iff : ∀ x, p x ↔ q (h x)) :
    (h.subtype h_iff).toEquiv = h.toEquiv.subtypeEquiv h_iff :=
  rfl

/-- A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between sets `s : Set X` and `t : Set Y`
whenever `h` maps `s` onto `t`. -/
/-
**Homeomorph.sets** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homeomorph`。
形式化陈述：sets {s : Set X} {t : Set Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t) : s ≃ₜ t
参数：h : X ≃ₜ Y；h_eq : s = h ⁻¹' t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between sets `s : Set X` a
nd `t : Set Y`
whenever `h` maps `s` onto `t`.
-/
abbrev sets {s : Set X} {t : Set Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t) : s ≃ₜ t :=
  h.subtype <| Set.ext_iff.mp h_eq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If two sets are equal, then they are homeomorphic. -/
/-
**Homeomorph.setCongr** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：setCongr {s t : Set X} (h : s = t) : s ≃ₜ t where toEquiv
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets are equal, then they are homeomorphic.
-/
def setCongr {s t : Set X} (h : s = t) : s ≃ₜ t where
  toEquiv := Equiv.setCongr h

section prod

variable (X Y W Z)

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
/-
**Homeomorph.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodUnique [Unique Y] : X × Y ≃ₜ X where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X × {*}` is homeomorphic to `X`.
-/
def prodUnique [Unique Y] :
    X × Y ≃ₜ X where
  toEquiv := Equiv.prodUnique X Y
/-
**Homeomorph.coe_prodUnique** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ (X : Type u_1) (Y : Type u_2) [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Unique Y],   ⇑(Homeomorph.prodUnique X Y) = Prod.fst
参数：X : Type u_1；Y : Type u_2；Homeomorph.prodUnique X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_prodUnique [Unique Y] : ⇑(prodUnique X Y) = Prod.fst := rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
/-
**Homeomorph.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：uniqueProd (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [Unique
 X] : X × Y ≃ₜ Y
参数：X Y : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X × {*}` is homeomorphic to `X`.
-/
def uniqueProd (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [Unique X] :
    X × Y ≃ₜ Y :=
  (prodComm _ _).trans (prodUnique Y X)
/-
**Homeomorph.coe_uniqueProd** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ (X : Type u_1) (Y : Type u_2) [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Unique X],   ⇑(Homeomorph.uniqueProd X Y) = Prod.snd
参数：X : Type u_1；Y : Type u_2；Homeomorph.uniqueProd X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_uniqueProd [Unique X] : ⇑(uniqueProd X Y) = Prod.snd := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The product over `S ⊕ T` of a family of topological spaces
is homeomorphic to the product of (the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `Homeomorph`.
-/
/-
**Homeomorph.sumPiEquivProdPi** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumPiEquivProdPi (S T : Type*) (A : S oplus T -> Type*) [forall st, Topolo
gicalSpace (A st)] : (Π (st : S oplus T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π 
(t : T), A (.inr t)) where __
参数：S T : Type*；A : S oplus T -> Type*；A st。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product over `S ⊕ T` of a family of topological spaces
is homeomorphic to the product of (the product over `S`) and (the product over `
T`).

This is `Equiv.sumPiEquivProdPi` as a `Homeomorph`.
-/
def sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  continuous_invFun := continuous_pi <| by rintro (s | t) <;> dsimp <;> fun_prop

/-- The product `Π t : α, f t` of a family of topological spaces is homeomorphic to the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
@[simps! -fullyApplied]
/-
**Homeomorph.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piUnique {α : Type*} [Unique α] (f : α -> Type*) [forall x, TopologicalSpa
ce (f x)] : (Π t, f t) ≃ₜ f default
参数：f : α -> Type*；f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `Π t : α, f t` of a family of topological spaces is homeomorphic to 
the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
def piUnique {α : Type*} [Unique α] (f : α → Type*) [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃ₜ f default :=
  (Equiv.piUnique f).toHomeomorphOfContinuousOpen (continuous_apply default) (isOpenMap_eval _)

end prod

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps +simpRhs toEquiv, simps! -isSimp apply]
/-
**Homeomorph.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piCongrLeft {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (
Y j)] (e : ι ≃ ι') : (forall i, Y (e i)) ≃ₜ forall j, Y j where continuous_toFun
参数：Y j；e : ι ≃ ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`.
-/
def piCongrLeft {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ₜ ∀ j, Y j where
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
/-
**Homeomorph.piCongrLeft_refl** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：piCongrLeft_refl {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace 
(X i)] : piCongrLeft (.refl ι) = .refl (forall i, X i)
参数：X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma piCongrLeft_refl {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (∀ i, X i) :=
  rfl

@[simp]
/-
**Homeomorph.piCongrLeft_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：piCongrLeft_symm_apply {ι ι' : Type*} {Y : ι' -> Type*} [forall j, Topolog
icalSpace (Y j)] (e : ι ≃ ι') : ⇑(piCongrLeft (Y
参数：Y j；e : ι ≃ ι'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piCongrLeft_symm_apply {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (Y := Y) e).symm = (· <| e ·) :=
  rfl

@[simp]
/-
**Homeomorph.piCongrLeft_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：piCongrLeft_apply_apply {ι ι' : Type*} {Y : ι' -> Type*} [forall j, Topolo
gicalSpace (Y j)] (e : ι ≃ ι') (x : forall i, Y (e i)) (i : ι) : piCongrLeft e x
 (e i) = x i
参数：Y j；e : ι ≃ ι'；x : forall i, Y (e i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') (x : ∀ i, Y (e i)) (i : ι) : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

set_option backward.defeqAttrib.useBackward true in
/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
/-
**Homeomorph.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piCongrRight {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalSpace 
(Y₁ i)] [forall i, TopologicalSpace (Y₂ i)] (F : forall i, Y₁ i ≃ₜ Y₂ i) : (fora
ll i, Y₁ i) ≃ₜ forall i, Y₂ i where toEquiv
参数：Y₁ i；Y₂ i；F : forall i, Y₁ i ≃ₜ Y₂ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i
`.
-/
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) : (∀ i, Y₁ i) ≃ₜ ∀ i, Y₂ i where
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
/-
**Homeomorph.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalS
pace (Y₁ i)] [forall i, TopologicalSpace (Y₂ i)] (F : forall i, Y₁ i ≃ₜ Y₂ i) : 
(piCongrRight F).symm = piCongrRight fun i => (F i).symm
参数：Y₁ i；Y₂ i；F : forall i, Y₁ i ≃ₜ Y₂ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
/-
**Homeomorph.piCongr** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ -> Type*} {Y₂ : ι₂ -> Type*} [forall i₁, 
TopologicalSpace (Y₁ i₁)] [forall i₂, TopologicalSpace (Y₂ i₂)] (e : ι₁ ≃ ι₂) (F
 : forall i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (forall i₁, Y₁ i₁) ≃ₜ forall i₂, Y₂ i₂
参数：Y₁ i₁；Y₂ i₂；e : ι₁ ≃ ι₂；F : forall i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphis
ms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`.
-/
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ → Type*} {Y₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (Y₁ i₁)] [∀ i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (∀ i₁, Y₁ i₁) ≃ₜ ∀ i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

/-- `ULift X` is homeomorphic to `X`. -/
/-
**Homeomorph.ulift.** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift X` is homeomorphic to `X`.
-/
def ulift.{u, v} {X : Type v} [TopologicalSpace X] : ULift.{u, v} X ≃ₜ X where
  toEquiv := Equiv.ulift

set_option backward.isDefEq.respectTransparency false in
/-- The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism. -/
@[simps!]
/-
**Homeomorph.sumArrowHomeomorphProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι oplus ι' -> X) ≃ₜ (ι -> X)
 × (ι' -> X) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism.
-/
def sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X) where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    dsimp [Equiv.sumArrowEquivProdArrow]
    fun_prop
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd
/-
**Homeomorph._root_.Fin.appendEquiv_eq_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Hom
eomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem _root_.Fin.appendEquiv_eq_homeomorph (m n : ℕ) : Fin.appendEquiv m n =
    (sumArrowHomeomorphProdArrow.symm.trans
    (piCongrLeft (Y := fun _ ↦ X) finSumFinEquiv)).toEquiv := by
  apply Equiv.symm_bijective.injective
  ext x i <;> simp

@[fun_prop]
/-
**Homeomorph._root_.Fin.continuous_append** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fin.continuous_append (m n : ℕ) :
    Continuous fun (p : (Fin m → X) × (Fin n → X)) ↦ Fin.append p.1 p.2 := by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_homeomorph]
  exact Homeomorph.continuous_toFun _

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) → X`.
`Fin.appendEquiv` as a homeomorphism -/
@[simps!]
/-
**Homeomorph._root_.Fin.appendHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) →
 X`.
`Fin.appendEquiv` as a homeomorphism
-/
def _root_.Fin.appendHomeomorph (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toEquiv := Fin.appendEquiv m n

@[simp]
/-
**Homeomorph._root_.Fin.appendHomeomorph_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Home
omorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fin.appendHomeomorph_toEquiv (m n : ℕ) :
    (Fin.appendHomeomorph (X := X) m n).toEquiv = Fin.appendEquiv m n :=
  rfl

section Distrib

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
@[simps! apply symm_apply toEquiv]
/-
**Homeomorph.sigmaProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`.
-/
def sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y :=
  Homeomorph.symm <|
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

end Distrib

set_option backward.defeqAttrib.useBackward true in
/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
/-
**Homeomorph.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι -> X) ≃ₜ X wh
ere toEquiv
参数：ι X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` has a unique element, then `ι → X` is homeomorphic to `X`.
-/
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι → X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X

/-- Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`. -/
@[simps! -fullyApplied]
/-
**Homeomorph.piFinTwo.** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`.
-/
def piFinTwo.{u} (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)] : (∀ i, X i) ≃ₜ X 0 × X 1 where
  toEquiv := piFinTwoEquiv X

/-- Homeomorphism between `X² = Fin 2 → X` and `X × X`. -/
@[simps! -fullyApplied]
/-
**Homeomorph.finTwoArrow** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：finTwoArrow : (Fin 2 -> X) ≃ₜ X × X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between `X² = Fin 2 → X` and `X × X`.
-/
def finTwoArrow : (Fin 2 → X) ≃ₜ X × X :=
  { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
/-
**Homeomorph.image** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where -- TODO: by continuity!
 continuous_toFun
参数：e : X ≃ₜ Y；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a topological space is homeomorphic to its image under a homeomorphi
sm.
-/
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.mapsToRestrict (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
/-
**Homeomorph.Set.univ** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph.Set`。
形式化陈述：(X : Type u_7) → [inst : TopologicalSpace X] → ↑Set.univ ≃ₜ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.univ X` is homeomorphic to `X`.
-/
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
/-
**Homeomorph.Set.prod** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph.Set`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] → [ins
t_1 : TopologicalSpace Y] → (s : Set X) → (t : Set Y) → ↑(s ×ˢ t) ≃ₜ ↑s × ↑t
参数：s : Set X；t : Set Y；s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ×ˢ t` is homeomorphic to `s × t`.
-/
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prodMk continuous_subtype_val.snd').subtype_mk _

section

variable {ι : Type*}

/-- The topological space `Π i, Y i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not. -/
@[simps!]
/-
**Homeomorph.piEquivPiSubtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piEquivPiSubtypeProd (p : ι -> Prop) (Y : ι -> Type*) [forall i, Topologic
alSpace (Y i)] [DecidablePred p] : (forall i, Y i) ≃ₜ (forall i : { x // p x }, 
Y i) × forall i : { x // ¬p x }, Y i where toEquiv
参数：p : ι -> Prop；Y : ι -> Type*；Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological space `Π i, Y i` can be split as a product by separating the ind
ices in ι
  depending on whether they satisfy a predicate p or not.
-/
def piEquivPiSubtypeProd (p : ι → Prop) (Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
    [DecidablePred p] : (∀ i, Y i) ≃ₜ (∀ i : { x // p x }, Y i) × ∀ i : { x // ¬p x }, Y i where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]

variable [DecidableEq ι] (i : ι)

/-- A product of topological spaces can be split as the binary product of one of the spaces and
  the product of all the remaining spaces. -/
@[simps!]
/-
**Homeomorph.piSplitAt** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：piSplitAt (Y : ι -> Type*) [forall j, TopologicalSpace (Y j)] : (forall j,
 Y j) ≃ₜ Y i × forall j : { j // j != i }, Y j where toEquiv
参数：Y : ι -> Type*；Y j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of topological spaces can be split as the binary product of one of the
 spaces and
  the product of all the remaining spaces.
-/
def piSplitAt (Y : ι → Type*) [∀ j, TopologicalSpace (Y j)] :
    (∀ j, Y j) ≃ₜ Y i × ∀ j : { j // j ≠ i }, Y j where
  toEquiv := Equiv.piSplitAt i Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd

variable (Y)

/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps!]
/-
**Homeomorph.funSplitAt** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：funSplitAt : (ι -> Y) ≃ₜ Y × ({ j // j != i } -> Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of copies of a topological space can be split as the binary product of
 one copy and
  the product of all the remaining copies.
-/
def funSplitAt : (ι → Y) ≃ₜ Y × ({ j // j ≠ i } → Y) :=
  piSplitAt i _

end

end Homeomorph

namespace Topology.IsEmbedding

/-- Homeomorphism given an embedding. -/
@[simps! apply_coe]
/-
**Topology.IsEmbedding.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsEmbedd
ing`。
形式化陈述：toHomeomorph {f : X -> Y} (hf : IsEmbedding f) : X ≃ₜ Set.range f
参数：hf : IsEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…

--- 原说明 ---
Homeomorphism given an embedding.
-/
noncomputable def toHomeomorph {f : X → Y} (hf : IsEmbedding f) :
    X ≃ₜ Set.range f :=
  Equiv.ofInjective f hf.injective |>.toHomeomorphOfIsInducing <|
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

@[simp]
/-
**Topology.IsEmbedding.toHomeomorph_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gy.IsEmbedding`。
形式化陈述：toHomeomorph_symm_apply {f : X -> Y} (hf : IsEmbedding f) (x : X) : hf.toH
omeomorph.symm ⟨f x, by simp⟩ = x
参数：hf : IsEmbedding f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `Topology.IsEmbedding.toHomeomorph_apply_coe`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y}   (hf
 : Topology.IsEmbedding f) (a : X…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toHomeomorph_symm_apply {f : X → Y} (hf : IsEmbedding f) (x : X) :
    hf.toHomeomorph.symm ⟨f x, by simp⟩ = x :=
  hf.toHomeomorph.injective (by ext; simp)

/-- A surjective embedding is a homeomorphism. -/
@[simps! apply]
/-
**Topology.IsEmbedding.toHomeomorphOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Topol
ogy.IsEmbedding`。
形式化陈述：toHomeomorphOfSurjective {f : X -> Y} (hf : IsEmbedding f) (hsurj : Functi
on.Surjective f) : X ≃ₜ Y
参数：hf : IsEmbedding f；hsurj : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…

--- 原说明 ---
A surjective embedding is a homeomorphism.
-/
noncomputable def toHomeomorphOfSurjective {f : X → Y}
    (hf : IsEmbedding f) (hsurj : Function.Surjective f) : X ≃ₜ Y :=
  Equiv.ofBijective f ⟨hf.injective, hsurj⟩ |>.toHomeomorphOfIsInducing hf.toIsInducing

/-- A set is homeomorphic to its image under any embedding. -/
/-
**Topology.IsEmbedding.homeomorphImage** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsEmb
edding`。
形式化陈述：homeomorphImage {f : X -> Y} (hf : IsEmbedding f) (s : Set X) : s ≃ₜ f '' 
s
参数：hf : IsEmbedding f；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is homeomorphic to its image under any embedding.
-/
noncomputable def homeomorphImage {f : X → Y} (hf : IsEmbedding f) (s : Set X) : s ≃ₜ f '' s :=
  (hf.comp .subtypeVal).toHomeomorph.trans <| .setCongr <| by simp [Set.range_comp]

/-- An embedding restricts to a homeomorphism between the preimage and any subset of its range. -/
/-
**Topology.IsEmbedding.homeomorphOfSubsetRange** 是 Mathlib 中的一个定义，位于命名空间 `Topolo
gy.IsEmbedding`。
形式化陈述：homeomorphOfSubsetRange {f : X -> Y} (hf : IsEmbedding f) {s : Set Y} (hs 
: s subseteq Set.range f) : (f ⁻¹' s) ≃ₜ s
参数：hf : IsEmbedding f；hs : s subseteq Set.range f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s

--- 原说明 ---
An embedding restricts to a homeomorphism between the preimage and any subset of
 its range.
-/
noncomputable def homeomorphOfSubsetRange {f : X → Y} (hf : IsEmbedding f)
    {s : Set Y} (hs : s ⊆ Set.range f) : (f ⁻¹' s) ≃ₜ s :=
  hf.homeomorphImage (f ⁻¹' s) |>.trans <| .setCongr <| Set.image_preimage_eq_of_subset hs

@[simp]
/-
**Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe** 是 Mathlib 中的一个定理，位于命名
空间 `Topology.IsEmbedding`。
形式化陈述：homeomorphOfSubsetRange_apply_coe {f : X -> Y} (hf : IsEmbedding f) {s : S
et Y} (hs : s subseteq Set.range f) (x : f ⁻¹' s) : ↑(hf.homeomorphOfSubsetRange
 hs x) = f ↑x
参数：hf : IsEmbedding f；hs : s subseteq Set.range f；x : f ⁻¹' s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeomorphOfSubsetRange_apply_coe {f : X → Y} (hf : IsEmbedding f)
    {s : Set Y} (hs : s ⊆ Set.range f) (x : f ⁻¹' s) :
    ↑(hf.homeomorphOfSubsetRange hs x) = f ↑x := rfl

end Topology.IsEmbedding

/-
**Topology.IsEmbedding.uliftMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.uliftMap {f : X -> Y} (hf : IsEmbedding f) : IsEmbedd
ing (ULift.map f)
参数：hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
lemma Topology.IsEmbedding.uliftMap {f : X → Y} (hf : IsEmbedding f) :
    IsEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isEmbedding (.comp hf <| Homeomorph.ulift.isEmbedding)
/-
**Topology.IsOpenEmbedding.uliftMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.uliftMap {f : X -> Y} (hf : IsOpenEmbedding f) : 
IsOpenEmbedding (ULift.map f)
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
lemma Topology.IsOpenEmbedding.uliftMap {f : X → Y} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isOpenEmbedding (.comp hf <| Homeomorph.ulift.isOpenEmbedding)
/-
**Topology.IsClosedEmbedding.uliftMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.uliftMap {f : X -> Y} (hf : IsClosedEmbedding f
) : IsClosedEmbedding (ULift.map f)
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
lemma Topology.IsClosedEmbedding.uliftMap {f : X → Y} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isClosedEmbedding (.comp hf <| Homeomorph.ulift.isClosedEmbedding)

end

namespace Continuous

variable [TopologicalSpace X] [TopologicalSpace Y]

/-
**Continuous.continuous_symm_of_equiv_compact_to_t2** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuous`。
形式化陈述：continuous_symm_of_equiv_compact_to_t2 [CompactSpace X] [T2Space Y] {f : X
 ≃ Y} (hf : Continuous f) : Continuous f.symm
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace X] [T2Space Y] {f : X ≃ Y}
    (hf : Continuous f) : Continuous f.symm := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage_symm] at hC'

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv]
/-
**Continuous.homeoOfEquivCompactToT2** 是 Mathlib 中的一个定义，位于命名空间 `Continuous`。
形式化陈述：homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Con
tinuous f) : X ≃ₜ Y
参数：hf : Continuous f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuous_symm_of_equiv_compact_to_t2`：continuous_symm_of_eq
uiv_compact_to_t2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) :
 Continuous f.symm

--- 原说明 ---
Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`).
-/
def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }

end Continuous

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {W : Type*} [TopologicalSpace W] {f : X → Y}

namespace IsHomeomorph
variable (hf : IsHomeomorph f)
include hf

/-
**IsHomeomorph.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsHomeomorph f → IsClosedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
protected lemma isClosedMap : IsClosedMap f := (hf.homeomorph f).isClosedMap
/-
**IsHomeomorph.isInducing** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isInducing : IsInducing f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
lemma isInducing : IsInducing f := (hf.homeomorph f).isInducing
/-
**IsHomeomorph.isQuotientMap** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isQuotientMap : IsQuotientMap f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
lemma isQuotientMap : IsQuotientMap f := (hf.homeomorph f).isQuotientMap
/-
**IsHomeomorph.isEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isEmbedding : IsEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
lemma isEmbedding : IsEmbedding f := (hf.homeomorph f).isEmbedding
/-
**IsHomeomorph.isOpenEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isOpenEmbedding : IsOpenEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
lemma isOpenEmbedding : IsOpenEmbedding f := (hf.homeomorph f).isOpenEmbedding
/-
**IsHomeomorph.isClosedEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isClosedEmbedding : IsClosedEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
lemma isClosedEmbedding : IsClosedEmbedding f := (hf.homeomorph f).isClosedEmbedding
/-
**IsHomeomorph.isDenseEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：isDenseEmbedding : IsDenseEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isDenseEmbedding`：isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbe
dding h
-/
lemma isDenseEmbedding : IsDenseEmbedding f := (hf.homeomorph f).isDenseEmbedding

end IsHomeomorph

/-- A map is a homeomorphism iff it is the map underlying a bundled homeomorphism `h : X ≃ₜ Y`. -/
/-
**isHomeomorph_iff_exists_homeomorph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isHomeomorph_iff_exists_homeomorph : IsHomeomorph f ↔ exists h : X ≃ₜ Y, h
 = f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h

--- 原说明 ---
A map is a homeomorphism iff it is the map underlying a bundled homeomorphism `h
 : X ≃ₜ Y`.
-/
lemma isHomeomorph_iff_exists_homeomorph : IsHomeomorph f ↔ ∃ h : X ≃ₜ Y, h = f :=
  ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

/-- A map is a homeomorphism iff it is continuous and has a continuous inverse. -/
/-
**isHomeomorph_iff_exists_inverse** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isHomeomorph_iff_exists_inverse : IsHomeomorph f ↔ Continuous f ∧ exists g
 : Y -> X, LeftInverse g f ∧ RightInverse g f ∧ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A map is a homeomorphism iff it is continuous and has a continuous inverse.
-/
lemma isHomeomorph_iff_exists_inverse : IsHomeomorph f ↔ Continuous f ∧ ∃ g : Y → X,
    LeftInverse g f ∧ RightInverse g f ∧ Continuous g := by
  refine ⟨fun hf ↦ ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ ↦ ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

/-- An equivalence between topological spaces is a homeomorphism iff it is continuous in both
directions. -/
/-
**Equiv.isHomeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.isHomeomorph_iff (e : X ≃ Y) : IsHomeomorph e ↔ Continuous e ∧ Conti
nuous e.symm
参数：e : X ≃ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.continuous_symm_iff`：Equiv.continuous_symm_iff (e : X ≃ Y) : Conti
nuous e.symm ↔ IsOpenMap e
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsOpen
Map f
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
An equivalence between topological spaces is a homeomorphism iff it is continuou
s in both
directions.
-/
theorem Equiv.isHomeomorph_iff (e : X ≃ Y) :
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm := by
  rw [e.continuous_symm_iff]
  exact ⟨fun h ↦ ⟨h.continuous, h.isOpenMap⟩, fun ⟨hc, ho⟩ ↦ ⟨hc, ho, e.bijective⟩⟩

/-- A map is a homeomorphism iff it is a surjective embedding. -/
/-
**isHomeomorph_iff_isEmbedding_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isHomeomorph_iff_isEmbedding_surjective : IsHomeomorph f ↔ IsEmbedding f ∧
 Surjective f where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsHomeomorph.isEmbedding`：isEmbedding : IsEmbedding f
· 使用定理 `IsHomeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Funct
ion.Surjectiv…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isOpenEmbedding_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topo
logicalSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsOpenEmbeddin
g f ↔ Topology.IsE…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…

--- 原说明 ---
A map is a homeomorphism iff it is a surjective embedding.
-/
lemma isHomeomorph_iff_isEmbedding_surjective : IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where
  mp hf := ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

/-- A map is a homeomorphism iff it is a quotient map and injective. -/
/-
**isHomeomorph_iff_isQuotientMap_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isHomeomorph_iff_isQuotientMap_injective {f : X -> Y} : IsHomeomorph f ↔ I
sQuotientMap f ∧ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsHomeomorph.isQuotientMap`：isQuotientMap : IsQuotientMap f
· 使用定理 `IsHomeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Injective…
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…

--- 原说明 ---
A map is a homeomorphism iff it is a quotient map and injective.
-/
lemma isHomeomorph_iff_isQuotientMap_injective {f : X → Y} :
    IsHomeomorph f ↔ IsQuotientMap f ∧ Injective f := by
  refine ⟨fun h ↦ ⟨h.isQuotientMap, h.injective⟩,
    fun h ↦ ⟨h.1.continuous, fun s hs ↦ ?_, h.2, h.1.surjective⟩⟩
  rwa [← h.1.isOpen_preimage, Set.preimage_image_eq _ h.2]

/-- A map is a homeomorphism iff it is continuous, closed and bijective. -/
/-
**isHomeomorph_iff_continuous_isClosedMap_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：isHomeomorph_iff_continuous_isClosedMap_bijective : IsHomeomorph f ↔ Conti
nuous f ∧ IsClosedMap f ∧ Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsHomeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsCl
osedMap f
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ

--- 原说明 ---
A map is a homeomorphism iff it is continuous, closed and bijective.
-/
lemma isHomeomorph_iff_continuous_isClosedMap_bijective : IsHomeomorph f ↔
    Continuous f ∧ IsClosedMap f ∧ Function.Bijective f :=
  ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

/-- A map from a compact space to a T2 space is a homeomorphism iff it is continuous and
  bijective. -/
/-
**isHomeomorph_iff_continuous_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isHomeomorph_iff_continuous_bijective [CompactSpace X] [T2Space Y] : IsHom
eomorph f ↔ Continuous f ∧ Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isHomeomorph_iff_continuous_isClosedMap_bijective`：isHomeomorph_iff_cont
inuous_isClosedMap_bijective : IsHomeomorph f ↔ Continuous f ∧ IsClosedMap f ∧ F
unction.Bijective f
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A map from a compact space to a T2 space is a homeomorphism iff it is continuous
 and
  bijective.
-/
lemma isHomeomorph_iff_continuous_bijective [CompactSpace X] [T2Space Y] :
    IsHomeomorph f ↔ Continuous f ∧ Bijective f := by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf ↦ ?_
  rw [eq_true hf.isClosedMap, true_and]
/-
**IsHomeomorph.sumMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHomeomorph.sumMap {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph 
g) : IsHomeomorph (Sum.map f g)
参数：hf : IsHomeomorph f；hg : IsHomeomorph g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sumMap`：Continuous.sumMap {f : X -> Y} {g : Z -> W} (hf : Con
tinuous f) (hg : Continuous g) : Continuous (Sum.map f g)
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsOpenMap.sumMap`：IsOpenMap.sumMap {f : X -> Y} {g : Z -> W} (hf : IsOpe
nMap f) (hg : IsOpenMap g) : IsOpenMap (Sum.map f g)
· 使用定理 `IsHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsOpen
Map f
· 使用定理 `Function.Bijective.sumMap`：∀ {α : Type u} {α' : Type w} {β : Type v} {β'
 : Type x} {f : α → β} {g : α' → β'},   Function.Bijective f → Function.Bijectiv
e g → Function.…
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
-/
lemma IsHomeomorph.sumMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Sum.map f g) := ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩
/-
**IsHomeomorph.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHomeomorph.prodMap {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph
 g) : IsHomeomorph (Prod.map f g)
参数：hf : IsHomeomorph f；hg : IsHomeomorph g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsOpenMap.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topol
ogicalS…
· 使用定理 `IsHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsOpen
Map f
· 使用定理 `Function.Bijective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Bijective f → Function.Bij
ective g → Funct…
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
-/
lemma IsHomeomorph.prodMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Prod.map f g) := ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩
/-
**IsHomeomorph.sigmaMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHomeomorph.sigmaMap {ι κ : Type*} {X : ι -> Type*} {Y : κ -> Type*} [for
all i, TopologicalSpace (X i)] [forall i, TopologicalSpace (Y i)] {f : ι -> κ} (
hf : Bijective f) {g : (i : ι) -> X i -> Y (f i)} (hg : forall i, IsHomeomorph (
g i)) : IsHomeomorph (Sigma.map f g)
参数：X i；Y i；hf : Bijective f；i : ι；f i；hg : forall i, IsHomeomorph (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isEmbedding_sigmaMap`：Topology.isEmbedding_sigmaMap {f₁ : ι -> 
κ} {f₂ : forall i, σ i -> τ (f₁ i)} (h : Injective f₁) : IsEmbedding (Sigma.map 
f₁ f₂) ↔ forall i, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.sigma_map`：Function.Surjective.sigma_map {f₁ : α₁ ->
 α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)} (h₁ : Surjective f₁) (h₂ : forall a, Sur
jective (f₂ a)) : S…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsHomeomorph.sigmaMap {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] {f : ι → κ}
    (hf : Bijective f) {g : (i : ι) → X i → Y (f i)} (hg : ∀ i, IsHomeomorph (g i)) :
    IsHomeomorph (Sigma.map f g) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i ↦ (hg i).1, hf.2.sigma_map fun i ↦ (hg i).2⟩
/-
**IsHomeomorph.pi_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHomeomorph.pi_map {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalS
pace (X i)] [forall i, TopologicalSpace (Y i)] {f : (i : ι) -> X i -> Y i} (h : 
forall i, IsHomeomorph (f i)) : IsHomeomorph (fun (x : forall i, X i) i => f i (
x i))
参数：X i；Y i；i : ι；h : forall i, IsHomeomorph (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
lemma IsHomeomorph.pi_map {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsHomeomorph (f i)) :
    IsHomeomorph (fun (x : ∀ i, X i) i ↦ f i (x i)) :=
  (Homeomorph.piCongrRight fun i ↦ (h i).homeomorph (f i)).isHomeomorph

/-- A bijection between discrete topological spaces induces a homeomorphism. -/
/-
**Homeomorph.ofDiscrete** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.ofDiscrete [DiscreteTopology X] [DiscreteTopology Y] (f : X ≃ Y
) : X ≃ₜ Y where toEquiv
参数：f : X ≃ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bijection between discrete topological spaces induces a homeomorphism.
-/
def Homeomorph.ofDiscrete [DiscreteTopology X] [DiscreteTopology Y] (f : X ≃ Y) : X ≃ₜ Y where
  toEquiv := f
/-
**Equiv.isHomeomorph_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.isHomeomorph_of_discrete [DiscreteTopology X] [DiscreteTopology Y] (
f : X ≃ Y) : IsHomeomorph f
参数：f : X ≃ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem Equiv.isHomeomorph_of_discrete [DiscreteTopology X] [DiscreteTopology Y]
    (f : X ≃ Y) : IsHomeomorph f :=
  (Homeomorph.ofDiscrete f).isHomeomorph

section

/-- If `f : X → Y` is coinducing and has connected fibers, it induces a homeomorphism on `π₀`. -/
/-
**Topology.IsCoinducing.connectedComponentsHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 
``。
形式化陈述：Topology.IsCoinducing.connectedComponentsHomeomorph {f : X -> Y} (hf : IsC
oinducing f) (hf' : forall y, IsConnected (f ⁻¹' {y})) : ConnectedComponents X ≃
ₜ ConnectedComponents Y
参数：hf : IsCoinducing f；hf' : forall y, IsConnected (f ⁻¹' {y})。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…

--- 原说明 ---
If `f : X → Y` is coinducing and has connected fibers, it induces a homeomorphis
m on `π₀`.
-/
noncomputable def Topology.IsCoinducing.connectedComponentsHomeomorph {f : X → Y}
    (hf : IsCoinducing f) (hf' : ∀ y, IsConnected (f ⁻¹' {y})) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  IsHomeomorph.homeomorph hf.continuous.connectedComponentsMap <| by
    have hbij := hf.connectedComponentsMap_bijective hf'
    exact ⟨hf.continuous.connectedComponentsMap_continuous,
      hf.connectedComponentsMap.isOpenMap_of_injective hbij.injective, hbij⟩

variable {f : X → Y} (hf : Topology.IsCoinducing f) (hf' : ∀ y, IsConnected (f ⁻¹' {y}))

@[simp]
/-
**Topology.IsCoinducing.connectedComponentsHomeomorph_mk** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Topology.IsCoinducing.connectedComponentsHomeomorph_mk (x : X) : hf.connec
tedComponentsHomeomorph hf' (.mk x) = .mk (f x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_mk (x : X) :
    hf.connectedComponentsHomeomorph hf' (.mk x) = .mk (f x) :=
  rfl

@[simp]
/-
**Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply (x : X) 
: (hf.connectedComponentsHomeomorph hf').symm (.mk (f x)) = .mk x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply (x : X) :
    (hf.connectedComponentsHomeomorph hf').symm (.mk (f x)) = .mk x :=
  (hf.connectedComponentsHomeomorph hf').injective (by simp)

end

