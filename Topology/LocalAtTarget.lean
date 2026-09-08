/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Properties of maps that are local at the target or at the source.

We show that the following properties of continuous maps are local at the target :
- `Topology.IsInducing`
- `IsOpenMap`
- `IsClosedMap`
- `Topology.IsEmbedding`
- `Topology.IsOpenEmbedding`
- `Topology.IsClosedEmbedding`
- `GeneralizingMap`

We show that the following properties of continuous maps are local at the source:
- `IsOpenMap`
- `GeneralizingMap`

-/

public section

open Filter Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
variable {ι : Type*} {U : ι → Opens β}

/-
**Set.restrictPreimage_isInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.restrictPreimage_isInducing (s : Set β) (h : IsInducing f) : IsInducin
g (s.restrictPreimage f)
参数：s : Set β；h : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : Topologi
calSpace X] [inst_2 :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
-/
theorem Set.restrictPreimage_isInducing (s : Set β) (h : IsInducing f) :
    IsInducing (s.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← @Filter.comap_comap _ _ _ _ _ f,
    Function.comp_apply] at h ⊢
  intro a
  rw [← h, ← IsInducing.subtypeVal.nhds_eq_comap]

alias Topology.IsInducing.restrictPreimage := Set.restrictPreimage_isInducing
/-
**Set.restrictPreimage_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.restrictPreimage_isEmbedding (s : Set β) (h : IsEmbedding f) : IsEmbed
ding (s.restrictPreimage f)
参数：s : Set β；h : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} [i
nst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} (s : Set β),
   Topology.IsInducing f →…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Function.Injective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t 
: Set β) {f : α → β},   Function.Injective f → Function.Injective (t.restrictPre
image f)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem Set.restrictPreimage_isEmbedding (s : Set β) (h : IsEmbedding f) :
    IsEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding
/-
**Set.restrictPreimage_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
 IsOpenEmbedding (s.restrictPreimage f)
参数：s : Set β；h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} (s : Set β)
,   Topology.IsEmbedding f …
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
-/
theorem Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
    IsOpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding
/-
**Set.restrictPreimage_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding 
f) : IsClosedEmbedding (s.restrictPreimage f)
参数：s : Set β；h : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} (s : Set β)
,   Topology.IsEmbedding f …
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Topology.IsInducing.isClosed_preimage`：isClosed_preimage (h : IsInducing
 f) (s : Set Y) (hs : IsClosed s) : IsClosed (f ⁻¹' s)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
-/
theorem Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding f) :
    IsClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding
/-
**IsClosedMap.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) : IsClosedMap
 (s.restrictPreimage f)
参数：H : IsClosedMap f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_restrictPreimage`：image_restrictPreimage : t.restrictPreimage 
f '' Subtype.val ⁻¹' s = Subtype.val ⁻¹' f '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) :
    IsClosedMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsClosed u → Subtype.val ⁻¹' u = t →
    ∃ v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩
/-
**IsOpenMap.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) : IsOpenMap (s.re
strictPreimage f)
参数：H : IsOpenMap f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_restrictPreimage`：image_restrictPreimage : t.restrictPreimage 
f '' Subtype.val ⁻¹' s = Subtype.val ⁻¹' f '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) :
    IsOpenMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsOpen u → Subtype.val ⁻¹' u = t →
    ∃ v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩
/-
**GeneralizingMap.restrictPreimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GeneralizingMap.restrictPreimage (H : GeneralizingMap f) (s : Set β) : Gen
eralizingMap (s.restrictPreimage f)
参数：H : GeneralizingMap f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma GeneralizingMap.restrictPreimage (H : GeneralizingMap f) (s : Set β) :
    GeneralizingMap (s.restrictPreimage f) := by
  intro x y h
  obtain ⟨a, ha, hy⟩ := H (h.map <| continuous_subtype_val (p := (· ∈ s)))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]
/-
**IsProperMap.restrictPreimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.restrictPreimage (H : IsProperMap f) (s : Set β) : IsProperMap
 (s.restrictPreimage f)
参数：H : IsProperMap f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_isClosedMap_and_compact_fibers`：isProperMap_iff_isClosed
Map_and_compact_fibers : IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ forall y
, IsCompact (f ⁻¹' {y})
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用引理 `IsProperMap.continuous`：IsProperMap.continuous (h : IsProperMap f) : Con
tinuous f
· 使用定理 `IsClosedMap.restrictPreimage`：IsClosedMap.restrictPreimage (H : IsClosed
Map f) (s : Set β) : IsClosedMap (s.restrictPreimage f)
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Set.image_val_preimage_restrictPreimage`：image_val_preimage_restrictPrei
mage {u : Set t} : Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val
 '' u
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
lemma IsProperMap.restrictPreimage (H : IsProperMap f) (s : Set β) :
    IsProperMap (s.restrictPreimage f) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage _, fun y ↦ ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff, image_val_preimage_restrictPreimage, image_singleton]
  exact H.isCompact_preimage isCompact_singleton
/-
**IsOpenQuotientMap.restrictPreimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenQuotientMap.restrictPreimage (H : IsOpenQuotientMap f) (s : Set β) :
 IsOpenQuotientMap (s.restrictPreimage f)
参数：H : IsOpenQuotientMap f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t
 : Set β) {f : α → β},   Function.Surjective f → Function.Surjective (t.restrict
Preimage f)
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.restrictPreimage`：IsOpenMap.restrictPreimage (H : IsOpenMap f)
 (s : Set β) : IsOpenMap (s.restrictPreimage f)
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
lemma IsOpenQuotientMap.restrictPreimage (H : IsOpenQuotientMap f) (s : Set β) :
    IsOpenQuotientMap (s.restrictPreimage f) :=
  ⟨H.surjective.restrictPreimage _, H.continuous.restrictPreimage, H.isOpenMap.restrictPreimage _⟩

namespace TopologicalSpace.IsOpenCover

section LocalAtTarget

variable {U : ι → Opens β} {s : Set β} (hU : IsOpenCover U)
include hU

/-
**TopologicalSpace.IsOpenCover.isOpen_iff_inter** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.IsOpenCover`。
形式化陈述：isOpen_iff_inter : IsOpen s ↔ forall i, IsOpen (s inter U i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
-/
theorem isOpen_iff_inter :
    IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i ↦ H.inter (U i).isOpen
  · intro H
    simpa [← inter_iUnion, hU.iSup_set_eq_univ] using isOpen_iUnion H
/-
**TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.IsOpenCover`。
形式化陈述：isOpen_iff_coe_preimage : IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U 
i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isOpen_iff_inter`：isOpen_iff_inter : IsOpen
 s ↔ forall i, IsOpen (s inter U i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_coe_preimage :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  simp [hU.isOpen_iff_inter (s := s), (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_preimage_eq_inter_range]
/-
**TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isClosed_iff_coe_preimage {s : Set β} : IsClosed s ↔ forall i, IsClosed ((
↑) ⁻¹' s : Set (U i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`：isOpen_iff_coe_pre
image : IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U i))
-/
theorem isClosed_iff_coe_preimage {s : Set β} :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using hU.isOpen_iff_coe_preimage (s := sᶜ)
/-
**TopologicalSpace.IsOpenCover.isLocallyClosed_iff_coe_preimage** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isLocallyClosed_iff_coe_preimage {s : Set β} : IsLocallyClosed s ↔ forall 
i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.coborder_preimage`：Topology.IsOpenEmbedding.cob
order_preimage (hf : IsOpenEmbedding f) (s : Set Y) : coborder (f ⁻¹' s) = f ⁻¹'
 coborder s
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`：isOpen_iff_coe_pre
image : IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U i))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLocallyClosed_iff_coe_preimage {s : Set β} :
    IsLocallyClosed s ↔ ∀ i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  have (i : _) : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s :=
    (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
  simp [isLocallyClosed_iff_isOpen_coborder, hU.isOpen_iff_coe_preimage, this]
/-
**TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage** 是 Mathlib 中的一个定理
，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isOpenMap_iff_restrictPreimage : IsOpenMap f ↔ forall i, IsOpenMap ((U i).
1.restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.restrictPreimage`：IsOpenMap.restrictPreimage (H : IsOpenMap f)
 (s : Set β) : IsOpenMap (s.restrictPreimage f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`：isOpen_iff_coe_pre
image : IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U i))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem isOpenMap_iff_restrictPreimage :
    IsOpenMap f ↔ ∀ i, IsOpenMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i ↦ h.restrictPreimage _, fun H s hs ↦ ?_⟩
  rw [hU.isOpen_iff_coe_preimage]
  intro i
  convert! H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩
/-
**TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isClosedMap_iff_restrictPreimage : IsClosedMap f ↔ forall i, IsClosedMap (
(U i).1.restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.restrictPreimage`：IsClosedMap.restrictPreimage (H : IsClosed
Map f) (s : Set β) : IsClosedMap (s.restrictPreimage f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage`：isClosed_iff_coe
_preimage {s : Set β} : IsClosed s ↔ forall i, IsClosed ((↑) ⁻¹' s : Set (U i))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_compl_comm`：eq_compl_comm : x = yᶜ ↔ y = xᶜ
-/
theorem isClosedMap_iff_restrictPreimage :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs ↦ ?_⟩
  rw [hU.isClosed_iff_coe_preimage]
  intro i
  convert! H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩
/-
**TopologicalSpace.IsOpenCover.isInducing_iff_restrictPreimage** 是 Mathlib 中的一个定
理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isInducing_iff_restrictPreimage (h : Continuous f) : IsInducing f ↔ forall
 i, IsInducing ((U i).1.restrictPreimage f)
参数：h : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : Topologi
calSpace X] [inst_2 :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_eq_top`：iSup_eq_top (hu : IsOpenCover 
u) : ⨆ i, u i = ⊤
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Filter.subtype_coe_map_comap`：subtype_coe_map_comap (s : Set α) (f : Fil
ter α) : map ((↑) : s -> α) (comap ((↑) : s -> α) f) = f ⊓ 𝓟 s
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem isInducing_iff_restrictPreimage (h : Continuous f) :
    IsInducing f ↔ ∀ i, IsInducing ((U i).1.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← Filter.comap_comap]
  constructor
  · intro H i x
    rw [Function.comp_apply, ← H, ← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ iSup U by simp [hU.iSup_eq_top])
    simpa [← ((h.1 _ (U i).2).isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hi⟩, H i ⟨x, hi⟩,
      subtype_coe_map_comap] using preimage_mem_comap ((U i).2.mem_nhds hi)
/-
**TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isEmbedding_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ fora
ll i, IsEmbedding ((U i).1.restrictPreimage f)
参数：h : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `TopologicalSpace.IsOpenCover.isInducing_iff_restrictPreimage`：isInducing
_iff_restrictPreimage (h : Continuous f) : IsInducing f ↔ forall i, IsInducing (
(U i).1.restrictPreimage f)
· 使用定理 `Set.injective_iff_injective_of_iUnion_eq_univ`：injective_iff_injective_o
f_iUnion_eq_univ : Injective f ↔ forall i, Injective ((U i).restrictPreimage f)
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
-/
theorem isEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsEmbedding f ↔ ∀ i, IsEmbedding ((U i).1.restrictPreimage f) := by
  simpa [isEmbedding_iff, forall_and] using and_congr (hU.isInducing_iff_restrictPreimage h)
    (injective_iff_injective_of_iUnion_eq_univ hU.iSup_set_eq_univ)
/-
**TopologicalSpace.IsOpenCover.isOpenEmbedding_iff_restrictPreimage** 是 Mathlib 
中的一个定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isOpenEmbedding_iff_restrictPreimage (h : Continuous f) : IsOpenEmbedding 
f ↔ forall i, IsOpenEmbedding ((U i).1.restrictPreimage f)
参数：h : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage`：isEmbeddi
ng_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ forall i, IsEmbeddi
ng ((U i).1.restrictPreimage f)
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
· 使用定理 `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`：isOpen_iff_coe_pre
image : IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U i))
-/
theorem isOpenEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsOpenEmbedding f ↔ ∀ i, IsOpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isOpenEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isOpen_iff_coe_preimage
/-
**TopologicalSpace.IsOpenCover.isClosedEmbedding_iff_restrictPreimage** 是 Mathli
b 中的一个定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isClosedEmbedding_iff_restrictPreimage (h : Continuous f) : IsClosedEmbedd
ing f ↔ forall i, IsClosedEmbedding ((U i).1.restrictPreimage f)
参数：h : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage`：isEmbeddi
ng_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ forall i, IsEmbeddi
ng ((U i).1.restrictPreimage f)
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
· 使用定理 `TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage`：isClosed_iff_coe
_preimage {s : Set β} : IsClosed s ↔ forall i, IsClosed ((↑) ⁻¹' s : Set (U i))
-/
theorem isClosedEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsClosedEmbedding f ↔ ∀ i, IsClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isClosedEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isClosed_iff_coe_preimage
/-
**TopologicalSpace.IsOpenCover.isHomeomorph_iff_restrictPreimage** 是 Mathlib 中的一
个定理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：isHomeomorph_iff_restrictPreimage (h : Continuous f) : IsHomeomorph f ↔ fo
rall i, IsHomeomorph ((U i).1.restrictPreimage f)
参数：h : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage`：isEmbeddi
ng_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ forall i, IsEmbeddi
ng ((U i).1.restrictPreimage f)
· 使用定理 `Set.surjective_iff_surjective_of_iUnion_eq_univ`：surjective_iff_surjecti
ve_of_iUnion_eq_univ : Surjective f ↔ forall i, Surjective ((U i).restrictPreima
ge f)
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isHomeomorph_iff_restrictPreimage (h : Continuous f) :
    IsHomeomorph f ↔ ∀ i, IsHomeomorph ((U i).1.restrictPreimage f) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective, forall_and,
    ← isEmbedding_iff_restrictPreimage hU h,
    surjective_iff_surjective_of_iUnion_eq_univ hU.iSup_set_eq_univ, Opens.carrier_eq_coe]

omit [TopologicalSpace α] in
/-
**TopologicalSpace.IsOpenCover.denseRange_iff_restrictPreimage** 是 Mathlib 中的一个定
理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：denseRange_iff_restrictPreimage : DenseRange f ↔ forall i, DenseRange ((U 
i).1.restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用引理 `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`：iSup_set_eq_univ (hu : Is
OpenCover u) : ⋃ i, (u i : Set X) = univ
-/
theorem denseRange_iff_restrictPreimage :
    DenseRange f ↔ ∀ i, DenseRange ((U i).1.restrictPreimage f) := by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rw [← iUnion_subset_iff, ← Set.univ_subset_iff, iff_iff_eq]
  congr 1
  exact hU.iSup_set_eq_univ.symm
/-
**TopologicalSpace.IsOpenCover.generalizingMap_iff_restrictPreimage** 是 Mathlib 
中的一个引理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：generalizingMap_iff_restrictPreimage : GeneralizingMap f ↔ forall i, Gener
alizingMap ((U i).1.restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GeneralizingMap.restrictPreimage`：GeneralizingMap.restrictPreimage (H : 
GeneralizingMap f) (s : Set β) : GeneralizingMap (s.restrictPreimage f)
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subtype_specializes_iff`：subtype_specializes_iff {p : X -> Prop} (x y : 
Subtype p) : x ⤳ y ↔ (x : X) ⤳ y
-/
lemma generalizingMap_iff_restrictPreimage :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun hf ↦ fun i ↦ hf.restrictPreimage _, fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, ?_, congr(($heq).val)⟩
  rwa [subtype_specializes_iff] at ha

end LocalAtTarget

section LocalAtSource

variable {U : ι → Opens α} (hU : IsOpenCover U)
include hU

/-
**TopologicalSpace.IsOpenCover.isOpenMap_iff_comp** 是 Mathlib 中的一个引理，位于命名空间 `Top
ologicalSpace.IsOpenCover`。
形式化陈述：isOpenMap_iff_comp : IsOpenMap f ↔ forall i, IsOpenMap (f ∘ ((↑) : U i -> 
α))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding'`：isOpenEmbedding' (U : Opens α) 
: IsOpenEmbedding (Subtype.val : U -> α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `TopologicalSpace.IsOpenCover.iUnion_inter`：iUnion_inter (hu : IsOpenCove
r u) (s : Set X) : ⋃ i, s inter u i = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
-/
lemma isOpenMap_iff_comp : IsOpenMap f ↔ ∀ i, IsOpenMap (f ∘ ((↑) : U i → α)) := by
  refine ⟨fun hf ↦ fun i ↦ hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf ↦ ?_⟩
  intro V hV
  convert! isOpen_iUnion (fun i ↦ hf i _ <| isOpen_induced hV)
  simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
    Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hU.iUnion_inter]
/-
**TopologicalSpace.IsOpenCover.generalizingMap_iff_comp** 是 Mathlib 中的一个引理，位于命名空
间 `TopologicalSpace.IsOpenCover`。
形式化陈述：generalizingMap_iff_comp : GeneralizingMap f ↔ forall i, GeneralizingMap (
f ∘ ((↑) : U i -> α))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GeneralizingMap.comp`：GeneralizingMap.comp {f : X -> Y} {g : Y -> Z} (hf
 : GeneralizingMap f) (hg : GeneralizingMap g) : GeneralizingMap (g ∘ f)
· 使用引理 `Topology.IsOpenEmbedding.generalizingMap`：Topology.IsOpenEmbedding.gener
alizingMap (hf : IsOpenEmbedding f) : GeneralizingMap f
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding'`：isOpenEmbedding' (U : Opens α) 
: IsOpenEmbedding (Subtype.val : U -> α)
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma generalizingMap_iff_comp :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap (f ∘ ((↑) : U i → α)) := by
  refine ⟨fun hf i ↦ ((U i).isOpenEmbedding'.generalizingMap).comp hf, fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i → α)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

end LocalAtSource

end TopologicalSpace.IsOpenCover


/--
Given a continuous map `f : X → Y` between topological spaces.
Suppose we have an open cover `U i` of the range of `f`, and a family of continuous maps `V i → X`
whose images are a cover of `X` that is coarser than the pullback of `U` under `f`.
To check that `f` is an embedding it suffices to check that `V i → Y` is an embedding for all `i`.
-/
-- TODO : the lemma name does not match the content (there is no hypothesis `iSup_eq_top`!)
/-
**isEmbedding_of_iSup_eq_top_of_preimage_subset_range** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：isEmbedding_of_iSup_eq_top_of_preimage_subset_range {X Y} [TopologicalSpac
e X] [TopologicalSpace Y] (f : X -> Y) (h : Continuous f) {ι : Type*} (U : ι -> 
Opens Y) (hU : Set.range f subseteq (iSup U :)) (V : ι -> Type*) [forall i, Topo
logicalSpace (V i)] (iV : forall i, V i -> X) (hiV : forall i, Continuous (iV i)
) (hV : forall i, f ⁻¹' U i subseteq Set.range (iV i)) (hV' : forall i, IsEmbedd
ing (f ∘ iV i)) : IsEmbedding f
参数：f : X -> Y；h : Continuous f；U : ι -> Opens Y；hU : Set.range f subseteq (iSup 
U :)；V : ι -> Type*；V i；iV : forall i, V i -> X；hiV : forall i, Continuous (iV i
)；hV : forall i, f ⁻¹' U i subseteq Set.range (iV i)；hV' : forall i, IsEmbedding
 (f ∘ iV i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage`：isEmbeddi
ng_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ forall i, IsEmbeddi
ng ((U i).1.restrictPreimage f)
· 使用引理 `TopologicalSpace.IsOpenCover.mk`：mk (h : iSup u = ⊤) : IsOpenCover u
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Topology.IsEmbedding.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} (s : Set β)
,   Topology.IsEmbedding f …
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.range_restrictPreimage`：range_restrictPreimage : range (t.restrictPr
eimage f) = Subtype.val ⁻¹' range f
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 37 条，此处仅展示前 30 条）
-/
theorem isEmbedding_of_iSup_eq_top_of_preimage_subset_range
    {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : Continuous f) {ι : Type*}
    (U : ι → Opens Y) (hU : Set.range f ⊆ (iSup U :))
    (V : ι → Type*) [∀ i, TopologicalSpace (V i)]
    (iV : ∀ i, V i → X) (hiV : ∀ i, Continuous (iV i)) (hV : ∀ i, f ⁻¹' U i ⊆ Set.range (iV i))
    (hV' : ∀ i, IsEmbedding (f ∘ iV i)) : IsEmbedding f := by
  wlog hU' : iSup U = ⊤
  · let f₀ : X → Set.range f := fun x ↦ ⟨f x, ⟨x, rfl⟩⟩
    suffices IsEmbedding f₀ from IsEmbedding.subtypeVal.comp this
    have hU'' : (⨆ i, (U i).comap ⟨Subtype.val, continuous_subtype_val⟩ :
        Opens (Set.range f)) = ⊤ := by
      rw [← top_le_iff]
      simpa [Set.range_subset_iff, SetLike.le_def] using hU
    refine this _ ?_ _ ?_ V iV hiV ?_ ?_ hU''
    · fun_prop
    · rw [hU'']; simp
    · exact hV
    · exact fun i ↦ IsEmbedding.of_comp (by fun_prop) continuous_subtype_val (hV' i)
  rw [(IsOpenCover.mk hU').isEmbedding_iff_restrictPreimage h]
  intro i
  let f' := (Subtype.val ∘ (f ⁻¹' U i).restrictPreimage (iV i))
  have : IsEmbedding f' :=
    IsEmbedding.subtypeVal.comp ((IsEmbedding.of_comp (hiV i) h (hV' _)).restrictPreimage _)
  have hf' : Set.range f' = f ⁻¹' U i := by
    simpa [f', Set.range_comp, Set.range_restrictPreimage] using hV i
  let e := this.toHomeomorph.trans (Homeomorph.setCongr hf')
  refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
  convert! ((hV' i).comp IsEmbedding.subtypeVal).comp e.symm.isEmbedding
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp
  rfl
