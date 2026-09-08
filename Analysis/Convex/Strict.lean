/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Order.Basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/

@[expose] public section


open Set

open Convex Pointwise

variable {𝕜 𝕝 E F β : Type*}

open Function Set

open Convex

section OrderedSemiring

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
/-
**StrictConvex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Topolo
gicalSpace E] [AddCommMonoid E] [SMul 𝕜 E] (s : Set E) : Prop
参数：𝕜 : Type*；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is strictly convex if the open segment between any two distinct points lie
s is in its
interior. This basically means "convex and not flat on the boundary".
-/
def StrictConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E]
    [AddCommMonoid E] [SMul 𝕜 E] (s : Set E) : Prop :=
  s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior s

variable [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E)

variable {s}
variable {x y : E} {a b : 𝕜}

/-
**strictConvex_iff_openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_iff_openSegment_subset : StrictConvex 𝕜 s ↔ s.Pairwise fun x 
y => openSegment 𝕜 x y subseteq interior s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `openSegment_subset_iff`：openSegment_subset_iff : openSegment 𝕜 x y subse
teq s ↔ forall a b : 𝕜, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s
-/
theorem strictConvex_iff_openSegment_subset :
    StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y ⊆ interior s :=
  forall₅_congr fun _ _ _ _ _ => (openSegment_subset_iff 𝕜).symm
/-
**StrictConvex.openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.openSegment_subset (hs : StrictConvex 𝕜 s) (hx : x in s) (hy 
: y in s) (h : x != y) : openSegment 𝕜 x y subseteq interior s
参数：hs : StrictConvex 𝕜 s；hx : x in s；hy : y in s；h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `strictConvex_iff_openSegment_subset`：strictConvex_iff_openSegment_subset
 : StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y subseteq interior 
s
-/
theorem StrictConvex.openSegment_subset (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
    (h : x ≠ y) : openSegment 𝕜 x y ⊆ interior s :=
  strictConvex_iff_openSegment_subset.1 hs hx hy h
/-
**strictConvex_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_empty : StrictConvex 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
theorem strictConvex_empty : StrictConvex 𝕜 (∅ : Set E) :=
  pairwise_empty _
/-
**strictConvex_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_univ : StrictConvex 𝕜 (univ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem strictConvex_univ : StrictConvex 𝕜 (univ : Set E) := by
  intro x _ y _ _ a b _ _ _
  rw [interior_univ]
  exact mem_univ _

protected nonrec theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
  hs.eq hx hy fun H => h <| H ha hb hab
/-
**StrictConvex.inter** 是 Mathlib 中的一个定理，位于命名空间 `StrictConvex`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMonoid E] [inst_4 : SMul 𝕜 
E] {s t : Set E},   StrictConvex 𝕜 s → StrictConvex 𝕜 t → StrictConvex 𝕜 (s ∩ t)
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s ∩ t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩
/-
**Directed.strictConvex_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.strictConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hdir : Directed
 (· subseteq ·) s) (hs : forall ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 
(⋃ i, s i)
参数：hdir : Directed (· subseteq ·) s；hs : forall ⦃i : ι⦄, StrictConvex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem Directed.strictConvex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hs : ∀ ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_iUnion] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_iUnion s k) (hs (hik hx) (hjk hy) hxy ha hb hab)
/-
**DirectedOn.strictConvex_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.strictConvex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· sub
seteq ·) S) (hS : forall s in S, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀ S)
参数：Set E；hdir : DirectedOn (· subseteq ·) S；hS : forall s in S, StrictConvex 𝕜 s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Directed.strictConvex_iUnion`：Directed.strictConvex_iUnion {ι : Sort*} {
s : ι -> Set E} (hdir : Directed (· subseteq ·) s) (hs : forall ⦃i : ι⦄, StrictC
onvex 𝕜 (s i)) : S…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem DirectedOn.strictConvex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) S)
    (hS : ∀ s ∈ S, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).strictConvex_iUnion fun s => hS _ s.2

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-
**StrictConvex.convex** 是 Mathlib 中的一个定理，位于命名空间 `StrictConvex`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMonoid E] [inst_4 : _root_.
Module 𝕜 E] {s : Set E}, StrictConvex 𝕜 s → Convex 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_pairwise_pos`：convex_iff_pairwise_pos : Convex 𝕜 s ↔ s.Pairwi
se fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in 
s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
protected theorem StrictConvex.convex (hs : StrictConvex 𝕜 s) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.2 fun _ hx _ hy hxy _ _ ha hb hab =>
    interior_subset <| hs hx hy hxy ha hb hab

/-- An open convex set is strictly convex. -/
/-
**Convex.strictConvex_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMonoid E] [inst_4 : _root_.
Module 𝕜 E] {s : Set E}, IsOpen s → Convex 𝕜 s → StrictConvex 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s

--- 原说明 ---
An open convex set is strictly convex.
-/
protected theorem Convex.strictConvex_of_isOpen (h : IsOpen s) (hs : Convex 𝕜 s) :
    StrictConvex 𝕜 s :=
  fun _ hx _ hy _ _ _ ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab
/-
**IsOpen.strictConvex_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.strictConvex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s
参数：h : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.convex`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜]
 [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMono
id E] [in…
· 使用定理 `Convex.strictConvex_of_isOpen`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : A
ddCommMonoid E] [in…
-/
theorem IsOpen.strictConvex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, Convex.strictConvex_of_isOpen h⟩
/-
**strictConvex_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E)
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
theorem strictConvex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E) :=
  pairwise_singleton _ _
/-
**Set.Subsingleton.strictConvex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.strictConvex (hs : s.Subsingleton) : StrictConvex 𝕜 s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem Set.Subsingleton.strictConvex (hs : s.Subsingleton) : StrictConvex 𝕜 s :=
  hs.pairwise _
/-
**StrictConvex.linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.linear_image [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F] [LinearMa
p.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕝] F) (hf : IsOpenM
ap f) : StrictConvex 𝕜 (f '' s)
参数：hs : StrictConvex 𝕜 s；f : E ->ₗ[𝕝] F；hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem StrictConvex.linear_image [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
    [LinearMap.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕝] F) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, ?_⟩
  rw [map_add, f.map_smul_of_tower a, f.map_smul_of_tower b]
/-
**StrictConvex.is_linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E -> F} (h : IsL
inearMap 𝕜 f) (hf : IsOpenMap f) : StrictConvex 𝕜 (f '' s)
参数：hs : StrictConvex 𝕜 s；h : IsLinearMap 𝕜 f；hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.linear_image`：StrictConvex.linear_image [Semiring 𝕝] [Modul
e 𝕝 E] [Module 𝕝 F] [LinearMap.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (
f : E ->ₗ[𝕝] F)…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E → F} (h : IsLinearMap 𝕜 f)
    (hf : IsOpenMap f) : StrictConvex 𝕜 (f '' s) :=
  hs.linear_image (h.mk' f) hf
/-
**StrictConvex.linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E ->
ₗ[𝕜] F) (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.preimage f
)
参数：hs : StrictConvex 𝕜 s；f : E ->ₗ[𝕜] F；hf : Continuous f；hfinj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕜] F)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.preimage f) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab
/-
**StrictConvex.is_linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E
 -> F} (h : IsLinearMap 𝕜 f) (hf : Continuous f) (hfinj : Injective f) : StrictC
onvex 𝕜 (s.preimage f)
参数：hs : StrictConvex 𝕜 s；h : IsLinearMap 𝕜 f；hf : Continuous f；hfinj : Injective
 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.linear_preimage`：StrictConvex.linear_preimage {s : Set F} (
hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F) (hf : Continuous f) (hfinj : Injective f
) : StrictConvex 𝕜…
-/
theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E → F}
    (h : IsLinearMap 𝕜 f) (hf : Continuous f) (hfinj : Injective f) :
    StrictConvex 𝕜 (s.preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace β] [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [OrderTopology β] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]

/-
**Set.OrdConnected.strictConvex** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : AddCommMonoid β] [inst_4 : LinearO
rder β] [IsOrderedCancelAddMonoid β] [OrderTopology β]   [inst_7 : _root_.Module
 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set β}, s.OrdConnected → StrictConvex 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strictConvex_iff_openSegment_subset`：strictConvex_iff_openSegment_subset
 : StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y subseteq interior 
s
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `openSegment_subset_Ioo`：openSegment_subset_Ioo (h : x < y) : openSegment
 𝕜 x y subseteq Ioo x y
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_symm`：openSegment_symm (x y : E) : openSegment 𝕜 x y = openS
egment 𝕜 y x
-/
protected theorem Set.OrdConnected.strictConvex {s : Set β} (hs : OrdConnected s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 fun x hx y hy hxy => ?_
  rcases hxy.lt_or_gt with hlt | hlt <;> [skip; rw [openSegment_symm]] <;>
    exact
      (openSegment_subset_Ioo hlt).trans
        (isOpen_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)
/-
**strictConvex_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Iic (r : β) : StrictConvex 𝕜 (Iic r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
theorem strictConvex_Iic (r : β) : StrictConvex 𝕜 (Iic r) :=
  ordConnected_Iic.strictConvex
/-
**strictConvex_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Ici (r : β) : StrictConvex 𝕜 (Ici r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
-/
theorem strictConvex_Ici (r : β) : StrictConvex 𝕜 (Ici r) :=
  ordConnected_Ici.strictConvex
/-
**strictConvex_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Iio (r : β) : StrictConvex 𝕜 (Iio r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
theorem strictConvex_Iio (r : β) : StrictConvex 𝕜 (Iio r) :=
  ordConnected_Iio.strictConvex
/-
**strictConvex_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
-/
theorem strictConvex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r) :=
  ordConnected_Ioi.strictConvex
/-
**strictConvex_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
-/
theorem strictConvex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s) :=
  ordConnected_Icc.strictConvex
/-
**strictConvex_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
-/
theorem strictConvex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s) :=
  ordConnected_Ioo.strictConvex
/-
**strictConvex_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
-/
theorem strictConvex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s) :=
  ordConnected_Ico.strictConvex
/-
**strictConvex_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
· 使用定理 `Set.ordConnected_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (S
et.Ioc b a).OrdConnected
-/
theorem strictConvex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s) :=
  ordConnected_Ioc.strictConvex
/-
**strictConvex_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_uIcc (r s : β) : StrictConvex 𝕜 (uIcc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvex_Icc`：strictConvex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s)
-/
theorem strictConvex_uIcc (r s : β) : StrictConvex 𝕜 (uIcc r s) :=
  strictConvex_Icc _ _
/-
**strictConvex_uIoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_uIoc (r s : β) : StrictConvex 𝕜 (uIoc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvex_Ioc`：strictConvex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s)
-/
theorem strictConvex_uIoc (r s : β) : StrictConvex 𝕜 (uIoc r s) :=
  strictConvex_Ioc _ _

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [ContinuousAdd E] [Module 𝕜 E] {s : Set E}

/-- The translation of a strictly convex set is also strictly convex. -/
/-
**StrictConvex.preimage_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) : StrictCo
nvex 𝕜 ((fun x => z + x) ⁻¹' s)
参数：hs : StrictConvex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `continuous_const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => m + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂

--- 原说明 ---
The translation of a strictly convex set is also strictly convex.
-/
theorem StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage (continuous_const_add _) ?_
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← _root_.add_smul, hab, one_smul] at h

/-- The translation of a strictly convex set is also strictly convex. -/
/-
**StrictConvex.preimage_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) : StrictCon
vex 𝕜 ((fun x => x + z) ⁻¹' s)
参数：hs : StrictConvex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `StrictConvex.preimage_add_right`：StrictConvex.preimage_add_right (hs : S
trictConvex 𝕜 s) (z : E) : StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s)

--- 原说明 ---
The translation of a strictly convex set is also strictly convex.
-/
theorem StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.preimage_add_right z

end AddCancelCommMonoid

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

section continuous_add

variable [ContinuousAdd E] {s t : Set E}

/-
**StrictConvex.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictC
onvex 𝕜 (s + t)
参数：hs : StrictConvex 𝕜 s；ht : StrictConvex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用定理 `isOpenMap_add_left`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 :
 AddGroup G] [SeparatelyContinuousAdd G] (a : G),   IsOpenMap fun x => a + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `subset_interior_add_left`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : AddGroup α] [ContinuousConstVAdd αᵃᵒᵖ α] {s t : Set α},   interior s + t 
⊆ interior (s …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd_op`：∀ {M : Type u_3} [inst : T
opologicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConst
VAdd Mᵃᵒᵖ M
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `StrictConvex.convex`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜]
 [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMono
id E] [in…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s + t) := by
  rintro _ ⟨v, hv, w, hw, rfl⟩ _ ⟨x, hx, y, hy, rfl⟩ h a b ha hb hab
  rw [smul_add, smul_add, add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) Subset.rfl) ?_
    rw [Convex.combo_self hab, singleton_add]
    exact
      (isOpenMap_add_left _).image_interior_subset _
        (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
  exact
    subset_interior_add_left
      (add_mem_add (hs hv hx hvx ha hb hab) <| ht.convex hw hy ha.le hb.le hab)
/-
**StrictConvex.add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z : E) : StrictConvex 𝕜 ((f
un x => z + x) '' s)
参数：hs : StrictConvex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `StrictConvex.add`：StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictC
onvex 𝕜 t) : StrictConvex 𝕜 (s + t)
· 使用定理 `strictConvex_singleton`：strictConvex_singleton (c : E) : StrictConvex 𝕜 
({c} : Set E)
-/
theorem StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) '' s) := by
  simpa only [singleton_add] using (strictConvex_singleton z).add hs
/-
**StrictConvex.add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.add_right (hs : StrictConvex 𝕜 s) (z : E) : StrictConvex 𝕜 ((
fun x => x + z) '' s)
参数：hs : StrictConvex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `StrictConvex.add_left`：StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z 
: E) : StrictConvex 𝕜 ((fun x => z + x) '' s)
-/
theorem StrictConvex.add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) '' s) := by simpa only [add_comm] using hs.add_left z

/-- The translation of a strictly convex set is also strictly convex. -/
/-
**StrictConvex.vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : StrictConvex 𝕜 (x +ᵥ s
)
参数：hs : StrictConvex 𝕜 s；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.add_left`：StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z 
: E) : StrictConvex 𝕜 ((fun x => z + x) '' s)

--- 原说明 ---
The translation of a strictly convex set is also strictly convex.
-/
theorem StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : StrictConvex 𝕜 (x +ᵥ s) :=
  hs.add_left x

end continuous_add

section ContinuousSMul

variable [Field 𝕝] [Module 𝕝 E] [ContinuousConstSMul 𝕝 E]
  [LinearMap.CompatibleSMul E E 𝕜 𝕝] {s : Set E} {x : E}

/-
**StrictConvex.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s)
参数：hs : StrictConvex 𝕜 s；c : 𝕝。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.Subsingleton.strictConvex`：Set.Subsingleton.strictConvex (hs : s.Sub
singleton) : StrictConvex 𝕜 s
· 使用引理 `Set.subsingleton_zero_smul_set`：subsingleton_zero_smul_set (s : Set β) :
 ((0 : α) • s).Subsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictConvex.linear_image`：StrictConvex.linear_image [Semiring 𝕝] [Modul
e 𝕝 E] [Module 𝕝 F] [LinearMap.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (
f : E ->ₗ[𝕝] F)…
· 使用定理 `isOpenMap_smul₀`：isOpenMap_smul₀ {c : G₀} (hc : c != 0) : IsOpenMap fun 
x : α => c • x
-/
theorem StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s) := by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).strictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)
/-
**StrictConvex.affinity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.affinity [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c
 : 𝕝) : StrictConvex 𝕜 (z +ᵥ c • s)
参数：hs : StrictConvex 𝕜 s；z : E；c : 𝕝。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.vadd`：StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : S
trictConvex 𝕜 (x +ᵥ s)
· 使用定理 `StrictConvex.smul`：StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : S
trictConvex 𝕜 (c • s)
-/
theorem StrictConvex.affinity [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝) :
    StrictConvex 𝕜 (z +ᵥ c • s) :=
  (hs.smul c).vadd z

end ContinuousSMul

end AddCommGroup

end OrderedSemiring

section CommSemiring
variable [CommSemiring 𝕜] [IsDomain 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [AddCommGroup E]
  [Module 𝕜 E] [Module.IsTorsionFree 𝕜 E] [ContinuousConstSMul 𝕜 E] {s : Set E}

/-
**StrictConvex.preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) : StrictConvex 
𝕜 ((fun z => c • z) ⁻¹' s)
参数：hs : StrictConvex 𝕜 s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `strictConvex_univ`：strictConvex_univ : StrictConvex 𝕜 (univ : Set E)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `strictConvex_empty`：strictConvex_empty : StrictConvex 𝕜 (∅ : Set E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictConvex.linear_preimage`：StrictConvex.linear_preimage {s : Set F} (
hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F) (hf : Continuous f) (hfinj : Injective f
) : StrictConvex 𝕜…
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) :
    StrictConvex 𝕜 ((fun z => c • z) ⁻¹' s) := by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strictConvex_univ
      · exact strictConvex_empty
    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ LinearMap.mk₂' LinearMap.mk₂'ₛₗ
    exact continuous_const_smul _

end CommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E} {x y : E}

/-
**StrictConvex.eq_of_openSegment_subset_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.eq_of_openSegment_subset_frontier [IsOrderedRing 𝕜] [Nontrivi
al 𝕜] [DenselyOrdered 𝕜] (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s) (h 
: openSegment 𝕜 x y subseteq frontier s) : x = y
参数：hs : StrictConvex 𝕜 s；hx : x in s；hy : y in s；h : openSegment 𝕜 x y subseteq 
frontier s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenselyOrdered.dense`：∀ {α : Type u_5} {inst : LT α} [self : DenselyOrde
red α] (a₁ a₂ : α), a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem StrictConvex.eq_of_openSegment_subset_frontier
    [IsOrderedRing 𝕜] [Nontrivial 𝕜] [DenselyOrdered 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (h : openSegment 𝕜 x y ⊆ frontier s) :
    x = y := by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel _ _)
/-
**StrictConvex.add_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.add_smul_mem [AddRightStrictMono 𝕜] (hs : StrictConvex 𝕜 s) (
hx : x in s) (hxy : x + y in s) (hy : y != 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1
) : x + t • y in interior s
参数：hs : StrictConvex 𝕜 s；hx : x in s；hxy : x + y in s；hy : y != 0；ht₀ : 0 < t；ht
₁ : t < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
-/
theorem StrictConvex.add_smul_mem [AddRightStrictMono 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hxy : x + y ∈ s)
    (hy : y ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • y ∈ interior s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> simp
  rw [h]
  exact hs hx hxy (fun h => hy <| add_left_cancel (a := x) (by rw [← h, add_zero]))
    (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel 1 t)
/-
**StrictConvex.smul_mem_of_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.smul_mem_of_zero_mem [AddRightStrictMono 𝕜] (hs : StrictConve
x 𝕜 s) (zero_mem : (0 : E) in s) (hx : x in s) (hx₀ : x != 0) {t : 𝕜} (ht₀ : 0 <
 t) (ht₁ : t < 1) : t • x in interior s
参数：hs : StrictConvex 𝕜 s；zero_mem : (0 : E) in s；hx : x in s；hx₀ : x != 0；ht₀ : 
0 < t；ht₁ : t < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `StrictConvex.add_smul_mem`：StrictConvex.add_smul_mem [AddRightStrictMono
 𝕜] (hs : StrictConvex 𝕜 s) (hx : x in s) (hxy : x + y in s) (hy : y != 0) {t : 
𝕜} (ht₀ : 0 < t…
-/
theorem StrictConvex.smul_mem_of_zero_mem [AddRightStrictMono 𝕜]
    (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : t • x ∈ interior s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁
/-
**StrictConvex.add_smul_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.add_smul_sub_mem [AddRightMono 𝕜] (h : StrictConvex 𝕜 s) (hx 
: x in s) (hy : y in s) (hxy : x != y) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x +
 t • (y - x) in interior s
参数：h : StrictConvex 𝕜 s；hx : x in s；hy : y in s；hxy : x != y；ht₀ : 0 < t；ht₁ : t
 < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.openSegment_subset`：StrictConvex.openSegment_subset (hs : S
trictConvex 𝕜 s) (hx : x in s) (hy : y in s) (h : x != y) : openSegment 𝕜 x y su
bseteq interior s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `openSegment_eq_image'`：openSegment_eq_image' (x y : E) : openSegment 𝕜 x
 y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem StrictConvex.add_smul_sub_mem [AddRightMono 𝕜]
    (h : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) ∈ interior s := by
  apply h.openSegment_subset hx hy hxy
  rw [openSegment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

/-- The preimage of a strictly convex set under an affine map is strictly convex. -/
/-
**StrictConvex.affine_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E ->
ᵃ[𝕜] F} (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s)
参数：hs : StrictConvex 𝕜 s；hf : Continuous f；hfinj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Convex.combo_affine_apply`：Convex.combo_affine_apply {x y : E} {a b : 𝕜}
 {f : E ->ᵃ[𝕜] F} (h : a + b = 1) : f (a • x + b • y) = a • f x + b • f y
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
The preimage of a strictly convex set under an affine map is strictly convex.
-/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F}
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

/-- The image of a strictly convex set under an affine map is strictly convex. -/
/-
**StrictConvex.affine_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F} (hf : I
sOpenMap f) : StrictConvex 𝕜 (f '' s)
参数：hs : StrictConvex 𝕜 s；hf : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Convex.combo_affine_apply`：Convex.combo_affine_apply {x y : E} {a b : 𝕜}
 {f : E ->ᵃ[𝕜] F} (h : a + b = 1) : f (a • x + b • y) = a • f x + b • f y

--- 原说明 ---
The image of a strictly convex set under an affine map is strictly convex.
-/
theorem StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩

variable [IsTopologicalAddGroup E]
/-
**StrictConvex.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 (-s)
参数：hs : StrictConvex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.is_linear_preimage`：StrictConvex.is_linear_preimage {s : Se
t F} (hs : StrictConvex 𝕜 s) {f : E -> F} (h : IsLinearMap 𝕜 f) (hf : Continuous
 f) (hfinj : Injectiv…
· 使用定理 `IsLinearMap.isLinearMap_neg`：isLinearMap_neg : IsLinearMap R fun z : M =
> -z
· 使用定理 `Continuous.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X → 
G}, …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
theorem StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg continuous_id.neg neg_injective
/-
**StrictConvex.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictC
onvex 𝕜 (s - t)
参数：hs : StrictConvex 𝕜 s；ht : StrictConvex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.add`：StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictC
onvex 𝕜 t) : StrictConvex 𝕜 (s + t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `StrictConvex.neg`：StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConve
x 𝕜 (-s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s - t) :=
  (sub_eq_add_neg s t).symm ▸ hs.add ht.neg

end AddCommGroup

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/-- Alternative definition of set strict convexity, using division. -/
/-
**strictConvex_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_iff_div : StrictConvex 𝕜 s ↔ s.Pairwise fun x y => forall ⦃a 
b : 𝕜⦄, 0 < a -> 0 < b -> (a / (a + b)) • x + (b / (a + b)) • y in interior s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Alternative definition of set strict convexity, using division.
-/
theorem strictConvex_iff_div :
    StrictConvex 𝕜 s ↔
      s.Pairwise fun x y =>
        ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → (a / (a + b)) • x + (b / (a + b)) • y ∈ interior s :=
  ⟨fun h x hx y hy hxy a b ha hb ↦ h hx hy hxy (by positivity) (by positivity) (by field),
    fun h x hx y hy hxy a b ha hb hab ↦ by
    convert! h hx hy hxy ha hb <;> rw [hab, div_one]⟩
/-
**StrictConvex.mem_smul_of_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 :
 E) in s) (hx : x in s) (hx₀ : x != 0) {t : 𝕜} (ht : 1 < t) : x in t • interior 
s
参数：hs : StrictConvex 𝕜 s；zero_mem : (0 : E) in s；hx : x in s；hx₀ : x != 0；ht : 1
 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `StrictConvex.smul_mem_of_zero_mem`：StrictConvex.smul_mem_of_zero_mem [Ad
dRightStrictMono 𝕜] (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) in s) (hx : x in
 s) (hx₀ : x != 0) {t :…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht : 1 < t) : x ∈ t • interior s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (by positivity)]
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (by positivity) (inv_lt_one_of_one_lt₀ ht)

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `Convex` and `Set.OrdConnected`.
-/


section

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {s : Set 𝕜}

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
/-
**strictConvex_iff_convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Convex 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.convex`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜]
 [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMono
id E] [in…
· 使用定理 `Set.OrdConnected.strictConvex`：∀ {𝕜 : Type u_1} {β : Type u_5} [inst : S
emiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace β]   [inst_3 : A
ddCommMonoid β] [in…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected

--- 原说明 ---
A set in a linear ordered field is strictly convex if and only if it is convex.
-/
theorem strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, fun hs => hs.ordConnected.strictConvex⟩
/-
**strictConvex_iff_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvex_iff_ordConnected : StrictConvex 𝕜 s ↔ s.OrdConnected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `strictConvex_iff_convex`：strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Co
nvex 𝕜 s
· 使用定理 `convex_iff_ordConnected`：convex_iff_ordConnected [Field 𝕜] [LinearOrder 
𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} : Convex 𝕜 s ↔ s.OrdConnected
-/
theorem strictConvex_iff_ordConnected : StrictConvex 𝕜 s ↔ s.OrdConnected :=
  strictConvex_iff_convex.trans convex_iff_ordConnected

alias ⟨StrictConvex.ordConnected, _⟩ := strictConvex_iff_ordConnected

end

