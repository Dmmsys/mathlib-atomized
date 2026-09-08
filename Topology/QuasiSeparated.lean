/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.NoetherianSpace

/-!
# Quasi-separated spaces

A topological space is quasi-separated if the intersections of any pairs of compact open subsets
are still compact.
Notable examples include spectral spaces, Noetherian spaces, and Hausdorff spaces.

A non-example is the interval `[0, 1]` with doubled origin: the two copies of `[0, 1]` are compact
open subsets, but their intersection `(0, 1]` is not.

## Main results

- `IsQuasiSeparated`: A subset `s` of a topological space is quasi-separated if the intersections
  of any pairs of compact open subsets of `s` are still compact.
- `QuasiSeparatedSpace`: A topological space is quasi-separated if the intersections of any pairs
  of compact open subsets are still compact.
- `QuasiSeparatedSpace.of_isOpenEmbedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/

@[expose] public section

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

/-- A subset `s` of a topological space is quasi-separated if the intersections of any pairs of
compact open subsets of `s` are still compact.

Note that this is equivalent to `s` being a `QuasiSeparatedSpace` only when `s` is open. -/
/-
**IsQuasiSeparated** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsQuasiSeparated (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `s` of a topological space is quasi-separated if the intersections of a
ny pairs of
compact open subsets of `s` are still compact.

Note that this is equivalent to `s` being a `QuasiSeparatedSpace` only when `s` 
is open.
-/
def IsQuasiSeparated (s : Set α) : Prop :=
  ∀ U V : Set α, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)

/-- A topological space is quasi-separated if the intersections of any pairs of compact open
subsets are still compact. -/
@[mk_iff]
/-
**QuasiSeparatedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is quasi-separated if the intersections of any pairs of comp
act open
subsets are still compact.
-/
class QuasiSeparatedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of two open compact subsets of a quasi-separated space is compact. -/
  inter_isCompact :
    ∀ U V : Set α, IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V)
/-
**isQuasiSeparated_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuasiSeparated_univ_iff {α : Type*} [TopologicalSpace α] : IsQuasiSepara
ted (Set.univ : Set α) ↔ QuasiSeparatedSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasiSeparatedSpace_iff`：∀ (α : Type u_3) [inst : TopologicalSpace α],  
 QuasiSeparatedSpace α ↔ ∀ (U V : Set α), IsOpen U → IsCompact U → IsOpen V → Is
Compact V → I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isQuasiSeparated_univ_iff {α : Type*} [TopologicalSpace α] :
    IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α := by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]
/-
**isQuasiSeparated_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuasiSeparated_univ {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpac
e α] : IsQuasiSeparated (Set.univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isQuasiSeparated_univ_iff`：isQuasiSeparated_univ_iff {α : Type*} [Topolo
gicalSpace α] : IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α
-/
theorem isQuasiSeparated_univ {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpace α] :
    IsQuasiSeparated (Set.univ : Set α) :=
  isQuasiSeparated_univ_iff.mpr inferInstance
/-
**IsQuasiSeparated.image_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsQuasiSeparated.image_of_isEmbedding {s : Set α} (H : IsQuasiSeparated s)
 (h : IsEmbedding f) : IsQuasiSeparated (f '' s)
参数：H : IsQuasiSeparated s；h : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Set.InjOn.mem_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} 
{f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → (f x ∈ f '' s₁ ↔ x ∈ s₁)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `trivial`：True
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
-/
theorem IsQuasiSeparated.image_of_isEmbedding {s : Set α} (H : IsQuasiSeparated s)
    (h : IsEmbedding f) : IsQuasiSeparated (f '' s) := by
  intro U V hU hU' hU'' hV hV' hV''
  convert!
    (H (f ⁻¹' U) (f ⁻¹' V) ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image
      h.continuous
  · symm
    rw [← Set.preimage_inter, Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert! hU''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert! hV''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)
/-
**IsQuasiSeparated.of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsQuasiSeparated.of_subset {s t : Set α} (ht : IsQuasiSeparated t) (h : s 
subseteq t) : IsQuasiSeparated s
参数：ht : IsQuasiSeparated t；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsQuasiSeparated.of_subset {s t : Set α} (ht : IsQuasiSeparated t) (h : s ⊆ t) :
    IsQuasiSeparated s := by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''
/-
**Topology.IsOpenEmbedding.isQuasiSeparated_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.isQuasiSeparated_iff (h : IsOpenEmbedding f) {s :
 Set α} : IsQuasiSeparated s ↔ IsQuasiSeparated (f '' s)
参数：h : IsOpenEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuasiSeparated.image_of_isEmbedding`：IsQuasiSeparated.image_of_isEmbed
ding {s : Set α} (H : IsQuasiSeparated s) (h : IsEmbedding f) : IsQuasiSeparated
 (f '' s)
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
-/
theorem Topology.IsOpenEmbedding.isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} :
    IsQuasiSeparated s ↔ IsQuasiSeparated (f '' s) := by
  refine ⟨fun hs => hs.image_of_isEmbedding h.isEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.isEmbedding.isCompact_iff, Set.image_inter h.injective]
  exact
    H (f '' U) (f '' V) (image_mono hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (image_mono hV) (h.isOpenMap _ hV') (hV''.image h.continuous)
/-
**Topology.IsOpenEmbedding.quasiSeparatedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.quasiSeparatedSpace [QuasiSeparatedSpace β] (h : 
IsOpenEmbedding f) : QuasiSeparatedSpace α
参数：h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isQuasiSeparated_univ_iff`：isQuasiSeparated_univ_iff {α : Type*} [Topolo
gicalSpace α] : IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α
· 使用定理 `Topology.IsOpenEmbedding.isQuasiSeparated_iff`：Topology.IsOpenEmbedding.
isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} : IsQuasiSeparated s ↔ 
IsQuasiSeparated (f '' s)
· 使用定理 `IsQuasiSeparated.of_subset`：IsQuasiSeparated.of_subset {s t : Set α} (ht
 : IsQuasiSeparated t) (h : s subseteq t) : IsQuasiSeparated s
· 使用定理 `isQuasiSeparated_univ`：isQuasiSeparated_univ {α : Type*} [TopologicalSpa
ce α] [QuasiSeparatedSpace α] : IsQuasiSeparated (Set.univ : Set α)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma Topology.IsOpenEmbedding.quasiSeparatedSpace [QuasiSeparatedSpace β] (h : IsOpenEmbedding f) :
    QuasiSeparatedSpace α := by
  rw [← isQuasiSeparated_univ_iff, h.isQuasiSeparated_iff]
  exact isQuasiSeparated_univ.of_subset <| Set.subset_univ _
/-
**isQuasiSeparated_iff_quasiSeparatedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuasiSeparated_iff_quasiSeparatedSpace (s : Set α) (hs : IsOpen s) : IsQ
uasiSeparated s ↔ QuasiSeparatedSpace s
参数：s : Set α；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isQuasiSeparated_univ_iff`：isQuasiSeparated_univ_iff {α : Type*} [Topolo
gicalSpace α] : IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsOpenEmbedding.isQuasiSeparated_iff`：Topology.IsOpenEmbedding.
isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} : IsQuasiSeparated s ↔ 
IsQuasiSeparated (f '' s)
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
-/
theorem isQuasiSeparated_iff_quasiSeparatedSpace (s : Set α) (hs : IsOpen s) :
    IsQuasiSeparated s ↔ QuasiSeparatedSpace s := by
  rw [← isQuasiSeparated_univ_iff]
  convert! (hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff (s := Set.univ)).symm
  simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T2Space.to_quasiSeparatedSpace [T2Space α] : QuasiSeparatedSpace α :=
  ⟨fun _ _ _ hU' _ hV' => hU'.inter hV'⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NoetherianSpace.to_quasiSeparatedSpace [NoetherianSpace α] :
    QuasiSeparatedSpace α :=
  ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩
/-
**QuasiSeparatedSpace.of_isTopologicalBasis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSeparatedSpace.of_isTopologicalBasis {ι : Type*} {b : ι -> Set α} (ba
sis : IsTopologicalBasis (range b)) (isCompact_inter : forall i j, IsCompact (b 
i inter b j)) : QuasiSeparatedSpace α where inter_isCompact U V hUopen hUcomp hV
open hVcomp
参数：basis : IsTopologicalBasis (range b)；isCompact_inter : forall i j, IsCompact 
(b i inter b j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis`：isCompact_ope
n_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι -> Set X) (hb : IsTopologica
lBasis (Set.range b)) (hb' : forall i, IsCompac…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.iUnion₂_inter_iUnion₂`：iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι
₁ -> Sort*} {k₂ : κ₁ -> Sort*} (f : forall i₁, ι₂ i₁ -> Set α) (g : forall j₁, k
₂ j₁ -> Set α) …
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma QuasiSeparatedSpace.of_isTopologicalBasis {ι : Type*} {b : ι → Set α}
    (basis : IsTopologicalBasis (range b)) (isCompact_inter : ∀ i j, IsCompact (b i ∩ b j)) :
    QuasiSeparatedSpace α where
  inter_isCompact U V hUopen hUcomp hVopen hVcomp := by
    have aux := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b basis fun i ↦ by
      simpa using isCompact_inter i i
    obtain ⟨s, hs, rfl⟩ := (aux _).1 ⟨hUcomp, hUopen⟩
    obtain ⟨t, ht, rfl⟩ := (aux _).1 ⟨hVcomp, hVopen⟩
    rw [iUnion₂_inter_iUnion₂]
    exact hs.isCompact_biUnion fun i hi ↦ ht.isCompact_biUnion fun j hj ↦ isCompact_inter ..

section QuasiSeparatedSpace
variable [QuasiSeparatedSpace α] {U V : Set α}

/-
**IsQuasiSeparated.of_quasiSeparatedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsQuasiSeparated.of_quasiSeparatedSpace (s : Set α) : IsQuasiSeparated s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuasiSeparated.of_subset`：IsQuasiSeparated.of_subset {s t : Set α} (ht
 : IsQuasiSeparated t) (h : s subseteq t) : IsQuasiSeparated s
· 使用定理 `isQuasiSeparated_univ`：isQuasiSeparated_univ {α : Type*} [TopologicalSpa
ce α] [QuasiSeparatedSpace α] : IsQuasiSeparated (Set.univ : Set α)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma IsQuasiSeparated.of_quasiSeparatedSpace (s : Set α) : IsQuasiSeparated s :=
  isQuasiSeparated_univ.of_subset (Set.subset_univ _)
/-
**QuasiSeparatedSpace.of_isOpenEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSeparatedSpace.of_isOpenEmbedding {f : β -> α} (h : IsOpenEmbedding f
) : QuasiSeparatedSpace β
参数：h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isQuasiSeparated_univ_iff`：isQuasiSeparated_univ_iff {α : Type*} [Topolo
gicalSpace α] : IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsOpenEmbedding.isQuasiSeparated_iff`：Topology.IsOpenEmbedding.
isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} : IsQuasiSeparated s ↔ 
IsQuasiSeparated (f '' s)
· 使用引理 `IsQuasiSeparated.of_quasiSeparatedSpace`：IsQuasiSeparated.of_quasiSepara
tedSpace (s : Set α) : IsQuasiSeparated s
-/
lemma QuasiSeparatedSpace.of_isOpenEmbedding {f : β → α} (h : IsOpenEmbedding f) :
    QuasiSeparatedSpace β :=
  isQuasiSeparated_univ_iff.mp (h.isQuasiSeparated_iff.mpr <| .of_quasiSeparatedSpace _)
/-
**IsCompact.inter_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.inter_of_isOpen (hUcomp : IsCompact U) (hVcomp : IsCompact V) (h
Uopen : IsOpen U) (hVopen : IsOpen V) : IsCompact (U inter V)
参数：hUcomp : IsCompact U；hVcomp : IsCompact V；hUopen : IsOpen U；hVopen : IsOpen V
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiSeparatedSpace.inter_isCompact`：∀ {α : Type u_3} {inst : Topologica
lSpace α} [self : QuasiSeparatedSpace α] (U V : Set α),   IsOpen U → IsCompact U
 → IsOpen V → IsCompact V…
-/
lemma IsCompact.inter_of_isOpen (hUcomp : IsCompact U) (hVcomp : IsCompact V) (hUopen : IsOpen U)
    (hVopen : IsOpen V) : IsCompact (U ∩ V) :=
  QuasiSeparatedSpace.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp
/-
**QuasiSeparatedSpace.isCompact_sInter_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSeparatedSpace.isCompact_sInter_of_nonempty {s : Set (Set α)} (hf : s
.Finite) (hne : s.Nonempty) (ho : forall t in s, IsOpen t ∨ IsClosed t) (hc : fo
rall t in s, IsCompact t) : IsCompact (⋂₀ s)
参数：Set α；hf : s.Finite；hne : s.Nonempty；ho : forall t in s, IsOpen t ∨ IsClosed 
t；hc : forall t in s, IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.sInter_union`：sInter_union (S T : Set (Set α)) : ⋂₀ (S union T) = ⋂₀
 S inter ⋂₀ T
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
-/
lemma QuasiSeparatedSpace.isCompact_sInter_of_nonempty {s : Set (Set α)} (hf : s.Finite)
    (hne : s.Nonempty) (ho : ∀ t ∈ s, IsOpen t ∨ IsClosed t) (hc : ∀ t ∈ s, IsCompact t) :
    IsCompact (⋂₀ s) := by
  wlog h : ∀ t ∈ s, IsOpen t
  · let a := { t ∈ s | IsOpen t }
    let b := { t ∈ s | IsClosed t }
    have heq : s = a ∪ b := subset_antisymm (by grind) (by grind)
    rw [heq, Set.sInter_union]
    simp only [not_forall] at h
    obtain ⟨t, ht, hno⟩ := h
    obtain (ha | ha) := a.eq_empty_or_nonempty
    · simp only [ha, Set.sInter_empty, Set.univ_inter]
      exact IsCompact.of_isClosed_subset (hc _ ht) (isClosed_sInter (by grind)) (by grind)
    · apply IsCompact.inter_right
      · apply this (hf.subset (by grind)) ha <;> grind
      · exact isClosed_sInter (by grind)
  revert hne
  induction s, hf using Set.Finite.induction_on with
  | empty => simp
  | insert ha hs ih =>
    rename_i s
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · grind
    · grind [IsCompact.inter_of_isOpen, hs.isOpen_sInter, Set.sInter_insert]
/-
**QuasiSeparatedSpace.isCompact_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSeparatedSpace.isCompact_sInter [CompactSpace α] {s : Set (Set α)} (h
f : s.Finite) (ho : forall t in s, IsOpen t ∨ IsClosed t) (hc : forall t in s, I
sCompact t) : IsCompact (⋂₀ s)
参数：Set α；hf : s.Finite；ho : forall t in s, IsOpen t ∨ IsClosed t；hc : forall t i
n s, IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `QuasiSeparatedSpace.isCompact_sInter_of_nonempty`：QuasiSeparatedSpace.is
Compact_sInter_of_nonempty {s : Set (Set α)} (hf : s.Finite) (hne : s.Nonempty) 
(ho : forall t in s, IsOpen t ∨ IsClos…
-/
lemma QuasiSeparatedSpace.isCompact_sInter [CompactSpace α] {s : Set (Set α)} (hf : s.Finite)
    (ho : ∀ t ∈ s, IsOpen t ∨ IsClosed t) (hc : ∀ t ∈ s, IsCompact t) :
    IsCompact (⋂₀ s) := by
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp [CompactSpace.isCompact_univ]
  · exact QuasiSeparatedSpace.isCompact_sInter_of_nonempty hf hne ho hc

end QuasiSeparatedSpace

/-
**quasiSeparatedSpace_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasiSeparatedSpace_congr (e : α ≃ₜ β) : QuasiSeparatedSpace α ↔ QuasiSepa
ratedSpace β where mp _
参数：e : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `QuasiSeparatedSpace.of_isOpenEmbedding`：QuasiSeparatedSpace.of_isOpenEmb
edding {f : β -> α} (h : IsOpenEmbedding f) : QuasiSeparatedSpace β
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
lemma quasiSeparatedSpace_congr (e : α ≃ₜ β) : QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β where
  mp _ := .of_isOpenEmbedding e.symm.isOpenEmbedding
  mpr _ := .of_isOpenEmbedding e.isOpenEmbedding
