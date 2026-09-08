/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `WellFounded ((· > ·) : TopologicalSpace.Opens α → TopologicalSpace.Opens α → Prop)`
- `WellFounded ((· < ·) : TopologicalSpace.Closeds α → TopologicalSpace.Closeds α → Prop)`
- `∀ s : Set α, IsCompact s`
- `∀ s : TopologicalSpace.Opens α, IsCompact s`

The first is chosen as the definition, and the equivalence is shown in
`TopologicalSpace.noetherianSpace_TFAE`.

Many examples of Noetherian spaces come from algebraic topology. For example, the underlying space
of a Noetherian scheme (e.g., the spectrum of a Noetherian ring) is Noetherian.

## Main Results

- `TopologicalSpace.NoetherianSpace.set`: Every subspace of a Noetherian space is Noetherian.
- `TopologicalSpace.NoetherianSpace.isCompact`: Every set in a Noetherian space is a compact set.
- `TopologicalSpace.noetherianSpace_TFAE`: Describes the equivalent definitions of Noetherian
  spaces.
- `TopologicalSpace.NoetherianSpace.range`: The image of a Noetherian space under a continuous map
  is Noetherian.
- `TopologicalSpace.NoetherianSpace.iUnion`: The finite union of Noetherian spaces is Noetherian.
- `TopologicalSpace.NoetherianSpace.discrete`: A Noetherian and Hausdorff space is discrete.
- `TopologicalSpace.NoetherianSpace.exists_finset_irreducible`: Every closed subset of a Noetherian
  space is a finite union of irreducible closed subsets.
- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`: The number of irreducible
  components of a Noetherian space is finite.

-/

public section

open Topology

variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- Type class for Noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
/-
**TopologicalSpace.NoetherianSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopologicalSpace
`。
形式化陈述：NoetherianSpace : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for Noetherian spaces. It is defined to be spaces whose open sets sat
isfies ACC.
-/
abbrev NoetherianSpace : Prop := WellFoundedGT (Opens α)
/-
**TopologicalSpace.noetherianSpace_iff_opens** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace`。
形式化陈述：noetherianSpace_iff_opens : NoetherianSpace α ↔ forall s : Opens α, IsComp
act (s : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.NoetherianSpace.eq_1`：∀ (α : Type u_1) [inst : Topologi
calSpace α],   TopologicalSpace.NoetherianSpace α = WellFoundedGT (TopologicalSp
ace.Opens α)
· 使用定理 `CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact`：wellFoundedGT_iff_
isSupFiniteCompact : WellFoundedGT α ↔ IsSupFiniteCompact α
· 使用定理 `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`：isSupFinite
Compact_iff_all_elements_compact : IsSupFiniteCompact α ↔ forall k : α, IsCompac
tElement k
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `TopologicalSpace.Opens.isCompactElement_iff`：isCompactElement_iff (s : O
pens α) : IsCompactElement s ↔ IsCompact (s : Set α)
-/
theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) := by
  rw [NoetherianSpace, CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact,
    CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NoetherianSpace.compactSpace [h : NoetherianSpace α] : CompactSpace α :=
  ⟨(noetherianSpace_iff_opens α).mp h ⊤⟩

variable {α β}

/-- In a Noetherian space, all sets are compact. -/
/-
**TopologicalSpace.NoetherianSpace.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] (s : Set α), IsCompact s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_finite_subcover`：isCompact_iff_finite_subcover : IsCompact
 s ↔ forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subset
eq ⋃ i, U i) -> exi…
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.noetherianSpace_iff_opens`：noetherianSpace_iff_opens : 
NoetherianSpace α ↔ forall s : Opens α, IsCompact (s : Set α)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
In a Noetherian space, all sets are compact.
-/
protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s := by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩
/-
**TopologicalSpace._root_.Topology.IsInducing.noetherianSpace** 是 Mathlib 中的一个定理
，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Topology.IsInducing.noetherianSpace [NoetherianSpace α] {i : β → α}
    (hi : IsInducing i) : NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)

@[stacks 0052 "(1)"]
/-
**TopologicalSpace.NoetherianSpace.set** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] (s : Set α),   TopologicalSpace.NoetherianSpace ↑s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.noetherianSpace`：∀ {α : Type u_1} {β : Type u_2} [in
st : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [TopologicalSpace.Noeth
erianSpace α] {i : β → α}…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
instance NoetherianSpace.set [NoetherianSpace α] (s : Set α) : NoetherianSpace s :=
  IsInducing.subtypeVal.noetherianSpace

variable (α) in
open List in
/-
**TopologicalSpace.noetherianSpace_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace`。
形式化陈述：noetherianSpace_TFAE : TFAE [NoetherianSpace α, WellFoundedLT (Closeds α),
 forall s : Set α, IsCompact s, forall s : Opens α, IsCompact (s : Set α)]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.wellFounded_iff`：Function.Surjective.wellFounded_iff
 {f : α -> β} (hf : Surjective f) (o : forall {a b}, r a b ↔ s (f a) (f b)) : We
llFounded r ↔ WellFounded…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.Opens.compl_bijective`：∀ {α : Type u_2} [inst : Topolog
icalSpace α], Function.Bijective TopologicalSpace.Opens.compl
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `TopologicalSpace.noetherianSpace_iff_opens`：noetherianSpace_iff_opens : 
NoetherianSpace α ↔ forall s : Opens α, IsCompact (s : Set α)
· 使用定理 `TopologicalSpace.NoetherianSpace.isCompact`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [TopologicalSpace.NoetherianSpace α] (s : Set α), IsCompact s
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem noetherianSpace_TFAE :
    TFAE [NoetherianSpace α,
      WellFoundedLT (Closeds α),
      ∀ s : Set α, IsCompact s,
      ∀ s : Opens α, IsCompact (s : Set α)] := by
  tfae_have 1 ↔ 2 := by
    simp_rw [isWellFounded_iff]
    exact Opens.compl_bijective.2.wellFounded_iff (@OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4 := noetherianSpace_iff_opens α
  tfae_have 1 → 3 := @NoetherianSpace.isCompact α _
  tfae_have 3 → 4 := fun h s => h s
  tfae_finish
/-
**TopologicalSpace.noetherianSpace_iff_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace`。
形式化陈述：noetherianSpace_iff_isCompact : NoetherianSpace α ↔ forall s : Set α, IsCo
mpact s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TopologicalSpace.noetherianSpace_TFAE`：noetherianSpace_TFAE : TFAE [Noet
herianSpace α, WellFoundedLT (Closeds α), forall s : Set α, IsCompact s, forall 
s : Opens α, IsCompact (s :…
-/
theorem noetherianSpace_iff_isCompact : NoetherianSpace α ↔ ∀ s : Set α, IsCompact s :=
  (noetherianSpace_TFAE α).out 0 2
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoetherianSpace α] : WellFoundedLT (Closeds α) :=
  Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} : NoetherianSpace (CofiniteTopology α) := by
  simp only [noetherianSpace_iff_isCompact, isCompact_iff_ultrafilter_le_nhds,
    CofiniteTopology.nhds_eq, Ultrafilter.le_sup_iff, Filter.le_principal_iff]
  intro s f hs
  rcases f.le_cofinite_or_eq_pure with (hf | ⟨a, rfl⟩)
  · rcases Filter.nonempty_of_mem hs with ⟨a, ha⟩
    exact ⟨a, ha, Or.inr hf⟩
  · exact ⟨a, hs, Or.inl le_rfl⟩
/-
**TopologicalSpace.noetherianSpace_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace`。
形式化陈述：noetherianSpace_of_surjective [NoetherianSpace α] (f : α -> β) (hf : Conti
nuous f) (hf' : Function.Surjective f) : NoetherianSpace β
参数：f : α -> β；hf : Continuous f；hf' : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.noetherianSpace_iff_isCompact`：noetherianSpace_iff_isCo
mpact : NoetherianSpace α ↔ forall s : Set α, IsCompact s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Set.image_surjective`：image_surjective : Surjective (image f) ↔ Surjecti
ve f
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `TopologicalSpace.NoetherianSpace.isCompact`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [TopologicalSpace.NoetherianSpace α] (s : Set α), IsCompact s
-/
theorem noetherianSpace_of_surjective [NoetherianSpace α] (f : α → β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β :=
  noetherianSpace_iff_isCompact.2 <| (Set.image_surjective.mpr hf').forall.2 fun s =>
    (NoetherianSpace.isCompact s).image hf
/-
**TopologicalSpace.noetherianSpace_iff_of_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace`。
形式化陈述：noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ Noeth
erianSpace β
参数：f : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.noetherianSpace_of_surjective`：noetherianSpace_of_surje
ctive [NoetherianSpace α] (f : α -> β) (hf : Continuous f) (hf' : Function.Surje
ctive f) : NoetherianSpace β
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
theorem noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩
/-
**TopologicalSpace.NoetherianSpace.range** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β]   [TopologicalSpace.NoetherianSpace α] (f : α → β), Continuous f
 → TopologicalSpace.NoetherianSpace ↑(Set.range f)
参数：f : α → β；Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.noetherianSpace_of_surjective`：noetherianSpace_of_surje
ctive [NoetherianSpace α] (f : α -> β) (hf : Continuous f) (hf' : Function.Surje
ctive f) : NoetherianSpace β
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem NoetherianSpace.range [NoetherianSpace α] (f : α → β) (hf : Continuous f) :
    NoetherianSpace (Set.range f) :=
  noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.rangeFactorization_surjective
/-
**TopologicalSpace.noetherianSpace_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace`。
形式化陈述：noetherianSpace_set_iff (s : Set α) : NoetherianSpace s ↔ forall t, t subs
eteq s -> IsCompact t
参数：s : Set α。
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
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem noetherianSpace_set_iff (s : Set α) :
    NoetherianSpace s ↔ ∀ t, t ⊆ s → IsCompact t := by
  simp only [noetherianSpace_iff_isCompact, IsEmbedding.subtypeVal.isCompact_iff,
    Subtype.forall_set_subtype]

@[simp]
/-
**TopologicalSpace.noetherian_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce`。
形式化陈述：noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace
 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.noetherianSpace_iff_of_homeomorph`：noetherianSpace_iff_
of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β
-/
theorem noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α :=
  noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)
/-
**TopologicalSpace.NoetherianSpace.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {ι : Type u_3} (f : ι → Set α
) [Finite ι]   [hf : ∀ (i : ι), TopologicalSpace.NoetherianSpace ↑(f i)], Topolo
gicalSpace.NoetherianSpace ↑(⋃ i, f i)
参数：f : ι → Set α；i : ι；f i；⋃ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem NoetherianSpace.iUnion {ι : Type*} (f : ι → Set α) [Finite ι]
    [hf : ∀ i, NoetherianSpace (f i)] : NoetherianSpace (⋃ i, f i) := by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  intro t ht
  rw [← Set.inter_eq_left.mpr ht, Set.inter_iUnion]
  exact isCompact_iUnion fun i => hf i _ Set.inter_subset_right

-- This is not an instance since it makes a loop with `t2_space_discrete`.
/-
**TopologicalSpace.NoetherianSpace.discrete** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] [T2Space α], DiscreteTopology α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.NoetherianSpace.isCompact`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [TopologicalSpace.NoetherianSpace α] (s : Set α), IsCompact s
-/
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩

attribute [local instance] NoetherianSpace.discrete

/-- Spaces that are both Noetherian and Hausdorff are finite. -/
/-
**TopologicalSpace.NoetherianSpace.finite** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] [T2Space α], Finite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_finite_univ`：∀ {α : Type u}, Set.univ.Finite → Finite α
· 使用定理 `IsCompact.finite_of_discrete`：IsCompact.finite_of_discrete [DiscreteTopo
logy X] (hs : IsCompact s) : s.Finite
· 使用定理 `TopologicalSpace.NoetherianSpace.discrete`：∀ {α : Type u_1} [inst : Topo
logicalSpace α] [TopologicalSpace.NoetherianSpace α] [T2Space α], DiscreteTopolo
gy α
· 使用定理 `TopologicalSpace.NoetherianSpace.isCompact`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [TopologicalSpace.NoetherianSpace α] (s : Set α), IsCompact s

--- 原说明 ---
Spaces that are both Noetherian and Hausdorff are finite.
-/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α :=
  Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Finite.to_noetherianSpace [Finite α] : NoetherianSpace α :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IndiscreteTopology α] : NoetherianSpace α :=
  noetherianSpace_of_surjective CofiniteTopology.of.symm continuous_of_indiscreteTopology
    CofiniteTopology.of.symm.surjective

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
/-
**TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible** 是 Mat
hlib 中的一个定理，位于命名空间 `TopologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] (s : TopologicalSpace.Closeds α),   ∃ S, S.Finite ∧ (∀ t ∈ S, IsIrreduci
ble ↑t) ∧ s = sSup S
参数：s : TopologicalSpace.Closeds α；∀ t ∈ S, IsIrreducible ↑t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `TopologicalSpace.instWellFoundedLTClosedsOfNoetherianSpace`：∀ {α : Type 
u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α],   WellFou
ndedLT (TopologicalSpace.Closeds α)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Closeds.coe_nonempty`：coe_nonempty {s : Closeds α} : (s
 : Set α).Nonempty ↔ s != ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `TopologicalSpace.Closeds.instCanLiftSetCoeIsClosed`：∀ {α : Type u_2} [in
st : TopologicalSpace α], CanLift (Set α) (TopologicalSpace.Closeds α) SetLike.c
oe IsClosed
· 使用定理 `inf_lt_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b <
 a ↔ ¬a ≤ b
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `sSup_union`：sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup 
t
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
In a Noetherian space, every closed set is a finite union of irreducible closed 
sets.
-/
theorem NoetherianSpace.exists_finite_set_closeds_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Set (Closeds α), S.Finite ∧ (∀ t ∈ S, IsIrreducible (t : Set α)) ∧ s = sSup S := by
  apply wellFounded_lt.induction s; clear s
  intro s H
  rcases eq_or_ne s ⊥ with rfl | h₀
  · use ∅; simp
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      use {s}; simp [h₁]
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      refine ⟨S₁ ∪ S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
/-
**TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible** 是 Ma
thlib 中的一个定理，位于命名空间 `TopologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] {s : Set α},   IsClosed s → ∃ S, S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t
 ∈ S, IsIrreducible t) ∧ s = ⋃₀ S
参数：∀ t ∈ S, IsClosed t；∀ t ∈ S, IsIrreducible t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `TopologicalSpace.Closeds.instCanLiftSetCoeIsClosed`：∀ {α : Type u_2} [in
st : TopologicalSpace α], CanLift (Set α) (TopologicalSpace.Closeds α) SetLike.c
oe IsClosed
· 使用定理 `TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible`：
∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α
] (s : TopologicalSpace.Closeds α),   ∃ S, S.Finite ∧ (∀ t ∈…
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `TopologicalSpace.Closeds.isClosed'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Closeds α), IsClosed self.carrier
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Closeds.coe_finset_sup`：coe_finset_sup (f : ι -> Closed
s α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In a Noetherian space, every closed set is a finite union of irreducible closed 
sets.
-/
theorem NoetherianSpace.exists_finite_set_isClosed_irreducible [NoetherianSpace α]
    {s : Set α} (hs : IsClosed s) : ∃ S : Set (Set α), S.Finite ∧
      (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧ s = ⋃₀ S := by
  lift s to Closeds α using hs
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  refine ⟨(↑) '' S, hSf.image _, Set.forall_mem_image.2 fun S _ ↦ S.2, Set.forall_mem_image.2 hS,
    ?_⟩
  lift S to Finset (Closeds α) using hSf
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
/-
**TopologicalSpace.NoetherianSpace.exists_finset_irreducible** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α] (s : TopologicalSpace.Closeds α),   ∃ S, (∀ (k : ↥S), IsIrreducible ↑↑k)
 ∧ s = S.sup id
参数：s : TopologicalSpace.Closeds α；∀ (k : ↥S), IsIrreducible ↑↑k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible`：
∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α
] (s : TopologicalSpace.Closeds α),   ∃ S, S.Finite ∧ (∀ t ∈…

--- 原说明 ---
In a Noetherian space, every closed set is a finite union of irreducible closed 
sets.
-/
theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s

@[stacks 0052 "(2)"]
/-
**TopologicalSpace.NoetherianSpace.finite_irreducibleComponents** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α], (irreducibleComponents α).Finite
参数：irreducibleComponents α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`
：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace 
α] {s : Set α},   IsClosed s → ∃ S, S.Finite ∧ (∀ t ∈ S, IsCl…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIrreducible_iff_sUnion_isClosed`：isIrreducible_iff_sUnion_isClosed : I
sIrreducible s ↔ forall t : Finset (Set X), (forall z in t, IsClosed z) -> (s su
bseteq ⋃₀ ↑t) -> exists…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem NoetherianSpace.finite_irreducibleComponents [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]

@[stacks 0052 "(3)"]
/-
**TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComp
onent** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianS
pace α],   ∀ Z ∈ irreducibleComponents α, ∃ o, IsOpen o ∧ o.Nonempty ∧ o ⊆ Z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`：∀ {α : Ty
pe u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α], (irred
ucibleComponents α).Finite
· 使用定理 `closure_sUnion_irreducibleComponents_sdiff_singleton`：closure_sUnion_irr
educibleComponents_sdiff_singleton (hX : (irreducibleComponents X).Finite) (Z : 
Set X) (hZ : Z in irreducibleComponents X)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_empty_ne`：nonempty_iff_empty_ne : s.Nonempty ↔ ∅ != s
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent [NoetherianSpace α]
    (Z : Set α) (H : Z ∈ irreducibleComponents α) :
    ∃ o : Set α, IsOpen o ∧ o.Nonempty ∧ o ⊆ Z := by
  have hα : (irreducibleComponents α).Finite := finite_irreducibleComponents
  have hZ := closure_sUnion_irreducibleComponents_sdiff_singleton hα Z H
  refine ⟨(⋃₀ (irreducibleComponents α \ {Z}))ᶜ, ?_, ?_, subset_closure.trans hZ.le⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hα.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · contrapose! hZ
    rw [hZ, closure_empty, ← Set.nonempty_iff_empty_ne]
    exact H.1.nonempty
/-
**TopologicalSpace.NoetherianSpace.of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {W V : Set α} [TopologicalSpa
ce.NoetherianSpace ↑W],   V ⊆ W → TopologicalSpace.NoetherianSpace ↑V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.noetherianSpace`：∀ {α : Type u_1} {β : Type u_2} [in
st : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [TopologicalSpace.Noeth
erianSpace α] {i : β → α}…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
-/
lemma NoetherianSpace.of_subset {W V : Set α} [NoetherianSpace W]
    (h : V ⊆ W) : NoetherianSpace V :=
  Topology.IsInducing.noetherianSpace (Topology.IsEmbedding.inclusion h).isInducing
/-
**TopologicalSpace.NoetherianSpace.inter_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (W V : Set α) [TopologicalSpa
ce.NoetherianSpace ↑W],   TopologicalSpace.NoetherianSpace ↑(W ∩ V)
参数：W V : Set α；W ∩ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NoetherianSpace.of_subset`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] {W V : Set α} [TopologicalSpace.NoetherianSpace ↑W],   V ⊆ W → 
TopologicalSpace.NoetherianSpace…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma NoetherianSpace.inter_of_left (W V : Set α) [NoetherianSpace W] :
    NoetherianSpace (W ∩ V : Set α) := .of_subset Set.inter_subset_left
/-
**TopologicalSpace.NoetherianSpace.inter_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NoetherianSpace`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (W V : Set α) [TopologicalSpa
ce.NoetherianSpace ↑V],   TopologicalSpace.NoetherianSpace ↑(W ∩ V)
参数：W V : Set α；W ∩ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NoetherianSpace.of_subset`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] {W V : Set α} [TopologicalSpace.NoetherianSpace ↑W],   V ⊆ W → 
TopologicalSpace.NoetherianSpace…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma NoetherianSpace.inter_of_right (W V : Set α) [NoetherianSpace V] :
    NoetherianSpace (W ∩ V : Set α) := .of_subset Set.inter_subset_right

end TopologicalSpace

