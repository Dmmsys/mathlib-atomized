/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic

/-!
# Connected subsets and their relation to clopen sets

In this file we show how connected subsets of a topological space are intimately connected
to clopen sets.

## Main declarations

+ `IsClopen.biUnion_connectedComponent_eq`: a clopen set is the union of its connected components.
+ `PreconnectedSpace.induction₂`: an induction principle for preconnected spaces.
+ `ConnectedComponents`: The connected components of a topological space, as a quotient type.

-/

@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
/-
**IsPreconnected.subset_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht :
 IsClopen t) (hne : (s inter t).Nonempty) : s subseteq t
参数：hs : IsPreconnected s；ht : IsClopen t；hne : (s inter t).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_left_of_subset_union`：IsPreconnected.subset_left_o
f_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s su
bseteq u union v) (hsu : (s inte…
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ

--- 原说明 ---
Preconnected sets are either contained in or disjoint to any given clopen set.
-/
theorem IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s ∩ t).Nonempty) : s ⊆ t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne
/-
**Sigma.isConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.isConnected_iff [forall i, TopologicalSpace (X i)] {s : Set (Σ i, X 
i)} : IsConnected s ↔ exists i t, IsConnected t ∧ s = Sigma.mk i '' t
参数：X i；Σ i, X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.subset_isClopen`：IsPreconnected.subset_isClopen {s t : Se
t α} (hs : IsPreconnected s) (ht : IsClopen t) (hne : (s inter t).Nonempty) : s 
subseteq t
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `isClopen_range_sigmaMk`：isClopen_range_sigmaMk {X : ι -> Type*} [forall 
i, TopologicalSpace (X i)] {i : ι} : IsClopen (Set.range (@Sigma.mk ι X i))
· 使用定理 `IsConnected.preimage_of_isOpenMap`：IsConnected.preimage_of_isOpenMap [To
pologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α -> β} (hinj : Function
.Injective f) (hf : IsO…
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
-/
theorem Sigma.isConnected_iff [∀ i, TopologicalSpace (X i)] {s : Set (Σ i, X i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn
/-
**Sigma.isPreconnected_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.isPreconnected_iff [hι : Nonempty ι] [forall i, TopologicalSpace (X 
i)] {s : Set (Σ i, X i)} : IsPreconnected s ↔ exists i t, IsPreconnected t ∧ s =
 Sigma.mk i '' t
参数：X i；Σ i, X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sigma.isConnected_iff`：Sigma.isConnected_iff [forall i, TopologicalSpace
 (X i)] {s : Set (Σ i, X i)} : IsConnected s ↔ exists i t, IsConnected t ∧ s = S
igma.mk i '…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
-/
theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (X i)]
    {s : Set (Σ i, X i)} : IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn
/-
**Sum.isConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sum.isConnected_iff [TopologicalSpace β] {s : Set (α oplus β)} : IsConnect
ed s ↔ (exists t, IsConnected t ∧ s = Sum.inl '' t) ∨ exists t, IsConnected t ∧ 
s = Sum.inr '' t
参数：α oplus β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.subset_isClopen`：IsPreconnected.subset_isClopen {s t : Se
t α} (hs : IsPreconnected s) (ht : IsClopen t) (hne : (s inter t).Nonempty) : s 
subseteq t
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `isClopen_range_inl`：isClopen_range_inl : IsClopen (range (Sum.inl : X ->
 X oplus Y))
· 使用定理 `IsConnected.preimage_of_isOpenMap`：IsConnected.preimage_of_isOpenMap [To
pologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α -> β} (hinj : Function
.Injective f) (hf : IsO…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `isOpenMap_inl`：isOpenMap_inl : IsOpenMap (@inl X Y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `isClopen_range_inr`：isClopen_range_inr : IsClopen (range (Sum.inr : Y ->
 X oplus Y))
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `isOpenMap_inr`：isOpenMap_inr : IsOpenMap (@inr X Y)
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
-/
theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsConnected s ↔
      (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s ⊆ range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s ⊆ range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn
/-
**Sum.isPreconnected_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (α oplus β)} : IsPrec
onnected s ↔ (exists t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ exists t, IsPreco
nnected t ∧ s = Sum.inr '' t
参数：α oplus β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.isConnected_iff`：Sum.isConnected_iff [TopologicalSpace β] {s : Set (
α oplus β)} : IsConnected s ↔ (exists t, IsConnected t ∧ s = Sum.inl '' t) ∨ exi
sts t, Is…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
-/
theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsPreconnected s ↔
      (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

/-- A continuous map from a connected space to a disjoint union `Σ i, X i` can be lifted to one of
the components `X i`. See also `ContinuousMap.exists_lift_sigma` for a version with bundled
`ContinuousMap`s. -/
/-
**Continuous.exists_lift_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_lift_sigma [ConnectedSpace α] [forall i, TopologicalSpac
e (X i)] {f : α -> Σ i, X i} (hf : Continuous f) : exists (i : ι) (g : α -> X i)
, Continuous g ∧ f = Sigma.mk i ∘ g
参数：X i；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sigma.isConnected_iff`：Sigma.isConnected_iff [forall i, TopologicalSpace
 (X i)] {s : Set (Σ i, X i)} : IsConnected s ↔ exists i t, IsConnected t ∧ s = S
igma.mk i '…
· 使用定理 `isConnected_range`：isConnected_range [TopologicalSpace β] [ConnectedSpac
e α] {f : α -> β} (h : Continuous f) : IsConnected (range f)
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Set.range_subset_range_iff_exists_comp`：range_subset_range_iff_exists_co
mp {f : α -> γ} {g : β -> γ} : range f subseteq range g ↔ exists h : α -> β, f =
 g ∘ h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.sigmaMk`：Topology.IsEmbedding.sigmaMk {i : ι} : IsE
mbedding (@Sigma.mk ι σ i)

--- 原说明 ---
A continuous map from a connected space to a disjoint union `Σ i, X i` can be li
fted to one of
the components `X i`. See also `ContinuousMap.exists_lift_sigma` for a version w
ith bundled
`ContinuousMap`s.
-/
theorem Continuous.exists_lift_sigma [ConnectedSpace α] [∀ i, TopologicalSpace (X i)]
    {f : α → Σ i, X i} (hf : Continuous f) :
    ∃ (i : ι) (g : α → X i), Continuous g ∧ f = Sigma.mk i ∘ g := by
  obtain ⟨i, hi⟩ : ∃ i, range f ⊆ range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf
/-
**nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_inter [PreconnectedSpace α] {s t : Set α} : IsOpen s -> IsOpen t 
-> s union t = univ -> s.Nonempty -> t.Nonempty -> (s inter t).Nonempty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
-/
theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t
/-
**isClopen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = 
univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nonempty_inter`：nonempty_inter [PreconnectedSpace α] {s t : Set α} : IsO
pen s -> IsOpen t -> s union t = univ -> s.Nonempty -> t.Nonempty -> (s inter t)
.Non…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `isClopen_empty`：isClopen_empty : IsClopen (∅ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClopen_univ`：isClopen_univ : IsClopen (univ : Set X)
-/
theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s.Nonempty ∧ sᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using h
      have ⟨_, h2, h3⟩ := nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) h1.1 h1.2
      h3 h2,
    by rintro (rfl | rfl); exacts [isClopen_empty, isClopen_univ]⟩
/-
**IsClopen.eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : 
s.Nonempty) : s = univ
参数：h' : IsClopen s；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
-/
theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty

open Set.Notation in
/-
**isClopen_preimage_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X} (hu :
 IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (v ↓inter u)
参数：hu : IsOpen u；huv : Disjoint (frontier u) v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_induced_iff`：isClosed_induced_iff [t : TopologicalSpace β] {s :
 Set α} {f : α -> β} : IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t 
= s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用引理 `Set.image_val_injective`：image_val_injective : Function.Injective ((↑) :
 Set A -> Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `closure_eq_self_union_frontier`：closure_eq_self_union_frontier (s : Set 
X) : closure s = s union frontier s
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
-/
lemma isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (v ↓∩ u) := by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_comm _ (frontier u),
    huv.inter_eq, union_empty]

section disjoint_subsets

variable [PreconnectedSpace α]
  {s : ι → Set α} (h_nonempty : ∀ i, (s i).Nonempty) (h_disj : Pairwise (Disjoint on s))
include h_nonempty h_disj

/-- In a preconnected space, any disjoint family of non-empty clopen subsets has at most one
element. -/
/-
**subsingleton_of_disjoint_isClopen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_of_disjoint_isClopen (h_clopen : forall i, IsClopen (s i)) : 
Subsingleton ι
参数：h_clopen : forall i, IsClopen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a

--- 原说明 ---
In a preconnected space, any disjoint family of non-empty clopen subsets has at 
most one
element.
-/
lemma subsingleton_of_disjoint_isClopen
    (h_clopen : ∀ i, IsClopen (s i)) :
    Subsingleton ι := by
  rw [← not_nontrivial_iff_subsingleton]
  by_contra ⟨i, j, h_ne⟩
  replace h_ne : s i ∩ s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact (h_nonempty i).ne_empty hi
  · rw [hi, univ_inter] at h_ne
    exact (h_nonempty j).ne_empty h_ne

/-- In a preconnected space, any disjoint cover by non-empty open subsets has at most one
element. -/
/-
**subsingleton_of_disjoint_isOpen_iUnion_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_of_disjoint_isOpen_iUnion_eq_univ (h_open : forall i, IsOpen 
(s i)) (h_Union : ⋃ i, s i = univ) : Subsingleton ι
参数：h_open : forall i, IsOpen (s i)；h_Union : ⋃ i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subsingleton_of_disjoint_isClopen`：subsingleton_of_disjoint_isClopen (h_
clopen : forall i, IsClopen (s i)) : Subsingleton ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Set.iUnion_sdiff`：iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 \ s = ⋃ i, t i \ s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
In a preconnected space, any disjoint cover by non-empty open subsets has at mos
t one
element.
-/
lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    (h_open : ∀ i, IsOpen (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff, compl_eq_univ_sdiff, ← h_Union, iUnion_sdiff]
  refine isOpen_iUnion (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

/-- In a preconnected space, any finite disjoint cover by non-empty closed subsets has at most one
element. -/
/-
**subsingleton_of_disjoint_isClosed_iUnion_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι] (h_closed : fo
rall i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) : Subsingleton ι
参数：h_closed : forall i, IsClosed (s i)；h_Union : ⋃ i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subsingleton_of_disjoint_isClopen`：subsingleton_of_disjoint_isClopen (h_
clopen : forall i, IsClopen (s i)) : Subsingleton ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Set.iUnion_sdiff`：iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 \ s = ⋃ i, t i \ s
· 使用定理 `isClosed_iUnion_of_finite`：isClosed_iUnion_of_finite [Finite ι] {s : ι -
> Set X} (h : forall i, IsClosed (s i)) : IsClosed (⋃ i, s i)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
In a preconnected space, any finite disjoint cover by non-empty closed subsets h
as at most one
element.
-/
lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι]
    (h_closed : ∀ i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff, compl_eq_univ_sdiff, ← h_Union, iUnion_sdiff]
  refine isClosed_iUnion_of_finite (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

end disjoint_subsets

/-
**frontier_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} : frontier s = ∅ ↔
 s = ∅ ∨ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isClopen_iff_frontier_eq_empty`：isClopen_iff_frontier_eq_empty : IsClope
n s ↔ frontier s = ∅
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
-/
theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff
/-
**nonempty_frontier_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} : (frontier s).Non
empty ↔ s.Nonempty ∧ s != univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s ≠ univ := by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

/-- In a preconnected space, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
/-
**PreconnectedSpace.induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preconnected space, given a transitive relation `P`, if `P x y` and `P y x`
 are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a versio
n of the fact
that, if an equivalence relation has open classes, then it has a single equivale
nce class.
-/
lemma PreconnectedSpace.induction₂' [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y ∧ P y x) (h' : IsTrans α P) (x y : α) :
    P x y := by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz ↦ ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h'.trans x t z h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz ↦ ?_)
    filter_upwards [h z] with t ht
    exact h'.trans x z t hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y ∈ u
  simp [D]

/-- In a preconnected space, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
/-
**PreconnectedSpace.induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preconnected space, if a symmetric transitive relation `P x y` is true for 
`y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that,
 if an equivalence
relation has open classes, then it has a single equivalence class.
-/
lemma PreconnectedSpace.induction₂ [PreconnectedSpace α] (P : α → α → Prop) [Std.Symm P]
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y) (h' : IsTrans α P) (x y : α) : P x y := by
  refine PreconnectedSpace.induction₂' P (fun z ↦ ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, symm ha⟩

/-- In a preconnected set, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
/-
**IsPreconnected.induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preconnected set, given a transitive relation `P`, if `P x y` and `P y x` a
re true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a versio
n of the fact
that, if an equivalence relation has open classes, then it has a single equivale
nce class.
-/
lemma IsPreconnected.induction₂' {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y ∧ P y x)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  let Q : s → s → Prop := fun a b ↦ P a b
  change Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · exact ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ↦ h' a b c ha hb hc⟩

/-- In a preconnected set, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
/-
**IsPreconnected.induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preconnected set, if a symmetric transitive relation `P x y` is true for `y
` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that,
 if an equivalence
relation has open classes, then it has a single equivalence class.
-/
lemma IsPreconnected.induction₂ {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    (h'' : ∀ x y, x ∈ s → y ∈ s → P x y → P y x)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  apply hs.induction₂' P (fun z hz ↦ ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

/-- A set `s` is preconnected if and only if for every cover by two open sets that are disjoint on
`s`, it is contained in one of the two covering sets. -/
/-
**isPreconnected_iff_subset_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_iff_subset_of_disjoint {s : Set α} : IsPreconnected s ↔ for
all u v, IsOpen u -> IsOpen v -> s subseteq u union v -> s inter (u inter v) = ∅
 -> s subseteq u ∨ s subseteq v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅

--- 原说明 ---
A set `s` is preconnected if and only if for every cover by two open sets that a
re disjoint on
`s`, it is contained in one of the two covering sets.
-/
theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
/-
**isConnected_iff_sUnion_disjoint_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_iff_sUnion_disjoint_open {s : Set α} : IsConnected s ↔ forall 
U : Finset (Set α), (forall u v : Set α, u in U -> v in U -> (s inter (u inter v
)).Nonempty -> u = v) -> (forall u in U, IsOpen u) -> (s subseteq ⋃₀ ↑U) -> exis
ts u in U, s subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsConnected.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (s : Set α)
, IsConnected s = (s.Nonempty ∧ IsPreconnected s)
· 使用定理 `isPreconnected_iff_subset_of_disjoint`：isPreconnected_iff_subset_of_disj
oint {s : Set α} : IsPreconnected s ↔ forall u v, IsOpen u -> IsOpen v -> s subs
eteq u union v -> s inter (…
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `Set.Nonempty.not_subset_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → 
¬s ⊆ ∅
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint o
n `s`,
it is contained in one of the members of the collection.
-/
theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α), (∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v) →
        (∀ u ∈ U, IsOpen u) → (s ⊆ ⋃₀ ↑U) → ∃ u ∈ U, s ⊆ u := by
  rw [IsConnected, isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
/-
**disjoint_or_subset_of_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht :
 IsClopen t) : Disjoint s t ∨ s subseteq t
参数：hs : IsPreconnected s；ht : IsClopen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `IsPreconnected.subset_isClopen`：IsPreconnected.subset_isClopen {s t : Se
t α} (hs : IsPreconnected s) (ht : IsClopen t) (hne : (s inter t).Nonempty) : s 
subseteq t
· 使用引理 `Set.disjoint_or_nonempty_inter`：disjoint_or_nonempty_inter (s t : Set α)
 : Disjoint s t ∨ (s inter t).Nonempty

--- 原说明 ---
Preconnected sets are either contained in or disjoint to any given clopen set.
-/
theorem disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right <| hs.subset_isClopen ht

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
/-
**isPreconnected_iff_subset_of_disjoint_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_iff_subset_of_disjoint_closed : IsPreconnected s ↔ forall u
 v, IsClosed u -> IsClosed v -> s subseteq u union v -> s inter (u inter v) = ∅ 
-> s subseteq u ∨ s subseteq v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `isPreconnected_closed_iff`：isPreconnected_closed_iff {s : Set α} : IsPre
connected s ↔ forall t t', IsClosed t -> IsClosed t' -> s subseteq t union t' ->
 (s inter t).No…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅

--- 原说明 ---
A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets.
-/
theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A closed set `s` is preconnected if and only if for every cover by two closed sets that are
disjoint, it is contained in one of the two covering sets. -/
/-
**isPreconnected_iff_subset_of_fully_disjoint_closed** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClo
sed s) : IsPreconnected s ↔ forall u v, IsClosed u -> IsClosed v -> s subseteq u
 union v -> Disjoint u v -> s subseteq u ∨ s subseteq v
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isPreconnected_iff_subset_of_disjoint_closed`：isPreconnected_iff_subset_
of_disjoint_closed : IsPreconnected s ↔ forall u v, IsClosed u -> IsClosed v -> 
s subseteq u union v -> s inter (u…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.inter_inter_distrib_right`：inter_inter_distrib_right (s t u : Set α)
 : s inter t inter u = s inter u inter (t inter u)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
A closed set `s` is preconnected if and only if for every cover by two closed se
ts that are
disjoint, it is contained in one of the two covering sets.
-/
theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq, inter_empty]
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]
/-
**IsClopen.isPreconnected_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.isPreconnected_iff {s : Set α} (hs : IsClopen s) : IsPreconnected
 s ↔ forall a b, IsClopen a -> IsClopen b -> a.Nonempty -> b.Nonempty -> Disjoin
t a b -> s != a union b
参数：hs : IsClopen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Set.union_inter_cancel_left`：union_inter_cancel_left {s t : Set α} : (s 
union t) inter s = s
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用引理 `isClopen_inter_of_disjoint_cover_clopen'`：isClopen_inter_of_disjoint_cov
er_clopen' {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b) (ha :
 IsOpen a) (hb : IsOpen b) (ha…
-/
lemma IsClopen.isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    IsPreconnected s ↔
      ∀ a b, IsClopen a → IsClopen b → a.Nonempty → b.Nonempty → Disjoint a b → s ≠ a ∪ b := by
  refine ⟨?_, fun H a b ha hb hsab hsa hsb ↦ ?_⟩
  · contrapose!
    rintro ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ H
    exact (H a b ha.isOpen hb.isOpen subset_rfl (by rwa [union_inter_cancel_left])
      (by rwa [union_inter_cancel_right])).ne_empty (by grind)
  · rw [nonempty_iff_ne_empty]
    intro h
    exact H (s ∩ a) (s ∩ b)
      (isClopen_inter_of_disjoint_cover_clopen' hs hsab ha hb (by grind))
      (isClopen_inter_of_disjoint_cover_clopen' hs (by grind) hb ha (by grind))
      hsa hsb (by grind [Set.disjoint_iff_inter_eq_empty]) (by grind)
/-
**IsClopen.not_isPreconnected_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.not_isPreconnected_iff {s : Set α} (hs : IsClopen s) : ¬ IsPrecon
nected s ↔ exists a b, IsClopen a ∧ IsClopen b ∧ a.Nonempty ∧ b.Nonempty ∧ Disjo
int a b ∧ s = a union b
参数：hs : IsClopen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsClopen.isPreconnected_iff`：IsClopen.isPreconnected_iff {s : Set α} (hs
 : IsClopen s) : IsPreconnected s ↔ forall a b, IsClopen a -> IsClopen b -> a.No
nempty -> b.Nonem…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsClopen.not_isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    ¬ IsPreconnected s ↔
      ∃ a b, IsClopen a ∧ IsClopen b ∧ a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ s = a ∪ b := by
  simp [hs.isPreconnected_iff]
/-
**IsClopen.connectedComponent_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x in s) : c
onnectedComponent x subseteq s
参数：hs : IsClopen s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_isClopen`：IsPreconnected.subset_isClopen {s t : Se
t α} (hs : IsPreconnected s) (ht : IsClopen t) (hne : (s inter t).Nonempty) : s 
subseteq t
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x ∈ s) :
    connectedComponent x ⊆ s :=
  isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
/-
**connectedComponent_subset_iInter_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_subset_iInter_isClopen {x : α} : connectedComponent x s
ubseteq ⋂ Z : { Z : Set α // IsClopen Z ∧ x in Z }, Z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The connected component of a point is always a subset of the intersection of all
 its clopen
neighbourhoods.
-/
theorem connectedComponent_subset_iInter_isClopen {x : α} :
    connectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

/-- A clopen set is the union of its connected components. -/
/-
**IsClopen.biUnion_connectedComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) : ⋃ x 
in Z, connectedComponent x = Z
参数：h : IsClopen Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x

--- 原说明 ---
A clopen set is the union of its connected components.
-/
theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    ⋃ x ∈ Z, connectedComponent x = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

open Set.Notation in
/-- If `u v : Set X` and `u ⊆ v` is clopen in `v`, then `u` is the union of the connected
components of `v` in `X` which intersect `u`. -/
/-
**IsClopen.biUnion_connectedComponentIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u 
v : Set X} (hu : IsClopen (v ↓inter u)) (huv₁ : u subseteq v) : u = ⋃ x in u, co
nnectedComponentIn v x
参数：hu : IsClopen (v ↓inter u)；huv₁ : u subseteq v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClopen.biUnion_connectedComponent_eq`：IsClopen.biUnion_connectedCompon
ent_eq {Z : Set α} (h : IsClopen Z) : ⋃ x in Z, connectedComponent x = Z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用引理 `Set.image_val_iUnion`：image_val_iUnion : ↑(⋃ i, t i) = ⋃ i, (t i : Set α
)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.subset_iUnion₂_of_subset`：subset_iUnion₂_of_subset {s : Set α} {t : 
forall i, κ i -> Set α} (i : ι) (j : κ i) (h : s subseteq t i j) : s subseteq ⋃ 
(i) (j), t i j

--- 原说明 ---
If `u v : Set X` and `u ⊆ v` is clopen in `v`, then `u` is the union of the conn
ected
components of `v` in `X` which intersect `u`.
-/
lemma IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsClopen (v ↓∩ u)) (huv₁ : u ⊆ v) :
    u = ⋃ x ∈ u, connectedComponentIn v x := by
  have := congr(((↑) : Set v → Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
  exact le_antisymm (iUnion_subset fun _ ↦ le_rfl) <|
    iUnion_subset fun hx ↦ subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl
/-
**IsClopen.connectedComponentIn_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.connectedComponentIn_eq {U : Set α} (hU : IsClopen U) {x : α} (hx
 : x in U) : connectedComponentIn U x = connectedComponent x
参数：hU : IsClopen U；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `isPreconnected_connectedComponentIn`：isPreconnected_connectedComponentIn
 {x : α} {F : Set α} : IsPreconnected (connectedComponentIn F x)
· 使用定理 `mem_connectedComponentIn`：mem_connectedComponentIn {x : α} {F : Set α} (
hx : x in F) : x in connectedComponentIn F x
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
-/
lemma IsClopen.connectedComponentIn_eq {U : Set α} (hU : IsClopen U) {x : α} (hx : x ∈ U) :
    connectedComponentIn U x = connectedComponent x :=
  subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

variable [TopologicalSpace β] {f : α → β}

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
/-
**Topology.IsCoinducing.isConnected_preimage_of_isClosed** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Topology.IsCoinducing.isConnected_preimage_of_isClosed (connected_fibers :
 forall t : β, IsConnected (f ⁻¹' {t})) (hcl : IsCoinducing f) {t : Set β} (ht :
 IsClosed t) (ht' : IsConnected t) : IsConnected (f ⁻¹' t)
参数：connected_fibers : forall t : β, IsConnected (f ⁻¹' {t})；hcl : IsCoinducing f
；ht : IsClosed t；ht' : IsConnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Nonempty.preimage`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.No
nempty → ∀ {f : α → β}, Function.Surjective f → (f ⁻¹' s).Nonempty
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPreconnected_iff_subset_of_fully_disjoint_closed`：isPreconnected_iff_s
ubset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) : IsPreconnected s 
↔ forall u v, IsClosed u -> IsClosed v -…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPreconnected_iff_subset_of_disjoint_closed`：isPreconnected_iff_subset_
of_disjoint_closed : IsPreconnected s ↔ forall u v, IsClosed u -> IsClosed v -> 
s subseteq u union v -> s inter (u…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Function.Surjective.preimage_subset_preimage_iff`：∀ {α : Type u_1} {β : 
Type u_2} {f : α → β} {s t : Set β}, Function.Surjective f → (f ⁻¹' s ⊆ f ⁻¹' t 
↔ s ⊆ t)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Disjoint.of_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β},   Fun
ction.Surjective f → ∀ {s t : Set β}, Disjoint (f ⁻¹' s) (f ⁻¹' t) → Disjoint s 
t
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The preimage of a connected component is preconnected if the function has connec
ted fibers
and a subset is closed iff the preimage is.
-/
theorem Topology.IsCoinducing.isConnected_preimage_of_isClosed
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) {t : Set β} (ht : IsClosed t) (ht' : IsConnected t) :
    IsConnected (f ⁻¹' t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' ∈ t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

@[deprecated Topology.IsCoinducing.isConnected_preimage_of_isClosed (since := "2026-04-01")]
/-
**preimage_connectedComponent_connected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_connectedComponent_connected (connected_fibers : forall t : β, Is
Connected (f ⁻¹' {t})) (hcl : IsCoinducing f) (t : β) : IsConnected (f ⁻¹' conne
ctedComponent t)
参数：connected_fibers : forall t : β, IsConnected (f ⁻¹' {t})；hcl : IsCoinducing f
；t : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.isConnected_preimage_of_isClosed`：Topology.IsCoind
ucing.isConnected_preimage_of_isClosed (connected_fibers : forall t : β, IsConne
cted (f ⁻¹' {t})) (hcl : IsCoinducing f) {t …
· 使用定理 `isClosed_connectedComponent`：isClosed_connectedComponent {x : α} : IsClo
sed (connectedComponent x)
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
-/
theorem preimage_connectedComponent_connected (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) (t : β) :
    IsConnected (f ⁻¹' connectedComponent t) := by
  apply hcl.isConnected_preimage_of_isClosed
  · exact isClosed_connectedComponent
  · exact isConnected_connectedComponent
  · exact connected_fibers
/-
**Topology.IsCoinducing.preimage_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Topology.IsCoinducing.preimage_connectedComponent (hf : IsCoinducing f) (h
_fibers : forall y : β, IsConnected (f ⁻¹' {y})) (a : α) : f ⁻¹' connectedCompon
ent (f a) = connectedComponent a
参数：hf : IsCoinducing f；h_fibers : forall y : β, IsConnected (f ⁻¹' {y})；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `Topology.IsCoinducing.isConnected_preimage_of_isClosed`：Topology.IsCoind
ucing.isConnected_preimage_of_isClosed (connected_fibers : forall t : β, IsConne
cted (f ⁻¹' {t})) (hcl : IsCoinducing f) {t …
· 使用定理 `isClosed_connectedComponent`：isClosed_connectedComponent {x : α} : IsClo
sed (connectedComponent x)
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `Continuous.mapsTo_connectedComponent`：Continuous.mapsTo_connectedCompone
nt [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : MapsTo f (conn
ectedComponent a) (connect…
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…
-/
theorem Topology.IsCoinducing.preimage_connectedComponent (hf : IsCoinducing f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f ⁻¹' connectedComponent (f a) = connectedComponent a :=
  ((hf.isConnected_preimage_of_isClosed h_fibers isClosed_connectedComponent
    isConnected_connectedComponent).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)
/-
**Topology.IsCoinducing.image_connectedComponent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsCoinducing.image_connectedComponent {f : α -> β} (hf : IsCoindu
cing f) (h_fibers : forall y : β, IsConnected (f ⁻¹' {y})) (a : α) : f '' connec
tedComponent a = connectedComponent (f a)
参数：hf : IsCoinducing f；h_fibers : forall y : β, IsConnected (f ⁻¹' {y})；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.preimage_connectedComponent`：Topology.IsCoinducing
.preimage_connectedComponent (hf : IsCoinducing f) (h_fibers : forall y : β, IsC
onnected (f ⁻¹' {y})) (a : α) : f ⁻¹' c…
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
-/
lemma Topology.IsCoinducing.image_connectedComponent {f : α → β} (hf : IsCoinducing f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f '' connectedComponent a = connectedComponent (f a) := by
  rw [← hf.preimage_connectedComponent h_fibers,
    image_preimage_eq _ fun y ↦ (h_fibers y).nonempty]

end Preconnected

section connectedComponentSetoid
/-- The setoid of connected components of a topological space -/
@[instance_reducible]
/-
**connectedComponentSetoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid of connected components of a topological space
-/
def connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

/-- The quotient of a space by its connected components -/
/-
**ConnectedComponents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConnectedComponents (α : Type u) [TopologicalSpace α]
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a space by its connected components
-/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)

namespace ConnectedComponents

/-- Coercion from a topological space to the set of connected components of this space. -/
/-
**ConnectedComponents.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ConnectedComponents.mk (j : J) : ConnectedComponents J
参数：j : J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Coercion from a topological space to the set of connected components of this spa
ce.
-/
def mk : α → ConnectedComponents α := Quotient.mk''
/-
**ConnectedComponents.** 是 Mathlib 中的一个实例，位于命名空间 `ConnectedComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
/-
**ConnectedComponents.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedComponents`
。
形式化陈述：coe_eq_coe {x y : α} : (x : ConnectedComponents α) = y ↔ connectedComponen
t x = connectedComponent y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
/-
**ConnectedComponents.coe_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedComponents`
。
形式化陈述：coe_ne_coe {x y : α} : (x : ConnectedComponents α) != y ↔ connectedCompone
nt x != connectedComponent y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ConnectedComponents.coe_eq_coe`：coe_eq_coe {x y : α} : (x : ConnectedCom
ponents α) = y ↔ connectedComponent x = connectedComponent y
-/
theorem coe_ne_coe {x y : α} :
    (x : ConnectedComponents α) ≠ y ↔ connectedComponent x ≠ connectedComponent y :=
  coe_eq_coe.not
/-
**ConnectedComponents.coe_eq_coe'** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedComponents
`。
形式化陈述：coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x in connectedCo
mponent y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ConnectedComponents.coe_eq_coe`：coe_eq_coe {x y : α} : (x : ConnectedCom
ponents α) = y ↔ connectedComponent x = connectedComponent y
· 使用定理 `connectedComponent_eq_iff_mem`：connectedComponent_eq_iff_mem {x y : α} :
 connectedComponent x = connectedComponent y ↔ x in connectedComponent y
-/
theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x ∈ connectedComponent y :=
  coe_eq_coe.trans connectedComponent_eq_iff_mem
/-
**ConnectedComponents.** 是 Mathlib 中的一个实例，位于命名空间 `ConnectedComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨mk default⟩
/-
**ConnectedComponents.** 是 Mathlib 中的一个实例，位于命名空间 `ConnectedComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (ConnectedComponents α) :=
  inferInstanceAs (TopologicalSpace (Quotient _))
/-
**ConnectedComponents.surjective_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedCompone
nts`。
形式化陈述：surjective_coe : Surjective (mk : α -> ConnectedComponents α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem surjective_coe : Surjective (mk : α → ConnectedComponents α) :=
  Quot.mk_surjective
/-
**ConnectedComponents.isQuotientMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedComp
onents`。
形式化陈述：isQuotientMap_coe : IsQuotientMap (mk : α -> ConnectedComponents α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_coe : IsQuotientMap (mk : α → ConnectedComponents α) :=
  isQuotientMap_quot_mk

@[continuity]
/-
**ConnectedComponents.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedCompone
nts`。
形式化陈述：continuous_coe : Continuous (mk : α -> ConnectedComponents α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
· 使用定理 `ConnectedComponents.isQuotientMap_coe`：isQuotientMap_coe : IsQuotientMap
 (mk : α -> ConnectedComponents α)
-/
theorem continuous_coe : Continuous (mk : α → ConnectedComponents α) :=
  isQuotientMap_coe.continuous

@[simp]
/-
**ConnectedComponents.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConnectedComponents`。
形式化陈述：range_coe : range (mk : α -> ConnectedComponents α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
-/
theorem range_coe : range (mk : α → ConnectedComponents α) = univ :=
  surjective_coe.range_eq
/-
**ConnectedComponents.nonempty_iff_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Connected
Components`。
形式化陈述：nonempty_iff_nonempty : Nonempty (ConnectedComponents α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nonempty`：Function.Surjective.nonempty [h : Nonempty
 β] {f : α -> β} (hf : Function.Surjective f) : Nonempty α
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
lemma nonempty_iff_nonempty : Nonempty (ConnectedComponents α) ↔ Nonempty α :=
  ⟨fun _ ↦ ConnectedComponents.surjective_coe.nonempty, fun h ↦ h.map ConnectedComponents.mk⟩
/-
**ConnectedComponents.** 是 Mathlib 中的一个实例，位于命名空间 `ConnectedComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (ConnectedComponents α) := by
  rwa [ConnectedComponents.nonempty_iff_nonempty]
/-
**ConnectedComponents.isEmpty_iff_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `ConnectedCo
mponents`。
形式化陈述：isEmpty_iff_isEmpty : IsEmpty (ConnectedComponents α) ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用引理 `ConnectedComponents.nonempty_iff_nonempty`：nonempty_iff_nonempty : Nonem
pty (ConnectedComponents α) ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isEmpty_iff_isEmpty : IsEmpty (ConnectedComponents α) ↔ IsEmpty α := by
  rw [← not_iff_not, not_isEmpty_iff, not_isEmpty_iff, nonempty_iff_nonempty]
/-
**ConnectedComponents.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `ConnectedComponent
s`。
形式化陈述：subsingleton [PreconnectedSpace α] : Subsingleton (ConnectedComponents α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PreconnectedSpace.connectedComponent_eq_univ`：PreconnectedSpace.connecte
dComponent_eq_univ {X : Type*} [TopologicalSpace X] [h : PreconnectedSpace X] (x
 : X) : connectedComponent x = uni…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance subsingleton [PreconnectedSpace α] : Subsingleton (ConnectedComponents α) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

section

variable {ι : Type*} {U : ι → Set α} (hclopen : ∀ i, IsClopen (U i))
  (hdisj : Pairwise (Disjoint on U)) (hunion : ⋃ i, U i = Set.univ)
  (hconn : ∀ i, IsPreconnected (U i))

include hclopen hdisj hunion in
/-- A pairwise disjoint cover by clopens partitions the connected components. -/
/-
**ConnectedComponents.equivOfIsClopen** 是 Mathlib 中的一个定义，位于命名空间 `ConnectedCompon
ents`。
形式化陈述：equivOfIsClopen : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A pairwise disjoint cover by clopens partitions the connected components.
-/
noncomputable def equivOfIsClopen : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i) := by
  haveI heq {x : α} {i} (hx : x ∈ U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx, (hclopen i).connectedComponentIn_eq hx]
  refine .symm <| .ofBijective
      (fun ⟨i, x⟩ ↦
        x.lift (ConnectedComponents.mk ∘ Subtype.val)
          (fun x y (hxy : connectedComponent x = connectedComponent y) ↦ by
            simp [← heq x.2, ← heq y.2, hxy]))
      ⟨fun ⟨i, x⟩ ⟨j, y⟩ ↦ ?_, fun x ↦ ?_⟩
  · intro hxy
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    obtain rfl : i = j := by
      apply hdisj.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hclopen j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    simp [← Set.image_val_inj, heq, hxy]
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hunion x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl

@[simp]
/-
**ConnectedComponents.equivOfIsClopen_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 `Connect
edComponents`。
形式化陈述：equivOfIsClopen_symm_mk {i : ι} (x : U i) : (equivOfIsClopen hclopen hdisj
 hunion).symm ⟨i, .mk x⟩ = .mk x
参数：x : U i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma equivOfIsClopen_symm_mk {i : ι} (x : U i) :
    (equivOfIsClopen hclopen hdisj hunion).symm ⟨i, .mk x⟩ = .mk x := rfl
/-
**ConnectedComponents.equivOfIsClopen_mk** 是 Mathlib 中的一个引理，位于命名空间 `ConnectedCom
ponents`。
形式化陈述：equivOfIsClopen_mk {i : ι} (x : α) (hx : x in U i) : equivOfIsClopen hclop
en hdisj hunion (.mk x) = ⟨i, .mk ⟨x, hx⟩⟩
参数：x : α；hx : x in U i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivOfIsClopen_mk {i : ι} (x : α) (hx : x ∈ U i) :
    equivOfIsClopen hclopen hdisj hunion (.mk x) = ⟨i, .mk ⟨x, hx⟩⟩ := by
  apply (equivOfIsClopen hclopen hdisj hunion).symm.injective
  simp

include hclopen hdisj hunion in
/-- If `ι` indexes a disjoint union decomposition of `α`, it is equivalent to the connected
components of `α`. -/
/-
**ConnectedComponents.equivOfIsClopenOfIsConnected** 是 Mathlib 中的一个定义，位于命名空间 `Co
nnectedComponents`。
形式化陈述：equivOfIsClopenOfIsConnected (hconn : forall i, IsConnected (U i)) : Conne
ctedComponents α ≃ ι
参数：hconn : forall i, IsConnected (U i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `ι` indexes a disjoint union decomposition of `α`, it is equivalent to the co
nnected
components of `α`.
-/
noncomputable def equivOfIsClopenOfIsConnected (hconn : ∀ i, IsConnected (U i)) :
    ConnectedComponents α ≃ ι :=
  have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  letI _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)
/-
**ConnectedComponents.equivOfIsClopenOfIsConnected_mk** 是 Mathlib 中的一个引理，位于命名空间 
`ConnectedComponents`。
形式化陈述：equivOfIsClopenOfIsConnected_mk (hconn : forall i, IsConnected (U i)) {i :
 ι} (x : α) (hx : x in U i) : equivOfIsClopenOfIsConnected hclopen hdisj hunion 
hconn (.mk x) = i
参数：hconn : forall i, IsConnected (U i)；x : α；hx : x in U i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ConnectedComponents.equivOfIsClopen_mk`：equivOfIsClopen_mk {i : ι} (x : 
α) (hx : x in U i) : equivOfIsClopen hclopen hdisj hunion (.mk x) = ⟨i, .mk ⟨x, 
hx⟩⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivOfIsClopenOfIsConnected_mk (hconn : ∀ i, IsConnected (U i)) {i : ι} (x : α)
    (hx : x ∈ U i) :
    equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn (.mk x) = i := by
  simp [equivOfIsClopenOfIsConnected, equivOfIsClopen_mk _ _ _ _ hx]

end

variable (α) in
/-- If `X` has infinitely many connected components, it admits disjoint union decompositions with
arbitrarily many summands. -/
/-
**ConnectedComponents.exists_fun_isClopen_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 
`ConnectedComponents`。
形式化陈述：exists_fun_isClopen_of_infinite [Infinite (ConnectedComponents α)] (n : Na
t) (hn : 0 < n) : exists (U : Fin n -> Set α), (forall i, IsClopen (U i)) ∧ (for
all i, (U i).Nonempty) ∧ Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.u
niv
参数：ConnectedComponents α；n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `PreirreducibleSpace.preconnectedSpace`：∀ (α : Type u) [inst : Topologica
lSpace α] [PreirreducibleSpace α], PreconnectedSpace α
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.iUnion_fin_add_one_eq_iUnion_succ`：iUnion_fin_add_one_eq_iUnion_succ
 {n : Nat} (f : Fin (n + 1) -> Set α) : ⋃ i, f i = f 0 union Set.iUnion (f ∘ Fin
.succ)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` has infinitely many connected components, it admits disjoint union decomp
ositions with
arbitrarily many summands.
-/
lemma exists_fun_isClopen_of_infinite [Infinite (ConnectedComponents α)] (n : ℕ) (hn : 0 < n) :
    ∃ (U : Fin n → Set α), (∀ i, IsClopen (U i)) ∧ (∀ i, (U i).Nonempty) ∧
      Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ := by
  cases isEmpty_or_nonempty α
  · exact (not_finite (ConnectedComponents α)).elim
  obtain (_ | n) := n
  · simp at hn
  clear hn
  induction n with
  | zero => exact ⟨![.univ], by simp [isClopen_univ, Set.iUnion_fin_add_one_eq_iUnion_succ]⟩
  | succ n IH =>
    obtain ⟨U, h₁, h₂, h₃, h₄⟩ := IH
    obtain ⟨i, hi⟩ : ∃ i, ¬ IsConnected (U i) := by
      simp_rw [isConnected_iff_connectedSpace, ← not_forall]
      exact fun _ ↦ not_finite_iff_infinite.mpr ‹_› (.of_equiv _ (equivOfIsClopen h₁ h₃ h₄).symm)
    obtain ⟨U, rfl⟩ := (Equiv.piCongrLeft (fun _ ↦ Set α) (Equiv.swap 0 i)).symm.surjective U
    cases U using Fin.consCases with | cons s U =>
    simp only [Equiv.piCongrLeft_symm_apply, Equiv.swap_apply_right, Fin.cons_zero] at *
    obtain ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ := (show IsClopen s by simpa using h₁ i)
      |>.not_isPreconnected_iff.mp (mt (⟨by simpa using h₂ i, ·⟩) hi)
    refine ⟨Fin.cons a (Fin.cons b U), ?_, ?_, ?_, ?_⟩
    · simpa [Fin.forall_iff_succ, *] using fun x ↦ h₁ (Equiv.swap 0 i (.succ x))
    · simpa [Fin.forall_iff_succ, *] using fun x ↦ h₂ (Equiv.swap 0 i (.succ x))
    · have h₃' (j : _) : Disjoint (U j) a ∧ Disjoint (U j) b := by
        simpa [onFun] using h₃ ((Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j))
      simpa [Pairwise, Fin.forall_iff_succ, onFun, hab, disjoint_comm (a := a),
        disjoint_comm (a := b), h₃'] using
        h₃.comp_of_injective ((Equiv.swap 0 i).injective.comp (Fin.succ_injective _))
    · simpa [← union_assoc, (Equiv.surjective _).iUnion_comp] using h₄

end ConnectedComponents

/-- The preimage of a singleton in `connectedComponents` is the connected component
of an element in the equivalence class. -/
/-
**connectedComponents_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponents_preimage_singleton {x : α} : (↑) ⁻¹' ({↑x} : Set (Conn
ectedComponents α)) = connectedComponent x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `ConnectedComponents.coe_eq_coe'`：coe_eq_coe' {x y : α} : (x : ConnectedC
omponents α) = y ↔ x in connectedComponent y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The preimage of a singleton in `connectedComponents` is the connected component
of an element in the equivalence class.
-/
theorem connectedComponents_preimage_singleton {x : α} :
    (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedComponent x := by
  ext y
  rw [mem_preimage, mem_singleton_iff, ConnectedComponents.coe_eq_coe']

/-- The preimage of the image of a set under the quotient map to `connectedComponents α`
is the union of the connected components of the elements in it. -/
/-
**connectedComponents_preimage_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponents_preimage_image (U : Set α) : (↑) ⁻¹' ((↑) '' U : Set (
ConnectedComponents α)) = ⋃ x in U, connectedComponent x
参数：U : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_iUnion`：image_eq_iUnion (f : α -> β) (s : Set α) : f '' s =
 ⋃ i in s, {f i}
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `connectedComponents_preimage_singleton`：connectedComponents_preimage_sin
gleton {x : α} : (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedCompone
nt x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The preimage of the image of a set under the quotient map to `connectedComponent
s α`
is the union of the connected components of the elements in it.
-/
theorem connectedComponents_preimage_image (U : Set α) :
    (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x ∈ U, connectedComponent x := by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]
/-
**ConnectedComponents.discreteTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConnectedComponents.discreteTopology_iff : DiscreteTopology (ConnectedComp
onents α) ↔ forall x : α, IsOpen (connectedComponent x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `ConnectedComponents.isQuotientMap_coe`：isQuotientMap_coe : IsQuotientMap
 (mk : α -> ConnectedComponents α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ConnectedComponents.discreteTopology_iff :
    DiscreteTopology (ConnectedComponents α) ↔ ∀ x : α, IsOpen (connectedComponent x) := by
  simp_rw [discreteTopology_iff_isOpen_singleton, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

end connectedComponentSetoid

/-- If every map to `Bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected -/
/-
**isPreconnected_of_forall_constant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_of_forall_constant {s : Set α} (hs : forall f : α -> Bool, 
ContinuousOn f s -> forall x in s, forall y in s, f x = f y) : IsPreconnected s
参数：hs : forall f : α -> Bool, ContinuousOn f s -> forall x in s, forall y in s, 
f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_boolIndicator_iff_isClopen`：continuousOn_boolIndicator_iff_
isClopen (s U : Set X) : ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s -> 
X) ⁻¹' U)
· 使用定理 `Set.preimage_subtype_coe_eq_compl`：preimage_subtype_coe_eq_compl {s u v 
: Set α} (hsuv : s subseteq u union v) (H : s inter (u inter v) = ∅) : ((↑) : s 
-> α) ⁻¹' u = ((↑) ⁻¹' …
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_iff_boolIndicator`：mem_iff_boolIndicator (x : α) : x in s ↔ s.bo
olIndicator x = true
· 使用定理 `Set.notMem_iff_boolIndicator`：notMem_iff_boolIndicator (x : α) : x ∉ s ↔
 s.boolIndicator x = false
· 使用定理 `Bool.true_eq_false`：(true = false) = False

--- 原说明 ---
If every map to `Bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected
-/
theorem isPreconnected_of_forall_constant {s : Set α}
    (hs : ∀ f : α → Bool, ContinuousOn f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : IsPreconnected s := by
  unfold IsPreconnected
  by_contra! ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_notMem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.notMem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

/-- A `PreconnectedSpace` version of `isPreconnected_of_forall_constant` -/
/-
**preconnectedSpace_of_forall_constant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preconnectedSpace_of_forall_constant (hs : forall f : α -> Bool, Continuou
s f -> forall x y, f x = f y) : PreconnectedSpace α
参数：hs : forall f : α -> Bool, Continuous f -> forall x y, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isPreconnected_of_forall_constant`：isPreconnected_of_forall_constant {s 
: Set α} (hs : forall f : α -> Bool, ContinuousOn f s -> forall x in s, forall y
 in s, f x = f y) : IsP…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f

--- 原说明 ---
A `PreconnectedSpace` version of `isPreconnected_of_forall_constant`
-/
theorem preconnectedSpace_of_forall_constant
    (hs : ∀ f : α → Bool, Continuous f → ∀ x y, f x = f y) : PreconnectedSpace α :=
  ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuousOn_univ.mp hf) x y⟩
/-
**preconnectedSpace_iff_clopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preconnectedSpace_iff_clopen : PreconnectedSpace α ↔ forall s : Set α, IsC
lopen s -> s = ∅ ∨ s = Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
· 使用定理 `preconnectedSpace_of_forall_constant`：preconnectedSpace_of_forall_consta
nt (hs : forall f : α -> Bool, Continuous f -> forall x y, f x = f y) : Preconne
ctedSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Bool.compl_singleton`：compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {
!b}
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preconnectedSpace_iff_clopen :
    PreconnectedSpace α ↔ ∀ s : Set α, IsClopen s → s = ∅ ∨ s = Set.univ := by
  refine ⟨fun _ _ => isClopen_iff.mp, fun h ↦ ?_⟩
  refine preconnectedSpace_of_forall_constant fun f hf x y ↦ ?_
  have : f ⁻¹' {false} = (f ⁻¹' {true})ᶜ := by
    rw [← Set.preimage_compl, Bool.compl_singleton, Bool.not_true]
  obtain (h | h) := h _ ((isClopen_discrete {true}).preimage hf) <;> simp_all
/-
**connectedSpace_iff_clopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedSpace_iff_clopen : ConnectedSpace α ↔ Nonempty α ∧ forall s : Set
 α, IsClopen s -> s = ∅ ∨ s = Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `connectedSpace_iff_univ`：connectedSpace_iff_univ : ConnectedSpace α ↔ Is
Connected (univ : Set α)
· 使用定理 `IsConnected.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (s : Set α)
, IsConnected s = (s.Nonempty ∧ IsPreconnected s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `preconnectedSpace_iff_univ`：preconnectedSpace_iff_univ : PreconnectedSpa
ce α ↔ IsPreconnected (univ : Set α)
· 使用定理 `preconnectedSpace_iff_clopen`：preconnectedSpace_iff_clopen : Preconnecte
dSpace α ↔ forall s : Set α, IsClopen s -> s = ∅ ∨ s = Set.univ
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem connectedSpace_iff_clopen :
    ConnectedSpace α ↔ Nonempty α ∧ ∀ s : Set α, IsClopen s → s = ∅ ∨ s = Set.univ := by
  rw [connectedSpace_iff_univ, IsConnected, ← preconnectedSpace_iff_univ,
    preconnectedSpace_iff_clopen, Set.nonempty_iff_univ_nonempty]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : CompactSpace <| ConnectedComponents α := Quotient.compactSpace
