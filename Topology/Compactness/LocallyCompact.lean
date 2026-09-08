/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Compactness.Compact
/-!
# Locally compact spaces

This file contains basic results about locally compact spaces.
-/

public section

open Set Filter Topology TopologicalSpace

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Y] :
    WeaklyLocallyCompactSpace (X × Y) where
  exists_compact_mem_nhds x :=
    let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Finite ι] {X : ι → Type*} [(i : ι) → TopologicalSpace (X i)]
    [(i : ι) → WeaklyLocallyCompactSpace (X i)] :
    WeaklyLocallyCompactSpace ((i : ι) → X i) where
  exists_compact_mem_nhds f := by
    choose s hsc hs using fun i ↦ exists_compact_mem_nhds (f i)
    exact ⟨pi univ s, isCompact_univ_pi hsc, set_pi_mem_nhds univ.toFinite fun i _ ↦ hs i⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [CompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩
/-
**Topology.IsClosedEmbedding.weaklyLocallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [WeaklyLocallyCompactSpace Y]   {f : X → Y}, Topology.IsClosedEm
bedding f → WeaklyLocallyCompactSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
-/
protected theorem Topology.IsClosedEmbedding.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x :=
    let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hK, hf.continuous.continuousAt hKx⟩
/-
**IsClosed.weaklyLocallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X]
 {s : Set X},   IsClosed s → WeaklyLocallyCompactSpace ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.weaklyLocallyCompactSpace`：∀ {X : Type u_1} {
Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [WeaklyL
ocallyCompactSpace Y]   {f : X → Y}, Topol…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
-/
protected theorem IsClosed.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) : WeaklyLocallyCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace
/-
**IsOpenQuotientMap.weaklyLocallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenQuotientMap.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X] 
{f : X -> Y} (hf : IsOpenQuotientMap f) : WeaklyLocallyCompactSpace Y where exis
ts_compact_mem_nhds
参数：hf : IsOpenQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem IsOpenQuotientMap.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {f : X → Y} (hf : IsOpenQuotientMap f) : WeaklyLocallyCompactSpace Y where
  exists_compact_mem_nhds := by
    refine hf.surjective.forall.2 fun x ↦ ?_
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    exact ⟨f '' K, hKc.image hf.continuous, hf.isOpenMap.image_mem_nhds hKx⟩

/-- In a weakly locally compact space,
every compact set is contained in the interior of a compact set. -/
/-
**exists_compact_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_compact_superset [WeaklyLocallyCompactSpace X] {K : Set X} (hK : Is
Compact K) : exists K', IsCompact K' ∧ K subseteq interior K'
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_mem_nhds`：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.isCompact_biUnion`：Finset.isCompact_biUnion (s : Finset ι) {f : ι
 -> Set X} (hf : forall i in s, IsCompact (f i)) : IsCompact (⋃ i in s, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
In a weakly locally compact space,
every compact set is contained in the interior of a compact set.
-/
theorem exists_compact_superset [WeaklyLocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ interior K' := by
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ ↦ interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x ∈ I, s x, I.isCompact_biUnion fun _ _ ↦ hc _, hIK.trans ?_⟩
  exact iUnion₂_subset fun x hx ↦ interior_mono <| subset_iUnion₂ (s := fun x _ ↦ s x) x hx

/-- In a weakly locally compact space,
the filters `𝓝 x` and `cocompact X` are disjoint for all `X`. -/
/-
**disjoint_nhds_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_cocompact [WeaklyLocallyCompactSpace X] (x : X) : Disjoint (
𝓝 x) (cocompact X)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X

--- 原说明 ---
In a weakly locally compact space,
the filters `𝓝 x` and `cocompact X` are disjoint for all `X`.
-/
theorem disjoint_nhds_cocompact [WeaklyLocallyCompactSpace X] (x : X) :
    Disjoint (𝓝 x) (cocompact X) :=
  let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact
/-
**compact_basis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compact_basis_nhds [LocallyCompactSpace X] (x : X) : (𝓝 x).HasBasis (fun s
 => s in 𝓝 x ∧ IsCompact s) fun s => s
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
-/
theorem compact_basis_nhds [LocallyCompactSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  hasBasis_self.2 <| by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x
/-
**local_compact_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：local_compact_nhds [LocallyCompactSpace X] {x : X} {n : Set X} (h : n in 𝓝
 x) : exists s in 𝓝 x, s subseteq n ∧ IsCompact s
参数：h : n in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
-/
theorem local_compact_nhds [LocallyCompactSpace X] {x : X} {n : Set X} (h : n ∈ 𝓝 x) :
    ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h
/-
**LocallyCompactSpace.of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyCompactSpace.of_hasBasis {ι : X -> Type*} {p : forall x, ι x -> Pro
p} {s : forall x, ι x -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s x)) (hc :
 forall x i, p x i -> IsCompact (s x i)) : LocallyCompactSpace X
参数：h : forall x, (𝓝 x).HasBasis (p x) (s x)；hc : forall x i, p x i -> IsCompact 
(s x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem LocallyCompactSpace.of_hasBasis {ι : X → Type*} {p : ∀ x, ι x → Prop}
    {s : ∀ x, ι x → Set X} (h : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace X :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩
/-
**Prod.locallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.locallyCompactSpace (X : Type*) (Y : Type*) [TopologicalSpace X] [Top
ologicalSpace Y] [LocallyCompactSpace X] [LocallyCompactSpace Y] : LocallyCompac
tSpace (X × Y)
参数：X : Type*；Y : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_nhds'`：Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {
pX : ιX -> Prop} {pY : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {p : X 
× Y} (hx : (𝓝 p.…
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `LocallyCompactSpace.of_hasBasis`：LocallyCompactSpace.of_hasBasis {ι : X 
-> Type*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X} (h : forall x
, (𝓝 x).HasBasis (p x…
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
-/
instance Prod.locallyCompactSpace (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    LocallyCompactSpace (X × Y) :=
  have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

section Pi

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, LocallyCompactSpace (X i)]

/-- In general it suffices that all but finitely many of the spaces are compact,
  but that's not straightforward to state and use. -/
/-
**Pi.locallyCompactSpace_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (forall 
i, X i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_pi_mem_nhds_iff`：set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s 
: forall i, Set (A i)} (a : forall i, A i) : I.pi s in 𝓝 a ↔ forall i : ι, i in 
I -> s i …
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `trivial`：True
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
In general it suffices that all but finitely many of the spaces are compact,
  but that's not straightforward to state and use.
-/
instance Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (∀ i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨(Set.univ : Set ι).pi n'', ?_, subset_trans (fun _ h => ?_) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩

/-- For spaces that are not Hausdorff. -/
/-
**Pi.locallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.locallyCompactSpace [forall i, CompactSpace (X i)] : LocallyCompactSpac
e (forall i, X i)
参数：X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_pi_mem_nhds_iff`：set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s 
: forall i, Set (A i)} (a : forall i, A i) : I.pi s in 𝓝 a ↔ forall i : ι, i in 
I -> s i …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_ite`：univ_pi_ite (s : Set ι) [DecidablePred (· in s)] (t : f
orall i, Set (α i)) : (pi univ fun i => if i in s then t i else univ) = s.pi t
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
For spaces that are not Hausdorff.
-/
instance Pi.locallyCompactSpace [∀ i, CompactSpace (X i)] : LocallyCompactSpace (∀ i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨s.pi n'', ?_, subset_trans (fun _ => ?_) hsub, ?_⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · classical
      rw [← Set.univ_pi_ite]
      refine isCompact_univ_pi fun i => ?_
      by_cases h : i ∈ s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩
/-
**Function.locallyCompactSpace_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace Y] 
: LocallyCompactSpace (ι -> Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace_of_finite
/-
**Function.locallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.locallyCompactSpace [LocallyCompactSpace Y] [CompactSpace Y] : Lo
callyCompactSpace (ι -> Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.locallyCompactSpace [LocallyCompactSpace Y] [CompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace

end Pi

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [LocallyCompactSpace X] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨K, hKx, hKs, hKc⟩ := local_compact_nhds (hf.continuousAt hs); ⟨K, hKx, hKc, hKs⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [LocallyCompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds (x : X) :=
    let ⟨K, hx, _, hKc⟩ := local_compact_nhds (x := x) univ_mem; ⟨K, hKc, hx⟩

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
/-
**exists_compact_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_compact_subset [LocallyCompactSpace X] {x : X} {U : Set X} (hU : Is
Open U) (hx : x in U) : exists K : Set X, IsCompact K ∧ x in interior K ∧ K subs
eteq U
参数：hU : IsOpen U；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x

--- 原说明 ---
A reformulation of the definition of locally compact space: In a locally compact
 space,
  every open set containing `x` has a compact subset containing `x` in its inter
ior.
-/
theorem exists_compact_subset [LocallyCompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x ∈ U) : ∃ K : Set X, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

/-- If `f : X → Y` is a continuous map in a locally compact pair of topological spaces,
`K : set X` is a compact set, and `U` is an open neighbourhood of `f '' K`,
then there exists a compact neighbourhood `L` of `K` such that `f` maps `L` to `U`.

This is a generalization of `exists_mem_nhds_isCompact_mapsTo`. -/
/-
**exists_mem_nhdsSet_isCompact_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_mem_nhdsSet_isCompact_mapsTo [LocallyCompactPair X Y] {f : X -> Y} 
{K : Set X} {U : Set Y} (hf : Continuous f) (hK : IsCompact K) (hU : IsOpen U) (
hKU : MapsTo f K U) : exists L in 𝓝ˢ K, IsCompact L ∧ MapsTo f L U
参数：hf : Continuous f；hK : IsCompact K；hU : IsOpen U；hKU : MapsTo f K U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.elim_nhds_subcover_nhdsSet`：IsCompact.elim_nhds_subcover_nhdsS
et (hs : IsCompact s) {U : X -> Set X} (hU : forall x in s, U x in 𝓝 x) : exists
 t : Finset X, (forall x i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.isCompact_biUnion`：Finset.isCompact_biUnion (s : Finset ι) {f : ι
 -> Set X} (hf : forall i in s, IsCompact (f i)) : IsCompact (⋃ i in s, f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iUnion₂`：mapsTo_iUnion₂ {s : forall i, κ i -> Set α} {t : Set
 β} {f : α -> β} : MapsTo f (⋃ (i) (j), s i j) t ↔ forall i j, MapsTo f (s i j) 
t
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LocallyCompactPair.exists_mem_nhds_isCompact_mapsTo`：∀ {X : Type u_3} {Y
 : Type u_4} {inst : TopologicalSpace X} {inst_1 : TopologicalSpace Y}   [self :
 LocallyCompactPair X Y] {f : X → Y} {x :…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `f : X → Y` is a continuous map in a locally compact pair of topological spac
es,
`K : set X` is a compact set, and `U` is an open neighbourhood of `f '' K`,
then there exists a compact neighbourhood `L` of `K` such that `f` maps `L` to `
U`.

This is a generalization of `exists_mem_nhds_isCompact_mapsTo`.
-/
lemma exists_mem_nhdsSet_isCompact_mapsTo [LocallyCompactPair X Y] {f : X → Y} {K : Set X}
    {U : Set Y} (hf : Continuous f) (hK : IsCompact K) (hU : IsOpen U) (hKU : MapsTo f K U) :
    ∃ L ∈ 𝓝ˢ K, IsCompact L ∧ MapsTo f L U := by
  choose! V hxV hVc hVU using fun x (hx : x ∈ K) ↦
    exists_mem_nhds_isCompact_mapsTo hf (hU.mem_nhds (hKU hx))
  rcases hK.elim_nhds_subcover_nhdsSet hxV with ⟨s, hsK, hKs⟩
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx ↦ hVc x (hsK x hx), mapsTo_iUnion₂.2 fun x hx ↦
    hVU x (hsK x hx)⟩

/-- In a locally compact space, for every containment `K ⊆ U` of a compact set `K` in an open
  set `U`, there is a compact neighborhood `L` such that `K ⊆ L ⊆ U`: equivalently, there is a
  compact `L` such that `K ⊆ interior L` and `L ⊆ U`.
  See also `exists_compact_closed_between`, in which one guarantees additionally that `L` is closed
  if the space is regular. -/
/-
**exists_compact_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_compact_between [LocallyCompactSpace X] {K U : Set X} (hK : IsCompa
ct K) (hU : IsOpen U) (h_KU : K subseteq U) : exists L, IsCompact L ∧ K subseteq
 interior L ∧ L subseteq U
参数：hK : IsCompact K；hU : IsOpen U；h_KU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_mem_nhdsSet_isCompact_mapsTo`：exists_mem_nhdsSet_isCompact_mapsTo
 [LocallyCompactPair X Y] {f : X -> Y} {K : Set X} {U : Set Y} (hf : Continuous 
f) (hK : IsCompact K) (hU…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s

--- 原说明 ---
In a locally compact space, for every containment `K ⊆ U` of a compact set `K` i
n an open
  set `U`, there is a compact neighborhood `L` such that `K ⊆ L ⊆ U`: equivalent
ly, there is a
  compact `L` such that `K ⊆ interior L` and `L ⊆ U`.
  See also `exists_compact_closed_between`, in which one guarantees additionally
 that `L` is closed
  if the space is regular.
-/
theorem exists_compact_between [LocallyCompactSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (h_KU : K ⊆ U) : ∃ L, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U :=
  let ⟨L, hKL, hL, hLU⟩ := exists_mem_nhdsSet_isCompact_mapsTo continuous_id hK hU h_KU
  ⟨L, hL, subset_interior_iff_mem_nhdsSet.2 hKL, hLU⟩

/-- In a (possibly non-Hausdorff) locally compact space, for every compact set `K`,
`𝓝ˢ K` has a basis consisting of compact sets. -/
/-
**IsCompact.nhdsSet_basis_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_basis_isCompact [LocallyCompactSpace X] {K : Set X} (hK 
: IsCompact K) : (𝓝ˢ K).HasBasis (fun L => L in 𝓝ˢ K ∧ IsCompact L) id
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `exists_compact_between`：exists_compact_between [LocallyCompactSpace X] {
K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K subseteq U) : exists L
, IsCompact …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s

--- 原说明 ---
In a (possibly non-Hausdorff) locally compact space, for every compact set `K`,
`𝓝ˢ K` has a basis consisting of compact sets.
-/
theorem IsCompact.nhdsSet_basis_isCompact [LocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun L ↦ L ∈ 𝓝ˢ K ∧ IsCompact L) id := by
  rw [hasBasis_self, (hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], hL, hLU⟩
/-
**IsOpenQuotientMap.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenQuotientMap.locallyCompactSpace [LocallyCompactSpace X] {f : X -> Y}
 (hf : IsOpenQuotientMap f) : LocallyCompactSpace Y where local_compact_nhds
参数：hf : IsOpenQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `local_compact_nhds`：local_compact_nhds [LocallyCompactSpace X] {x : X} {
n : Set X} (h : n in 𝓝 x) : exists s in 𝓝 x, s subseteq n ∧ IsCompact s
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
theorem IsOpenQuotientMap.locallyCompactSpace [LocallyCompactSpace X] {f : X → Y}
    (hf : IsOpenQuotientMap f) : LocallyCompactSpace Y where
  local_compact_nhds := by
    refine hf.surjective.forall.2 fun x U hU ↦ ?_
    rcases local_compact_nhds (hf.continuous.continuousAt hU) with ⟨K, hKx, hKU, hKc⟩
    exact ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, image_subset_iff.2 hKU, hKc.image hf.continuous⟩

/-- If `f` is a topology inducing map with a locally compact codomain and a locally closed range,
then the domain of `f` is a locally compact space. -/
/-
**Topology.IsInducing.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.locallyCompactSpace [LocallyCompactSpace Y] {f : X -> 
Y} (hf : IsInducing f) (h : IsLocallyClosed (range f)) : LocallyCompactSpace X
参数：hf : IsInducing f；h : IsLocallyClosed (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_nhdsWithin_range`：∀ {α : Type u_5} {β : Type u_6} [inst : Topologi
calSpace β] (f : α → β) (y : β),   Filter.comap f (nhdsWithin y (Set.range f)) =
 Filter.coma…
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `LocallyCompactSpace.of_hasBasis`：LocallyCompactSpace.of_hasBasis {ι : X 
-> Type*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X} (h : forall x
, (𝓝 x).HasBasis (p x…
· 使用引理 `Topology.IsInducing.isCompact_preimage_iff`：Topology.IsInducing.isCompac
t_preimage_iff {f : X -> Y} (hf : IsInducing f) {K : Set Y} (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K) ↔ Is…
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)

--- 原说明 ---
If `f` is a topology inducing map with a locally compact codomain and a locally 
closed range,
then the domain of `f` is a locally compact space.
-/
theorem Topology.IsInducing.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsInducing f) (h : IsLocallyClosed (range f)) : LocallyCompactSpace X := by
  rcases h with ⟨U, Z, hU, hZ, hUZ⟩
  have (x : X) : (𝓝 x).HasBasis (fun s ↦ (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ U)
      (fun s ↦ f ⁻¹' (s ∩ Z)) := by
    have H : U ∈ 𝓝 (f x) := hU.mem_nhds (hUZ.subset <| mem_range_self _).1
    rw [hf.nhds_eq_comap, ← comap_nhdsWithin_range, hUZ,
      nhdsWithin_inter_of_mem (nhdsWithin_le_nhds H)]
    exact (nhdsWithin_hasBasis ((compact_basis_nhds (f x)).restrict_subset H) _).comap _
  refine .of_hasBasis this fun x s ⟨⟨_, hs⟩, hsU⟩ ↦ ?_
  rw [hf.isCompact_preimage_iff]
  exacts [hs.inter_right hZ, hUZ ▸ by gcongr]
/-
**Topology.IsClosedEmbedding.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [LocallyCompactSpace Y]   {f : X → Y}, Topology.IsClosedEmbeddin
g f → LocallyCompactSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.locallyCompactSpace`：Topology.IsInducing.locallyComp
actSpace [LocallyCompactSpace Y] {f : X -> Y} (hf : IsInducing f) (h : IsLocally
Closed (range f)) : LocallyCo…
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
protected theorem Topology.IsClosedEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed
/-
**Topology.IsOpenEmbedding.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.IsOpenEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [LocallyCompactSpace Y]   {f : X → Y}, Topology.IsOpenEmbedding 
f → LocallyCompactSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.locallyCompactSpace`：Topology.IsInducing.locallyComp
actSpace [LocallyCompactSpace Y] {f : X -> Y} (hf : IsInducing f) (h : IsLocally
Closed (range f)) : LocallyCo…
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
protected theorem Topology.IsOpenEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsOpenEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isOpen_range.isLocallyClosed
/-
**IsLocallyClosed.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyClosed
`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyCompactSpace X] {s : 
Set X},   IsLocallyClosed s → LocallyCompactSpace ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.locallyCompactSpace`：Topology.IsInducing.locallyComp
actSpace [LocallyCompactSpace Y] {f : X -> Y} (hf : IsInducing f) (h : IsLocally
Closed (range f)) : LocallyCo…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
protected theorem IsLocallyClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsLocallyClosed s) : LocallyCompactSpace s :=
  IsEmbedding.subtypeVal.locallyCompactSpace <| by rwa [Subtype.range_val]
/-
**IsClosed.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyCompactSpace X] {s : 
Set X}, IsClosed s → LocallyCompactSpace ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyClosed.locallyCompactSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [LocallyCompactSpace X] {s : Set X},   IsLocallyClosed s → LocallyComp
actSpace ↑s
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
-/
protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace
/-
**IsOpen.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyCompactSpace X] {s : 
Set X}, IsOpen s → LocallyCompactSpace ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyClosed.locallyCompactSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [LocallyCompactSpace X] {s : Set X},   IsLocallyClosed s → LocallyComp
actSpace ↑s
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
-/
protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace X] {s : Set X} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace
