/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets in uniform spaces

* `compactSpace_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

-/

public section

universe u v ua ub uc ud

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

section Compact

open Uniformity Set Filter UniformSpace
open scoped SetRel Topology

variable [UniformSpace α] {K : Set α}

/-- Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
/-
**lebesgue_number_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α} (hK : IsCompact K) (hop
en : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, U i) : exists V in 𝓤 α, f
orall x in K, exists i, ball x V subseteq U i
参数：hK : IsCompact K；hopen : forall i, IsOpen (U i)；hcover : K subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Monotone.relComp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {ι : Ty
pe u_6} [inst : Preorder ι] {f : ι → SetRel α β}   {g : ι → SetRel β γ}, Monoton
e f → …
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lift'_comp_uniformity`：∀ {α : Type ua} [inst : UniformSpace α], ((unifor
mity α).lift' fun s => s.comp s) = uniformity α
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsCompact.elim_nhds_subcover'`：IsCompact.elim_nhds_subcover' (hs : IsCom
pact s) (U : forall x in s, Set X) (hU : forall x (hx : x in s), U x ‹x in s› in
 𝓝 x) : exists t : …
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an 
entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`.
-/
theorem lebesgue_number_lemma {ι : Sort*} {U : ι → Set α} (hK : IsCompact K)
    (hopen : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ i, ball x V ⊆ U i := by
  have : ∀ x ∈ K, ∃ i, ∃ V ∈ 𝓤 α, ball x (V ○ V) ⊆ U i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff, nhds_eq_comap_uniformity, ← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.relComp monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx ↦ ball x (W x hx)) (fun x hx ↦ ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x ∈ t, W x x.2, (biInter_finset_mem _).2 fun x _ ↦ hW x x.2, fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz ↦ hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩
/-
**lebesgue_number_lemma_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_nhds' {U : (x : α) -> x in K -> Set α} (hK : IsCompa
ct K) (hU : forall x hx, U x hx in 𝓝 x) : exists V in 𝓤 α, forall x in K, exists
 y : K, ball x V subseteq U y y.2
参数：x : α；hK : IsCompact K；hU : forall x hx, U x hx in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `lebesgue_number_lemma`：lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α
} (hK : IsCompact K) (hopen : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, 
U i) : exis…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem lebesgue_number_lemma_nhds' {U : (x : α) → x ∈ K → Set α} (hK : IsCompact K)
    (hU : ∀ x hx, U x hx ∈ 𝓝 x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y : K, ball x V ⊆ U y y.2 := by
  rcases lebesgue_number_lemma (U := fun x : K => interior (U x x.2)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩
/-
**lebesgue_number_lemma_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_nhds {U : α -> Set α} (hK : IsCompact K) (hU : foral
l x in K, U x in 𝓝 x) : exists V in 𝓤 α, forall x in K, exists y, ball x V subse
teq U y
参数：hK : IsCompact K；hU : forall x in K, U x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lebesgue_number_lemma`：lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α
} (hK : IsCompact K) (hopen : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, 
U i) : exis…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem lebesgue_number_lemma_nhds {U : α → Set α} (hK : IsCompact K) (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y, ball x V ⊆ U y := by
  rcases lebesgue_number_lemma (U := fun x => interior (U x)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩
/-
**lebesgue_number_lemma_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_nhdsWithin' {U : (x : α) -> x in K -> Set α} (hK : I
sCompact K) (hU : forall x hx, U x hx in 𝓝[K] x) : exists V in 𝓤 α, forall x in 
K, exists y : K, ball x V inter K subseteq U y y.2
参数：x : α；hK : IsCompact K；hU : forall x hx, U x hx in 𝓝[K] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_subset`：inter_subset (a b c : Set α) : a inter b subseteq c ↔ 
a subseteq bᶜ union c
· 使用定理 `lebesgue_number_lemma_nhds'`：lebesgue_number_lemma_nhds' {U : (x : α) ->
 x in K -> Set α} (hK : IsCompact K) (hU : forall x hx, U x hx in 𝓝 x) : exists 
V in 𝓤 α, forall …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_inf_principal'`：mem_inf_principal' {f : Filter α} {s t : Set 
α} : s in f ⊓ 𝓟 t ↔ tᶜ union s in f
-/
theorem lebesgue_number_lemma_nhdsWithin' {U : (x : α) → x ∈ K → Set α} (hK : IsCompact K)
    (hU : ∀ x hx, U x hx ∈ 𝓝[K] x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y : K, ball x V ∩ K ⊆ U y y.2 :=
  (lebesgue_number_lemma_nhds' hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩
/-
**lebesgue_number_lemma_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_nhdsWithin {U : α -> Set α} (hK : IsCompact K) (hU :
 forall x in K, U x in 𝓝[K] x) : exists V in 𝓤 α, forall x in K, exists y, ball 
x V inter K subseteq U y
参数：hK : IsCompact K；hU : forall x in K, U x in 𝓝[K] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_subset`：inter_subset (a b c : Set α) : a inter b subseteq c ↔ 
a subseteq bᶜ union c
· 使用定理 `lebesgue_number_lemma_nhds`：lebesgue_number_lemma_nhds {U : α -> Set α} 
(hK : IsCompact K) (hU : forall x in K, U x in 𝓝 x) : exists V in 𝓤 α, forall x 
in K, exists y, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_inf_principal'`：mem_inf_principal' {f : Filter α} {s t : Set 
α} : s in f ⊓ 𝓟 t ↔ tᶜ union s in f
-/
theorem lebesgue_number_lemma_nhdsWithin {U : α → Set α} (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝[K] x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y, ball x V ∩ K ⊆ U y :=
  (lebesgue_number_lemma_nhds hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

/-- Let `U : ι → Set α` be an open cover of a compact set `K`.
Then there exists an entourage `V`
such that for each `x ∈ K` its `V`-neighborhood is included in some `U i`.

Moreover, one can choose an entourage from a given basis. -/
/-
**Filter.HasBasis.lebesgue_number_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBas
is`。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α] {K : Set α} {ι' : Sort u_2} {ι : S
ort u_3} {p : ι' → Prop}   {V : ι' → Set (α × α)} {U : ι → Set α},   (uniformity
 α).HasBasis p V →     IsCompact K → (∀ (j : ι), IsOpen (U j)) → K ⊆ ⋃ j, U j → 
∃ i, p i ∧ ∀ x ∈ K, ∃ j, UniformSpace.ball x (V i) ⊆ U j
参数：α × α；uniformity α；∀ (j : ι), IsOpen (U j)；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `lebesgue_number_lemma`：lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α
} (hK : IsCompact K) (hopen : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, 
U i) : exis…

--- 原说明 ---
Let `U : ι → Set α` be an open cover of a compact set `K`.
Then there exists an entourage `V`
such that for each `x ∈ K` its `V`-neighborhood is included in some `U i`.

Moreover, one can choose an entourage from a given basis.
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma {ι' ι : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : ι → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hopen : ∀ j, IsOpen (U j)) (hcover : K ⊆ ⋃ j, U j) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ j, ball x (V i) ⊆ U j := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun i hi ↦ Subset.trans (ball_mono hst _) hi
/-
**Filter.HasBasis.lebesgue_number_lemma_nhds'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.
HasBasis`。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι
' → Prop} {V : ι' → Set (α × α)}   {U : (x : α) → x ∈ K → Set α},   (uniformity 
α).HasBasis p V →     IsCompact K →       (∀ (x : α) (hx : x ∈ K), U x hx ∈ nhds
 x) → ∃ i, p i ∧ ∀ x ∈ K, ∃ y, UniformSpace.ball x (V i) ⊆ U ↑y ⋯
参数：α × α；x : α；uniformity α；∀ (x : α) (hx : x ∈ K), U x hx ∈ nhds x；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `lebesgue_number_lemma_nhds'`：lebesgue_number_lemma_nhds' {U : (x : α) ->
 x in K -> Set α} (hK : IsCompact K) (hU : forall x hx, U x hx in 𝓝 x) : exists 
V in 𝓤 α, forall …
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds' {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : (x : α) → x ∈ K → Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : ∀ x hx, U x hx ∈ 𝓝 x) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ y : K, ball x (V i) ⊆ U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds' hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun y hy ↦ Subset.trans (ball_mono hst _) hy
/-
**Filter.HasBasis.lebesgue_number_lemma_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Filter.H
asBasis`。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι
' → Prop} {V : ι' → Set (α × α)}   {U : α → Set α},   (uniformity α).HasBasis p 
V →     IsCompact K → (∀ x ∈ K, U x ∈ nhds x) → ∃ i, p i ∧ ∀ x ∈ K, ∃ y, Uniform
Space.ball x (V i) ⊆ U y
参数：α × α；uniformity α；∀ x ∈ K, U x ∈ nhds x；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `lebesgue_number_lemma_nhds`：lebesgue_number_lemma_nhds {U : α -> Set α} 
(hK : IsCompact K) (hU : forall x in K, U x in 𝓝 x) : exists V in 𝓤 α, forall x 
in K, exists y, …
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : α → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝 x) : ∃ i, p i ∧ ∀ x ∈ K, ∃ y, ball x (V i) ⊆ U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun y hy ↦ Subset.trans (ball_mono hst _) hy
/-
**Filter.HasBasis.lebesgue_number_lemma_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 `F
ilter.HasBasis`。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι
' → Prop} {V : ι' → Set (α × α)}   {U : (x : α) → x ∈ K → Set α},   (uniformity 
α).HasBasis p V →     IsCompact K →       (∀ (x : α) (hx : x ∈ K), U x hx ∈ nhds
Within x K) →         ∃ i, p i ∧ ∀ x ∈ K, ∃ y, UniformSpace.ball x (V i) ∩ K ⊆ U
 ↑y ⋯
参数：α × α；x : α；uniformity α；∀ (x : α) (hx : x ∈ K), U x hx ∈ nhdsWithin x K；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `lebesgue_number_lemma_nhdsWithin'`：lebesgue_number_lemma_nhdsWithin' {U 
: (x : α) -> x in K -> Set α} (hK : IsCompact K) (hU : forall x hx, U x hx in 𝓝[
K] x) : exists V in 𝓤 α…
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin' {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : (x : α) → x ∈ K → Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : ∀ x hx, U x hx ∈ 𝓝[K] x) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ y : K, ball x (V i) ∩ K ⊆ U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin' hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp
    fun y hy ↦ Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy
/-
**Filter.HasBasis.lebesgue_number_lemma_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter.HasBasis`。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι
' → Prop} {V : ι' → Set (α × α)}   {U : α → Set α},   (uniformity α).HasBasis p 
V →     IsCompact K → (∀ x ∈ K, U x ∈ nhdsWithin x K) → ∃ i, p i ∧ ∀ x ∈ K, ∃ y,
 UniformSpace.ball x (V i) ∩ K ⊆ U y
参数：α × α；uniformity α；∀ x ∈ K, U x ∈ nhdsWithin x K；V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `lebesgue_number_lemma_nhdsWithin`：lebesgue_number_lemma_nhdsWithin {U : 
α -> Set α} (hK : IsCompact K) (hU : forall x in K, U x in 𝓝[K] x) : exists V in
 𝓤 α, forall x in K, e…
-/
protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : α → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝[K] x) : ∃ i, p i ∧ ∀ x ∈ K, ∃ y, ball x (V i) ∩ K ⊆ U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp
    fun y hy ↦ Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

/-- Let `c : Set (Set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
/-
**lebesgue_number_lemma_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_sUnion {S : Set (Set α)} (hK : IsCompact K) (hopen :
 forall s in S, IsOpen s) (hcover : K subseteq ⋃₀ S) : exists V in 𝓤 α, forall x
 in K, exists s in S, ball x V subseteq s
参数：Set α；hK : IsCompact K；hopen : forall s in S, IsOpen s；hcover : K subseteq ⋃₀
 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `lebesgue_number_lemma`：lebesgue_number_lemma {ι : Sort*} {U : ι -> Set α
} (hK : IsCompact K) (hopen : forall i, IsOpen (U i)) (hcover : K subseteq ⋃ i, 
U i) : exis…
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i

--- 原说明 ---
Let `c : Set (Set α)` be an open cover of a compact set `s`. Then there exists a
n entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`
.
-/
theorem lebesgue_number_lemma_sUnion {S : Set (Set α)}
    (hK : IsCompact K) (hopen : ∀ s ∈ S, IsOpen s) (hcover : K ⊆ ⋃₀ S) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ s ∈ S, ball x V ⊆ s := by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

/-- If `K` is a compact set in a uniform space and `{V i | p i}` is a basis of entourages,
then `{⋃ x ∈ K, UniformSpace.ball x (V i) | p i}` is a basis of `𝓝ˢ K`.

Here "`{s i | p i}` is a basis of a filter `l`" means `Filter.HasBasis l p s`. -/
/-
**IsCompact.nhdsSet_basis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_basis_uniformity {p : ι -> Prop} {V : ι -> Set (α × α)} 
(hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) : (𝓝ˢ K).HasBasis p fun i => ⋃ 
x in K, ball x (V i) where mem_iff' U
参数：α × α；hbasis : (𝓤 α).HasBasis p V；hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma`：∀ {α : Type ua} [inst : UniformSp
ace α] {K : Set α} {ι' : Sort u_2} {ι : Sort u_3} {p : ι' → Prop}   {V : ι' → Se
t (α × α)} {U : ι → Set α},…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `bUnion_mem_nhdsSet`：bUnion_mem_nhdsSet {t : X -> Set X} (h : forall x in
 s, t x in 𝓝 x) : (⋃ x in s, t x) in 𝓝ˢ s
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l

--- 原说明 ---
If `K` is a compact set in a uniform space and `{V i | p i}` is a basis of entou
rages,
then `{⋃ x ∈ K, UniformSpace.ball x (V i) | p i}` is a basis of `𝓝ˢ K`.

Here "`{s i | p i}` is a basis of a filter `l`" means `Filter.HasBasis l p s`.
-/
theorem IsCompact.nhdsSet_basis_uniformity {p : ι → Prop} {V : ι → Set (α × α)}
    (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (V i) where
  mem_iff' U := by
    constructor
    · intro H
      have HKU : K ⊆ ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : ∃ i, p i ∧ ⋃ x ∈ K, ball x (V i) ⊆ interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ ↦ isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ ↦ ?_) hi
      exact ball_mem_nhds _ <| hbasis.mem_of_mem hpi

-- TODO: move to a separate file, golf using the regularity of a uniform space.
/-
**Disjoint.exists_uniform_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : 
IsClosed B) (h : Disjoint A B) : exists V in 𝓤 α, Disjoint (⋃ x in A, ball x V) 
(⋃ x in B, ball x V)
参数：hA : IsCompact A；hB : IsClosed B；h : Disjoint A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Disjoint.le_compl_right`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b
 : α}, Disjoint a b → a ≤ bᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_uniformity`：IsCompact.nhdsSet_basis_uniformity {
p : ι -> Prop} {V : ι -> Set (α × α)} (hbasis : (𝓤 α).HasBasis p V) (hK : IsComp
act K) : (𝓝ˢ K).HasBasis…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `UniformSpace.mem_comp_of_mem_ball`：mem_comp_of_mem_ball {V W : SetRel β 
β} {x y z : β} [V.IsSymm] (hx : x in ball z V) (hy : y in ball z W) : (x, y) in 
V ○ W
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
-/
theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) := by
  have : Bᶜ ∈ 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hxa hxb) hb
/-
**Disjoint.exists_uniform_thickening_of_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.exists_uniform_thickening_of_basis {p : ι -> Prop} {s : ι -> Set 
(α × α)} (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClos
ed B) (h : Disjoint A B) : exists i, p i ∧ Disjoint (⋃ x in A, ball x (s i)) (⋃ 
x in B, ball x (s i))
参数：α × α；hU : (𝓤 α).HasBasis p s；hA : IsCompact A；hB : IsClosed B；h : Disjoint A
 B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.exists_uniform_thickening`：Disjoint.exists_uniform_thickening {
A B : Set α} (hA : IsCompact A) (hB : IsClosed B) (h : Disjoint A B) : exists V 
in 𝓤 α, Disjoint (⋃ x in…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
-/
theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
/-
**lebesgue_number_of_compact_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K) (hU : IsO
pen U) (hKU : K subseteq U) : exists V in 𝓤 α, IsOpen V ∧ forall x in K, Uniform
Space.ball x V subseteq U
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_uniformity`：IsCompact.nhdsSet_basis_uniformity {
p : ι -> Prop} {V : ι -> Set (α × α)} (hbasis : (𝓤 α).HasBasis p V) (hK : IsComp
act K) : (𝓝ˢ K).HasBasis…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t

--- 原说明 ---
A useful consequence of the Lebesgue number lemma: given any compact set `K` con
tained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V`
 about any point of
`K` is contained in `U`.
-/
theorem lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U :=
  let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩


/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
/-
**nhdsSet_diagonal_eq_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `nhdsSet_diagonal_le_uniformity`：nhdsSet_diagonal_le_uniformity : 𝓝ˢ (dia
gonal α) <= 𝓤 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_prod_eq_comap_prod`：uniformity_prod_eq_comap_prod [UniformSpa
ce α] [UniformSpace β] : 𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, 
p.2.1), (p.1.2, p.2…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `IsCompact.nhdsSet_basis_uniformity`：IsCompact.nhdsSet_basis_uniformity {
p : ι -> Prop} {V : ι -> Set (α × α)} (hbasis : (𝓤 α).HasBasis p V) (hK : IsComp
act K) : (𝓝ˢ K).HasBasis…
· 使用定理 `isCompact_diagonal`：isCompact_diagonal [CompactSpace X] : IsCompact (dia
gonal X)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s

--- 原说明 ---
On a compact uniform space, the topology determines the uniform structure, entou
rages are
exactly the neighborhoods of the diagonal.
-/
theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α := by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U ∈ 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
/-
**compactSpace_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_diagonal_eq_uniformity`：nhdsSet_diagonal_eq_uniformity [CompactS
pace α] : 𝓝ˢ (diagonal α) = 𝓤 α
· 使用定理 `nhdsSet_diagonal`：nhdsSet_diagonal (X) [TopologicalSpace (X × X)] : 𝓝ˢ (
diagonal X) = ⨆ (x : X), 𝓝 (x, x)

--- 原说明 ---
On a compact uniform space, the topology determines the uniform structure, entou
rages are
exactly the neighborhoods of the diagonal.
-/
theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)
/-
**unique_uniformity_of_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ] {u 
u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace 
= t) : u = u'
参数：h : u.toTopologicalSpace = t；h' : u'.toTopologicalSpace = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compactSpace_uniformity`：compactSpace_uniformity [CompactSpace α] : 𝓤 α 
= ⨆ x, 𝓝 (x, x)
-/
theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u, compactSpace_uniformity, h, h']

end Compact

/-
**IsClosed.relPreimage_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.relPreimage_of_isCompact [TopologicalSpace α] [TopologicalSpace β
] {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : IsCompact t) : IsClosed (
s.preimage t)
参数：hs : IsClosed s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_eventually`：isOpen_iff_eventually : IsOpen s ↔ forall x, x in
 s -> forallᶠ y in 𝓝 x, y in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.eventually_forall_of_forall_eventually`：IsCompact.eventually_f
orall_of_forall_eventually {x₀ : X} {K : Set Y} (hK : IsCompact K) {P : X -> Y -
> Prop} (hP : forall y in K, forallᶠ z…
-/
theorem IsClosed.relPreimage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : IsCompact t) :
    IsClosed (s.preimage t) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually] at hs ⊢
  simp_rw [Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
  exact fun y hy => ht.eventually_forall_of_forall_eventually fun x hx => hs _ <| hy _ hx
/-
**IsClosed.relImage_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.relImage_of_isCompact [TopologicalSpace α] [TopologicalSpace β] {
s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : IsCompact t) : IsClosed (s.i
mage t)
参数：hs : IsClosed s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.relPreimage_of_isCompact`：IsClosed.relPreimage_of_isCompact [To
pologicalSpace α] [TopologicalSpace β] {s : SetRel α β} (hs : IsClosed s) {t : S
et β} (ht : IsCompact t…
· 使用引理 `IsClosed.relInv`：IsClosed.relInv [TopologicalSpace α] [TopologicalSpace 
β] {s : SetRel α β} (hs : IsClosed s) : IsClosed s.inv
-/
theorem IsClosed.relImage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : IsCompact t) :
    IsClosed (s.image t) :=
  hs.relInv.relPreimage_of_isCompact ht
