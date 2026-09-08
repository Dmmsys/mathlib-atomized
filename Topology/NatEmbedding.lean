/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Infinite Hausdorff topological spaces

In this file we prove several properties of infinite Hausdorff topological spaces.

- `exists_seq_infinite_isOpen_pairwise_disjoint`: there exists a sequence
  of pairwise disjoint infinite open sets;
- `exists_topology_isEmbedding_nat`: there exists a topological embedding of `ℕ` into the space;
- `exists_infinite_discreteTopology`: there exists an infinite subset with discrete topology.
-/

public section

open Function Filter Set Topology

variable (X : Type*) [TopologicalSpace X] [T2Space X] [Infinite X]

/-- In an infinite Hausdorff topological space, there exists a sequence of pairwise disjoint
infinite open sets. -/
/-
**exists_seq_infinite_isOpen_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_infinite_isOpen_pairwise_disjoint : exists U : Nat -> Set X, (f
orall n, (U n).Infinite) ∧ (forall n, IsOpen (U n)) ∧ Pairwise (Disjoint on U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `exists_seq_of_forall_finset_exists'`：exists_seq_of_forall_finset_exists'
 {α : Type*} (P : α -> Prop) (r : α -> α -> Prop) [Std.Symm r] (h : forall s : F
inset α, (forall x in s, …
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `interior_mem_nhds`：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_biInter_finset`：isOpen_biInter_finset {s : Finset α} {f : α -> Se
t X} (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, f i)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.infinite_iUnion`：infinite_iUnion {ι : Type*} [Infinite ι] {s : ι -> 
Set α} (hs : Function.Injective s) : (⋃ i, s i).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r →
 ¬r a b → a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
In an infinite Hausdorff topological space, there exists a sequence of pairwise 
disjoint
infinite open sets.
-/
theorem exists_seq_infinite_isOpen_pairwise_disjoint :
    ∃ U : ℕ → Set X, (∀ n, (U n).Infinite) ∧ (∀ n, IsOpen (U n)) ∧ Pairwise (Disjoint on U) := by
  suffices ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty) ∧ (∀ n, IsOpen (U n)) ∧
      Pairwise (Disjoint on U) by
    rcases this with ⟨U, hne, ho, hd⟩
    refine ⟨fun n ↦ ⋃ m, U (.pair n m), ?_, fun _ ↦ isOpen_iUnion fun _ ↦ ho _, ?_⟩
    · refine fun n ↦ infinite_iUnion fun i j hij ↦ ?_
      suffices n.pair i = n.pair j by simpa
      apply hd.eq
      simpa [hij, onFun] using (hne _).ne_empty
    · refine fun n n' hne ↦ disjoint_iUnion_left.2 fun m ↦ disjoint_iUnion_right.2 fun m' ↦ hd ?_
      simp [hne]
  by_cases h : DiscreteTopology X
  · refine ⟨fun n ↦ {Infinite.natEmbedding X n}, fun _ ↦ singleton_nonempty _,
      fun _ ↦ isOpen_discrete _, fun _ _ h ↦ ?_⟩
    simpa using h
  · simp only [discreteTopology_iff_nhds_ne, not_forall, ← ne_eq, ← neBot_iff] at h
    rcases h with ⟨x, hx⟩
    suffices ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty ∧ IsOpen (U n) ∧ (U n)ᶜ ∈ 𝓝 x) ∧
        Pairwise (Disjoint on U) by
      rcases this with ⟨U, hU, hd⟩
      exact ⟨U, fun n ↦ (hU n).1, fun n ↦ (hU n).2.1, hd⟩
    have : Std.Symm (α := Set X) Disjoint := ⟨fun _ _ h ↦ h.symm⟩
    refine exists_seq_of_forall_finset_exists' (fun U : Set X ↦ U.Nonempty ∧ IsOpen U ∧ Uᶜ ∈ 𝓝 x)
      Disjoint fun S hS ↦ ?_
    have : (⋂ U ∈ S, interior (Uᶜ)) \ {x} ∈ 𝓝[≠] x := inter_mem_inf ((biInter_finset_mem _).2
      fun U hU ↦ interior_mem_nhds.2 (hS _ hU).2.2) (mem_principal_self _)
    rcases hx.nonempty_of_mem this with ⟨y, hyU, hyx : y ≠ x⟩
    rcases t2_separation hyx with ⟨V, W, hVo, hWo, hyV, hxW, hVW⟩
    refine ⟨V ∩ ⋂ U ∈ S, interior (Uᶜ), ⟨⟨y, hyV, hyU⟩, ?_, ?_⟩, fun U hU ↦ ?_⟩
    · exact hVo.inter (isOpen_biInter_finset fun _ _ ↦ isOpen_interior)
    · refine mem_of_superset (hWo.mem_nhds hxW) fun z hzW ⟨hzV, _⟩ ↦ ?_
      exact disjoint_left.1 hVW hzV hzW
    · exact disjoint_left.2 fun z hzU ⟨_, hzU'⟩ ↦ interior_subset (mem_iInter₂.1 hzU' U hU) hzU

/-- If `X` is an infinite Hausdorff topological space, then there exists a topological embedding
`f : ℕ → X`.

Note: this theorem is true for an infinite KC-space but the proof in that case is different. -/
/-
**exists_topology_isEmbedding_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_topology_isEmbedding_nat : exists f : Nat -> X, IsEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_infinite_isOpen_pairwise_disjoint`：exists_seq_infinite_isOpen
_pairwise_disjoint : exists U : Nat -> Set X, (forall n, (U n).Infinite) ∧ (fora
ll n, IsOpen (U n)) ∧ Pairwise (Di…
· 使用定理 `Topology.IsInducing.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   To
pology.IsInducing f →…
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_bot_of_singletons_open`：eq_bot_of_singletons_open {t : TopologicalSpa
ce α} (h : forall x, IsOpen[t] {x}) : t = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r →
 ¬r a b → a = b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `X` is an infinite Hausdorff topological space, then there exists a topologic
al embedding
`f : ℕ → X`.

Note: this theorem is true for an infinite KC-space but the proof in that case i
s different.
-/
theorem exists_topology_isEmbedding_nat : ∃ f : ℕ → X, IsEmbedding f := by
  rcases exists_seq_infinite_isOpen_pairwise_disjoint X with ⟨U, hUi, hUo, hd⟩
  choose f hf using fun n ↦ (hUi n).nonempty
  refine ⟨f, IsInducing.isEmbedding ⟨Eq.symm (eq_bot_of_singletons_open fun n ↦ ⟨U n, hUo n, ?_⟩)⟩⟩
  refine eq_singleton_iff_unique_mem.2 ⟨hf _, fun m hm ↦ ?_⟩
  exact hd.eq (not_disjoint_iff.2 ⟨f m, hf _, hm⟩)

/-- If `X` is an infinite Hausdorff topological space, then there exists an infinite set `s : Set X`
that has the induced topology is the discrete topology. -/
/-
**exists_infinite_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_infinite_discreteTopology : exists s : Set X, s.Infinite ∧ Discrete
Topology s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_topology_isEmbedding_nat`：exists_topology_isEmbedding_nat : exist
s f : Nat -> X, IsEmbedding f
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `X` is an infinite Hausdorff topological space, then there exists an infinite
 set `s : Set X`
that has the induced topology is the discrete topology.
-/
theorem exists_infinite_discreteTopology : ∃ s : Set X, s.Infinite ∧ DiscreteTopology s := by
  rcases exists_topology_isEmbedding_nat X with ⟨f, hf⟩
  refine ⟨range f, infinite_range_of_injective hf.injective, ?_⟩
  exact hf.toHomeomorph.symm.isEmbedding.discreteTopology
