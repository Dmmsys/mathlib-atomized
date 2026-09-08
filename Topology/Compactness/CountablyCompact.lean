/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek, Yongxi Lin
-/
module

public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Sequences

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Perfect

/-!
# Countably compact sets

A set `A` in a topological space is **countably compact** if every countably generated proper
filter contained in `A` has a cluster point in `A`. Equivalently, every sequence in `A` has a
cluster point in `A`, and every countable open cover of `A` admits a finite subcover.

## Main definitions

* `IsCountablyCompact A`: `A` is countably compact (every countably generated proper filter
  contained in `A` has a cluster point in `A`).
* `CountablyCompactSpace E`: the whole space `E` is countably compact.

## Main results

* `IsCountablyCompact.elim_directed_cover`: for every countable open directed cover of a
  countably compact set, some single element of the cover contains the set.
* `IsCountablyCompact.elim_finite_subcover`: a countably compact set has a finite subcover for
  any countable open cover.
* `isCountablyCompact_iff_countable_open_cover`: countable compactness is equivalent to the
  finite subcover property for countable covers.
* `IsCompact.isCountablyCompact`: compact sets are countably compact.
* `IsSeqCompact.isCountablyCompact`: sequentially compact sets are countably compact.
* `IsCountablyCompact.isSeqCompact`: in a first-countable space, countable compactness implies
  sequential compactness.
* `IsCountablyCompact.exists_accPt_of_infinite`: every infinite subset of a countably compact
  set has an accumulation point in the set.
* `isCountablyCompact_iff_infinite_subset_has_accPt`: in a T₁ space, countable compactness is
  equivalent to the Bolzano–Weierstrass property (every infinite subset has an accumulation point).
* `IsLindelof.isCompact`: a countably compact Lindelöf set is compact.
* `IsCountablyCompact.image`: the continuous image of a countably compact set is countably compact.

## References

* [Engelking, *General Topology*][engelking1989]
-/

@[expose] public section

noncomputable section

open Set Filter Topology

variable {ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {A B : Set E}

/-- A set `A` is countably compact if every countably generated proper filter `f` with
`f ≤ 𝓟 A` has a cluster point in `A`. -/
/-
**IsCountablyCompact** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCountablyCompact (A : Set E) : Prop
参数：A : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `A` is countably compact if every countably generated proper filter `f` wi
th
`f ≤ 𝓟 A` has a cluster point in `A`.
-/
def IsCountablyCompact (A : Set E) : Prop :=
  ∀ ⦃f⦄ [NeBot f] [f.IsCountablyGenerated], f ≤ 𝓟 A → ∃ a ∈ A, ClusterPt a f

/-- A topological space is countably compact if every countably generated proper filter has a
cluster point. -/
/-
**CountablyCompactSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_4) → [TopologicalSpace E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is countably compact if every countably generated proper fil
ter has a
cluster point.
-/
class CountablyCompactSpace (E : Type*) [TopologicalSpace E] : Prop where
  isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)

/-- The empty set is countably compact. -/
/-
**isCountablyCompact_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_empty : IsCountablyCompact (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥

--- 原说明 ---
The empty set is countably compact.
-/
theorem isCountablyCompact_empty : IsCountablyCompact (∅ : Set E) :=
  fun _f _ _ hle => absurd (empty_mem_iff_bot.mp (le_principal_iff.mp hle)) NeBot.ne'

/-- A singleton set is countably compact. -/
/-
**isCountablyCompact_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_singleton {x : E} : IsCountablyCompact ({x} : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a

--- 原说明 ---
A singleton set is countably compact.
-/
theorem isCountablyCompact_singleton {x : E} : IsCountablyCompact ({x} : Set E) := fun _ _ _ hle ↦
  ⟨x, rfl, ClusterPt.of_le_nhds <| hle.trans (principal_singleton x ▸ pure_le_nhds x)⟩

/-- A closed subset of a countably compact set is countably compact. -/
/-
**IsCountablyCompact.of_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.of_isClosed_subset (hA : IsCountablyCompact A) (hB : Is
Closed B) (hBA : B subseteq A) : IsCountablyCompact B
参数：hA : IsCountablyCompact A；hB : IsClosed B；hBA : B subseteq A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g

--- 原说明 ---
A closed subset of a countably compact set is countably compact.
-/
theorem IsCountablyCompact.of_isClosed_subset (hA : IsCountablyCompact A) (hB : IsClosed B)
    (hBA : B ⊆ A) : IsCountablyCompact B := fun _f _ _ hle ↦
  let ⟨a, _, hac⟩ := hA (hle.trans (principal_mono.mpr hBA))
  ⟨a, isClosed_iff_clusterPt.mp hB a (hac.mono hle), hac⟩

/-- A closed subset of a countably compact space is countably compact. -/
/-
**IsClosed.isCountablyCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isCountablyCompact [CountablyCompactSpace E] (hA : IsClosed A) : 
IsCountablyCompact A
参数：hA : IsClosed A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.of_isClosed_subset`：IsCountablyCompact.of_isClosed_su
bset (hA : IsCountablyCompact A) (hB : IsClosed B) (hBA : B subseteq A) : IsCoun
tablyCompact B
· 使用定理 `CountablyCompactSpace.isCountablyCompact_univ`：∀ {E : Type u_4} {inst : 
TopologicalSpace E} [self : CountablyCompactSpace E], IsCountablyCompact Set.uni
v
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
A closed subset of a countably compact space is countably compact.
-/
theorem IsClosed.isCountablyCompact [CountablyCompactSpace E] (hA : IsClosed A) :
    IsCountablyCompact A :=
  CountablyCompactSpace.isCountablyCompact_univ.of_isClosed_subset hA (subset_univ _)

/-- A set is countably compact if and only if every sequence eventually in it has a cluster point
in it. -/
/-
**isCountablyCompact_iff_seq_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_seq_clusterPt : IsCountablyCompact A ↔ forall x : N
at -> E, (forallᶠ n in atTop, x n in A) -> exists a in A, MapClusterPt a atTop x
 where mp h x hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.map.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : Fi
lter α) [l.IsCountablyGenerated] (f : α → β),   (Filter.map f l).IsCountablyGene
rated
· 使用定理 `Filter.atTop.isCountablyGenerated`：∀ {α : Type u_1} [inst : Preorder α] 
[Countable α], Filter.atTop.IsCountablyGenerated
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `MapClusterPt.clusterPt`：∀ {X : Type u} [inst : TopologicalSpace X] {α : 
Type u_1} {F : Filter α} {u : α → X} {x : X},   MapClusterPt x F u → ClusterPt x
 (Filter.map…

--- 原说明 ---
A set is countably compact if and only if every sequence eventually in it has a 
cluster point
in it.
-/
theorem isCountablyCompact_iff_seq_clusterPt :
    IsCountablyCompact A ↔
      ∀ x : ℕ → E, (∀ᶠ n in atTop, x n ∈ A) → ∃ a ∈ A, MapClusterPt a atTop x where
  mp h x hx := h (tendsto_principal.mpr hx)
  mpr hA f _ _ hle := by
    obtain ⟨x, hx⟩ := f.exists_seq_tendsto
    obtain ⟨a, ha, hxa⟩ := hA x (by simpa using hx.mono_right hle)
    exact ⟨a, ha, hxa.clusterPt.mono hx⟩

alias ⟨IsCountablyCompact.seq_clusterPt,
  IsCountablyCompact.of_seq_clusterPt⟩ := isCountablyCompact_iff_seq_clusterPt

/-- For every countable open directed cover of a countably compact set, there exists a single
element of the cover which itself includes the set. -/
/-
**IsCountablyCompact.elim_directed_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.elim_directed_cover [Countable ι] [Nonempty ι] (hA : Is
CountablyCompact A) (U : ι -> Set E) (hUo : forall i, IsOpen (U i)) (hAU : A sub
seteq ⋃ i, U i) (hdU : Directed (· subseteq ·) U) : exists i, A subseteq U i
参数：hA : IsCountablyCompact A；U : ι -> Set E；hUo : forall i, IsOpen (U i)；hAU : A
 subseteq ⋃ i, U i；hdU : Directed (· subseteq ·) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `Filter.iInf_neBot_of_directed'`：iInf_neBot_of_directed' {f : ι -> Filter
 α} [Nonempty ι] (hd : Directed (· >= ·) f) : (forall i, NeBot (f i)) -> NeBot (
iInf f)
· 使用定理 `Set.Nonempty.principal_neBot`：∀ {α : Type u} {s : Set α}, s.Nonempty → (
Filter.principal s).NeBot
· 使用定理 `Set.sdiff_nonempty`：sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s
 subseteq t
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Filter.iInf.isCountablyGenerated`：∀ {ι : Sort u_6} {α : Type u_7} [Count
able ι] (f : ι → Filter α) [∀ (i : ι), (f i).IsCountablyGenerated],   (⨅ i, f i)
.IsCountablyGenerated
· 使用定理 `Filter.isCountablyGenerated_principal`：isCountablyGenerated_principal (s
 : Set α) : IsCountablyGenerated (𝓟 s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `ClusterPt.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X
} {s : Set X}, ClusterPt x (Filter.principal s) → x ∈ closure s
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i

--- 原说明 ---
For every countable open directed cover of a countably compact set, there exists
 a single
element of the cover which itself includes the set.
-/
theorem IsCountablyCompact.elim_directed_cover [Countable ι] [Nonempty ι]
    (hA : IsCountablyCompact A) (U : ι → Set E) (hUo : ∀ i, IsOpen (U i))
    (hAU : A ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) : ∃ i, A ⊆ U i := by
  by_contra! h
  have hdir : Directed (· ≥ ·) fun i => 𝓟 (A \ U i) :=
    fun i j => (hdU i j).imp fun _ ⟨hi, hj⟩ => ⟨principal_mono.mpr <| sdiff_subset_sdiff_right hi,
      principal_mono.mpr <| sdiff_subset_sdiff_right hj⟩
  have : NeBot (⨅ i, 𝓟 (A \ U i)) :=
    iInf_neBot_of_directed' hdir fun i => (sdiff_nonempty.mpr (h i)).principal_neBot
  have hle : (⨅ i, 𝓟 (A \ U i)) ≤ 𝓟 A :=
    iInf_le_of_le ‹Nonempty ι›.some <| principal_mono.mpr sdiff_subset
  rcases hA hle with ⟨a, ha, hac⟩
  rcases mem_iUnion.mp (hAU ha) with ⟨k, hk⟩
  exact closure_minimal (fun _ hx => hx.2) (hUo k).isClosed_compl
    (hac.mono (iInf_le _ k)).mem_closure hk

/-- A countably compact set has a finite subcover for any countable open cover. -/
/-
**IsCountablyCompact.elim_finite_subcover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.elim_finite_subcover (hA : IsCountablyCompact A) [Count
able ι] {U : ι -> Set E} (hUo : forall i, IsOpen (U i)) (hAU : A subseteq ⋃ i, U
 i) : exists t : Finset ι, A subseteq ⋃ i in t, U i
参数：hA : IsCountablyCompact A；hUo : forall i, IsOpen (U i)；hAU : A subseteq ⋃ i, 
U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.elim_directed_cover`：IsCountablyCompact.elim_directed
_cover [Countable ι] [Nonempty ι] (hA : IsCountablyCompact A) (U : ι -> Set E) (
hUo : forall i, IsOpen (U i)…
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x

--- 原说明 ---
A countably compact set has a finite subcover for any countable open cover.
-/
theorem IsCountablyCompact.elim_finite_subcover (hA : IsCountablyCompact A) [Countable ι]
    {U : ι → Set E} (hUo : ∀ i, IsOpen (U i)) (hAU : A ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i :=
  hA.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hAU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

/-- A set is countably compact if and only if every countable open cover has a finite subcover. -/
/-
**isCountablyCompact_iff_countable_open_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_countable_open_cover : IsCountablyCompact A ↔ foral
l (U : Nat -> Set E), (forall i, IsOpen (U i)) -> A subseteq ⋃ i, U i -> exists 
t : Finset Nat, A subseteq ⋃ i in t, U i where mp hA _ hUo hAU
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.elim_finite_subcover`：IsCountablyCompact.elim_finite_
subcover (hA : IsCountablyCompact A) [Countable ι] {U : ι -> Set E} (hUo : foral
l i, IsOpen (U i)) (hAU : A s…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `IsCountablyCompact.of_seq_clusterPt`：∀ {E : Type u_2} [inst : Topologica
lSpace E] {A : Set E},   (∀ (x : ℕ → E), (∀ᶠ (n : ℕ) in Filter.atTop, x n ∈ A) →
 ∃ a ∈ A, MapClusterPt a …
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A set is countably compact if and only if every countable open cover has a finit
e subcover.
-/
theorem isCountablyCompact_iff_countable_open_cover :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i where
  mp hA _ hUo hAU := hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    by_contra! hac
    let V : ℕ → Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
      compl_subset_compl.2 <| closure_mono <| image_mono <| Ici_subset_Ici.2 hmn
    simp only [mapClusterPt_atTop_iff_forall_mem_closure, not_forall] at hac
    have hAV : A ⊆ ⋃ n, V n := fun a haA => mem_iUnion.2 (hac a haA)
    obtain ⟨t, ht⟩ := h V (fun _ => isClosed_closure.isOpen_compl) hAV
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    let m := max N (t.sup id)
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hN m (le_max_left _ _)))
    have hxmV : x m ∈ V m := hVmono ((Finset.le_sup hjt).trans (le_max_right _ _)) hjV
    exact hxmV (subset_closure ⟨m, mem_Ici.mpr le_rfl, rfl⟩)

/-- A countably compact set has a finite subcover for any countable open cover indexed by a
subset. -/
/-
**IsCountablyCompact.elim_finite_subcover_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.elim_finite_subcover_image (hA : IsCountablyCompact A) 
{b : Set ι} (hb : b.Countable) {U : ι -> Set E} (hUo : forall i in b, IsOpen (U 
i)) (hAU : A subseteq ⋃ i in b, U i) : exists t subseteq b, t.Finite ∧ A subsete
q ⋃ i in t, U i
参数：hA : IsCountablyCompact A；hb : b.Countable；hUo : forall i in b, IsOpen (U i)；
hAU : A subseteq ⋃ i in b, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `IsCountablyCompact.elim_finite_subcover`：IsCountablyCompact.elim_finite_
subcover (hA : IsCountablyCompact A) [Countable ι] {U : ι -> Set E} (hUo : foral
l i, IsOpen (U i)) (hAU : A s…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)

--- 原说明 ---
A countably compact set has a finite subcover for any countable open cover index
ed by a
subset.
-/
theorem IsCountablyCompact.elim_finite_subcover_image (hA : IsCountablyCompact A)
    {b : Set ι} (hb : b.Countable) {U : ι → Set E} (hUo : ∀ i ∈ b, IsOpen (U i))
    (hAU : A ⊆ ⋃ i ∈ b, U i) : ∃ t ⊆ b, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  have := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) ↦ hUo i i.prop) (by simpa using hAU)
  simp only [Subtype.forall', biUnion_eq_iUnion] at hUo hAU
  replace hb := hb.to_subtype
  obtain ⟨d, hd⟩ := hA.elim_finite_subcover hUo hAU
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/-- Variant of `isCountablyCompact_iff_countable_open_cover` with `Set ℕ` instead of `Finset ℕ`. -/
/-
**isCountablyCompact_iff_countable_open_cover'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_countable_open_cover' : IsCountablyCompact A ↔ fora
ll (U : Nat -> Set E), (forall i, IsOpen (U i)) -> A subseteq ⋃ i, U i -> exists
 t : Set Nat, t.Finite ∧ A subseteq ⋃ i in t, U i
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Variant of `isCountablyCompact_iff_countable_open_cover` with `Set ℕ` instead of
 `Finset ℕ`.
-/
theorem isCountablyCompact_iff_countable_open_cover' :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
      ∃ t : Set ℕ, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  simp [isCountablyCompact_iff_countable_open_cover, Finset.exists]

/-- A compact set is countably compact. -/
/-
**IsCompact.isCountablyCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isCountablyCompact (hA : IsCompact A) : IsCountablyCompact A
参数：hA : IsCompact A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact set is countably compact.
-/
theorem IsCompact.isCountablyCompact (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ _ _ hle => hA hle

/-- A compact space is countably compact. -/
/-
**instCompactSpaceCountablyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instCompactSpaceCountablyCompactSpace {X : Type*} [TopologicalSpace X] [Co
mpactSpace X] : CountablyCompactSpace X where isCountablyCompact_univ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isCountablyCompact`：IsCompact.isCountablyCompact (hA : IsCompa
ct A) : IsCountablyCompact A
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)

--- 原说明 ---
A compact space is countably compact.
-/
instance instCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isCompact_univ.isCountablyCompact

/-- A sequentially compact set is countably compact. -/
/-
**IsSeqCompact.isCountablyCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.isCountablyCompact (hA : IsSeqCompact A) : IsCountablyCompact
 A
参数：hA : IsSeqCompact A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.of_seq_clusterPt`：∀ {E : Type u_2} [inst : Topologica
lSpace E] {A : Set E},   (∀ (x : ℕ → E), (∀ᶠ (n : ℕ) in Filter.atTop, x n ∈ A) →
 ∃ a ∈ A, MapClusterPt a …
· 使用定理 `IsSeqCompact.subseq_of_frequently_in`：IsSeqCompact.subseq_of_frequently_
in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X} (hx : existsᶠ n in atTop, x 
n in s) : exists a in s, e…
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MapClusterPt.of_comp`：MapClusterPt.of_comp {φ : β -> α} {p : Filter β} (
h : Tendsto φ p F) (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `Filter.Tendsto.mapClusterPt`：Filter.Tendsto.mapClusterPt [NeBot F] (h : 
Tendsto u F (𝓝 x)) : MapClusterPt x F u

--- 原说明 ---
A sequentially compact set is countably compact.
-/
theorem IsSeqCompact.isCountablyCompact (hA : IsSeqCompact A) :
    IsCountablyCompact A := IsCountablyCompact.of_seq_clusterPt fun x hx => by
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.subseq_of_frequently_in hx.frequently
  exact ⟨a, ha, hφa.mapClusterPt.of_comp hφ.tendsto_atTop⟩

/-- The continuous image of a countably compact set is countably compact. -/
/-
**IsCountablyCompact.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.image (hA : IsCountablyCompact A) {f : E -> F} (hf : Co
ntinuous f) : IsCountablyCompact (f '' A)
参数：hA : IsCountablyCompact A；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_neBot
_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α} (hs : m '' 
s in f) : NeBot (comap m f ⊓ 𝓟 s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.Inf.isCountablyGenerated`：∀ {α : Type u_1} (f g : Filter α) [f.Is
CountablyGenerated] [g.IsCountablyGenerated], (f ⊓ g).IsCountablyGenerated
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `Filter.isCountablyGenerated_principal`：isCountablyGenerated_principal (s
 : Set α) : IsCountablyGenerated (𝓟 s)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `ClusterPt.neBot`：ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : Ne
Bot (𝓝 x ⊓ F)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x

--- 原说明 ---
The continuous image of a countably compact set is countably compact.
-/
theorem IsCountablyCompact.image (hA : IsCountablyCompact A)
    {f : E → F} (hf : Continuous f) : IsCountablyCompact (f '' A) := by
  intro l hl_nebot hl_count hle
  have : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  have := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continuousAt.inf tendsto_comap).neBot⟩

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is countably compact if and
only if `s` is countably compact. -/
/-
**Topology.IsInducing.isCountablyCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isCountablyCompact_iff {f : E -> F} (hf : IsInducing f
) : IsCountablyCompact A ↔ IsCountablyCompact (f '' A)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.image`：IsCountablyCompact.image (hA : IsCountablyComp
act A) {f : E -> F} (hf : Continuous f) : IsCountablyCompact (f '' A)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Filter.map.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : Fi
lter α) [l.IsCountablyGenerated] (f : α → β),   (Filter.map f l).IsCountablyGene
rated
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsInducing.mapClusterPt_iff`：mapClusterPt_iff (hf : IsInducing 
f) {x : X} {l : Filter X} : MapClusterPt (f x) l f ↔ ClusterPt x l

--- 原说明 ---
If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is countably 
compact if and
only if `s` is countably compact.
-/
theorem Topology.IsInducing.isCountablyCompact_iff {f : E → F} (hf : IsInducing f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is countably compact if and
only if `s` is countably compact. -/
/-
**Topology.IsEmbedding.isCountablyCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isCountablyCompact_iff {f : E -> F} (hf : IsEmbedding
 f) : IsCountablyCompact A ↔ IsCountablyCompact (f '' A)
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isCountablyCompact_iff`：Topology.IsInducing.isCounta
blyCompact_iff {f : E -> F} (hf : IsInducing f) : IsCountablyCompact A ↔ IsCount
ablyCompact (f '' A)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…

--- 原说明 ---
If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is countably com
pact if and
only if `s` is countably compact.
-/
theorem Topology.IsEmbedding.isCountablyCompact_iff {f : E → F} (hf : IsEmbedding f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) :=
  hf.isInducing.isCountablyCompact_iff
/-
**Subtype.isCountablyCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isCountablyCompact_iff {p : E -> Prop} {A : Set { x // p x }} : Is
CountablyCompact A ↔ IsCountablyCompact ((↑) '' A : Set E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isCountablyCompact_iff`：Topology.IsEmbedding.isCoun
tablyCompact_iff {f : E -> F} (hf : IsEmbedding f) : IsCountablyCompact A ↔ IsCo
untablyCompact (f '' A)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem Subtype.isCountablyCompact_iff {p : E → Prop} {A : Set { x // p x }} :
    IsCountablyCompact A ↔ IsCountablyCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isCountablyCompact_iff
/-
**isCountablyCompact_iff_isCountablyCompact_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_isCountablyCompact_univ : IsCountablyCompact A ↔ Is
CountablyCompact (univ : Set A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.isCountablyCompact_iff`：Subtype.isCountablyCompact_iff {p : E ->
 Prop} {A : Set { x // p x }} : IsCountablyCompact A ↔ IsCountablyCompact ((↑) '
' A : Set E)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCountablyCompact_iff_isCountablyCompact_univ :
    IsCountablyCompact A ↔ IsCountablyCompact (univ : Set A) := by
  rw [Subtype.isCountablyCompact_iff, image_univ, Subtype.range_coe]
/-
**isCountablyCompact_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_univ_iff : IsCountablyCompact (univ : Set E) ↔ Countabl
yCompactSpace E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountablyCompactSpace.isCountablyCompact_univ`：∀ {E : Type u_4} {inst : 
TopologicalSpace E} [self : CountablyCompactSpace E], IsCountablyCompact Set.uni
v
-/
theorem isCountablyCompact_univ_iff : IsCountablyCompact (univ : Set E) ↔ CountablyCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
/-
**isCountablyCompact_iff_countablyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_countablyCompactSpace : IsCountablyCompact A ↔ Coun
tablyCompactSpace A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCountablyCompact_iff_isCountablyCompact_univ`：isCountablyCompact_iff_i
sCountablyCompact_univ : IsCountablyCompact A ↔ IsCountablyCompact (univ : Set A
)
· 使用定理 `isCountablyCompact_univ_iff`：isCountablyCompact_univ_iff : IsCountablyCo
mpact (univ : Set E) ↔ CountablyCompactSpace E
-/
theorem isCountablyCompact_iff_countablyCompactSpace :
    IsCountablyCompact A ↔ CountablyCompactSpace A :=
  isCountablyCompact_iff_isCountablyCompact_univ.trans isCountablyCompact_univ_iff

/-- If a sequential space is countably compact, then it is sequentially compact. We follow the proof
in [kremsater1972sequential]. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a sequential space is countably compact, then it is sequentially compact. We 
follow the proof
in [kremsater1972sequential].
-/
instance (priority := 50) [SequentialSpace E] [CountablyCompactSpace E] :
    SeqCompactSpace E := by
  -- We prove by contradiction. If `E` is not sequentially compact, then there exists a sequence
  -- `x : ℕ → E` with no convergent subsequence.
  by_contra
  simp only [seqCompactSpace_iff, IsSeqCompact, mem_univ, not_forall,
    true_and, not_exists, not_and, exists_const] at this
  obtain ⟨x, hx⟩ := this
  -- Consider the set `A = ⋃ i, closure {x i}`. It is closed by `isClosed_of_not_tendsto` and thus
  -- countably compact.
  let A := ⋃ i, closure {x i}
  have : IsCountablyCompact A :=
    (isClosed_iUnion_closure_singleton_of_not_tendsto hx).isCountablyCompact
  -- We use the countably compactness of `A` to find a cluster point `a`. Eventually `a` does not
  -- belong to the closure of `{x n}` as `x` has no convergent subsequence, and this contradicts `a`
  -- being a cluster point.
  obtain ⟨a, ha⟩ : ∃ a ∈ A, MapClusterPt a atTop x := by
    refine isCountablyCompact_iff_seq_clusterPt.1 this _ (.of_forall fun n => ?_)
    exact mem_iUnion_of_mem n <| subset_closure <| mem_singleton (x n)
  obtain ⟨k, hk⟩ : ∃ k, ∀ n > k, a ∉ closure {x n} := by
    by_contra!
    obtain ⟨φ, hφ1, hφ2⟩ := Nat.exists_strictMono_subsequence this
    refine hx a φ hφ1 (tendsto_atTop_nhds.2 fun U ha hUo => ⟨0, fun n _ => ?_⟩)
    simpa using mem_closure_iff.1 (hφ2 n) U hUo ha
  have : a ∉ ⋃ i, closure {x (i + (k + 1))} := by
    simpa [← iUnion_ge_eq_iUnion_nat_add (fun n => closure {x n}) (k + 1)] using!
      fun i hi => hk i (Nat.lt_of_lt_of_eq hi rfl)
  apply this
  suffices h : closure (x '' Ici (k + 1)) ⊆ ⋃ i, closure {x (i + (k + 1))} from
    h <| mapClusterPt_atTop_iff_forall_mem_closure.1 ha.2 (k + 1)
  refine (IsClosed.closure_subset_iff
    (isClosed_iUnion_closure_singleton_of_not_tendsto fun l φ hφ => ?_)).2 ?_
  · exact hx l _ ((strictMono_id.add_const _).comp hφ)
  · simp only [image_eq_iUnion, mem_Ici, iUnion_ge_eq_iUnion_nat_add _ (k + 1)]
    exact iUnion_mono fun i => subset_closure

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is sequentially compact
  if and only if `s` is sequentially compact. -/
/-
**Topology.IsInducing.isSeqCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isSeqCompact_iff {f : E -> F} (hf : IsInducing f) : Is
SeqCompact A ↔ IsSeqCompact (f '' A) where mp hA x hx
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is sequential
ly compact
  if and only if `s` is sequentially compact.
-/
theorem Topology.IsInducing.isSeqCompact_iff {f : E → F} (hf : IsInducing f) :
    IsSeqCompact A ↔ IsSeqCompact (f '' A) where
  mp hA x hx := by
    choose y hy using hx
    obtain ⟨a, ha, ⟨φ, hφ⟩⟩ := hA (fun n => (hy n).1)
    refine ⟨f a, mem_image_of_mem f ha, φ, hφ.1, ?_⟩
    suffices f ∘ y ∘ φ = x ∘ φ from this ▸ (hf.continuous.tendsto a).comp hφ.2
    grind
  mpr hA x hx := by
    obtain ⟨fa, hfa, ⟨φ, hφ⟩⟩ := hA (fun n => mem_image_of_mem f (hx n))
    choose a ha using hfa
    exact ⟨a, ha.1, φ, hφ.1, hf.tendsto_nhds_iff.2 (ha.2 ▸ hφ.2)⟩
/-
**Subtype.isSeqCompact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isSeqCompact_iff {p : E -> Prop} {A : Set { x // p x }} : IsSeqCom
pact A ↔ IsSeqCompact ((↑) '' A : Set E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isSeqCompact_iff`：Topology.IsInducing.isSeqCompact_i
ff {f : E -> F} (hf : IsInducing f) : IsSeqCompact A ↔ IsSeqCompact (f '' A) whe
re mp hA x hx
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem Subtype.isSeqCompact_iff {p : E → Prop} {A : Set { x // p x }} :
    IsSeqCompact A ↔ IsSeqCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isSeqCompact_iff
/-
**isSeqCompact_iff_isSeqCompact_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqCompact_iff_isSeqCompact_univ : IsSeqCompact A ↔ IsSeqCompact (univ :
 Set A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.isSeqCompact_iff`：Subtype.isSeqCompact_iff {p : E -> Prop} {A : 
Set { x // p x }} : IsSeqCompact A ↔ IsSeqCompact ((↑) '' A : Set E)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSeqCompact_iff_isSeqCompact_univ : IsSeqCompact A ↔ IsSeqCompact (univ : Set A) := by
  rw [Subtype.isSeqCompact_iff, image_univ, Subtype.range_coe]
/-
**isSeqCompact_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqCompact_univ_iff : IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeqCompactSpace.isSeqCompact_univ`：∀ {X : Type u_1} {inst : TopologicalS
pace X} [self : SeqCompactSpace X], IsSeqCompact Set.univ
-/
theorem isSeqCompact_univ_iff : IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
/-
**isSeqCompact_iff_seqCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqCompact_iff_seqCompactSpace : IsSeqCompact A ↔ SeqCompactSpace A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isSeqCompact_iff_isSeqCompact_univ`：isSeqCompact_iff_isSeqCompact_univ :
 IsSeqCompact A ↔ IsSeqCompact (univ : Set A)
· 使用定理 `isSeqCompact_univ_iff`：isSeqCompact_univ_iff : IsSeqCompact (univ : Set 
E) ↔ SeqCompactSpace E
-/
theorem isSeqCompact_iff_seqCompactSpace : IsSeqCompact A ↔ SeqCompactSpace A :=
  isSeqCompact_iff_isSeqCompact_univ.trans isSeqCompact_univ_iff

/-- A sequentially compact space is countably compact. -/
/-
**instSeqCompactSpaceCountablyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSeqCompactSpaceCountablyCompactSpace {X : Type*} [TopologicalSpace X] 
[SeqCompactSpace X] : CountablyCompactSpace X where isCountablyCompact_univ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqCompact.isCountablyCompact`：IsSeqCompact.isCountablyCompact (hA : I
sSeqCompact A) : IsCountablyCompact A
· 使用定理 `SeqCompactSpace.isSeqCompact_univ`：∀ {X : Type u_1} {inst : TopologicalS
pace X} [self : SeqCompactSpace X], IsSeqCompact Set.univ

--- 原说明 ---
A sequentially compact space is countably compact.
-/
instance instSeqCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isSeqCompact_univ.isCountablyCompact

/-- In a first-countable space, a countably compact set is sequentially compact. -/
/-
**IsCountablyCompact.isSeqCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.isSeqCompact [FirstCountableTopology E] (hA : IsCountab
lyCompact A) : IsSeqCompact A
参数：hA : IsCountablyCompact A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCountablyCompact_iff_countablyCompactSpace`：isCountablyCompact_iff_cou
ntablyCompactSpace : IsCountablyCompact A ↔ CountablyCompactSpace A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSeqCompact_iff_seqCompactSpace`：isSeqCompact_iff_seqCompactSpace : IsS
eqCompact A ↔ SeqCompactSpace A
· 使用定理 `instSeqCompactSpaceOfSequentialSpaceOfCountablyCompactSpace`：∀ {E : Type
 u_2} [inst : TopologicalSpace E] [SequentialSpace E] [CountablyCompactSpace E],
 SeqCompactSpace E
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X

--- 原说明 ---
In a first-countable space, a countably compact set is sequentially compact.
-/
theorem IsCountablyCompact.isSeqCompact [FirstCountableTopology E]
    (hA : IsCountablyCompact A) : IsSeqCompact A :=
  have : CountablyCompactSpace A := isCountablyCompact_iff_countablyCompactSpace.1 hA
  isSeqCompact_iff_seqCompactSpace.2 inferInstance

/-- A first-countable countably compact space is sequentially compact. -/
/-
**instCountablyCompactSpaceSeqCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instCountablyCompactSpaceSeqCompactSpace {X : Type*} [TopologicalSpace X] 
[FirstCountableTopology X] [CountablyCompactSpace X] : SeqCompactSpace X where i
sSeqCompact_univ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.isSeqCompact`：IsCountablyCompact.isSeqCompact [FirstC
ountableTopology E] (hA : IsCountablyCompact A) : IsSeqCompact A
· 使用定理 `CountablyCompactSpace.isCountablyCompact_univ`：∀ {E : Type u_4} {inst : 
TopologicalSpace E} [self : CountablyCompactSpace E], IsCountablyCompact Set.uni
v

--- 原说明 ---
A first-countable countably compact space is sequentially compact.
-/
instance instCountablyCompactSpaceSeqCompactSpace {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CountablyCompactSpace X] : SeqCompactSpace X where
  isSeqCompact_univ := CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact

/-- In a first-countable space, a set is countably compact iff it is sequentially compact. -/
/-
**isCountablyCompact_iff_isSeqCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_isSeqCompact [FirstCountableTopology E] : IsCountab
lyCompact A ↔ IsSeqCompact A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.isSeqCompact`：IsCountablyCompact.isSeqCompact [FirstC
ountableTopology E] (hA : IsCountablyCompact A) : IsSeqCompact A
· 使用定理 `IsSeqCompact.isCountablyCompact`：IsSeqCompact.isCountablyCompact (hA : I
sSeqCompact A) : IsCountablyCompact A

--- 原说明 ---
In a first-countable space, a set is countably compact iff it is sequentially co
mpact.
-/
theorem isCountablyCompact_iff_isSeqCompact [FirstCountableTopology E] :
    IsCountablyCompact A ↔ IsSeqCompact A :=
  ⟨fun h => h.isSeqCompact, fun h => h.isCountablyCompact⟩

/-- Every infinite subset of a countably compact set has an accumulation point in the set. -/
/-
**IsCountablyCompact.exists_accPt_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.exists_accPt_of_infinite (hA : IsCountablyCompact A) (h
BA : B subseteq A) (hB : B.Infinite) : exists a in A, AccPt a (𝓟 B)
参数：hA : IsCountablyCompact A；hBA : B subseteq A；hB : B.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `IsCountablyCompact.seq_clusterPt`：∀ {E : Type u_2} [inst : TopologicalSp
ace E] {A : Set E},   IsCountablyCompact A → ∀ (x : ℕ → E), (∀ᶠ (n : ℕ) in Filte
r.atTop, x n ∈ A) → ∃ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
Every infinite subset of a countably compact set has an accumulation point in th
e set.
-/
theorem IsCountablyCompact.exists_accPt_of_infinite
    (hA : IsCountablyCompact A) (hBA : B ⊆ A) (hB : B.Infinite) :
    ∃ a ∈ A, AccPt a (𝓟 B) := by
  let f := hB.natEmbedding
  let x : ℕ → E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ :=
    IsCountablyCompact.seq_clusterPt hA x (Eventually.of_forall (fun n => hBA (f n).2))
  refine ⟨a, haA, accPt_iff_clusterPt.2 <| ClusterPt.mono hac <| le_inf ?_ ?_⟩
  · exact tendsto_principal.mpr <| Nat.cofinite_eq_atTop ▸
      ((Set.finite_singleton a).preimage hx_inj.injOn).compl_mem_cofinite
  · exact tendsto_principal.mpr <| Eventually.of_forall fun n => (f n).2

/-- In a `T₁` space, a set is countably compact if and only if every infinite subset has an
accumulation point in the set. -/
/-
**isCountablyCompact_iff_infinite_subset_has_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iff_infinite_subset_has_accPt [T1Space E] {A : Set E} :
 IsCountablyCompact A ↔ forall B subseteq A, B.Infinite -> exists a in A, AccPt 
a (𝓟 B) where mp hA _ hBA hB
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablyCompact.exists_accPt_of_infinite`：IsCountablyCompact.exists_a
ccPt_of_infinite (hA : IsCountablyCompact A) (hBA : B subseteq A) (hB : B.Infini
te) : exists a in A, AccPt a (𝓟 B…
· 使用定理 `IsCountablyCompact.of_seq_clusterPt`：∀ {E : Type u_2} [inst : Topologica
lSpace E] {A : Set E},   (∀ (x : ℕ → E), (∀ᶠ (n : ℕ) in Filter.atTop, x n ∈ A) →
 ∃ a ∈ A, MapClusterPt a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用引理 `IsCompact.exists_mapClusterPt_of_frequently`：IsCompact.exists_mapCluster
Pt_of_frequently {l : Filter ι} {f : ι -> X} (hs : IsCompact s) (hf : existsᶠ x 
in l, f x in s) : exists a in s, …
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Infinite.inter_of_finite_sdiff`：∀ {α : Type u_1} {s t : Set α}, s.In
finite → (s \ t).Finite → (s ∩ t).Infinite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.compl_ofPred`：compl_ofPred {α} (p : α -> Prop) : { a | p a }ᶜ = { a 
| ¬p a }
· 使用定理 `Filter.mem_cofinite`：mem_cofinite {s : Set α} : s in @cofinite α ↔ sᶜ.Fi
nite
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
In a `T₁` space, a set is countably compact if and only if every infinite subset
 has an
accumulation point in the set.
-/
theorem isCountablyCompact_iff_infinite_subset_has_accPt [T1Space E] {A : Set E} :
    IsCountablyCompact A ↔ ∀ B ⊆ A, B.Infinite → ∃ a ∈ A, AccPt a (𝓟 B) where
  mp hA _ hBA hB := hA.exists_accPt_of_infinite hBA hB
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    rw [← Nat.cofinite_eq_atTop] at hx ⊢
    by_cases! hfin : (Set.range x).Finite
    · -- Case 1: Finite range
      suffices ∃ a ∈ range x ∩ A, MapClusterPt a cofinite x by aesop
      exact hfin.inter_of_left A |>.isCompact.exists_mapClusterPt_of_frequently <|
        hx.frequently.mp (by simp)
    · -- Case 2: Infinite range
      obtain ⟨a, haA, hacc⟩ := h (Set.range x ∩ A) inter_subset_right <| by
        rw [eventually_iff, mem_cofinite, compl_ofPred] at hx
        exact hfin.inter_of_finite_sdiff (hx.image x |>.subset (by grind))
      refine ⟨a, haA, ?_⟩
      simp_rw [mapClusterPt_iff_frequently, frequently_cofinite_iff_infinite]
      exact fun s hs ↦ Infinite.of_accPt (hacc.nhds_inter hs) |>.mono (by grind) |>.of_image x

/-- A countably compact Lindelöf set is compact. -/
/-
**IsLindelof.isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLindelof.isCompact (hA : IsCountablyCompact A) (hl : IsLindelof A) : IsC
ompact A
参数：hA : IsCountablyCompact A；hl : IsLindelof A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_of_finite_subcover`：isCompact_of_finite_subcover (h : forall {
ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) 
-> exists t : Fins…
· 使用定理 `IsLindelof.indexed_countable_subcover`：IsLindelof.indexed_countable_subc
over {ι : Type v} [Nonempty ι] (hs : IsLindelof s) (U : ι -> Set X) (hUo : foral
l i, IsOpen (U i)) (hsU : s…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCountablyCompact_iff_countable_open_cover`：isCountablyCompact_iff_coun
table_open_cover : IsCountablyCompact A ↔ forall (U : Nat -> Set E), (forall i, 
IsOpen (U i)) -> A subseteq ⋃ i, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
A countably compact Lindelöf set is compact.
-/
theorem IsLindelof.isCompact (hA : IsCountablyCompact A) (hl : IsLindelof A) :
    IsCompact A := by
  refine isCompact_of_finite_subcover fun {ι} U hUo hAU => ?_
  by_cases! h : Nonempty ι
  · obtain ⟨f, hf⟩ := hl.indexed_countable_subcover U hUo hAU
    obtain ⟨t, ht⟩ := isCountablyCompact_iff_countable_open_cover.1 hA (U ∘ f)
      (fun n => hUo (f n)) hf
    classical
    exact ⟨t.image f, by simp_all⟩
  · exact ⟨∅, by simp_all⟩

/-- A countably compact Lindelöf space is compact. -/
/-
**LindelofSpace.compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LindelofSpace.compactSpace {X : Type*} [TopologicalSpace X] [LindelofSpace
 X] [h : CountablyCompactSpace X] : CompactSpace X where isCompact_univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.isCompact`：IsLindelof.isCompact (hA : IsCountablyCompact A) (
hl : IsLindelof A) : IsCompact A
· 使用定理 `CountablyCompactSpace.isCountablyCompact_univ`：∀ {E : Type u_4} {inst : 
TopologicalSpace E} [self : CountablyCompactSpace E], IsCountablyCompact Set.uni
v
· 使用定理 `LindelofSpace.isLindelof_univ`：∀ {X : Type u_2} {inst : TopologicalSpace
 X} [self : LindelofSpace X], IsLindelof Set.univ

--- 原说明 ---
A countably compact Lindelöf space is compact.
-/
theorem LindelofSpace.compactSpace {X : Type*} [TopologicalSpace X]
    [LindelofSpace X] [h : CountablyCompactSpace X] : CompactSpace X where
  isCompact_univ := isLindelof_univ.isCompact h.isCountablyCompact_univ

@[deprecated (since := "2026-05-19")]
alias LindelofSpace.CompactSpace := LindelofSpace.compactSpace

/-- In a Hereditarily Lindelöf space, a countably compact set is compact. -/
/-
**IsCountablyCompact.isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.isCompact [HereditarilyLindelofSpace E] (hA : IsCountab
lyCompact A) : IsCompact A
参数：hA : IsCountablyCompact A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.isCompact`：IsLindelof.isCompact (hA : IsCountablyCompact A) (
hl : IsLindelof A) : IsCompact A
· 使用定理 `HereditarilyLindelofSpace.isLindelof`：HereditarilyLindelofSpace.isLindel
of [HereditarilyLindelofSpace X] (s : Set X) : IsLindelof s

--- 原说明 ---
In a Hereditarily Lindelöf space, a countably compact set is compact.
-/
theorem IsCountablyCompact.isCompact [HereditarilyLindelofSpace E]
    (hA : IsCountablyCompact A) : IsCompact A :=
  (HereditarilyLindelofSpace.isLindelof A).isCompact hA

/-- The union of two countably compact sets is countably compact. -/
/-
**IsCountablyCompact.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCountablyCompact.union (hA : IsCountablyCompact A) (hB : IsCountablyComp
act B) : IsCountablyCompact (A union B)
参数：hA : IsCountablyCompact A；hB : IsCountablyCompact B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCountablyCompact_iff_countable_open_cover'`：isCountablyCompact_iff_cou
ntable_open_cover' : IsCountablyCompact A ↔ forall (U : Nat -> Set E), (forall i
, IsOpen (U i)) -> A subseteq ⋃ i,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂

--- 原说明 ---
The union of two countably compact sets is countably compact.
-/
theorem IsCountablyCompact.union (hA : IsCountablyCompact A) (hB : IsCountablyCompact B) :
    IsCountablyCompact (A ∪ B) := by
  rw [isCountablyCompact_iff_countable_open_cover'] at hA hB ⊢
  intro U hUo hAU
  obtain ⟨t₁, ht₁, hA_sub⟩ : ∃ (t₁ : Set ℕ), t₁.Finite ∧ A ⊆ ⋃ k ∈ t₁, U k :=
    hA U hUo (subset_union_left.trans hAU)
  obtain ⟨t₂, ht₂, hB_sub⟩ : ∃ (t₂ : Set ℕ), t₂.Finite ∧ B ⊆ ⋃ k ∈ t₂, U k :=
    hB U hUo (subset_union_right.trans hAU)
  have h : (⋃ k ∈ t₁, U k) ∪ (⋃ k ∈ t₂, U k) = ⋃ k ∈ (t₁ ∪ t₂), U k := by ext; aesop
  exact ⟨t₁ ∪ t₂, ht₁.union ht₂, h ▸ union_subset_union hA_sub hB_sub⟩

/-- A finite union of countably compact sets is countably compact. -/
/-
**Finset.isCountablyCompact_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.isCountablyCompact_biUnion (s : Finset ι) {f : ι -> Set E} (hf : fo
rall i in s, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ i in s, f i)
参数：s : Finset ι；hf : forall i in s, IsCountablyCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `isCountablyCompact_empty`：isCountablyCompact_empty : IsCountablyCompact 
(∅ : Set E)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `IsCountablyCompact.union`：IsCountablyCompact.union (hA : IsCountablyComp
act A) (hB : IsCountablyCompact B) : IsCountablyCompact (A union B)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
A finite union of countably compact sets is countably compact.
-/
theorem Finset.isCountablyCompact_biUnion (s : Finset ι) {f : ι → Set E}
    (hf : ∀ i ∈ s, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCountablyCompact_empty
  | @insert a s ha ih => simpa [Finset.biUnion_insert] using
    (hf a (Finset.mem_insert_self a s)).union <| ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite union of countably compact sets is countably compact. -/
/-
**Set.Finite.isCountablyCompact_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCountablyCompact_biUnion {s : Set ι} {f : ι -> Set E} (hs : s
.Finite) (hf : forall i in s, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ 
i in s, f i)
参数：hs : s.Finite；hf : forall i in s, IsCountablyCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.isCountablyCompact_biUnion`：Finset.isCountablyCompact_biUnion (s 
: Finset ι) {f : ι -> Set E} (hf : forall i in s, IsCountablyCompact (f i)) : Is
CountablyCompact (⋃ i i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A finite union of countably compact sets is countably compact.
-/
theorem Set.Finite.isCountablyCompact_biUnion {s : Set ι} {f : ι → Set E} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ i ∈ s, f i) := by
  let s' : Finset ι := hs.toFinset
  have h1 : (⋃ i ∈ s, f i) = (⋃ i ∈ s', f i) := by simp [s']
  exact h1 ▸ Finset.isCountablyCompact_biUnion s' (fun i hi => hf i ((hs.mem_toFinset).mp hi))

/-- A finite union of countably compact sets is countably compact. -/
/-
**Set.Finite.isCountablyCompact_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCountablyCompact_sUnion {S : Set (Set E)} (hf : S.Finite) (hc
 : forall s in S, IsCountablyCompact s) : IsCountablyCompact (⋃₀ S)
参数：Set E；hf : S.Finite；hc : forall s in S, IsCountablyCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.isCountablyCompact_biUnion`：Set.Finite.isCountablyCompact_biU
nion {s : Set ι} {f : ι -> Set E} (hs : s.Finite) (hf : forall i in s, IsCountab
lyCompact (f i)) : IsCounta…

--- 原说明 ---
A finite union of countably compact sets is countably compact.
-/
theorem Set.Finite.isCountablyCompact_sUnion {S : Set (Set E)} (hf : S.Finite)
    (hc : ∀ s ∈ S, IsCountablyCompact s) :
    IsCountablyCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCountablyCompact_biUnion hc

/-- A finite union of countably compact sets is countably compact. -/
/-
**isCountablyCompact_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCountablyCompact_iUnion {ι : Sort*} {f : ι -> Set E} [Finite ι] (h : for
all i, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ i, f i)
参数：h : forall i, IsCountablyCompact (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isCountablyCompact_sUnion`：Set.Finite.isCountablyCompact_sUni
on {S : Set (Set E)} (hf : S.Finite) (hc : forall s in S, IsCountablyCompact s) 
: IsCountablyCompact (⋃₀ S…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
A finite union of countably compact sets is countably compact.
-/
theorem isCountablyCompact_iUnion {ι : Sort*} {f : ι → Set E} [Finite ι]
    (h : ∀ i, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i, f i) :=
  (finite_range f).isCountablyCompact_sUnion <| forall_mem_range.2 h

end

