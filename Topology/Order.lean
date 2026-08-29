/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Induced

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion. That is, for topologies `t₁` and
`t₂` on `α`, we write `t₁ ≤ t₂` if every set open in `t₂` is also open in `t₁`. (One also calls
`t₁` *finer* than `t₂`, and `t₂` *coarser* than `t₁`.)

Any function `f : α → β` induces

* `TopologicalSpace.induced f : TopologicalSpace β → TopologicalSpace α`;
* `TopologicalSpace.coinduced f : TopologicalSpace α → TopologicalSpace β`.

Continuity, the ordering on topologies and (co)induced topologies are related as follows:

* The identity map `(α, t₁) → (α, t₂)` is continuous iff `t₁ ≤ t₂`.
* A map `f : (α, t) → (β, u)` is continuous
  * iff `t ≤ TopologicalSpace.induced f u` (`continuous_iff_le_induced`)
  * iff `TopologicalSpace.coinduced f t ≤ u` (`continuous_iff_coinduced_le`).

Topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the indiscrete
topology.

For a function `f : α → β`, `(TopologicalSpace.coinduced f, TopologicalSpace.induced f)` is a Galois
connection between topologies on `α` and topologies on `β`.

## Implementation notes

There is a Galois insertion between topologies on `α` (with the inclusion ordering) and all
collections of sets in `α`. The complete lattice structure on topologies on `α` is defined as the
reverse of the one obtained via this Galois insertion. More precisely, we use the corresponding
Galois coinsertion between topologies on `α` (with the reversed inclusion ordering) and collections
of sets in `α` (with the reversed inclusion ordering).

## Tags

finer, coarser, induced topology, coinduced topology
-/

@[expose] public section

open Function Set Filter Topology

universe u v w

namespace TopologicalSpace

variable {α : Type u}

/--
Inductive type `GenerateOpen` / 归纳类型 `GenerateOpen`

English:
inductive GenerateOpen
  parameters: (g : Set (Set α))
  constructors (4):
    - basic: forall s in g, GenerateOpen g s
    - univ: GenerateOpen g univ
    - inter: forall s t, GenerateOpen g s -> GenerateOpen g t -> GenerateOpen g (s inter t)
    - sUnion: forall S : Set (Set α), (forall s in S, GenerateOpen g s) -> GenerateOpen g (⋃₀ S)

中文:
归纳类型 GenerateOpen
  参数: (g : 集合 (集合 α))
  构造子 (4 个):
    - basic: 对任意 s in g, GenerateOpen g s
    - univ: GenerateOpen g univ
    - inter: 对任意 s t, GenerateOpen g s -> GenerateOpen g t -> GenerateOpen g (s inter t)
    - sUnion: 对任意 S : 集合 (集合 α), (对任意 s in S, GenerateOpen g s) -> GenerateOpen g (⋃₀ S)
-/
inductive GenerateOpen (g : Set (Set α)) : Set α -> Prop
  | basic : forall s in g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : forall s t, GenerateOpen g s -> GenerateOpen g t -> GenerateOpen g (s inter t)
  | sUnion : forall S : Set (Set α), (forall s in S, GenerateOpen g s) -> GenerateOpen g (⋃₀ S)

/-- The smallest topological space containing the collection `g` of basic sets -/
@[instance_reducible]
/--
Definition of `generateFrom` / `generateFrom` 的定义

English:
definition generateFrom
  signature: (g : Set (Set α))
  body: GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

中文:
定义 generateFrom
  签名: (g : 集合 (集合 α))
  定义体: GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

Depends on / 依赖: GenerateOpen
-/
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

/--
theorem `isOpen_generateFrom_of_mem` / 定理 `isOpen_generateFrom_of_mem`

English:
theorem isOpen_generateFrom_of_mem
  given: {g : Set (Set α)} {s : Set α} (hs : s in g)
  proof: GenerateOpen.basic s hs

中文:
定理 isOpen_generateFrom_of_mem
  条件: {g : 集合 (集合 α)} {s : 集合 α} (hs : s in g)
  证明: GenerateOpen.basic s hs

Depends on / 依赖: GenerateOpen, GenerateOpen.basic
-/
theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s in g) :
    IsOpen[generateFrom g] s :=
  GenerateOpen.basic s hs

/--
theorem `nhds_generateFrom` / 定理 `nhds_generateFrom`

English:
theorem nhds_generateFrom
  given: {g : Set (Set α)} {a : α}
  proof: by
  let := generateFrom g
  rw [nhds_def]
refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) le_iInf₂ ?_
  rintro s ⟨ha, hs⟩
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)

中文:
定理 nhds_generateFrom
  条件: {g : 集合 (集合 α)} {a : α}
  证明: by
  let := generateFrom g
  rw [nhds_def]
refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) le_iInf₂ ?_
  rintro s ⟨ha, hs⟩
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)

Depends on / 依赖: biInf_mono, generateFrom, inf_principal, le_antisymm, le_inf, le_top, le_top.trans_eq, nhds_def, principal_mono, principal_univ, principal_univ.symm, sUnion, subset_sUnion_of_mem, trans_eq
-/
theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s := by
  let := generateFrom g
  rw [nhds_def]
refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) le_iInf₂ ?_
  rintro s ⟨ha, hs⟩
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)

/--
lemma `tendsto_nhds_generateFrom_iff` / 引理 `tendsto_nhds_generateFrom_iff`

English:
lemma tendsto_nhds_generateFrom_iff
  statement: {β : Type*} {m : α -> β} {f : Filter α} {g : Set (Set β)}
  proof: by
  simp only [nhds_generateFrom, @forall_comm (b in _), tendsto_iInf, mem_ofPred_eq, and_imp,
    tendsto_principal]; rfl

中文:
引理 tendsto_nhds_generateFrom_iff
  结论: {β : 类型} {m : α -> β} {f : 滤子 α} {g : 集合 (集合 β)}
  证明: by
  simp only [nhds_generateFrom, @forall_comm (b in _), tendsto_iInf, mem_ofPred_eq, and_imp,
    tendsto_principal]; rfl

Depends on / 依赖: and_imp, forall_comm, mem_ofPred_eq, nhds_generateFrom, tendsto_iInf, tendsto_principal
-/
lemma tendsto_nhds_generateFrom_iff {β : Type*} {m : α -> β} {f : Filter α} {g : Set (Set β)}
    {b : β} : Tendsto m f (@nhds β (generateFrom g) b) ↔ forall s in g, b in s -> m ⁻¹' s in f := by
  simp only [nhds_generateFrom, @forall_comm (b in _), tendsto_iInf, mem_ofPred_eq, and_imp,
    tendsto_principal]; rfl

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
@[instance_reducible]
/--
Definition of `mkOfNhds` / `mkOfNhds` 的定义

English:
definition mkOfNhds
  signature: (n : α -> Filter α)
  body: forall a in s, s in n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)

中文:
定义 mkOfNhds
  签名: (n : α -> 滤子 α)
  定义体: forall a in s, s in n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)
-/
protected def mkOfNhds (n : α -> Filter α) : TopologicalSpace α where
  IsOpen s := forall a in s, s in n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)

/--
theorem `nhds_mkOfNhds_of_hasBasis` / 定理 `nhds_mkOfNhds_of_hasBasis`

English:
theorem nhds_mkOfNhds_of_hasBasis
  statement: {n : α -> Filter α} {ι : α -> Sort*} {p : forall a, ι a -> Prop}
  proof: by
  let t : TopologicalSpace α := .mkOfNhds n
  apply le_antisymm
  · intro U hU
    replace hpure : pure <= n := fun x => (hb x).ge_iff.2 (hpure x)
    refine mem_nhds_iff.2 ⟨{x | U in n x}, fun x hx => hpure x hx, fun x hx => ?_, hU⟩
    rcases (hb x).mem_iff.1 hx with ⟨i, hpi, hi⟩
    exact (hopen x i hpi).mono fun y => by gcongr
  · exact (nhds_basis_opens a).ge_iff.2 fun U ⟨haU, hUo⟩ => hUo a haU

中文:
定理 nhds_mkOfNhds_of_hasBasis
  结论: {n : α -> 滤子 α} {ι : α -> 类型层*} {p : 对任意 a, ι a -> 命题}
  证明: by
  let t : TopologicalSpace α := .mkOfNhds n
  apply le_antisymm
  · intro U hU
    replace hpure : pure <= n := fun x => (hb x).ge_iff.2 (hpure x)
    refine mem_nhds_iff.2 ⟨{x | U in n x}, fun x hx => hpure x hx, fun x hx => ?_, hU⟩
    rcases (hb x).mem_iff.1 hx with ⟨i, hpi, hi⟩
    exact (hopen x i hpi).mono fun y => by gcongr
  · exact (nhds_basis_opens a).ge_iff.2 fun U ⟨haU, hUo⟩ => hUo a haU

Depends on / 依赖: TopologicalSpace, ge_iff, le_antisymm, mem_iff, mem_nhds_iff, mkOfNhds, nhds_basis_opens, replace
-/
theorem nhds_mkOfNhds_of_hasBasis {n : α -> Filter α} {ι : α -> Sort*} {p : forall a, ι a -> Prop}
    {s : forall a, ι a -> Set α} (hb : forall a, (n a).HasBasis (p a) (s a))
    (hpure : forall a i, p a i -> a in s a i) (hopen : forall a i, p a i -> forallᶠ x in n a, s a i in n x) (a : α) :
    @nhds α (.mkOfNhds n) a = n a := by
  let t : TopologicalSpace α := .mkOfNhds n
  apply le_antisymm
  · intro U hU
    replace hpure : pure <= n := fun x => (hb x).ge_iff.2 (hpure x)
    refine mem_nhds_iff.2 ⟨{x | U in n x}, fun x hx => hpure x hx, fun x hx => ?_, hU⟩
    rcases (hb x).mem_iff.1 hx with ⟨i, hpi, hi⟩
    exact (hopen x i hpi).mono fun y => by gcongr
  · exact (nhds_basis_opens a).ge_iff.2 fun U ⟨haU, hUo⟩ => hUo a haU

/--
theorem `nhds_mkOfNhds` / 定理 `nhds_mkOfNhds`

English:
theorem nhds_mkOfNhds
  statement: (n : α -> Filter α) (a : α) (h₀ : pure <= n)
  proof: nhds_mkOfNhds_of_hasBasis (fun a => (n a).basis_sets) h₀ h₁ _

中文:
定理 nhds_mkOfNhds
  结论: (n : α -> 滤子 α) (a : α) (h₀ : pure <= n)
  证明: nhds_mkOfNhds_of_hasBasis (fun a => (n a).basis_sets) h₀ h₁ _

Depends on / 依赖: basis_sets, nhds_mkOfNhds_of_hasBasis
-/
theorem nhds_mkOfNhds (n : α -> Filter α) (a : α) (h₀ : pure <= n)
    (h₁ : forall a, forall s in n a, forallᶠ y in n a, s in n y) :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a :=
  nhds_mkOfNhds_of_hasBasis (fun a => (n a).basis_sets) h₀ h₁ _

/--
theorem `nhds_mkOfNhds_single` / 定理 `nhds_mkOfNhds_single`

English:
theorem nhds_mkOfNhds_single
  given: [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ <= l) (b : α)
  proof: by
  refine nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => ?_
  rcases eq_or_ne a a₀ with (rfl | ha)
  · filter_upwards [hs] with b hb
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_of_ne hb]
  · simpa only [update_of_ne ha, mem_pure, eventually_pure] using hs

中文:
定理 nhds_mkOfNhds_single
  条件: [DecidableEq α] {a₀ : α} {l : 滤子 α} (h : pure a₀ <= l) (b : α)
  证明: by
  refine nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => ?_
  rcases eq_or_ne a a₀ with (rfl | ha)
  · filter_upwards [hs] with b hb
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_of_ne hb]
  · simpa only [update_of_ne ha, mem_pure, eventually_pure] using hs

Depends on / 依赖: eq_or_ne, eventually_pure, filter_upwards, le_rfl, le_update_iff, le_update_iff.mpr, mem_pure, nhds_mkOfNhds, update_of_ne
-/
theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ <= l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds (update pure a₀ l)) b =
      (update pure a₀ l : α -> Filter α) b := by
  refine nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => ?_
  rcases eq_or_ne a a₀ with (rfl | ha)
  · filter_upwards [hs] with b hb
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_of_ne hb]
  · simpa only [update_of_ne ha, mem_pure, eventually_pure] using hs

/--
theorem `nhds_mkOfNhds_filterBasis` / 定理 `nhds_mkOfNhds_filterBasis`

English:
theorem nhds_mkOfNhds_filterBasis
  statement: (B : α -> FilterBasis α) (a : α) (h₀ : forall x, forall n in B x, x in n)
  proof: nhds_mkOfNhds_of_hasBasis (fun a => (B a).hasBasis) h₀ h₁ a

中文:
定理 nhds_mkOfNhds_filterBasis
  结论: (B : α -> 滤子基 α) (a : α) (h₀ : 对任意 x, 对任意 n in B x, x in n)
  证明: nhds_mkOfNhds_of_hasBasis (fun a => (B a).hasBasis) h₀ h₁ a

Depends on / 依赖: hasBasis, nhds_mkOfNhds_of_hasBasis
-/
theorem nhds_mkOfNhds_filterBasis (B : α -> FilterBasis α) (a : α) (h₀ : forall x, forall n in B x, x in n)
    (h₁ : forall x, forall n in B x, exists n₁ in B x, forall x' in n₁, exists n₂ in B x', n₂ subseteq n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter :=
  nhds_mkOfNhds_of_hasBasis (fun a => (B a).hasBasis) h₀ h₁ a

section Lattice

variable {α : Type u} {β : Type v}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (TopologicalSpace α)
  body: { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => forall U, IsOpen[t] U -> IsOpen[s] U }

中文:
实例 :
  签名: 偏序 (拓扑空间 α)
  定义体: { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => forall U, IsOpen[t] U -> IsOpen[s] U }

Depends on / 依赖: IsOpen, OrderDual, OrderDual.toDual, PartialOrder, PartialOrder.lift, TopologicalSpace, TopologicalSpace.ext, toDual
-/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => forall U, IsOpen[t] U -> IsOpen[s] U }

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {α} {t s : TopologicalSpace α}
  statement: t <= s ↔ IsOpen[s] <= IsOpen[t]
  proof: Iff.rfl

中文:
定理 le_def
  条件: {α} {t s : 拓扑空间 α}
  结论: t <= s ↔ 是开集[s] <= 是开集[t]
  证明: Iff.rfl
-/
protected theorem le_def {α} {t s : TopologicalSpace α} : t <= s ↔ IsOpen[s] <= IsOpen[t] :=
  Iff.rfl

/--
theorem `le_generateFrom_iff_subset_isOpen` / 定理 `le_generateFrom_iff_subset_isOpen`

English:
theorem le_generateFrom_iff_subset_isOpen
  given: {g : Set (Set α)} {t : TopologicalSpace α}
  proof: ⟨fun ht s hs => ht _ .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩

中文:
定理 le_generateFrom_iff_subset_isOpen
  条件: {g : 集合 (集合 α)} {t : 拓扑空间 α}
  证明: ⟨fun ht s hs => ht _ .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩

Depends on / 依赖: IsOpen, IsOpen.inter, hs.recOn, isOpen_sUnion, isOpen_univ
-/
theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t <= generateFrom g ↔ g subseteq { s | IsOpen[t] s } :=
⟨fun ht s hs => ht _ .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
@[instance_reducible]
/--
Definition of `mkOfClosure` / `mkOfClosure` 的定义

English:
definition mkOfClosure
  signature: (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s)
  body: u in s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion

中文:
定义 mkOfClosure
  签名: (s : 集合 (集合 α)) (hs : { u | GenerateOpen s u } = s)
  定义体: u in s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
-/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) :
    TopologicalSpace α where
  IsOpen u := u in s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion

/--
theorem `mkOfClosure_sets` / 定理 `mkOfClosure_sets`

English:
theorem mkOfClosure_sets
  given: {s : Set (Set α)} {hs : {u | GenerateOpen s u} = s}
  proof: TopologicalSpace.ext (by ext U; exact Set.ext_iff.mp hs.symm U)

中文:
定理 mkOfClosure_sets
  条件: {s : 集合 (集合 α)} {hs : {u | GenerateOpen s u} = s}
  证明: TopologicalSpace.ext (by ext U; exact Set.ext_iff.mp hs.symm U)

Depends on / 依赖: Set.ext_iff.mp, TopologicalSpace, TopologicalSpace.ext, ext_iff, hs.symm
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : {u | GenerateOpen s u} = s} :
    TopologicalSpace.mkOfClosure s hs = generateFrom s :=
  TopologicalSpace.ext (by ext U; exact Set.ext_iff.mp hs.symm U)

/--
theorem `gc_generateFrom` / 定理 `gc_generateFrom`

English:
theorem gc_generateFrom
  given: (α)
  proof: fun _ _ =>
  le_generateFrom_iff_subset_isOpen.symm

中文:
定理 gc_generateFrom
  条件: (α)
  证明: fun _ _ =>
  le_generateFrom_iff_subset_isOpen.symm
-/
theorem gc_generateFrom (α) :
    GaloisConnection (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) := fun _ _ =>
  le_generateFrom_iff_subset_isOpen.symm

/--
Definition of `gciGenerateFrom` / `gciGenerateFrom` 的定义

English:
definition gciGenerateFrom
  signature: (α : Type*)
  body: gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

中文:
定义 gciGenerateFrom
  签名: (α : 类型)
  定义体: gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

Depends on / 依赖: gc_generateFrom
-/
def gciGenerateFrom (α : Type*) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) where
  gc := gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (TopologicalSpace α)
  body: (gciGenerateFrom α).liftCompleteLattice

@[mono, gcongr]

中文:
实例 :
  签名: 完备格 (拓扑空间 α)
  定义体: (gciGenerateFrom α).liftCompleteLattice

@[mono, gcongr]

Depends on / 依赖: gciGenerateFrom, liftCompleteLattice
-/
instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice

@[mono, gcongr]
/--
theorem `generateFrom_anti` / 定理 `generateFrom_anti`

English:
theorem generateFrom_anti
  given: {α} {g₁ g₂ : Set (Set α)} (h : g₁ subseteq g₂)
  proof: (gc_generateFrom _).monotone_u h

中文:
定理 generateFrom_anti
  条件: {α} {g₁ g₂ : 集合 (集合 α)} (h : g₁ subseteq g₂)
  证明: (gc_generateFrom _).monotone_u h

Depends on / 依赖: gc_generateFrom, monotone_u
-/
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ subseteq g₂) :
    generateFrom g₂ <= generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h

/--
theorem `generateFrom_setOfPred_isOpen` / 定理 `generateFrom_setOfPred_isOpen`

English:
theorem generateFrom_setOfPred_isOpen
  given: (t : TopologicalSpace α)
  proof: (gciGenerateFrom α).u_l_eq t

@[deprecated (since := "2026-07-09")]
alias generateFrom_setOf_isOpen := generateFrom_setOfPred_isOpen

中文:
定理 generateFrom_setOfPred_isOpen
  条件: (t : 拓扑空间 α)
  证明: (gciGenerateFrom α).u_l_eq t

@[deprecated (since := "2026-07-09")]
alias generateFrom_setOf_isOpen := generateFrom_setOfPred_isOpen

Depends on / 依赖: gciGenerateFrom, u_l_eq
-/
theorem generateFrom_setOfPred_isOpen (t : TopologicalSpace α) :
    generateFrom { s | IsOpen[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t

@[deprecated (since := "2026-07-09")]
alias generateFrom_setOf_isOpen := generateFrom_setOfPred_isOpen

/--
theorem `leftInverse_generateFrom` / 定理 `leftInverse_generateFrom`

English:
theorem leftInverse_generateFrom
  proof: (gciGenerateFrom α).leftInverse_u_l

中文:
定理 leftInverse_generateFrom
  证明: (gciGenerateFrom α).leftInverse_u_l

Depends on / 依赖: gciGenerateFrom, leftInverse_u_l
-/
theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).leftInverse_u_l

/--
theorem `generateFrom_surjective` / 定理 `generateFrom_surjective`

English:
theorem generateFrom_surjective
  statement: Surjective (generateFrom : Set (Set α) -> TopologicalSpace α)
  proof: (gciGenerateFrom α).u_surjective

中文:
定理 generateFrom_surjective
  结论: 满射 (generateFrom : 集合 (集合 α) -> 拓扑空间 α)
  证明: (gciGenerateFrom α).u_surjective

Depends on / 依赖: gciGenerateFrom, u_surjective
-/
theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) -> TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective

/--
theorem `setOfPred_isOpen_injective` / 定理 `setOfPred_isOpen_injective`

English:
theorem setOfPred_isOpen_injective
  statement: Injective fun t : TopologicalSpace α => { s | IsOpen[t] s }
  proof: (gciGenerateFrom α).l_injective

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_injective := setOfPred_isOpen_injective

中文:
定理 setOfPred_isOpen_injective
  结论: 单射 fun t : 拓扑空间 α => { s | 是开集[t] s }
  证明: (gciGenerateFrom α).l_injective

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_injective := setOfPred_isOpen_injective

Depends on / 依赖: gciGenerateFrom, l_injective
-/
theorem setOfPred_isOpen_injective : Injective fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).l_injective

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_injective := setOfPred_isOpen_injective

end Lattice

end TopologicalSpace

section Lattice

variable {α : Type*} {t t₁ t₂ : TopologicalSpace α} {s : Set α}

/--
theorem `IsOpen.mono` / 定理 `IsOpen.mono`

English:
theorem IsOpen.mono
  given: (hs : IsOpen[t₂] s) (h : t₁ <= t₂)
  statement: IsOpen[t₁] s
  proof: h s hs

中文:
定理 是开集.mono
  条件: (hs : 是开集[t₂] s) (h : t₁ <= t₂)
  结论: 是开集[t₁] s
  证明: h s hs
-/
theorem IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ <= t₂) : IsOpen[t₁] s := h s hs

/--
theorem `IsClosed.mono` / 定理 `IsClosed.mono`

English:
theorem IsClosed.mono
  given: (hs : IsClosed[t₂] s) (h : t₁ <= t₂)
  statement: IsClosed[t₁] s
  proof: (@isOpen_compl_iff α s t₁).mp hs.isOpen_compl.mono h

中文:
定理 是闭集.mono
  条件: (hs : 是闭集[t₂] s) (h : t₁ <= t₂)
  结论: 是闭集[t₁] s
  证明: (@isOpen_compl_iff α s t₁).mp hs.isOpen_compl.mono h

Depends on / 依赖: hs.isOpen_compl.mono, isOpen_compl, isOpen_compl_iff
-/
theorem IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsClosed[t₁] s :=
(@isOpen_compl_iff α s t₁).mp hs.isOpen_compl.mono h

/--
theorem `closure.mono` / 定理 `closure.mono`

English:
theorem closure.mono
  given: (h : t₁ <= t₂)
  statement: closure[t₁] s subseteq closure[t₂] s
  proof: @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)

中文:
定理 closure.mono
  条件: (h : t₁ <= t₂)
  结论: closure[t₁] s subseteq closure[t₂] s
  证明: @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)

Depends on / 依赖: IsClosed, IsClosed.mono, closure, closure_minimal, isClosed_closure, subset_closure
-/
theorem closure.mono (h : t₁ <= t₂) : closure[t₁] s subseteq closure[t₂] s :=
  @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)

/--
theorem `isOpen_implies_isOpen_iff` / 定理 `isOpen_implies_isOpen_iff`

English:
theorem isOpen_implies_isOpen_iff
  statement: (forall s, IsOpen[t₁] s -> IsOpen[t₂] s) ↔ t₂ <= t₁
  proof: Iff.rfl

中文:
定理 isOpen_implies_isOpen_iff
  结论: (对任意 s, 是开集[t₁] s -> 是开集[t₂] s) ↔ t₂ <= t₁
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_implies_isOpen_iff : (forall s, IsOpen[t₁] s -> IsOpen[t₂] s) ↔ t₂ <= t₁ :=
  Iff.rfl

section nontriviality

/-- A topological space is indiscrete if the only open sets are the empty set and the whole space,
that is that its topology equals the indiscrete topology `⊤`.

This can also go by the name "trivial topology" or "codiscrete topology". -/
@[mk_iff]
/--
Definition of `IndiscreteTopology` / `IndiscreteTopology` 的定义

English:
class IndiscreteTopology
  parameters: (α) [TopologicalSpace α]
  axioms and operations (1):
    - eq_top((α)) : ‹TopologicalSpace α› = ⊤

中文:
类 Indiscrete拓扑
  参数: (α) [拓扑空间 α]
  公理与运算 (1 个):
    - eq_top((α)) : ‹拓扑空间 α› = ⊤
-/
class IndiscreteTopology (α) [TopologicalSpace α] where
  eq_top (α) : ‹TopologicalSpace α› = ⊤

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @IndiscreteTopology α ⊤
  body: @IndiscreteTopology.mk _ ⊤ rfl

中文:
实例 :
  签名: @Indiscrete拓扑 α ⊤
  定义体: @IndiscreteTopology.mk _ ⊤ rfl

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.mk
-/
instance : @IndiscreteTopology α ⊤ := @IndiscreteTopology.mk _ ⊤ rfl


/-- A topological space is nontrivial if it is not the indiscrete topology. -/
@[mk_iff]
/--
Definition of `NontrivialTopology` / `NontrivialTopology` 的定义

English:
class NontrivialTopology
  parameters: (α) [TopologicalSpace α]
  axioms and operations (1):
    - ne_top((α)) : ‹TopologicalSpace α› != ⊤

中文:
类 非平凡拓扑
  参数: (α) [拓扑空间 α]
  公理与运算 (1 个):
    - ne_top((α)) : ‹拓扑空间 α› != ⊤
-/
class NontrivialTopology (α) [TopologicalSpace α] where
  ne_top (α) : ‹TopologicalSpace α› != ⊤

/--
theorem `TopologicalSpace.indiscrete_or_nontrivial` / 定理 `TopologicalSpace.indiscrete_or_nontrivial`

English:
theorem TopologicalSpace.indiscrete_or_nontrivial
  given: (α) [TopologicalSpace α]
  proof: (eq_or_ne ‹TopologicalSpace α› ⊤).imp .mk .mk

@[simp, push]

中文:
定理 拓扑空间.indiscrete_or_nontrivial
  条件: (α) [拓扑空间 α]
  证明: (eq_or_ne ‹TopologicalSpace α› ⊤).imp .mk .mk

@[simp, push]

Depends on / 依赖: TopologicalSpace, eq_or_ne
-/
theorem TopologicalSpace.indiscrete_or_nontrivial (α) [TopologicalSpace α] :
    IndiscreteTopology α ∨ NontrivialTopology α :=
  (eq_or_ne ‹TopologicalSpace α› ⊤).imp .mk .mk

@[simp, push]
/--
theorem `TopologicalSpace.not_indiscrete_iff` / 定理 `TopologicalSpace.not_indiscrete_iff`

English:
theorem TopologicalSpace.not_indiscrete_iff
  given: [TopologicalSpace α]
  proof: ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h x => h.ne_top x.eq_top⟩

@[simp, push]

中文:
定理 拓扑空间.not_indiscrete_iff
  条件: [拓扑空间 α]
  证明: ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h x => h.ne_top x.eq_top⟩

@[simp, push]

Depends on / 依赖: eq_top, h.ne_top, ne_top, x.eq_top
-/
theorem TopologicalSpace.not_indiscrete_iff [TopologicalSpace α] :
    ¬IndiscreteTopology α ↔ NontrivialTopology α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h x => h.ne_top x.eq_top⟩

@[simp, push]
/--
theorem `TopologicalSpace.not_nontrivial_iff` / 定理 `TopologicalSpace.not_nontrivial_iff`

English:
theorem TopologicalSpace.not_nontrivial_iff
  given: [TopologicalSpace α]
  proof: TopologicalSpace.not_indiscrete_iff.not_right.symm

中文:
定理 拓扑空间.not_nontrivial_iff
  条件: [拓扑空间 α]
  证明: TopologicalSpace.not_indiscrete_iff.not_right.symm

Depends on / 依赖: TopologicalSpace, TopologicalSpace.not_indiscrete_iff.not_right.symm, not_indiscrete_iff, not_right
-/
theorem TopologicalSpace.not_nontrivial_iff [TopologicalSpace α] :
    ¬NontrivialTopology α ↔ IndiscreteTopology α :=
  TopologicalSpace.not_indiscrete_iff.not_right.symm

end nontriviality

/--
theorem `IndiscreteTopology.isOpen_iff` / 定理 `IndiscreteTopology.isOpen_iff`

English:
theorem IndiscreteTopology.isOpen_iff
  given: [IndiscreteTopology α] (U : Set α)
  proof: by
  cases IndiscreteTopology.eq_top α
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | basic _ h => exact False.elim h
    | univ => exact .inr rfl
    | inter _ _ _ _ h₁ h₂ =>
      rcases h₁ with (rfl | rfl) <;> rcases h₂ with (rfl | rfl) <;> simp
    | sUnion _ _ ih => exact sUnion_mem_empty_univ ih
  · rintro (rfl | rfl)
    exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]

中文:
定理 Indiscrete拓扑.isOpen_iff
  条件: [Indiscrete拓扑 α] (U : 集合 α)
  证明: by
  cases IndiscreteTopology.eq_top α
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | basic _ h => exact False.elim h
    | univ => exact .inr rfl
    | inter _ _ _ _ h₁ h₂ =>
      rcases h₁ with (rfl | rfl) <;> rcases h₂ with (rfl | rfl) <;> simp
    | sUnion _ _ ih => exact sUnion_mem_empty_univ ih
  · rintro (rfl | rfl)
    exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]

Depends on / 依赖: False.elim, IndiscreteTopology, IndiscreteTopology.eq_top, eq_top, exacts, isOpen_empty, isOpen_univ, sUnion, sUnion_mem_empty_univ
-/
theorem IndiscreteTopology.isOpen_iff [IndiscreteTopology α] (U : Set α) :
    IsOpen U ↔ U = ∅ ∨ U = univ := by
  cases IndiscreteTopology.eq_top α
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | basic _ h => exact False.elim h
    | univ => exact .inr rfl
    | inter _ _ _ _ h₁ h₂ =>
      rcases h₁ with (rfl | rfl) <;> rcases h₂ with (rfl | rfl) <;> simp
    | sUnion _ _ ih => exact sUnion_mem_empty_univ ih
  · rintro (rfl | rfl)
    exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]

/--
theorem `TopologicalSpace.isOpen_top_iff` / 定理 `TopologicalSpace.isOpen_top_iff`

English:
theorem TopologicalSpace.isOpen_top_iff
  given: {α} (U : Set α)
  statement: IsOpen[⊤] U ↔ U = ∅ ∨ U = univ
  proof: letI : TopologicalSpace α := ⊤; IndiscreteTopology.isOpen_iff _

中文:
定理 拓扑空间.isOpen_top_iff
  条件: {α} (U : 集合 α)
  结论: 是开集[⊤] U ↔ U = ∅ ∨ U = univ
  证明: letI : TopologicalSpace α := ⊤; IndiscreteTopology.isOpen_iff _

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.isOpen_iff, TopologicalSpace, isOpen_iff
-/
theorem TopologicalSpace.isOpen_top_iff {α} (U : Set α) : IsOpen[⊤] U ↔ U = ∅ ∨ U = univ :=
  letI : TopologicalSpace α := ⊤; IndiscreteTopology.isOpen_iff _

/--
theorem `IndiscreteTopology.isClosed_iff` / 定理 `IndiscreteTopology.isClosed_iff`

English:
theorem IndiscreteTopology.isClosed_iff
  given: [IndiscreteTopology α] (C : Set α)
  proof: by
  simp [← isOpen_compl_iff, IndiscreteTopology.isOpen_iff, Or.comm]

中文:
定理 Indiscrete拓扑.isClosed_iff
  条件: [Indiscrete拓扑 α] (C : 集合 α)
  证明: by
  simp [← isOpen_compl_iff, IndiscreteTopology.isOpen_iff, Or.comm]

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.isOpen_iff, Or.comm, isOpen_compl_iff, isOpen_iff
-/
theorem IndiscreteTopology.isClosed_iff [IndiscreteTopology α] (C : Set α) :
    IsClosed C ↔ C = ∅ ∨ C = Set.univ := by
  simp [← isOpen_compl_iff, IndiscreteTopology.isOpen_iff, Or.comm]

/--
theorem `dense_indiscrete` / 定理 `dense_indiscrete`

English:
theorem dense_indiscrete
  given: [IndiscreteTopology α] {s : Set α} (h : s.Nonempty)
  statement: Dense s
  proof: by
  simp [dense_iff_inter_open, IndiscreteTopology.isOpen_iff, h]

中文:
定理 dense_indiscrete
  条件: [Indiscrete拓扑 α] {s : 集合 α} (h : s.非空)
  结论: 稠密 s
  证明: by
  simp [dense_iff_inter_open, IndiscreteTopology.isOpen_iff, h]

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.isOpen_iff, dense_iff_inter_open, isOpen_iff
-/
theorem dense_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) : Dense s := by
  simp [dense_iff_inter_open, IndiscreteTopology.isOpen_iff, h]

/--
theorem `closure_indiscrete` / 定理 `closure_indiscrete`

English:
theorem closure_indiscrete
  given: [IndiscreteTopology α] {s : Set α} (h : s.Nonempty)
  proof: Dense.closure_eq (dense_indiscrete h)

中文:
定理 closure_indiscrete
  条件: [Indiscrete拓扑 α] {s : 集合 α} (h : s.非空)
  证明: Dense.closure_eq (dense_indiscrete h)

Depends on / 依赖: Dense.closure_eq, closure_eq, dense_indiscrete
-/
theorem closure_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) :
    closure s = Set.univ := Dense.closure_eq (dense_indiscrete h)

/-- Every function to the indiscrete topology is continuous -/
@[fun_prop]
/--
theorem `continuous_of_indiscreteTopology` / 定理 `continuous_of_indiscreteTopology`

English:
theorem continuous_of_indiscreteTopology
  statement: {β} [TopologicalSpace β] [IndiscreteTopology β]
  proof: by simp [IndiscreteTopology.isOpen_iff]

中文:
定理 continuous_of_indiscreteTopology
  结论: {β} [拓扑空间 β] [Indiscrete拓扑 β]
  证明: by simp [IndiscreteTopology.isOpen_iff]

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.isOpen_iff, isOpen_iff
-/
theorem continuous_of_indiscreteTopology {β} [TopologicalSpace β] [IndiscreteTopology β]
    {f : α -> β} : Continuous f where
  isOpen_preimage := by simp [IndiscreteTopology.isOpen_iff]

/--
Definition of `DiscreteTopology` / `DiscreteTopology` 的定义

English:
class DiscreteTopology
  parameters: (α : Type*) [t : TopologicalSpace α]
  axioms and operations (1):
    - eq_bot : t = ⊥

中文:
类 离散拓扑
  参数: (α : 类型) [t : 拓扑空间 α]
  公理与运算 (1 个):
    - eq_bot : t = ⊥
-/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥

/--
theorem `discreteTopology_bot` / 定理 `discreteTopology_bot`

English:
theorem discreteTopology_bot
  given: (α : Type*)
  statement: @DiscreteTopology α ⊥
  proof: @DiscreteTopology.mk α ⊥ rfl

中文:
定理 discreteTopology_bot
  条件: (α : 类型)
  结论: @离散拓扑 α ⊥
  证明: @DiscreteTopology.mk α ⊥ rfl

Depends on / 依赖: DiscreteTopology, DiscreteTopology.mk
-/
theorem discreteTopology_bot (α : Type*) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl

section DiscreteTopology

variable [TopologicalSpace α] [DiscreteTopology α] {β : Type*}

@[simp]
/--
theorem `isOpen_discrete` / 定理 `isOpen_discrete`

English:
theorem isOpen_discrete
  given: (s : Set α)
  statement: IsOpen s
  proof: (@DiscreteTopology.eq_bot α _).symm ▸ trivial

中文:
定理 isOpen_discrete
  条件: (s : 集合 α)
  结论: 是开集 s
  证明: (@DiscreteTopology.eq_bot α _).symm ▸ trivial

Depends on / 依赖: DiscreteTopology, DiscreteTopology.eq_bot, eq_bot
-/
theorem isOpen_discrete (s : Set α) : IsOpen s := (@DiscreteTopology.eq_bot α _).symm ▸ trivial

/--
theorem `isClosed_discrete` / 定理 `isClosed_discrete`

English:
theorem isClosed_discrete
  given: (s : Set α)
  statement: IsClosed s
  proof: ⟨isOpen_discrete _⟩

中文:
定理 isClosed_discrete
  条件: (s : 集合 α)
  结论: 是闭集 s
  证明: ⟨isOpen_discrete _⟩
-/
@[simp] theorem isClosed_discrete (s : Set α) : IsClosed s := ⟨isOpen_discrete _⟩

/--
theorem `closure_discrete` / 定理 `closure_discrete`

English:
theorem closure_discrete
  given: (s : Set α)
  statement: closure s = s
  proof: (isClosed_discrete _).closure_eq

中文:
定理 closure_discrete
  条件: (s : 集合 α)
  结论: closure s = s
  证明: (isClosed_discrete _).closure_eq

Depends on / 依赖: closure_eq, isClosed_discrete
-/
theorem closure_discrete (s : Set α) : closure s = s := (isClosed_discrete _).closure_eq

/--
theorem `dense_discrete` / 定理 `dense_discrete`

English:
theorem dense_discrete
  given: {s : Set α}
  statement: Dense s ↔ s = univ
  proof: by simp [dense_iff_closure_eq]

@[simp]

中文:
定理 dense_discrete
  条件: {s : 集合 α}
  结论: 稠密 s ↔ s = univ
  证明: by simp [dense_iff_closure_eq]

@[simp]
-/
@[simp] theorem dense_discrete {s : Set α} : Dense s ↔ s = univ := by simp [dense_iff_closure_eq]

@[simp]
/--
theorem `denseRange_discrete` / 定理 `denseRange_discrete`

English:
theorem denseRange_discrete
  given: {ι : Type*} {f : ι -> α}
  statement: DenseRange f ↔ Surjective f
  proof: by
  rw [DenseRange]; rw [dense_discrete]; rw [range_eq_univ]

@[nontriviality, continuity, fun_prop]

中文:
定理 denseRange_discrete
  条件: {ι : 类型} {f : ι -> α}
  结论: DenseRange f ↔ 满射 f
  证明: by
  rw [DenseRange]; rw [dense_discrete]; rw [range_eq_univ]

@[nontriviality, continuity, fun_prop]

Depends on / 依赖: DenseRange, dense_discrete, range_eq_univ
-/
theorem denseRange_discrete {ι : Type*} {f : ι -> α} : DenseRange f ↔ Surjective f := by
  rw [DenseRange]; rw [dense_discrete]; rw [range_eq_univ]

@[nontriviality, continuity, fun_prop]
/--
theorem `continuous_of_discreteTopology` / 定理 `continuous_of_discreteTopology`

English:
theorem continuous_of_discreteTopology
  given: [TopologicalSpace β] {f : α -> β}
  statement: Continuous f
  proof: continuous_def.2 fun _ _ => isOpen_discrete _

中文:
定理 continuous_of_discreteTopology
  条件: [拓扑空间 β] {f : α -> β}
  结论: 连续 f
  证明: continuous_def.2 fun _ _ => isOpen_discrete _

Depends on / 依赖: continuous_def, isOpen_discrete
-/
theorem continuous_of_discreteTopology [TopologicalSpace β] {f : α -> β} : Continuous f :=
  continuous_def.2 fun _ _ => isOpen_discrete _

/--
theorem `continuous_discrete_rng` / 定理 `continuous_discrete_rng`

English:
theorem continuous_discrete_rng
  statement: {α} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β]
  proof: ⟨fun h _ => (isOpen_discrete _).preimage h, fun h => ⟨fun s _ => by
    rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
    exact isOpen_biUnion fun _ _ => h _⟩⟩

@[simp]

中文:
定理 continuous_discrete_rng
  结论: {α} [拓扑空间 α] [拓扑空间 β] [离散拓扑 β]
  证明: ⟨fun h _ => (isOpen_discrete _).preimage h, fun h => ⟨fun s _ => by
    rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
    exact isOpen_biUnion fun _ _ => h _⟩⟩

@[simp]

Depends on / 依赖: biUnion_of_singleton, isOpen_biUnion, isOpen_discrete, preimage
-/
theorem continuous_discrete_rng {α} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β]
    {f : α -> β} : Continuous f ↔ forall b : β, IsOpen (f ⁻¹' {b}) :=
  ⟨fun h _ => (isOpen_discrete _).preimage h, fun h => ⟨fun s _ => by
    rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
    exact isOpen_biUnion fun _ _ => h _⟩⟩

@[simp]
/--
theorem `nhds_discrete` / 定理 `nhds_discrete`

English:
theorem nhds_discrete
  given: (α : Type*) [TopologicalSpace α] [DiscreteTopology α]
  statement: @nhds α _ = pure
  proof: le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds

中文:
定理 nhds_discrete
  条件: (α : 类型) [拓扑空间 α] [离散拓扑 α]
  结论: @邻域滤子 α _ = pure
  证明: le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds

Depends on / 依赖: isOpen_discrete, le_antisymm, mem_nhds, pure_le_nhds
-/
theorem nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds

/--
theorem `mem_nhds_discrete` / 定理 `mem_nhds_discrete`

English:
theorem mem_nhds_discrete
  given: {x : α} {s : Set α}
  proof: by rw [nhds_discrete, mem_pure]

中文:
定理 mem_nhds_discrete
  条件: {x : α} {s : 集合 α}
  证明: by rw [nhds_discrete, mem_pure]

Depends on / 依赖: mem_pure, nhds_discrete
-/
theorem mem_nhds_discrete {x : α} {s : Set α} :
    s in 𝓝 x ↔ x in s := by rw [nhds_discrete, mem_pure]

end DiscreteTopology

/--
theorem `le_of_nhds_le_nhds` / 定理 `le_of_nhds_le_nhds`

English:
theorem le_of_nhds_le_nhds
  given: (h : forall x, @nhds α t₁ x <= @nhds α t₂ x)
  statement: t₁ <= t₂
  proof: fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁]; rw [@isOpen_iff_mem_nhds _ t₂]
  exact fun hs a ha => h _ (hs _ ha)

中文:
定理 le_of_nhds_le_nhds
  条件: (h : 对任意 x, @邻域滤子 α t₁ x <= @邻域滤子 α t₂ x)
  结论: t₁ <= t₂
  证明: fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁]; rw [@isOpen_iff_mem_nhds _ t₂]
  exact fun hs a ha => h _ (hs _ ha)

Depends on / 依赖: isOpen_iff_mem_nhds
-/
theorem le_of_nhds_le_nhds (h : forall x, @nhds α t₁ x <= @nhds α t₂ x) : t₁ <= t₂ := fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁]; rw [@isOpen_iff_mem_nhds _ t₂]
  exact fun hs a ha => h _ (hs _ ha)

/--
theorem `eq_bot_of_singletons_open` / 定理 `eq_bot_of_singletons_open`

English:
theorem eq_bot_of_singletons_open
  given: {t : TopologicalSpace α} (h : forall x, IsOpen[t] {x})
  statement: t = ⊥
  proof: bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x

中文:
定理 eq_bot_of_singletons_open
  条件: {t : 拓扑空间 α} (h : 对任意 x, 是开集[t] {x})
  结论: t = ⊥
  证明: bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x

Depends on / 依赖: biUnion_of_singleton, bot_unique, isOpen_biUnion
-/
theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : forall x, IsOpen[t] {x}) : t = ⊥ :=
  bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x

/--
theorem `discreteTopology_iff_forall_isOpen` / 定理 `discreteTopology_iff_forall_isOpen`

English:
theorem discreteTopology_iff_forall_isOpen
  given: [TopologicalSpace α]
  proof: ⟨@isOpen_discrete _ _, fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩⟩

中文:
定理 discreteTopology_iff_对任意_isOpen
  条件: [拓扑空间 α]
  证明: ⟨@isOpen_discrete _ _, fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩⟩

Depends on / 依赖: eq_bot_of_singletons_open, isOpen_discrete
-/
theorem discreteTopology_iff_forall_isOpen [TopologicalSpace α] :
    DiscreteTopology α ↔ forall s : Set α, IsOpen s :=
  ⟨@isOpen_discrete _ _, fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩⟩

/--
theorem `discreteTopology_iff_forall_isClosed` / 定理 `discreteTopology_iff_forall_isClosed`

English:
theorem discreteTopology_iff_forall_isClosed
  given: [TopologicalSpace α]
  proof: discreteTopology_iff_forall_isOpen.trans compl_surjective.forall.trans forall_congr' fun _ =>
    isOpen_compl_iff

中文:
定理 discreteTopology_iff_对任意_isClosed
  条件: [拓扑空间 α]
  证明: discreteTopology_iff_forall_isOpen.trans compl_surjective.forall.trans forall_congr' fun _ =>
    isOpen_compl_iff

Depends on / 依赖: compl_surjective, compl_surjective.forall.trans, discreteTopology_iff_forall_isOpen, discreteTopology_iff_forall_isOpen.trans, forall_congr, isOpen_compl_iff
-/
theorem discreteTopology_iff_forall_isClosed [TopologicalSpace α] :
    DiscreteTopology α ↔ forall s : Set α, IsClosed s :=
discreteTopology_iff_forall_isOpen.trans compl_surjective.forall.trans forall_congr' fun _ =>
    isOpen_compl_iff

/--
theorem `discreteTopology_iff_isOpen_singleton` / 定理 `discreteTopology_iff_isOpen_singleton`

English:
theorem discreteTopology_iff_isOpen_singleton
  given: [TopologicalSpace α]
  proof: ⟨fun _ _ => isOpen_discrete _, fun h => ⟨eq_bot_of_singletons_open h⟩⟩

中文:
定理 discreteTopology_iff_isOpen_singleton
  条件: [拓扑空间 α]
  证明: ⟨fun _ _ => isOpen_discrete _, fun h => ⟨eq_bot_of_singletons_open h⟩⟩

Depends on / 依赖: eq_bot_of_singletons_open, isOpen_discrete
-/
theorem discreteTopology_iff_isOpen_singleton [TopologicalSpace α] :
    DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Set α)) :=
  ⟨fun _ _ => isOpen_discrete _, fun h => ⟨eq_bot_of_singletons_open h⟩⟩

/--
theorem `DiscreteTopology.of_finite_of_isClosed_singleton` / 定理 `DiscreteTopology.of_finite_of_isClosed_singleton`

English:
theorem DiscreteTopology.of_finite_of_isClosed_singleton
  statement: [TopologicalSpace α] [Finite α]
  proof: discreteTopology_iff_forall_isClosed.mpr fun s =>
    s.iUnion_of_singleton_coe ▸ isClosed_iUnion_of_finite fun _ => h _

中文:
定理 离散拓扑.of_finite_of_isClosed_singleton
  结论: [拓扑空间 α] [有限 α]
  证明: discreteTopology_iff_forall_isClosed.mpr fun s =>
    s.iUnion_of_singleton_coe ▸ isClosed_iUnion_of_finite fun _ => h _

Depends on / 依赖: discreteTopology_iff_forall_isClosed, discreteTopology_iff_forall_isClosed.mpr, iUnion_of_singleton_coe, isClosed_iUnion_of_finite, s.iUnion_of_singleton_coe
-/
theorem DiscreteTopology.of_finite_of_isClosed_singleton [TopologicalSpace α] [Finite α]
    (h : forall a : α, IsClosed {a}) : DiscreteTopology α :=
  discreteTopology_iff_forall_isClosed.mpr fun s =>
    s.iUnion_of_singleton_coe ▸ isClosed_iUnion_of_finite fun _ => h _

/--
theorem `discreteTopology_iff_singleton_mem_nhds` / 定理 `discreteTopology_iff_singleton_mem_nhds`

English:
theorem discreteTopology_iff_singleton_mem_nhds
  given: [TopologicalSpace α]
  proof: by
  simp only [discreteTopology_iff_isOpen_singleton,
    isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]

中文:
定理 discreteTopology_iff_singleton_mem_nhds
  条件: [拓扑空间 α]
  证明: by
  simp only [discreteTopology_iff_isOpen_singleton,
    isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]

Depends on / 依赖: discreteTopology_iff_isOpen_singleton, forall_eq, isOpen_iff_mem_nhds, mem_singleton_iff
-/
theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ forall x : α, {x} in 𝓝 x := by
  simp only [discreteTopology_iff_isOpen_singleton,
    isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]

/--
theorem `discreteTopology_iff_nhds` / 定理 `discreteTopology_iff_nhds`

English:
theorem discreteTopology_iff_nhds
  given: [TopologicalSpace α]
  proof: by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  apply forall_congr' (fun x => ?_)
  simp [le_antisymm_iff, pure_le_nhds x]

中文:
定理 discreteTopology_iff_nhds
  条件: [拓扑空间 α]
  证明: by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  apply forall_congr' (fun x => ?_)
  simp [le_antisymm_iff, pure_le_nhds x]

Depends on / 依赖: discreteTopology_iff_singleton_mem_nhds, forall_congr, le_antisymm_iff, pure_le_nhds
-/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ forall x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  apply forall_congr' (fun x => ?_)
  simp [le_antisymm_iff, pure_le_nhds x]

/--
theorem `discreteTopology_iff_nhds_ne` / 定理 `discreteTopology_iff_nhds_ne`

English:
theorem discreteTopology_iff_nhds_ne
  given: [TopologicalSpace α]
  proof: by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]

中文:
定理 discreteTopology_iff_nhds_ne
  条件: [拓扑空间 α]
  证明: by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]

Depends on / 依赖: compl_compl, discreteTopology_iff_singleton_mem_nhds, inf_principal_eq_bot, nhdsWithin
-/
theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ forall x : α, 𝓝[!=] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]

/--
theorem `DiscreteTopology.of_continuous_injective` / 定理 `DiscreteTopology.of_continuous_injective`

English:
theorem DiscreteTopology.of_continuous_injective
  proof: discreteTopology_iff_forall_isOpen.2 fun s =>
    hinj.preimage_image s ▸ (isOpen_discrete _).preimage hc

中文:
定理 离散拓扑.of_continuous_injective
  证明: discreteTopology_iff_forall_isOpen.2 fun s =>
    hinj.preimage_image s ▸ (isOpen_discrete _).preimage hc

Depends on / 依赖: discreteTopology_iff_forall_isOpen, hinj.preimage_image, isOpen_discrete, preimage, preimage_image
-/
theorem DiscreteTopology.of_continuous_injective
    {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β] {f : α -> β}
    (hc : Continuous f) (hinj : Injective f) : DiscreteTopology α :=
  discreteTopology_iff_forall_isOpen.2 fun s =>
    hinj.preimage_image s ▸ (isOpen_discrete _).preimage hc

end Lattice

section GaloisConnection

variable {α β γ : Type*}

/--
theorem `isOpen_induced_iff` / 定理 `isOpen_induced_iff`

English:
theorem isOpen_induced_iff
  given: [t : TopologicalSpace β] {s : Set α} {f : α -> β}
  proof: Iff.rfl

中文:
定理 isOpen_induced_iff
  条件: [t : 拓扑空间 β] {s : 集合 α} {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α -> β} :
    IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

/--
theorem `isClosed_induced_iff` / 定理 `isClosed_induced_iff`

English:
theorem isClosed_induced_iff
  given: [t : TopologicalSpace β] {s : Set α} {f : α -> β}
  proof: by
  let := t.induced f
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])

中文:
定理 isClosed_induced_iff
  条件: [t : 拓扑空间 β] {s : 集合 α} {f : α -> β}
  证明: by
  let := t.induced f
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])

Depends on / 依赖: compl_inj_iff, compl_surjective, compl_surjective.exists.trans, induced, isOpen_compl_iff, isOpen_induced_iff, preimage_compl, t.induced
-/
theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α -> β} :
    IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s := by
  let := t.induced f
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])

/--
theorem `isOpen_coinduced` / 定理 `isOpen_coinduced`

English:
theorem isOpen_coinduced
  given: {t : TopologicalSpace α} {s : Set β} {f : α -> β}
  proof: Iff.rfl

中文:
定理 isOpen_coinduced
  条件: {t : 拓扑空间 α} {s : 集合 β} {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α -> β} :
    IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl

/--
theorem `isClosed_coinduced` / 定理 `isClosed_coinduced`

English:
theorem isClosed_coinduced
  given: {t : TopologicalSpace α} {s : Set β} {f : α -> β}
  proof: by
  simp only [← isOpen_compl_iff, isOpen_coinduced (f := f), preimage_compl]

中文:
定理 isClosed_coinduced
  条件: {t : 拓扑空间 α} {s : 集合 β} {f : α -> β}
  证明: by
  simp only [← isOpen_compl_iff, isOpen_coinduced (f := f), preimage_compl]

Depends on / 依赖: isOpen_coinduced, isOpen_compl_iff, preimage_compl
-/
theorem isClosed_coinduced {t : TopologicalSpace α} {s : Set β} {f : α -> β} :
    IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_coinduced (f := f), preimage_compl]

/--
theorem `preimage_nhds_coinduced` / 定理 `preimage_nhds_coinduced`

English:
theorem preimage_nhds_coinduced
  statement: [TopologicalSpace α] {π : α -> β} {s : Set β} {a : α}
  proof: by
  let := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

中文:
定理 preimage_nhds_coinduced
  结论: [拓扑空间 α] {π : α -> β} {s : 集合 β} {a : α}
  证明: by
  let := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

Depends on / 依赖: Set.preimage_mono, TopologicalSpace, TopologicalSpace.coinduced, V_op, coinduced, mem_V, mem_nhds_iff, mem_nhds_iff.mp, mem_nhds_iff.mpr, preimage_mono
-/
theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α -> β} {s : Set β} {a : α}
    (hs : s in @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s in 𝓝 a := by
  let := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α -> β} {g : β -> α}

/--
theorem `Continuous.coinduced_le` / 定理 `Continuous.coinduced_le`

English:
theorem Continuous.coinduced_le
  given: (h : Continuous[t, t'] f)
  statement: t.coinduced f <= t'
  proof: (@continuous_def α β t t').1 h

中文:
定理 连续.coinduced_le
  条件: (h : 连续[t, t'] f)
  结论: t.coinduced f <= t'
  证明: (@continuous_def α β t t').1 h

Depends on / 依赖: continuous_def
-/
theorem Continuous.coinduced_le (h : Continuous[t, t'] f) : t.coinduced f <= t' :=
  (@continuous_def α β t t').1 h

/--
theorem `coinduced_le_iff_le_induced` / 定理 `coinduced_le_iff_le_induced`

English:
theorem coinduced_le_iff_le_induced
  statement: {f : α -> β} {tα : TopologicalSpace α}
  proof: ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩

中文:
定理 coinduced_le_iff_le_induced
  结论: {f : α -> β} {tα : 拓扑空间 α}
  证明: ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩
-/
theorem coinduced_le_iff_le_induced {f : α -> β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <= tβ.induced f :=
  ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩

/--
theorem `Continuous.le_induced` / 定理 `Continuous.le_induced`

English:
theorem Continuous.le_induced
  given: (h : Continuous[t, t'] f)
  statement: t <= t'.induced f
  proof: coinduced_le_iff_le_induced.1 h.coinduced_le

中文:
定理 连续.le_induced
  条件: (h : 连续[t, t'] f)
  结论: t <= t'.induced f
  证明: coinduced_le_iff_le_induced.1 h.coinduced_le

Depends on / 依赖: coinduced_le, coinduced_le_iff_le_induced, h.coinduced_le
-/
theorem Continuous.le_induced (h : Continuous[t, t'] f) : t <= t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le

/--
theorem `gc_coinduced_induced` / 定理 `gc_coinduced_induced`

English:
theorem gc_coinduced_induced
  given: (f : α -> β)
  proof: fun _ _ =>
  coinduced_le_iff_le_induced

@[gcongr]

中文:
定理 gc_coinduced_induced
  条件: (f : α -> β)
  证明: fun _ _ =>
  coinduced_le_iff_le_induced

@[gcongr]
-/
theorem gc_coinduced_induced (f : α -> β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun _ _ =>
  coinduced_le_iff_le_induced

@[gcongr]
/--
theorem `induced_mono` / 定理 `induced_mono`

English:
theorem induced_mono
  given: (h : t₁ <= t₂)
  statement: t₁.induced g <= t₂.induced g
  proof: (gc_coinduced_induced g).monotone_u h

@[gcongr]

中文:
定理 induced_mono
  条件: (h : t₁ <= t₂)
  结论: t₁.induced g <= t₂.induced g
  证明: (gc_coinduced_induced g).monotone_u h

@[gcongr]

Depends on / 依赖: gc_coinduced_induced, monotone_u
-/
theorem induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h

@[gcongr]
/--
theorem `coinduced_mono` / 定理 `coinduced_mono`

English:
theorem coinduced_mono
  given: (h : t₁ <= t₂)
  statement: t₁.coinduced f <= t₂.coinduced f
  proof: (gc_coinduced_induced f).monotone_l h

@[simp]

中文:
定理 coinduced_mono
  条件: (h : t₁ <= t₂)
  结论: t₁.coinduced f <= t₂.coinduced f
  证明: (gc_coinduced_induced f).monotone_l h

@[simp]

Depends on / 依赖: gc_coinduced_induced, monotone_l
-/
theorem coinduced_mono (h : t₁ <= t₂) : t₁.coinduced f <= t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
/--
theorem `induced_top` / 定理 `induced_top`

English:
theorem induced_top
  statement: (⊤ : TopologicalSpace α).induced g = ⊤
  proof: (gc_coinduced_induced g).u_top

@[simp]

中文:
定理 induced_top
  结论: (⊤ : 拓扑空间 α).induced g = ⊤
  证明: (gc_coinduced_induced g).u_top

@[simp]

Depends on / 依赖: gc_coinduced_induced, u_top
-/
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top

@[simp]
/--
theorem `induced_inf` / 定理 `induced_inf`

English:
theorem induced_inf
  statement: (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g
  proof: (gc_coinduced_induced g).u_inf

@[simp]

中文:
定理 induced_inf
  结论: (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g
  证明: (gc_coinduced_induced g).u_inf

@[simp]

Depends on / 依赖: gc_coinduced_induced, u_inf
-/
theorem induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
  (gc_coinduced_induced g).u_inf

@[simp]
/--
theorem `induced_iInf` / 定理 `induced_iInf`

English:
theorem induced_iInf
  given: {ι : Sort w} {t : ι -> TopologicalSpace α}
  proof: (gc_coinduced_induced g).u_iInf

@[simp]

中文:
定理 induced_iInf
  条件: {ι : 类型层 w} {t : ι -> 拓扑空间 α}
  证明: (gc_coinduced_induced g).u_iInf

@[simp]

Depends on / 依赖: gc_coinduced_induced, u_iInf
-/
theorem induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_iInf

@[simp]
/--
theorem `induced_sInf` / 定理 `induced_sInf`

English:
theorem induced_sInf
  given: {s : Set (TopologicalSpace α)}
  proof: by
  rw [sInf_eq_iInf']; rw [sInf_image']; rw [induced_iInf]

@[simp]

中文:
定理 induced_sInf
  条件: {s : 集合 (拓扑空间 α)}
  证明: by
  rw [sInf_eq_iInf']; rw [sInf_image']; rw [induced_iInf]

@[simp]

Depends on / 依赖: induced_iInf, sInf_eq_iInf, sInf_image
-/
theorem induced_sInf {s : Set (TopologicalSpace α)} :
    TopologicalSpace.induced g (sInf s) = sInf (TopologicalSpace.induced g '' s) := by
  rw [sInf_eq_iInf']; rw [sInf_image']; rw [induced_iInf]

@[simp]
/--
theorem `coinduced_bot` / 定理 `coinduced_bot`

English:
theorem coinduced_bot
  statement: (⊥ : TopologicalSpace α).coinduced f = ⊥
  proof: (gc_coinduced_induced f).l_bot

@[simp]

中文:
定理 coinduced_bot
  结论: (⊥ : 拓扑空间 α).coinduced f = ⊥
  证明: (gc_coinduced_induced f).l_bot

@[simp]

Depends on / 依赖: gc_coinduced_induced, l_bot
-/
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
/--
theorem `coinduced_sup` / 定理 `coinduced_sup`

English:
theorem coinduced_sup
  statement: (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f
  proof: (gc_coinduced_induced f).l_sup

@[simp]

中文:
定理 coinduced_sup
  结论: (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f
  证明: (gc_coinduced_induced f).l_sup

@[simp]

Depends on / 依赖: gc_coinduced_induced, l_sup
-/
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
/--
theorem `coinduced_iSup` / 定理 `coinduced_iSup`

English:
theorem coinduced_iSup
  given: {ι : Sort w} {t : ι -> TopologicalSpace α}
  proof: (gc_coinduced_induced f).l_iSup

@[simp]

中文:
定理 coinduced_iSup
  条件: {ι : 类型层 w} {t : ι -> 拓扑空间 α}
  证明: (gc_coinduced_induced f).l_iSup

@[simp]

Depends on / 依赖: gc_coinduced_induced, l_iSup
-/
theorem coinduced_iSup {ι : Sort w} {t : ι -> TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_iSup

@[simp]
/--
theorem `coinduced_sSup` / 定理 `coinduced_sSup`

English:
theorem coinduced_sSup
  given: {s : Set (TopologicalSpace α)}
  proof: by
  rw [sSup_eq_iSup']; rw [sSup_image']; rw [coinduced_iSup]

中文:
定理 coinduced_sSup
  条件: {s : 集合 (拓扑空间 α)}
  证明: by
  rw [sSup_eq_iSup']; rw [sSup_image']; rw [coinduced_iSup]

Depends on / 依赖: coinduced_iSup, sSup_eq_iSup, sSup_image
-/
theorem coinduced_sSup {s : Set (TopologicalSpace α)} :
    TopologicalSpace.coinduced f (sSup s) = sSup ((TopologicalSpace.coinduced f) '' s) := by
  rw [sSup_eq_iSup']; rw [sSup_image']; rw [coinduced_iSup]

/--
theorem `induced_id` / 定理 `induced_id`

English:
theorem induced_id
  given: [t : TopologicalSpace α]
  statement: t.induced id = t
  proof: TopologicalSpace.ext
funext fun s => propext ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

中文:
定理 induced_id
  条件: [t : 拓扑空间 α]
  结论: t.induced id = t
  证明: TopologicalSpace.ext
funext fun s => propext ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext, propext
-/
theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
TopologicalSpace.ext
funext fun s => propext ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

/--
theorem `induced_fun_id` / 定理 `induced_fun_id`

English:
theorem induced_fun_id
  given: {t : TopologicalSpace α}
  statement: t.induced (·) = t
  proof: induced_id

中文:
定理 induced_fun_id
  条件: {t : 拓扑空间 α}
  结论: t.induced (·) = t
  证明: induced_id

Depends on / 依赖: induced_id
-/
theorem induced_fun_id {t : TopologicalSpace α} : t.induced (·) = t := induced_id

/--
theorem `induced_compose` / 定理 `induced_compose`

English:
theorem induced_compose
  given: {tγ : TopologicalSpace γ} {f : α -> β} {g : β -> γ}
  proof: TopologicalSpace.ext
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

中文:
定理 induced_compose
  条件: {tγ : 拓扑空间 γ} {f : α -> β} {g : β -> γ}
  证明: TopologicalSpace.ext
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext, preimage, propext
-/
theorem induced_compose {tγ : TopologicalSpace γ} {f : α -> β} {g : β -> γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
TopologicalSpace.ext
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

/--
theorem `induced_const` / 定理 `induced_const`

English:
theorem induced_const
  given: [t : TopologicalSpace α] {x : α}
  statement: (t.induced fun _ : β => x) = ⊤
  proof: le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced

中文:
定理 induced_const
  条件: [t : 拓扑空间 α] {x : α}
  结论: (t.induced fun _ : β => x) = ⊤
  证明: le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced

Depends on / 依赖: continuous_const, le_antisymm, le_induced, le_top
-/
theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun _ : β => x) = ⊤ :=
  le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced

/--
theorem `coinduced_id` / 定理 `coinduced_id`

English:
theorem coinduced_id
  given: [t : TopologicalSpace α]
  statement: t.coinduced id = t
  proof: TopologicalSpace.ext rfl

中文:
定理 coinduced_id
  条件: [t : 拓扑空间 α]
  结论: t.coinduced id = t
  证明: TopologicalSpace.ext rfl

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext
-/
theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  TopologicalSpace.ext rfl

/--
theorem `coinduced_compose` / 定理 `coinduced_compose`

English:
theorem coinduced_compose
  given: [tα : TopologicalSpace α] {f : α -> β} {g : β -> γ}
  proof: TopologicalSpace.ext rfl

中文:
定理 coinduced_compose
  条件: [tα : 拓扑空间 α] {f : α -> β} {g : β -> γ}
  证明: TopologicalSpace.ext rfl

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext
-/
theorem coinduced_compose [tα : TopologicalSpace α] {f : α -> β} {g : β -> γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  TopologicalSpace.ext rfl

/--
theorem `Equiv.induced_symm` / 定理 `Equiv.induced_symm`

English:
theorem Equiv.induced_symm
  given: {α β : Type*} (e : α ≃ β)
  proof: by
  ext t U
  rw [isOpen_induced_iff]; rw [isOpen_coinduced]
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, Equiv.image_symm_eq_preimage]

中文:
定理 等价.induced_symm
  条件: {α β : 类型} (e : α ≃ β)
  证明: by
  ext t U
  rw [isOpen_induced_iff]; rw [isOpen_coinduced]
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, Equiv.image_symm_eq_preimage]

Depends on / 依赖: Equiv.image_symm_eq_preimage, e.symm.preimage_eq_iff_eq_image, exists_eq_right, image_symm_eq_preimage, isOpen_coinduced, isOpen_induced_iff, preimage_eq_iff_eq_image
-/
theorem Equiv.induced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e := by
  ext t U
  rw [isOpen_induced_iff]; rw [isOpen_coinduced]
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, Equiv.image_symm_eq_preimage]

/--
theorem `Equiv.coinduced_symm` / 定理 `Equiv.coinduced_symm`

English:
theorem Equiv.coinduced_symm
  given: {α β : Type*} (e : α ≃ β)
  proof: e.symm.induced_symm.symm

中文:
定理 等价.coinduced_symm
  条件: {α β : 类型} (e : α ≃ β)
  证明: e.symm.induced_symm.symm

Depends on / 依赖: e.symm.induced_symm.symm, induced_symm
-/
theorem Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e :=
  e.symm.induced_symm.symm

/--
lemma `WithTopology.topology_eq_induced` / 引理 `WithTopology.topology_eq_induced`

English:
lemma WithTopology.topology_eq_induced
  given: {X : Type*} (t : TopologicalSpace X)
  proof: congrFun (WithTopology.equiv X t).coinduced_symm t

中文:
引理 With拓扑.topology_eq_induced
  条件: {X : 类型} (t : 拓扑空间 X)
  证明: congrFun (WithTopology.equiv X t).coinduced_symm t

Depends on / 依赖: WithTopology, WithTopology.equiv, coinduced_symm
-/
lemma WithTopology.topology_eq_induced {X : Type*} (t : TopologicalSpace X) :
    instTopologicalSpace X t = .induced ofTopology t :=
  congrFun (WithTopology.equiv X t).coinduced_symm t

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

/--
Instance `inhabitedTopologicalSpace` / 实例 `inhabitedTopologicalSpace`

English:
instance inhabitedTopologicalSpace
  signature: {α : Type u}
  body: ⟨⊥⟩

中文:
实例 inhabitedTopologicalSpace
  签名: {α : 类型u}
  定义体: ⟨⊥⟩
-/
instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩

instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] :
    Unique (TopologicalSpace α) where
  default := ⊥
  uniq t :=
    eq_bot_of_singletons_open fun x =>
      Subsingleton.set_cases (@isOpen_empty _ t) (@isOpen_univ _ t) ({x} : Set α)

instance (priority := 100) Subsingleton.discreteTopology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Subsingleton α] : IndiscreteTopology α where
  body: Subsingleton.elim _ _

中文:
实例 [拓扑空间
  签名: α] [子单例 α] : Indiscrete拓扑 α where
  定义体: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [TopologicalSpace α] [Subsingleton α] : IndiscreteTopology α where
  eq_top := Subsingleton.elim _ _

variable (α) in
/--
lemma `Nontrivial.of_nontrivialTopology` / 引理 `Nontrivial.of_nontrivialTopology`

English:
lemma Nontrivial.of_nontrivialTopology
  given: [TopologicalSpace α] [h : NontrivialTopology α]
  proof: by contrapose! h; infer_instance

中文:
引理 非平凡.of_nontrivialTopology
  条件: [拓扑空间 α] [h : 非平凡拓扑 α]
  证明: by contrapose! h; infer_instance

Depends on / 依赖: contrapose, infer_instance
-/
lemma Nontrivial.of_nontrivialTopology [TopologicalSpace α] [h : NontrivialTopology α] :
    Nontrivial α := by contrapose! h; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Empty
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 空
  定义体: ⊥
-/
instance : TopologicalSpace Empty := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology Empty
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 空
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology Empty := ⟨rfl⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IndiscreteTopology Empty
  body: inferInstance

中文:
实例 :
  签名: Indiscrete拓扑 空
  定义体: inferInstance
-/
instance : IndiscreteTopology Empty := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace PEmpty
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 命题空
  定义体: ⊥
-/
instance : TopologicalSpace PEmpty := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology PEmpty
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 命题空
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology PEmpty := ⟨rfl⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IndiscreteTopology PEmpty
  body: inferInstance

中文:
实例 :
  签名: Indiscrete拓扑 命题空
  定义体: inferInstance
-/
instance : IndiscreteTopology PEmpty := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace PUnit
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 命题单元
  定义体: ⊥
-/
instance : TopologicalSpace PUnit := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology PUnit
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 命题单元
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology PUnit := ⟨rfl⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IndiscreteTopology PUnit
  body: inferInstance

中文:
实例 :
  签名: Indiscrete拓扑 命题单元
  定义体: inferInstance
-/
instance : IndiscreteTopology PUnit := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Bool
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 布尔值
  定义体: ⊥
-/
instance : TopologicalSpace Bool := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology Bool
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 布尔值
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology Bool := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Nat
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 自然数
  定义体: ⊥
-/
instance : TopologicalSpace Nat := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology Nat
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 自然数
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology Nat := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Int
  body: ⊥

中文:
实例 :
  签名: 拓扑空间 整数
  定义体: ⊥
-/
instance : TopologicalSpace Int := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology Int
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 整数
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology Int := ⟨rfl⟩

instance {n} : TopologicalSpace (Fin n) := ⊥
instance {n} : DiscreteTopology (Fin n) := ⟨rfl⟩

/--
Definition of `WithDiscreteTopology` / `WithDiscreteTopology` 的定义

English:
abbreviation WithDiscreteTopology
  signature: (α : Type*)
  body: WithTopology α ⊥

中文:
缩写 WithDiscreteTopology
  签名: (α : 类型)
  定义体: WithTopology α ⊥

Depends on / 依赖: WithTopology
-/
abbrev WithDiscreteTopology (α : Type*) := WithTopology α ⊥

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (WithDiscreteTopology α)
  body: coinduced_bot

中文:
实例 :
  签名: 离散拓扑 (WithDiscreteTopology α)
  定义体: coinduced_bot

Depends on / 依赖: coinduced_bot
-/
instance : DiscreteTopology (WithDiscreteTopology α) where
  eq_bot := coinduced_bot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IndiscreteTopology (WithTopology α ⊤)
  body: by rw [WithTopology.topology_eq_induced, induced_top]

中文:
实例 :
  签名: Indiscrete拓扑 (With拓扑 α ⊤)
  定义体: by rw [WithTopology.topology_eq_induced, induced_top]

Depends on / 依赖: WithTopology, WithTopology.topology_eq_induced, induced_top, topology_eq_induced
-/
instance : IndiscreteTopology (WithTopology α ⊤) where
  eq_top := by rw [WithTopology.topology_eq_induced, induced_top]

/--
theorem `WithTopology.nontrivialTopology_iff` / 定理 `WithTopology.nontrivialTopology_iff`

English:
theorem WithTopology.nontrivialTopology_iff
  given: {t : TopologicalSpace α}
  proof: by
  simp_rw [nontrivialTopology_iff, topology_eq_induced, ne_eq, not_iff_not]
  constructor
  · intro h
    simpa [induced_compose, comp_def, induced_fun_id] using congr(induced (toTopology t) $h)
  · simp +contextual

中文:
定理 With拓扑.nontrivialTopology_iff
  条件: {t : 拓扑空间 α}
  证明: by
  simp_rw [nontrivialTopology_iff, topology_eq_induced, ne_eq, not_iff_not]
  constructor
  · intro h
    simpa [induced_compose, comp_def, induced_fun_id] using congr(induced (toTopology t) $h)
  · simp +contextual
-/
protected theorem WithTopology.nontrivialTopology_iff {t : TopologicalSpace α} :
    NontrivialTopology (WithTopology α t) ↔ t != ⊤ := by
  simp_rw [nontrivialTopology_iff, topology_eq_induced, ne_eq, not_iff_not]
  constructor
  · intro h
    simpa [induced_compose, comp_def, induced_fun_id] using congr(induced (toTopology t) $h)
  · simp +contextual

/--
lemma `Nat.cast_continuous` / 引理 `Nat.cast_continuous`

English:
lemma Nat.cast_continuous
  given: {R : Type*} [NatCast R] [TopologicalSpace R]
  proof: continuous_of_discreteTopology

中文:
引理 自然数.cast_continuous
  条件: {R : 类型} [自然数嵌入 R] [拓扑空间 R]
  证明: continuous_of_discreteTopology
-/
lemma Nat.cast_continuous {R : Type*} [NatCast R] [TopologicalSpace R] :
    Continuous (Nat.cast (R := R)) :=
  continuous_of_discreteTopology

/--
lemma `Int.cast_continuous` / 引理 `Int.cast_continuous`

English:
lemma Int.cast_continuous
  given: {R : Type*} [IntCast R] [TopologicalSpace R]
  proof: continuous_of_discreteTopology

中文:
引理 整数.cast_continuous
  条件: {R : 类型} [整数嵌入 R] [拓扑空间 R]
  证明: continuous_of_discreteTopology
-/
lemma Int.cast_continuous {R : Type*} [IntCast R] [TopologicalSpace R] :
    Continuous (Int.cast (R := R)) :=
  continuous_of_discreteTopology

/--
Instance `sierpinskiSpace` / 实例 `sierpinskiSpace`

English:
instance sierpinskiSpace
  signature: : TopologicalSpace Prop
  body: generateFrom {{True}}

中文:
实例 sierpinskiSpace
  签名: : 拓扑空间 命题
  定义体: generateFrom {{True}}

Depends on / 依赖: generateFrom
-/
instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}

/--
theorem `continuous_empty_function` / 定理 `continuous_empty_function`

English:
theorem continuous_empty_function
  statement: [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
  proof: letI := Function.isEmpty f
  continuous_of_discreteTopology

中文:
定理 continuous_empty_function
  结论: [拓扑空间 α] [拓扑空间 β] [是空 β]
  证明: letI := Function.isEmpty f
  continuous_of_discreteTopology

Depends on / 依赖: Function, Function.isEmpty, continuous_of_discreteTopology, isEmpty
-/
theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
    (f : α -> β) : Continuous f :=
  letI := Function.isEmpty f
  continuous_of_discreteTopology

/--
theorem `le_generateFrom` / 定理 `le_generateFrom`

English:
theorem le_generateFrom
  given: {t : TopologicalSpace α} {g : Set (Set α)} (h : forall s in g, IsOpen s)
  proof: le_generateFrom_iff_subset_isOpen.2 h

中文:
定理 le_generateFrom
  条件: {t : 拓扑空间 α} {g : 集合 (集合 α)} (h : 对任意 s in g, 是开集 s)
  证明: le_generateFrom_iff_subset_isOpen.2 h

Depends on / 依赖: le_generateFrom_iff_subset_isOpen
-/
theorem le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : forall s in g, IsOpen s) :
    t <= generateFrom g :=
  le_generateFrom_iff_subset_isOpen.2 h

/--
theorem `induced_generateFrom_eq` / 定理 `induced_generateFrom_eq`

English:
theorem induced_generateFrom_eq
  given: {α β} {b : Set (Set β)} {f : α -> β}
  proof: le_antisymm (le_generateFrom <| forall_mem_image.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))

中文:
定理 induced_generateFrom_eq
  条件: {α β} {b : 集合 (集合 β)} {f : α -> β}
  证明: le_antisymm (le_generateFrom <| forall_mem_image.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))

Depends on / 依赖: GenerateOpen, GenerateOpen.basic, coinduced_le_iff_le_induced, forall_mem_image, le_antisymm, le_generateFrom, mem_image_of_mem
-/
theorem induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α -> β} :
    (generateFrom b).induced f = generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| forall_mem_image.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))

/--
theorem `le_induced_generateFrom` / 定理 `le_induced_generateFrom`

English:
theorem le_induced_generateFrom
  statement: {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α -> β}
  proof: by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h

中文:
定理 le_induced_generateFrom
  结论: {α β} [t : 拓扑空间 α] {b : 集合 (集合 β)} {f : α -> β}
  证明: by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h

Depends on / 依赖: and_imp, exists_imp, induced_generateFrom_eq, le_generateFrom, mem_image
-/
theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α -> β}
    (h : forall a : Set β, a in b -> IsOpen (f ⁻¹' a)) : t <= induced f (generateFrom b) := by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h

/--
lemma `generateFrom_insert_of_generateOpen` / 引理 `generateFrom_insert_of_generateOpen`

English:
lemma generateFrom_insert_of_generateOpen
  statement: {α : Type*} {s : Set (Set α)} {t : Set α}
  proof: by
  refine le_antisymm (generateFrom_anti <| subset_insert t s) (le_generateFrom ?_)
  rintro t (rfl | h)
  · exact ht
  · exact isOpen_generateFrom_of_mem h

@[simp]

中文:
引理 generateFrom_insert_of_generateOpen
  结论: {α : 类型} {s : 集合 (集合 α)} {t : 集合 α}
  证明: by
  refine le_antisymm (generateFrom_anti <| subset_insert t s) (le_generateFrom ?_)
  rintro t (rfl | h)
  · exact ht
  · exact isOpen_generateFrom_of_mem h

@[simp]

Depends on / 依赖: generateFrom_anti, isOpen_generateFrom_of_mem, le_antisymm, le_generateFrom, subset_insert
-/
lemma generateFrom_insert_of_generateOpen {α : Type*} {s : Set (Set α)} {t : Set α}
    (ht : GenerateOpen s t) : generateFrom (insert t s) = generateFrom s := by
  refine le_antisymm (generateFrom_anti <| subset_insert t s) (le_generateFrom ?_)
  rintro t (rfl | h)
  · exact ht
  · exact isOpen_generateFrom_of_mem h

@[simp]
/--
lemma `generateFrom_insert_univ` / 引理 `generateFrom_insert_univ`

English:
lemma generateFrom_insert_univ
  given: {α : Type*} {s : Set (Set α)}
  proof: generateFrom_insert_of_generateOpen .univ

@[simp]

中文:
引理 generateFrom_insert_univ
  条件: {α : 类型} {s : 集合 (集合 α)}
  证明: generateFrom_insert_of_generateOpen .univ

@[simp]

Depends on / 依赖: generateFrom_insert_of_generateOpen
-/
lemma generateFrom_insert_univ {α : Type*} {s : Set (Set α)} :
    generateFrom (insert univ s) = generateFrom s :=
  generateFrom_insert_of_generateOpen .univ

@[simp]
/--
lemma `generateFrom_insert_empty` / 引理 `generateFrom_insert_empty`

English:
lemma generateFrom_insert_empty
  given: {α : Type*} {s : Set (Set α)}
  proof: by
  rw [← sUnion_empty]
  exact generateFrom_insert_of_generateOpen (.sUnion ∅ (fun s_1 a => False.elim a))

中文:
引理 generateFrom_insert_empty
  条件: {α : 类型} {s : 集合 (集合 α)}
  证明: by
  rw [← sUnion_empty]
  exact generateFrom_insert_of_generateOpen (.sUnion ∅ (fun s_1 a => False.elim a))

Depends on / 依赖: False.elim, generateFrom_insert_of_generateOpen, sUnion, sUnion_empty
-/
lemma generateFrom_insert_empty {α : Type*} {s : Set (Set α)} :
    generateFrom (insert ∅ s) = generateFrom s := by
  rw [← sUnion_empty]
  exact generateFrom_insert_of_generateOpen (.sUnion ∅ (fun s_1 a => False.elim a))

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
@[instance_reducible]
/--
Definition of `nhdsAdjoint` / `nhdsAdjoint` 的定义

English:
definition nhdsAdjoint
  signature: (a : α) (f : Filter α)
  body: a in s -> s in f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)

中文:
定义 nhdsAdjoint
  签名: (a : α) (f : 滤子 α)
  定义体: a in s -> s in f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)
-/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen s := a in s -> s in f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)

/--
theorem `gc_nhds` / 定理 `gc_nhds`

English:
theorem gc_nhds
  given: (a : α)
  statement: GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a
  proof: fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

中文:
定理 gc_nhds
  条件: (a : α)
  结论: GaloisConnection (nhdsAdjoint a) fun t => @邻域滤子 α t a
  证明: fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

Depends on / 依赖: le_nhds_iff
-/
theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

/--
theorem `nhds_mono` / 定理 `nhds_mono`

English:
theorem nhds_mono
  given: {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
  proof: (gc_nhds a).monotone_u h

中文:
定理 nhds_mono
  条件: {t₁ t₂ : 拓扑空间 α} {a : α} (h : t₁ <= t₂)
  证明: (gc_nhds a).monotone_u h

Depends on / 依赖: gc_nhds, monotone_u
-/
theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂) :
    @nhds α t₁ a <= @nhds α t₂ a :=
  (gc_nhds a).monotone_u h

/--
theorem `le_iff_nhds` / 定理 `le_iff_nhds`

English:
theorem le_iff_nhds
  given: {α : Type*} (t t' : TopologicalSpace α)
  proof: ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩

中文:
定理 le_iff_nhds
  条件: {α : 类型} (t t' : 拓扑空间 α)
  证明: ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩

Depends on / 依赖: le_of_nhds_le_nhds, nhds_mono
-/
theorem le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) :
    t <= t' ↔ forall x, @nhds α t x <= @nhds α t' x :=
  ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩

/--
theorem `isOpen_singleton_nhdsAdjoint` / 定理 `isOpen_singleton_nhdsAdjoint`

English:
theorem isOpen_singleton_nhdsAdjoint
  given: {α : Type*} {a b : α} (f : Filter α) (hb : b != a)
  proof: fun h =>
  absurd h hb.symm

中文:
定理 isOpen_singleton_nhdsAdjoint
  条件: {α : 类型} {a b : α} (f : 滤子 α) (hb : b != a)
  证明: fun h =>
  absurd h hb.symm
-/
theorem isOpen_singleton_nhdsAdjoint {α : Type*} {a b : α} (f : Filter α) (hb : b != a) :
    IsOpen[nhdsAdjoint a f] {b} := fun h =>
  absurd h hb.symm

/--
theorem `nhds_nhdsAdjoint_same` / 定理 `nhds_nhdsAdjoint_same`

English:
theorem nhds_nhdsAdjoint_same
  given: (a : α) (f : Filter α)
  proof: by
  let _ := nhdsAdjoint a f
  apply le_antisymm
  · rintro t ⟨hat : a in t, htf : t in f⟩
    exact IsOpen.mem_nhds (fun _ => htf) hat
  · exact sup_le (pure_le_nhds _) ((gc_nhds a).le_u_l f)

中文:
定理 nhds_nhdsAdjoint_same
  条件: (a : α) (f : 滤子 α)
  证明: by
  let _ := nhdsAdjoint a f
  apply le_antisymm
  · rintro t ⟨hat : a in t, htf : t in f⟩
    exact IsOpen.mem_nhds (fun _ => htf) hat
  · exact sup_le (pure_le_nhds _) ((gc_nhds a).le_u_l f)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, gc_nhds, le_antisymm, le_u_l, mem_nhds, nhdsAdjoint, pure_le_nhds, sup_le
-/
theorem nhds_nhdsAdjoint_same (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f := by
  let _ := nhdsAdjoint a f
  apply le_antisymm
  · rintro t ⟨hat : a in t, htf : t in f⟩
    exact IsOpen.mem_nhds (fun _ => htf) hat
  · exact sup_le (pure_le_nhds _) ((gc_nhds a).le_u_l f)

/--
theorem `nhds_nhdsAdjoint_of_ne` / 定理 `nhds_nhdsAdjoint_of_ne`

English:
theorem nhds_nhdsAdjoint_of_ne
  given: {a b : α} (f : Filter α) (h : b != a)
  proof: let _ := nhdsAdjoint a f
(isOpen_singleton_iff_nhds_eq_pure _).1 isOpen_singleton_nhdsAdjoint f h

中文:
定理 nhds_nhdsAdjoint_of_ne
  条件: {a b : α} (f : 滤子 α) (h : b != a)
  证明: let _ := nhdsAdjoint a f
(isOpen_singleton_iff_nhds_eq_pure _).1 isOpen_singleton_nhdsAdjoint f h

Depends on / 依赖: isOpen_singleton_iff_nhds_eq_pure, isOpen_singleton_nhdsAdjoint, nhdsAdjoint
-/
theorem nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) (h : b != a) :
    @nhds α (nhdsAdjoint a f) b = pure b :=
  let _ := nhdsAdjoint a f
(isOpen_singleton_iff_nhds_eq_pure _).1 isOpen_singleton_nhdsAdjoint f h

/--
theorem `nhds_nhdsAdjoint` / 定理 `nhds_nhdsAdjoint`

English:
theorem nhds_nhdsAdjoint
  given: [DecidableEq α] (a : α) (f : Filter α)
  proof: eq_update_iff.2 ⟨nhds_nhdsAdjoint_same .., fun _ => nhds_nhdsAdjoint_of_ne _⟩

中文:
定理 nhds_nhdsAdjoint
  条件: [DecidableEq α] (a : α) (f : 滤子 α)
  证明: eq_update_iff.2 ⟨nhds_nhdsAdjoint_same .., fun _ => nhds_nhdsAdjoint_of_ne _⟩

Depends on / 依赖: eq_update_iff, nhds_nhdsAdjoint_of_ne, nhds_nhdsAdjoint_same
-/
theorem nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) = update pure a (pure a ⊔ f) :=
  eq_update_iff.2 ⟨nhds_nhdsAdjoint_same .., fun _ => nhds_nhdsAdjoint_of_ne _⟩

/--
theorem `le_nhdsAdjoint_iff'` / 定理 `le_nhdsAdjoint_iff'`

English:
theorem le_nhdsAdjoint_iff'
  given: {a : α} {f : Filter α} {t : TopologicalSpace α}
  proof: by
  classical
  simp_rw [le_iff_nhds, nhds_nhdsAdjoint, forall_update_iff, (pure_le_nhds _).ge_iff_eq']

中文:
定理 le_nhdsAdjoint_iff'
  条件: {a : α} {f : 滤子 α} {t : 拓扑空间 α}
  证明: by
  classical
  simp_rw [le_iff_nhds, nhds_nhdsAdjoint, forall_update_iff, (pure_le_nhds _).ge_iff_eq']

Depends on / 依赖: classical, forall_update_iff, ge_iff_eq, le_iff_nhds, nhds_nhdsAdjoint, pure_le_nhds, simp_rw
-/
theorem le_nhdsAdjoint_iff' {a : α} {f : Filter α} {t : TopologicalSpace α} :
    t <= nhdsAdjoint a f ↔ @nhds α t a <= pure a ⊔ f ∧ forall b != a, @nhds α t b = pure b := by
  classical
  simp_rw [le_iff_nhds, nhds_nhdsAdjoint, forall_update_iff, (pure_le_nhds _).ge_iff_eq']

/--
theorem `le_nhdsAdjoint_iff` / 定理 `le_nhdsAdjoint_iff`

English:
theorem le_nhdsAdjoint_iff
  given: {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α)
  proof: by
  simp only [le_nhdsAdjoint_iff', @isOpen_singleton_iff_nhds_eq_pure α t]

中文:
定理 le_nhdsAdjoint_iff
  条件: {α : 类型} (a : α) (f : 滤子 α) (t : 拓扑空间 α)
  证明: by
  simp only [le_nhdsAdjoint_iff', @isOpen_singleton_iff_nhds_eq_pure α t]

Depends on / 依赖: isOpen_singleton_iff_nhds_eq_pure, le_nhdsAdjoint_iff
-/
theorem le_nhdsAdjoint_iff {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t <= nhdsAdjoint a f ↔ @nhds α t a <= pure a ⊔ f ∧ forall b != a, IsOpen[t] {b} := by
  simp only [le_nhdsAdjoint_iff', @isOpen_singleton_iff_nhds_eq_pure α t]

/--
theorem `nhds_iInf` / 定理 `nhds_iInf`

English:
theorem nhds_iInf
  given: {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α}
  proof: (gc_nhds a).u_iInf

中文:
定理 nhds_iInf
  条件: {ι : 类型层*} {t : ι -> 拓扑空间 α} {a : α}
  证明: (gc_nhds a).u_iInf

Depends on / 依赖: gc_nhds, u_iInf
-/
theorem nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
    @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_iInf

/--
theorem `nhds_sInf` / 定理 `nhds_sInf`

English:
theorem nhds_sInf
  given: {s : Set (TopologicalSpace α)} {a : α}
  proof: (gc_nhds a).u_sInf

中文:
定理 nhds_sInf
  条件: {s : 集合 (拓扑空间 α)} {a : α}
  证明: (gc_nhds a).u_sInf

Depends on / 依赖: gc_nhds, u_sInf
-/
theorem nhds_sInf {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (sInf s) a = ⨅ t in s, @nhds α t a :=
  (gc_nhds a).u_sInf

-- Porting note: type error without `b₁ := t₁`
/--
theorem `nhds_inf` / 定理 `nhds_inf`

English:
theorem nhds_inf
  given: {t₁ t₂ : TopologicalSpace α} {a : α}
  proof: (gc_nhds a).u_inf (b₁ := t₁)

中文:
定理 nhds_inf
  条件: {t₁ t₂ : 拓扑空间 α} {a : α}
  证明: (gc_nhds a).u_inf (b₁ := t₁)

Depends on / 依赖: gc_nhds, u_inf
-/
theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  (gc_nhds a).u_inf (b₁ := t₁)

/--
theorem `nhds_top` / 定理 `nhds_top`

English:
theorem nhds_top
  given: {a : α}
  statement: @nhds α ⊤ a = ⊤
  proof: (gc_nhds a).u_top

中文:
定理 nhds_top
  条件: {a : α}
  结论: @邻域滤子 α ⊤ a = ⊤
  证明: (gc_nhds a).u_top

Depends on / 依赖: gc_nhds, u_top
-/
theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top

/--
theorem `isOpen_sup` / 定理 `isOpen_sup`

English:
theorem isOpen_sup
  given: {t₁ t₂ : TopologicalSpace α} {s : Set α}
  proof: Iff.rfl

中文:
定理 isOpen_sup
  条件: {t₁ t₂ : 拓扑空间 α} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    IsOpen[t₁ ⊔ t₂] s ↔ IsOpen[t₁] s ∧ IsOpen[t₂] s :=
  Iff.rfl


/--
theorem `IndiscreteTopology.nhds_eq` / 定理 `IndiscreteTopology.nhds_eq`

English:
theorem IndiscreteTopology.nhds_eq
  given: [TopologicalSpace α] [IndiscreteTopology α] (a : α)
  proof: by
  cases IndiscreteTopology.eq_top α
  exact nhds_top

中文:
定理 Indiscrete拓扑.nhds_eq
  条件: [拓扑空间 α] [Indiscrete拓扑 α] (a : α)
  证明: by
  cases IndiscreteTopology.eq_top α
  exact nhds_top

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.eq_top, eq_top, nhds_top
-/
theorem IndiscreteTopology.nhds_eq [TopologicalSpace α] [IndiscreteTopology α] (a : α) :
    nhds a = ⊤ := by
  cases IndiscreteTopology.eq_top α
  exact nhds_top

/--
theorem `clusterPt_of_indiscreteTopology` / 定理 `clusterPt_of_indiscreteTopology`

English:
theorem clusterPt_of_indiscreteTopology
  statement: [TopologicalSpace α] [IndiscreteTopology α]
  proof: by
  simpa [ClusterPt, IndiscreteTopology.nhds_eq]

中文:
定理 clusterPt_of_indiscreteTopology
  结论: [拓扑空间 α] [Indiscrete拓扑 α]
  证明: by
  simpa [ClusterPt, IndiscreteTopology.nhds_eq]

Depends on / 依赖: ClusterPt, IndiscreteTopology, IndiscreteTopology.nhds_eq, nhds_eq
-/
theorem clusterPt_of_indiscreteTopology [TopologicalSpace α] [IndiscreteTopology α]
    {x : α} {f : Filter α} [f.NeBot] : ClusterPt x f := by
  simpa [ClusterPt, IndiscreteTopology.nhds_eq]

/-- In the indiscrete topology no points are separable.

The corresponding `bot` lemma is handled more generally by `inseparable_iff_eq`. -/
@[simp]
/--
theorem `Inseparable.all` / 定理 `Inseparable.all`

English:
theorem Inseparable.all
  given: [TopologicalSpace α] [IndiscreteTopology α] (x y : α)
  proof: (IndiscreteTopology.nhds_eq _).trans (IndiscreteTopology.nhds_eq _).symm

中文:
定理 不可分.all
  条件: [拓扑空间 α] [Indiscrete拓扑 α] (x y : α)
  证明: (IndiscreteTopology.nhds_eq _).trans (IndiscreteTopology.nhds_eq _).symm

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.nhds_eq, nhds_eq
-/
theorem Inseparable.all [TopologicalSpace α] [IndiscreteTopology α] (x y : α) :
    Inseparable x y :=
  (IndiscreteTopology.nhds_eq _).trans (IndiscreteTopology.nhds_eq _).symm

/--
theorem `IndiscreteTopology.of_forall_inseparable` / 定理 `IndiscreteTopology.of_forall_inseparable`

English:
theorem IndiscreteTopology.of_forall_inseparable
  statement: [TopologicalSpace α]
  proof: ext_nhds fun x => nhds_top ▸ top_unique fun _ hs a => mem_of_mem_nhds h x a ▸ hs

中文:
定理 Indiscrete拓扑.of_对任意_inseparable
  结论: [拓扑空间 α]
  证明: ext_nhds fun x => nhds_top ▸ top_unique fun _ hs a => mem_of_mem_nhds h x a ▸ hs

Depends on / 依赖: ext_nhds, mem_of_mem_nhds, nhds_top, top_unique
-/
theorem IndiscreteTopology.of_forall_inseparable [TopologicalSpace α]
    (h : forall x y : α, Inseparable x y) : IndiscreteTopology α where
eq_top := ext_nhds fun x => nhds_top ▸ top_unique fun _ hs a => mem_of_mem_nhds h x a ▸ hs

/--
theorem `TopologicalSpace.indiscrete_iff_forall_inseparable` / 定理 `TopologicalSpace.indiscrete_iff_forall_inseparable`

English:
theorem TopologicalSpace.indiscrete_iff_forall_inseparable
  given: {t : TopologicalSpace α}
  proof: Inseparable.all
  mpr := .of_forall_inseparable

中文:
定理 拓扑空间.indiscrete_iff_对任意_inseparable
  条件: {t : 拓扑空间 α}
  证明: Inseparable.all
  mpr := .of_forall_inseparable

Depends on / 依赖: Inseparable, Inseparable.all
-/
theorem TopologicalSpace.indiscrete_iff_forall_inseparable {t : TopologicalSpace α} :
    IndiscreteTopology α ↔ (forall x y : α, Inseparable x y) where
  mp _ := Inseparable.all
  mpr := .of_forall_inseparable

/--
theorem `TopologicalSpace.nontrivial_iff_exists_not_inseparable` / 定理 `TopologicalSpace.nontrivial_iff_exists_not_inseparable`

English:
theorem TopologicalSpace.nontrivial_iff_exists_not_inseparable
  given: {t : TopologicalSpace α}
  proof: by
  simpa using indiscrete_iff_forall_inseparable.not

alias ⟨NontrivialTopology.exists_not_inseparable, NontrivialTopology.of_exists_not_inseparable⟩ :=
  TopologicalSpace.nontrivial_iff_exists_not_inseparable

@[deprecated Inseparable.all (since := "2026-01-21")]

中文:
定理 拓扑空间.nontrivial_iff_存在_not_inseparable
  条件: {t : 拓扑空间 α}
  证明: by
  simpa using indiscrete_iff_forall_inseparable.not

alias ⟨NontrivialTopology.exists_not_inseparable, NontrivialTopology.of_exists_not_inseparable⟩ :=
  TopologicalSpace.nontrivial_iff_exists_not_inseparable

@[deprecated Inseparable.all (since := "2026-01-21")]

Depends on / 依赖: indiscrete_iff_forall_inseparable, indiscrete_iff_forall_inseparable.not
-/
theorem TopologicalSpace.nontrivial_iff_exists_not_inseparable {t : TopologicalSpace α} :
    NontrivialTopology α ↔ exists x y : α, ¬Inseparable x y := by
  simpa using indiscrete_iff_forall_inseparable.not

alias ⟨NontrivialTopology.exists_not_inseparable, NontrivialTopology.of_exists_not_inseparable⟩ :=
  TopologicalSpace.nontrivial_iff_exists_not_inseparable

@[deprecated Inseparable.all (since := "2026-01-21")]
/--
theorem `inseparable_top` / 定理 `inseparable_top`

English:
theorem inseparable_top
  given: (x y : α)
  statement: @Inseparable α ⊤ x y
  proof: @Inseparable.all _ ⊤ _ x y

@[deprecated TopologicalSpace.indiscrete_iff_forall_inseparable (since := "2026-01-21")]

中文:
定理 inseparable_top
  条件: (x y : α)
  结论: @不可分 α ⊤ x y
  证明: @Inseparable.all _ ⊤ _ x y

@[deprecated TopologicalSpace.indiscrete_iff_forall_inseparable (since := "2026-01-21")]

Depends on / 依赖: Inseparable, Inseparable.all
-/
theorem inseparable_top (x y : α) : @Inseparable α ⊤ x y :=
  @Inseparable.all _ ⊤ _ x y

@[deprecated TopologicalSpace.indiscrete_iff_forall_inseparable (since := "2026-01-21")]
/--
theorem `TopologicalSpace.eq_top_iff_forall_inseparable` / 定理 `TopologicalSpace.eq_top_iff_forall_inseparable`

English:
theorem TopologicalSpace.eq_top_iff_forall_inseparable
  given: {t : TopologicalSpace α}
  proof: by
  rw [← TopologicalSpace.indiscrete_iff_forall_inseparable]; rw [indiscreteTopology_iff]

@[deprecated TopologicalSpace.nontrivial_iff_exists_not_inseparable (since := "2026-01-21")]

中文:
定理 拓扑空间.eq_top_iff_对任意_inseparable
  条件: {t : 拓扑空间 α}
  证明: by
  rw [← TopologicalSpace.indiscrete_iff_forall_inseparable]; rw [indiscreteTopology_iff]

@[deprecated TopologicalSpace.nontrivial_iff_exists_not_inseparable (since := "2026-01-21")]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.indiscrete_iff_forall_inseparable, indiscreteTopology_iff, indiscrete_iff_forall_inseparable
-/
theorem TopologicalSpace.eq_top_iff_forall_inseparable {t : TopologicalSpace α} :
    t = ⊤ ↔ (forall x y : α, Inseparable x y) := by
  rw [← TopologicalSpace.indiscrete_iff_forall_inseparable]; rw [indiscreteTopology_iff]

@[deprecated TopologicalSpace.nontrivial_iff_exists_not_inseparable (since := "2026-01-21")]
/--
theorem `TopologicalSpace.ne_top_iff_exists_not_inseparable` / 定理 `TopologicalSpace.ne_top_iff_exists_not_inseparable`

English:
theorem TopologicalSpace.ne_top_iff_exists_not_inseparable
  given: {t : TopologicalSpace α}
  proof: by
  rw [← TopologicalSpace.nontrivial_iff_exists_not_inseparable]; rw [nontrivialTopology_iff]

中文:
定理 拓扑空间.ne_top_iff_存在_not_inseparable
  条件: {t : 拓扑空间 α}
  证明: by
  rw [← TopologicalSpace.nontrivial_iff_exists_not_inseparable]; rw [nontrivialTopology_iff]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.nontrivial_iff_exists_not_inseparable, nontrivialTopology_iff, nontrivial_iff_exists_not_inseparable
-/
theorem TopologicalSpace.ne_top_iff_exists_not_inseparable {t : TopologicalSpace α} :
    t != ⊤ ↔ exists x y : α, ¬Inseparable x y := by
  rw [← TopologicalSpace.nontrivial_iff_exists_not_inseparable]; rw [nontrivialTopology_iff]

open TopologicalSpace

variable {γ : Type*} {f : α -> β} {ι : Sort*}

/--
theorem `continuous_iff_coinduced_le` / 定理 `continuous_iff_coinduced_le`

English:
theorem continuous_iff_coinduced_le
  given: {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β}
  proof: continuous_def

中文:
定理 continuous_iff_coinduced_le
  条件: {t₁ : 拓扑空间 α} {t₂ : 拓扑空间 β}
  证明: continuous_def

Depends on / 依赖: continuous_def
-/
theorem continuous_iff_coinduced_le {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ coinduced f t₁ <= t₂ :=
  continuous_def

/--
theorem `continuous_iff_le_induced` / 定理 `continuous_iff_le_induced`

English:
theorem continuous_iff_le_induced
  given: {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β}
  proof: Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

中文:
定理 continuous_iff_le_induced
  条件: {t₁ : 拓扑空间 α} {t₂ : 拓扑空间 β}
  证明: Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

Depends on / 依赖: Iff.trans, continuous_iff_coinduced_le, gc_coinduced_induced
-/
theorem continuous_iff_le_induced {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

/--
lemma `continuous_generateFrom_iff` / 引理 `continuous_generateFrom_iff`

English:
lemma continuous_generateFrom_iff
  given: {t : TopologicalSpace α} {b : Set (Set β)}
  proof: by
  rw [continuous_iff_coinduced_le]; rw [le_generateFrom_iff_subset_isOpen]
  simp only [isOpen_coinduced, subset_def, mem_ofPred_eq]

@[continuity, fun_prop]

中文:
引理 continuous_generateFrom_iff
  条件: {t : 拓扑空间 α} {b : 集合 (集合 β)}
  证明: by
  rw [continuous_iff_coinduced_le]; rw [le_generateFrom_iff_subset_isOpen]
  simp only [isOpen_coinduced, subset_def, mem_ofPred_eq]

@[continuity, fun_prop]

Depends on / 依赖: continuous_iff_coinduced_le, isOpen_coinduced, le_generateFrom_iff_subset_isOpen, mem_ofPred_eq, subset_def
-/
lemma continuous_generateFrom_iff {t : TopologicalSpace α} {b : Set (Set β)} :
    Continuous[t, generateFrom b] f ↔ forall s in b, IsOpen (f ⁻¹' s) := by
  rw [continuous_iff_coinduced_le]; rw [le_generateFrom_iff_subset_isOpen]
  simp only [isOpen_coinduced, subset_def, mem_ofPred_eq]

@[continuity, fun_prop]
/--
theorem `continuous_induced_dom` / 定理 `continuous_induced_dom`

English:
theorem continuous_induced_dom
  given: {t : TopologicalSpace β}
  statement: Continuous[induced f t, t] f
  proof: continuous_iff_le_induced.2 le_rfl

中文:
定理 continuous_induced_dom
  条件: {t : 拓扑空间 β}
  结论: 连续[induced f t, t] f
  证明: continuous_iff_le_induced.2 le_rfl

Depends on / 依赖: continuous_iff_le_induced, le_rfl
-/
theorem continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, t] f :=
  continuous_iff_le_induced.2 le_rfl

/--
theorem `continuous_induced_rng` / 定理 `continuous_induced_rng`

English:
theorem continuous_induced_rng
  given: {g : γ -> α} {t₂ : TopologicalSpace β} {t₁ : TopologicalSpace γ}
  proof: by
  simp only [continuous_iff_le_induced, induced_compose]

中文:
定理 continuous_induced_rng
  条件: {g : γ -> α} {t₂ : 拓扑空间 β} {t₁ : 拓扑空间 γ}
  证明: by
  simp only [continuous_iff_le_induced, induced_compose]

Depends on / 依赖: continuous_iff_le_induced, induced_compose
-/
theorem continuous_induced_rng {g : γ -> α} {t₂ : TopologicalSpace β} {t₁ : TopologicalSpace γ} :
    Continuous[t₁, induced f t₂] g ↔ Continuous[t₁, t₂] (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]

/--
theorem `continuous_coinduced_rng` / 定理 `continuous_coinduced_rng`

English:
theorem continuous_coinduced_rng
  given: {t : TopologicalSpace α}
  proof: continuous_iff_coinduced_le.2 le_rfl

中文:
定理 continuous_coinduced_rng
  条件: {t : 拓扑空间 α}
  证明: continuous_iff_coinduced_le.2 le_rfl

Depends on / 依赖: continuous_iff_coinduced_le, le_rfl
-/
theorem continuous_coinduced_rng {t : TopologicalSpace α} :
    Continuous[t, coinduced f t] f :=
  continuous_iff_coinduced_le.2 le_rfl

/--
theorem `continuous_coinduced_dom` / 定理 `continuous_coinduced_dom`

English:
theorem continuous_coinduced_dom
  given: {g : β -> γ} {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace γ}
  proof: by
  simp only [continuous_iff_coinduced_le, coinduced_compose]

中文:
定理 continuous_coinduced_dom
  条件: {g : β -> γ} {t₁ : 拓扑空间 α} {t₂ : 拓扑空间 γ}
  证明: by
  simp only [continuous_iff_coinduced_le, coinduced_compose]

Depends on / 依赖: coinduced_compose, continuous_iff_coinduced_le
-/
theorem continuous_coinduced_dom {g : β -> γ} {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace γ} :
    Continuous[coinduced f t₁, t₂] g ↔ Continuous[t₁, t₂] (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]

/--
theorem `continuous_le_dom` / 定理 `continuous_le_dom`

English:
theorem continuous_le_dom
  statement: {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ <= t₁)
  proof: by
  rw [continuous_iff_le_induced] at h₂ ⊢
  exact le_trans h₁ h₂

中文:
定理 continuous_le_dom
  结论: {t₁ t₂ : 拓扑空间 α} {t₃ : 拓扑空间 β} (h₁ : t₂ <= t₁)
  证明: by
  rw [continuous_iff_le_induced] at h₂ ⊢
  exact le_trans h₁ h₂

Depends on / 依赖: continuous_iff_le_induced, le_trans
-/
theorem continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ <= t₁)
    (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂, t₃] f := by
  rw [continuous_iff_le_induced] at h₂ ⊢
  exact le_trans h₁ h₂

/--
theorem `continuous_le_rng` / 定理 `continuous_le_rng`

English:
theorem continuous_le_rng
  statement: {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ <= t₃)
  proof: by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  exact le_trans h₂ h₁

中文:
定理 continuous_le_rng
  结论: {t₁ : 拓扑空间 α} {t₂ t₃ : 拓扑空间 β} (h₁ : t₂ <= t₃)
  证明: by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  exact le_trans h₂ h₁

Depends on / 依赖: continuous_iff_coinduced_le, le_trans
-/
theorem continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ <= t₃)
    (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁, t₃] f := by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  exact le_trans h₂ h₁

/--
theorem `continuous_sup_dom` / 定理 `continuous_sup_dom`

English:
theorem continuous_sup_dom
  given: {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
  proof: by
  simp only [continuous_iff_le_induced, sup_le_iff]

中文:
定理 continuous_sup_dom
  条件: {t₁ t₂ : 拓扑空间 α} {t₃ : 拓扑空间 β}
  证明: by
  simp only [continuous_iff_le_induced, sup_le_iff]

Depends on / 依赖: continuous_iff_le_induced, sup_le_iff
-/
theorem continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Continuous[t₂, t₃] f := by
  simp only [continuous_iff_le_induced, sup_le_iff]

/--
theorem `continuous_sup_rng_left` / 定理 `continuous_sup_rng_left`

English:
theorem continuous_sup_rng_left
  given: {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β}
  proof: continuous_le_rng le_sup_left

中文:
定理 continuous_sup_rng_left
  条件: {t₁ : 拓扑空间 α} {t₃ t₂ : 拓扑空间 β}
  证明: continuous_le_rng le_sup_left

Depends on / 依赖: continuous_le_rng, le_sup_left
-/
theorem continuous_sup_rng_left {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f -> Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_left

/--
theorem `continuous_sup_rng_right` / 定理 `continuous_sup_rng_right`

English:
theorem continuous_sup_rng_right
  given: {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β}
  proof: continuous_le_rng le_sup_right

中文:
定理 continuous_sup_rng_right
  条件: {t₁ : 拓扑空间 α} {t₃ t₂ : 拓扑空间 β}
  证明: continuous_le_rng le_sup_right

Depends on / 依赖: continuous_le_rng, le_sup_right
-/
theorem continuous_sup_rng_right {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₃] f -> Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_right

/--
theorem `continuous_sSup_dom` / 定理 `continuous_sSup_dom`

English:
theorem continuous_sSup_dom
  given: {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
  proof: by
  simp only [continuous_iff_le_induced, sSup_le_iff]

中文:
定理 continuous_sSup_dom
  条件: {T : 集合 (拓扑空间 α)} {t₂ : 拓扑空间 β}
  证明: by
  simp only [continuous_iff_le_induced, sSup_le_iff]

Depends on / 依赖: continuous_iff_le_induced, sSup_le_iff
-/
theorem continuous_sSup_dom {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β} :
    Continuous[sSup T, t₂] f ↔ forall t in T, Continuous[t, t₂] f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]

/--
theorem `continuous_sSup_rng` / 定理 `continuous_sSup_rng`

English:
theorem continuous_sSup_rng
  statement: {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace β)}
  proof: continuous_iff_coinduced_le.2 le_sSup_of_le h₁ continuous_iff_coinduced_le.1 hf

中文:
定理 continuous_sSup_rng
  结论: {t₁ : 拓扑空间 α} {t₂ : 集合 (拓扑空间 β)}
  证明: continuous_iff_coinduced_le.2 le_sSup_of_le h₁ continuous_iff_coinduced_le.1 hf

Depends on / 依赖: continuous_iff_coinduced_le, le_sSup_of_le
-/
theorem continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace β)}
    {t : TopologicalSpace β} (h₁ : t in t₂) (hf : Continuous[t₁, t] f) :
    Continuous[t₁, sSup t₂] f :=
continuous_iff_coinduced_le.2 le_sSup_of_le h₁ continuous_iff_coinduced_le.1 hf

/--
theorem `continuous_iSup_dom` / 定理 `continuous_iSup_dom`

English:
theorem continuous_iSup_dom
  given: {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace β}
  proof: by
  simp only [continuous_iff_le_induced, iSup_le_iff]

中文:
定理 continuous_iSup_dom
  条件: {t₁ : ι -> 拓扑空间 α} {t₂ : 拓扑空间 β}
  证明: by
  simp only [continuous_iff_le_induced, iSup_le_iff]

Depends on / 依赖: continuous_iff_le_induced, iSup_le_iff
-/
theorem continuous_iSup_dom {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[iSup t₁, t₂] f ↔ forall i, Continuous[t₁ i, t₂] f := by
  simp only [continuous_iff_le_induced, iSup_le_iff]

/--
theorem `continuous_iSup_rng` / 定理 `continuous_iSup_rng`

English:
theorem continuous_iSup_rng
  statement: {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace β} {i : ι}
  proof: continuous_sSup_rng ⟨i, rfl⟩ h

中文:
定理 continuous_iSup_rng
  结论: {t₁ : 拓扑空间 α} {t₂ : ι -> 拓扑空间 β} {i : ι}
  证明: continuous_sSup_rng ⟨i, rfl⟩ h

Depends on / 依赖: continuous_sSup_rng
-/
theorem continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace β} {i : ι}
    (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, iSup t₂] f :=
  continuous_sSup_rng ⟨i, rfl⟩ h

/--
theorem `continuous_inf_rng` / 定理 `continuous_inf_rng`

English:
theorem continuous_inf_rng
  given: {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
  proof: by
  simp only [continuous_iff_coinduced_le, le_inf_iff]

中文:
定理 continuous_inf_rng
  条件: {t₁ : 拓扑空间 α} {t₂ t₃ : 拓扑空间 β}
  证明: by
  simp only [continuous_iff_coinduced_le, le_inf_iff]

Depends on / 依赖: continuous_iff_coinduced_le, le_inf_iff
-/
theorem continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} :
    Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Continuous[t₁, t₃] f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]

/--
theorem `continuous_inf_dom_left` / 定理 `continuous_inf_dom_left`

English:
theorem continuous_inf_dom_left
  given: {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
  proof: continuous_le_dom inf_le_left

中文:
定理 continuous_inf_dom_left
  条件: {t₁ t₂ : 拓扑空间 α} {t₃ : 拓扑空间 β}
  证明: continuous_le_dom inf_le_left

Depends on / 依赖: continuous_le_dom, inf_le_left
-/
theorem continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_left

/--
theorem `continuous_inf_dom_right` / 定理 `continuous_inf_dom_right`

English:
theorem continuous_inf_dom_right
  given: {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
  proof: continuous_le_dom inf_le_right

中文:
定理 continuous_inf_dom_right
  条件: {t₁ t₂ : 拓扑空间 α} {t₃ : 拓扑空间 β}
  证明: continuous_le_dom inf_le_right

Depends on / 依赖: continuous_le_dom, inf_le_right
-/
theorem continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₂, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_right

/--
theorem `continuous_sInf_dom` / 定理 `continuous_sInf_dom`

English:
theorem continuous_sInf_dom
  statement: {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
  proof: continuous_le_dom sInf_le h₁

中文:
定理 continuous_sInf_dom
  结论: {t₁ : 集合 (拓扑空间 α)} {t₂ : 拓扑空间 β}
  证明: continuous_le_dom sInf_le h₁

Depends on / 依赖: continuous_le_dom, sInf_le
-/
theorem continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
    {t : TopologicalSpace α} (h₁ : t in t₁) :
    Continuous[t, t₂] f -> Continuous[sInf t₁, t₂] f :=
continuous_le_dom sInf_le h₁

/--
theorem `continuous_sInf_rng` / 定理 `continuous_sInf_rng`

English:
theorem continuous_sInf_rng
  given: {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β)}
  proof: by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]

中文:
定理 continuous_sInf_rng
  条件: {t₁ : 拓扑空间 α} {T : 集合 (拓扑空间 β)}
  证明: by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]

Depends on / 依赖: continuous_iff_coinduced_le, le_sInf_iff
-/
theorem continuous_sInf_rng {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β)} :
    Continuous[t₁, sInf T] f ↔ forall t in T, Continuous[t₁, t] f := by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]

/--
theorem `continuous_iInf_dom` / 定理 `continuous_iInf_dom`

English:
theorem continuous_iInf_dom
  given: {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace β} {i : ι}
  proof: continuous_le_dom iInf_le _ _

中文:
定理 continuous_iInf_dom
  条件: {t₁ : ι -> 拓扑空间 α} {t₂ : 拓扑空间 β} {i : ι}
  证明: continuous_le_dom iInf_le _ _

Depends on / 依赖: continuous_le_dom, iInf_le
-/
theorem continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace β} {i : ι} :
    Continuous[t₁ i, t₂] f -> Continuous[iInf t₁, t₂] f :=
continuous_le_dom iInf_le _ _

/--
theorem `continuous_iInf_rng` / 定理 `continuous_iInf_rng`

English:
theorem continuous_iInf_rng
  given: {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace β}
  proof: by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]

@[continuity, fun_prop]

中文:
定理 continuous_iInf_rng
  条件: {t₁ : 拓扑空间 α} {t₂ : ι -> 拓扑空间 β}
  证明: by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]

@[continuity, fun_prop]

Depends on / 依赖: continuous_iff_coinduced_le, le_iInf_iff
-/
theorem continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace β} :
    Continuous[t₁, iInf t₂] f ↔ forall i, Continuous[t₁, t₂ i] f := by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]

@[continuity, fun_prop]
/--
theorem `continuous_bot` / 定理 `continuous_bot`

English:
theorem continuous_bot
  given: {t : TopologicalSpace β}
  statement: Continuous[⊥, t] f
  proof: continuous_iff_le_induced.2 bot_le

@[continuity, fun_prop]

中文:
定理 continuous_bot
  条件: {t : 拓扑空间 β}
  结论: 连续[⊥, t] f
  证明: continuous_iff_le_induced.2 bot_le

@[continuity, fun_prop]

Depends on / 依赖: bot_le, continuous_iff_le_induced
-/
theorem continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f :=
  continuous_iff_le_induced.2 bot_le

@[continuity, fun_prop]
/--
theorem `continuous_top` / 定理 `continuous_top`

English:
theorem continuous_top
  given: {t : TopologicalSpace α}
  statement: Continuous[t, ⊤] f
  proof: continuous_iff_coinduced_le.2 le_top

中文:
定理 continuous_top
  条件: {t : 拓扑空间 α}
  结论: 连续[t, ⊤] f
  证明: continuous_iff_coinduced_le.2 le_top

Depends on / 依赖: continuous_iff_coinduced_le, le_top
-/
theorem continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f :=
  continuous_iff_coinduced_le.2 le_top

/--
theorem `continuous_id_iff_le` / 定理 `continuous_id_iff_le`

English:
theorem continuous_id_iff_le
  given: {t t' : TopologicalSpace α}
  statement: Continuous[t, t'] id ↔ t <= t'
  proof: @continuous_def _ _ t t' id

中文:
定理 continuous_id_iff_le
  条件: {t t' : 拓扑空间 α}
  结论: 连续[t, t'] id ↔ t <= t'
  证明: @continuous_def _ _ t t' id

Depends on / 依赖: continuous_def
-/
theorem continuous_id_iff_le {t t' : TopologicalSpace α} : Continuous[t, t'] id ↔ t <= t' :=
  @continuous_def _ _ t t' id

/--
theorem `continuous_id_of_le` / 定理 `continuous_id_of_le`

English:
theorem continuous_id_of_le
  given: {t t' : TopologicalSpace α} (h : t <= t')
  statement: Continuous[t, t'] id
  proof: continuous_id_iff_le.2 h

中文:
定理 continuous_id_of_le
  条件: {t t' : 拓扑空间 α} (h : t <= t')
  结论: 连续[t, t'] id
  证明: continuous_id_iff_le.2 h

Depends on / 依赖: continuous_id_iff_le
-/
theorem continuous_id_of_le {t t' : TopologicalSpace α} (h : t <= t') : Continuous[t, t'] id :=
  continuous_id_iff_le.2 h

-- 𝓝 in the induced topology
/--
theorem `mem_nhds_induced` / 定理 `mem_nhds_induced`

English:
theorem mem_nhds_induced
  given: [T : TopologicalSpace α] (f : β -> α) (a : β) (s : Set β)
  proof: by
  let := T.induced f
  simp_rw [mem_nhds_iff, isOpen_induced_iff]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

中文:
定理 mem_nhds_induced
  条件: [T : 拓扑空间 α] (f : β -> α) (a : β) (s : 集合 β)
  证明: by
  let := T.induced f
  simp_rw [mem_nhds_iff, isOpen_induced_iff]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

Depends on / 依赖: Set.preimage_mono, Subset, Subset.rfl, T.induced, finvsub, induced, isOpen_induced_iff, mem_nhds_iff, preimage_mono, simp_rw
-/
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β) (s : Set β) :
    s in @nhds β (TopologicalSpace.induced f T) a ↔ exists u in 𝓝 (f a), f ⁻¹' u subseteq s := by
  let := T.induced f
  simp_rw [mem_nhds_iff, isOpen_induced_iff]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

/--
theorem `nhds_induced` / 定理 `nhds_induced`

English:
theorem nhds_induced
  given: [T : TopologicalSpace α] (f : β -> α) (a : β)
  proof: by
  ext s
  rw [mem_nhds_induced]; rw [mem_comap]

中文:
定理 nhds_induced
  条件: [T : 拓扑空间 α] (f : β -> α) (a : β)
  证明: by
  ext s
  rw [mem_nhds_induced]; rw [mem_comap]

Depends on / 依赖: mem_comap, mem_nhds_induced
-/
theorem nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by
  ext s
  rw [mem_nhds_induced]; rw [mem_comap]

/--
theorem `induced_iff_nhds_eq` / 定理 `induced_iff_nhds_eq`

English:
theorem induced_iff_nhds_eq
  given: [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β -> α)
  proof: by
  simp only [ext_iff_nhds, nhds_induced]

中文:
定理 induced_iff_nhds_eq
  条件: [tα : 拓扑空间 α] [tβ : 拓扑空间 β] (f : β -> α)
  证明: by
  simp only [ext_iff_nhds, nhds_induced]

Depends on / 依赖: ext_iff_nhds, nhds_induced
-/
theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β -> α) :
    tβ = tα.induced f ↔ forall b, 𝓝 b = comap f (𝓝 <| f b) := by
  simp only [ext_iff_nhds, nhds_induced]

/--
theorem `map_nhds_induced_of_surjective` / 定理 `map_nhds_induced_of_surjective`

English:
theorem map_nhds_induced_of_surjective
  statement: [T : TopologicalSpace α] {f : β -> α} (hf : Surjective f)
  proof: by
  rw [nhds_induced]; rw [map_comap_of_surjective hf]

中文:
定理 map_nhds_induced_of_surjective
  结论: [T : 拓扑空间 α] {f : β -> α} (hf : 满射 f)
  证明: by
  rw [nhds_induced]; rw [map_comap_of_surjective hf]

Depends on / 依赖: map_comap_of_surjective, nhds_induced
-/
theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β -> α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced]; rw [map_comap_of_surjective hf]

/--
theorem `continuous_nhdsAdjoint_dom` / 定理 `continuous_nhdsAdjoint_dom`

English:
theorem continuous_nhdsAdjoint_dom
  given: [TopologicalSpace β] {f : α -> β} {a : α} {l : Filter α}
  proof: by
  simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, tendsto_iff_comap]

中文:
定理 continuous_nhdsAdjoint_dom
  条件: [拓扑空间 β] {f : α -> β} {a : α} {l : 滤子 α}
  证明: by
  simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, tendsto_iff_comap]

Depends on / 依赖: continuous_iff_le_induced, gc_nhds, nhds_induced, simp_rw, tendsto_iff_comap
-/
theorem continuous_nhdsAdjoint_dom [TopologicalSpace β] {f : α -> β} {a : α} {l : Filter α} :
    Continuous[nhdsAdjoint a l, _] f ↔ Tendsto f l (𝓝 (f a)) := by
  simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, tendsto_iff_comap]

/--
theorem `coinduced_nhdsAdjoint` / 定理 `coinduced_nhdsAdjoint`

English:
theorem coinduced_nhdsAdjoint
  given: (f : α -> β) (a : α) (l : Filter α)
  proof: eq_of_forall_ge_iff fun _ => by
    rw [gc_nhds]; rw [← continuous_iff_coinduced_le]; rw [continuous_nhdsAdjoint_dom]; rw [Tendsto]

中文:
定理 coinduced_nhdsAdjoint
  条件: (f : α -> β) (a : α) (l : 滤子 α)
  证明: eq_of_forall_ge_iff fun _ => by
    rw [gc_nhds]; rw [← continuous_iff_coinduced_le]; rw [continuous_nhdsAdjoint_dom]; rw [Tendsto]

Depends on / 依赖: Tendsto, continuous_iff_coinduced_le, continuous_nhdsAdjoint_dom, eq_of_forall_ge_iff, gc_nhds
-/
theorem coinduced_nhdsAdjoint (f : α -> β) (a : α) (l : Filter α) :
    coinduced f (nhdsAdjoint a l) = nhdsAdjoint (f a) (map f l) :=
  eq_of_forall_ge_iff fun _ => by
    rw [gc_nhds]; rw [← continuous_iff_coinduced_le]; rw [continuous_nhdsAdjoint_dom]; rw [Tendsto]

end Constructions

section Induced

open TopologicalSpace

variable {α : Type*} {β : Type*}
variable [t : TopologicalSpace β] {f : α -> β}

/--
theorem `isOpen_induced_eq` / 定理 `isOpen_induced_eq`

English:
theorem isOpen_induced_eq
  given: {s : Set α}
  proof: Iff.rfl

中文:
定理 isOpen_induced_eq
  条件: {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_induced_eq {s : Set α} :
    IsOpen[induced f t] s ↔ s in preimage f '' { s | IsOpen s } :=
  Iff.rfl

/--
theorem `isOpen_induced` / 定理 `isOpen_induced`

English:
theorem isOpen_induced
  given: {s : Set β} (h : IsOpen s)
  statement: IsOpen[induced f t] (f ⁻¹' s)
  proof: ⟨s, h, rfl⟩

中文:
定理 isOpen_induced
  条件: {s : 集合 β} (h : 是开集 s)
  结论: 是开集[induced f t] (f ⁻¹' s)
  证明: ⟨s, h, rfl⟩
-/
theorem isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩

/--
theorem `isClosed_induced` / 定理 `isClosed_induced`

English:
theorem isClosed_induced
  given: {s : Set β} (h : IsClosed s)
  statement: IsClosed[induced f t] (f ⁻¹' s)
  proof: by
  simp_rw [← isOpen_compl_iff]
  exact isOpen_induced h.isOpen_compl

中文:
定理 isClosed_induced
  条件: {s : 集合 β} (h : 是闭集 s)
  结论: 是闭集[induced f t] (f ⁻¹' s)
  证明: by
  simp_rw [← isOpen_compl_iff]
  exact isOpen_induced h.isOpen_compl

Depends on / 依赖: h.isOpen_compl, isOpen_compl, isOpen_compl_iff, isOpen_induced, simp_rw
-/
theorem isClosed_induced {s : Set β} (h : IsClosed s) : IsClosed[induced f t] (f ⁻¹' s) := by
  simp_rw [← isOpen_compl_iff]
  exact isOpen_induced h.isOpen_compl

/--
theorem `map_nhds_induced_eq` / 定理 `map_nhds_induced_eq`

English:
theorem map_nhds_induced_eq
  given: (a : α)
  statement: map f (@nhds α (induced f t) a) = 𝓝[range f] f a
  proof: by
  rw [nhds_induced]; rw [Filter.map_comap]; rw [nhdsWithin]

中文:
定理 map_nhds_induced_eq
  条件: (a : α)
  结论: map f (@邻域滤子 α (induced f t) a) = 𝓝[range f] f a
  证明: by
  rw [nhds_induced]; rw [Filter.map_comap]; rw [nhdsWithin]

Depends on / 依赖: Filter, Filter.map_comap, map_comap, nhdsWithin, nhds_induced
-/
theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced]; rw [Filter.map_comap]; rw [nhdsWithin]

/--
theorem `map_nhds_induced_of_mem` / 定理 `map_nhds_induced_of_mem`

English:
theorem map_nhds_induced_of_mem
  given: {a : α} (h : range f in 𝓝 (f a))
  proof: by rw [nhds_induced, Filter.map_comap_of_mem h]

中文:
定理 map_nhds_induced_of_mem
  条件: {a : α} (h : range f in 𝓝 (f a))
  证明: by rw [nhds_induced, Filter.map_comap_of_mem h]

Depends on / 依赖: Filter, Filter.map_comap_of_mem, map_comap_of_mem, nhds_induced
-/
theorem map_nhds_induced_of_mem {a : α} (h : range f in 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]

/--
theorem `closure_induced` / 定理 `closure_induced`

English:
theorem closure_induced
  given: {f : α -> β} {a : α} {s : Set α}
  proof: by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

中文:
定理 closure_induced
  条件: {f : α -> β} {a : α} {s : 集合 α}
  证明: by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

Depends on / 依赖: and_comm, frequently_comap, mem_closure_iff_frequently, mem_image, nhds_induced
-/
theorem closure_induced {f : α -> β} {a : α} {s : Set α} :
    a in @closure α (t.induced f) s ↔ f a in closure (f '' s) := by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

/--
theorem `isClosed_induced_iff'` / 定理 `isClosed_induced_iff'`

English:
theorem isClosed_induced_iff'
  given: {f : α -> β} {s : Set α}
  proof: by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]

中文:
定理 isClosed_induced_iff'
  条件: {f : α -> β} {s : 集合 α}
  证明: by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]

Depends on / 依赖: closure_induced, closure_subset_iff_isClosed, subset_def
-/
theorem isClosed_induced_iff' {f : α -> β} {s : Set α} :
    IsClosed[t.induced f] s ↔ forall a, f a in closure (f '' s) -> a in s := by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]

end Induced

section Sierpinski

variable {α : Type*}

@[simp]
/--
theorem `isOpen_singleton_true` / 定理 `isOpen_singleton_true`

English:
theorem isOpen_singleton_true
  statement: IsOpen ({True} : Set Prop)
  proof: TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]

中文:
定理 isOpen_singleton_true
  结论: 是开集 ({真} : 集合 命题)
  证明: TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]

Depends on / 依赖: GenerateOpen, TopologicalSpace, TopologicalSpace.GenerateOpen.basic, mem_singleton
-/
theorem isOpen_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]
/--
theorem `nhds_true` / 定理 `nhds_true`

English:
theorem nhds_true
  statement: 𝓝 True = pure True
  proof: le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]

中文:
定理 nhds_true
  结论: 𝓝 真 = pure 真
  证明: le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]

Depends on / 依赖: isOpen_singleton_true, isOpen_singleton_true.mem_nhds, le_antisymm, le_pure_iff, mem_nhds, mem_singleton, pure_le_nhds
-/
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]
/--
theorem `nhds_false` / 定理 `nhds_false`

English:
theorem nhds_false
  statement: 𝓝 False = ⊤
  proof: TopologicalSpace.nhds_generateFrom.trans by simp [@and_comm (_ in _)]

中文:
定理 nhds_false
  结论: 𝓝 假 = ⊤
  证明: TopologicalSpace.nhds_generateFrom.trans by simp [@and_comm (_ in _)]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.nhds_generateFrom.trans, and_comm, nhds_generateFrom
-/
theorem nhds_false : 𝓝 False = ⊤ :=
TopologicalSpace.nhds_generateFrom.trans by simp [@and_comm (_ in _)]

/--
theorem `tendsto_nhds_true` / 定理 `tendsto_nhds_true`

English:
theorem tendsto_nhds_true
  given: {l : Filter α} {p : α -> Prop}
  proof: by simp

中文:
定理 tendsto_nhds_true
  条件: {l : 滤子 α} {p : α -> 命题}
  证明: by simp
-/
theorem tendsto_nhds_true {l : Filter α} {p : α -> Prop} :
    Tendsto p l (𝓝 True) ↔ forallᶠ x in l, p x := by simp

/--
theorem `tendsto_nhds_Prop` / 定理 `tendsto_nhds_Prop`

English:
theorem tendsto_nhds_Prop
  given: {l : Filter α} {p : α -> Prop} {q : Prop}
  proof: by
  by_cases q <;> simp [*]

中文:
定理 tendsto_nhds_Prop
  条件: {l : 滤子 α} {p : α -> 命题} {q : 命题}
  证明: by
  by_cases q <;> simp [*]
-/
theorem tendsto_nhds_Prop {l : Filter α} {p : α -> Prop} {q : Prop} :
    Tendsto p l (𝓝 q) ↔ (q -> forallᶠ x in l, p x) := by
  by_cases q <;> simp [*]

variable [TopologicalSpace α]

/--
theorem `continuous_Prop` / 定理 `continuous_Prop`

English:
theorem continuous_Prop
  given: {p : α -> Prop}
  statement: Continuous p ↔ IsOpen { x | p x }
  proof: by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl

中文:
定理 continuous_Prop
  条件: {p : α -> 命题}
  结论: 连续 p ↔ 是开集 { x | p x }
  证明: by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, isOpen_iff_mem_nhds, tendsto_nhds_Prop
-/
theorem continuous_Prop {p : α -> Prop} : Continuous p ↔ IsOpen { x | p x } := by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl

/--
theorem `isOpen_iff_continuous_mem` / 定理 `isOpen_iff_continuous_mem`

English:
theorem isOpen_iff_continuous_mem
  given: {s : Set α}
  statement: IsOpen s ↔ Continuous (· in s)
  proof: continuous_Prop.symm

中文:
定理 isOpen_iff_continuous_mem
  条件: {s : 集合 α}
  结论: 是开集 s ↔ 连续 (· in s)
  证明: continuous_Prop.symm

Depends on / 依赖: continuous_Prop, continuous_Prop.symm
-/
theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous (· in s) :=
  continuous_Prop.symm

end Sierpinski

section iInf

open TopologicalSpace

variable {α : Type u} {ι : Sort v}

/--
theorem `generateFrom_union` / 定理 `generateFrom_union`

English:
theorem generateFrom_union
  given: (a₁ a₂ : Set (Set α))
  proof: (gc_generateFrom α).u_inf

中文:
定理 generateFrom_union
  条件: (a₁ a₂ : 集合 (集合 α))
  证明: (gc_generateFrom α).u_inf

Depends on / 依赖: gc_generateFrom, u_inf
-/
theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    generateFrom (a₁ union a₂) = generateFrom a₁ ⊓ generateFrom a₂ :=
  (gc_generateFrom α).u_inf

/--
theorem `setOfPred_isOpen_sup` / 定理 `setOfPred_isOpen_sup`

English:
theorem setOfPred_isOpen_sup
  given: (t₁ t₂ : TopologicalSpace α)
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sup := setOfPred_isOpen_sup

中文:
定理 setOfPred_isOpen_sup
  条件: (t₁ t₂ : 拓扑空间 α)
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sup := setOfPred_isOpen_sup
-/
theorem setOfPred_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | IsOpen[t₁ ⊔ t₂] s } = { s | IsOpen[t₁] s } inter { s | IsOpen[t₂] s } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sup := setOfPred_isOpen_sup

/--
theorem `generateFrom_iUnion` / 定理 `generateFrom_iUnion`

English:
theorem generateFrom_iUnion
  given: {f : ι -> Set (Set α)}
  proof: (gc_generateFrom α).u_iInf

中文:
定理 generateFrom_iUnion
  条件: {f : ι -> 集合 (集合 α)}
  证明: (gc_generateFrom α).u_iInf

Depends on / 依赖: gc_generateFrom, u_iInf
-/
theorem generateFrom_iUnion {f : ι -> Set (Set α)} :
    generateFrom (⋃ i, f i) = ⨅ i, generateFrom (f i) :=
  (gc_generateFrom α).u_iInf

/--
theorem `setOfPred_isOpen_iSup` / 定理 `setOfPred_isOpen_iSup`

English:
theorem setOfPred_isOpen_iSup
  given: {t : ι -> TopologicalSpace α}
  proof: (gc_generateFrom α).l_iSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_iSup := setOfPred_isOpen_iSup

中文:
定理 setOfPred_isOpen_iSup
  条件: {t : ι -> 拓扑空间 α}
  证明: (gc_generateFrom α).l_iSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_iSup := setOfPred_isOpen_iSup

Depends on / 依赖: gc_generateFrom, l_iSup
-/
theorem setOfPred_isOpen_iSup {t : ι -> TopologicalSpace α} :
    { s | IsOpen[⨆ i, t i] s } = ⋂ i, { s | IsOpen[t i] s } :=
  (gc_generateFrom α).l_iSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_iSup := setOfPred_isOpen_iSup

/--
theorem `generateFrom_sUnion` / 定理 `generateFrom_sUnion`

English:
theorem generateFrom_sUnion
  given: {S : Set (Set (Set α))}
  proof: (gc_generateFrom α).u_sInf

中文:
定理 generateFrom_sUnion
  条件: {S : 集合 (集合 (集合 α))}
  证明: (gc_generateFrom α).u_sInf

Depends on / 依赖: gc_generateFrom, u_sInf
-/
theorem generateFrom_sUnion {S : Set (Set (Set α))} :
    generateFrom (⋃₀ S) = ⨅ s in S, generateFrom s :=
  (gc_generateFrom α).u_sInf

/--
theorem `setOfPred_isOpen_sSup` / 定理 `setOfPred_isOpen_sSup`

English:
theorem setOfPred_isOpen_sSup
  given: {T : Set (TopologicalSpace α)}
  proof: (gc_generateFrom α).l_sSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sSup := setOfPred_isOpen_sSup

中文:
定理 setOfPred_isOpen_sSup
  条件: {T : 集合 (拓扑空间 α)}
  证明: (gc_generateFrom α).l_sSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sSup := setOfPred_isOpen_sSup

Depends on / 依赖: gc_generateFrom, l_sSup
-/
theorem setOfPred_isOpen_sSup {T : Set (TopologicalSpace α)} :
    { s | IsOpen[sSup T] s } = ⋂ t in T, { s | IsOpen[t] s } :=
  (gc_generateFrom α).l_sSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sSup := setOfPred_isOpen_sSup

/--
theorem `generateFrom_union_isOpen` / 定理 `generateFrom_union_isOpen`

English:
theorem generateFrom_union_isOpen
  given: (a b : TopologicalSpace α)
  proof: (gciGenerateFrom α).u_inf_l _ _

中文:
定理 generateFrom_union_isOpen
  条件: (a b : 拓扑空间 α)
  证明: (gciGenerateFrom α).u_inf_l _ _

Depends on / 依赖: gciGenerateFrom, u_inf_l
-/
theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } union { s | IsOpen[b] s }) = a ⊓ b :=
  (gciGenerateFrom α).u_inf_l _ _

/--
theorem `generateFrom_iUnion_isOpen` / 定理 `generateFrom_iUnion_isOpen`

English:
theorem generateFrom_iUnion_isOpen
  given: (f : ι -> TopologicalSpace α)
  proof: (gciGenerateFrom α).u_iInf_l _

中文:
定理 generateFrom_iUnion_isOpen
  条件: (f : ι -> 拓扑空间 α)
  证明: (gciGenerateFrom α).u_iInf_l _

Depends on / 依赖: gciGenerateFrom, u_iInf_l
-/
theorem generateFrom_iUnion_isOpen (f : ι -> TopologicalSpace α) :
    generateFrom (⋃ i, { s | IsOpen[f i] s }) = ⨅ i, f i :=
  (gciGenerateFrom α).u_iInf_l _

/--
theorem `generateFrom_inter` / 定理 `generateFrom_inter`

English:
theorem generateFrom_inter
  given: (a b : TopologicalSpace α)
  proof: (gciGenerateFrom α).u_sup_l _ _

中文:
定理 generateFrom_inter
  条件: (a b : 拓扑空间 α)
  证明: (gciGenerateFrom α).u_sup_l _ _

Depends on / 依赖: gciGenerateFrom, u_sup_l
-/
theorem generateFrom_inter (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } inter { s | IsOpen[b] s }) = a ⊔ b :=
  (gciGenerateFrom α).u_sup_l _ _

/--
theorem `generateFrom_iInter` / 定理 `generateFrom_iInter`

English:
theorem generateFrom_iInter
  given: (f : ι -> TopologicalSpace α)
  proof: (gciGenerateFrom α).u_iSup_l _

中文:
定理 generateFrom_i整数er
  条件: (f : ι -> 拓扑空间 α)
  证明: (gciGenerateFrom α).u_iSup_l _

Depends on / 依赖: gciGenerateFrom, u_iSup_l
-/
theorem generateFrom_iInter (f : ι -> TopologicalSpace α) :
    generateFrom (⋂ i, { s | IsOpen[f i] s }) = ⨆ i, f i :=
  (gciGenerateFrom α).u_iSup_l _

/--
theorem `generateFrom_iInter_of_generateFrom_eq_self` / 定理 `generateFrom_iInter_of_generateFrom_eq_self`

English:
theorem generateFrom_iInter_of_generateFrom_eq_self
  statement: (f : ι -> Set (Set α))
  proof: (gciGenerateFrom α).u_iSup_of_l_u_eq_self f hf

中文:
定理 generateFrom_i整数er_of_generateFrom_eq_self
  结论: (f : ι -> 集合 (集合 α))
  证明: (gciGenerateFrom α).u_iSup_of_l_u_eq_self f hf

Depends on / 依赖: gciGenerateFrom, u_iSup_of_l_u_eq_self
-/
theorem generateFrom_iInter_of_generateFrom_eq_self (f : ι -> Set (Set α))
    (hf : forall i, { s | IsOpen[generateFrom (f i)] s } = f i) :
    generateFrom (⋂ i, f i) = ⨆ i, generateFrom (f i) :=
  (gciGenerateFrom α).u_iSup_of_l_u_eq_self f hf

variable {t : ι -> TopologicalSpace α}

/--
theorem `isOpen_iSup_iff` / 定理 `isOpen_iSup_iff`

English:
theorem isOpen_iSup_iff
  given: {s : Set α}
  statement: IsOpen[⨆ i, t i] s ↔ forall i, IsOpen[t i] s
  proof: show s in {s | IsOpen[iSup t] s} ↔ s in { x : Set α | forall i : ι, IsOpen[t i] x } by
    simp [setOfPred_isOpen_iSup]

中文:
定理 isOpen_iSup_iff
  条件: {s : 集合 α}
  结论: 是开集[⨆ i, t i] s ↔ 对任意 i, 是开集[t i] s
  证明: show s in {s | IsOpen[iSup t] s} ↔ s in { x : Set α | forall i : ι, IsOpen[t i] x } by
    simp [setOfPred_isOpen_iSup]

Depends on / 依赖: IsOpen, setOfPred_isOpen_iSup
-/
theorem isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ forall i, IsOpen[t i] s :=
  show s in {s | IsOpen[iSup t] s} ↔ s in { x : Set α | forall i : ι, IsOpen[t i] x } by
    simp [setOfPred_isOpen_iSup]

/--
theorem `isOpen_sSup_iff` / 定理 `isOpen_sSup_iff`

English:
theorem isOpen_sSup_iff
  given: {s : Set α} {T : Set (TopologicalSpace α)}
  proof: by
  simp +instances only [sSup_eq_iSup, isOpen_iSup_iff]

中文:
定理 isOpen_sSup_iff
  条件: {s : 集合 α} {T : 集合 (拓扑空间 α)}
  证明: by
  simp +instances only [sSup_eq_iSup, isOpen_iSup_iff]

Depends on / 依赖: instances, isOpen_iSup_iff, sSup_eq_iSup
-/
theorem isOpen_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsOpen[sSup T] s ↔ forall t in T, IsOpen[t] s := by
  simp +instances only [sSup_eq_iSup, isOpen_iSup_iff]

/--
theorem `isClosed_iSup_iff` / 定理 `isClosed_iSup_iff`

English:
theorem isClosed_iSup_iff
  given: {s : Set α}
  statement: IsClosed[⨆ i, t i] s ↔ forall i, IsClosed[t i] s
  proof: by
  simp only [← @isOpen_compl_iff _ _ (⨆ i, t i), ← @isOpen_compl_iff _ _ (t _), isOpen_iSup_iff]

中文:
定理 isClosed_iSup_iff
  条件: {s : 集合 α}
  结论: 是闭集[⨆ i, t i] s ↔ 对任意 i, 是闭集[t i] s
  证明: by
  simp only [← @isOpen_compl_iff _ _ (⨆ i, t i), ← @isOpen_compl_iff _ _ (t _), isOpen_iSup_iff]

Depends on / 依赖: isOpen_compl_iff, isOpen_iSup_iff
-/
theorem isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s ↔ forall i, IsClosed[t i] s := by
  simp only [← @isOpen_compl_iff _ _ (⨆ i, t i), ← @isOpen_compl_iff _ _ (t _), isOpen_iSup_iff]

/--
theorem `isClosed_sSup_iff` / 定理 `isClosed_sSup_iff`

English:
theorem isClosed_sSup_iff
  given: {s : Set α} {T : Set (TopologicalSpace α)}
  proof: by
  simp +instances only [sSup_eq_iSup, isClosed_iSup_iff]

中文:
定理 isClosed_sSup_iff
  条件: {s : 集合 α} {T : 集合 (拓扑空间 α)}
  证明: by
  simp +instances only [sSup_eq_iSup, isClosed_iSup_iff]

Depends on / 依赖: instances, isClosed_iSup_iff, sSup_eq_iSup
-/
theorem isClosed_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsClosed[sSup T] s ↔ forall t in T, IsClosed[t] s := by
  simp +instances only [sSup_eq_iSup, isClosed_iSup_iff]

end iInf
