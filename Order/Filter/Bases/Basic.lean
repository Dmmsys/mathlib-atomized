/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Set.Sigma
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Interval.Set.Basic

/-!
# Basic results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : Filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → Set α`,
the proposition `h : Filter.IsBasis p s` makes sure the range of `s` bounded by `p`
(i.e. `s '' Set.ofPred p`) defines a filter basis `h.filterBasis`.

If one already has a filter `l` on `α`, `Filter.HasBasis l p s` (where `p : ι → Prop`
and `s : ι → Set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : Filter.IsBasis p s`, and
`l = h.filterBasis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `HasBasis.index (h : Filter.HasBasis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

## Main statements

* `Filter.HasBasis.mem_iff`, `HasBasis.mem_of_superset`, `HasBasis.mem_of_mem` : restate `t ∈ f` in
  terms of a basis;

* `Filter.HasBasis.le_iff`, `Filter.HasBasis.ge_iff`, `Filter.HasBasis.le_basis_iff` : restate
  `l ≤ l'` in terms of bases.

* `Filter.basis_sets` : all sets of a filter form a basis;

* `Filter.HasBasis.inf`, `Filter.HasBasis.inf_principal`, `Filter.HasBasis.prod`,
  `Filter.HasBasis.prod_self`, `Filter.HasBasis.map`, `Filter.HasBasis.comap` : combinators to
  construct filters of `l ⊓ l'`, `l ⊓ 𝓟 t`, `l ×ˢ l'`, `l ×ˢ l`, `l.map f`, `l.comap f`
  respectively;

* `Filter.HasBasis.tendsto_right_iff`, `Filter.HasBasis.tendsto_left_iff`,
  `Filter.HasBasis.tendsto_iff` : restate `Tendsto f l l'` in terms of bases.

## Implementation notes

As with `Set.iUnion`/`biUnion`/`Set.sUnion`, there are three different approaches to filter bases:

* `Filter.HasBasis l s`, `s : Set (Set α)`;
* `Filter.HasBasis l s`, `s : ι → Set α`;
* `Filter.HasBasis l p s`, `p : ι → Prop`, `s : ι → Set α`.

We use the latter one because, e.g., `𝓝 x` in an `EMetricSpace` or in a `MetricSpace` has a basis
of this form. The other two can be emulated using `s = id` or `p = fun _ ↦ True`.

With this approach sometimes one needs to `simp` the statement provided by the `Filter.HasBasis`
machinery, e.g., `simp only [true_and_iff]` or `simp only [forall_const]` can help with the case
`p = fun _ ↦ True`.

## Main statements
-/

@[expose] public section

assert_not_exists Finset

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

/--
Definition of `FilterBasis` / `FilterBasis` 的定义

English:
structure FilterBasis
  parameters: (α : Type*)
  axioms and operations (3):
    - sets : Set (Set α)
    - nonempty : sets.Nonempty
    - inter_sets({x y}) : x in sets -> y in sets -> exists z in sets, z subseteq x inter y

中文:
结构 FilterBasis
  参数: (α : 类型)
  公理与运算 (3 个):
    - sets : Set (Set α)
    - nonempty : sets.Nonempty
    - inter_sets({x y}) : x in sets -> y in sets -> 存在 z in sets, z subseteq x inter y
-/
structure FilterBasis (α : Type*) where
  /-- Sets of a filter basis. -/
  sets : Set (Set α)
  /-- The set of filter basis sets is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis sets is directed downwards. -/
  inter_sets {x y} : x in sets -> y in sets -> exists z in sets, z subseteq x inter y

/--
Instance `FilterBasis.nonempty_sets` / 实例 `FilterBasis.nonempty_sets`

English:
instance FilterBasis.nonempty_sets
  signature: (B : FilterBasis α)
  body: B.nonempty.to_subtype

中文:
实例 FilterBasis.nonempty_sets
  签名: (B : FilterBasis α)
  定义体: B.nonempty.to_subtype

Depends on / 依赖: B.nonempty.to_subtype, nonempty, to_subtype
-/
instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.nonempty.to_subtype

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
instance {α : Type*} : Membership (Set α) (FilterBasis α) :=
  ⟨fun B U => U in B.sets⟩

/--
theorem `FilterBasis.mem_sets` / 定理 `FilterBasis.mem_sets`

English:
theorem FilterBasis.mem_sets
  given: {s : Set α} {B : FilterBasis α}
  statement: s in B.sets ↔ s in B
  proof: Iff.rfl

中文:
定理 FilterBasis.mem_sets
  条件: {s : Set α} {B : FilterBasis α}
  结论: s in B.sets ↔ s in B
  证明: Iff.rfl
-/
@[simp] theorem FilterBasis.mem_sets {s : Set α} {B : FilterBasis α} : s in B.sets ↔ s in B := Iff.rfl

-- For illustration purposes, the filter basis defining `(atTop : Filter ℕ)`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FilterBasis Nat)
  body: ⟨{ sets := range Ici
      nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨Ici (max n m), mem_range_self _, Ici_inter_Ici.symm.subset⟩ }⟩

中文:
实例 :
  签名: Inhabited (FilterBasis 自然数)
  定义体: ⟨{ sets := range Ici
      nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨Ici (max n m), mem_range_self _, Ici_inter_Ici.symm.subset⟩ }⟩

Depends on / 依赖: Ici_inter_Ici, Ici_inter_Ici.symm.subset, inter_sets, mem_range_self, nonempty, subset
-/
instance : Inhabited (FilterBasis Nat) :=
  ⟨{ sets := range Ici
      nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨Ici (max n m), mem_range_self _, Ici_inter_Ici.symm.subset⟩ }⟩

/--
Definition of `Filter.asBasis` / `Filter.asBasis` 的定义

English:
definition Filter.asBasis
  signature: (f : Filter α)
  body: ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x inter y, inter_mem hx hy, subset_rfl⟩⟩

中文:
定义 Filter.asBasis
  签名: (f : Filter α)
  定义体: ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x inter y, inter_mem hx hy, subset_rfl⟩⟩

Depends on / 依赖: f.sets, inter_mem, subset_rfl, univ_mem
-/
def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun {x y} hx hy => ⟨x inter y, inter_mem hx hy, subset_rfl⟩⟩

-- TODO: consider adding `protected`?
/--
Definition of `Filter.IsBasis` / `Filter.IsBasis` 的定义

English:
structure Filter.IsBasis
  parameters: (p : ι -> Prop) (s : ι -> Set α)
  axioms and operations (2):
    - nonempty : exists i, p i
    - inter : forall {i j}, p i -> p j -> exists k, p k ∧ s k subseteq s i inter s j

中文:
结构 Filter.IsBasis
  参数: (p : ι -> 命题) (s : ι -> Set α)
  公理与运算 (2 个):
    - nonempty : 存在 i, p i
    - inter : 对任意 {i j}, p i -> p j -> 存在 k, p k ∧ s k subseteq s i inter s j
-/
structure Filter.IsBasis (p : ι -> Prop) (s : ι -> Set α) : Prop where
  /-- There exists at least one `i` that satisfies `p`. -/
  nonempty : exists i, p i
  /-- `s` is directed downwards on `i` such that `p i`. -/
  inter : forall {i j}, p i -> p j -> exists k, p k ∧ s k subseteq s i inter s j

namespace Filter

namespace IsBasis

/--
Definition of `filterBasis` / `filterBasis` 的定义

English:
definition filterBasis
  signature: {p : ι -> Prop} {s : ι -> Set α} (h : IsBasis p s)
  body: { t | exists i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩

中文:
定义 filterBasis
  签名: {p : ι -> 命题} {s : ι -> Set α} (h : IsBasis p s)
  定义体: { t | exists i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩
-/
protected def filterBasis {p : ι -> Prop} {s : ι -> Set α} (h : IsBasis p s) : FilterBasis α where
  sets := { t | exists i, p i ∧ s i = t }
  nonempty :=
    let ⟨i, hi⟩ := h.nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩

variable {p : ι -> Prop} {s : ι -> Set α} (h : IsBasis p s)

/--
theorem `mem_filterBasis_iff` / 定理 `mem_filterBasis_iff`

English:
theorem mem_filterBasis_iff
  given: {U : Set α}
  statement: U in h.filterBasis ↔ exists i, p i ∧ s i = U
  proof: Iff.rfl

中文:
定理 mem_filterBasis_iff
  条件: {U : Set α}
  结论: U in h.filterBasis ↔ 存在 i, p i ∧ s i = U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_filterBasis_iff {U : Set α} : U in h.filterBasis ↔ exists i, p i ∧ s i = U :=
  Iff.rfl

end IsBasis

end Filter

namespace FilterBasis

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (B : FilterBasis α)
  body: { s | exists t in B, t subseteq s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, 

中文:
定义 filter
  签名: (B : FilterBasis α)
  定义体: { s | exists t in B, t subseteq s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, 
-/
protected def filter (B : FilterBasis α) : Filter α where
  sets := { s | exists t in B, t subseteq s }
  univ_sets := B.nonempty.imp fun s s_in => ⟨s_in, s.subset_univ⟩
  sets_of_superset := fun ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun ⟨_s, s_in, hs⟩ ⟨_t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, u_sub.trans (inter_subset_inter hs ht)⟩

/--
theorem `mem_filter_iff` / 定理 `mem_filter_iff`

English:
theorem mem_filter_iff
  given: (B : FilterBasis α) {U : Set α}
  statement: U in B.filter ↔ exists s in B, s subseteq U
  proof: Iff.rfl

中文:
定理 mem_filter_iff
  条件: (B : FilterBasis α) {U : Set α}
  结论: U in B.filter ↔ 存在 s in B, s subseteq U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U in B.filter ↔ exists s in B, s subseteq U :=
  Iff.rfl

/--
theorem `mem_filter_of_mem` / 定理 `mem_filter_of_mem`

English:
theorem mem_filter_of_mem
  given: (B : FilterBasis α) {U : Set α}
  statement: U in B -> U in B.filter
  proof: fun U_in =>
  ⟨U, U_in, Subset.refl _⟩

中文:
定理 mem_filter_of_mem
  条件: (B : FilterBasis α) {U : Set α}
  结论: U in B -> U in B.filter
  证明: fun U_in =>
  ⟨U, U_in, Subset.refl _⟩

Depends on / 依赖: U_in
-/
theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U in B -> U in B.filter := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩

/--
theorem `eq_iInf_principal` / 定理 `eq_iInf_principal`

English:
theorem eq_iInf_principal
  given: (B : FilterBasis α)
  statement: B.filter = ⨅ s : B.sets, 𝓟 s
  proof: by
  have : Directed (· >= ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of

中文:
定理 eq_iInf_principal
  条件: (B : FilterBasis α)
  结论: B.filter = ⨅ s : B.sets, 𝓟 s
  证明: by
  have : Directed (· >= ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of

Depends on / 依赖: B.inter_sets, B.sets, Directed, U_in, V_in, W_in, W_sub, inter_sets, le_principal_iff, mem_filter_iff, mem_iInf_of_directed, mem_principal, subset_inter_iff, subset_inter_iff.mp
-/
theorem eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s := by
  have : Directed (· >= ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of_directed this]

/--
theorem `generate` / 定理 `generate`

English:
theorem generate
  given: (B : FilterBasis α)
  statement: generate B.sets = B.filter
  proof: by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem

中文:
定理 generate
  条件: (B : FilterBasis α)
  结论: generate B.sets = B.filter
  证明: by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem
-/
protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter := by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem

/--
lemma `ker_filter` / 引理 `ker_filter`

English:
lemma ker_filter
  given: (F : FilterBasis α)
  statement: F.filter.ker = ⋂₀ F.sets
  proof: by
  aesop (add simp [ker, FilterBasis.filter])

中文:
引理 ker_filter
  条件: (F : FilterBasis α)
  结论: F.filter.ker = ⋂₀ F.sets
  证明: by
  aesop (add simp [ker, FilterBasis.filter])

Depends on / 依赖: FilterBasis, FilterBasis.filter, filter
-/
lemma ker_filter (F : FilterBasis α) : F.filter.ker = ⋂₀ F.sets := by
  aesop (add simp [ker, FilterBasis.filter])

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι -> Prop} {s : ι -> Set α}

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (h : IsBasis p s)
  body: h.filterBasis.filter

中文:
定义 filter
  签名: (h : IsBasis p s)
  定义体: h.filterBasis.filter
-/
protected def filter (h : IsBasis p s) : Filter α :=
  h.filterBasis.filter

/--
theorem `mem_filter_iff` / 定理 `mem_filter_iff`

English:
theorem mem_filter_iff
  given: (h : IsBasis p s) {U : Set α}
  proof: by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]

中文:
定理 mem_filter_iff
  条件: (h : IsBasis p s) {U : Set α}
  证明: by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]
-/
protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U in h.filter ↔ exists i, p i ∧ s i subseteq U := by
  simp only [IsBasis.filter, FilterBasis.mem_filter_iff, mem_filterBasis_iff,
    exists_exists_and_eq_and]

/--
theorem `filter_eq_generate` / 定理 `filter_eq_generate`

English:
theorem filter_eq_generate
  given: (h : IsBasis p s)
  statement: h.filter = generate { U | exists i, p i ∧ s i = U }
  proof: by
  rw [IsBasis.filter]; rw [← h.filterBasis.generate]; rw [IsBasis.filterBasis]

中文:
定理 filter_eq_generate
  条件: (h : IsBasis p s)
  结论: h.filter = generate { U | 存在 i, p i ∧ s i = U }
  证明: by
  rw [IsBasis.filter]; rw [← h.filterBasis.generate]; rw [IsBasis.filterBasis]

Depends on / 依赖: IsBasis, IsBasis.filter, IsBasis.filterBasis, filter, filterBasis, generate, h.filterBasis.generate
-/
theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | exists i, p i ∧ s i = U } := by
  rw [IsBasis.filter]; rw [← h.filterBasis.generate]; rw [IsBasis.filterBasis]

end IsBasis

-- TODO: consider adding `protected`?
/--
Definition of `HasBasis` / `HasBasis` 的定义

English:
structure HasBasis
  parameters: (l : Filter α) (p : ι -> Prop) (s : ι -> Set α)
  axioms and operations (1):
    - mem_iff' : forall t : Set α, t in l ↔ exists i, p i ∧ s i subseteq t

中文:
结构 HasBasis
  参数: (l : Filter α) (p : ι -> 命题) (s : ι -> Set α)
  公理与运算 (1 个):
    - mem_iff' : 对任意 t : Set α, t in l ↔ 存在 i, p i ∧ s i subseteq t
-/
structure HasBasis (l : Filter α) (p : ι -> Prop) (s : ι -> Set α) : Prop where
  /-- A set `t` belongs to a filter `l` iff it includes an element of the basis. -/
  mem_iff' : forall t : Set α, t in l ↔ exists i, p i ∧ s i subseteq t

section SameType

variable {l l' : Filter α} {p : ι -> Prop} {s : ι -> Set α} {t : Set α} {i : ι} {p' : ι' -> Prop}
  {s' : ι' -> Set α} {i' : ι'}

/--
theorem `HasBasis.mem_iff` / 定理 `HasBasis.mem_iff`

English:
theorem HasBasis.mem_iff
  given: (hl : l.HasBasis p s)
  statement: t in l ↔ exists i, p i ∧ s i subseteq t
  proof: hl.mem_iff' t

中文:
定理 HasBasis.mem_iff
  条件: (hl : l.HasBasis p s)
  结论: t in l ↔ 存在 i, p i ∧ s i subseteq t
  证明: hl.mem_iff' t

Depends on / 依赖: hl.mem_iff, mem_iff
-/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t in l ↔ exists i, p i ∧ s i subseteq t :=
  hl.mem_iff' t

/--
theorem `HasBasis.eq_of_same_basis` / 定理 `HasBasis.eq_of_same_basis`

English:
theorem HasBasis.eq_of_same_basis
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p s)
  statement: l = l'
  proof: by
  ext t
  rw [hl.mem_iff]; rw [hl'.mem_iff]

中文:
定理 HasBasis.eq_of_same_basis
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p s)
  结论: l = l'
  证明: by
  ext t
  rw [hl.mem_iff]; rw [hl'.mem_iff]

Depends on / 依赖: hl.mem_iff, mem_iff
-/
theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' := by
  ext t
  rw [hl.mem_iff]; rw [hl'.mem_iff]

/--
theorem `hasBasis_iff` / 定理 `hasBasis_iff`

English:
theorem hasBasis_iff
  statement: l.HasBasis p s ↔ forall t, t in l ↔ exists i, p i ∧ s i subseteq t
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
定理 hasBasis_iff
  结论: l.HasBasis p s ↔ 对任意 t, t in l ↔ 存在 i, p i ∧ s i subseteq t
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
theorem hasBasis_iff : l.HasBasis p s ↔ forall t, t in l ↔ exists i, p i ∧ s i subseteq t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
theorem `HasBasis.ex_mem` / 定理 `HasBasis.ex_mem`

English:
theorem HasBasis.ex_mem
  given: (h : l.HasBasis p s)
  statement: exists i, p i
  proof: (h.mem_iff.mp univ_mem).imp fun _ => And.left

中文:
定理 HasBasis.ex_mem
  条件: (h : l.HasBasis p s)
  结论: 存在 i, p i
  证明: (h.mem_iff.mp univ_mem).imp fun _ => And.left

Depends on / 依赖: And.left, h.mem_iff.mp, mem_iff, univ_mem
-/
theorem HasBasis.ex_mem (h : l.HasBasis p s) : exists i, p i :=
  (h.mem_iff.mp univ_mem).imp fun _ => And.left

/--
theorem `HasBasis.nonempty` / 定理 `HasBasis.nonempty`

English:
theorem HasBasis.nonempty
  given: (h : l.HasBasis p s)
  statement: Nonempty ι
  proof: h.ex_mem.nonempty

中文:
定理 HasBasis.nonempty
  条件: (h : l.HasBasis p s)
  结论: Nonempty ι
  证明: h.ex_mem.nonempty
-/
protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  h.ex_mem.nonempty

/--
theorem `IsBasis.hasBasis` / 定理 `IsBasis.hasBasis`

English:
theorem IsBasis.hasBasis
  given: (h : IsBasis p s)
  statement: HasBasis h.filter p s
  proof: ⟨fun t => by simp only [h.mem_filter_iff]⟩

中文:
定理 IsBasis.hasBasis
  条件: (h : IsBasis p s)
  结论: HasBasis h.filter p s
  证明: ⟨fun t => by simp only [h.mem_filter_iff]⟩
-/
protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filter p s :=
  ⟨fun t => by simp only [h.mem_filter_iff]⟩

/--
theorem `HasBasis.mem_of_superset` / 定理 `HasBasis.mem_of_superset`

English:
theorem HasBasis.mem_of_superset
  given: (hl : l.HasBasis p s) (hi : p i) (ht : s i subseteq t)
  proof: hl.mem_iff.2 ⟨i, hi, ht⟩

中文:
定理 HasBasis.mem_of_superset
  条件: (hl : l.HasBasis p s) (hi : p i) (ht : s i subseteq t)
  证明: hl.mem_iff.2 ⟨i, hi, ht⟩
-/
protected theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i subseteq t) :
    t in l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩

/--
theorem `HasBasis.mem_of_mem` / 定理 `HasBasis.mem_of_mem`

English:
theorem HasBasis.mem_of_mem
  given: (hl : l.HasBasis p s) (hi : p i)
  statement: s i in l
  proof: hl.mem_of_superset hi Subset.rfl

中文:
定理 HasBasis.mem_of_mem
  条件: (hl : l.HasBasis p s) (hi : p i)
  结论: s i in l
  证明: hl.mem_of_superset hi Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, hl.mem_of_superset, mem_of_superset
-/
theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i in l :=
  hl.mem_of_superset hi Subset.rfl

/--
Definition of `HasBasis.index` / `HasBasis.index` 的定义

English:
definition HasBasis.index
  signature: (h : l.HasBasis p s) (t : Set α) (ht : t in l)
  body: ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩

中文:
定义 HasBasis.index
  签名: (h : l.HasBasis p s) (t : Set α) (ht : t in l)
  定义体: ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩

Depends on / 依赖: choose_spec, h.mem_iff, mem_iff
-/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t in l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).choose, (h.mem_iff.1 ht).choose_spec.1⟩

/--
theorem `HasBasis.property_index` / 定理 `HasBasis.property_index`

English:
theorem HasBasis.property_index
  given: (h : l.HasBasis p s) (ht : t in l)
  statement: p (h.index t ht)
  proof: (h.index t ht).2

中文:
定理 HasBasis.property_index
  条件: (h : l.HasBasis p s) (ht : t in l)
  结论: p (h.index t ht)
  证明: (h.index t ht).2

Depends on / 依赖: h.index
-/
theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t in l) : p (h.index t ht) :=
  (h.index t ht).2

/--
theorem `HasBasis.set_index_mem` / 定理 `HasBasis.set_index_mem`

English:
theorem HasBasis.set_index_mem
  given: (h : l.HasBasis p s) (ht : t in l)
  statement: s (h.index t ht) in l
  proof: h.mem_of_mem h.property_index _

中文:
定理 HasBasis.set_index_mem
  条件: (h : l.HasBasis p s) (ht : t in l)
  结论: s (h.index t ht) in l
  证明: h.mem_of_mem h.property_index _

Depends on / 依赖: h.mem_of_mem, h.property_index, mem_of_mem, property_index
-/
theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t in l) : s (h.index t ht) in l :=
h.mem_of_mem h.property_index _

/--
theorem `HasBasis.set_index_subset` / 定理 `HasBasis.set_index_subset`

English:
theorem HasBasis.set_index_subset
  given: (h : l.HasBasis p s) (ht : t in l)
  statement: s (h.index t ht) subseteq t
  proof: (h.mem_iff.1 ht).choose_spec.2

中文:
定理 HasBasis.set_index_subset
  条件: (h : l.HasBasis p s) (ht : t in l)
  结论: s (h.index t ht) subseteq t
  证明: (h.mem_iff.1 ht).choose_spec.2

Depends on / 依赖: choose_spec, h.mem_iff, mem_iff
-/
theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t in l) : s (h.index t ht) subseteq t :=
  (h.mem_iff.1 ht).choose_spec.2

/--
theorem `HasBasis.isBasis` / 定理 `HasBasis.isBasis`

English:
theorem HasBasis.isBasis
  given: (h : l.HasBasis p s)
  statement: IsBasis p s where
  proof: h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)

中文:
定理 HasBasis.isBasis
  条件: (h : l.HasBasis p s)
  结论: IsBasis p s where
  证明: h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)

Depends on / 依赖: ex_mem, h.ex_mem
-/
theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s where
  nonempty := h.ex_mem
  inter hi hj := by
    simpa only [h.mem_iff] using inter_mem (h.mem_of_mem hi) (h.mem_of_mem hj)

/--
theorem `HasBasis.filter_eq` / 定理 `HasBasis.filter_eq`

English:
theorem HasBasis.filter_eq
  given: (h : l.HasBasis p s)
  statement: h.isBasis.filter = l
  proof: by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]

中文:
定理 HasBasis.filter_eq
  条件: (h : l.HasBasis p s)
  结论: h.isBasis.filter = l
  证明: by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]

Depends on / 依赖: IsBasis, IsBasis.mem_filter_iff, h.mem_iff, mem_filter_iff, mem_iff
-/
theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.isBasis.filter = l := by
  ext U
  simp [h.mem_iff, IsBasis.mem_filter_iff]

/--
theorem `HasBasis.eq_generate` / 定理 `HasBasis.eq_generate`

English:
theorem HasBasis.eq_generate
  given: (h : l.HasBasis p s)
  statement: l = generate { U | exists i, p i ∧ s i = U }
  proof: by
  rw [← h.isBasis.filter_eq_generate]; rw [h.filter_eq]

中文:
定理 HasBasis.eq_generate
  条件: (h : l.HasBasis p s)
  结论: l = generate { U | 存在 i, p i ∧ s i = U }
  证明: by
  rw [← h.isBasis.filter_eq_generate]; rw [h.filter_eq]

Depends on / 依赖: filter_eq, filter_eq_generate, h.filter_eq, h.isBasis.filter_eq_generate, isBasis
-/
theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | exists i, p i ∧ s i = U } := by
  rw [← h.isBasis.filter_eq_generate]; rw [h.filter_eq]

/--
theorem `_root_.FilterBasis.hasBasis` / 定理 `_root_.FilterBasis.hasBasis`

English:
theorem _root_.FilterBasis.hasBasis
  given: (B : FilterBasis α)
  proof: ⟨fun _ => B.mem_filter_iff⟩

中文:
定理 _root_.FilterBasis.hasBasis
  条件: (B : FilterBasis α)
  证明: ⟨fun _ => B.mem_filter_iff⟩
-/
protected theorem _root_.FilterBasis.hasBasis (B : FilterBasis α) :
    HasBasis B.filter (fun s : Set α => s in B) id :=
  ⟨fun _ => B.mem_filter_iff⟩

/--
theorem `HasBasis.to_hasBasis'` / 定理 `HasBasis.to_hasBasis'`

English:
theorem HasBasis.to_hasBasis'
  statement: (hl : l.HasBasis p s) (h : forall i, p i -> exists i', p' i' ∧ s' i' subseteq s i)
  proof: by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩

中文:
定理 HasBasis.to_hasBasis'
  结论: (hl : l.HasBasis p s) (h : 对任意 i, p i -> 存在 i', p' i' ∧ s' i' subseteq s i)
  证明: by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩

Depends on / 依赖: hl.mem_iff, mem_iff, mem_of_superset, s.trans
-/
theorem HasBasis.to_hasBasis' (hl : l.HasBasis p s) (h : forall i, p i -> exists i', p' i' ∧ s' i' subseteq s i)
    (h' : forall i', p' i' -> s' i' in l) : l.HasBasis p' s' := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', hs's.trans ht⟩

/--
theorem `HasBasis.to_hasBasis` / 定理 `HasBasis.to_hasBasis`

English:
theorem HasBasis.to_hasBasis
  statement: (hl : l.HasBasis p s) (h : forall i, p i -> exists i', p' i' ∧ s' i' subseteq s i)
  proof: hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩

中文:
定理 HasBasis.to_hasBasis
  结论: (hl : l.HasBasis p s) (h : 对任意 i, p i -> 存在 i', p' i' ∧ s' i' subseteq s i)
  证明: hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩

Depends on / 依赖: hl.mem_iff, hl.to_hasBasis, mem_iff, to_hasBasis
-/
theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : forall i, p i -> exists i', p' i' ∧ s' i' subseteq s i)
    (h' : forall i', p' i' -> exists i, p i ∧ s i subseteq s' i') : l.HasBasis p' s' :=
  hl.to_hasBasis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩

/--
lemma `HasBasis.congr` / 引理 `HasBasis.congr`

English:
lemma HasBasis.congr
  statement: (hl : l.HasBasis p s) {p' s'} (hp : forall i, p i ↔ p' i)
  proof: ⟨fun t => by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i =>
    and_congr_right fun hi => hs i hi ▸ Iff.rfl⟩

中文:
引理 HasBasis.congr
  结论: (hl : l.HasBasis p s) {p' s'} (hp : 对任意 i, p i ↔ p' i)
  证明: ⟨fun t => by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i =>
    and_congr_right fun hi => hs i hi ▸ Iff.rfl⟩
-/
protected lemma HasBasis.congr (hl : l.HasBasis p s) {p' s'} (hp : forall i, p i ↔ p' i)
    (hs : forall i, p i -> s i = s' i) : l.HasBasis p' s' :=
  ⟨fun t => by simp only [hl.mem_iff, ← hp]; exact exists_congr fun i =>
    and_congr_right fun hi => hs i hi ▸ Iff.rfl⟩

/--
theorem `HasBasis.to_subset` / 定理 `HasBasis.to_subset`

English:
theorem HasBasis.to_subset
  statement: (hl : l.HasBasis p s) {t : ι -> Set α} (h : forall i, p i -> t i subseteq s i)
  proof: hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht

中文:
定理 HasBasis.to_subset
  结论: (hl : l.HasBasis p s) {t : ι -> Set α} (h : 对任意 i, p i -> t i subseteq s i)
  证明: hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht

Depends on / 依赖: hl.to_hasBasis, to_hasBasis
-/
theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι -> Set α} (h : forall i, p i -> t i subseteq s i)
    (ht : forall i, p i -> t i in l) : l.HasBasis p t :=
  hl.to_hasBasis' (fun i hi => ⟨i, hi, h i hi⟩) ht

/--
theorem `HasBasis.eventually_iff` / 定理 `HasBasis.eventually_iff`

English:
theorem HasBasis.eventually_iff
  given: (hl : l.HasBasis p s) {q : α -> Prop}
  proof: by simpa using! hl.mem_iff

中文:
定理 HasBasis.eventually_iff
  条件: (hl : l.HasBasis p s) {q : α -> 命题}
  证明: by simpa using! hl.mem_iff

Depends on / 依赖: hl.mem_iff, mem_iff
-/
theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α -> Prop} :
    (forallᶠ x in l, q x) ↔ exists i, p i ∧ forall ⦃x⦄, x in s i -> q x := by simpa using! hl.mem_iff

/--
theorem `HasBasis.frequently_iff` / 定理 `HasBasis.frequently_iff`

English:
theorem HasBasis.frequently_iff
  given: (hl : l.HasBasis p s) {q : α -> Prop}
  proof: by
  simp only [Filter.Frequently, hl.eventually_iff]; push Not; rfl

中文:
定理 HasBasis.frequently_iff
  条件: (hl : l.HasBasis p s) {q : α -> 命题}
  证明: by
  simp only [Filter.Frequently, hl.eventually_iff]; push Not; rfl

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_iff, hl.eventually_iff
-/
theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α -> Prop} :
    (existsᶠ x in l, q x) ↔ forall i, p i -> exists x in s i, q x := by
  simp only [Filter.Frequently, hl.eventually_iff]; push Not; rfl

/--
theorem `HasBasis.exists_iff` / 定理 `HasBasis.exists_iff`

English:
theorem HasBasis.exists_iff
  statement: (hl : l.HasBasis p s) {P : Set α -> Prop}
  proof: ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩

中文:
定理 HasBasis.exists_iff
  结论: (hl : l.HasBasis p s) {P : Set α -> 命题}
  证明: ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩

Depends on / 依赖: hl.mem_iff, hl.mem_of_mem, mem_iff, mem_of_mem
-/
theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α -> Prop}
    (mono : forall ⦃s t⦄, s subseteq t -> P t -> P s) : (exists s in l, P s) ↔ exists i, p i ∧ P (s i) :=
  ⟨fun ⟨_s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩

/--
theorem `HasBasis.forall_iff` / 定理 `HasBasis.forall_iff`

English:
theorem HasBasis.forall_iff
  statement: (hl : l.HasBasis p s) {P : Set α -> Prop}
  proof: ⟨fun H i hi => H (s i) hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩

中文:
定理 HasBasis.forall_iff
  结论: (hl : l.HasBasis p s) {P : Set α -> 命题}
  证明: ⟨fun H i hi => H (s i) hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩

Depends on / 依赖: hl.mem_iff, hl.mem_of_mem, mem_iff, mem_of_mem
-/
theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α -> Prop}
    (mono : forall ⦃s t⦄, s subseteq t -> P s -> P t) : (forall s in l, P s) ↔ forall i, p i -> P (s i) :=
⟨fun H i hi => H (s i) hl.mem_of_mem hi, fun H _s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩

/--
theorem `HasBasis.neBot_iff` / 定理 `HasBasis.neBot_iff`

English:
theorem HasBasis.neBot_iff
  given: (hl : l.HasBasis p s)
  proof: forall_mem_nonempty_iff_neBot.symm.trans hl.forall_iff fun _ _ => Nonempty.mono

中文:
定理 HasBasis.neBot_iff
  条件: (hl : l.HasBasis p s)
  证明: forall_mem_nonempty_iff_neBot.symm.trans hl.forall_iff fun _ _ => Nonempty.mono
-/
protected theorem HasBasis.neBot_iff (hl : l.HasBasis p s) :
    NeBot l ↔ forall {i}, p i -> (s i).Nonempty :=
forall_mem_nonempty_iff_neBot.symm.trans hl.forall_iff fun _ _ => Nonempty.mono

/--
theorem `HasBasis.eq_bot_iff` / 定理 `HasBasis.eq_bot_iff`

English:
theorem HasBasis.eq_bot_iff
  given: (hl : l.HasBasis p s)
  statement: l = ⊥ ↔ exists i, p i ∧ s i = ∅
  proof: not_iff_not.1 neBot_iff.symm.trans
hl.neBot_iff.trans by simp only [not_exists, not_and, nonempty_iff_ne_empty]

中文:
定理 HasBasis.eq_bot_iff
  条件: (hl : l.HasBasis p s)
  结论: l = ⊥ ↔ 存在 i, p i ∧ s i = ∅
  证明: not_iff_not.1 neBot_iff.symm.trans
hl.neBot_iff.trans by simp only [not_exists, not_and, nonempty_iff_ne_empty]

Depends on / 依赖: RingHom, RingHom.ker_isPrime, convert, hl.neBot_iff.trans, ker_isPrime, neBot_iff, neBot_iff.symm.trans, nonempty_iff_ne_empty, not_and, not_exists, not_iff_not
-/
theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ exists i, p i ∧ s i = ∅ :=
not_iff_not.1 neBot_iff.symm.trans
hl.neBot_iff.trans by simp only [not_exists, not_and, nonempty_iff_ne_empty]

/--
theorem `basis_sets` / 定理 `basis_sets`

English:
theorem basis_sets
  given: (l : Filter α)
  statement: l.HasBasis (fun s : Set α => s in l) id
  proof: ⟨fun _ => exists_mem_subset_iff.symm⟩

中文:
定理 basis_sets
  条件: (l : Filter α)
  结论: l.HasBasis (fun s : Set α => s in l) id
  证明: ⟨fun _ => exists_mem_subset_iff.symm⟩

Depends on / 依赖: RingHom, RingHom.ker_isMaximal_of_surjective, convert, exists_mem_subset_iff, exists_mem_subset_iff.symm, ker_isMaximal_of_surjective
-/
theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s in l) id :=
  ⟨fun _ => exists_mem_subset_iff.symm⟩

/--
theorem `asBasis_filter` / 定理 `asBasis_filter`

English:
theorem asBasis_filter
  given: (f : Filter α)
  statement: f.asBasis.filter = f
  proof: Filter.ext fun _ => exists_mem_subset_iff

中文:
定理 asBasis_filter
  条件: (f : Filter α)
  结论: f.asBasis.filter = f
  证明: Filter.ext fun _ => exists_mem_subset_iff

Depends on / 依赖: Filter, Filter.ext, exists_mem_subset_iff
-/
theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f :=
  Filter.ext fun _ => exists_mem_subset_iff

/--
theorem `hasBasis_self` / 定理 `hasBasis_self`

English:
theorem hasBasis_self
  given: {l : Filter α} {P : Set α -> Prop}
  proof: by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩

中文:
定理 hasBasis_self
  条件: {l : Filter α} {P : Set α -> 命题}
  证明: by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩

Depends on / 依赖: and_assoc, forall_congr, hasBasis_iff, mem_of_superset
-/
theorem hasBasis_self {l : Filter α} {P : Set α -> Prop} :
    HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r subseteq t := by
  simp only [hasBasis_iff, id, and_assoc]
  exact forall_congr' fun s =>
    ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, _, hts⟩ => mem_of_superset hl hts⟩⟩

/--
theorem `HasBasis.comp_surjective` / 定理 `HasBasis.comp_surjective`

English:
theorem HasBasis.comp_surjective
  given: (h : l.HasBasis p s) {g : ι' -> ι} (hg : Function.Surjective g)
  proof: ⟨fun _ => h.mem_iff.trans hg.exists⟩

中文:
定理 HasBasis.comp_surjective
  条件: (h : l.HasBasis p s) {g : ι' -> ι} (hg : Function.Surjective g)
  证明: ⟨fun _ => h.mem_iff.trans hg.exists⟩

Depends on / 依赖: h.mem_iff.trans, hg.exists, mem_iff
-/
theorem HasBasis.comp_surjective (h : l.HasBasis p s) {g : ι' -> ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun _ => h.mem_iff.trans hg.exists⟩

/--
theorem `HasBasis.comp_equiv` / 定理 `HasBasis.comp_equiv`

English:
theorem HasBasis.comp_equiv
  given: (h : l.HasBasis p s) (e : ι' ≃ ι)
  statement: l.HasBasis (p ∘ e) (s ∘ e)
  proof: h.comp_surjective e.surjective

中文:
定理 HasBasis.comp_equiv
  条件: (h : l.HasBasis p s) (e : ι' ≃ ι)
  结论: l.HasBasis (p ∘ e) (s ∘ e)
  证明: h.comp_surjective e.surjective

Depends on / 依赖: comp_surjective, e.surjective, h.comp_surjective, surjective
-/
theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_surjective e.surjective

/--
theorem `HasBasis.to_image_id'` / 定理 `HasBasis.to_image_id'`

English:
theorem HasBasis.to_image_id'
  given: (h : l.HasBasis p s)
  statement: l.HasBasis (fun t => exists i, p i ∧ s i = t) id
  proof: ⟨fun _ => by simp [h.mem_iff]⟩

中文:
定理 HasBasis.to_image_id'
  条件: (h : l.HasBasis p s)
  结论: l.HasBasis (fun t => 存在 i, p i ∧ s i = t) id
  证明: ⟨fun _ => by simp [h.mem_iff]⟩

Depends on / 依赖: h.mem_iff, mem_iff
-/
theorem HasBasis.to_image_id' (h : l.HasBasis p s) : l.HasBasis (fun t => exists i, p i ∧ s i = t) id :=
  ⟨fun _ => by simp [h.mem_iff]⟩

/--
theorem `HasBasis.to_image_id` / 定理 `HasBasis.to_image_id`

English:
theorem HasBasis.to_image_id
  given: {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} (h : l.HasBasis p s)
  proof: h.to_image_id'

中文:
定理 HasBasis.to_image_id
  条件: {ι : 类型} {p : ι -> 命题} {s : ι -> Set α} (h : l.HasBasis p s)
  证明: h.to_image_id'

Depends on / 依赖: h.to_image_id, to_image_id
-/
theorem HasBasis.to_image_id {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} (h : l.HasBasis p s) :
    l.HasBasis (· in s '' {i | p i}) id :=
  h.to_image_id'

/--
theorem `HasBasis.restrict` / 定理 `HasBasis.restrict`

English:
theorem HasBasis.restrict
  statement: (h : l.HasBasis p s) {q : ι -> Prop}
  proof: by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, hji.trans hti⟩

中文:
定理 HasBasis.restrict
  结论: (h : l.HasBasis p s) {q : ι -> 命题}
  证明: by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, hji.trans hti⟩

Depends on / 依赖: h.mem_iff, hji.trans, mem_iff
-/
theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι -> Prop}
    (hq : forall i, p i -> exists j, p j ∧ q j ∧ s j subseteq s i) : l.HasBasis (fun i => p i ∧ q i) s := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, hji.trans hti⟩

/--
theorem `HasBasis.restrict_subset` / 定理 `HasBasis.restrict_subset`

English:
theorem HasBasis.restrict_subset
  given: (h : l.HasBasis p s) {V : Set α} (hV : V in l)
  proof: h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩

中文:
定理 HasBasis.restrict_subset
  条件: (h : l.HasBasis p s) {V : Set α} (hV : V in l)
  证明: h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩

Depends on / 依赖: h.mem_iff, h.mem_of_mem, h.restrict, inter_mem, mem_iff, mem_of_mem, restrict, subset_inter_iff
-/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V in l) :
    l.HasBasis (fun i => p i ∧ s i subseteq V) s :=
  h.restrict fun _i hi => (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun _j hj =>
    ⟨hj.1, subset_inter_iff.1 hj.2⟩

/--
theorem `HasBasis.hasBasis_self_subset` / 定理 `HasBasis.hasBasis_self_subset`

English:
theorem HasBasis.hasBasis_self_subset
  statement: {p : Set α -> Prop} (h : l.HasBasis (fun s => s in l ∧ p s) id)
  proof: by
  simpa only [and_assoc] using! h.restrict_subset hV

中文:
定理 HasBasis.hasBasis_self_subset
  结论: {p : Set α -> 命题} (h : l.HasBasis (fun s => s in l ∧ p s) id)
  证明: by
  simpa only [and_assoc] using! h.restrict_subset hV

Depends on / 依赖: and_assoc, h.restrict_subset, restrict_subset
-/
theorem HasBasis.hasBasis_self_subset {p : Set α -> Prop} (h : l.HasBasis (fun s => s in l ∧ p s) id)
    {V : Set α} (hV : V in l) : l.HasBasis (fun s => s in l ∧ p s ∧ s subseteq V) id := by
  simpa only [and_assoc] using! h.restrict_subset hV

/--
theorem `HasBasis.ge_iff` / 定理 `HasBasis.ge_iff`

English:
theorem HasBasis.ge_iff
  given: (hl' : l'.HasBasis p' s')
  statement: l <= l' ↔ forall i', p' i' -> s' i' in l
  proof: ⟨fun h _i' hi' => h hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩

中文:
定理 HasBasis.ge_iff
  条件: (hl' : l'.HasBasis p' s')
  结论: l <= l' ↔ 对任意 i', p' i' -> s' i' in l
  证明: ⟨fun h _i' hi' => h hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩

Depends on / 依赖: mem_iff, mem_of_mem, mem_of_superset
-/
theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l <= l' ↔ forall i', p' i' -> s' i' in l :=
⟨fun h _i' hi' => h hl'.mem_of_mem hi', fun h _s hs =>
    let ⟨_i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩

/--
theorem `HasBasis.le_iff` / 定理 `HasBasis.le_iff`

English:
theorem HasBasis.le_iff
  given: (hl : l.HasBasis p s)
  statement: l <= l' ↔ forall t in l', exists i, p i ∧ s i subseteq t
  proof: by
  simp only [le_def, hl.mem_iff]

中文:
定理 HasBasis.le_iff
  条件: (hl : l.HasBasis p s)
  结论: l <= l' ↔ 对任意 t in l', 存在 i, p i ∧ s i subseteq t
  证明: by
  simp only [le_def, hl.mem_iff]

Depends on / 依赖: hl.mem_iff, le_def, mem_iff
-/
theorem HasBasis.le_iff (hl : l.HasBasis p s) : l <= l' ↔ forall t in l', exists i, p i ∧ s i subseteq t := by
  simp only [le_def, hl.mem_iff]

/--
theorem `HasBasis.le_basis_iff` / 定理 `HasBasis.le_basis_iff`

English:
theorem HasBasis.le_basis_iff
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: by
  simp only [hl'.ge_iff, hl.mem_iff]

中文:
定理 HasBasis.le_basis_iff
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: by
  simp only [hl'.ge_iff, hl.mem_iff]

Depends on / 依赖: ge_iff, hl.mem_iff, mem_iff
-/
theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l <= l' ↔ forall i', p' i' -> exists i, p i ∧ s i subseteq s' i' := by
  simp only [hl'.ge_iff, hl.mem_iff]

/--
theorem `HasBasis.eq_top_iff` / 定理 `HasBasis.eq_top_iff`

English:
theorem HasBasis.eq_top_iff
  given: (h : l.HasBasis p s)
  statement: l = ⊤ ↔ forall i, p i -> s i = univ
  proof: by
  simp [← top_le_iff, h.ge_iff]

中文:
定理 HasBasis.eq_top_iff
  条件: (h : l.HasBasis p s)
  结论: l = ⊤ ↔ 对任意 i, p i -> s i = univ
  证明: by
  simp [← top_le_iff, h.ge_iff]

Depends on / 依赖: ge_iff, h.ge_iff, top_le_iff
-/
theorem HasBasis.eq_top_iff (h : l.HasBasis p s) : l = ⊤ ↔ forall i, p i -> s i = univ := by
  simp [← top_le_iff, h.ge_iff]

/--
theorem `HasBasis.ext` / 定理 `HasBasis.ext`

English:
theorem HasBasis.ext
  statement: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h

中文:
定理 HasBasis.ext
  结论: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h

Depends on / 依赖: hl.le_basis_iff, le_antisymm, le_basis_iff
-/
theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : forall i, p i -> exists i', p' i' ∧ s' i' subseteq s i) (h' : forall i', p' i' -> exists i, p i ∧ s i subseteq s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h

/--
theorem `HasBasis.inf'` / 定理 `HasBasis.inf'`

English:
theorem HasBasis.inf'
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_m

中文:
定理 HasBasis.inf'
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_m

Depends on / 依赖: hl.mem_iff, hl.mem_of_mem, inter_subset_inter, mem_iff, mem_inf_iff, mem_inf_of_inter, mem_of_mem
-/
theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 inter s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩

/--
theorem `HasBasis.inf` / 定理 `HasBasis.inf`

English:
theorem HasBasis.inf
  statement: {ι ι' : Type*} {p : ι -> Prop} {s : ι -> Set α} {p' : ι' -> Prop}
  proof: (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm

中文:
定理 HasBasis.inf
  结论: {ι ι' : 类型} {p : ι -> 命题} {s : ι -> Set α} {p' : ι' -> 命题}
  证明: (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm

Depends on / 依赖: Equiv.pprodEquivProd.symm, comp_equiv, hl.inf, pprodEquivProd
-/
theorem HasBasis.inf {ι ι' : Type*} {p : ι -> Prop} {s : ι -> Set α} {p' : ι' -> Prop}
    {s' : ι' -> Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 inter s' i.2 :=
  (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm

/--
theorem `hasBasis_iInf_of_directed'` / 定理 `hasBasis_iInf_of_directed'`

English:
theorem hasBasis_iInf_of_directed'
  statement: {ι : Type*} {ι' : ι -> Sort _} [Nonempty ι] {l : ι -> Filter α}
  proof: by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff

中文:
定理 hasBasis_iInf_of_directed'
  结论: {ι : 类型} {ι' : ι -> Sort _} [Nonempty ι] {l : ι -> Filter α}
  证明: by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff

Depends on / 依赖: CommMonoid, Sigma.exists, exists_congr, mem_iInf_of_directed, mem_iff, submonoid
-/
theorem hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι -> Sort _} [Nonempty ι] {l : ι -> Filter α}
    (s : forall i, ι' i -> Set α) (p : forall i, ι' i -> Prop) (hl : forall i, (l i).HasBasis (p i) (s i))
    (h : Directed (· >= ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σ i, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff

/--
theorem `hasBasis_iInf_of_directed` / 定理 `hasBasis_iInf_of_directed`

English:
theorem hasBasis_iInf_of_directed
  statement: {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι -> Filter α}
  proof: by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff

中文:
定理 hasBasis_iInf_of_directed
  结论: {ι : 类型} {ι' : Sort _} [Nonempty ι] {l : ι -> Filter α}
  证明: by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff

Depends on / 依赖: Prod.exists, exists_congr, mem_iInf_of_directed, mem_iff
-/
theorem hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι -> Filter α}
    (s : ι -> ι' -> Set α) (p : ι -> ι' -> Prop) (hl : forall i, (l i).HasBasis (p i) (s i))
    (h : Directed (· >= ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h]; rw [Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff

/--
theorem `hasBasis_biInf_of_directed'` / 定理 `hasBasis_biInf_of_directed'`

English:
theorem hasBasis_biInf_of_directed'
  statement: {ι : Type*} {ι' : ι -> Sort _} {dom : Set ι}
  proof: by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Sigma.exists]
  grind +splitIndPred

中文:
定理 hasBasis_biInf_of_directed'
  结论: {ι : 类型} {ι' : ι -> Sort _} {dom : Set ι}
  证明: by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Sigma.exists]
  grind +splitIndPred

Depends on / 依赖: Sigma.exists, mem_biInf_of_directed, splitIndPred
-/
theorem hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι -> Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι -> Filter α} (s : forall i, ι' i -> Set α) (p : forall i, ι' i -> Prop)
    (hl : forall i in dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i in dom, l i).HasBasis (fun ii' : Σ i, ι' i => ii'.1 in dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Sigma.exists]
  grind +splitIndPred

/--
theorem `hasBasis_biInf_of_directed` / 定理 `hasBasis_biInf_of_directed`

English:
theorem hasBasis_biInf_of_directed
  statement: {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
  proof: by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Prod.exists]
  grind +splitIndPred

中文:
定理 hasBasis_biInf_of_directed
  结论: {ι : 类型} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
  证明: by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Prod.exists]
  grind +splitIndPred

Depends on / 依赖: Prod.exists, mem_biInf_of_directed, splitIndPred
-/
theorem hasBasis_biInf_of_directed {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι -> Filter α} (s : ι -> ι' -> Set α) (p : ι -> ι' -> Prop)
    (hl : forall i in dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i in dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 in dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom]; rw [Prod.exists]
  grind +splitIndPred

/--
lemma `hasBasis_top` / 引理 `hasBasis_top`

English:
lemma hasBasis_top
  proof: ⟨fun U => by simp⟩

中文:
引理 hasBasis_top
  证明: ⟨fun U => by simp⟩
-/
lemma hasBasis_top :
    (⊤ : Filter α).HasBasis (fun _ : Unit => True) (fun _ => Set.univ) :=
  ⟨fun U => by simp⟩

/--
theorem `hasBasis_principal` / 定理 `hasBasis_principal`

English:
theorem hasBasis_principal
  given: (t : Set α)
  statement: (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t
  proof: ⟨fun U => by simp⟩

中文:
定理 hasBasis_principal
  条件: (t : Set α)
  结论: (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t
  证明: ⟨fun U => by simp⟩
-/
theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun _ : Unit => True) fun _ => t :=
  ⟨fun U => by simp⟩

/--
theorem `hasBasis_pure` / 定理 `hasBasis_pure`

English:
theorem hasBasis_pure
  given: (x : α)
  proof: by
  simp only [← principal_singleton, hasBasis_principal]

中文:
定理 hasBasis_pure
  条件: (x : α)
  证明: by
  simp only [← principal_singleton, hasBasis_principal]

Depends on / 依赖: hasBasis_principal, principal_singleton
-/
theorem hasBasis_pure (x : α) :
    (pure x : Filter α).HasBasis (fun _ : Unit => True) fun _ => {x} := by
  simp only [← principal_singleton, hasBasis_principal]

/--
theorem `HasBasis.sup'` / 定理 `HasBasis.sup'`

English:
theorem HasBasis.sup'
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩

中文:
定理 HasBasis.sup'
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩

Depends on / 依赖: PProd.exists, and_assoc, and_left_comm, exists_and_left, exists_and_right, hl.mem_iff, mem_iff, mem_sup, simp_rw, union_subset_iff
-/
theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 union s' i.2 :=
  ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩

/--
theorem `HasBasis.sup` / 定理 `HasBasis.sup`

English:
theorem HasBasis.sup
  statement: {ι ι' : Type*} {p : ι -> Prop} {s : ι -> Set α} {p' : ι' -> Prop}
  proof: (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm

中文:
定理 HasBasis.sup
  结论: {ι ι' : 类型} {p : ι -> 命题} {s : ι -> Set α} {p' : ι' -> 命题}
  证明: (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm

Depends on / 依赖: Equiv.pprodEquivProd.symm, comp_equiv, hl.sup, pprodEquivProd
-/
theorem HasBasis.sup {ι ι' : Type*} {p : ι -> Prop} {s : ι -> Set α} {p' : ι' -> Prop}
    {s' : ι' -> Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 union s' i.2 :=
  (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm

/--
theorem `hasBasis_iSup` / 定理 `hasBasis_iSup`

English:
theorem hasBasis_iSup
  statement: {ι : Sort*} {ι' : ι -> Type*} {l : ι -> Filter α} {p : forall i, ι' i -> Prop}
  proof: hasBasis_iff.mpr fun t => by
    simp only [(hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]

中文:
定理 hasBasis_iSup
  结论: {ι : Sort*} {ι' : ι -> 类型} {l : ι -> Filter α} {p : 对任意 i, ι' i -> 命题}
  证明: hasBasis_iff.mpr fun t => by
    simp only [(hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]

Depends on / 依赖: Classical, Classical.skolem, forall_and, hasBasis_iff, hasBasis_iff.mpr, iUnion_subset_iff, mem_iSup, mem_iff, skolem
-/
theorem hasBasis_iSup {ι : Sort*} {ι' : ι -> Type*} {l : ι -> Filter α} {p : forall i, ι' i -> Prop}
    {s : forall i, ι' i -> Set α} (hl : forall i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : forall i, ι' i => forall i, p i (f i)) fun f : forall i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [(hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]

/--
theorem `HasBasis.sup_principal` / 定理 `HasBasis.sup_principal`

English:
theorem HasBasis.sup_principal
  given: (hl : l.HasBasis p s) (t : Set α)
  proof: ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, and_true,
      Unique.exists_iff]⟩

中文:
定理 HasBasis.sup_principal
  条件: (hl : l.HasBasis p s) (t : Set α)
  证明: ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, and_true,
      Unique.exists_iff]⟩

Depends on / 依赖: PProd.exists, Unique, Unique.exists_iff, and_true, exists_iff, hasBasis_principal, hl.sup, mem_iff
-/
theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i union t :=
  ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, and_true,
      Unique.exists_iff]⟩

/--
theorem `HasBasis.sup_pure` / 定理 `HasBasis.sup_pure`

English:
theorem HasBasis.sup_pure
  given: (hl : l.HasBasis p s) (x : α)
  proof: by
  simp only [← principal_singleton, hl.sup_principal]

中文:
定理 HasBasis.sup_pure
  条件: (hl : l.HasBasis p s) (x : α)
  证明: by
  simp only [← principal_singleton, hl.sup_principal]

Depends on / 依赖: hl.sup_principal, principal_singleton, sup_principal
-/
theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i union {x} := by
  simp only [← principal_singleton, hl.sup_principal]

/--
theorem `HasBasis.inf_principal` / 定理 `HasBasis.inf_principal`

English:
theorem HasBasis.inf_principal
  given: (hl : l.HasBasis p s) (s' : Set α)
  proof: ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_ofPred_eq, mem_inter_iff, and_imp]⟩

中文:
定理 HasBasis.inf_principal
  条件: (hl : l.HasBasis p s) (s' : Set α)
  证明: ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_ofPred_eq, mem_inter_iff, and_imp]⟩

Depends on / 依赖: and_imp, hl.mem_iff, mem_iff, mem_inf_principal, mem_inter_iff, mem_ofPred_eq, subset_def
-/
theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i inter s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_ofPred_eq, mem_inter_iff, and_imp]⟩

/--
theorem `HasBasis.principal_inf` / 定理 `HasBasis.principal_inf`

English:
theorem HasBasis.principal_inf
  given: (hl : l.HasBasis p s) (s' : Set α)
  proof: by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'

中文:
定理 HasBasis.principal_inf
  条件: (hl : l.HasBasis p s) (s' : Set α)
  证明: by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'

Depends on / 依赖: hl.inf_principal, inf_comm, inf_principal, inter_comm
-/
theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' inter s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'

/--
theorem `HasBasis.inf_basis_neBot_iff` / 定理 `HasBasis.inf_basis_neBot_iff`

English:
theorem HasBasis.inf_basis_neBot_iff
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: (hl.inf' hl').neBot_iff.trans by simp [@forall_comm _ ι']

中文:
定理 HasBasis.inf_basis_neBot_iff
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: (hl.inf' hl').neBot_iff.trans by simp [@forall_comm _ ι']

Depends on / 依赖: forall_comm, hl.inf, neBot_iff, neBot_iff.trans
-/
theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ forall ⦃i⦄, p i -> forall ⦃i'⦄, p' i' -> (s i inter s' i').Nonempty :=
(hl.inf' hl').neBot_iff.trans by simp [@forall_comm _ ι']

/--
theorem `HasBasis.inf_neBot_iff` / 定理 `HasBasis.inf_neBot_iff`

English:
theorem HasBasis.inf_neBot_iff
  given: (hl : l.HasBasis p s)
  proof: hl.inf_basis_neBot_iff l'.basis_sets

中文:
定理 HasBasis.inf_neBot_iff
  条件: (hl : l.HasBasis p s)
  证明: hl.inf_basis_neBot_iff l'.basis_sets

Depends on / 依赖: basis_sets, hl.inf_basis_neBot_iff, inf_basis_neBot_iff
-/
theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ forall ⦃i⦄, p i -> forall ⦃s'⦄, s' in l' -> (s i inter s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets

/--
theorem `HasBasis.inf_principal_neBot_iff` / 定理 `HasBasis.inf_principal_neBot_iff`

English:
theorem HasBasis.inf_principal_neBot_iff
  given: (hl : l.HasBasis p s) {t : Set α}
  proof: (hl.inf_principal t).neBot_iff

中文:
定理 HasBasis.inf_principal_neBot_iff
  条件: (hl : l.HasBasis p s) {t : Set α}
  证明: (hl.inf_principal t).neBot_iff

Depends on / 依赖: hl.inf_principal, inf_principal, neBot_iff
-/
theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ forall ⦃i⦄, p i -> (s i inter t).Nonempty :=
  (hl.inf_principal t).neBot_iff

/--
theorem `HasBasis.disjoint_iff` / 定理 `HasBasis.disjoint_iff`

English:
theorem HasBasis.disjoint_iff
  given: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  proof: not_iff_not.mp by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]

中文:
定理 HasBasis.disjoint_iff
  条件: (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
  证明: not_iff_not.mp by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]

Depends on / 依赖: Ne.eq_def, _root_, _root_.disjoint_iff, bot_eq_empty, disjoint_iff, eq_def, hl.inf_basis_neBot_iff, inf_basis_neBot_iff, inf_eq_inter, neBot_iff, nonempty_iff_ne_empty, not_and, not_exists, not_iff_not, not_iff_not.mp
-/
theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ exists i, p i ∧ exists i', p' i' ∧ Disjoint (s i) (s' i') :=
not_iff_not.mp by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]

/--
theorem `_root_.Disjoint.exists_mem_filter_basis` / 定理 `_root_.Disjoint.exists_mem_filter_basis`

English:
theorem _root_.Disjoint.exists_mem_filter_basis
  statement: (h : Disjoint l l') (hl : l.HasBasis p s)
  proof: (hl.disjoint_iff hl').1 h

中文:
定理 _root_.Disjoint.exists_mem_filter_basis
  结论: (h : Disjoint l l') (hl : l.HasBasis p s)
  证明: (hl.disjoint_iff hl').1 h

Depends on / 依赖: disjoint_iff, hl.disjoint_iff
-/
theorem _root_.Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : exists i, p i ∧ exists i', p' i' ∧ Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h

/--
theorem `inf_neBot_iff` / 定理 `inf_neBot_iff`

English:
theorem inf_neBot_iff
  proof: l.basis_sets.inf_neBot_iff

中文:
定理 inf_neBot_iff
  证明: l.basis_sets.inf_neBot_iff

Depends on / 依赖: basis_sets, inf_neBot_iff, l.basis_sets.inf_neBot_iff
-/
theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ forall ⦃s : Set α⦄, s in l -> forall ⦃s'⦄, s' in l' -> (s inter s').Nonempty :=
  l.basis_sets.inf_neBot_iff

/--
theorem `inf_principal_neBot_iff` / 定理 `inf_principal_neBot_iff`

English:
theorem inf_principal_neBot_iff
  given: {s : Set α}
  statement: NeBot (l ⊓ 𝓟 s) ↔ forall U in l, (U inter s).Nonempty
  proof: l.basis_sets.inf_principal_neBot_iff

中文:
定理 inf_principal_neBot_iff
  条件: {s : Set α}
  结论: NeBot (l ⊓ 𝓟 s) ↔ 对任意 U in l, (U inter s).Nonempty
  证明: l.basis_sets.inf_principal_neBot_iff

Depends on / 依赖: basis_sets, inf_principal_neBot_iff, l.basis_sets.inf_principal_neBot_iff
-/
theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ forall U in l, (U inter s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff

/--
theorem `mem_iff_inf_principal_compl` / 定理 `mem_iff_inf_principal_compl`

English:
theorem mem_iff_inf_principal_compl
  given: {f : Filter α} {s : Set α}
  statement: s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
  proof: by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
inter_compl_nonempty_iff.2 fun hts => hs mem_of_superset ht hts⟩

中文:
定理 mem_iff_inf_principal_compl
  条件: {f : Filter α} {s : Set α}
  结论: s in f ↔ f ⊓ 𝓟 sᶜ = ⊥
  证明: by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
inter_compl_nonempty_iff.2 fun hts => hs mem_of_superset ht hts⟩

Depends on / 依赖: Set.not_nonempty_empty, inf_principal_neBot_iff, inf_principal_neBot_iff.trans, inter_compl_nonempty_iff, mem_of_superset, neBot_iff, not_iff_not, not_nonempty_empty, symm.trans
-/
theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s in f ↔ f ⊓ 𝓟 sᶜ = ⊥ := by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
inter_compl_nonempty_iff.2 fun hts => hs mem_of_superset ht hts⟩

/--
theorem `notMem_iff_inf_principal_compl` / 定理 `notMem_iff_inf_principal_compl`

English:
theorem notMem_iff_inf_principal_compl
  given: {f : Filter α} {s : Set α}
  statement: s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ)
  proof: (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[simp]

中文:
定理 notMem_iff_inf_principal_compl
  条件: {f : Filter α} {s : Set α}
  结论: s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ)
  证明: (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[simp]

Depends on / 依赖: mem_iff_inf_principal_compl, neBot_iff, neBot_iff.symm, not_congr
-/
theorem notMem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[simp]
/--
theorem `disjoint_principal_right` / 定理 `disjoint_principal_right`

English:
theorem disjoint_principal_right
  given: {f : Filter α} {s : Set α}
  statement: Disjoint f (𝓟 s) ↔ sᶜ in f
  proof: by
  rw [mem_iff_inf_principal_compl]; rw [compl_compl]; rw [disjoint_iff]

@[simp]

中文:
定理 disjoint_principal_right
  条件: {f : Filter α} {s : Set α}
  结论: Disjoint f (𝓟 s) ↔ sᶜ in f
  证明: by
  rw [mem_iff_inf_principal_compl]; rw [compl_compl]; rw [disjoint_iff]

@[simp]

Depends on / 依赖: compl_compl, disjoint_iff, mem_iff_inf_principal_compl
-/
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f := by
  rw [mem_iff_inf_principal_compl]; rw [compl_compl]; rw [disjoint_iff]

@[simp]
/--
theorem `disjoint_principal_left` / 定理 `disjoint_principal_left`

English:
theorem disjoint_principal_left
  given: {f : Filter α} {s : Set α}
  statement: Disjoint (𝓟 s) f ↔ sᶜ in f
  proof: by
  rw [disjoint_comm]; rw [disjoint_principal_right]

@[simp high] -- This should fire before `disjoint_principal_left` and `disjoint_principal_right`.

中文:
定理 disjoint_principal_left
  条件: {f : Filter α} {s : Set α}
  结论: Disjoint (𝓟 s) f ↔ sᶜ in f
  证明: by
  rw [disjoint_comm]; rw [disjoint_principal_right]

@[simp high] -- This should fire before `disjoint_principal_left` and `disjoint_principal_right`.

Depends on / 依赖: disjoint_comm, disjoint_principal_right
-/
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ in f := by
  rw [disjoint_comm]; rw [disjoint_principal_right]

@[simp high] -- This should fire before `disjoint_principal_left` and `disjoint_principal_right`.
/--
theorem `disjoint_principal_principal` / 定理 `disjoint_principal_principal`

English:
theorem disjoint_principal_principal
  given: {s t : Set α}
  statement: Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t
  proof: by
  rw [← subset_compl_iff_disjoint_left]; rw [disjoint_principal_left]; rw [mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]

中文:
定理 disjoint_principal_principal
  条件: {s t : Set α}
  结论: Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t
  证明: by
  rw [← subset_compl_iff_disjoint_left]; rw [disjoint_principal_left]; rw [mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]

Depends on / 依赖: disjoint_principal_left, mem_principal, subset_compl_iff_disjoint_left
-/
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  rw [← subset_compl_iff_disjoint_left]; rw [disjoint_principal_left]; rw [mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]
/--
theorem `disjoint_pure_pure` / 定理 `disjoint_pure_pure`

English:
theorem disjoint_pure_pure
  given: {x y : α}
  statement: Disjoint (pure x : Filter α) (pure y) ↔ x != y
  proof: by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]

中文:
定理 disjoint_pure_pure
  条件: {x y : α}
  结论: Disjoint (pure x : Filter α) (pure y) ↔ x != y
  证明: by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]

Depends on / 依赖: disjoint_principal_principal, disjoint_singleton, principal_singleton
-/
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x != y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]

/--
theorem `HasBasis.disjoint_iff_left` / 定理 `HasBasis.disjoint_iff_left`

English:
theorem HasBasis.disjoint_iff_left
  given: (h : l.HasBasis p s)
  proof: by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]

中文:
定理 HasBasis.disjoint_iff_left
  条件: (h : l.HasBasis p s)
  证明: by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]

Depends on / 依赖: Unique, Unique.exists_iff, basis_sets, disjoint_iff, disjoint_principal_left, exists_iff, h.disjoint_iff, hasBasis_principal, true_and
-/
theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ exists i, p i ∧ (s i)ᶜ in l' := by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]

/--
theorem `HasBasis.disjoint_iff_right` / 定理 `HasBasis.disjoint_iff_right`

English:
theorem HasBasis.disjoint_iff_right
  given: (h : l.HasBasis p s)
  proof: disjoint_comm.trans h.disjoint_iff_left

中文:
定理 HasBasis.disjoint_iff_right
  条件: (h : l.HasBasis p s)
  证明: disjoint_comm.trans h.disjoint_iff_left

Depends on / 依赖: disjoint_comm, disjoint_comm.trans, disjoint_iff_left, h.disjoint_iff_left
-/
theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ exists i, p i ∧ (s i)ᶜ in l' :=
  disjoint_comm.trans h.disjoint_iff_left

/--
theorem `le_iff_forall_inf_principal_compl` / 定理 `le_iff_forall_inf_principal_compl`

English:
theorem le_iff_forall_inf_principal_compl
  given: {f g : Filter α}
  statement: f <= g ↔ forall V in g, f ⊓ 𝓟 Vᶜ = ⊥
  proof: forall₂_congr fun _ _ => mem_iff_inf_principal_compl

中文:
定理 le_iff_forall_inf_principal_compl
  条件: {f g : Filter α}
  结论: f <= g ↔ 对任意 V in g, f ⊓ 𝓟 Vᶜ = ⊥
  证明: forall₂_congr fun _ _ => mem_iff_inf_principal_compl

Depends on / 依赖: mem_iff_inf_principal_compl
-/
theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f <= g ↔ forall V in g, f ⊓ 𝓟 Vᶜ = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl

/--
theorem `inf_neBot_iff_frequently_left` / 定理 `inf_neBot_iff_frequently_left`

English:
theorem inf_neBot_iff_frequently_left
  given: {f g : Filter α}
  proof: by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl

中文:
定理 inf_neBot_iff_frequently_left
  条件: {f g : Filter α}
  证明: by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl

Depends on / 依赖: and_comm, frequently_iff, inf_neBot_iff
-/
theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ forall {p : α -> Prop}, (forallᶠ x in f, p x) -> existsᶠ x in g, p x := by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl

/--
theorem `inf_neBot_iff_frequently_right` / 定理 `inf_neBot_iff_frequently_right`

English:
theorem inf_neBot_iff_frequently_right
  given: {f g : Filter α}
  proof: by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left

中文:
定理 inf_neBot_iff_frequently_right
  条件: {f g : Filter α}
  证明: by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left

Depends on / 依赖: inf_comm, inf_neBot_iff_frequently_left
-/
theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ forall {p : α -> Prop}, (forallᶠ x in g, p x) -> existsᶠ x in f, p x := by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left

/--
theorem `HasBasis.eq_biInf` / 定理 `HasBasis.eq_biInf`

English:
theorem HasBasis.eq_biInf
  given: (h : l.HasBasis p s)
  statement: l = ⨅ (i) (_ : p i), 𝓟 (s i)
  proof: eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal]

中文:
定理 HasBasis.eq_biInf
  条件: (h : l.HasBasis p s)
  结论: l = ⨅ (i) (_ : p i), 𝓟 (s i)
  证明: eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal]

Depends on / 依赖: eq_biInf_of_mem_iff_exists_mem, h.mem_iff, mem_iff, mem_principal
-/
theorem HasBasis.eq_biInf (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal]

/--
theorem `HasBasis.eq_iInf` / 定理 `HasBasis.eq_iInf`

English:
theorem HasBasis.eq_iInf
  given: (h : l.HasBasis (fun _ => True) s)
  statement: l = ⨅ i, 𝓟 (s i)
  proof: by
  simpa only [iInf_true] using h.eq_biInf

中文:
定理 HasBasis.eq_iInf
  条件: (h : l.HasBasis (fun _ => True) s)
  结论: l = ⨅ i, 𝓟 (s i)
  证明: by
  simpa only [iInf_true] using h.eq_biInf

Depends on / 依赖: eq_biInf, h.eq_biInf, iInf_true
-/
theorem HasBasis.eq_iInf (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [iInf_true] using h.eq_biInf

/--
theorem `hasBasis_iInf_principal` / 定理 `hasBasis_iInf_principal`

English:
theorem hasBasis_iInf_principal
  given: {s : ι -> Set α} (h : Directed (· >= ·) s) [Nonempty ι]
  proof: ⟨fun t => by
    simpa only [true_and] using! mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩

中文:
定理 hasBasis_iInf_principal
  条件: {s : ι -> Set α} (h : Directed (· >= ·) s) [Nonempty ι]
  证明: ⟨fun t => by
    simpa only [true_and] using! mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩

Depends on / 依赖: h.mono_comp, mem_iInf_of_directed, mono_comp, monotone_principal, monotone_principal.dual, true_and
-/
theorem hasBasis_iInf_principal {s : ι -> Set α} (h : Directed (· >= ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨fun t => by
    simpa only [true_and] using! mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩

/--
theorem `hasBasis_biInf_principal` / 定理 `hasBasis_biInf_principal`

English:
theorem hasBasis_biInf_principal
  statement: {s : β -> Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S)
  proof: ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed]; rw [← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩

中文:
定理 hasBasis_biInf_principal
  结论: {s : β -> Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S)
  证明: ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed]; rw [← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩

Depends on / 依赖: directedOn_iff_directed, directed_comp, h.mono_comp, mem_biInf_of_directed, mono_comp, principal_mono
-/
theorem hasBasis_biInf_principal {s : β -> Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S)
    (ne : S.Nonempty) : (⨅ i in S, 𝓟 (s i)).HasBasis (fun i => i in S) s :=
  ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed]; rw [← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩

/--
theorem `hasBasis_biInf_principal'` / 定理 `hasBasis_biInf_principal'`

English:
theorem hasBasis_biInf_principal'
  statement: {ι : Type*} {p : ι -> Prop} {s : ι -> Set α}
  proof: Filter.hasBasis_biInf_principal h ne

中文:
定理 hasBasis_biInf_principal'
  结论: {ι : 类型} {p : ι -> 命题} {s : ι -> Set α}
  证明: Filter.hasBasis_biInf_principal h ne

Depends on / 依赖: Filter, Filter.hasBasis_biInf_principal, hasBasis_biInf_principal
-/
theorem hasBasis_biInf_principal' {ι : Type*} {p : ι -> Prop} {s : ι -> Set α}
    (h : forall i, p i -> forall j, p j -> exists k, p k ∧ s k subseteq s i ∧ s k subseteq s j) (ne : exists i, p i) :
    (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_biInf_principal h ne

/--
theorem `HasBasis.map` / 定理 `HasBasis.map`

English:
theorem HasBasis.map
  given: (f : α -> β) (hl : l.HasBasis p s)
  statement: (l.map f).HasBasis p fun i => f '' s i
  proof: ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

中文:
定理 HasBasis.map
  条件: (f : α -> β) (hl : l.HasBasis p s)
  结论: (l.map f).HasBasis p fun i => f '' s i
  证明: ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

Depends on / 依赖: hl.mem_iff, image_subset_iff, mem_iff, mem_map, preimage
-/
theorem HasBasis.map (f : α -> β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

/--
theorem `HasBasis.comap` / 定理 `HasBasis.comap`

English:
theorem HasBasis.comap
  given: (f : β -> α) (hl : l.HasBasis p s)
  proof: ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h by rwa [mem_preimage, hx]⟩⟩

中文:
定理 HasBasis.comap
  条件: (f : β -> α) (hl : l.HasBasis p s)
  证明: ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h by rwa [mem_preimage, hx]⟩⟩

Depends on / 依赖: Iff.rfl.and, exists_congr, hl.mem_iff, mem_comap, mem_iff, mem_preimage
-/
theorem HasBasis.comap (f : β -> α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h by rwa [mem_preimage, hx]⟩⟩

/--
theorem `comap_hasBasis` / 定理 `comap_hasBasis`

English:
theorem comap_hasBasis
  given: (f : α -> β) (l : Filter β)
  proof: ⟨fun _ => mem_comap⟩

中文:
定理 comap_hasBasis
  条件: (f : α -> β) (l : Filter β)
  证明: ⟨fun _ => mem_comap⟩

Depends on / 依赖: mem_comap
-/
theorem comap_hasBasis (f : α -> β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s in l) fun s => f ⁻¹' s :=
  ⟨fun _ => mem_comap⟩

/--
theorem `HasBasis.forall_mem_mem` / 定理 `HasBasis.forall_mem_mem`

English:
theorem HasBasis.forall_mem_mem
  given: (h : HasBasis l p s) {x : α}
  proof: by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩

中文:
定理 HasBasis.forall_mem_mem
  条件: (h : HasBasis l p s) {x : α}
  证明: by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩

Depends on / 依赖: Subset, Subset.rfl, and_imp, exists_imp, h.mem_iff, mem_iff
-/
theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (forall t in l, x in t) ↔ forall i, p i -> x in s i := by
  simp only [h.mem_iff, exists_imp, and_imp]
  exact ⟨fun h i hi => h (s i) i hi Subset.rfl, fun h t i hi ht => ht (h i hi)⟩

/--
theorem `HasBasis.biInf_mem` / 定理 `HasBasis.biInf_mem`

English:
theorem HasBasis.biInf_mem
  statement: [CompleteLattice β] {f : Set α -> β} (h : HasBasis l p s)
  proof: le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi))
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)

中文:
定理 HasBasis.biInf_mem
  结论: [CompleteLattice β] {f : Set α -> β} (h : HasBasis l p s)
  证明: le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi))
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)
-/
protected theorem HasBasis.biInf_mem [CompleteLattice β] {f : Set α -> β} (h : HasBasis l p s)
    (hf : Monotone f) : ⨅ t in l, f t = ⨅ (i) (_ : p i), f (s i) :=
le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi))
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)

/--
theorem `HasBasis.biInter_mem` / 定理 `HasBasis.biInter_mem`

English:
theorem HasBasis.biInter_mem
  given: {f : Set α -> Set β} (h : HasBasis l p s) (hf : Monotone f)
  proof: h.biInf_mem hf

中文:
定理 HasBasis.biInter_mem
  条件: {f : Set α -> Set β} (h : HasBasis l p s) (hf : Monotone f)
  证明: h.biInf_mem hf
-/
protected theorem HasBasis.biInter_mem {f : Set α -> Set β} (h : HasBasis l p s) (hf : Monotone f) :
    ⋂ t in l, f t = ⋂ (i) (_ : p i), f (s i) :=
  h.biInf_mem hf

/--
theorem `HasBasis.ker` / 定理 `HasBasis.ker`

English:
theorem HasBasis.ker
  given: (h : HasBasis l p s)
  statement: l.ker = ⋂ (i) (_ : p i), s i
  proof: sInter_eq_biInter.trans h.biInter_mem monotone_id

中文:
定理 HasBasis.ker
  条件: (h : HasBasis l p s)
  结论: l.ker = ⋂ (i) (_ : p i), s i
  证明: sInter_eq_biInter.trans h.biInter_mem monotone_id
-/
protected theorem HasBasis.ker (h : HasBasis l p s) : l.ker = ⋂ (i) (_ : p i), s i :=
sInter_eq_biInter.trans h.biInter_mem monotone_id

variable {ι'' : Type*} [Preorder ι''] (l) (s'' : ι'' -> Set α)

/--
Definition of `IsAntitoneBasis` / `IsAntitoneBasis` 的定义

English:
structure IsAntitoneBasis
  parameters: : Prop extends IsBasis (fun _ => True) s'' where
  extends: IsBasis (fun _ => True) s''
  axioms and operations (1):
    - antitone : Antitone s''

中文:
结构 IsAntitoneBasis
  参数: : 命题 extends IsBasis (fun _ => True) s'' where
  继承: IsBasis (fun _ => True) s''
  公理与运算 (1 个):
    - antitone : Antitone s''
-/
structure IsAntitoneBasis : Prop extends IsBasis (fun _ => True) s'' where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s''

/--
Definition of `HasAntitoneBasis` / `HasAntitoneBasis` 的定义

English:
structure HasAntitoneBasis
  parameters: (l : Filter α) (s : ι'' -> Set α)
  extends: HasBasis l (fun _ => True) s
  axioms and operations (1):
    - antitone : Antitone s

中文:
结构 HasAntitoneBasis
  参数: (l : Filter α) (s : ι'' -> Set α)
  继承: HasBasis l (fun _ => True) s
  公理与运算 (1 个):
    - antitone : Antitone s

Depends on / 依赖: HasBasis, HasBasis.map, hf.toHasBasis, image_mono, toHasBasis
-/
structure HasAntitoneBasis (l : Filter α) (s : ι'' -> Set α) : Prop
    extends HasBasis l (fun _ => True) s where
  /-- The sequence of sets is antitone. -/
  protected antitone : Antitone s

/--
theorem `HasAntitoneBasis.map` / 定理 `HasAntitoneBasis.map`

English:
theorem HasAntitoneBasis.map
  statement: {l : Filter α} {s : ι'' -> Set α}
  proof: ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_mono hf.2 h⟩

中文:
定理 HasAntitoneBasis.map
  结论: {l : Filter α} {s : ι'' -> Set α}
  证明: ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_mono hf.2 h⟩
-/
protected theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' -> Set α}
    (hf : HasAntitoneBasis l s) (m : α -> β) : HasAntitoneBasis (map m l) (m '' s ·) :=
⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_mono hf.2 h⟩

/--
theorem `HasAntitoneBasis.comap` / 定理 `HasAntitoneBasis.comap`

English:
theorem HasAntitoneBasis.comap
  statement: {l : Filter α} {s : ι'' -> Set α}
  proof: ⟨hf.1.comap _, fun _ _ h => preimage_mono (hf.2 h)⟩

中文:
定理 HasAntitoneBasis.comap
  结论: {l : Filter α} {s : ι'' -> Set α}
  证明: ⟨hf.1.comap _, fun _ _ h => preimage_mono (hf.2 h)⟩
-/
protected theorem HasAntitoneBasis.comap {l : Filter α} {s : ι'' -> Set α}
    (hf : HasAntitoneBasis l s) (m : β -> α) : HasAntitoneBasis (comap m l) (m ⁻¹' s ·) :=
  ⟨hf.1.comap _, fun _ _ h => preimage_mono (hf.2 h)⟩

/--
lemma `HasAntitoneBasis.iInf_principal` / 引理 `HasAntitoneBasis.iInf_principal`

English:
lemma HasAntitoneBasis.iInf_principal
  statement: {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  proof: ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

中文:
引理 HasAntitoneBasis.iInf_principal
  结论: {ι : 类型} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  证明: ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

Depends on / 依赖: directed_ge, hasBasis_iInf_principal, hs.directed_ge
-/
lemma HasAntitoneBasis.iInf_principal {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {s : ι -> Set α} (hs : Antitone s) : (⨅ i, 𝓟 (s i)).HasAntitoneBasis s :=
  ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι -> Prop} {sa : ι -> Set α} {lb : Filter β} {pb : ι' -> Prop}
  {sb : ι' -> Set β} {f : α -> β}

/--
theorem `HasBasis.tendsto_left_iff` / 定理 `HasBasis.tendsto_left_iff`

English:
theorem HasBasis.tendsto_left_iff
  given: (hla : la.HasBasis pa sa)
  proof: by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl

中文:
定理 HasBasis.tendsto_left_iff
  条件: (hla : la.HasBasis pa sa)
  证明: by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl

Depends on / 依赖: Tendsto, hla.map, image_subset_iff, le_iff
-/
theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ forall t in lb, exists i, pa i ∧ MapsTo f (sa i) t := by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl

/--
theorem `HasBasis.tendsto_right_iff` / 定理 `HasBasis.tendsto_right_iff`

English:
theorem HasBasis.tendsto_right_iff
  given: (hlb : lb.HasBasis pb sb)
  proof: by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]

中文:
定理 HasBasis.tendsto_right_iff
  条件: (hlb : lb.HasBasis pb sb)
  证明: by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Tendsto, ge_iff, hlb.ge_iff, mem_map
-/
theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ forall i, pb i -> forallᶠ x in la, f x in sb i := by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]

/--
theorem `HasBasis.tendsto_iff` / 定理 `HasBasis.tendsto_iff`

English:
theorem HasBasis.tendsto_iff
  given: (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb)
  proof: by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]

中文:
定理 HasBasis.tendsto_iff
  条件: (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb)
  证明: by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]

Depends on / 依赖: eventually_iff, hla.eventually_iff, hlb.tendsto_right_iff, tendsto_right_iff
-/
theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ forall ib, pb ib -> exists ia, pa ia ∧ forall x in sa ia, f x in sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]

/--
theorem `Tendsto.basis_left` / 定理 `Tendsto.basis_left`

English:
theorem Tendsto.basis_left
  given: (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
  proof: hla.tendsto_left_iff.1 H

中文:
定理 Tendsto.basis_left
  条件: (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
  证明: hla.tendsto_left_iff.1 H

Depends on / 依赖: hla.tendsto_left_iff, tendsto_left_iff
-/
theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    forall t in lb, exists i, pa i ∧ MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H

/--
theorem `Tendsto.basis_right` / 定理 `Tendsto.basis_right`

English:
theorem Tendsto.basis_right
  given: (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb)
  proof: hlb.tendsto_right_iff.1 H

中文:
定理 Tendsto.basis_right
  条件: (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb)
  证明: hlb.tendsto_right_iff.1 H

Depends on / 依赖: hlb.tendsto_right_iff, tendsto_right_iff
-/
theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    forall i, pb i -> forallᶠ x in la, f x in sb i :=
  hlb.tendsto_right_iff.1 H

/--
theorem `Tendsto.basis_both` / 定理 `Tendsto.basis_both`

English:
theorem Tendsto.basis_both
  statement: (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
  proof: (hla.tendsto_iff hlb).1 H

中文:
定理 Tendsto.basis_both
  结论: (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
  证明: (hla.tendsto_iff hlb).1 H

Depends on / 依赖: hla.tendsto_iff, tendsto_iff
-/
theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    forall ib, pb ib -> exists ia, pa ia ∧ MapsTo f (sa ia) (sb ib) :=
  (hla.tendsto_iff hlb).1 H

/--
theorem `HasBasis.prod_pprod` / 定理 `HasBasis.prod_pprod`

English:
theorem HasBasis.prod_pprod
  given: (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb)
  proof: (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)

中文:
定理 HasBasis.prod_pprod
  条件: (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb)
  证明: (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)

Depends on / 依赖: Prod.fst, Prod.snd, hla.comap, hlb.comap
-/
theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)

/--
theorem `HasBasis.prod` / 定理 `HasBasis.prod`

English:
theorem HasBasis.prod
  statement: {ι ι' : Type*} {pa : ι -> Prop} {sa : ι -> Set α} {pb : ι' -> Prop}
  proof: (hla.comap Prod.fst).inf (hlb.comap Prod.snd)

中文:
定理 HasBasis.prod
  结论: {ι ι' : 类型} {pa : ι -> 命题} {sa : ι -> Set α} {pb : ι' -> 命题}
  证明: (hla.comap Prod.fst).inf (hlb.comap Prod.snd)

Depends on / 依赖: Prod.fst, Prod.snd, hla.comap, hlb.comap
-/
theorem HasBasis.prod {ι ι' : Type*} {pa : ι -> Prop} {sa : ι -> Set α} {pb : ι' -> Prop}
    {sb : ι' -> Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)

/--
theorem `HasBasis.principal_prod` / 定理 `HasBasis.principal_prod`

English:
theorem HasBasis.principal_prod
  given: (sa : Set α) (h : lb.HasBasis pb sb)
  proof: by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.snd).principal_inf _

中文:
定理 HasBasis.principal_prod
  条件: (sa : Set α) (h : lb.HasBasis pb sb)
  证明: by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.snd).principal_inf _
-/
protected theorem HasBasis.principal_prod (sa : Set α) (h : lb.HasBasis pb sb) :
    (𝓟 sa ×ˢ lb).HasBasis pb (sa ×ˢ sb ·) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.snd).principal_inf _

/--
theorem `HasBasis.prod_principal` / 定理 `HasBasis.prod_principal`

English:
theorem HasBasis.prod_principal
  given: (h : la.HasBasis pa sa) (sb : Set β)
  proof: by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.fst).inf_principal _

中文:
定理 HasBasis.prod_principal
  条件: (h : la.HasBasis pa sa) (sb : Set β)
  证明: by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.fst).inf_principal _
-/
protected theorem HasBasis.prod_principal (h : la.HasBasis pa sa) (sb : Set β) :
    (la ×ˢ 𝓟 sb).HasBasis pa (sa · ×ˢ sb) := by
  simpa only [prod_eq_inf, comap_principal, prod_eq] using (h.comap Prod.fst).inf_principal _

/--
theorem `HasBasis.top_prod` / 定理 `HasBasis.top_prod`

English:
theorem HasBasis.top_prod
  given: (h : lb.HasBasis pb sb)
  proof: by
  simpa only [principal_univ] using h.principal_prod univ

中文:
定理 HasBasis.top_prod
  条件: (h : lb.HasBasis pb sb)
  证明: by
  simpa only [principal_univ] using h.principal_prod univ
-/
protected theorem HasBasis.top_prod (h : lb.HasBasis pb sb) :
    (⊤ ×ˢ lb : Filter (α × β)).HasBasis pb (univ ×ˢ sb ·) := by
  simpa only [principal_univ] using h.principal_prod univ

/--
theorem `HasBasis.prod_top` / 定理 `HasBasis.prod_top`

English:
theorem HasBasis.prod_top
  given: (h : la.HasBasis pa sa)
  proof: by
  simpa only [principal_univ] using h.prod_principal univ

中文:
定理 HasBasis.prod_top
  条件: (h : la.HasBasis pa sa)
  证明: by
  simpa only [principal_univ] using h.prod_principal univ
-/
protected theorem HasBasis.prod_top (h : la.HasBasis pa sa) :
    (la ×ˢ ⊤ : Filter (α × β)).HasBasis pa (sa · ×ˢ univ) := by
  simpa only [principal_univ] using h.prod_principal univ

/--
theorem `HasBasis.prod_same_index` / 定理 `HasBasis.prod_same_index`

English:
theorem HasBasis.prod_same_index
  statement: {p : ι -> Prop} {sb : ι -> Set β} (hla : la.HasBasis p sa)
  proof: by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j subseteq t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩

中文:
定理 HasBasis.prod_same_index
  结论: {p : ι -> 命题} {sb : ι -> Set β} (hla : la.HasBasis p sa)
  证明: by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j subseteq t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩

Depends on / 依赖: Set.prod_mono, h_dir, hasBasis_iff, hla.prod_pprod, mem_iff, prod_mono, prod_pprod, subseteq
-/
theorem HasBasis.prod_same_index {p : ι -> Prop} {sb : ι -> Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : forall {i j}, p i -> p j -> exists k, p k ∧ sa k subseteq sa i ∧ sb k subseteq sb j) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i := by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j subseteq t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩

/--
theorem `HasBasis.prod_same_index_mono` / 定理 `HasBasis.prod_same_index_mono`

English:
theorem HasBasis.prod_same_index_mono
  statement: {ι : Type*} [LinearOrder ι] {p : ι -> Prop} {sa : ι -> Set α}
  proof: hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
⟨min i j, this, hsa this hi min_le_left _ _, hsb this hj min_le_right _ _⟩

中文:
定理 HasBasis.prod_same_index_mono
  结论: {ι : 类型} [LinearOrder ι] {p : ι -> 命题} {sa : ι -> Set α}
  证明: hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
⟨min i j, this, hsa this hi min_le_left _ _, hsb this hj min_le_right _ _⟩

Depends on / 依赖: hla.prod_same_index, min_le_left, min_le_right, min_rec, prod_same_index
-/
theorem HasBasis.prod_same_index_mono {ι : Type*} [LinearOrder ι] {p : ι -> Prop} {sa : ι -> Set α}
    {sb : ι -> Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
⟨min i j, this, hsa this hi min_le_left _ _, hsb this hj min_le_right _ _⟩

/--
theorem `HasBasis.prod_same_index_anti` / 定理 `HasBasis.prod_same_index_anti`

English:
theorem HasBasis.prod_same_index_anti
  statement: {ι : Type*} [LinearOrder ι] {p : ι -> Prop} {sa : ι -> Set α}
  proof: @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left

中文:
定理 HasBasis.prod_same_index_anti
  结论: {ι : 类型} [LinearOrder ι] {p : ι -> 命题} {sa : ι -> Set α}
  证明: @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left

Depends on / 依赖: HasBasis, HasBasis.prod_same_index_mono, dual_left, hsa.dual_left, hsb.dual_left, prod_same_index_mono
-/
theorem HasBasis.prod_same_index_anti {ι : Type*} [LinearOrder ι] {p : ι -> Prop} {sa : ι -> Set α}
    {sb : ι -> Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left

/--
theorem `HasBasis.prod_self` / 定理 `HasBasis.prod_self`

English:
theorem HasBasis.prod_self
  given: (hl : la.HasBasis pa sa)
  proof: hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))

中文:
定理 HasBasis.prod_self
  条件: (hl : la.HasBasis pa sa)
  证明: hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))

Depends on / 依赖: exists_prop, hl.mem_iff, hl.mem_of_mem, hl.prod_same_index, inter_mem, mem_iff, mem_of_mem, prod_same_index, subset_inter_iff
-/
theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))

/--
theorem `mem_prod_self_iff` / 定理 `mem_prod_self_iff`

English:
theorem mem_prod_self_iff
  given: {s}
  statement: s in la ×ˢ la ↔ exists t in la, t ×ˢ t subseteq s
  proof: la.basis_sets.prod_self.mem_iff

中文:
定理 mem_prod_self_iff
  条件: {s}
  结论: s in la ×ˢ la ↔ 存在 t in la, t ×ˢ t subseteq s
  证明: la.basis_sets.prod_self.mem_iff

Depends on / 依赖: basis_sets, la.basis_sets.prod_self.mem_iff, mem_iff, prod_self
-/
theorem mem_prod_self_iff {s} : s in la ×ˢ la ↔ exists t in la, t ×ˢ t subseteq s :=
  la.basis_sets.prod_self.mem_iff

/--
lemma `eventually_prod_self_iff` / 引理 `eventually_prod_self_iff`

English:
lemma eventually_prod_self_iff
  given: {r : α -> α -> Prop}
  proof: mem_prod_self_iff.trans by simp only [prod_subset_iff, mem_ofPred_eq]

中文:
引理 eventually_prod_self_iff
  条件: {r : α -> α -> 命题}
  证明: mem_prod_self_iff.trans by simp only [prod_subset_iff, mem_ofPred_eq]

Depends on / 依赖: mem_ofPred_eq, mem_prod_self_iff, mem_prod_self_iff.trans, prod_subset_iff
-/
lemma eventually_prod_self_iff {r : α -> α -> Prop} :
    (forallᶠ x in la ×ˢ la, r x.1 x.2) ↔ exists t in la, forall x in t, forall y in t, r x y :=
mem_prod_self_iff.trans by simp only [prod_subset_iff, mem_ofPred_eq]

/--
lemma `eventually_prod_self_iff'` / 引理 `eventually_prod_self_iff'`

English:
lemma eventually_prod_self_iff'
  given: {r : α × α -> Prop}
  proof: Iff.symm eventually_prod_self_iff.symm

中文:
引理 eventually_prod_self_iff'
  条件: {r : α × α -> 命题}
  证明: Iff.symm eventually_prod_self_iff.symm

Depends on / 依赖: Iff.symm, eventually_prod_self_iff, eventually_prod_self_iff.symm
-/
lemma eventually_prod_self_iff' {r : α × α -> Prop} :
    (forallᶠ x in la ×ˢ la, r x) ↔ exists t in la, forall x in t, forall y in t, r (x, y) :=
  Iff.symm eventually_prod_self_iff.symm

/--
theorem `HasAntitoneBasis.prod` / 定理 `HasAntitoneBasis.prod`

English:
theorem HasAntitoneBasis.prod
  statement: {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
  proof: ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩

中文:
定理 HasAntitoneBasis.prod
  结论: {ι : 类型} [LinearOrder ι] {f : Filter α} {g : Filter β}
  证明: ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩

Depends on / 依赖: antitoneOn, prod_same_index_anti, set_prod
-/
theorem HasAntitoneBasis.prod {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι -> Set α} {t : ι -> Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ˢ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩

/--
theorem `HasBasis.coprod` / 定理 `HasBasis.coprod`

English:
theorem HasBasis.coprod
  statement: {ι ι' : Type*} {pa : ι -> Prop} {sa : ι -> Set α} {pb : ι' -> Prop}
  proof: (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

中文:
定理 HasBasis.coprod
  结论: {ι ι' : 类型} {pa : ι -> 命题} {sa : ι -> Set α} {pb : ι' -> 命题}
  证明: (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

Depends on / 依赖: Prod.fst, Prod.snd, hla.comap, hlb.comap
-/
theorem HasBasis.coprod {ι ι' : Type*} {pa : ι -> Prop} {sa : ι -> Set α} {pb : ι' -> Prop}
    {sb : ι' -> Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 union Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

end TwoTypes

/--
theorem `map_sigma_mk_comap` / 定理 `map_sigma_mk_comap`

English:
theorem map_sigma_mk_comap
  statement: {π : α -> Type*} {π' : β -> Type*} {f : α -> β}
  proof: by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert! ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

中文:
定理 map_sigma_mk_comap
  结论: {π : α -> 类型} {π' : β -> 类型} {f : α -> β}
  证明: by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert! ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

Depends on / 依赖: Sigma.map, Sigma.mk, basis_sets, convert, eq_of_same_basis, image_sigmaMk_preimage_sigmaMap
-/
theorem map_sigma_mk_comap {π : α -> Type*} {π' : β -> Type*} {f : α -> β}
    (hf : Function.Injective f) (g : forall a, π a -> π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) := by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert! ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

end Filter
