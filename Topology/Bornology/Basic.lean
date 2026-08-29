/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Basic theory of bornology

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter. This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `Bornology.ofBounded`,
`IsBounded.union`, `IsBounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `Bornology α`: a class consisting of `cobounded : Filter α` and a proof that this filter
  contains the `cofinite` filter.
- `Bornology.IsCobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : Set α`, one should prefer `Bornology.IsCobounded s` over `s ∈ cobounded α`.
- `bornology.IsBounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `Bornology.IsBounded s` over `sᶜ ∈ cobounded α`.
- `BoundedSpace α`: a class extending `Bornology α` with the condition
  `Bornology.IsBounded (Set.univ : Set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/

@[expose] public section


open Set Filter

variable {ι α β : Type*}

/--
Definition of `Bornology` / `Bornology` 的定义

English:
class Bornology
  parameters: (α : Type*)
  axioms and operations (2):
    - cobounded((α)) : Filter α
    - le_cofinite((α)) : cobounded <= cofinite

中文:
类 有界结构
  参数: (α : 类型)
  公理与运算 (2 个):
    - cobounded((α)) : 滤子 α
    - le_cofinite((α)) : cobounded <= cofinite
-/
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded <= cofinite

@[ext]
/--
lemma `Bornology.ext` / 引理 `Bornology.ext`

English:
lemma Bornology.ext
  statement: (t t' : Bornology α)
  proof: by
  cases t
  cases t'
  congr

中文:
引理 有界结构.ext
  结论: (t t' : 有界结构 α)
  证明: by
  cases t
  cases t'
  congr
-/
lemma Bornology.ext (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps, instance_reducible]
/--
Definition of `Bornology.ofBounded` / `Bornology.ofBounded` 的定义

English:
definition Bornology.ofBounded
  signature: {α : Type*} (B : Set (Set α))
  body: comk (· in B) empty_mem subset_mem union_mem
  le_cofinite := by simpa [le_cofinite_iff_compl_singleton_mem]

中文:
定义 有界结构.ofBounded
  签名: {α : 类型} (B : 集合 (集合 α))
  定义体: comk (· in B) empty_mem subset_mem union_mem
  le_cofinite := by simpa [le_cofinite_iff_compl_singleton_mem]

Depends on / 依赖: empty_mem, subset_mem, union_mem
-/
def Bornology.ofBounded {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ in B)
    (subset_mem : forall s₁ in B, forall s₂ subseteq s₁, s₂ in B)
    (union_mem : forall s₁ in B, forall s₂ in B, s₁ union s₂ in B)
    (singleton_mem : forall x, {x} in B) : Bornology α where
  cobounded := comk (· in B) empty_mem subset_mem union_mem
  le_cofinite := by simpa [le_cofinite_iff_compl_singleton_mem]

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps! cobounded, instance_reducible]
/--
Definition of `Bornology.ofBounded'` / `Bornology.ofBounded'` 的定义

English:
definition Bornology.ofBounded'
  signature: {α : Type*} (B : Set (Set α))
  body: Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)

中文:
定义 有界结构.ofBounded'
  签名: {α : 类型} (B : 集合 (集合 α))
  定义体: Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)

Depends on / 依赖: Bornology, Bornology.ofBounded, empty_mem, ofBounded, sUnion_eq_univ_iff, sUnion_univ, singleton_subset_iff, singleton_subset_iff.mpr, subset_mem, union_mem
-/
def Bornology.ofBounded' {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ in B)
    (subset_mem : forall s₁ in B, forall s₂ subseteq s₁, s₂ in B)
    (union_mem : forall s₁ in B, forall s₂ in B, s₁ union s₂ in B)
    (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
namespace Bornology

section

/--
Definition of `IsCobounded` / `IsCobounded` 的定义

English:
definition IsCobounded
  signature: [Bornology α] (s : Set α)
  body: s in cobounded α

中文:
定义 IsCobounded
  签名: [有界结构 α] (s : 集合 α)
  定义体: s in cobounded α

Depends on / 依赖: cobounded
-/
def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s in cobounded α

/--
Definition of `IsBounded` / `IsBounded` 的定义

English:
definition IsBounded
  signature: [Bornology α] (s : Set α)
  body: IsCobounded sᶜ

中文:
定义 IsBounded
  签名: [有界结构 α] (s : 集合 α)
  定义体: IsCobounded sᶜ

Depends on / 依赖: IsCobounded
-/
def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ

variable {_ : Bornology α} {s t : Set α} {x : α}

/--
theorem `isCobounded_def` / 定理 `isCobounded_def`

English:
theorem isCobounded_def
  given: {s : Set α}
  statement: IsCobounded s ↔ s in cobounded α
  proof: Iff.rfl

中文:
定理 isCobounded_def
  条件: {s : 集合 α}
  结论: IsCobounded s ↔ s in cobounded α
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isCobounded_def {s : Set α} : IsCobounded s ↔ s in cobounded α :=
  Iff.rfl

/--
theorem `isBounded_def` / 定理 `isBounded_def`

English:
theorem isBounded_def
  given: {s : Set α}
  statement: IsBounded s ↔ sᶜ in cobounded α
  proof: Iff.rfl

@[simp]

中文:
定理 isBounded_def
  条件: {s : 集合 α}
  结论: IsBounded s ↔ sᶜ in cobounded α
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in cobounded α :=
  Iff.rfl

@[simp]
/--
theorem `isBounded_compl_iff` / 定理 `isBounded_compl_iff`

English:
theorem isBounded_compl_iff
  statement: IsBounded sᶜ ↔ IsCobounded s
  proof: by
  rw [isBounded_def]; rw [isCobounded_def]; rw [compl_compl]

@[simp]

中文:
定理 isBounded_compl_iff
  结论: IsBounded sᶜ ↔ IsCobounded s
  证明: by
  rw [isBounded_def]; rw [isCobounded_def]; rw [compl_compl]

@[simp]

Depends on / 依赖: compl_compl, isBounded_def, isCobounded_def
-/
theorem isBounded_compl_iff : IsBounded sᶜ ↔ IsCobounded s := by
  rw [isBounded_def]; rw [isCobounded_def]; rw [compl_compl]

@[simp]
/--
theorem `isCobounded_compl_iff` / 定理 `isCobounded_compl_iff`

English:
theorem isCobounded_compl_iff
  statement: IsCobounded sᶜ ↔ IsBounded s
  proof: Iff.rfl

alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff

alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff

@[simp]

中文:
定理 isCobounded_compl_iff
  结论: IsCobounded sᶜ ↔ IsBounded s
  证明: Iff.rfl

alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff

alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem isCobounded_compl_iff : IsCobounded sᶜ ↔ IsBounded s :=
  Iff.rfl

alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff

alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff

@[simp]
/--
theorem `isBounded_empty` / 定理 `isBounded_empty`

English:
theorem isBounded_empty
  statement: IsBounded (∅ : Set α)
  proof: by
  rw [isBounded_def]; rw [compl_empty]
  exact univ_mem

中文:
定理 isBounded_empty
  结论: IsBounded (∅ : 集合 α)
  证明: by
  rw [isBounded_def]; rw [compl_empty]
  exact univ_mem

Depends on / 依赖: compl_empty, isBounded_def, univ_mem
-/
theorem isBounded_empty : IsBounded (∅ : Set α) := by
  rw [isBounded_def]; rw [compl_empty]
  exact univ_mem

/--
theorem `nonempty_of_not_isBounded` / 定理 `nonempty_of_not_isBounded`

English:
theorem nonempty_of_not_isBounded
  given: (h : ¬IsBounded s)
  statement: s.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h isBounded_empty

@[simp]

中文:
定理 nonempty_of_not_isBounded
  条件: (h : ¬IsBounded s)
  结论: s.非空
  证明: by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h isBounded_empty

@[simp]

Depends on / 依赖: isBounded_empty, nonempty_iff_ne_empty
-/
theorem nonempty_of_not_isBounded (h : ¬IsBounded s) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h isBounded_empty

@[simp]
/--
theorem `isBounded_singleton` / 定理 `isBounded_singleton`

English:
theorem isBounded_singleton
  statement: IsBounded ({x} : Set α)
  proof: by
  rw [isBounded_def]
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite

中文:
定理 isBounded_singleton
  结论: IsBounded ({x} : 集合 α)
  证明: by
  rw [isBounded_def]
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite

Depends on / 依赖: compl_mem_cofinite, finite_singleton, isBounded_def, le_cofinite
-/
theorem isBounded_singleton : IsBounded ({x} : Set α) := by
  rw [isBounded_def]
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite

/--
theorem `isBounded_iff_forall_mem` / 定理 `isBounded_iff_forall_mem`

English:
theorem isBounded_iff_forall_mem
  statement: IsBounded s ↔ forall x in s, IsBounded s
  proof: ⟨fun h _ _ => h, fun h => by
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    exacts [isBounded_empty, h x hx]⟩

@[simp]

中文:
定理 isBounded_iff_对任意_mem
  结论: IsBounded s ↔ 对任意 x in s, IsBounded s
  证明: ⟨fun h _ _ => h, fun h => by
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    exacts [isBounded_empty, h x hx]⟩

@[simp]

Depends on / 依赖: eq_empty_or_nonempty, exacts, isBounded_empty, s.eq_empty_or_nonempty
-/
theorem isBounded_iff_forall_mem : IsBounded s ↔ forall x in s, IsBounded s :=
  ⟨fun h _ _ => h, fun h => by
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    exacts [isBounded_empty, h x hx]⟩

@[simp]
/--
theorem `isCobounded_univ` / 定理 `isCobounded_univ`

English:
theorem isCobounded_univ
  statement: IsCobounded (univ : Set α)
  proof: univ_mem

@[simp]

中文:
定理 isCobounded_univ
  结论: IsCobounded (univ : 集合 α)
  证明: univ_mem

@[simp]

Depends on / 依赖: univ_mem
-/
theorem isCobounded_univ : IsCobounded (univ : Set α) :=
  univ_mem

@[simp]
/--
theorem `isCobounded_inter` / 定理 `isCobounded_inter`

English:
theorem isCobounded_inter
  statement: IsCobounded (s inter t) ↔ IsCobounded s ∧ IsCobounded t
  proof: inter_mem_iff

中文:
定理 isCobounded_inter
  结论: IsCobounded (s inter t) ↔ IsCobounded s ∧ IsCobounded t
  证明: inter_mem_iff

Depends on / 依赖: inter_mem_iff
-/
theorem isCobounded_inter : IsCobounded (s inter t) ↔ IsCobounded s ∧ IsCobounded t :=
  inter_mem_iff

/--
theorem `IsCobounded.inter` / 定理 `IsCobounded.inter`

English:
theorem IsCobounded.inter
  given: (hs : IsCobounded s) (ht : IsCobounded t)
  statement: IsCobounded (s inter t)
  proof: isCobounded_inter.2 ⟨hs, ht⟩

@[simp]

中文:
定理 IsCobounded.inter
  条件: (hs : IsCobounded s) (ht : IsCobounded t)
  结论: IsCobounded (s inter t)
  证明: isCobounded_inter.2 ⟨hs, ht⟩

@[simp]

Depends on / 依赖: isCobounded_inter
-/
theorem IsCobounded.inter (hs : IsCobounded s) (ht : IsCobounded t) : IsCobounded (s inter t) :=
  isCobounded_inter.2 ⟨hs, ht⟩

@[simp]
/--
theorem `isBounded_union` / 定理 `isBounded_union`

English:
theorem isBounded_union
  statement: IsBounded (s union t) ↔ IsBounded s ∧ IsBounded t
  proof: by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]

中文:
定理 isBounded_union
  结论: IsBounded (s union t) ↔ IsBounded s ∧ IsBounded t
  证明: by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]

Depends on / 依赖: compl_union, isCobounded_compl_iff, isCobounded_inter
-/
theorem isBounded_union : IsBounded (s union t) ↔ IsBounded s ∧ IsBounded t := by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]

/--
theorem `IsBounded.union` / 定理 `IsBounded.union`

English:
theorem IsBounded.union
  given: (hs : IsBounded s) (ht : IsBounded t)
  statement: IsBounded (s union t)
  proof: isBounded_union.2 ⟨hs, ht⟩

中文:
定理 IsBounded.union
  条件: (hs : IsBounded s) (ht : IsBounded t)
  结论: IsBounded (s union t)
  证明: isBounded_union.2 ⟨hs, ht⟩

Depends on / 依赖: isBounded_union
-/
theorem IsBounded.union (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s union t) :=
  isBounded_union.2 ⟨hs, ht⟩

/--
theorem `IsCobounded.superset` / 定理 `IsCobounded.superset`

English:
theorem IsCobounded.superset
  given: (hs : IsCobounded s) (ht : s subseteq t)
  statement: IsCobounded t
  proof: mem_of_superset hs ht

中文:
定理 IsCobounded.superset
  条件: (hs : IsCobounded s) (ht : s subseteq t)
  结论: IsCobounded t
  证明: mem_of_superset hs ht

Depends on / 依赖: mem_of_superset
-/
theorem IsCobounded.superset (hs : IsCobounded s) (ht : s subseteq t) : IsCobounded t :=
  mem_of_superset hs ht

/--
theorem `IsBounded.subset` / 定理 `IsBounded.subset`

English:
theorem IsBounded.subset
  given: (ht : IsBounded t) (hs : s subseteq t)
  statement: IsBounded s
  proof: ht.superset (compl_subset_compl.mpr hs)

@[simp]

中文:
定理 IsBounded.subset
  条件: (ht : IsBounded t) (hs : s subseteq t)
  结论: IsBounded s
  证明: ht.superset (compl_subset_compl.mpr hs)

@[simp]

Depends on / 依赖: compl_subset_compl, compl_subset_compl.mpr, ht.superset, superset
-/
theorem IsBounded.subset (ht : IsBounded t) (hs : s subseteq t) : IsBounded s :=
  ht.superset (compl_subset_compl.mpr hs)

@[simp]
/--
theorem `sUnion_bounded_univ` / 定理 `sUnion_bounded_univ`

English:
theorem sUnion_bounded_univ
  statement: ⋃₀ { s : Set α | IsBounded s } = univ
  proof: sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩

中文:
定理 sUnion_bounded_univ
  结论: ⋃₀ { s : 集合 α | IsBounded s } = univ
  证明: sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩

Depends on / 依赖: isBounded_singleton, mem_singleton, sUnion_eq_univ_iff
-/
theorem sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ :=
  sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩

/--
theorem `IsBounded.insert` / 定理 `IsBounded.insert`

English:
theorem IsBounded.insert
  given: (h : IsBounded s) (x : α)
  statement: IsBounded (insert x s)
  proof: isBounded_singleton.union h

@[simp]

中文:
定理 IsBounded.insert
  条件: (h : IsBounded s) (x : α)
  结论: IsBounded (insert x s)
  证明: isBounded_singleton.union h

@[simp]

Depends on / 依赖: isBounded_singleton, isBounded_singleton.union
-/
theorem IsBounded.insert (h : IsBounded s) (x : α) : IsBounded (insert x s) :=
  isBounded_singleton.union h

@[simp]
/--
theorem `isBounded_insert` / 定理 `isBounded_insert`

English:
theorem isBounded_insert
  statement: IsBounded (insert x s) ↔ IsBounded s
  proof: ⟨fun h => h.subset (subset_insert _ _), (.insert · x)⟩

中文:
定理 isBounded_insert
  结论: IsBounded (insert x s) ↔ IsBounded s
  证明: ⟨fun h => h.subset (subset_insert _ _), (.insert · x)⟩

Depends on / 依赖: h.subset, insert, subset, subset_insert
-/
theorem isBounded_insert : IsBounded (insert x s) ↔ IsBounded s :=
  ⟨fun h => h.subset (subset_insert _ _), (.insert · x)⟩

/--
theorem `comap_cobounded_le_iff` / 定理 `comap_cobounded_le_iff`

English:
theorem comap_cobounded_le_iff
  given: [Bornology β] {f : α -> β}
  proof: by
  refine
    ⟨fun h s hs => ?_, fun h t ht =>
⟨(f '' tᶜ)ᶜ, h IsCobounded.compl ht, compl_subset_comm.1 subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm]; rw [← preimage_compl] at hts
  exact (IsCobounded.compl ht).subset ((image_mono hts).trans <| image_preimage_subset _ _)

中文:
定理 comap_cobounded_le_iff
  条件: [有界结构 β] {f : α -> β}
  证明: by
  refine
    ⟨fun h s hs => ?_, fun h t ht =>
⟨(f '' tᶜ)ᶜ, h IsCobounded.compl ht, compl_subset_comm.1 subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm]; rw [← preimage_compl] at hts
  exact (IsCobounded.compl ht).subset ((image_mono hts).trans <| image_preimage_subset _ _)

Depends on / 依赖: IsCobounded, IsCobounded.compl, compl_subset_comm, hs.compl, image_mono, image_preimage_subset, preimage_compl, subset, subset_compl_comm, subset_preimage_image
-/
theorem comap_cobounded_le_iff [Bornology β] {f : α -> β} :
    (cobounded β).comap f <= cobounded α ↔ forall ⦃s⦄, IsBounded s -> IsBounded (f '' s) := by
  refine
    ⟨fun h s hs => ?_, fun h t ht =>
⟨(f '' tᶜ)ᶜ, h IsCobounded.compl ht, compl_subset_comm.1 subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm]; rw [← preimage_compl] at hts
  exact (IsCobounded.compl ht).subset ((image_mono hts).trans <| image_preimage_subset _ _)

end

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  given: {t t' : Bornology α}
  proof: Bornology.ext_iff.trans Filter.ext_iff

中文:
定理 ext_iff'
  条件: {t t' : 有界结构 α}
  证明: Bornology.ext_iff.trans Filter.ext_iff

Depends on / 依赖: Bornology, Bornology.ext_iff.trans, Filter, Filter.ext_iff, ext_iff
-/
theorem ext_iff' {t t' : Bornology α} :
    t = t' ↔ forall s, s in @cobounded α t ↔ s in @cobounded α t' :=
  Bornology.ext_iff.trans Filter.ext_iff

/--
theorem `ext_iff_isBounded` / 定理 `ext_iff_isBounded`

English:
theorem ext_iff_isBounded
  given: {t t' : Bornology α}
  proof: ext_iff'.trans compl_surjective.forall

中文:
定理 ext_iff_isBounded
  条件: {t t' : 有界结构 α}
  证明: ext_iff'.trans compl_surjective.forall

Depends on / 依赖: compl_surjective, compl_surjective.forall, ext_iff
-/
theorem ext_iff_isBounded {t t' : Bornology α} :
    t = t' ↔ forall s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ext_iff'.trans compl_surjective.forall

variable {s : Set α}

/--
theorem `isCobounded_ofBounded_iff` / 定理 `isCobounded_ofBounded_iff`

English:
theorem isCobounded_ofBounded_iff
  given: (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ}
  proof: Iff.rfl

中文:
定理 isCobounded_ofBounded_iff
  条件: (B : 集合 (集合 α)) {empty_mem subset_mem union_mem sUnion_univ}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ in B :=
  Iff.rfl

/--
theorem `isBounded_ofBounded_iff` / 定理 `isBounded_ofBounded_iff`

English:
theorem isBounded_ofBounded_iff
  given: (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ}
  proof: by
  rw [isBounded_def]; rw [ofBounded_cobounded]; rw [compl_mem_comk]

中文:
定理 isBounded_ofBounded_iff
  条件: (B : 集合 (集合 α)) {empty_mem subset_mem union_mem sUnion_univ}
  证明: by
  rw [isBounded_def]; rw [ofBounded_cobounded]; rw [compl_mem_comk]

Depends on / 依赖: compl_mem_comk, isBounded_def, ofBounded_cobounded
-/
theorem isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s in B := by
  rw [isBounded_def]; rw [ofBounded_cobounded]; rw [compl_mem_comk]

variable [Bornology α]

/--
theorem `isCobounded_biInter` / 定理 `isCobounded_biInter`

English:
theorem isCobounded_biInter
  given: {s : Set ι} {f : ι -> Set α} (hs : s.Finite)
  proof: biInter_mem hs

@[simp]

中文:
定理 isCobounded_bi整数er
  条件: {s : 集合 ι} {f : ι -> 集合 α} (hs : s.有限)
  证明: biInter_mem hs

@[simp]

Depends on / 依赖: biInter_mem
-/
theorem isCobounded_biInter {s : Set ι} {f : ι -> Set α} (hs : s.Finite) :
    IsCobounded (⋂ i in s, f i) ↔ forall i in s, IsCobounded (f i) :=
  biInter_mem hs

@[simp]
/--
theorem `isCobounded_biInter_finset` / 定理 `isCobounded_biInter_finset`

English:
theorem isCobounded_biInter_finset
  given: (s : Finset ι) {f : ι -> Set α}
  proof: biInter_finset_mem s

@[simp]

中文:
定理 isCobounded_bi整数er_finset
  条件: (s : 有限集 ι) {f : ι -> 集合 α}
  证明: biInter_finset_mem s

@[simp]

Depends on / 依赖: biInter_finset_mem
-/
theorem isCobounded_biInter_finset (s : Finset ι) {f : ι -> Set α} :
    IsCobounded (⋂ i in s, f i) ↔ forall i in s, IsCobounded (f i) :=
  biInter_finset_mem s

@[simp]
/--
theorem `isCobounded_iInter` / 定理 `isCobounded_iInter`

English:
theorem isCobounded_iInter
  given: [Finite ι] {f : ι -> Set α}
  proof: iInter_mem

中文:
定理 isCobounded_i整数er
  条件: [有限 ι] {f : ι -> 集合 α}
  证明: iInter_mem

Depends on / 依赖: iInter_mem
-/
theorem isCobounded_iInter [Finite ι] {f : ι -> Set α} :
    IsCobounded (⋂ i, f i) ↔ forall i, IsCobounded (f i) :=
  iInter_mem

/--
theorem `isCobounded_sInter` / 定理 `isCobounded_sInter`

English:
theorem isCobounded_sInter
  given: {S : Set (Set α)} (hs : S.Finite)
  proof: sInter_mem hs

中文:
定理 isCobounded_s整数er
  条件: {S : 集合 (集合 α)} (hs : S.有限)
  证明: sInter_mem hs

Depends on / 依赖: sInter_mem
-/
theorem isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) :
    IsCobounded (⋂₀ S) ↔ forall s in S, IsCobounded s :=
  sInter_mem hs

/--
theorem `isBounded_biUnion` / 定理 `isBounded_biUnion`

English:
theorem isBounded_biUnion
  given: {s : Set ι} {f : ι -> Set α} (hs : s.Finite)
  proof: by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]

中文:
定理 isBounded_biUnion
  条件: {s : 集合 ι} {f : ι -> 集合 α} (hs : s.有限)
  证明: by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]

Depends on / 依赖: compl_iUnion, isCobounded_biInter, isCobounded_compl_iff
-/
theorem isBounded_biUnion {s : Set ι} {f : ι -> Set α} (hs : s.Finite) :
    IsBounded (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i) := by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]

/--
theorem `isBounded_biUnion_finset` / 定理 `isBounded_biUnion_finset`

English:
theorem isBounded_biUnion_finset
  given: (s : Finset ι) {f : ι -> Set α}
  proof: isBounded_biUnion s.finite_toSet

中文:
定理 isBounded_biUnion_finset
  条件: (s : 有限集 ι) {f : ι -> 集合 α}
  证明: isBounded_biUnion s.finite_toSet

Depends on / 依赖: finite_toSet, isBounded_biUnion, s.finite_toSet
-/
theorem isBounded_biUnion_finset (s : Finset ι) {f : ι -> Set α} :
    IsBounded (⋃ i in s, f i) ↔ forall i in s, IsBounded (f i) :=
  isBounded_biUnion s.finite_toSet

/--
theorem `isBounded_sUnion` / 定理 `isBounded_sUnion`

English:
theorem isBounded_sUnion
  given: {S : Set (Set α)} (hs : S.Finite)
  proof: by rw [sUnion_eq_biUnion, isBounded_biUnion hs]

@[simp]

中文:
定理 isBounded_sUnion
  条件: {S : 集合 (集合 α)} (hs : S.有限)
  证明: by rw [sUnion_eq_biUnion, isBounded_biUnion hs]

@[simp]

Depends on / 依赖: isBounded_biUnion, sUnion_eq_biUnion
-/
theorem isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) :
    IsBounded (⋃₀ S) ↔ forall s in S, IsBounded s := by rw [sUnion_eq_biUnion, isBounded_biUnion hs]

@[simp]
/--
theorem `isBounded_iUnion` / 定理 `isBounded_iUnion`

English:
theorem isBounded_iUnion
  given: [Finite ι] {s : ι -> Set α}
  proof: by
  rw [← sUnion_range]; rw [isBounded_sUnion (finite_range s)]; rw [forall_mem_range]

中文:
定理 isBounded_iUnion
  条件: [有限 ι] {s : ι -> 集合 α}
  证明: by
  rw [← sUnion_range]; rw [isBounded_sUnion (finite_range s)]; rw [forall_mem_range]

Depends on / 依赖: finite_range, forall_mem_range, isBounded_sUnion, sUnion_range
-/
theorem isBounded_iUnion [Finite ι] {s : ι -> Set α} :
    IsBounded (⋃ i, s i) ↔ forall i, IsBounded (s i) := by
  rw [← sUnion_range]; rw [isBounded_sUnion (finite_range s)]; rw [forall_mem_range]

/--
lemma `eventually_ne_cobounded` / 引理 `eventually_ne_cobounded`

English:
lemma eventually_ne_cobounded
  given: (a : α)
  statement: forallᶠ x in cobounded α, x != a
  proof: le_cofinite_iff_eventually_ne.1 (le_cofinite _) a

中文:
引理 eventually_ne_cobounded
  条件: (a : α)
  结论: 对任意ᶠ x in cobounded α, x != a
  证明: le_cofinite_iff_eventually_ne.1 (le_cofinite _) a

Depends on / 依赖: le_cofinite, le_cofinite_iff_eventually_ne
-/
lemma eventually_ne_cobounded (a : α) : forallᶠ x in cobounded α, x != a :=
  le_cofinite_iff_eventually_ne.1 (le_cofinite _) a

end Bornology

open Bornology

/--
theorem `Filter.HasBasis.disjoint_cobounded_iff` / 定理 `Filter.HasBasis.disjoint_cobounded_iff`

English:
theorem Filter.HasBasis.disjoint_cobounded_iff
  statement: [Bornology α] {ι : Sort*} {p : ι -> Prop}
  proof: h.disjoint_iff_left

中文:
定理 滤子.有基.disjoint_cobounded_iff
  结论: [有界结构 α] {ι : 类型层*} {p : ι -> 命题}
  证明: h.disjoint_iff_left

Depends on / 依赖: disjoint_iff_left, h.disjoint_iff_left
-/
theorem Filter.HasBasis.disjoint_cobounded_iff [Bornology α] {ι : Sort*} {p : ι -> Prop}
    {s : ι -> Set α} {l : Filter α} (h : l.HasBasis p s) :
    Disjoint l (cobounded α) ↔ exists i, p i ∧ Bornology.IsBounded (s i) :=
  h.disjoint_iff_left

/--
theorem `Filter.disjoint_cobounded_iff` / 定理 `Filter.disjoint_cobounded_iff`

English:
theorem Filter.disjoint_cobounded_iff
  given: [Bornology α] {l : Filter α}
  proof: l.basis_sets.disjoint_cobounded_iff

alias ⟨Disjoint.exists_isBounded, _⟩ := Filter.disjoint_cobounded_iff

中文:
定理 滤子.disjoint_cobounded_iff
  条件: [有界结构 α] {l : 滤子 α}
  证明: l.basis_sets.disjoint_cobounded_iff

alias ⟨Disjoint.exists_isBounded, _⟩ := Filter.disjoint_cobounded_iff

Depends on / 依赖: basis_sets, disjoint_cobounded_iff, l.basis_sets.disjoint_cobounded_iff
-/
theorem Filter.disjoint_cobounded_iff [Bornology α] {l : Filter α} :
    Disjoint l (cobounded α) ↔ exists s in l, Bornology.IsBounded s :=
  l.basis_sets.disjoint_cobounded_iff

alias ⟨Disjoint.exists_isBounded, _⟩ := Filter.disjoint_cobounded_iff

/--
theorem `Bornology.IsBounded.disjoint_cobounded` / 定理 `Bornology.IsBounded.disjoint_cobounded`

English:
theorem Bornology.IsBounded.disjoint_cobounded
  statement: [Bornology α]
  proof: l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩

中文:
定理 有界结构.IsBounded.disjoint_cobounded
  结论: [有界结构 α]
  证明: l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩

Depends on / 依赖: disjoint_cobounded_iff, l.disjoint_cobounded_iff.mpr
-/
theorem Bornology.IsBounded.disjoint_cobounded [Bornology α]
    {l : Filter α} {s : Set α} (hs : IsBounded s) (hl : s in l) :
    Disjoint l (cobounded α) :=
  l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩

/--
theorem `Set.Finite.isBounded` / 定理 `Set.Finite.isBounded`

English:
theorem Set.Finite.isBounded
  given: [Bornology α] {s : Set α} (hs : s.Finite)
  statement: IsBounded s
  proof: Bornology.le_cofinite α hs.compl_mem_cofinite

nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β -> α} {l : Filter β}
    (h : Tendsto f l (cobounded α)) (a : α) : forallᶠ x in l, f x != a :=
h.eventually eventually_ne_cobounded a

中文:
定理 集合.有限.isBounded
  条件: [有界结构 α] {s : 集合 α} (hs : s.有限)
  结论: IsBounded s
  证明: Bornology.le_cofinite α hs.compl_mem_cofinite

nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β -> α} {l : Filter β}
    (h : Tendsto f l (cobounded α)) (a : α) : forallᶠ x in l, f x != a :=
h.eventually eventually_ne_cobounded a

Depends on / 依赖: Bornology, Bornology.le_cofinite, compl_mem_cofinite, hs.compl_mem_cofinite, le_cofinite
-/
theorem Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded s :=
  Bornology.le_cofinite α hs.compl_mem_cofinite

nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β -> α} {l : Filter β}
    (h : Tendsto f l (cobounded α)) (a : α) : forallᶠ x in l, f x != a :=
h.eventually eventually_ne_cobounded a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bornology PUnit
  body: ⟨⊥, bot_le⟩

中文:
实例 :
  签名: 有界结构 命题单元
  定义体: ⟨⊥, bot_le⟩
-/
instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩

/--
Definition of `Bornology.cofinite` / `Bornology.cofinite` 的定义

English:
abbreviation Bornology.cofinite
  signature: : Bornology α where
  body: Filter.cofinite
  le_cofinite := le_rfl

中文:
缩写 有界结构.cofinite
  签名: : 有界结构 α where
  定义体: Filter.cofinite
  le_cofinite := le_rfl

Depends on / 依赖: Filter, Filter.cofinite, cofinite
-/
abbrev Bornology.cofinite : Bornology α where
  cobounded := Filter.cofinite
  le_cofinite := le_rfl

/--
Definition of `BoundedSpace` / `BoundedSpace` 的定义

English:
class BoundedSpace
  parameters: (α : Type*) [Bornology α]
  axioms and operations (1):
    - bounded_univ : Bornology.IsBounded (univ : Set α)

中文:
类 有界空间
  参数: (α : 类型) [有界结构 α]
  公理与运算 (1 个):
    - bounded_univ : 有界结构.IsBounded (univ : 集合 α)
-/
class BoundedSpace (α : Type*) [Bornology α] : Prop where
  /-- The `Set.univ` is bounded. -/
  bounded_univ : Bornology.IsBounded (univ : Set α)

/-- A finite space is bounded. -/
instance (priority := 100) BoundedSpace.of_finite {α : Type*} [Bornology α] [Finite α] :
    BoundedSpace α where
  bounded_univ := (toFinite _).isBounded

namespace Bornology

variable [Bornology α]

/--
theorem `isBounded_univ` / 定理 `isBounded_univ`

English:
theorem isBounded_univ
  statement: IsBounded (univ : Set α) ↔ BoundedSpace α
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
定理 isBounded_univ
  结论: IsBounded (univ : 集合 α) ↔ 有界空间 α
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩
-/
theorem isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/--
theorem `cobounded_eq_bot_iff` / 定理 `cobounded_eq_bot_iff`

English:
theorem cobounded_eq_bot_iff
  statement: cobounded α = ⊥ ↔ BoundedSpace α
  proof: by
  rw [← isBounded_univ]; rw [isBounded_def]; rw [compl_univ]; rw [empty_mem_iff_bot]

中文:
定理 cobounded_eq_bot_iff
  结论: cobounded α = ⊥ ↔ 有界空间 α
  证明: by
  rw [← isBounded_univ]; rw [isBounded_def]; rw [compl_univ]; rw [empty_mem_iff_bot]

Depends on / 依赖: compl_univ, empty_mem_iff_bot, isBounded_def, isBounded_univ
-/
theorem cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α := by
  rw [← isBounded_univ]; rw [isBounded_def]; rw [compl_univ]; rw [empty_mem_iff_bot]

variable [BoundedSpace α]

/--
theorem `IsBounded.all` / 定理 `IsBounded.all`

English:
theorem IsBounded.all
  given: (s : Set α)
  statement: IsBounded s
  proof: BoundedSpace.bounded_univ.subset s.subset_univ

中文:
定理 IsBounded.all
  条件: (s : 集合 α)
  结论: IsBounded s
  证明: BoundedSpace.bounded_univ.subset s.subset_univ

Depends on / 依赖: BoundedSpace, BoundedSpace.bounded_univ.subset, bounded_univ, s.subset_univ, subset, subset_univ
-/
theorem IsBounded.all (s : Set α) : IsBounded s :=
  BoundedSpace.bounded_univ.subset s.subset_univ

/--
theorem `IsCobounded.all` / 定理 `IsCobounded.all`

English:
theorem IsCobounded.all
  given: (s : Set α)
  statement: IsCobounded s
  proof: compl_compl s ▸ IsBounded.all sᶜ

中文:
定理 IsCobounded.all
  条件: (s : 集合 α)
  结论: IsCobounded s
  证明: compl_compl s ▸ IsBounded.all sᶜ

Depends on / 依赖: IsBounded, IsBounded.all, compl_compl
-/
theorem IsCobounded.all (s : Set α) : IsCobounded s :=
  compl_compl s ▸ IsBounded.all sᶜ

variable (α)

@[simp]
/--
theorem `cobounded_eq_bot` / 定理 `cobounded_eq_bot`

English:
theorem cobounded_eq_bot
  statement: cobounded α = ⊥
  proof: cobounded_eq_bot_iff.2 ‹_›

中文:
定理 cobounded_eq_bot
  结论: cobounded α = ⊥
  证明: cobounded_eq_bot_iff.2 ‹_›

Depends on / 依赖: cobounded_eq_bot_iff
-/
theorem cobounded_eq_bot : cobounded α = ⊥ :=
  cobounded_eq_bot_iff.2 ‹_›

end Bornology

namespace OrderDual
variable [Bornology α]

/--
Instance `instBornology` / 实例 `instBornology`

English:
instance instBornology
  signature: : Bornology αᵒᵈ
  body: ‹Bornology α›

中文:
实例 instBornology
  签名: : 有界结构 αᵒᵈ
  定义体: ‹Bornology α›

Depends on / 依赖: Bornology
-/
instance instBornology : Bornology αᵒᵈ := ‹Bornology α›

/--
lemma `isCobounded_preimage_ofDual` / 引理 `isCobounded_preimage_ofDual`

English:
lemma isCobounded_preimage_ofDual
  given: {s : Set α}
  proof: Iff.rfl

中文:
引理 isCobounded_preimage_ofDual
  条件: {s : 集合 α}
  证明: Iff.rfl
-/
@[simp] lemma isCobounded_preimage_ofDual {s : Set α} :
    IsCobounded (ofDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl

/--
lemma `isCobounded_preimage_toDual` / 引理 `isCobounded_preimage_toDual`

English:
lemma isCobounded_preimage_toDual
  given: {s : Set αᵒᵈ}
  proof: Iff.rfl

中文:
引理 isCobounded_preimage_toDual
  条件: {s : 集合 αᵒᵈ}
  证明: Iff.rfl
-/
@[simp] lemma isCobounded_preimage_toDual {s : Set αᵒᵈ} :
    IsCobounded (toDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl

/--
lemma `isBounded_preimage_ofDual` / 引理 `isBounded_preimage_ofDual`

English:
lemma isBounded_preimage_ofDual
  given: {s : Set α}
  proof: Iff.rfl

中文:
引理 isBounded_preimage_ofDual
  条件: {s : 集合 α}
  证明: Iff.rfl
-/
@[simp] lemma isBounded_preimage_ofDual {s : Set α} :
    IsBounded (ofDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

/--
lemma `isBounded_preimage_toDual` / 引理 `isBounded_preimage_toDual`

English:
lemma isBounded_preimage_toDual
  given: {s : Set αᵒᵈ}
  proof: Iff.rfl

中文:
引理 isBounded_preimage_toDual
  条件: {s : 集合 αᵒᵈ}
  证明: Iff.rfl
-/
@[simp] lemma isBounded_preimage_toDual {s : Set αᵒᵈ} :
    IsBounded (toDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

end OrderDual
