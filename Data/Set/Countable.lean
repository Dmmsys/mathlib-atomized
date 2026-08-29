/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Preorder.Finite

/-!
# Countable sets

In this file we define `Set.Countable s` as `Countable s`
and prove basic properties of this definition.

Note that this definition does not provide a computable encoding.
For a noncomputable conversion to `Encodable s`, use `Set.Countable.nonempty_encodable`.

## Keywords

sets, countable set
-/

@[expose] public section

assert_not_exists Monoid Multiset.sort

noncomputable section

open Function Set Encodable

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace Set

/--
Definition of `Countable` / `Countable` 的定义

English:
definition Countable
  signature: (s : Set α)
  body: Countable s

@[simp]

中文:
定义 可数
  签名: (s : 集合 α)
  定义体: Countable s

@[simp]
-/
protected def Countable (s : Set α) : Prop := Countable s

@[simp]
/--
theorem `countable_coe_iff` / 定理 `countable_coe_iff`

English:
theorem countable_coe_iff
  given: {s : Set α}
  statement: Countable s ↔ s.Countable
  proof: .rfl

中文:
定理 countable_coe_iff
  条件: {s : 集合 α}
  结论: 可数 s ↔ s.可数
  证明: .rfl
-/
theorem countable_coe_iff {s : Set α} : Countable s ↔ s.Countable := .rfl

/--
theorem `to_countable` / 定理 `to_countable`

English:
theorem to_countable
  given: (s : Set α) [Countable s]
  statement: s.Countable
  proof: ‹_›

中文:
定理 to_countable
  条件: (s : 集合 α) [可数 s]
  结论: s.可数
  证明: ‹_›
-/
theorem to_countable (s : Set α) [Countable s] : s.Countable := ‹_›

/-- Restate `Set.Countable` as a `Countable` instance. -/
alias ⟨_root_.Countable.to_set, Countable.to_subtype⟩ := countable_coe_iff

/--
theorem `countable_iff_exists_injective` / 定理 `countable_iff_exists_injective`

English:
theorem countable_iff_exists_injective
  given: {s : Set α}
  proof: countable_iff_exists_injective s

中文:
定理 countable_iff_存在_injective
  条件: {s : 集合 α}
  证明: countable_iff_exists_injective s
-/
protected theorem countable_iff_exists_injective {s : Set α} :
    s.Countable ↔ exists f : s -> Nat, Injective f :=
  countable_iff_exists_injective s

/--
theorem `countable_iff_exists_injOn` / 定理 `countable_iff_exists_injOn`

English:
theorem countable_iff_exists_injOn
  given: {s : Set α}
  statement: s.Countable ↔ exists f : α -> Nat, InjOn f s
  proof: Set.countable_iff_exists_injective.trans exists_injOn_iff_injective.symm

中文:
定理 countable_iff_存在_injOn
  条件: {s : 集合 α}
  结论: s.可数 ↔ 存在 f : α -> 自然数, 单射限制 f s
  证明: Set.countable_iff_exists_injective.trans exists_injOn_iff_injective.symm

Depends on / 依赖: Set.countable_iff_exists_injective.trans, countable_iff_exists_injective, exists_injOn_iff_injective, exists_injOn_iff_injective.symm
-/
theorem countable_iff_exists_injOn {s : Set α} : s.Countable ↔ exists f : α -> Nat, InjOn f s :=
  Set.countable_iff_exists_injective.trans exists_injOn_iff_injective.symm

/--
theorem `countable_iff_nonempty_encodable` / 定理 `countable_iff_nonempty_encodable`

English:
theorem countable_iff_nonempty_encodable
  given: {s : Set α}
  statement: s.Countable ↔ Nonempty (Encodable s)
  proof: Encodable.nonempty_encodable.symm

alias ⟨Countable.nonempty_encodable, _⟩ := countable_iff_nonempty_encodable

中文:
定理 countable_iff_nonempty_encodable
  条件: {s : 集合 α}
  结论: s.可数 ↔ 非空 (可编码 s)
  证明: Encodable.nonempty_encodable.symm

alias ⟨Countable.nonempty_encodable, _⟩ := countable_iff_nonempty_encodable

Depends on / 依赖: Encodable, Encodable.nonempty_encodable.symm, nonempty_encodable
-/
theorem countable_iff_nonempty_encodable {s : Set α} : s.Countable ↔ Nonempty (Encodable s) :=
  Encodable.nonempty_encodable.symm

alias ⟨Countable.nonempty_encodable, _⟩ := countable_iff_nonempty_encodable

/-- Convert `Set.Countable s` to `Encodable s` (noncomputable). -/
@[instance_reducible]
/--
Definition of `Countable.toEncodable` / `Countable.toEncodable` 的定义

English:
definition Countable.toEncodable
  signature: {s : Set α} (hs : s.Countable)
  body: Classical.choice hs.nonempty_encodable

中文:
定义 可数.toEncodable
  签名: {s : 集合 α} (hs : s.可数)
  定义体: Classical.choice hs.nonempty_encodable
-/
protected def Countable.toEncodable {s : Set α} (hs : s.Countable) : Encodable s :=
  Classical.choice hs.nonempty_encodable

section Enumerate

/--
Definition of `enumerateCountable` / `enumerateCountable` 的定义

English:
definition enumerateCountable
  signature: {s : Set α} (h : s.Countable) (default : α)
  body: fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default

中文:
定义 enumerateCountable
  签名: {s : 集合 α} (h : s.可数) (default : α)
  定义体: fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default
-/
def enumerateCountable {s : Set α} (h : s.Countable) (default : α) : Nat -> α := fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default

/--
theorem `subset_range_enumerate` / 定理 `subset_range_enumerate`

English:
theorem subset_range_enumerate
  given: {s : Set α} (h : s.Countable) (default : α)
  proof: fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [enumerateCountable, Encodable.encodek]⟩

中文:
定理 subset_range_enumerate
  条件: {s : 集合 α} (h : s.可数) (default : α)
  证明: fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [enumerateCountable, Encodable.encodek]⟩
-/
theorem subset_range_enumerate {s : Set α} (h : s.Countable) (default : α) :
    s subseteq range (enumerateCountable h default) := fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [enumerateCountable, Encodable.encodek]⟩

/--
lemma `range_enumerateCountable_subset` / 引理 `range_enumerateCountable_subset`

English:
lemma range_enumerateCountable_subset
  given: {s : Set α} (h : s.Countable) (default : α)
  proof: by
  refine range_subset_iff.mpr (fun n => ?_)
  rw [enumerateCountable]
  match @decode s (Countable.toEncodable h) n with
  | none => exact mem_insert _ _
  | some val => simp

中文:
引理 range_enumerateCountable_subset
  条件: {s : 集合 α} (h : s.可数) (default : α)
  证明: by
  refine range_subset_iff.mpr (fun n => ?_)
  rw [enumerateCountable]
  match @decode s (Countable.toEncodable h) n with
  | none => exact mem_insert _ _
  | some val => simp

Depends on / 依赖: Countable, Countable.toEncodable, decode, enumerateCountable, mem_insert, range_subset_iff, range_subset_iff.mpr, toEncodable
-/
lemma range_enumerateCountable_subset {s : Set α} (h : s.Countable) (default : α) :
    range (enumerateCountable h default) subseteq insert default s := by
  refine range_subset_iff.mpr (fun n => ?_)
  rw [enumerateCountable]
  match @decode s (Countable.toEncodable h) n with
  | none => exact mem_insert _ _
  | some val => simp

/--
lemma `range_enumerateCountable_of_mem` / 引理 `range_enumerateCountable_of_mem`

English:
lemma range_enumerateCountable_of_mem
  statement: {s : Set α} (h : s.Countable) {default : α}
  proof: subset_antisymm ((range_enumerateCountable_subset h _).trans_eq (insert_eq_of_mem h_mem))
    (subset_range_enumerate h default)

中文:
引理 range_enumerateCountable_of_mem
  结论: {s : 集合 α} (h : s.可数) {default : α}
  证明: subset_antisymm ((range_enumerateCountable_subset h _).trans_eq (insert_eq_of_mem h_mem))
    (subset_range_enumerate h default)

Depends on / 依赖: h_mem, insert_eq_of_mem, range_enumerateCountable_subset, subset_antisymm, subset_range_enumerate, trans_eq
-/
lemma range_enumerateCountable_of_mem {s : Set α} (h : s.Countable) {default : α}
    (h_mem : default in s) :
    range (enumerateCountable h default) = s :=
  subset_antisymm ((range_enumerateCountable_subset h _).trans_eq (insert_eq_of_mem h_mem))
    (subset_range_enumerate h default)

/--
lemma `enumerateCountable_mem` / 引理 `enumerateCountable_mem`

English:
lemma enumerateCountable_mem
  statement: {s : Set α} (h : s.Countable) {default : α} (h_mem : default in s)
  proof: by
  convert! mem_range_self n
  exact (range_enumerateCountable_of_mem h h_mem).symm

中文:
引理 enumerateCountable_mem
  结论: {s : 集合 α} (h : s.可数) {default : α} (h_mem : default in s)
  证明: by
  convert! mem_range_self n
  exact (range_enumerateCountable_of_mem h h_mem).symm

Depends on / 依赖: convert, h_mem, mem_range_self, range_enumerateCountable_of_mem
-/
lemma enumerateCountable_mem {s : Set α} (h : s.Countable) {default : α} (h_mem : default in s)
    (n : Nat) :
    enumerateCountable h default n in s := by
  convert! mem_range_self n
  exact (range_enumerateCountable_of_mem h h_mem).symm

end Enumerate

/--
theorem `Countable.mono` / 定理 `Countable.mono`

English:
theorem Countable.mono
  given: {s₁ s₂ : Set α} (h : s₁ subseteq s₂) (hs : s₂.Countable)
  statement: s₁.Countable
  proof: have := hs.to_subtype; (inclusion_injective h).countable

中文:
定理 可数.mono
  条件: {s₁ s₂ : 集合 α} (h : s₁ subseteq s₂) (hs : s₂.可数)
  结论: s₁.可数
  证明: have := hs.to_subtype; (inclusion_injective h).countable

Depends on / 依赖: countable, hs.to_subtype, inclusion_injective, to_subtype
-/
theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ subseteq s₂) (hs : s₂.Countable) : s₁.Countable :=
  have := hs.to_subtype; (inclusion_injective h).countable

/--
theorem `countable_range` / 定理 `countable_range`

English:
theorem countable_range
  given: [Countable ι] (f : ι -> β)
  statement: (range f).Countable
  proof: rangeFactorization_surjective.countable.to_set

中文:
定理 countable_range
  条件: [可数 ι] (f : ι -> β)
  结论: (range f).可数
  证明: rangeFactorization_surjective.countable.to_set

Depends on / 依赖: countable, rangeFactorization_surjective, rangeFactorization_surjective.countable.to_set, to_set
-/
theorem countable_range [Countable ι] (f : ι -> β) : (range f).Countable :=
  rangeFactorization_surjective.countable.to_set

/--
theorem `countable_iff_exists_subset_range` / 定理 `countable_iff_exists_subset_range`

English:
theorem countable_iff_exists_subset_range
  given: [Nonempty α] {s : Set α}
  proof: ⟨fun h => by
    inhabit α
    exact ⟨enumerateCountable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ =>
    (countable_range f).mono hsf⟩

中文:
定理 countable_iff_存在_subset_range
  条件: [非空 α] {s : 集合 α}
  证明: ⟨fun h => by
    inhabit α
    exact ⟨enumerateCountable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ =>
    (countable_range f).mono hsf⟩

Depends on / 依赖: countable_range, enumerateCountable, inhabit, subset_range_enumerate
-/
theorem countable_iff_exists_subset_range [Nonempty α] {s : Set α} :
    s.Countable ↔ exists f : Nat -> α, s subseteq range f :=
  ⟨fun h => by
    inhabit α
    exact ⟨enumerateCountable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ =>
    (countable_range f).mono hsf⟩

/--
theorem `countable_iff_exists_surjective` / 定理 `countable_iff_exists_surjective`

English:
theorem countable_iff_exists_surjective
  given: {s : Set α} (hs : s.Nonempty)
  proof: @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective

中文:
定理 countable_iff_存在_surjective
  条件: {s : 集合 α} (hs : s.非空)
  证明: @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ exists f : Nat -> s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective

/--
theorem `countable_univ_iff` / 定理 `countable_univ_iff`

English:
theorem countable_univ_iff
  statement: (univ : Set α).Countable ↔ Countable α
  proof: countable_coe_iff.symm.trans (Equiv.Set.univ _).countable_iff

中文:
定理 countable_univ_iff
  结论: (univ : 集合 α).可数 ↔ 可数 α
  证明: countable_coe_iff.symm.trans (Equiv.Set.univ _).countable_iff

Depends on / 依赖: Equiv.Set.univ, countable_coe_iff, countable_coe_iff.symm.trans, countable_iff
-/
theorem countable_univ_iff : (univ : Set α).Countable ↔ Countable α :=
  countable_coe_iff.symm.trans (Equiv.Set.univ _).countable_iff

/--
theorem `countable_univ` / 定理 `countable_univ`

English:
theorem countable_univ
  given: [Countable α]
  statement: (univ : Set α).Countable
  proof: to_countable univ

中文:
定理 countable_univ
  条件: [可数 α]
  结论: (univ : 集合 α).可数
  证明: to_countable univ

Depends on / 依赖: to_countable
-/
theorem countable_univ [Countable α] : (univ : Set α).Countable :=
  to_countable univ

/--
theorem `not_countable_univ_iff` / 定理 `not_countable_univ_iff`

English:
theorem not_countable_univ_iff
  statement: ¬ (univ : Set α).Countable ↔ Uncountable α
  proof: by
  rw [countable_univ_iff]; rw [not_countable_iff]

中文:
定理 not_countable_univ_iff
  结论: ¬ (univ : 集合 α).可数 ↔ 不可数 α
  证明: by
  rw [countable_univ_iff]; rw [not_countable_iff]

Depends on / 依赖: countable_univ_iff, not_countable_iff
-/
theorem not_countable_univ_iff : ¬ (univ : Set α).Countable ↔ Uncountable α := by
  rw [countable_univ_iff]; rw [not_countable_iff]

/--
theorem `not_countable_univ` / 定理 `not_countable_univ`

English:
theorem not_countable_univ
  given: [Uncountable α]
  statement: ¬ (univ : Set α).Countable
  proof: not_countable_univ_iff.2 ‹_›

中文:
定理 not_countable_univ
  条件: [不可数 α]
  结论: ¬ (univ : 集合 α).可数
  证明: not_countable_univ_iff.2 ‹_›

Depends on / 依赖: not_countable_univ_iff
-/
theorem not_countable_univ [Uncountable α] : ¬ (univ : Set α).Countable :=
  not_countable_univ_iff.2 ‹_›

/--
theorem `Countable.exists_eq_range` / 定理 `Countable.exists_eq_range`

English:
theorem Countable.exists_eq_range
  given: {s : Set α} (hc : s.Countable) (hs : s.Nonempty)
  proof: by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine ⟨(↑) ∘ f, ?_⟩
  rw [hf.range_comp]; rw [Subtype.range_coe]

中文:
定理 可数.存在_eq_range
  条件: {s : 集合 α} (hc : s.可数) (hs : s.非空)
  证明: by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine ⟨(↑) ∘ f, ?_⟩
  rw [hf.range_comp]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.range_coe, exists_surjective, hc.exists_surjective, hf.range_comp, range_coe, range_comp
-/
theorem Countable.exists_eq_range {s : Set α} (hc : s.Countable) (hs : s.Nonempty) :
    exists f : Nat -> α, s = range f := by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine ⟨(↑) ∘ f, ?_⟩
  rw [hf.range_comp]; rw [Subtype.range_coe]

/--
theorem `countable_empty` / 定理 `countable_empty`

English:
theorem countable_empty
  statement: (∅ : Set α).Countable
  proof: to_countable _

中文:
定理 countable_empty
  结论: (∅ : 集合 α).可数
  证明: to_countable _
-/
@[simp] theorem countable_empty : (∅ : Set α).Countable := to_countable _

/--
theorem `countable_singleton` / 定理 `countable_singleton`

English:
theorem countable_singleton
  given: (a : α)
  statement: ({a} : Set α).Countable
  proof: to_countable _

中文:
定理 countable_singleton
  条件: (a : α)
  结论: ({a} : 集合 α).可数
  证明: to_countable _
-/
@[simp] theorem countable_singleton (a : α) : ({a} : Set α).Countable := to_countable _

/--
theorem `Countable.image` / 定理 `Countable.image`

English:
theorem Countable.image
  given: {s : Set α} (hs : s.Countable) (f : α -> β)
  statement: (f '' s).Countable
  proof: by
  rw [image_eq_range]
  have := hs.to_subtype
  apply countable_range

中文:
定理 可数.像
  条件: {s : 集合 α} (hs : s.可数) (f : α -> β)
  结论: (f '' s).可数
  证明: by
  rw [image_eq_range]
  have := hs.to_subtype
  apply countable_range

Depends on / 依赖: countable_range, hs.to_subtype, image_eq_range, to_subtype
-/
theorem Countable.image {s : Set α} (hs : s.Countable) (f : α -> β) : (f '' s).Countable := by
  rw [image_eq_range]
  have := hs.to_subtype
  apply countable_range

/--
theorem `Infinite.exists_subset_countable_infinite` / 定理 `Infinite.exists_subset_countable_infinite`

English:
theorem Infinite.exists_subset_countable_infinite
  given: {α : Type u} {s : Set α} (hs : s.Infinite)
  proof: by
  obtain ⟨f, hf⟩ := Infinite.natEmbedding s hs
  refine ⟨range (Subtype.val ∘ f), ?_, ?_, ?_⟩
  · exact fun _ ⟨y, hy⟩ => hy ▸ Subtype.coe_prop (f y)
  · exact countable_range (Subtype.val ∘ f)
· exact infinite_range_of_injective Injective.comp Subtype.val_injective hf

中文:
定理 无限.存在_subset_countable_infinite
  条件: {α : 类型u} {s : 集合 α} (hs : s.无限)
  证明: by
  obtain ⟨f, hf⟩ := Infinite.natEmbedding s hs
  refine ⟨range (Subtype.val ∘ f), ?_, ?_, ?_⟩
  · exact fun _ ⟨y, hy⟩ => hy ▸ Subtype.coe_prop (f y)
  · exact countable_range (Subtype.val ∘ f)
· exact infinite_range_of_injective Injective.comp Subtype.val_injective hf

Depends on / 依赖: Infinite, Infinite.natEmbedding, Injective, Injective.comp, Subtype, Subtype.coe_prop, Subtype.val, Subtype.val_injective, coe_prop, countable_range, infinite_range_of_injective, natEmbedding, val_injective
-/
theorem Infinite.exists_subset_countable_infinite {α : Type u} {s : Set α} (hs : s.Infinite) :
    exists t subseteq s, t.Countable ∧ t.Infinite := by
  obtain ⟨f, hf⟩ := Infinite.natEmbedding s hs
  refine ⟨range (Subtype.val ∘ f), ?_, ?_, ?_⟩
  · exact fun _ ⟨y, hy⟩ => hy ▸ Subtype.coe_prop (f y)
  · exact countable_range (Subtype.val ∘ f)
· exact infinite_range_of_injective Injective.comp Subtype.val_injective hf

/--
theorem `MapsTo.countable_of_injOn` / 定理 `MapsTo.countable_of_injOn`

English:
theorem MapsTo.countable_of_injOn
  statement: {s : Set α} {t : Set β} {f : α -> β} (hf : MapsTo f s t)
  proof: have := ht.to_subtype
  have : Injective (hf.restrict f s t) := (injOn_iff_injective.1 hf').codRestrict _
  this.countable

中文:
定理 映射到.countable_of_injOn
  结论: {s : 集合 α} {t : 集合 β} {f : α -> β} (hf : 映射到 f s t)
  证明: have := ht.to_subtype
  have : Injective (hf.restrict f s t) := (injOn_iff_injective.1 hf').codRestrict _
  this.countable

Depends on / 依赖: Injective, codRestrict, countable, hf.restrict, ht.to_subtype, injOn_iff_injective, restrict, this.countable, to_subtype
-/
theorem MapsTo.countable_of_injOn {s : Set α} {t : Set β} {f : α -> β} (hf : MapsTo f s t)
    (hf' : InjOn f s) (ht : t.Countable) : s.Countable :=
  have := ht.to_subtype
  have : Injective (hf.restrict f s t) := (injOn_iff_injective.1 hf').codRestrict _
  this.countable

/--
theorem `Countable.preimage_of_injOn` / 定理 `Countable.preimage_of_injOn`

English:
theorem Countable.preimage_of_injOn
  statement: {s : Set β} (hs : s.Countable) {f : α -> β}
  proof: (mapsTo_preimage f s).countable_of_injOn hf hs

中文:
定理 可数.preimage_of_injOn
  结论: {s : 集合 β} (hs : s.可数) {f : α -> β}
  证明: (mapsTo_preimage f s).countable_of_injOn hf hs

Depends on / 依赖: countable_of_injOn, mapsTo_preimage
-/
theorem Countable.preimage_of_injOn {s : Set β} (hs : s.Countable) {f : α -> β}
    (hf : InjOn f (f ⁻¹' s)) : (f ⁻¹' s).Countable :=
  (mapsTo_preimage f s).countable_of_injOn hf hs

/--
theorem `Countable.preimage` / 定理 `Countable.preimage`

English:
theorem Countable.preimage
  given: {s : Set β} (hs : s.Countable) {f : α -> β} (hf : Injective f)
  proof: hs.preimage_of_injOn hf.injOn

中文:
定理 可数.原像
  条件: {s : 集合 β} (hs : s.可数) {f : α -> β} (hf : 单射 f)
  证明: hs.preimage_of_injOn hf.injOn
-/
protected theorem Countable.preimage {s : Set β} (hs : s.Countable) {f : α -> β} (hf : Injective f) :
    (f ⁻¹' s).Countable :=
  hs.preimage_of_injOn hf.injOn

/--
theorem `exists_seq_iSup_eq_top_iff_countable` / 定理 `exists_seq_iSup_eq_top_iff_countable`

English:
theorem exists_seq_iSup_eq_top_iff_countable
  given: [CompleteLattice α] {p : α -> Prop} (h : exists x, p x)
  proof: by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine ⟨range s, countable_range s, forall_mem_range.2 hps, ?_⟩
    rwa [sSup_range]
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [sSup_empty] at hS
      have := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun _ => x, fun _ => hx, Subsingleton.elim _ _⟩
    · rcases (Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine ⟨fun n => s n, fun n => hps _ (s n).coe_prop, ?_⟩
      rwa [hs.iSup_comp, ← sSup_eq_iSup']

中文:
定理 存在_seq_iSup_eq_top_iff_countable
  条件: [完备格 α] {p : α -> 命题} (h : 存在 x, p x)
  证明: by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine ⟨range s, countable_range s, forall_mem_range.2 hps, ?_⟩
    rwa [sSup_range]
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [sSup_empty] at hS
      have := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun _ => x, fun _ => hx, Subsingleton.elim _ _⟩
    · rcases (Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine ⟨fun n => s n, fun n => hps _ (s n).coe_prop, ?_⟩
      rwa [hs.iSup_comp, ← sSup_eq_iSup']

Depends on / 依赖: Set.countable_iff_exists_surjective, Subsingleton, Subsingleton.elim, coe_prop, countable_iff_exists_surjective, countable_range, eq_empty_or_nonempty, forall_mem_range, hs.iSup_comp, iSup_comp, sSup_empty, sSup_eq_iSup, sSup_range, subsingleton_of_bot_eq_top
-/
theorem exists_seq_iSup_eq_top_iff_countable [CompleteLattice α] {p : α -> Prop} (h : exists x, p x) :
    (exists s : Nat -> α, (forall n, p (s n)) ∧ ⨆ n, s n = ⊤) ↔
      exists S : Set α, S.Countable ∧ (forall s in S, p s) ∧ sSup S = ⊤ := by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine ⟨range s, countable_range s, forall_mem_range.2 hps, ?_⟩
    rwa [sSup_range]
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [sSup_empty] at hS
      have := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun _ => x, fun _ => hx, Subsingleton.elim _ _⟩
    · rcases (Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine ⟨fun n => s n, fun n => hps _ (s n).coe_prop, ?_⟩
      rwa [hs.iSup_comp, ← sSup_eq_iSup']

/--
theorem `exists_seq_cover_iff_countable` / 定理 `exists_seq_cover_iff_countable`

English:
theorem exists_seq_cover_iff_countable
  given: {p : Set α -> Prop} (h : exists s, p s)
  proof: exists_seq_iSup_eq_top_iff_countable h

中文:
定理 存在_seq_cover_iff_countable
  条件: {p : 集合 α -> 命题} (h : 存在 s, p s)
  证明: exists_seq_iSup_eq_top_iff_countable h

Depends on / 依赖: exists_seq_iSup_eq_top_iff_countable
-/
theorem exists_seq_cover_iff_countable {p : Set α -> Prop} (h : exists s, p s) :
    (exists s : Nat -> Set α, (forall n, p (s n)) ∧ ⋃ n, s n = univ) ↔
      exists S : Set (Set α), S.Countable ∧ (forall s in S, p s) ∧ ⋃₀ S = univ :=
  exists_seq_iSup_eq_top_iff_countable h

/--
theorem `countable_of_injective_of_countable_image` / 定理 `countable_of_injective_of_countable_image`

English:
theorem countable_of_injective_of_countable_image
  statement: {s : Set α} {f : α -> β} (hf : InjOn f s)
  proof: (mapsTo_image _ _).countable_of_injOn hf hs

中文:
定理 countable_of_injective_of_countable_image
  结论: {s : 集合 α} {f : α -> β} (hf : 单射限制 f s)
  证明: (mapsTo_image _ _).countable_of_injOn hf hs

Depends on / 依赖: countable_of_injOn, mapsTo_image
-/
theorem countable_of_injective_of_countable_image {s : Set α} {f : α -> β} (hf : InjOn f s)
    (hs : (f '' s).Countable) : s.Countable :=
  (mapsTo_image _ _).countable_of_injOn hf hs

/--
theorem `countable_iUnion` / 定理 `countable_iUnion`

English:
theorem countable_iUnion
  given: {t : ι -> Set α} [Countable ι] (ht : forall i, (t i).Countable)
  proof: by
  have := fun i => (ht i).to_subtype
  rw [iUnion_eq_range_psigma]
  apply countable_range

@[simp]

中文:
定理 countable_iUnion
  条件: {t : ι -> 集合 α} [可数 ι] (ht : 对任意 i, (t i).可数)
  证明: by
  have := fun i => (ht i).to_subtype
  rw [iUnion_eq_range_psigma]
  apply countable_range

@[simp]

Depends on / 依赖: countable_range, iUnion_eq_range_psigma, to_subtype
-/
theorem countable_iUnion {t : ι -> Set α} [Countable ι] (ht : forall i, (t i).Countable) :
    (⋃ i, t i).Countable := by
  have := fun i => (ht i).to_subtype
  rw [iUnion_eq_range_psigma]
  apply countable_range

@[simp]
/--
theorem `countable_iUnion_iff` / 定理 `countable_iUnion_iff`

English:
theorem countable_iUnion_iff
  given: [Countable ι] {t : ι -> Set α}
  proof: ⟨fun h _ => h.mono subset_iUnion _ _, countable_iUnion⟩

中文:
定理 countable_iUnion_iff
  条件: [可数 ι] {t : ι -> 集合 α}
  证明: ⟨fun h _ => h.mono subset_iUnion _ _, countable_iUnion⟩

Depends on / 依赖: countable_iUnion, h.mono, subset_iUnion
-/
theorem countable_iUnion_iff [Countable ι] {t : ι -> Set α} :
    (⋃ i, t i).Countable ↔ forall i, (t i).Countable :=
⟨fun h _ => h.mono subset_iUnion _ _, countable_iUnion⟩

/--
theorem `Countable.biUnion_iff` / 定理 `Countable.biUnion_iff`

English:
theorem Countable.biUnion_iff
  given: {s : Set α} {t : forall a in s, Set β} (hs : s.Countable)
  proof: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [countable_iUnion_iff]; rw [SetCoe.forall']

中文:
定理 可数.biUnion_iff
  条件: {s : 集合 α} {t : 对任意 a in s, 集合 β} (hs : s.可数)
  证明: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [countable_iUnion_iff]; rw [SetCoe.forall']

Depends on / 依赖: SetCoe, SetCoe.forall, biUnion_eq_iUnion, countable_iUnion_iff, hs.to_subtype, to_subtype
-/
theorem Countable.biUnion_iff {s : Set α} {t : forall a in s, Set β} (hs : s.Countable) :
    (⋃ a in s, t a ‹_›).Countable ↔ forall a (ha : a in s), (t a ha).Countable := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [countable_iUnion_iff]; rw [SetCoe.forall']

/--
theorem `Countable.sUnion_iff` / 定理 `Countable.sUnion_iff`

English:
theorem Countable.sUnion_iff
  given: {s : Set (Set α)} (hs : s.Countable)
  proof: by rw [sUnion_eq_biUnion, hs.biUnion_iff]

alias ⟨_, Countable.biUnion⟩ := Countable.biUnion_iff

alias ⟨_, Countable.sUnion⟩ := Countable.sUnion_iff

@[simp]

中文:
定理 可数.sUnion_iff
  条件: {s : 集合 (集合 α)} (hs : s.可数)
  证明: by rw [sUnion_eq_biUnion, hs.biUnion_iff]

alias ⟨_, Countable.biUnion⟩ := Countable.biUnion_iff

alias ⟨_, Countable.sUnion⟩ := Countable.sUnion_iff

@[simp]

Depends on / 依赖: biUnion_iff, hs.biUnion_iff, sUnion_eq_biUnion
-/
theorem Countable.sUnion_iff {s : Set (Set α)} (hs : s.Countable) :
    (⋃₀ s).Countable ↔ forall a in s, a.Countable := by rw [sUnion_eq_biUnion, hs.biUnion_iff]

alias ⟨_, Countable.biUnion⟩ := Countable.biUnion_iff

alias ⟨_, Countable.sUnion⟩ := Countable.sUnion_iff

@[simp]
/--
theorem `countable_union` / 定理 `countable_union`

English:
theorem countable_union
  given: {s t : Set α}
  statement: (s union t).Countable ↔ s.Countable ∧ t.Countable
  proof: by
  simp [union_eq_iUnion, and_comm]

中文:
定理 countable_union
  条件: {s t : 集合 α}
  结论: (s union t).可数 ↔ s.可数 ∧ t.可数
  证明: by
  simp [union_eq_iUnion, and_comm]

Depends on / 依赖: and_comm, union_eq_iUnion
-/
theorem countable_union {s t : Set α} : (s union t).Countable ↔ s.Countable ∧ t.Countable := by
  simp [union_eq_iUnion, and_comm]

/--
theorem `Countable.union` / 定理 `Countable.union`

English:
theorem Countable.union
  given: {s t : Set α} (hs : s.Countable) (ht : t.Countable)
  statement: (s union t).Countable
  proof: countable_union.2 ⟨hs, ht⟩

中文:
定理 可数.union
  条件: {s t : 集合 α} (hs : s.可数) (ht : t.可数)
  结论: (s union t).可数
  证明: countable_union.2 ⟨hs, ht⟩

Depends on / 依赖: countable_union
-/
theorem Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) : (s union t).Countable :=
  countable_union.2 ⟨hs, ht⟩

/--
theorem `Countable.of_sdiff` / 定理 `Countable.of_sdiff`

English:
theorem Countable.of_sdiff
  given: {s t : Set α} (h : (s \ t).Countable) (ht : t.Countable)
  statement: s.Countable
  proof: (h.union ht).mono (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias Countable.of_diff := Countable.of_sdiff

@[simp]

中文:
定理 可数.of_sdiff
  条件: {s t : 集合 α} (h : (s \ t).可数) (ht : t.可数)
  结论: s.可数
  证明: (h.union ht).mono (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias Countable.of_diff := Countable.of_sdiff

@[simp]

Depends on / 依赖: h.union, subset_sdiff_union
-/
theorem Countable.of_sdiff {s t : Set α} (h : (s \ t).Countable) (ht : t.Countable) : s.Countable :=
  (h.union ht).mono (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias Countable.of_diff := Countable.of_sdiff

@[simp]
/--
theorem `countable_insert` / 定理 `countable_insert`

English:
theorem countable_insert
  given: {s : Set α} {a : α}
  statement: (insert a s).Countable ↔ s.Countable
  proof: by
  simp only [insert_eq, countable_union, countable_singleton, true_and]

中文:
定理 countable_insert
  条件: {s : 集合 α} {a : α}
  结论: (insert a s).可数 ↔ s.可数
  证明: by
  simp only [insert_eq, countable_union, countable_singleton, true_and]

Depends on / 依赖: countable_singleton, countable_union, insert_eq, true_and
-/
theorem countable_insert {s : Set α} {a : α} : (insert a s).Countable ↔ s.Countable := by
  simp only [insert_eq, countable_union, countable_singleton, true_and]

/--
theorem `Countable.insert` / 定理 `Countable.insert`

English:
theorem Countable.insert
  given: {s : Set α} (a : α) (h : s.Countable)
  statement: (insert a s).Countable
  proof: countable_insert.2 h

中文:
定理 可数.insert
  条件: {s : 集合 α} (a : α) (h : s.可数)
  结论: (insert a s).可数
  证明: countable_insert.2 h
-/
protected theorem Countable.insert {s : Set α} (a : α) (h : s.Countable) : (insert a s).Countable :=
  countable_insert.2 h

/--
theorem `Finite.countable` / 定理 `Finite.countable`

English:
theorem Finite.countable
  given: {s : Set α} (hs : s.Finite)
  statement: s.Countable
  proof: have := hs.to_subtype; s.to_countable

@[nontriviality]

中文:
定理 有限.countable
  条件: {s : 集合 α} (hs : s.有限)
  结论: s.可数
  证明: have := hs.to_subtype; s.to_countable

@[nontriviality]

Depends on / 依赖: hs.to_subtype, s.to_countable, to_countable, to_subtype
-/
theorem Finite.countable {s : Set α} (hs : s.Finite) : s.Countable :=
  have := hs.to_subtype; s.to_countable

@[nontriviality]
/--
theorem `Countable.of_subsingleton` / 定理 `Countable.of_subsingleton`

English:
theorem Countable.of_subsingleton
  given: [Subsingleton α] (s : Set α)
  statement: s.Countable
  proof: (Finite.of_subsingleton s).countable

中文:
定理 可数.of_subsingleton
  条件: [子单例 α] (s : 集合 α)
  结论: s.可数
  证明: (Finite.of_subsingleton s).countable

Depends on / 依赖: Finite, Finite.of_subsingleton, countable, of_subsingleton
-/
theorem Countable.of_subsingleton [Subsingleton α] (s : Set α) : s.Countable :=
  (Finite.of_subsingleton s).countable

/--
theorem `Subsingleton.countable` / 定理 `Subsingleton.countable`

English:
theorem Subsingleton.countable
  given: {s : Set α} (hs : s.Subsingleton)
  statement: s.Countable
  proof: hs.finite.countable

中文:
定理 子单例.countable
  条件: {s : 集合 α} (hs : s.子单例)
  结论: s.可数
  证明: hs.finite.countable

Depends on / 依赖: countable, finite, hs.finite.countable
-/
theorem Subsingleton.countable {s : Set α} (hs : s.Subsingleton) : s.Countable :=
  hs.finite.countable

/--
theorem `countable_isTop` / 定理 `countable_isTop`

English:
theorem countable_isTop
  given: (α : Type*) [PartialOrder α]
  statement: { x : α | IsTop x }.Countable
  proof: (finite_isTop α).countable

中文:
定理 countable_isTop
  条件: (α : 类型) [偏序 α]
  结论: { x : α | IsTop x }.可数
  证明: (finite_isTop α).countable

Depends on / 依赖: countable, finite_isTop
-/
theorem countable_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Countable :=
  (finite_isTop α).countable

/--
theorem `countable_isBot` / 定理 `countable_isBot`

English:
theorem countable_isBot
  given: (α : Type*) [PartialOrder α]
  statement: { x : α | IsBot x }.Countable
  proof: (finite_isBot α).countable

中文:
定理 countable_isBot
  条件: (α : 类型) [偏序 α]
  结论: { x : α | IsBot x }.可数
  证明: (finite_isBot α).countable

Depends on / 依赖: countable, finite_isBot
-/
theorem countable_isBot (α : Type*) [PartialOrder α] : { x : α | IsBot x }.Countable :=
  (finite_isBot α).countable

/--
theorem `countable_ofPred_finite_subset` / 定理 `countable_ofPred_finite_subset`

English:
theorem countable_ofPred_finite_subset
  given: {s : Set α} (hs : s.Countable)
  proof: by
  have := hs.to_subtype
  refine (countable_range fun t : Finset s => Subtype.val '' (t : Set s)).mono ?_
  rintro t ⟨ht, hts⟩
  lift t to Set s using hts
  lift t to Finset s using ht.of_finite_image Subtype.val_injective.injOn
  exact mem_range_self _

@[deprecated (since := "2026-07-09")]
alias countable_setOf_finite_subset := countable_ofPred_finite_subset

中文:
定理 countable_ofPred_finite_subset
  条件: {s : 集合 α} (hs : s.可数)
  证明: by
  have := hs.to_subtype
  refine (countable_range fun t : Finset s => Subtype.val '' (t : Set s)).mono ?_
  rintro t ⟨ht, hts⟩
  lift t to Set s using hts
  lift t to Finset s using ht.of_finite_image Subtype.val_injective.injOn
  exact mem_range_self _

@[deprecated (since := "2026-07-09")]
alias countable_setOf_finite_subset := countable_ofPred_finite_subset

Depends on / 依赖: Finset, Subtype, Subtype.val, Subtype.val_injective.injOn, countable_range, hs.to_subtype, ht.of_finite_image, mem_range_self, of_finite_image, to_subtype, val_injective
-/
theorem countable_ofPred_finite_subset {s : Set α} (hs : s.Countable) :
    { t | Set.Finite t ∧ t subseteq s }.Countable := by
  have := hs.to_subtype
  refine (countable_range fun t : Finset s => Subtype.val '' (t : Set s)).mono ?_
  rintro t ⟨ht, hts⟩
  lift t to Set s using hts
  lift t to Finset s using ht.of_finite_image Subtype.val_injective.injOn
  exact mem_range_self _

@[deprecated (since := "2026-07-09")]
alias countable_setOf_finite_subset := countable_ofPred_finite_subset

/--
theorem `Countable.ofPred_finite` / 定理 `Countable.ofPred_finite`

English:
theorem Countable.ofPred_finite
  given: [Countable α]
  statement: {s : Set α | s.Finite}.Countable
  proof: by
  simpa using countable_ofPred_finite_subset countable_univ

@[deprecated (since := "2026-07-09")] alias Countable.setOf_finite := Countable.ofPred_finite

中文:
定理 可数.ofPred_finite
  条件: [可数 α]
  结论: {s : 集合 α | s.有限}.可数
  证明: by
  simpa using countable_ofPred_finite_subset countable_univ

@[deprecated (since := "2026-07-09")] alias Countable.setOf_finite := Countable.ofPred_finite

Depends on / 依赖: countable_ofPred_finite_subset, countable_univ
-/
theorem Countable.ofPred_finite [Countable α] : {s : Set α | s.Finite}.Countable := by
  simpa using countable_ofPred_finite_subset countable_univ

@[deprecated (since := "2026-07-09")] alias Countable.setOf_finite := Countable.ofPred_finite

/--
theorem `Countable.of_preimage_singleton` / 定理 `Countable.of_preimage_singleton`

English:
theorem Countable.of_preimage_singleton
  statement: {f : α -> β} [Countable β]
  proof: by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion h]

中文:
定理 可数.of_preimage_singleton
  结论: {f : α -> β} [可数 β]
  证明: by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion h]

Depends on / 依赖: Set.countable_iUnion, Set.countable_univ_iff, Set.iUnion_of_singleton, Set.preimage_iUnion, Set.preimage_univ, countable_iUnion, countable_univ_iff, iUnion_of_singleton, preimage_iUnion, preimage_univ, simp_rw
-/
theorem Countable.of_preimage_singleton {f : α -> β} [Countable β]
    (h : forall (b : β), (f ⁻¹' {b}).Countable) : Countable α := by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion h]

/--
theorem `countable_univ_pi` / 定理 `countable_univ_pi`

English:
theorem countable_univ_pi
  statement: {π : α -> Type*} [Finite α] {s : forall a, Set (π a)}
  proof: have := fun a => (hs a).to_subtype; .of_equiv _ (Equiv.Set.univPi s).symm

中文:
定理 countable_univ_pi
  结论: {π : α -> 类型} [有限 α] {s : 对任意 a, 集合 (π a)}
  证明: have := fun a => (hs a).to_subtype; .of_equiv _ (Equiv.Set.univPi s).symm

Depends on / 依赖: Equiv.Set.univPi, of_equiv, to_subtype, univPi
-/
theorem countable_univ_pi {π : α -> Type*} [Finite α] {s : forall a, Set (π a)}
    (hs : forall a, (s a).Countable) : (pi univ s).Countable :=
  have := fun a => (hs a).to_subtype; .of_equiv _ (Equiv.Set.univPi s).symm

/--
theorem `countable_pi` / 定理 `countable_pi`

English:
theorem countable_pi
  given: {π : α -> Type*} [Finite α] {s : forall a, Set (π a)} (hs : forall a, (s a).Countable)
  proof: by
  simpa only [← mem_univ_pi] using! countable_univ_pi hs

中文:
定理 countable_pi
  条件: {π : α -> 类型} [有限 α] {s : 对任意 a, 集合 (π a)} (hs : 对任意 a, (s a).可数)
  证明: by
  simpa only [← mem_univ_pi] using! countable_univ_pi hs

Depends on / 依赖: countable_univ_pi, mem_univ_pi
-/
theorem countable_pi {π : α -> Type*} [Finite α] {s : forall a, Set (π a)} (hs : forall a, (s a).Countable) :
    { f : forall a, π a | forall a, f a in s a }.Countable := by
  simpa only [← mem_univ_pi] using! countable_univ_pi hs

/--
theorem `Countable.prod` / 定理 `Countable.prod`

English:
theorem Countable.prod
  given: {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
  proof: have := hs.to_subtype; have := ht.to_subtype; .of_equiv _ (Equiv.Set.prod _ _).symm

中文:
定理 可数.乘积
  条件: {s : 集合 α} {t : 集合 β} (hs : s.可数) (ht : t.可数)
  证明: have := hs.to_subtype; have := ht.to_subtype; .of_equiv _ (Equiv.Set.prod _ _).symm
-/
protected theorem Countable.prod {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable) :
    Set.Countable (s ×ˢ t) :=
have := hs.to_subtype; have := ht.to_subtype; .of_equiv _ (Equiv.Set.prod _ _).symm

/--
theorem `Countable.image2` / 定理 `Countable.image2`

English:
theorem Countable.image2
  statement: {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
  proof: by
  rw [← image_prod]
  exact (hs.prod ht).image _

中文:
定理 可数.image2
  结论: {s : 集合 α} {t : 集合 β} (hs : s.可数) (ht : t.可数)
  证明: by
  rw [← image_prod]
  exact (hs.prod ht).image _

Depends on / 依赖: hs.prod, image_prod
-/
theorem Countable.image2 {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
    (f : α -> β -> γ) : (image2 f s t).Countable := by
  rw [← image_prod]
  exact (hs.prod ht).image _

/--
theorem `countable_ofPred_nonempty_of_disjoint` / 定理 `countable_ofPred_nonempty_of_disjoint`

English:
theorem countable_ofPred_nonempty_of_disjoint
  statement: {f : β -> Set α}
  proof: by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : forall t : {t // (f t).Nonempty}, exists x : s, x.1 in f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t inter f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF ⟨t, _⟩, ?_⟩
      rw [htt']
      exact hF ⟨t', _⟩
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

@[deprecated (since := "2026-07-09")]
alias countable_setOf_nonempty_of_disjoint := countable_ofPred_nonempty_of_disjoint

中文:
定理 countable_ofPred_nonempty_of_disjoint
  结论: {f : β -> 集合 α}
  证明: by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : forall t : {t // (f t).Nonempty}, exists x : s, x.1 in f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t inter f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF ⟨t, _⟩, ?_⟩
      rw [htt']
      exact hF ⟨t', _⟩
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

@[deprecated (since := "2026-07-09")]
alias countable_setOf_nonempty_of_disjoint := countable_ofPred_nonempty_of_disjoint

Depends on / 依赖: Injective, Injective.countable, Nonempty, Set.countable_coe_iff, Subtype, Subtype.mk.injEq, countable, countable_coe_iff, not_disjoint_iff_nonempty_inter
-/
theorem countable_ofPred_nonempty_of_disjoint {f : β -> Set α}
    (hf : Pairwise (Disjoint on f)) {s : Set α} (h'f : forall t, f t subseteq s) (hs : s.Countable) :
    Set.Countable {t | (f t).Nonempty} := by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : forall t : {t // (f t).Nonempty}, exists x : s, x.1 in f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t inter f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF ⟨t, _⟩, ?_⟩
      rw [htt']
      exact hF ⟨t', _⟩
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

@[deprecated (since := "2026-07-09")]
alias countable_setOf_nonempty_of_disjoint := countable_ofPred_nonempty_of_disjoint

end Set

/--
theorem `Finset.countable_toSet` / 定理 `Finset.countable_toSet`

English:
theorem Finset.countable_toSet
  given: (s : Finset α)
  statement: Set.Countable (↑s : Set α)
  proof: s.finite_toSet.countable

中文:
定理 有限集.countable_toSet
  条件: (s : 有限集 α)
  结论: 集合.可数 (↑s : 集合 α)
  证明: s.finite_toSet.countable

Depends on / 依赖: countable, finite_toSet, s.finite_toSet.countable
-/
theorem Finset.countable_toSet (s : Finset α) : Set.Countable (↑s : Set α) :=
  s.finite_toSet.countable
