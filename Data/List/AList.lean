/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
module

public import Mathlib.Data.List.Sigma

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `Sigma`: The elements of the list are of type `Sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `AList` structure. This file defines this structure and
provides ways to access, modify, and combine `AList`s.

* `AList.keys` returns a list of keys of the alist.
* `AList.membership` returns membership in the set of keys.
* `AList.erase` removes a certain key.
* `AList.insert` adds a key-value mapping to the list.
* `AList.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/

@[expose] public section


universe u v w

open List

variable {α : Type u} {β : α -> Type v}

/--
Definition of `AList` / `AList` 的定义

English:
structure AList
  parameters: (β : α -> Type v)
  axioms and operations (2):
    - entries : List (Sigma β)
    - nodupKeys : entries.NodupKeys

中文:
结构 AList
  参数: (β : α -> 类型v)
  公理与运算 (2 个):
    - entries : List (Sigma β)
    - nodupKeys : entries.NodupKeys
-/
structure AList (β : α -> Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/--
Definition of `List.toAList` / `List.toAList` 的定义

English:
definition List.toAList
  signature: [DecidableEq α] {β : α -> Type v} (l : List (Sigma β))
  body: _
  nodupKeys := nodupKeys_dedupKeys l

中文:
定义 List.toAList
  签名: [DecidableEq α] {β : α -> 类型v} (l : List (Sigma β))
  定义体: _
  nodupKeys := nodupKeys_dedupKeys l
-/
def List.toAList [DecidableEq α] {β : α -> Type v} (l : List (Sigma β)) : AList β where
  entries := _
  nodupKeys := nodupKeys_dedupKeys l

namespace AList

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall {s t : AList β}, s.entries = t.entries -> s = t

中文:
定理 ext
  结论: 对任意 {s t : AList β}, s.entries = t.entries -> s = t
-/
theorem ext : forall {s t : AList β}, s.entries = t.entries -> s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [forall a, DecidableEq (β a)] : DecidableEq (AList β)
  body: fun xs ys => by
  rw [AList.ext_iff]; infer_instance

中文:
实例 [DecidableEq
  签名: α] [对任意 a, DecidableEq (β a)] : DecidableEq (AList β)
  定义体: fun xs ys => by
  rw [AList.ext_iff]; infer_instance

Depends on / 依赖: AList.ext_iff, ext_iff, infer_instance
-/
instance [DecidableEq α] [forall a, DecidableEq (β a)] : DecidableEq (AList β) := fun xs ys => by
  rw [AList.ext_iff]; infer_instance

/-! ### keys -/


/--
Definition of `keys` / `keys` 的定义

English:
definition keys
  signature: (s : AList β)
  body: s.entries.keys

中文:
定义 keys
  签名: (s : AList β)
  定义体: s.entries.keys

Depends on / 依赖: entries, s.entries.keys
-/
def keys (s : AList β) : List α :=
  s.entries.keys

/--
theorem `keys_nodup` / 定理 `keys_nodup`

English:
theorem keys_nodup
  given: (s : AList β)
  statement: s.keys.Nodup
  proof: s.nodupKeys

@[simp]

中文:
定理 keys_nodup
  条件: (s : AList β)
  结论: s.keys.Nodup
  证明: s.nodupKeys

@[simp]

Depends on / 依赖: nodupKeys, s.nodupKeys
-/
theorem keys_nodup (s : AList β) : s.keys.Nodup :=
  s.nodupKeys

@[simp]
/--
theorem `keys_mk` / 定理 `keys_mk`

English:
theorem keys_mk
  given: (l : List (Sigma β)) (h)
  statement: (AList.mk l h).keys = l.keys
  proof: rfl

中文:
定理 keys_mk
  条件: (l : List (Sigma β)) (h)
  结论: (AList.mk l h).keys = l.keys
  证明: rfl
-/
theorem keys_mk (l : List (Sigma β)) (h) : (AList.mk l h).keys = l.keys :=
  rfl

/-! ### mem -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (AList β)
  body: ⟨fun s a => a in s.keys⟩

中文:
实例 :
  签名: Membership α (AList β)
  定义体: ⟨fun s a => a in s.keys⟩

Depends on / 依赖: s.keys
-/
instance : Membership α (AList β) :=
  ⟨fun s a => a in s.keys⟩

/--
theorem `mem_keys` / 定理 `mem_keys`

English:
theorem mem_keys
  given: {a : α} {s : AList β}
  statement: a in s ↔ a in s.keys
  proof: Iff.rfl

中文:
定理 mem_keys
  条件: {a : α} {s : AList β}
  结论: a in s ↔ a in s.keys
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys :=
  Iff.rfl

/--
theorem `mem_of_perm` / 定理 `mem_of_perm`

English:
theorem mem_of_perm
  given: {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  statement: a in s₁ ↔ a in s₂
  proof: (p.map Sigma.fst).mem_iff

@[simp]

中文:
定理 mem_of_perm
  条件: {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  结论: a in s₁ ↔ a in s₂
  证明: (p.map Sigma.fst).mem_iff

@[simp]

Depends on / 依赖: Sigma.fst, mem_iff, p.map
-/
theorem mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a in s₁ ↔ a in s₂ :=
  (p.map Sigma.fst).mem_iff

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {l : List (Sigma β)} {h} {x : α}
  statement: x in AList.mk l h ↔ x in l.keys
  proof: .rfl

中文:
定理 mem_mk
  条件: {l : List (Sigma β)} {h} {x : α}
  结论: x in AList.mk l h ↔ x in l.keys
  证明: .rfl
-/
theorem mem_mk {l : List (Sigma β)} {h} {x : α} : x in AList.mk l h ↔ x in l.keys :=
  .rfl

/-! ### empty -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (AList β)
  body: ⟨⟨[], nodupKeys_nil⟩⟩

中文:
实例 :
  签名: EmptyCollection (AList β)
  定义体: ⟨⟨[], nodupKeys_nil⟩⟩

Depends on / 依赖: nodupKeys_nil
-/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], nodupKeys_nil⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AList β)
  body: ⟨∅⟩

@[simp]

中文:
实例 :
  签名: Inhabited (AList β)
  定义体: ⟨∅⟩

@[simp]
-/
instance : Inhabited (AList β) :=
  ⟨∅⟩

@[simp]
/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (a : α)
  statement: a ∉ (∅ : AList β)
  proof: not_mem_nil

@[simp]

中文:
定理 notMem_empty
  条件: (a : α)
  结论: a ∉ (∅ : AList β)
  证明: not_mem_nil

@[simp]

Depends on / 依赖: not_mem_nil
-/
theorem notMem_empty (a : α) : a ∉ (∅ : AList β) :=
  not_mem_nil

@[simp]
/--
theorem `empty_entries` / 定理 `empty_entries`

English:
theorem empty_entries
  statement: (∅ : AList β).entries = []
  proof: rfl

@[simp]

中文:
定理 empty_entries
  结论: (∅ : AList β).entries = []
  证明: rfl

@[simp]
-/
theorem empty_entries : (∅ : AList β).entries = [] :=
  rfl

@[simp]
/--
theorem `keys_empty` / 定理 `keys_empty`

English:
theorem keys_empty
  statement: (∅ : AList β).keys = []
  proof: rfl

中文:
定理 keys_empty
  结论: (∅ : AList β).keys = []
  证明: rfl
-/
theorem keys_empty : (∅ : AList β).keys = [] :=
  rfl

/-! ### singleton -/


/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α) (b : β a)
  body: ⟨[⟨a, b⟩], nodupKeys_singleton _⟩

@[simp]

中文:
定义 singleton
  签名: (a : α) (b : β a)
  定义体: ⟨[⟨a, b⟩], nodupKeys_singleton _⟩

@[simp]

Depends on / 依赖: nodupKeys_singleton
-/
def singleton (a : α) (b : β a) : AList β :=
  ⟨[⟨a, b⟩], nodupKeys_singleton _⟩

@[simp]
/--
theorem `singleton_entries` / 定理 `singleton_entries`

English:
theorem singleton_entries
  given: (a : α) (b : β a)
  statement: (singleton a b).entries = [Sigma.mk a b]
  proof: rfl

@[simp]

中文:
定理 singleton_entries
  条件: (a : α) (b : β a)
  结论: (singleton a b).entries = [Sigma.mk a b]
  证明: rfl

@[simp]
-/
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl

@[simp]
/--
theorem `keys_singleton` / 定理 `keys_singleton`

English:
theorem keys_singleton
  given: (a : α) (b : β a)
  statement: (singleton a b).keys = [a]
  proof: rfl

中文:
定理 keys_singleton
  条件: (a : α) (b : β a)
  结论: (singleton a b).keys = [a]
  证明: rfl
-/
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl

/-! ### lookup -/


section

variable [DecidableEq α]

/--
Definition of `lookup` / `lookup` 的定义

English:
definition lookup
  signature: (a : α) (s : AList β)
  body: s.entries.dlookup a

@[simp]

中文:
定义 lookup
  签名: (a : α) (s : AList β)
  定义体: s.entries.dlookup a

@[simp]

Depends on / 依赖: dlookup, entries, s.entries.dlookup
-/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.dlookup a

@[simp]
/--
theorem `lookup_empty` / 定理 `lookup_empty`

English:
theorem lookup_empty
  given: (a)
  statement: lookup a (∅ : AList β) = none
  proof: rfl

中文:
定理 lookup_empty
  条件: (a)
  结论: lookup a (∅ : AList β) = none
  证明: rfl
-/
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl

/--
theorem `lookup_isSome` / 定理 `lookup_isSome`

English:
theorem lookup_isSome
  given: {a : α} {s : AList β}
  statement: (s.lookup a).isSome ↔ a in s
  proof: dlookup_isSome

中文:
定理 lookup_isSome
  条件: {a : α} {s : AList β}
  结论: (s.lookup a).isSome ↔ a in s
  证明: dlookup_isSome

Depends on / 依赖: dlookup_isSome
-/
theorem lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a in s :=
  dlookup_isSome

/--
theorem `lookup_eq_none` / 定理 `lookup_eq_none`

English:
theorem lookup_eq_none
  given: {a : α} {s : AList β}
  statement: lookup a s = none ↔ a ∉ s
  proof: dlookup_eq_none

中文:
定理 lookup_eq_none
  条件: {a : α} {s : AList β}
  结论: lookup a s = none ↔ a ∉ s
  证明: dlookup_eq_none

Depends on / 依赖: dlookup_eq_none
-/
theorem lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s :=
  dlookup_eq_none

/--
theorem `mem_lookup_iff` / 定理 `mem_lookup_iff`

English:
theorem mem_lookup_iff
  given: {a : α} {b : β a} {s : AList β}
  proof: mem_dlookup_iff s.nodupKeys

中文:
定理 mem_lookup_iff
  条件: {a : α} {b : β a} {s : AList β}
  证明: mem_dlookup_iff s.nodupKeys

Depends on / 依赖: mem_dlookup_iff, nodupKeys, s.nodupKeys
-/
theorem mem_lookup_iff {a : α} {b : β a} {s : AList β} :
    b in lookup a s ↔ Sigma.mk a b in s.entries :=
  mem_dlookup_iff s.nodupKeys

/--
theorem `perm_lookup` / 定理 `perm_lookup`

English:
theorem perm_lookup
  given: {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  proof: perm_dlookup _ s₁.nodupKeys p

中文:
定理 perm_lookup
  条件: {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  证明: perm_dlookup _ s₁.nodupKeys p

Depends on / 依赖: nodupKeys, perm_dlookup
-/
theorem perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.nodupKeys p

instance (a : α) (s : AList β) : Decidable (a in s) :=
  decidable_of_iff _ lookup_isSome

end

/--
theorem `keys_subset_keys_of_entries_subset_entries` / 定理 `keys_subset_keys_of_entries_subset_entries`

English:
theorem keys_subset_keys_of_entries_subset_entries
  proof: by
  intro k hk
  let : DecidableEq α := Classical.decEq α
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  rw [← mem_lookup_iff]; rw [Option.mem_def] at this
  rw [← mem_keys]; rw [← lookup_isSome]; rw [this]
  exact Option.isSome_some

中文:
定理 keys_subset_keys_of_entries_subset_entries
  证明: by
  intro k hk
  let : DecidableEq α := Classical.decEq α
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  rw [← mem_lookup_iff]; rw [Option.mem_def] at this
  rw [← mem_keys]; rw [← lookup_isSome]; rw [this]
  exact Option.isSome_some

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Option.get_mem, Option.isSome_some, Option.mem_def, get_mem, isSome_some, lookup_isSome, mem_def, mem_keys, mem_lookup_iff
-/
theorem keys_subset_keys_of_entries_subset_entries
    {s₁ s₂ : AList β} (h : s₁.entries subseteq s₂.entries) : s₁.keys subseteq s₂.keys := by
  intro k hk
  let : DecidableEq α := Classical.decEq α
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  rw [← mem_lookup_iff]; rw [Option.mem_def] at this
  rw [← mem_keys]; rw [← lookup_isSome]; rw [this]
  exact Option.isSome_some

/-! ### replace -/

section
variable [DecidableEq α]

/--
Definition of `replace` / `replace` 的定义

English:
definition replace
  signature: (a : α) (b : β a) (s : AList β)
  body: ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩

@[simp]

中文:
定义 replace
  签名: (a : α) (b : β a) (s : AList β)
  定义体: ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩

@[simp]

Depends on / 依赖: entries, kreplace, kreplace_nodupKeys, nodupKeys, s.entries, s.nodupKeys
-/
def replace (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩

@[simp]
/--
theorem `keys_replace` / 定理 `keys_replace`

English:
theorem keys_replace
  given: (a : α) (b : β a) (s : AList β)
  statement: (replace a b s).keys = s.keys
  proof: keys_kreplace _ _ _

@[simp]

中文:
定理 keys_replace
  条件: (a : α) (b : β a) (s : AList β)
  结论: (replace a b s).keys = s.keys
  证明: keys_kreplace _ _ _

@[simp]

Depends on / 依赖: keys_kreplace
-/
theorem keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _

@[simp]
/--
theorem `mem_replace` / 定理 `mem_replace`

English:
theorem mem_replace
  given: {a a' : α} {b : β a} {s : AList β}
  statement: a' in replace a b s ↔ a' in s
  proof: by
  rw [mem_keys]; rw [keys_replace]; rw [← mem_keys]

中文:
定理 mem_replace
  条件: {a a' : α} {b : β a} {s : AList β}
  结论: a' in replace a b s ↔ a' in s
  证明: by
  rw [mem_keys]; rw [keys_replace]; rw [← mem_keys]

Depends on / 依赖: keys_replace, mem_keys
-/
theorem mem_replace {a a' : α} {b : β a} {s : AList β} : a' in replace a b s ↔ a' in s := by
  rw [mem_keys]; rw [keys_replace]; rw [← mem_keys]

/--
theorem `perm_replace` / 定理 `perm_replace`

English:
theorem perm_replace
  given: {a : α} {b : β a} {s₁ s₂ : AList β}
  proof: Perm.kreplace s₁.nodupKeys

中文:
定理 perm_replace
  条件: {a : α} {b : β a} {s₁ s₂ : AList β}
  证明: Perm.kreplace s₁.nodupKeys

Depends on / 依赖: Perm.kreplace, kreplace, nodupKeys
-/
theorem perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries -> (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.nodupKeys

end

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: {δ : Type w} (f : δ -> forall a, β a -> δ) (d : δ) (m : AList β)
  body: m.entries.foldl (fun r a => f r a.1 a.2) d

中文:
定义 foldl
  签名: {δ : Type w} (f : δ -> 对任意 a, β a -> δ) (d : δ) (m : AList β)
  定义体: m.entries.foldl (fun r a => f r a.1 a.2) d

Depends on / 依赖: entries, m.entries.foldl
-/
def foldl {δ : Type w} (f : δ -> forall a, β a -> δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d

/-! ### erase -/


section

variable [DecidableEq α]

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (a : α) (s : AList β)
  body: ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩

@[simp]

中文:
定义 erase
  签名: (a : α) (s : AList β)
  定义体: ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩

@[simp]

Depends on / 依赖: entries, kerase, nodupKeys, s.entries.kerase, s.nodupKeys.kerase
-/
def erase (a : α) (s : AList β) : AList β :=
  ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩

@[simp]
/--
theorem `keys_erase` / 定理 `keys_erase`

English:
theorem keys_erase
  given: (a : α) (s : AList β)
  statement: (erase a s).keys = s.keys.erase a
  proof: keys_kerase

@[simp]

中文:
定理 keys_erase
  条件: (a : α) (s : AList β)
  结论: (erase a s).keys = s.keys.erase a
  证明: keys_kerase

@[simp]

Depends on / 依赖: keys_kerase
-/
theorem keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase

@[simp]
/--
theorem `mem_erase` / 定理 `mem_erase`

English:
theorem mem_erase
  given: {a a' : α} {s : AList β}
  statement: a' in erase a s ↔ a' != a ∧ a' in s
  proof: by
  rw [mem_keys]; rw [keys_erase]; rw [s.keys_nodup.mem_erase_iff]; rw [← mem_keys]

中文:
定理 mem_erase
  条件: {a a' : α} {s : AList β}
  结论: a' in erase a s ↔ a' != a ∧ a' in s
  证明: by
  rw [mem_keys]; rw [keys_erase]; rw [s.keys_nodup.mem_erase_iff]; rw [← mem_keys]

Depends on / 依赖: keys_erase, keys_nodup, mem_erase_iff, mem_keys, s.keys_nodup.mem_erase_iff
-/
theorem mem_erase {a a' : α} {s : AList β} : a' in erase a s ↔ a' != a ∧ a' in s := by
  rw [mem_keys]; rw [keys_erase]; rw [s.keys_nodup.mem_erase_iff]; rw [← mem_keys]

/--
theorem `perm_erase` / 定理 `perm_erase`

English:
theorem perm_erase
  given: {a : α} {s₁ s₂ : AList β}
  proof: Perm.kerase s₁.nodupKeys

@[simp]

中文:
定理 perm_erase
  条件: {a : α} {s₁ s₂ : AList β}
  证明: Perm.kerase s₁.nodupKeys

@[simp]

Depends on / 依赖: Perm.kerase, kerase, nodupKeys
-/
theorem perm_erase {a : α} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries -> (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.nodupKeys

@[simp]
/--
theorem `lookup_erase` / 定理 `lookup_erase`

English:
theorem lookup_erase
  given: (a) (s : AList β)
  statement: lookup a (erase a s) = none
  proof: dlookup_kerase a s.nodupKeys

@[simp]

中文:
定理 lookup_erase
  条件: (a) (s : AList β)
  结论: lookup a (erase a s) = none
  证明: dlookup_kerase a s.nodupKeys

@[simp]

Depends on / 依赖: dlookup_kerase, nodupKeys, s.nodupKeys
-/
theorem lookup_erase (a) (s : AList β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.nodupKeys

@[simp]
/--
theorem `lookup_erase_ne` / 定理 `lookup_erase_ne`

English:
theorem lookup_erase_ne
  given: {a a'} {s : AList β} (h : a != a')
  statement: lookup a (erase a' s) = lookup a s
  proof: dlookup_kerase_ne h

中文:
定理 lookup_erase_ne
  条件: {a a'} {s : AList β} (h : a != a')
  结论: lookup a (erase a' s) = lookup a s
  证明: dlookup_kerase_ne h

Depends on / 依赖: dlookup_kerase_ne
-/
theorem lookup_erase_ne {a a'} {s : AList β} (h : a != a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h

/--
theorem `erase_erase` / 定理 `erase_erase`

English:
theorem erase_erase
  given: (a a' : α) (s : AList β)
  statement: (s.erase a).erase a' = (s.erase a').erase a
  proof: ext kerase_kerase

中文:
定理 erase_erase
  条件: (a a' : α) (s : AList β)
  结论: (s.erase a).erase a' = (s.erase a').erase a
  证明: ext kerase_kerase

Depends on / 依赖: kerase_kerase
-/
theorem erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a').erase a :=
ext kerase_kerase

/-! ### insert -/


/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (a : α) (b : β a) (s : AList β)
  body: ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩

@[simp]

中文:
定义 insert
  签名: (a : α) (b : β a) (s : AList β)
  定义体: ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩

@[simp]

Depends on / 依赖: entries, kinsert, kinsert_nodupKeys, nodupKeys, s.entries, s.nodupKeys
-/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩

@[simp]
/--
theorem `entries_insert` / 定理 `entries_insert`

English:
theorem entries_insert
  given: {a} {b : β a} {s : AList β}
  proof: rfl

中文:
定理 entries_insert
  条件: {a} {b : β a} {s : AList β}
  证明: rfl
-/
theorem entries_insert {a} {b : β a} {s : AList β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl

/--
theorem `entries_insert_of_notMem` / 定理 `entries_insert_of_notMem`

English:
theorem entries_insert_of_notMem
  given: {a} {b : β a} {s : AList β} (h : a ∉ s)
  proof: by rw [entries_insert, kerase_of_notMem_keys h]

中文:
定理 entries_insert_of_notMem
  条件: {a} {b : β a} {s : AList β} (h : a ∉ s)
  证明: by rw [entries_insert, kerase_of_notMem_keys h]

Depends on / 依赖: entries_insert, kerase_of_notMem_keys
-/
theorem entries_insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [entries_insert, kerase_of_notMem_keys h]

/--
theorem `insert_of_notMem` / 定理 `insert_of_notMem`

English:
theorem insert_of_notMem
  given: {a} {b : β a} {s : AList β} (h : a ∉ s)
  proof: ext entries_insert_of_notMem h

@[simp]

中文:
定理 insert_of_notMem
  条件: {a} {b : β a} {s : AList β} (h : a ∉ s)
  证明: ext entries_insert_of_notMem h

@[simp]

Depends on / 依赖: entries_insert_of_notMem
-/
theorem insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩ :=
ext entries_insert_of_notMem h

@[simp]
/--
theorem `insert_empty` / 定理 `insert_empty`

English:
theorem insert_empty
  given: (a) (b : β a)
  statement: insert a b ∅ = singleton a b
  proof: rfl

@[simp]

中文:
定理 insert_empty
  条件: (a) (b : β a)
  结论: insert a b ∅ = singleton a b
  证明: rfl

@[simp]
-/
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl

@[simp]
/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  given: {a a'} {b' : β a'} (s : AList β)
  statement: a in insert a' b' s ↔ a = a' ∨ a in s
  proof: mem_keys_kinsert

@[simp]

中文:
定理 mem_insert
  条件: {a a'} {b' : β a'} (s : AList β)
  结论: a in insert a' b' s ↔ a = a' ∨ a in s
  证明: mem_keys_kinsert

@[simp]

Depends on / 依赖: mem_keys_kinsert
-/
theorem mem_insert {a a'} {b' : β a'} (s : AList β) : a in insert a' b' s ↔ a = a' ∨ a in s :=
  mem_keys_kinsert

@[simp]
/--
theorem `keys_insert` / 定理 `keys_insert`

English:
theorem keys_insert
  given: {a} {b : β a} (s : AList β)
  statement: (insert a b s).keys = a :: s.keys.erase a
  proof: by
  simp [insert, keys, keys_kerase]

中文:
定理 keys_insert
  条件: {a} {b : β a} (s : AList β)
  结论: (insert a b s).keys = a :: s.keys.erase a
  证明: by
  simp [insert, keys, keys_kerase]

Depends on / 依赖: insert, keys_kerase
-/
theorem keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]

/--
theorem `perm_insert` / 定理 `perm_insert`

English:
theorem perm_insert
  given: {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  proof: by
  simp only [entries_insert]; exact p.kinsert s₁.nodupKeys

@[simp]

中文:
定理 perm_insert
  条件: {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries)
  证明: by
  simp only [entries_insert]; exact p.kinsert s₁.nodupKeys

@[simp]

Depends on / 依赖: entries_insert, kinsert, nodupKeys, p.kinsert
-/
theorem perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [entries_insert]; exact p.kinsert s₁.nodupKeys

@[simp]
/--
theorem `lookup_insert` / 定理 `lookup_insert`

English:
theorem lookup_insert
  given: {a} {b : β a} (s : AList β)
  statement: lookup a (insert a b s) = some b
  proof: by
  simp only [lookup, insert, dlookup_kinsert]

@[simp]

中文:
定理 lookup_insert
  条件: {a} {b : β a} (s : AList β)
  结论: lookup a (insert a b s) = some b
  证明: by
  simp only [lookup, insert, dlookup_kinsert]

@[simp]

Depends on / 依赖: dlookup_kinsert, insert, lookup
-/
theorem lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, dlookup_kinsert]

@[simp]
/--
theorem `lookup_insert_ne` / 定理 `lookup_insert_ne`

English:
theorem lookup_insert_ne
  given: {a a'} {b' : β a'} {s : AList β} (h : a != a')
  proof: dlookup_kinsert_ne h

中文:
定理 lookup_insert_ne
  条件: {a a'} {b' : β a'} {s : AList β} (h : a != a')
  证明: dlookup_kinsert_ne h

Depends on / 依赖: dlookup_kinsert_ne
-/
theorem lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a != a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h

/--
theorem `lookup_insert_eq_none` / 定理 `lookup_insert_eq_none`

English:
theorem lookup_insert_eq_none
  given: {l : AList β} {k k' : α} {v : β k}
  proof: by
  by_cases h : k' = k
  · subst h; simp
  · simp_all [lookup_insert_ne h]

@[simp]

中文:
定理 lookup_insert_eq_none
  条件: {l : AList β} {k k' : α} {v : β k}
  证明: by
  by_cases h : k' = k
  · subst h; simp
  · simp_all [lookup_insert_ne h]

@[simp]
-/
@[simp] theorem lookup_insert_eq_none {l : AList β} {k k' : α} {v : β k} :
    (l.insert k v).lookup k' = none ↔ (k' != k) ∧ l.lookup k' = none := by
  by_cases h : k' = k
  · subst h; simp
  · simp_all [lookup_insert_ne h]

@[simp]
/--
theorem `lookup_to_alist` / 定理 `lookup_to_alist`

English:
theorem lookup_to_alist
  given: {a} (s : List (Sigma β))
  statement: lookup a s.toAList = s.dlookup a
  proof: by
  rw [List.toAList]; rw [lookup]; rw [dlookup_dedupKeys]

@[simp]

中文:
定理 lookup_to_alist
  条件: {a} (s : List (Sigma β))
  结论: lookup a s.toAList = s.dlookup a
  证明: by
  rw [List.toAList]; rw [lookup]; rw [dlookup_dedupKeys]

@[simp]

Depends on / 依赖: List.toAList, dlookup_dedupKeys, lookup, toAList
-/
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAList = s.dlookup a := by
  rw [List.toAList]; rw [lookup]; rw [dlookup_dedupKeys]

@[simp]
/--
theorem `insert_insert` / 定理 `insert_insert`

English:
theorem insert_insert
  given: {a} {b b' : β a} (s : AList β)
  proof: by
  ext : 1; simp only [AList.entries_insert, List.kerase_cons_eq]

中文:
定理 insert_insert
  条件: {a} {b b' : β a} (s : AList β)
  证明: by
  ext : 1; simp only [AList.entries_insert, List.kerase_cons_eq]

Depends on / 依赖: AList.entries_insert, List.kerase_cons_eq, entries_insert, kerase_cons_eq
-/
theorem insert_insert {a} {b b' : β a} (s : AList β) :
    (s.insert a b).insert a b' = s.insert a b' := by
  ext : 1; simp only [AList.entries_insert, List.kerase_cons_eq]

/--
theorem `insert_insert_of_ne` / 定理 `insert_insert_of_ne`

English:
theorem insert_insert_of_ne
  given: {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a != a')
  proof: by
  simp only [entries_insert]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply Perm.swap; exact h; exact h.symm]

@[simp]

中文:
定理 insert_insert_of_ne
  条件: {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a != a')
  证明: by
  simp only [entries_insert]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply Perm.swap; exact h; exact h.symm]

@[simp]

Depends on / 依赖: Perm.swap, entries_insert, h.symm, kerase_comm, kerase_cons_ne
-/
theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a != a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [entries_insert]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply Perm.swap; exact h; exact h.symm]

@[simp]
/--
theorem `insert_singleton_eq` / 定理 `insert_singleton_eq`

English:
theorem insert_singleton_eq
  given: {a : α} {b b' : β a}
  statement: insert a b (singleton a b') = singleton a b
  proof: ext by
    simp only [AList.entries_insert, List.kerase_cons_eq, AList.singleton_entries]

@[simp]

中文:
定理 insert_singleton_eq
  条件: {a : α} {b b' : β a}
  结论: insert a b (singleton a b') = singleton a b
  证明: ext by
    simp only [AList.entries_insert, List.kerase_cons_eq, AList.singleton_entries]

@[simp]

Depends on / 依赖: AList.entries_insert, AList.singleton_entries, List.kerase_cons_eq, entries_insert, kerase_cons_eq, singleton_entries
-/
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
ext by
    simp only [AList.entries_insert, List.kerase_cons_eq, AList.singleton_entries]

@[simp]
/--
theorem `entries_toAList` / 定理 `entries_toAList`

English:
theorem entries_toAList
  given: (xs : List (Sigma β))
  statement: (List.toAList xs).entries = dedupKeys xs
  proof: rfl

中文:
定理 entries_toAList
  条件: (xs : List (Sigma β))
  结论: (List.toAList xs).entries = dedupKeys xs
  证明: rfl
-/
theorem entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupKeys xs :=
  rfl

/--
theorem `toAList_cons` / 定理 `toAList_cons`

English:
theorem toAList_cons
  given: (a : α) (b : β a) (xs : List (Sigma β))
  proof: rfl

中文:
定理 toAList_cons
  条件: (a : α) (b : β a) (xs : List (Sigma β))
  证明: rfl
-/
theorem toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAList (⟨a, b⟩ :: xs) = insert a b xs.toAList :=
  rfl

/--
theorem `mk_cons_eq_insert` / 定理 `mk_cons_eq_insert`

English:
theorem mk_cons_eq_insert
  given: (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys)
  proof: by
  simpa [insert] using (kerase_of_notMem_keys <| notMem_keys_of_nodupKeys_cons h).symm

中文:
定理 mk_cons_eq_insert
  条件: (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys)
  证明: by
  simpa [insert] using (kerase_of_notMem_keys <| notMem_keys_of_nodupKeys_cons h).symm

Depends on / 依赖: insert, kerase_of_notMem_keys, notMem_keys_of_nodupKeys_cons
-/
theorem mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys) :
    (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h⟩ := by
  simpa [insert] using (kerase_of_notMem_keys <| notMem_keys_of_nodupKeys_cons h).symm

/-- Recursion on an `AList`, using `insert`. Use as `induction l`. -/
@[elab_as_elim, induction_eliminator]
/--
Definition of `insertRec` / `insertRec` 的定义

English:
definition insertRec
  signature: {C : AList β -> Sort*} (H0 : C ∅)

中文:
定义 insertRec
  签名: {C : AList β -> Sort*} (H0 : C ∅)
-/
def insertRec {C : AList β -> Sort*} (H0 : C ∅)
    (IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) :
    forall l : AList β, C l
  | ⟨[], _⟩ => H0
  | ⟨c :: l, h⟩ => by
    rw [mk_cons_eq_insert]
    refine IH _ _ _ ?_ (insertRec H0 IH _)
    exact notMem_keys_of_nodupKeys_cons h

-- Test that the `induction` tactic works on `insertRec`.
example (l : AList β) : True := by induction l <;> trivial

@[simp]
/--
theorem `insertRec_empty` / 定理 `insertRec_empty`

English:
theorem insertRec_empty
  statement: {C : AList β -> Sort*} (H0 : C ∅)
  proof: by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insertRec]

中文:
定理 insertRec_empty
  结论: {C : AList β -> Sort*} (H0 : C ∅)
  证明: by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insertRec]

Depends on / 依赖: insertRec
-/
theorem insertRec_empty {C : AList β -> Sort*} (H0 : C ∅)
    (IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) :
    @insertRec α β _ C H0 IH ∅ = H0 := by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insertRec]

/--
theorem `insertRec_insert` / 定理 `insertRec_insert`

English:
theorem insertRec_insert
  statement: {C : AList β -> Sort*} (H0 : C ∅)
  proof: by
  obtain ⟨l, hl⟩ := l
  suffices @insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩ ≍
      IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩) by
    cases c
    apply eq_of_heq
    convert! this <;> rw [insert_of_notMem h]
  rw [insertRec]
  apply cast_heq

中文:
定理 insertRec_insert
  结论: {C : AList β -> Sort*} (H0 : C ∅)
  证明: by
  obtain ⟨l, hl⟩ := l
  suffices @insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩ ≍
      IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩) by
    cases c
    apply eq_of_heq
    convert! this <;> rw [insert_of_notMem h]
  rw [insertRec]
  apply cast_heq

Depends on / 依赖: cast_heq, convert, eq_of_heq, insertRec, insert_of_notMem, nodupKeys_cons
-/
theorem insertRec_insert {C : AList β -> Sort*} (H0 : C ∅)
    (IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) {c : Sigma β}
    {l : AList β} (h : c.1 ∉ l) :
    @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l h (@insertRec α β _ C H0 IH l) := by
  obtain ⟨l, hl⟩ := l
  suffices @insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩ ≍
      IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩) by
    cases c
    apply eq_of_heq
    convert! this <;> rw [insert_of_notMem h]
  rw [insertRec]
  apply cast_heq

/--
theorem `insertRec_insert_mk` / 定理 `insertRec_insert_mk`

English:
theorem insertRec_insert_mk
  statement: {C : AList β -> Sort*} (H0 : C ∅)
  proof: @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h

中文:
定理 insertRec_insert_mk
  结论: {C : AList β -> Sort*} (H0 : C ∅)
  证明: @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h

Depends on / 依赖: insertRec_insert
-/
theorem insertRec_insert_mk {C : AList β -> Sort*} (H0 : C ∅)
    (IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) {a : α} (b : β a)
    {l : AList β} (h : a ∉ l) :
    @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (@insertRec α β _ C H0 IH l) :=
  @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h

/-! ### extract -/


/--
Definition of `extract` / `extract` 的定义

English:
definition extract
  signature: (a : α) (s : AList β)
  body: have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]

中文:
定义 extract
  签名: (a : α) (s : AList β)
  定义体: have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]

Depends on / 依赖: NodupKeys, entries, kerase, kextract, kextract_eq_dlookup_kerase, nodupKeys, s.entries, s.nodupKeys.kerase
-/
def extract (a : α) (s : AList β) : Option (β a) × AList β :=
  have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]
/--
theorem `extract_eq_lookup_erase` / 定理 `extract_eq_lookup_erase`

English:
theorem extract_eq_lookup_erase
  given: (a : α) (s : AList β)
  statement: extract a s = (lookup a s, erase a s)
  proof: by
  simp [extract]; constructor <;> rfl

中文:
定理 extract_eq_lookup_erase
  条件: (a : α) (s : AList β)
  结论: extract a s = (lookup a s, erase a s)
  证明: by
  simp [extract]; constructor <;> rfl

Depends on / 依赖: extract
-/
theorem extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s, erase a s) := by
  simp [extract]; constructor <;> rfl

/-! ### union -/


/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (s₁ s₂ : AList β)
  body: ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩

中文:
定义 union
  签名: (s₁ s₂ : AList β)
  定义体: ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩

Depends on / 依赖: entries, entries.kunion, kunion, nodupKeys, nodupKeys.kunion
-/
def union (s₁ s₂ : AList β) : AList β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union (AList β)
  body: ⟨union⟩

@[simp]

中文:
实例 :
  签名: Union (AList β)
  定义体: ⟨union⟩

@[simp]
-/
instance : Union (AList β) :=
  ⟨union⟩

@[simp]
/--
theorem `union_entries` / 定理 `union_entries`

English:
theorem union_entries
  given: {s₁ s₂ : AList β}
  statement: (s₁ union s₂).entries = kunion s₁.entries s₂.entries
  proof: rfl

@[simp]

中文:
定理 union_entries
  条件: {s₁ s₂ : AList β}
  结论: (s₁ union s₂).entries = kunion s₁.entries s₂.entries
  证明: rfl

@[simp]
-/
theorem union_entries {s₁ s₂ : AList β} : (s₁ union s₂).entries = kunion s₁.entries s₂.entries :=
  rfl

@[simp]
/--
theorem `empty_union` / 定理 `empty_union`

English:
theorem empty_union
  given: {s : AList β}
  statement: (∅ : AList β) union s = s
  proof: ext rfl

@[simp]

中文:
定理 empty_union
  条件: {s : AList β}
  结论: (∅ : AList β) union s = s
  证明: ext rfl

@[simp]
-/
theorem empty_union {s : AList β} : (∅ : AList β) union s = s :=
  ext rfl

@[simp]
/--
theorem `union_empty` / 定理 `union_empty`

English:
theorem union_empty
  given: {s : AList β}
  statement: s union (∅ : AList β) = s
  proof: ext by simp

@[simp]

中文:
定理 union_empty
  条件: {s : AList β}
  结论: s union (∅ : AList β) = s
  证明: ext by simp

@[simp]
-/
theorem union_empty {s : AList β} : s union (∅ : AList β) = s :=
ext by simp

@[simp]
/--
theorem `mem_union` / 定理 `mem_union`

English:
theorem mem_union
  given: {a} {s₁ s₂ : AList β}
  statement: a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
  proof: mem_keys_kunion

中文:
定理 mem_union
  条件: {a} {s₁ s₂ : AList β}
  结论: a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
  证明: mem_keys_kunion

Depends on / 依赖: mem_keys_kunion
-/
theorem mem_union {a} {s₁ s₂ : AList β} : a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂ :=
  mem_keys_kunion

/--
theorem `perm_union` / 定理 `perm_union`

English:
theorem perm_union
  statement: {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
  proof: by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]

中文:
定理 perm_union
  结论: {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
  证明: by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]

Depends on / 依赖: kunion, nodupKeys
-/
theorem perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ union s₃).entries ~ (s₂ union s₄).entries := by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]

/--
theorem `union_erase` / 定理 `union_erase`

English:
theorem union_erase
  given: (a : α) (s₁ s₂ : AList β)
  statement: erase a (s₁ union s₂) = erase a s₁ union erase a s₂
  proof: ext kunion_kerase.symm

@[simp]

中文:
定理 union_erase
  条件: (a : α) (s₁ s₂ : AList β)
  结论: erase a (s₁ union s₂) = erase a s₁ union erase a s₂
  证明: ext kunion_kerase.symm

@[simp]

Depends on / 依赖: kunion_kerase, kunion_kerase.symm
-/
theorem union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ union s₂) = erase a s₁ union erase a s₂ :=
  ext kunion_kerase.symm

@[simp]
/--
theorem `lookup_union_left` / 定理 `lookup_union_left`

English:
theorem lookup_union_left
  given: {a} {s₁ s₂ : AList β}
  statement: a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁
  proof: dlookup_kunion_left

@[simp]

中文:
定理 lookup_union_left
  条件: {a} {s₁ s₂ : AList β}
  结论: a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁
  证明: dlookup_kunion_left

@[simp]

Depends on / 依赖: dlookup_kunion_left
-/
theorem lookup_union_left {a} {s₁ s₂ : AList β} : a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁ :=
  dlookup_kunion_left

@[simp]
/--
theorem `lookup_union_right` / 定理 `lookup_union_right`

English:
theorem lookup_union_right
  given: {a} {s₁ s₂ : AList β}
  statement: a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
  proof: dlookup_kunion_right

中文:
定理 lookup_union_right
  条件: {a} {s₁ s₂ : AList β}
  结论: a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
  证明: dlookup_kunion_right

Depends on / 依赖: dlookup_kunion_right
-/
theorem lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂ :=
  dlookup_kunion_right

-- The corresponding lemma in `simp`-normal form is `lookup_union_eq_some`.
/--
theorem `mem_lookup_union` / 定理 `mem_lookup_union`

English:
theorem mem_lookup_union
  given: {a} {b : β a} {s₁ s₂ : AList β}
  proof: mem_dlookup_kunion

@[simp]

中文:
定理 mem_lookup_union
  条件: {a} {b : β a} {s₁ s₂ : AList β}
  证明: mem_dlookup_kunion

@[simp]

Depends on / 依赖: mem_dlookup_kunion
-/
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} :
    b in lookup a (s₁ union s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂ :=
  mem_dlookup_kunion

@[simp]
/--
theorem `lookup_union_eq_some` / 定理 `lookup_union_eq_some`

English:
theorem lookup_union_eq_some
  given: {a} {b : β a} {s₁ s₂ : AList β}
  proof: mem_dlookup_kunion

中文:
定理 lookup_union_eq_some
  条件: {a} {b : β a} {s₁ s₂ : AList β}
  证明: mem_dlookup_kunion

Depends on / 依赖: mem_dlookup_kunion
-/
theorem lookup_union_eq_some {a} {b : β a} {s₁ s₂ : AList β} :
    lookup a (s₁ union s₂) = some b ↔ lookup a s₁ = some b ∨ a ∉ s₁ ∧ lookup a s₂ = some b :=
  mem_dlookup_kunion

/--
theorem `mem_lookup_union_middle` / 定理 `mem_lookup_union_middle`

English:
theorem mem_lookup_union_middle
  given: {a} {b : β a} {s₁ s₂ s₃ : AList β}
  proof: mem_dlookup_kunion_middle

中文:
定理 mem_lookup_union_middle
  条件: {a} {b : β a} {s₁ s₂ s₃ : AList β}
  证明: mem_dlookup_kunion_middle

Depends on / 依赖: mem_dlookup_kunion_middle
-/
theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} :
    b in lookup a (s₁ union s₃) -> a ∉ s₂ -> b in lookup a (s₁ union s₂ union s₃) :=
  mem_dlookup_kunion_middle

/--
theorem `insert_union` / 定理 `insert_union`

English:
theorem insert_union
  given: {a} {b : β a} {s₁ s₂ : AList β}
  proof: by ext; simp

中文:
定理 insert_union
  条件: {a} {b : β a} {s₁ s₂ : AList β}
  证明: by ext; simp
-/
theorem insert_union {a} {b : β a} {s₁ s₂ : AList β} :
    insert a b (s₁ union s₂) = insert a b s₁ union s₂ := by ext; simp

/--
theorem `union_assoc` / 定理 `union_assoc`

English:
theorem union_assoc
  given: {s₁ s₂ s₃ : AList β}
  statement: (s₁ union s₂ union s₃).entries ~ (s₁ union (s₂ union s₃)).entries
  proof: lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])

中文:
定理 union_assoc
  条件: {s₁ s₂ s₃ : AList β}
  结论: (s₁ union s₂ union s₃).entries ~ (s₁ union (s₂ union s₃)).entries
  证明: lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])

Depends on / 依赖: AList.nodupKeys, and_assoc, and_or_left, lookup_ext, nodupKeys, not_or, or_assoc
-/
theorem union_assoc {s₁ s₂ s₃ : AList β} : (s₁ union s₂ union s₃).entries ~ (s₁ union (s₂ union s₃)).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])

end

/-! ### disjoint -/


/--
Definition of `Disjoint` / `Disjoint` 的定义

English:
definition Disjoint
  signature: (s₁ s₂ : AList β)
  body: forall k in s₁.keys, k ∉ s₂.keys

中文:
定义 Disjoint
  签名: (s₁ s₂ : AList β)
  定义体: forall k in s₁.keys, k ∉ s₂.keys
-/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  forall k in s₁.keys, k ∉ s₂.keys

variable [DecidableEq α]

/--
theorem `union_comm_of_disjoint` / 定理 `union_comm_of_disjoint`

English:
theorem union_comm_of_disjoint
  given: {s₁ s₂ : AList β} (h : Disjoint s₁ s₂)
  proof: lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp only [union_entries, Option.mem_def, dlookup_kunion_eq_some]
      constructor <;> intro h'
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          apply h
          rw [keys]; rw [← List.dlookup

中文:
定理 union_comm_of_disjoint
  条件: {s₁ s₂ : AList β} (h : Disjoint s₁ s₂)
  证明: lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp only [union_entries, Option.mem_def, dlookup_kunion_eq_some]
      constructor <;> intro h'
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          apply h
          rw [keys]; rw [← List.dlookup

Depends on / 依赖: AList.nodupKeys, List.dlookup_isSome, Option.mem_def, dlookup_isSome, dlookup_kunion_eq_some, intros, lookup_ext, mem_def, nodupKeys, union_entries
-/
theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ union s₂).entries ~ (s₂ union s₁).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp only [union_entries, Option.mem_def, dlookup_kunion_eq_some]
      constructor <;> intro h'
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          apply h
          rw [keys]; rw [← List.dlookup_isSome]; rw [h']
          exact rfl
        · left
          rw [h'.2]
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          intro h''
          apply h _ h''
          rw [keys]; rw [← List.dlookup_isSome]; rw [h']
          exact rfl
        · left
          rw [h'.2])

end AList
