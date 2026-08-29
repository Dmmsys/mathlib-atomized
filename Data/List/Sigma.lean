/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Lookmap
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `List (Sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : Sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `List (Sigma β)` behaves like a key-value store.

## Main Definitions

- `List.keys` extracts the list of keys.
- `List.NodupKeys` determines if the store has duplicate keys.
- `List.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `List.kreplace` replaces the first value with a given key by a given value.
- `List.kerase` removes a value.
- `List.kinsert` inserts a value.
- `List.kunion` computes the union of two stores.
- `List.kextract` returns a value with a given key and the rest of the values.
-/

@[expose] public section

universe u u' v v'

namespace List

variable {α : Type u} {α' : Type u'} {β : α -> Type v} {β' : α' -> Type v'} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/


/--
Definition of `keys` / `keys` 的定义

English:
definition keys
  signature: : List (Sigma β) -> List α
  body: map Sigma.fst

@[simp, grind =]

中文:
定义 keys
  签名: : 列表 (依赖和类型 β) -> 列表 α
  定义体: map Sigma.fst

@[simp, grind =]

Depends on / 依赖: Sigma.fst
-/
def keys : List (Sigma β) -> List α :=
  map Sigma.fst

@[simp, grind =]
/--
theorem `keys_nil` / 定理 `keys_nil`

English:
theorem keys_nil
  statement: @keys α β [] = []
  proof: rfl

@[simp, grind =]

中文:
定理 keys_nil
  结论: @keys α β [] = []
  证明: rfl

@[simp, grind =]
-/
theorem keys_nil : @keys α β [] = [] :=
  rfl

@[simp, grind =]
/--
theorem `keys_cons` / 定理 `keys_cons`

English:
theorem keys_cons
  given: {s} {l : List (Sigma β)}
  statement: (s :: l).keys = s.1 :: l.keys
  proof: rfl

@[simp, grind =]

中文:
定理 keys_cons
  条件: {s} {l : 列表 (依赖和类型 β)}
  结论: (s :: l).keys = s.1 :: l.keys
  证明: rfl

@[simp, grind =]
-/
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl

@[simp, grind =]
/--
theorem `keys_append` / 定理 `keys_append`

English:
theorem keys_append
  statement: (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys
  proof: by
  simp [keys]

中文:
定理 keys_append
  结论: (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys
  证明: by
  simp [keys]
-/
theorem keys_append : (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys := by
  simp [keys]

/--
theorem `mem_keys_of_mem` / 定理 `mem_keys_of_mem`

English:
theorem mem_keys_of_mem
  given: {s : Sigma β} {l : List (Sigma β)}
  statement: s in l -> s.1 in l.keys
  proof: mem_map_of_mem

中文:
定理 mem_keys_of_mem
  条件: {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)}
  结论: s in l -> s.1 in l.keys
  证明: mem_map_of_mem

Depends on / 依赖: mem_map_of_mem
-/
theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s in l -> s.1 in l.keys :=
  mem_map_of_mem

/--
theorem `exists_of_mem_keys` / 定理 `exists_of_mem_keys`

English:
theorem exists_of_mem_keys
  given: {a} {l : List (Sigma β)} (h : a in l.keys)
  proof: by
  have := exists_of_mem_map h
  grind

@[grind =]

中文:
定理 存在_of_mem_keys
  条件: {a} {l : 列表 (依赖和类型 β)} (h : a in l.keys)
  证明: by
  have := exists_of_mem_map h
  grind

@[grind =]

Depends on / 依赖: exists_of_mem_map
-/
theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a in l.keys) :
    exists b : β a, Sigma.mk a b in l := by
  have := exists_of_mem_map h
  grind

@[grind =]
/--
theorem `mem_keys` / 定理 `mem_keys`

English:
theorem mem_keys
  given: {a} {l : List (Sigma β)}
  statement: a in l.keys ↔ exists b : β a, Sigma.mk a b in l
  proof: ⟨exists_of_mem_keys, fun ⟨_, h⟩ => mem_keys_of_mem h⟩

中文:
定理 mem_keys
  条件: {a} {l : 列表 (依赖和类型 β)}
  结论: a in l.keys ↔ 存在 b : β a, 依赖和类型.mk a b in l
  证明: ⟨exists_of_mem_keys, fun ⟨_, h⟩ => mem_keys_of_mem h⟩

Depends on / 依赖: exists_of_mem_keys, mem_keys_of_mem
-/
theorem mem_keys {a} {l : List (Sigma β)} : a in l.keys ↔ exists b : β a, Sigma.mk a b in l :=
  ⟨exists_of_mem_keys, fun ⟨_, h⟩ => mem_keys_of_mem h⟩

/--
theorem `notMem_keys` / 定理 `notMem_keys`

English:
theorem notMem_keys
  given: {a} {l : List (Sigma β)}
  statement: a ∉ l.keys ↔ forall b : β a, Sigma.mk a b ∉ l
  proof: by
  grind

中文:
定理 notMem_keys
  条件: {a} {l : 列表 (依赖和类型 β)}
  结论: a ∉ l.keys ↔ 对任意 b : β a, 依赖和类型.mk a b ∉ l
  证明: by
  grind
-/
theorem notMem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ forall b : β a, Sigma.mk a b ∉ l := by
  grind

/--
theorem `ne_key` / 定理 `ne_key`

English:
theorem ne_key
  given: {a} {l : List (Sigma β)}
  statement: a ∉ l.keys ↔ forall s : Sigma β, s in l -> a != s.1
  proof: by
  grind

中文:
定理 ne_key
  条件: {a} {l : 列表 (依赖和类型 β)}
  结论: a ∉ l.keys ↔ 对任意 s : 依赖和类型 β, s in l -> a != s.1
  证明: by
  grind
-/
theorem ne_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ forall s : Sigma β, s in l -> a != s.1 := by
  grind

/-! ### `NodupKeys` -/


/-- Determines whether the store uses a key several times. -/
@[grind]
/--
Definition of `NodupKeys` / `NodupKeys` 的定义

English:
definition NodupKeys
  signature: (l : List (Sigma β))
  body: l.keys.Nodup

中文:
定义 NodupKeys
  签名: (l : 列表 (依赖和类型 β))
  定义体: l.keys.Nodup

Depends on / 依赖: l.keys.Nodup
-/
def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup

/--
theorem `nodupKeys_iff_pairwise` / 定理 `nodupKeys_iff_pairwise`

English:
theorem nodupKeys_iff_pairwise
  given: {l}
  statement: NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 != s'.1) l
  proof: pairwise_map

中文:
定理 nodupKeys_iff_pairwise
  条件: {l}
  结论: NodupKeys l ↔ 两两 (fun s s' : 依赖和类型 β => s.1 != s'.1) l
  证明: pairwise_map

Depends on / 依赖: pairwise_map
-/
theorem nodupKeys_iff_pairwise {l} : NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 != s'.1) l :=
  pairwise_map

/--
theorem `NodupKeys.pairwise_ne` / 定理 `NodupKeys.pairwise_ne`

English:
theorem NodupKeys.pairwise_ne
  given: {l} (h : NodupKeys l)
  proof: nodupKeys_iff_pairwise.1 h

@[simp]

中文:
定理 NodupKeys.pairwise_ne
  条件: {l} (h : NodupKeys l)
  证明: nodupKeys_iff_pairwise.1 h

@[simp]

Depends on / 依赖: nodupKeys_iff_pairwise
-/
theorem NodupKeys.pairwise_ne {l} (h : NodupKeys l) :
    Pairwise (fun s s' : Sigma β => s.1 != s'.1) l :=
  nodupKeys_iff_pairwise.1 h

@[simp]
/--
theorem `nodupKeys_nil` / 定理 `nodupKeys_nil`

English:
theorem nodupKeys_nil
  statement: @NodupKeys α β []
  proof: Pairwise.nil

@[simp]

中文:
定理 nodupKeys_nil
  结论: @NodupKeys α β []
  证明: Pairwise.nil

@[simp]

Depends on / 依赖: Pairwise, Pairwise.nil
-/
theorem nodupKeys_nil : @NodupKeys α β [] :=
  Pairwise.nil

@[simp]
/--
theorem `nodupKeys_cons` / 定理 `nodupKeys_cons`

English:
theorem nodupKeys_cons
  given: {s : Sigma β} {l : List (Sigma β)}
  proof: by simp [keys, NodupKeys]

中文:
定理 nodupKeys_cons
  条件: {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)}
  证明: by simp [keys, NodupKeys]

Depends on / 依赖: NodupKeys
-/
theorem nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
    NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l := by simp [keys, NodupKeys]

/--
theorem `nodupKeys_middle` / 定理 `nodupKeys_middle`

English:
theorem nodupKeys_middle
  given: {s : Sigma β}
  proof: by
  simp_all [NodupKeys, keys, nodup_middle]

中文:
定理 nodupKeys_middle
  条件: {s : 依赖和类型 β}
  证明: by
  simp_all [NodupKeys, keys, nodup_middle]

Depends on / 依赖: NodupKeys, nodup_middle
-/
theorem nodupKeys_middle {s : Sigma β} :
    (l₁ ++ s :: l₂).NodupKeys ↔ (s :: (l₁ ++ l₂)).NodupKeys := by
  simp_all [NodupKeys, keys, nodup_middle]

/--
theorem `notMem_keys_of_nodupKeys_cons` / 定理 `notMem_keys_of_nodupKeys_cons`

English:
theorem notMem_keys_of_nodupKeys_cons
  given: {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l))
  proof: by grind

中文:
定理 notMem_keys_of_nodupKeys_cons
  条件: {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)} (h : NodupKeys (s :: l))
  证明: by grind
-/
theorem notMem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    s.1 ∉ l.keys := by grind

/--
theorem `nodupKeys_of_nodupKeys_cons` / 定理 `nodupKeys_of_nodupKeys_cons`

English:
theorem nodupKeys_of_nodupKeys_cons
  given: {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l))
  proof: (nodupKeys_cons.1 h).2

中文:
定理 nodupKeys_of_nodupKeys_cons
  条件: {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)} (h : NodupKeys (s :: l))
  证明: (nodupKeys_cons.1 h).2

Depends on / 依赖: nodupKeys_cons
-/
theorem nodupKeys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    NodupKeys l :=
  (nodupKeys_cons.1 h).2

/--
theorem `NodupKeys.eq_of_fst_eq` / 定理 `NodupKeys.eq_of_fst_eq`

English:
theorem NodupKeys.eq_of_fst_eq
  statement: {l : List (Sigma β)} (nd : NodupKeys l) {s s' : Sigma β} (h : s in l)
  proof: @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 -> s = s') _
    ⟨fun _ _ H h => (H h.symm).symm⟩ (fun _ _ _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun h h' => (h h').elim) _ h _ h'

中文:
定理 NodupKeys.eq_of_fst_eq
  结论: {l : 列表 (依赖和类型 β)} (nd : NodupKeys l) {s s' : 依赖和类型 β} (h : s in l)
  证明: @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 -> s = s') _
    ⟨fun _ _ H h => (H h.symm).symm⟩ (fun _ _ _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun h h' => (h h').elim) _ h _ h'

Depends on / 依赖: Pairwise, Pairwise.forall_of_forall, forall_of_forall, h.symm, nodupKeys_iff_pairwise
-/
theorem NodupKeys.eq_of_fst_eq {l : List (Sigma β)} (nd : NodupKeys l) {s s' : Sigma β} (h : s in l)
    (h' : s' in l) : s.1 = s'.1 -> s = s' :=
  @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 -> s = s') _
    ⟨fun _ _ H h => (H h.symm).symm⟩ (fun _ _ _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun h h' => (h h').elim) _ h _ h'

/--
theorem `NodupKeys.eq_of_mk_mem` / 定理 `NodupKeys.eq_of_mk_mem`

English:
theorem NodupKeys.eq_of_mk_mem
  statement: {a : α} {b b' : β a} {l : List (Sigma β)} (nd : NodupKeys l)
  proof: by
  grind [NodupKeys.eq_of_fst_eq]

中文:
定理 NodupKeys.eq_of_mk_mem
  结论: {a : α} {b b' : β a} {l : 列表 (依赖和类型 β)} (nd : NodupKeys l)
  证明: by
  grind [NodupKeys.eq_of_fst_eq]

Depends on / 依赖: NodupKeys, NodupKeys.eq_of_fst_eq, eq_of_fst_eq
-/
theorem NodupKeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b in l) (h' : Sigma.mk a b' in l) : b = b' := by
  grind [NodupKeys.eq_of_fst_eq]

/--
theorem `nodupKeys_singleton` / 定理 `nodupKeys_singleton`

English:
theorem nodupKeys_singleton
  given: (s : Sigma β)
  statement: NodupKeys [s]
  proof: nodup_singleton _

中文:
定理 nodupKeys_singleton
  条件: (s : 依赖和类型 β)
  结论: NodupKeys [s]
  证明: nodup_singleton _

Depends on / 依赖: nodup_singleton
-/
theorem nodupKeys_singleton (s : Sigma β) : NodupKeys [s] :=
  nodup_singleton _

/--
theorem `NodupKeys.sublist` / 定理 `NodupKeys.sublist`

English:
theorem NodupKeys.sublist
  given: {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂)
  statement: NodupKeys l₂ -> NodupKeys l₁
  proof: Nodup.sublist h.map _

@[grind ->]

中文:
定理 NodupKeys.sublist
  条件: {l₁ l₂ : 列表 (依赖和类型 β)} (h : l₁ <+ l₂)
  结论: NodupKeys l₂ -> NodupKeys l₁
  证明: Nodup.sublist h.map _

@[grind ->]

Depends on / 依赖: Nodup.sublist, h.map, sublist
-/
theorem NodupKeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : NodupKeys l₂ -> NodupKeys l₁ :=
Nodup.sublist h.map _

@[grind ->]
/--
theorem `NodupKeys.nodup` / 定理 `NodupKeys.nodup`

English:
theorem NodupKeys.nodup
  given: {l : List (Sigma β)}
  statement: NodupKeys l -> Nodup l
  proof: Nodup.of_map _

中文:
定理 NodupKeys.nodup
  条件: {l : 列表 (依赖和类型 β)}
  结论: NodupKeys l -> Nodup l
  证明: Nodup.of_map _
-/
protected theorem NodupKeys.nodup {l : List (Sigma β)} : NodupKeys l -> Nodup l :=
  Nodup.of_map _

/--
theorem `perm_nodupKeys` / 定理 `perm_nodupKeys`

English:
theorem perm_nodupKeys
  given: {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂)
  statement: NodupKeys l₁ ↔ NodupKeys l₂
  proof: (h.map _).nodup_iff

中文:
定理 perm_nodupKeys
  条件: {l₁ l₂ : 列表 (依赖和类型 β)} (h : l₁ ~ l₂)
  结论: NodupKeys l₁ ↔ NodupKeys l₂
  证明: (h.map _).nodup_iff

Depends on / 依赖: h.map, nodup_iff
-/
theorem perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : NodupKeys l₁ ↔ NodupKeys l₂ :=
  (h.map _).nodup_iff

/--
theorem `nodupKeys_flatten` / 定理 `nodupKeys_flatten`

English:
theorem nodupKeys_flatten
  given: {L : List (List (Sigma β))}
  proof: by
  rw [nodupKeys_iff_pairwise]; rw [pairwise_flatten]; rw [pairwise_map]
  refine and_congr (forall₂_congr fun l _ => by simp [nodupKeys_iff_pairwise]) ?_
  simp [keys, disjoint_iff_ne, Sigma.forall]

中文:
定理 nodupKeys_flatten
  条件: {L : 列表 (列表 (依赖和类型 β))}
  证明: by
  rw [nodupKeys_iff_pairwise]; rw [pairwise_flatten]; rw [pairwise_map]
  refine and_congr (forall₂_congr fun l _ => by simp [nodupKeys_iff_pairwise]) ?_
  simp [keys, disjoint_iff_ne, Sigma.forall]

Depends on / 依赖: Sigma.forall, and_congr, disjoint_iff_ne, nodupKeys_iff_pairwise, pairwise_flatten, pairwise_map
-/
theorem nodupKeys_flatten {L : List (List (Sigma β))} :
    NodupKeys (flatten L) ↔ (forall l in L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys) := by
  rw [nodupKeys_iff_pairwise]; rw [pairwise_flatten]; rw [pairwise_map]
  refine and_congr (forall₂_congr fun l _ => by simp [nodupKeys_iff_pairwise]) ?_
  simp [keys, disjoint_iff_ne, Sigma.forall]

/--
theorem `nodup_zipIdx_map_snd` / 定理 `nodup_zipIdx_map_snd`

English:
theorem nodup_zipIdx_map_snd
  given: (l : List α)
  statement: (l.zipIdx.map Prod.snd).Nodup
  proof: by
  simp [List.nodup_range']

中文:
定理 nodup_zipIdx_map_snd
  条件: (l : 列表 α)
  结论: (l.zipIdx.map 积类型.snd).Nodup
  证明: by
  simp [List.nodup_range']

Depends on / 依赖: List.nodup_range, nodup_range
-/
theorem nodup_zipIdx_map_snd (l : List α) : (l.zipIdx.map Prod.snd).Nodup := by
  simp [List.nodup_range']

/--
theorem `mem_ext` / 定理 `mem_ext`

English:
theorem mem_ext
  statement: {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
  proof: by grind [perm_ext_iff_of_nodup]

中文:
定理 mem_ext
  结论: {l₀ l₁ : 列表 (依赖和类型 β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
  证明: by grind [perm_ext_iff_of_nodup]

Depends on / 依赖: perm_ext_iff_of_nodup
-/
theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
    (h : forall x, x in l₀ ↔ x in l₁) : l₀ ~ l₁ := by grind [perm_ext_iff_of_nodup]

variable [DecidableEq α] [DecidableEq α']

/-! ### `dlookup` -/

/--
Definition of `dlookup` / `dlookup` 的定义

English:
definition dlookup
  signature: (a : α)

中文:
定义 dlookup
  签名: (a : α)
-/
def dlookup (a : α) : List (Sigma β) -> Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l

@[simp, grind =]
/--
theorem `dlookup_nil` / 定理 `dlookup_nil`

English:
theorem dlookup_nil
  given: (a : α)
  statement: dlookup a [] = @none (β a)
  proof: rfl

@[simp, grind =]

中文:
定理 dlookup_nil
  条件: (a : α)
  结论: dlookup a [] = @none (β a)
  证明: rfl

@[simp, grind =]
-/
theorem dlookup_nil (a : α) : dlookup a [] = @none (β a) :=
  rfl

@[simp, grind =]
/--
theorem `dlookup_cons_eq` / 定理 `dlookup_cons_eq`

English:
theorem dlookup_cons_eq
  given: (l) (a : α) (b : β a)
  statement: dlookup a (⟨a, b⟩ :: l) = some b
  proof: dif_pos rfl

@[simp, grind =]

中文:
定理 dlookup_cons_eq
  条件: (l) (a : α) (b : β a)
  结论: dlookup a (⟨a, b⟩ :: l) = some b
  证明: dif_pos rfl

@[simp, grind =]

Depends on / 依赖: dif_pos
-/
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl

@[simp, grind =]
/--
theorem `dlookup_cons_ne` / 定理 `dlookup_cons_ne`

English:
theorem dlookup_cons_ne
  given: (l) {a}
  statement: forall s : Sigma β, a != s.1 -> dlookup a (s :: l) = dlookup a l

中文:
定理 dlookup_cons_ne
  条件: (l) {a}
  结论: 对任意 s : 依赖和类型 β, a != s.1 -> dlookup a (s :: l) = dlookup a l
-/
theorem dlookup_cons_ne (l) {a} : forall s : Sigma β, a != s.1 -> dlookup a (s :: l) = dlookup a l
  | ⟨_, _⟩, h => dif_neg h.symm

@[grind =]
/--
theorem `dlookup_isSome` / 定理 `dlookup_isSome`

English:
theorem dlookup_isSome
  given: {a : α} {l : List (Sigma β)}
  statement: (dlookup a l).isSome ↔ a in l.keys
  proof: by
  induction l with
  | nil => simp
  | cons s _ _ => by_cases a = s.fst <;> grind

中文:
定理 dlookup_isSome
  条件: {a : α} {l : 列表 (依赖和类型 β)}
  结论: (dlookup a l).isSome ↔ a in l.keys
  证明: by
  induction l with
  | nil => simp
  | cons s _ _ => by_cases a = s.fst <;> grind

Depends on / 依赖: s.fst
-/
theorem dlookup_isSome {a : α} {l : List (Sigma β)} : (dlookup a l).isSome ↔ a in l.keys := by
  induction l with
  | nil => simp
  | cons s _ _ => by_cases a = s.fst <;> grind

/--
theorem `dlookup_eq_none` / 定理 `dlookup_eq_none`

English:
theorem dlookup_eq_none
  given: {a : α} {l : List (Sigma β)}
  statement: dlookup a l = none ↔ a ∉ l.keys
  proof: by
  simp [← dlookup_isSome, Option.isNone_iff_eq_none]

中文:
定理 dlookup_eq_none
  条件: {a : α} {l : 列表 (依赖和类型 β)}
  结论: dlookup a l = none ↔ a ∉ l.keys
  证明: by
  simp [← dlookup_isSome, Option.isNone_iff_eq_none]

Depends on / 依赖: Option.isNone_iff_eq_none, dlookup_isSome, isNone_iff_eq_none
-/
theorem dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.keys := by
  simp [← dlookup_isSome, Option.isNone_iff_eq_none]

/--
theorem `of_mem_dlookup` / 定理 `of_mem_dlookup`

English:
theorem of_mem_dlookup
  given: {a : α} {b : β a} {l : List (Sigma β)}
  proof: by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases a = s.fst <;> grind

中文:
定理 of_mem_dlookup
  条件: {a : α} {b : β a} {l : 列表 (依赖和类型 β)}
  证明: by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases a = s.fst <;> grind

Depends on / 依赖: s.fst
-/
theorem of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β)} :
    b in dlookup a l -> Sigma.mk a b in l := by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases a = s.fst <;> grind

/--
theorem `mem_dlookup` / 定理 `mem_dlookup`

English:
theorem mem_dlookup
  given: {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sigma.mk a b in l)
  proof: by
  obtain ⟨b', h'⟩ := Option.isSome_iff_exists.mp (dlookup_isSome.mpr (mem_keys_of_mem h))
  cases nd.eq_of_mk_mem h (of_mem_dlookup h')
  exact h'

中文:
定理 mem_dlookup
  条件: {a} {b : β a} {l : 列表 (依赖和类型 β)} (nd : l.NodupKeys) (h : 依赖和类型.mk a b in l)
  证明: by
  obtain ⟨b', h'⟩ := Option.isSome_iff_exists.mp (dlookup_isSome.mpr (mem_keys_of_mem h))
  cases nd.eq_of_mk_mem h (of_mem_dlookup h')
  exact h'

Depends on / 依赖: Option.isSome_iff_exists.mp, dlookup_isSome, dlookup_isSome.mpr, eq_of_mk_mem, isSome_iff_exists, mem_keys_of_mem, nd.eq_of_mk_mem, of_mem_dlookup
-/
theorem mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sigma.mk a b in l) :
    b in dlookup a l := by
  obtain ⟨b', h'⟩ := Option.isSome_iff_exists.mp (dlookup_isSome.mpr (mem_keys_of_mem h))
  cases nd.eq_of_mk_mem h (of_mem_dlookup h')
  exact h'

/--
theorem `map_dlookup_eq_find` / 定理 `map_dlookup_eq_find`

English:
theorem map_dlookup_eq_find
  given: (a : α) (l : List (Sigma β))
  proof: by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases s.fst = a <;> grind

中文:
定理 map_dlookup_eq_find
  条件: (a : α) (l : 列表 (依赖和类型 β))
  证明: by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases s.fst = a <;> grind

Depends on / 依赖: s.fst
-/
theorem map_dlookup_eq_find (a : α) (l : List (Sigma β)) :
    (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l := by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases s.fst = a <;> grind

/--
theorem `mem_dlookup_iff` / 定理 `mem_dlookup_iff`

English:
theorem mem_dlookup_iff
  given: {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys)
  proof: ⟨of_mem_dlookup, mem_dlookup nd⟩

中文:
定理 mem_dlookup_iff
  条件: {a : α} {b : β a} {l : 列表 (依赖和类型 β)} (nd : l.NodupKeys)
  证明: ⟨of_mem_dlookup, mem_dlookup nd⟩

Depends on / 依赖: mem_dlookup, of_mem_dlookup
-/
theorem mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) :
    b in dlookup a l ↔ Sigma.mk a b in l :=
  ⟨of_mem_dlookup, mem_dlookup nd⟩

/--
theorem `perm_dlookup` / 定理 `perm_dlookup`

English:
theorem perm_dlookup
  given: (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂)
  proof: by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  ext b; simp only [← Option.mem_def, mem_dlookup_iff nd₁, mem_dlookup_iff nd₂, p.mem_iff]

中文:
定理 perm_dlookup
  条件: (a : α) {l₁ l₂ : 列表 (依赖和类型 β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂)
  证明: by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  ext b; simp only [← Option.mem_def, mem_dlookup_iff nd₁, mem_dlookup_iff nd₂, p.mem_iff]

Depends on / 依赖: Option.mem_def, mem_def, mem_dlookup_iff, mem_iff, p.mem_iff, perm_nodupKeys
-/
theorem perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    dlookup a l₁ = dlookup a l₂ := by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  ext b; simp only [← Option.mem_def, mem_dlookup_iff nd₁, mem_dlookup_iff nd₂, p.mem_iff]

/--
theorem `lookup_ext` / 定理 `lookup_ext`

English:
theorem lookup_ext
  statement: {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
  proof: by
  grind [_=_ mem_dlookup_iff, mem_ext]

中文:
定理 lookup_ext
  结论: {l₀ l₁ : 列表 (依赖和类型 β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
  证明: by
  grind [_=_ mem_dlookup_iff, mem_ext]

Depends on / 依赖: mem_dlookup_iff, mem_ext
-/
theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
    (h : forall x y, y in l₀.dlookup x ↔ y in l₁.dlookup x) : l₀ ~ l₁ := by
  grind [_=_ mem_dlookup_iff, mem_ext]

/--
theorem `dlookup_map` / 定理 `dlookup_map`

English:
theorem dlookup_map
  statement: (l : List (Sigma β))
  proof: by
  induction l with
  | nil => grind
  | cons s _ _ =>
have (h : a != s.fst) : ¬ f a = (⟨f s.fst, g s.fst s.snd⟩ : Sigma β').fst := fun he => h hf he
    by_cases a = s.fst <;> grind [Sigma.map]

中文:
定理 dlookup_map
  结论: (l : 列表 (依赖和类型 β))
  证明: by
  induction l with
  | nil => grind
  | cons s _ _ =>
have (h : a != s.fst) : ¬ f a = (⟨f s.fst, g s.fst s.snd⟩ : Sigma β').fst := fun he => h hf he
    by_cases a = s.fst <;> grind [Sigma.map]

Depends on / 依赖: Sigma.map, s.fst, s.snd
-/
theorem dlookup_map (l : List (Sigma β))
    {f : α -> α'} (hf : Function.Injective f) (g : forall a, β a -> β' (f a)) (a : α) :
    (l.map (.map f g)).dlookup (f a) = (l.dlookup a).map (g a) := by
  induction l with
  | nil => grind
  | cons s _ _ =>
have (h : a != s.fst) : ¬ f a = (⟨f s.fst, g s.fst s.snd⟩ : Sigma β').fst := fun he => h hf he
    by_cases a = s.fst <;> grind [Sigma.map]

/--
theorem `dlookup_map₁` / 定理 `dlookup_map₁`

English:
theorem dlookup_map₁
  statement: {β : Type v} (l : List (Σ _ : α, β))
  proof: by
  have := dlookup_map (β' := fun _ => β) (f := f) (g := fun _ => id)
  grind [Option.map_id']

中文:
定理 dlookup_map₁
  结论: {β : 类型v} (l : 列表 (Σ _ : α, β))
  证明: by
  have := dlookup_map (β' := fun _ => β) (f := f) (g := fun _ => id)
  grind [Option.map_id']

Depends on / 依赖: Option.map_id, dlookup_map, map_id
-/
theorem dlookup_map₁ {β : Type v} (l : List (Σ _ : α, β))
    {f : α -> α'} (hf : Function.Injective f) (a : α) :
    (l.map (.map f fun _ => id) : List (Σ _ : α', β)).dlookup (f a) = l.dlookup a := by
  have := dlookup_map (β' := fun _ => β) (f := f) (g := fun _ => id)
  grind [Option.map_id']

/--
theorem `dlookup_map₂` / 定理 `dlookup_map₂`

English:
theorem dlookup_map₂
  given: {γ δ : α -> Type*} {l : List (Σ a, γ a)} {f : forall a, γ a -> δ a} (a : α)
  proof: dlookup_map l Function.injective_id _ _

#adaptation_note /-- Before leanprover/lean4#13166
the grind proof here worked, but after changes to the canonicalizer it now times out.
Changes to grind attributes in Batteries in
https://github.com/leanprover-community/batteries/pull/1744
may allow restorin

中文:
定理 dlookup_map₂
  条件: {γ δ : α -> 类型} {l : 列表 (Σ a, γ a)} {f : 对任意 a, γ a -> δ a} (a : α)
  证明: dlookup_map l Function.injective_id _ _

#adaptation_note /-- Before leanprover/lean4#13166
the grind proof here worked, but after changes to the canonicalizer it now times out.
Changes to grind attributes in Batteries in
https://github.com/leanprover-community/batteries/pull/1744
may allow restorin

Depends on / 依赖: Function, Function.injective_id, dlookup_map, injective_id
-/
theorem dlookup_map₂ {γ δ : α -> Type*} {l : List (Σ a, γ a)} {f : forall a, γ a -> δ a} (a : α) :
    (l.map (.map id f) : List (Σ a, δ a)).dlookup a = (l.dlookup a).map (f a) :=
  dlookup_map l Function.injective_id _ _

#adaptation_note /-- Before leanprover/lean4#13166
the grind proof here worked, but after changes to the canonicalizer it now times out.
Changes to grind attributes in Batteries in
https://github.com/leanprover-community/batteries/pull/1744
may allow restoring the original proof:
```
  induction l with
  | nil => grind [nodupKeys_nil]
  | cons hd tl =>
    have := dlookup_map₁ tl hf hd.fst
    grind [dlookup_isSome, → notMem_keys_of_nodupKeys_cons, nodupKeys_of_nodupKeys_cons,
      nodupKeys_cons]
```
-/
omit [DecidableEq α] [DecidableEq α'] in
/--
theorem `NodupKeys.map₁` / 定理 `NodupKeys.map₁`

English:
theorem NodupKeys.map₁
  statement: {β : Type v} (f : α -> α') (hf : Function.Injective f) {l : List (Σ _ : α, β)}
  proof: by
  induction l with
  | nil => exact nodupKeys_nil
  | cons hd tl ih =>
    simp only [map_cons, nodupKeys_cons] at nd ⊢
    exact ⟨mt (fun h => by
      simp only [keys, map_map] at h ⊢
      obtain ⟨x, hm, he⟩ := mem_map.mp h
      exact mem_map.mpr ⟨x, hm, hf he⟩) nd.1, ih nd.2⟩

omit [Decidabl

中文:
定理 NodupKeys.map₁
  结论: {β : 类型v} (f : α -> α') (hf : 函数.单射 f) {l : 列表 (Σ _ : α, β)}
  证明: by
  induction l with
  | nil => exact nodupKeys_nil
  | cons hd tl ih =>
    simp only [map_cons, nodupKeys_cons] at nd ⊢
    exact ⟨mt (fun h => by
      simp only [keys, map_map] at h ⊢
      obtain ⟨x, hm, he⟩ := mem_map.mp h
      exact mem_map.mpr ⟨x, hm, hf he⟩) nd.1, ih nd.2⟩

omit [Decidabl

Depends on / 依赖: map_cons, map_map, mem_map, mem_map.mp, mem_map.mpr, nodupKeys_cons, nodupKeys_nil
-/
theorem NodupKeys.map₁ {β : Type v} (f : α -> α') (hf : Function.Injective f) {l : List (Σ _ : α, β)}
    (nd : l.NodupKeys) : (l.map (.map f fun _ => id) : List (Σ _ : α', β)).NodupKeys := by
  induction l with
  | nil => exact nodupKeys_nil
  | cons hd tl ih =>
    simp only [map_cons, nodupKeys_cons] at nd ⊢
    exact ⟨mt (fun h => by
      simp only [keys, map_map] at h ⊢
      obtain ⟨x, hm, he⟩ := mem_map.mp h
      exact mem_map.mpr ⟨x, hm, hf he⟩) nd.1, ih nd.2⟩

omit [DecidableEq α] in
/--
theorem `map₂_keys` / 定理 `map₂_keys`

English:
theorem map₂_keys
  given: {β β' : α -> Type*} (f : (a : α) -> β a -> β' a) (l : List (Σ a, β a))
  proof: by
  induction l <;> grind [Sigma.map]

omit [DecidableEq α] in

中文:
定理 map₂_keys
  条件: {β β' : α -> 类型} (f : (a : α) -> β a -> β' a) (l : 列表 (Σ a, β a))
  证明: by
  induction l <;> grind [Sigma.map]

omit [DecidableEq α] in

Depends on / 依赖: Sigma.map
-/
theorem map₂_keys {β β' : α -> Type*} (f : (a : α) -> β a -> β' a) (l : List (Σ a, β a)) :
    (l.map (.map id f)).keys = l.keys := by
  induction l <;> grind [Sigma.map]

omit [DecidableEq α] in
/--
theorem `NodupKeys.map₂` / 定理 `NodupKeys.map₂`

English:
theorem NodupKeys.map₂
  statement: {β β' : α -> Type*} (f : (a : α) -> β a -> β' a) (l : List (Σ a, β a))
  proof: by
  simp_all [NodupKeys, map₂_keys]

@[simp, grind =]

中文:
定理 NodupKeys.map₂
  结论: {β β' : α -> 类型} (f : (a : α) -> β a -> β' a) (l : 列表 (Σ a, β a))
  证明: by
  simp_all [NodupKeys, map₂_keys]

@[simp, grind =]

Depends on / 依赖: NodupKeys
-/
theorem NodupKeys.map₂ {β β' : α -> Type*} (f : (a : α) -> β a -> β' a) (l : List (Σ a, β a))
    (nd : l.NodupKeys) : (l.map (.map id f)).NodupKeys := by
  simp_all [NodupKeys, map₂_keys]

@[simp, grind =]
/--
theorem `dlookup_append` / 定理 `dlookup_append`

English:
theorem dlookup_append
  given: (l₁ l₂ : List (Sigma β)) (a : α)
  proof: by
  induction l₁ with
  | nil => rfl
  | cons s _ _ => by_cases a = s.fst <;> grind

中文:
定理 dlookup_append
  条件: (l₁ l₂ : 列表 (依赖和类型 β)) (a : α)
  证明: by
  induction l₁ with
  | nil => rfl
  | cons s _ _ => by_cases a = s.fst <;> grind

Depends on / 依赖: s.fst
-/
theorem dlookup_append (l₁ l₂ : List (Sigma β)) (a : α) :
    (l₁ ++ l₂).dlookup a = (l₁.dlookup a).or (l₂.dlookup a) := by
  induction l₁ with
  | nil => rfl
  | cons s _ _ => by_cases a = s.fst <;> grind

/--
theorem `sublist_dlookup` / 定理 `sublist_dlookup`

English:
theorem sublist_dlookup
  statement: {l₁ l₂ : List (Sigma β)} {a : α} {b : β a}
  proof: by
  grind [Option.mem_def, => perm_dlookup, -> Sublist.exists_perm_append]

中文:
定理 sublist_dlookup
  结论: {l₁ l₂ : 列表 (依赖和类型 β)} {a : α} {b : β a}
  证明: by
  grind [Option.mem_def, => perm_dlookup, -> Sublist.exists_perm_append]

Depends on / 依赖: Option.mem_def, Sublist, Sublist.exists_perm_append, exists_perm_append, mem_def, perm_dlookup
-/
theorem sublist_dlookup {l₁ l₂ : List (Sigma β)} {a : α} {b : β a}
    (nd₂ : l₂.NodupKeys) (s : l₁ <+ l₂) (mem : b in l₁.dlookup a) : b in l₂.dlookup a := by
  grind [Option.mem_def, => perm_dlookup, -> Sublist.exists_perm_append]

/-! ### `lookupAll` -/


/--
Definition of `lookupAll` / `lookupAll` 的定义

English:
definition lookupAll
  signature: (a : α)

中文:
定义 lookupAll
  签名: (a : α)
-/
def lookupAll (a : α) : List (Sigma β) -> List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOn h b :: lookupAll a l else lookupAll a l

@[simp]
/--
theorem `lookupAll_nil` / 定理 `lookupAll_nil`

English:
theorem lookupAll_nil
  given: (a : α)
  statement: lookupAll a [] = @nil (β a)
  proof: rfl

@[simp]

中文:
定理 lookupAll_nil
  条件: (a : α)
  结论: lookupAll a [] = @nil (β a)
  证明: rfl

@[simp]
-/
theorem lookupAll_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl

@[simp]
/--
theorem `lookupAll_cons_eq` / 定理 `lookupAll_cons_eq`

English:
theorem lookupAll_cons_eq
  given: (l) (a : α) (b : β a)
  statement: lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l
  proof: dif_pos rfl

@[simp]

中文:
定理 lookupAll_cons_eq
  条件: (l) (a : α) (b : β a)
  结论: lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem lookupAll_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl

@[simp]
/--
theorem `lookupAll_cons_ne` / 定理 `lookupAll_cons_ne`

English:
theorem lookupAll_cons_ne
  given: (l) {a}
  statement: forall s : Sigma β, a != s.1 -> lookupAll a (s :: l) = lookupAll a l

中文:
定理 lookupAll_cons_ne
  条件: (l) {a}
  结论: 对任意 s : 依赖和类型 β, a != s.1 -> lookupAll a (s :: l) = lookupAll a l
-/
theorem lookupAll_cons_ne (l) {a} : forall s : Sigma β, a != s.1 -> lookupAll a (s :: l) = lookupAll a l
  | ⟨_, _⟩, h => dif_neg h.symm

/--
theorem `lookupAll_eq_nil` / 定理 `lookupAll_eq_nil`

English:
theorem lookupAll_eq_nil
  given: {a : α}

中文:
定理 lookupAll_eq_nil
  条件: {a : α}
-/
theorem lookupAll_eq_nil {a : α} :
    forall {l : List (Sigma β)}, lookupAll a l = [] ↔ forall b : β a, Sigma.mk a b ∉ l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp only [lookupAll_cons_eq, mem_cons, Sigma.mk.inj_iff, heq_eq_eq, true_and, not_or,
        false_iff, not_forall, not_and, not_not, reduceCtorEq]
      use b
      simp
    · simp [h, lookupAll_eq_nil]

/--
theorem `head?_lookupAll` / 定理 `head?_lookupAll`

English:
theorem head?_lookupAll
  given: (a : α)
  statement: forall l : List (Sigma β), head? (lookupAll a l) = dlookup a l

中文:
定理 head?_lookupAll
  条件: (a : α)
  结论: 对任意 l : 列表 (依赖和类型 β), head? (lookupAll a l) = dlookup a l
-/
theorem head?_lookupAll (a : α) : forall l : List (Sigma β), head? (lookupAll a l) = dlookup a l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst h; simp
    · rw [lookupAll_cons_ne, dlookup_cons_ne, head?_lookupAll a l] <;> assumption

/--
theorem `mem_lookupAll` / 定理 `mem_lookupAll`

English:
theorem mem_lookupAll
  given: {a : α} {b : β a}

中文:
定理 mem_lookupAll
  条件: {a : α} {b : β a}
-/
theorem mem_lookupAll {a : α} {b : β a} :
    forall {l : List (Sigma β)}, b in lookupAll a l ↔ Sigma.mk a b in l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp [*, mem_lookupAll]
    · simp [*, mem_lookupAll]

/--
theorem `lookupAll_sublist` / 定理 `lookupAll_sublist`

English:
theorem lookupAll_sublist
  given: (a : α)
  statement: forall l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l

中文:
定理 lookupAll_sublist
  条件: (a : α)
  结论: 对任意 l : 列表 (依赖和类型 β), (lookupAll a l).map (依赖和类型.mk a) <+ l
-/
theorem lookupAll_sublist (a : α) : forall l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp only [lookupAll_cons_eq, List.map]
      exact (lookupAll_sublist a l).cons_cons _
    · simp only [ne_eq, h, not_false_iff, lookupAll_cons_ne]
      exact (lookupAll_sublist a l).cons _

/--
theorem `lookupAll_length_le_one` / 定理 `lookupAll_length_le_one`

English:
theorem lookupAll_length_le_one
  given: (a : α) {l : List (Sigma β)} (h : l.NodupKeys)
  proof: by
  have := Nodup.sublist ((lookupAll_sublist a l).map _) h
  rw [map_map] at this
  rwa [← nodup_replicate, ← map_const]

中文:
定理 lookupAll_length_le_one
  条件: (a : α) {l : 列表 (依赖和类型 β)} (h : l.NodupKeys)
  证明: by
  have := Nodup.sublist ((lookupAll_sublist a l).map _) h
  rw [map_map] at this
  rwa [← nodup_replicate, ← map_const]

Depends on / 依赖: Nodup.sublist, lookupAll_sublist, map_const, map_map, nodup_replicate, sublist
-/
theorem lookupAll_length_le_one (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    length (lookupAll a l) <= 1 := by
  have := Nodup.sublist ((lookupAll_sublist a l).map _) h
  rw [map_map] at this
  rwa [← nodup_replicate, ← map_const]

/--
theorem `lookupAll_eq_dlookup` / 定理 `lookupAll_eq_dlookup`

English:
theorem lookupAll_eq_dlookup
  given: (a : α) {l : List (Sigma β)} (h : l.NodupKeys)
  proof: by
  rw [← head?_lookupAll]
  have h1 := lookupAll_length_le_one a h; revert h1
  rcases lookupAll a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro h1 <;> try rfl
  exact absurd h1 (by simp)

中文:
定理 lookupAll_eq_dlookup
  条件: (a : α) {l : 列表 (依赖和类型 β)} (h : l.NodupKeys)
  证明: by
  rw [← head?_lookupAll]
  have h1 := lookupAll_length_le_one a h; revert h1
  rcases lookupAll a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro h1 <;> try rfl
  exact absurd h1 (by simp)

Depends on / 依赖: _lookupAll, absurd, lookupAll, lookupAll_length_le_one, revert
-/
theorem lookupAll_eq_dlookup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    lookupAll a l = (dlookup a l).toList := by
  rw [← head?_lookupAll]
  have h1 := lookupAll_length_le_one a h; revert h1
  rcases lookupAll a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro h1 <;> try rfl
  exact absurd h1 (by simp)

/--
theorem `lookupAll_nodup` / 定理 `lookupAll_nodup`

English:
theorem lookupAll_nodup
  given: (a : α) {l : List (Sigma β)} (h : l.NodupKeys)
  statement: (lookupAll a l).Nodup
  proof: by
  (rw [lookupAll_eq_dlookup a h]; apply Option.toList_nodup)

中文:
定理 lookupAll_nodup
  条件: (a : α) {l : 列表 (依赖和类型 β)} (h : l.NodupKeys)
  结论: (lookupAll a l).Nodup
  证明: by
  (rw [lookupAll_eq_dlookup a h]; apply Option.toList_nodup)

Depends on / 依赖: Option.toList_nodup, lookupAll_eq_dlookup, not_nontrivial_singleton, toList_nodup
-/
theorem lookupAll_nodup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : (lookupAll a l).Nodup := by
  (rw [lookupAll_eq_dlookup a h]; apply Option.toList_nodup)

/--
theorem `perm_lookupAll` / 定理 `perm_lookupAll`

English:
theorem perm_lookupAll
  statement: (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys)
  proof: by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  simp [lookupAll_eq_dlookup, nd₁, nd₂, perm_dlookup a nd₁ p]

中文:
定理 perm_lookupAll
  结论: (a : α) {l₁ l₂ : 列表 (依赖和类型 β)} (nd₁ : l₁.NodupKeys)
  证明: by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  simp [lookupAll_eq_dlookup, nd₁, nd₂, perm_dlookup a nd₁ p]

Depends on / 依赖: hs.ne_empty, hs.ne_singleton, lookupAll_eq_dlookup, ne_empty, ne_singleton, not_congr, not_or_intro, perm_dlookup, perm_nodupKeys, subset_singleton_iff_eq
-/
theorem perm_lookupAll (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys)
    (p : l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂ := by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  simp [lookupAll_eq_dlookup, nd₁, nd₂, perm_dlookup a nd₁ p]

/-! ### `kreplace` -/


/--
Definition of `kreplace` / `kreplace` 的定义

English:
definition kreplace
  signature: (a : α) (b : β a)
  body: lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none

中文:
定义 kreplace
  签名: (a : α) (b : β a)
  定义体: lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none

Depends on / 依赖: lookmap
-/
def kreplace (a : α) (b : β a) : List (Sigma β) -> List (Sigma β) :=
  lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none

/--
theorem `kreplace_of_forall_not` / 定理 `kreplace_of_forall_not`

English:
theorem kreplace_of_forall_not
  statement: (a : α) (b : β a) {l : List (Sigma β)}
  proof: lookmap_of_forall_not _ by
    grind

中文:
定理 kreplace_of_对任意_not
  结论: (a : α) (b : β a) {l : 列表 (依赖和类型 β)}
  证明: lookmap_of_forall_not _ by
    grind

Depends on / 依赖: lookmap_of_forall_not
-/
theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)}
    (H : forall b : β a, Sigma.mk a b ∉ l) : kreplace a b l = l :=
lookmap_of_forall_not _ by
    grind

/--
theorem `kreplace_self` / 定理 `kreplace_self`

English:
theorem kreplace_self
  statement: {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l)
  proof: by
  refine (lookmap_congr ?_).trans (lookmap_id' (Option.guard fun (s : Sigma β) => a = s.1) ?_ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      simp [nd.eq_of_mk_mem h h']
    · simp_all
    · simp_all
    · rfl
  · simp

中文:
定理 kreplace_self
  结论: {a : α} {b : β a} {l : 列表 (依赖和类型 β)} (nd : NodupKeys l)
  证明: by
  refine (lookmap_congr ?_).trans (lookmap_id' (Option.guard fun (s : Sigma β) => a = s.1) ?_ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      simp [nd.eq_of_mk_mem h h']
    · simp_all
    · simp_all
    · rfl
  · simp

Depends on / 依赖: Option.guard, eq_of_mk_mem, lookmap_congr, lookmap_id, nd.eq_of_mk_mem, split_ifs
-/
theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b in l) : kreplace a b l = l := by
  refine (lookmap_congr ?_).trans (lookmap_id' (Option.guard fun (s : Sigma β) => a = s.1) ?_ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      simp [nd.eq_of_mk_mem h h']
    · simp_all
    · simp_all
    · rfl
  · simp

/--
theorem `keys_kreplace` / 定理 `keys_kreplace`

English:
theorem keys_kreplace
  given: (a : α) (b : β a)
  statement: forall l : List (Sigma β), (kreplace a b l).keys = l.keys
  proof: lookmap_map_eq _ _ by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩
    dsimp
    split_ifs with h <;> simp +contextual [h]

中文:
定理 keys_kreplace
  条件: (a : α) (b : β a)
  结论: 对任意 l : 列表 (依赖和类型 β), (kreplace a b l).keys = l.keys
  证明: lookmap_map_eq _ _ by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩
    dsimp
    split_ifs with h <;> simp +contextual [h]

Depends on / 依赖: contextual, lookmap_map_eq, split_ifs
-/
theorem keys_kreplace (a : α) (b : β a) : forall l : List (Sigma β), (kreplace a b l).keys = l.keys :=
lookmap_map_eq _ _ by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩
    dsimp
    split_ifs with h <;> simp +contextual [h]

/--
theorem `kreplace_nodupKeys` / 定理 `kreplace_nodupKeys`

English:
theorem kreplace_nodupKeys
  given: (a : α) (b : β a) {l : List (Sigma β)}
  proof: by simp [NodupKeys, keys_kreplace]

中文:
定理 kreplace_nodupKeys
  条件: (a : α) (b : β a) {l : 列表 (依赖和类型 β)}
  证明: by simp [NodupKeys, keys_kreplace]

Depends on / 依赖: NodupKeys, keys_kreplace
-/
theorem kreplace_nodupKeys (a : α) (b : β a) {l : List (Sigma β)} :
    (kreplace a b l).NodupKeys ↔ l.NodupKeys := by simp [NodupKeys, keys_kreplace]

/--
theorem `Perm.kreplace` / 定理 `Perm.kreplace`

English:
theorem Perm.kreplace
  given: {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys)
  proof: perm_lookmap _ by
    refine nd.pairwise_ne.imp ?_
    intro x y h z h₁ w h₂
    split_ifs at h₁ h₂ with h_2 h_1 <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

中文:
定理 置换.kreplace
  条件: {a : α} {b : β a} {l₁ l₂ : 列表 (依赖和类型 β)} (nd : l₁.NodupKeys)
  证明: perm_lookmap _ by
    refine nd.pairwise_ne.imp ?_
    intro x y h z h₁ w h₂
    split_ifs at h₁ h₂ with h_2 h_1 <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

Depends on / 依赖: h_2.symm.trans, nd.pairwise_ne.imp, pairwise_ne, perm_lookmap, split_ifs
-/
theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ -> kreplace a b l₁ ~ kreplace a b l₂ :=
perm_lookmap _ by
    refine nd.pairwise_ne.imp ?_
    intro x y h z h₁ w h₂
    split_ifs at h₁ h₂ with h_2 h_1 <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

/-! ### `kerase` -/


/--
Definition of `kerase` / `kerase` 的定义

English:
definition kerase
  signature: (a : α)
  body: eraseP fun s => a = s.1

@[simp]

中文:
定义 kerase
  签名: (a : α)
  定义体: eraseP fun s => a = s.1

@[simp]

Depends on / 依赖: eraseP
-/
def kerase (a : α) : List (Sigma β) -> List (Sigma β) :=
  eraseP fun s => a = s.1

@[simp]
/--
theorem `kerase_nil` / 定理 `kerase_nil`

English:
theorem kerase_nil
  given: {a}
  statement: @kerase _ β _ a [] = []
  proof: rfl

@[simp]

中文:
定理 kerase_nil
  条件: {a}
  结论: @kerase _ β _ a [] = []
  证明: rfl

@[simp]
-/
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl

@[simp]
/--
theorem `kerase_cons_eq` / 定理 `kerase_cons_eq`

English:
theorem kerase_cons_eq
  given: {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1)
  proof: by simp [kerase, h]

@[simp]

中文:
定理 kerase_cons_eq
  条件: {a} {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)} (h : a = s.1)
  证明: by simp [kerase, h]

@[simp]

Depends on / 依赖: kerase
-/
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) :
    kerase a (s :: l) = l := by simp [kerase, h]

@[simp]
/--
theorem `kerase_cons_ne` / 定理 `kerase_cons_ne`

English:
theorem kerase_cons_ne
  given: {a} {s : Sigma β} {l : List (Sigma β)} (h : a != s.1)
  proof: by simp [kerase, h]

@[simp]

中文:
定理 kerase_cons_ne
  条件: {a} {s : 依赖和类型 β} {l : 列表 (依赖和类型 β)} (h : a != s.1)
  证明: by simp [kerase, h]

@[simp]

Depends on / 依赖: kerase
-/
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a != s.1) :
    kerase a (s :: l) = s :: kerase a l := by simp [kerase, h]

@[simp]
/--
theorem `kerase_of_notMem_keys` / 定理 `kerase_of_notMem_keys`

English:
theorem kerase_of_notMem_keys
  given: {a} {l : List (Sigma β)} (h : a ∉ l.keys)
  statement: kerase a l = l
  proof: by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]

中文:
定理 kerase_of_notMem_keys
  条件: {a} {l : 列表 (依赖和类型 β)} (h : a ∉ l.keys)
  结论: kerase a l = l
  证明: by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]

Depends on / 依赖: not_or
-/
theorem kerase_of_notMem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]

/--
theorem `kerase_sublist` / 定理 `kerase_sublist`

English:
theorem kerase_sublist
  given: (a : α) (l : List (Sigma β))
  statement: kerase a l <+ l
  proof: eraseP_sublist

中文:
定理 kerase_sublist
  条件: (a : α) (l : 列表 (依赖和类型 β))
  结论: kerase a l <+ l
  证明: eraseP_sublist

Depends on / 依赖: eraseP_sublist
-/
theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  eraseP_sublist

/--
theorem `kerase_keys_subset` / 定理 `kerase_keys_subset`

English:
theorem kerase_keys_subset
  given: (a) (l : List (Sigma β))
  statement: (kerase a l).keys subseteq l.keys
  proof: ((kerase_sublist a l).map _).subset

中文:
定理 kerase_keys_subset
  条件: (a) (l : 列表 (依赖和类型 β))
  结论: (kerase a l).keys subseteq l.keys
  证明: ((kerase_sublist a l).map _).subset

Depends on / 依赖: kerase_sublist, subset
-/
theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys subseteq l.keys :=
  ((kerase_sublist a l).map _).subset

/--
theorem `mem_keys_of_mem_keys_kerase` / 定理 `mem_keys_of_mem_keys_kerase`

English:
theorem mem_keys_of_mem_keys_kerase
  given: {a₁ a₂} {l : List (Sigma β)}
  proof: @kerase_keys_subset _ _ _ _ _ _

中文:
定理 mem_keys_of_mem_keys_kerase
  条件: {a₁ a₂} {l : 列表 (依赖和类型 β)}
  证明: @kerase_keys_subset _ _ _ _ _ _

Depends on / 依赖: Exists, Exists.intro, eq_singleton_or_nontrivial, imp_left, kerase_keys_subset
-/
theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} :
    a₁ in (kerase a₂ l).keys -> a₁ in l.keys :=
  @kerase_keys_subset _ _ _ _ _ _

/--
theorem `exists_of_kerase` / 定理 `exists_of_kerase`

English:
theorem exists_of_kerase
  given: {a : α} {l : List (Sigma β)} (h : a in l.keys)
  proof: by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd; rfl, by simp⟩
    · simp only [keys_cons, mem_cons] at h
      rcases h with h | h
      · exact absurd h e
      rcases ih h with ⟨b, tl₁, tl₂, h₁, 

中文:
定理 存在_of_kerase
  条件: {a : α} {l : 列表 (依赖和类型 β)} (h : a in l.keys)
  证明: by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd; rfl, by simp⟩
    · simp only [keys_cons, mem_cons] at h
      rcases h with h | h
      · exact absurd h e
      rcases ih h with ⟨b, tl₁, tl₂, h₁, 

Depends on / 依赖: absurd, keys_cons, mem_cons, not_mem_cons_of_ne_of_not_mem
-/
theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a in l.keys) :
    exists (b : β a) (l₁ l₂ : List (Sigma β)),
      a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd; rfl, by simp⟩
    · simp only [keys_cons, mem_cons] at h
      rcases h with h | h
      · exact absurd h e
      rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
      exact ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by (rw [h₂]; rfl), by
            simp [e, h₃]⟩

@[simp]
/--
theorem `mem_keys_kerase_of_ne` / 定理 `mem_keys_kerase_of_ne`

English:
theorem mem_keys_kerase_of_ne
  given: {a₁ a₂} {l : List (Sigma β)} (h : a₁ != a₂)
  proof: (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ in l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]

中文:
定理 mem_keys_kerase_of_ne
  条件: {a₁ a₂} {l : 列表 (依赖和类型 β)} (h : a₁ != a₂)
  证明: (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ in l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]

Depends on / 依赖: Iff.intro, exists_of_kerase, kerase, l.keys, mem_keys_of_mem_keys_kerase
-/
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ != a₂) :
    a₁ in (kerase a₂ l).keys ↔ a₁ in l.keys :=
  (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ in l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]

/--
theorem `keys_kerase` / 定理 `keys_kerase`

English:
theorem keys_kerase
  given: {a} {l : List (Sigma β)}
  statement: (kerase a l).keys = l.keys.erase a
  proof: by
  rw [keys]; rw [kerase]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [Function.comp_def]
  congr

中文:
定理 keys_kerase
  条件: {a} {l : 列表 (依赖和类型 β)}
  结论: (kerase a l).keys = l.keys.erase a
  证明: by
  rw [keys]; rw [kerase]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [Function.comp_def]
  congr

Depends on / 依赖: Function, Function.comp_def, comp_def, eraseP_map, erase_eq_eraseP, kerase
-/
theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a := by
  rw [keys]; rw [kerase]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [Function.comp_def]
  congr

/--
theorem `kerase_kerase` / 定理 `kerase_kerase`

English:
theorem kerase_kerase
  given: {a a'} {l : List (Sigma β)}
  proof: by
  by_cases h : a = a'
  · subst a'; rfl
  induction l with
  | nil => rfl
  | cons x xs =>
    by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_

中文:
定理 kerase_kerase
  条件: {a a'} {l : 列表 (依赖和类型 β)}
  证明: by
  by_cases h : a = a'
  · subst a'; rfl
  induction l with
  | nil => rfl
  | cons x xs =>
    by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_

Depends on / 依赖: Ne.symm, kerase_cons_eq, kerase_cons_ne
-/
theorem kerase_kerase {a a'} {l : List (Sigma β)} :
    (kerase a' l).kerase a = (kerase a l).kerase a' := by
  by_cases h : a = a'
  · subst a'; rfl
  induction l with
  | nil => rfl
  | cons x xs =>
    by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_cons_ne, *]

/--
theorem `NodupKeys.kerase` / 定理 `NodupKeys.kerase`

English:
theorem NodupKeys.kerase
  given: (a : α)
  statement: NodupKeys l -> (kerase a l).NodupKeys
  proof: NodupKeys.sublist kerase_sublist _ _

中文:
定理 NodupKeys.kerase
  条件: (a : α)
  结论: NodupKeys l -> (kerase a l).NodupKeys
  证明: NodupKeys.sublist kerase_sublist _ _

Depends on / 依赖: NodupKeys, NodupKeys.sublist, kerase_sublist, sublist
-/
theorem NodupKeys.kerase (a : α) : NodupKeys l -> (kerase a l).NodupKeys :=
NodupKeys.sublist kerase_sublist _ _

/--
theorem `Perm.kerase` / 定理 `Perm.kerase`

English:
theorem Perm.kerase
  given: {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys)
  proof: by
  apply Perm.eraseP
  apply (nodupKeys_iff_pairwise.1 nd).imp
  intros; simp_all

@[simp]

中文:
定理 置换.kerase
  条件: {a : α} {l₁ l₂ : 列表 (依赖和类型 β)} (nd : l₁.NodupKeys)
  证明: by
  apply Perm.eraseP
  apply (nodupKeys_iff_pairwise.1 nd).imp
  intros; simp_all

@[simp]

Depends on / 依赖: Perm.eraseP, eraseP, intros, nodupKeys_iff_pairwise
-/
theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ -> kerase a l₁ ~ kerase a l₂ := by
  apply Perm.eraseP
  apply (nodupKeys_iff_pairwise.1 nd).imp
  intros; simp_all

@[simp]
/--
theorem `notMem_keys_kerase` / 定理 `notMem_keys_kerase`

English:
theorem notMem_keys_kerase
  given: (a) {l : List (Sigma β)} (nd : l.NodupKeys)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [nodupKeys_cons] at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]

@[simp]

中文:
定理 notMem_keys_kerase
  条件: (a) {l : 列表 (依赖和类型 β)} (nd : l.NodupKeys)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [nodupKeys_cons] at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]

@[simp]

Depends on / 依赖: nodupKeys_cons
-/
theorem notMem_keys_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    a ∉ (kerase a l).keys := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [nodupKeys_cons] at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]

@[simp]
/--
theorem `dlookup_kerase` / 定理 `dlookup_kerase`

English:
theorem dlookup_kerase
  given: (a) {l : List (Sigma β)} (nd : l.NodupKeys)
  proof: dlookup_eq_none.mpr (notMem_keys_kerase a nd)

@[simp]

中文:
定理 dlookup_kerase
  条件: (a) {l : 列表 (依赖和类型 β)} (nd : l.NodupKeys)
  证明: dlookup_eq_none.mpr (notMem_keys_kerase a nd)

@[simp]

Depends on / 依赖: dlookup_eq_none, dlookup_eq_none.mpr, notMem_keys_kerase
-/
theorem dlookup_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    dlookup a (kerase a l) = none :=
  dlookup_eq_none.mpr (notMem_keys_kerase a nd)

@[simp]
/--
theorem `dlookup_kerase_ne` / 定理 `dlookup_kerase_ne`

English:
theorem dlookup_kerase_ne
  given: {a a'} {l : List (Sigma β)} (h : a != a')
  proof: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ah, bh⟩ := hd
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · subst h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]

中文:
定理 dlookup_kerase_ne
  条件: {a a'} {l : 列表 (依赖和类型 β)} (h : a != a')
  证明: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ah, bh⟩ := hd
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · subst h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]

Depends on / 依赖: Ne.irrefl, irrefl
-/
theorem dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a != a') :
    dlookup a (kerase a' l) = dlookup a l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ah, bh⟩ := hd
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · subst h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]

/--
theorem `kerase_append_left` / 定理 `kerase_append_left`

English:
theorem kerase_append_left
  given: {a}

中文:
定理 kerase_append_left
  条件: {a}
-/
theorem kerase_append_left {a} :
    forall {l₁ l₂ : List (Sigma β)}, a in l₁.keys -> kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by cases h
  | s :: l₁, l₂, h₁ => by
    if h₂ : a = s.1 then simp [h₂]
    else simp_all [kerase_append_left]

/--
theorem `kerase_append_right` / 定理 `kerase_append_right`

English:
theorem kerase_append_right
  given: {a}

中文:
定理 kerase_append_right
  条件: {a}
-/
theorem kerase_append_right {a} :
    forall {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys -> kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, _ => rfl
  | _ :: l₁, l₂, h => by
    simp only [keys_cons, mem_cons, not_or] at h
    simp [h.1, kerase_append_right h.2]

/--
theorem `kerase_comm` / 定理 `kerase_comm`

English:
theorem kerase_comm
  given: (a₁ a₂) (l : List (Sigma β))
  proof: if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ in l.keys then
      if ha₂ : a₂ in l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, _ =>
          if h' : a₂ in l₁.keys then by
            simp [kerase_append_left h',

中文:
定理 kerase_comm
  条件: (a₁ a₂) (l : 列表 (依赖和类型 β))
  证明: if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ in l.keys then
      if ha₂ : a₂ in l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, _ =>
          if h' : a₂ in l₁.keys then by
            simp [kerase_append_left h',

Depends on / 依赖: Ne.symm, exists_of_kerase, kerase, kerase_append_left, kerase_append_right, kerase_cons_ne, l.keys, mem_keys_kerase_of_ne, mem_keys_of_mem_keys_kerase
-/
theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) :
    kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ in l.keys then
      if ha₂ : a₂ in l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, _ =>
          if h' : a₂ in l₁.keys then by
            simp [kerase_append_left h',
              kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]

/--
theorem `sizeOf_kerase` / 定理 `sizeOf_kerase`

English:
theorem sizeOf_kerase
  statement: [SizeOf (Sigma β)] (x : α)
  proof: by
  induction xs with
  | nil => simp
  | cons y ys => by_cases x = y.1 <;> simp [*]

中文:
定理 sizeOf_kerase
  结论: [SizeOf (依赖和类型 β)] (x : α)
  证明: by
  induction xs with
  | nil => simp
  | cons y ys => by_cases x = y.1 <;> simp [*]
-/
theorem sizeOf_kerase [SizeOf (Sigma β)] (x : α)
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.kerase x xs) <= SizeOf.sizeOf xs := by
  induction xs with
  | nil => simp
  | cons y ys => by_cases x = y.1 <;> simp [*]

/-! ### `kinsert` -/


/--
Definition of `kinsert` / `kinsert` 的定义

English:
definition kinsert
  signature: (a : α) (b : β a) (l : List (Sigma β))
  body: ⟨a, b⟩ :: kerase a l

@[simp]

中文:
定义 kinsert
  签名: (a : α) (b : β a) (l : 列表 (依赖和类型 β))
  定义体: ⟨a, b⟩ :: kerase a l

@[simp]

Depends on / 依赖: kerase
-/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l

@[simp]
/--
theorem `kinsert_def` / 定理 `kinsert_def`

English:
theorem kinsert_def
  given: {a} {b : β a} {l : List (Sigma β)}
  statement: kinsert a b l = ⟨a, b⟩ :: kerase a l
  proof: rfl

中文:
定理 kinsert_def
  条件: {a} {b : β a} {l : 列表 (依赖和类型 β)}
  结论: kinsert a b l = ⟨a, b⟩ :: kerase a l
  证明: rfl
-/
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl

/--
theorem `mem_keys_kinsert` / 定理 `mem_keys_kinsert`

English:
theorem mem_keys_kinsert
  given: {a a'} {b' : β a'} {l : List (Sigma β)}
  proof: by by_cases h : a = a' <;> simp [h]

中文:
定理 mem_keys_kinsert
  条件: {a a'} {b' : β a'} {l : 列表 (依赖和类型 β)}
  证明: by by_cases h : a = a' <;> simp [h]
-/
theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} :
    a in (kinsert a' b' l).keys ↔ a = a' ∨ a in l.keys := by by_cases h : a = a' <;> simp [h]

/--
theorem `kinsert_nodupKeys` / 定理 `kinsert_nodupKeys`

English:
theorem kinsert_nodupKeys
  given: (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys)
  proof: nodupKeys_cons.mpr ⟨notMem_keys_kerase a nd, nd.kerase a⟩

中文:
定理 kinsert_nodupKeys
  条件: (a) (b : β a) {l : 列表 (依赖和类型 β)} (nd : l.NodupKeys)
  证明: nodupKeys_cons.mpr ⟨notMem_keys_kerase a nd, nd.kerase a⟩

Depends on / 依赖: kerase, nd.kerase, nodupKeys_cons, nodupKeys_cons.mpr, notMem_keys_kerase
-/
theorem kinsert_nodupKeys (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    (kinsert a b l).NodupKeys :=
  nodupKeys_cons.mpr ⟨notMem_keys_kerase a nd, nd.kerase a⟩

/--
theorem `Perm.kinsert` / 定理 `Perm.kinsert`

English:
theorem Perm.kinsert
  given: {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂)
  proof: (p.kerase nd₁).cons _

中文:
定理 置换.kinsert
  条件: {a} {b : β a} {l₁ l₂ : 列表 (依赖和类型 β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂)
  证明: (p.kerase nd₁).cons _

Depends on / 依赖: Nonempty, Nonempty.of_image2_left, kerase, of_image2_left, p.kerase
-/
theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _

/--
theorem `dlookup_kinsert` / 定理 `dlookup_kinsert`

English:
theorem dlookup_kinsert
  given: {a} {b : β a} (l : List (Sigma β))
  proof: by
  simp only [kinsert, dlookup_cons_eq]

中文:
定理 dlookup_kinsert
  条件: {a} {b : β a} (l : 列表 (依赖和类型 β))
  证明: by
  simp only [kinsert, dlookup_cons_eq]

Depends on / 依赖: Nonempty, Nonempty.of_image2_right, dlookup_cons_eq, kinsert, of_image2_right
-/
theorem dlookup_kinsert {a} {b : β a} (l : List (Sigma β)) :
    dlookup a (kinsert a b l) = some b := by
  simp only [kinsert, dlookup_cons_eq]

/--
theorem `dlookup_kinsert_ne` / 定理 `dlookup_kinsert_ne`

English:
theorem dlookup_kinsert_ne
  given: {a a'} {b' : β a'} {l : List (Sigma β)} (h : a != a')
  proof: by simp [h]

中文:
定理 dlookup_kinsert_ne
  条件: {a a'} {b' : β a'} {l : 列表 (依赖和类型 β)} (h : a != a')
  证明: by simp [h]
-/
theorem dlookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a != a') :
    dlookup a (kinsert a' b' l) = dlookup a l := by simp [h]

/-! ### `kextract` -/


/--
Definition of `kextract` / `kextract` 的定义

English:
definition kextract
  signature: (a : α)
  body: kextract a l
      (b', s :: l')

@[simp]

中文:
定义 kextract
  签名: (a : α)
  定义体: kextract a l
      (b', s :: l')

@[simp]

Depends on / 依赖: kextract
-/
def kextract (a : α) : List (Sigma β) -> Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOn h s.2), l)
    else
      let (b', l') := kextract a l
      (b', s :: l')

@[simp]
/--
theorem `kextract_eq_dlookup_kerase` / 定理 `kextract_eq_dlookup_kerase`

English:
theorem kextract_eq_dlookup_kerase
  given: (a : α)

中文:
定理 kextract_eq_dlookup_kerase
  条件: (a : α)
-/
theorem kextract_eq_dlookup_kerase (a : α) :
    forall l : List (Sigma β), kextract a l = (dlookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp only [kextract]; split_ifs with h
    · subst a'
      simp [kerase]
    · simp [Ne.symm h, kextract_eq_dlookup_kerase a l, kerase]

/-! ### `dedupKeys` -/


/--
Definition of `dedupKeys` / `dedupKeys` 的定义

English:
definition dedupKeys
  signature: : List (Sigma β) -> List (Sigma β)
  body: List.foldr (fun x => kinsert x.1 x.2) []

中文:
定义 dedupKeys
  签名: : 列表 (依赖和类型 β) -> 列表 (依赖和类型 β)
  定义体: List.foldr (fun x => kinsert x.1 x.2) []

Depends on / 依赖: List.foldr, kinsert
-/
def dedupKeys : List (Sigma β) -> List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []

/--
theorem `dedupKeys_cons` / 定理 `dedupKeys_cons`

English:
theorem dedupKeys_cons
  given: {x : Sigma β} (l : List (Sigma β))
  proof: rfl

中文:
定理 dedupKeys_cons
  条件: {x : 依赖和类型 β} (l : 列表 (依赖和类型 β))
  证明: rfl
-/
theorem dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) :
    dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l) :=
  rfl

/--
theorem `nodupKeys_dedupKeys` / 定理 `nodupKeys_dedupKeys`

English:
theorem nodupKeys_dedupKeys
  given: (l : List (Sigma β))
  statement: NodupKeys (dedupKeys l)
  proof: by
  dsimp [dedupKeys]
  generalize hl : nil = l'
  have : NodupKeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction l with
  | nil => apply this
  | cons x xs l_ih =>
    cases x
    simp only [foldr_cons, kinsert_def, nodupKeys_cons]
    constructor
    · simp only [keys_kerase]


中文:
定理 nodupKeys_dedupKeys
  条件: (l : 列表 (依赖和类型 β))
  结论: NodupKeys (dedupKeys l)
  证明: by
  dsimp [dedupKeys]
  generalize hl : nil = l'
  have : NodupKeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction l with
  | nil => apply this
  | cons x xs l_ih =>
    cases x
    simp only [foldr_cons, kinsert_def, nodupKeys_cons]
    constructor
    · simp only [keys_kerase]


Depends on / 依赖: NodupKeys, dedupKeys, foldr_cons, generalize, kerase, keys_kerase, kinsert_def, l_ih, l_ih.kerase, l_ih.not_mem_erase, nodupKeys_cons, nodup_nil, not_mem_erase
-/
theorem nodupKeys_dedupKeys (l : List (Sigma β)) : NodupKeys (dedupKeys l) := by
  dsimp [dedupKeys]
  generalize hl : nil = l'
  have : NodupKeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction l with
  | nil => apply this
  | cons x xs l_ih =>
    cases x
    simp only [foldr_cons, kinsert_def, nodupKeys_cons]
    constructor
    · simp only [keys_kerase]
      apply l_ih.not_mem_erase
    · exact l_ih.kerase _

/--
theorem `dlookup_dedupKeys` / 定理 `dlookup_dedupKeys`

English:
theorem dlookup_dedupKeys
  given: (a : α) (l : List (Sigma β))
  statement: dlookup a (dedupKeys l) = dlookup a l
  proof: by
  induction l with
  | nil => rfl
  | cons l_hd _ l_ih =>
    obtain ⟨a', b⟩ := l_hd
    by_cases h : a = a'
    · subst a'
      rw [dedupKeys_cons]; rw [dlookup_kinsert]; rw [dlookup_cons_eq]
    · rw [dedupKeys_cons, dlookup_kinsert_ne h, l_ih, dlookup_cons_ne]
      exact h

中文:
定理 dlookup_dedupKeys
  条件: (a : α) (l : 列表 (依赖和类型 β))
  结论: dlookup a (dedupKeys l) = dlookup a l
  证明: by
  induction l with
  | nil => rfl
  | cons l_hd _ l_ih =>
    obtain ⟨a', b⟩ := l_hd
    by_cases h : a = a'
    · subst a'
      rw [dedupKeys_cons]; rw [dlookup_kinsert]; rw [dlookup_cons_eq]
    · rw [dedupKeys_cons, dlookup_kinsert_ne h, l_ih, dlookup_cons_ne]
      exact h

Depends on / 依赖: dedupKeys_cons, dlookup_cons_eq, dlookup_cons_ne, dlookup_kinsert, dlookup_kinsert_ne, l_hd, l_ih
-/
theorem dlookup_dedupKeys (a : α) (l : List (Sigma β)) : dlookup a (dedupKeys l) = dlookup a l := by
  induction l with
  | nil => rfl
  | cons l_hd _ l_ih =>
    obtain ⟨a', b⟩ := l_hd
    by_cases h : a = a'
    · subst a'
      rw [dedupKeys_cons]; rw [dlookup_kinsert]; rw [dlookup_cons_eq]
    · rw [dedupKeys_cons, dlookup_kinsert_ne h, l_ih, dlookup_cons_ne]
      exact h

/--
theorem `sizeOf_cons_le_sizeOf_cons` / 定理 `sizeOf_cons_le_sizeOf_cons`

English:
theorem sizeOf_cons_le_sizeOf_cons
  statement: {α : Type*} [SizeOf α] {l r : List α} (a : α)
  proof: by
  rw [cons.sizeOf_spec]; rw [cons.sizeOf_spec]
  exact Nat.add_le_add_iff_left.mpr h

中文:
定理 sizeOf_cons_le_sizeOf_cons
  结论: {α : 类型} [SizeOf α] {l r : 列表 α} (a : α)
  证明: by
  rw [cons.sizeOf_spec]; rw [cons.sizeOf_spec]
  exact Nat.add_le_add_iff_left.mpr h

Depends on / 依赖: Nat.add_le_add_iff_left.mpr, add_le_add_iff_left, cons.sizeOf_spec, sizeOf_spec
-/
theorem sizeOf_cons_le_sizeOf_cons {α : Type*} [SizeOf α] {l r : List α} (a : α)
    (h : SizeOf.sizeOf l <= SizeOf.sizeOf r) :
    SizeOf.sizeOf (a :: l) <= SizeOf.sizeOf (a :: r) := by
  rw [cons.sizeOf_spec]; rw [cons.sizeOf_spec]
  exact Nat.add_le_add_iff_left.mpr h

/--
theorem `sizeOf_dedupKeys` / 定理 `sizeOf_dedupKeys`

English:
theorem sizeOf_dedupKeys
  statement: [SizeOf (Sigma β)]
  proof: by
  induction xs with
  | nil => simp [dedupKeys]
  | cons x xs h =>
    simp only [dedupKeys_cons, kinsert_def, Sigma.eta]
    exact sizeOf_cons_le_sizeOf_cons x (le_trans (sizeOf_kerase x.fst xs.dedupKeys) h)

中文:
定理 sizeOf_dedupKeys
  结论: [SizeOf (依赖和类型 β)]
  证明: by
  induction xs with
  | nil => simp [dedupKeys]
  | cons x xs h =>
    simp only [dedupKeys_cons, kinsert_def, Sigma.eta]
    exact sizeOf_cons_le_sizeOf_cons x (le_trans (sizeOf_kerase x.fst xs.dedupKeys) h)

Depends on / 依赖: Sigma.eta, dedupKeys, dedupKeys_cons, kinsert_def, le_trans, sizeOf_cons_le_sizeOf_cons, sizeOf_kerase, x.fst, xs.dedupKeys
-/
theorem sizeOf_dedupKeys [SizeOf (Sigma β)]
    (xs : List (Sigma β)) : SizeOf.sizeOf (dedupKeys xs) <= SizeOf.sizeOf xs := by
  induction xs with
  | nil => simp [dedupKeys]
  | cons x xs h =>
    simp only [dedupKeys_cons, kinsert_def, Sigma.eta]
    exact sizeOf_cons_le_sizeOf_cons x (le_trans (sizeOf_kerase x.fst xs.dedupKeys) h)

/-! ### `kunion` -/


/--
Definition of `kunion` / `kunion` 的定义

English:
definition kunion
  signature: : List (Sigma β) -> List (Sigma β) -> List (Sigma β)

中文:
定义 kunion
  签名: : 列表 (依赖和类型 β) -> 列表 (依赖和类型 β) -> 列表 (依赖和类型 β)
-/
def kunion : List (Sigma β) -> List (Sigma β) -> List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)

@[simp]
/--
theorem `nil_kunion` / 定理 `nil_kunion`

English:
theorem nil_kunion
  given: {l : List (Sigma β)}
  statement: kunion [] l = l
  proof: rfl

@[simp]

中文:
定理 nil_kunion
  条件: {l : 列表 (依赖和类型 β)}
  结论: kunion [] l = l
  证明: rfl

@[simp]
-/
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl

@[simp]
/--
theorem `kunion_nil` / 定理 `kunion_nil`

English:
theorem kunion_nil
  statement: forall {l : List (Sigma β)}, kunion l [] = l

中文:
定理 kunion_nil
  结论: 对任意 {l : 列表 (依赖和类型 β)}, kunion l [] = l
-/
theorem kunion_nil : forall {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by rw [kunion, kerase_nil, kunion_nil]

@[simp]
/--
theorem `kunion_cons` / 定理 `kunion_cons`

English:
theorem kunion_cons
  given: {s} {l₁ l₂ : List (Sigma β)}
  proof: rfl

@[simp]

中文:
定理 kunion_cons
  条件: {s} {l₁ l₂ : 列表 (依赖和类型 β)}
  证明: rfl

@[simp]
-/
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} :
    kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl

@[simp]
/--
theorem `mem_keys_kunion` / 定理 `mem_keys_kunion`

English:
theorem mem_keys_kunion
  given: {a} {l₁ l₂ : List (Sigma β)}
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h]; simp [h, ih]]

@[simp]

中文:
定理 mem_keys_kunion
  条件: {a} {l₁ l₂ : 列表 (依赖和类型 β)}
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h]; simp [h, ih]]

@[simp]

Depends on / 依赖: generalizing
-/
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} :
    a in (kunion l₁ l₂).keys ↔ a in l₁.keys ∨ a in l₂.keys := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h]; simp [h, ih]]

@[simp]
/--
theorem `kunion_kerase` / 定理 `kunion_kerase`

English:
theorem kunion_kerase
  given: {a}

中文:
定理 kunion_kerase
  条件: {a}
-/
theorem kunion_kerase {a} :
    forall {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by by_cases h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]

/--
theorem `NodupKeys.kunion` / 定理 `NodupKeys.kunion`

English:
theorem NodupKeys.kunion
  given: (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
  statement: (kunion l₁ l₂).NodupKeys
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp only [nil_kunion, nd₂]
  | cons s l₁ ih =>
    simp only [nodupKeys_cons] at nd₁
    simp [nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]

中文:
定理 NodupKeys.kunion
  条件: (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
  结论: (kunion l₁ l₂).NodupKeys
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp only [nil_kunion, nd₂]
  | cons s l₁ ih =>
    simp only [nodupKeys_cons] at nd₁
    simp [nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]

Depends on / 依赖: generalizing, kerase, nil_kunion, nodupKeys_cons
-/
theorem NodupKeys.kunion (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) : (kunion l₁ l₂).NodupKeys := by
  induction l₁ generalizing l₂ with
  | nil => simp only [nil_kunion, nd₂]
  | cons s l₁ ih =>
    simp only [nodupKeys_cons] at nd₁
    simp [nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]

/--
theorem `Perm.kunion_right` / 定理 `Perm.kunion_right`

English:
theorem Perm.kunion_right
  given: {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l)
  proof: by
  induction p generalizing l with
  | nil => rfl
  | cons hd _ ih =>
    simp [ih (List.kerase _ _)]
  | swap s₁ s₂ l => simp [kerase_comm, Perm.swap]
  | trans _ _ ih₁₂ ih₂₃ => exact Perm.trans (ih₁₂ l) (ih₂₃ l)

中文:
定理 置换.kunion_right
  条件: {l₁ l₂ : 列表 (依赖和类型 β)} (p : l₁ ~ l₂) (l)
  证明: by
  induction p generalizing l with
  | nil => rfl
  | cons hd _ ih =>
    simp [ih (List.kerase _ _)]
  | swap s₁ s₂ l => simp [kerase_comm, Perm.swap]
  | trans _ _ ih₁₂ ih₂₃ => exact Perm.trans (ih₁₂ l) (ih₂₃ l)

Depends on / 依赖: List.kerase, Perm.swap, Perm.trans, generalizing, kerase, kerase_comm
-/
theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) :
    kunion l₁ l ~ kunion l₂ l := by
  induction p generalizing l with
  | nil => rfl
  | cons hd _ ih =>
    simp [ih (List.kerase _ _)]
  | swap s₁ s₂ l => simp [kerase_comm, Perm.swap]
  | trans _ _ ih₁₂ ih₂₃ => exact Perm.trans (ih₁₂ l) (ih₂₃ l)

/--
theorem `Perm.kunion_left` / 定理 `Perm.kunion_left`

English:
theorem Perm.kunion_left

中文:
定理 置换.kunion_left
-/
theorem Perm.kunion_left :
    forall (l) {l₁ l₂ : List (Sigma β)}, l₁.NodupKeys -> l₁ ~ l₂ -> kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, _, _, nd₁, p => ((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s

/--
theorem `Perm.kunion` / 定理 `Perm.kunion`

English:
theorem Perm.kunion
  statement: {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
  proof: (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]

中文:
定理 置换.kunion
  结论: {l₁ l₂ l₃ l₄ : 列表 (依赖和类型 β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
  证明: (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]

Depends on / 依赖: kunion_left, kunion_right
-/
theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
    (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]
/--
theorem `dlookup_kunion_left` / 定理 `dlookup_kunion_left`

English:
theorem dlookup_kunion_left
  given: {a} {l₁ l₂ : List (Sigma β)} (h : a in l₁.keys)
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons s _ ih =>
    simp only [keys_cons, mem_cons] at h
    rcases h with rfl | h <;> obtain ⟨a'⟩ := s
    · simp
    · rw [kunion_cons]
      by_cases h' : a = a'
      · subst h'
        simp
      · simp [h', ih h]

@[simp]

中文:
定理 dlookup_kunion_left
  条件: {a} {l₁ l₂ : 列表 (依赖和类型 β)} (h : a in l₁.keys)
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons s _ ih =>
    simp only [keys_cons, mem_cons] at h
    rcases h with rfl | h <;> obtain ⟨a'⟩ := s
    · simp
    · rw [kunion_cons]
      by_cases h' : a = a'
      · subst h'
        simp
      · simp [h', ih h]

@[simp]

Depends on / 依赖: generalizing, keys_cons, kunion_cons, mem_cons
-/
theorem dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a in l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons s _ ih =>
    simp only [keys_cons, mem_cons] at h
    rcases h with rfl | h <;> obtain ⟨a'⟩ := s
    · simp
    · rw [kunion_cons]
      by_cases h' : a = a'
      · subst h'
        simp
      · simp [h', ih h]

@[simp]
/--
theorem `dlookup_kunion_right` / 定理 `dlookup_kunion_right`

English:
theorem dlookup_kunion_right
  given: {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys)
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih => simp_all [not_or]

中文:
定理 dlookup_kunion_right
  条件: {a} {l₁ l₂ : 列表 (依赖和类型 β)} (h : a ∉ l₁.keys)
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih => simp_all [not_or]

Depends on / 依赖: generalizing, not_or
-/
theorem dlookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih => simp_all [not_or]

/--
theorem `mem_dlookup_kunion` / 定理 `mem_dlookup_kunion`

English:
theorem mem_dlookup_kunion
  given: {a} {b : β a} {l₁ l₂ : List (Sigma β)}
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s _ ih =>
    obtain ⟨a'⟩ := s
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · simp [h₁, @ih (kerase a' l₂)]

@[simp]

中文:
定理 mem_dlookup_kunion
  条件: {a} {b : β a} {l₁ l₂ : 列表 (依赖和类型 β)}
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s _ ih =>
    obtain ⟨a'⟩ := s
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · simp [h₁, @ih (kerase a' l₂)]

@[simp]

Depends on / 依赖: generalizing, kerase
-/
theorem mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b in dlookup a (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b in dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s _ ih =>
    obtain ⟨a'⟩ := s
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · simp [h₁, @ih (kerase a' l₂)]

@[simp]
/--
theorem `dlookup_kunion_eq_some` / 定理 `dlookup_kunion_eq_some`

English:
theorem dlookup_kunion_eq_some
  given: {a} {b : β a} {l₁ l₂ : List (Sigma β)}
  proof: mem_dlookup_kunion

中文:
定理 dlookup_kunion_eq_some
  条件: {a} {b : β a} {l₁ l₂ : 列表 (依赖和类型 β)}
  证明: mem_dlookup_kunion

Depends on / 依赖: mem_dlookup_kunion
-/
theorem dlookup_kunion_eq_some {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    dlookup a (kunion l₁ l₂) = some b ↔
      dlookup a l₁ = some b ∨ a ∉ l₁.keys ∧ dlookup a l₂ = some b :=
  mem_dlookup_kunion

/--
theorem `mem_dlookup_kunion_middle` / 定理 `mem_dlookup_kunion_middle`

English:
theorem mem_dlookup_kunion_middle
  statement: {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
  proof: match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
| Or.inr h => mem_dlookup_kunion.mpr Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩

中文:
定理 mem_dlookup_kunion_middle
  结论: {a} {b : β a} {l₁ l₂ l₃ : 列表 (依赖和类型 β)}
  证明: match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
| Or.inr h => mem_dlookup_kunion.mpr Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩

Depends on / 依赖: Or.inl, Or.inr, mem_dlookup_kunion, mem_dlookup_kunion.mp, mem_dlookup_kunion.mpr, mem_keys_kunion, mem_keys_kunion.mp, not_or, not_or.mpr
-/
theorem mem_dlookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
    (h₁ : b in dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
    b in dlookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
| Or.inr h => mem_dlookup_kunion.mpr Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩

end List
