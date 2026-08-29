/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

/-!
# Finite sets in `Option α`

In this file we define

* `Option.toFinset`: construct an empty or singleton `Finset α` from an `Option α`;
* `Finset.insertNone`: given `s : Finset α`, lift it to a finset on `Option α` using `Option.some`
  and then insert `Option.none`;
* `Finset.eraseNone`: given `s : Finset (Option α)`, returns `t : Finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/

@[expose] public section


variable {α β : Type*}

open Function

namespace Option

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (o : Option α)
  body: o.elim ∅ singleton

@[simp]

中文:
定义 toFinset
  签名: (o : 选项类型 α)
  定义体: o.elim ∅ singleton

@[simp]

Depends on / 依赖: o.elim, singleton
-/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton

@[simp]
/--
theorem `toFinset_none` / 定理 `toFinset_none`

English:
theorem toFinset_none
  statement: none.toFinset = (∅ : Finset α)
  proof: rfl

@[simp]

中文:
定理 toFinset_none
  结论: none.toFinset = (∅ : 有限集 α)
  证明: rfl

@[simp]
-/
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl

@[simp]
/--
theorem `toFinset_some` / 定理 `toFinset_some`

English:
theorem toFinset_some
  given: {a : α}
  statement: (some a).toFinset = {a}
  proof: rfl

@[simp]

中文:
定理 toFinset_some
  条件: {a : α}
  结论: (some a).toFinset = {a}
  证明: rfl

@[simp]
-/
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl

@[simp]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  given: {a : α} {o : Option α}
  statement: a in o.toFinset ↔ a in o
  proof: by
  cases o <;> simp [eq_comm]

中文:
定理 mem_toFinset
  条件: {a : α} {o : 选项类型 α}
  结论: a in o.toFinset ↔ a in o
  证明: by
  cases o <;> simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem mem_toFinset {a : α} {o : Option α} : a in o.toFinset ↔ a in o := by
  cases o <;> simp [eq_comm]

/--
theorem `card_toFinset` / 定理 `card_toFinset`

English:
theorem card_toFinset
  given: (o : Option α)
  statement: o.toFinset.card = o.elim 0 1
  proof: by cases o <;> rfl

中文:
定理 card_toFinset
  条件: (o : 选项类型 α)
  结论: o.toFinset.card = o.elim 0 1
  证明: by cases o <;> rfl
-/
theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl

end Option

namespace Finset

/--
Definition of `insertNone` / `insertNone` 的定义

English:
definition insertNone
  signature: : Finset α ↪o Finset (Option α)
  body: (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
    rw [cons_subset_cons]; rw [map_subset_map]

@[simp]

中文:
定义 insertNone
  签名: : 有限集 α ↪o 有限集 (选项类型 α)
  定义体: (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
    rw [cons_subset_cons]; rw [map_subset_map]

@[simp]

Depends on / 依赖: Embedding, Embedding.some, OrderEmbedding, OrderEmbedding.ofMapLEIff, cons_subset_cons, map_subset_map, ofMapLEIff, s.map
-/
def insertNone : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
    rw [cons_subset_cons]; rw [map_subset_map]

@[simp]
/--
theorem `mem_insertNone` / 定理 `mem_insertNone`

English:
theorem mem_insertNone
  given: {s : Finset α}
  statement: forall {o : Option α}, o in insertNone s ↔ forall a in o, a in s

中文:
定理 mem_insertNone
  条件: {s : 有限集 α}
  结论: 对任意 {o : 选项类型 α}, o in insertNone s ↔ 对任意 a in o, a in s
-/
theorem mem_insertNone {s : Finset α} : forall {o : Option α}, o in insertNone s ↔ forall a in o, a in s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
| some a => Multiset.mem_cons.trans by simp

/--
lemma `forall_mem_insertNone` / 引理 `forall_mem_insertNone`

English:
lemma forall_mem_insertNone
  given: {s : Finset α} {p : Option α -> Prop}
  proof: by simp [Option.forall]

中文:
引理 对任意_mem_insertNone
  条件: {s : 有限集 α} {p : 选项类型 α -> 命题}
  证明: by simp [Option.forall]

Depends on / 依赖: Option.forall
-/
lemma forall_mem_insertNone {s : Finset α} {p : Option α -> Prop} :
    (forall a in insertNone s, p a) ↔ p none ∧ forall a in s, p a := by simp [Option.forall]

/--
theorem `some_mem_insertNone` / 定理 `some_mem_insertNone`

English:
theorem some_mem_insertNone
  given: {s : Finset α} {a : α}
  statement: some a in insertNone s ↔ a in s
  proof: by simp

中文:
定理 some_mem_insertNone
  条件: {s : 有限集 α} {a : α}
  结论: some a in insertNone s ↔ a in s
  证明: by simp
-/
theorem some_mem_insertNone {s : Finset α} {a : α} : some a in insertNone s ↔ a in s := by simp

/--
lemma `none_mem_insertNone` / 引理 `none_mem_insertNone`

English:
lemma none_mem_insertNone
  given: {s : Finset α}
  statement: none in insertNone s
  proof: by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
.Nonempty := ⟨none, none_mem_insertNone⟩ lemma insertNone_nonempty {s : Finset α} : insertNone s

@[simp]

中文:
引理 none_mem_insertNone
  条件: {s : 有限集 α}
  结论: none in insertNone s
  证明: by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
.Nonempty := ⟨none, none_mem_insertNone⟩ lemma insertNone_nonempty {s : Finset α} : insertNone s

@[simp]
-/
lemma none_mem_insertNone {s : Finset α} : none in insertNone s := by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
.Nonempty := ⟨none, none_mem_insertNone⟩ lemma insertNone_nonempty {s : Finset α} : insertNone s

@[simp]
/--
theorem `card_insertNone` / 定理 `card_insertNone`

English:
theorem card_insertNone
  given: (s : Finset α)
  statement: s.insertNone.card = s.card + 1
  proof: by simp [insertNone]

中文:
定理 card_insertNone
  条件: (s : 有限集 α)
  结论: s.insertNone.card = s.card + 1
  证明: by simp [insertNone]

Depends on / 依赖: insertNone
-/
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insertNone]

/--
Definition of `eraseNone` / `eraseNone` 的定义

English:
definition eraseNone
  signature: : Finset (Option α) ->o Finset α
  body: (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]

中文:
定义 eraseNone
  签名: : 有限集 (选项类型 α) ->o 有限集 α
  定义体: (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]

Depends on / 依赖: Equiv.optionIsSomeEquiv, Finset, Finset.mapEmbedding, Finset.subtype, mapEmbedding, optionIsSomeEquiv, subtype, subtype_mono, toEmbedding, toOrderHom, toOrderHom.comp
-/
def eraseNone : Finset (Option α) ->o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]
/--
theorem `mem_eraseNone` / 定理 `mem_eraseNone`

English:
theorem mem_eraseNone
  given: {s : Finset (Option α)} {x : α}
  statement: x in eraseNone s ↔ some x in s
  proof: by
  simp [eraseNone]

中文:
定理 mem_eraseNone
  条件: {s : 有限集 (选项类型 α)} {x : α}
  结论: x in eraseNone s ↔ some x in s
  证明: by
  simp [eraseNone]

Depends on / 依赖: eraseNone
-/
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x in eraseNone s ↔ some x in s := by
  simp [eraseNone]

/--
lemma `forall_mem_eraseNone` / 引理 `forall_mem_eraseNone`

English:
lemma forall_mem_eraseNone
  given: {s : Finset (Option α)} {p : Option α -> Prop}
  proof: by simp

中文:
引理 对任意_mem_eraseNone
  条件: {s : 有限集 (选项类型 α)} {p : 选项类型 α -> 命题}
  证明: by simp
-/
lemma forall_mem_eraseNone {s : Finset (Option α)} {p : Option α -> Prop} :
    (forall a in eraseNone s, p a) ↔ forall a : α, (a : Option α) in s -> p a := by simp

/--
theorem `eraseNone_eq_biUnion` / 定理 `eraseNone_eq_biUnion`

English:
theorem eraseNone_eq_biUnion
  given: [DecidableEq α] (s : Finset (Option α))
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_eq_biUnion
  条件: [DecidableEq α] (s : 有限集 (选项类型 α))
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) :
    eraseNone s = s.biUnion Option.toFinset := by
  ext
  simp

@[simp]
/--
theorem `eraseNone_map_some` / 定理 `eraseNone_map_some`

English:
theorem eraseNone_map_some
  given: (s : Finset α)
  statement: eraseNone (s.map Embedding.some) = s
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_map_some
  条件: (s : 有限集 α)
  结论: eraseNone (s.map 嵌入.some) = s
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_map_some (s : Finset α) : eraseNone (s.map Embedding.some) = s := by
  ext
  simp

@[simp]
/--
theorem `eraseNone_image_some` / 定理 `eraseNone_image_some`

English:
theorem eraseNone_image_some
  given: [DecidableEq (Option α)] (s : Finset α)
  proof: by simpa only [map_eq_image] using! eraseNone_map_some s

@[simp]

中文:
定理 eraseNone_image_some
  条件: [DecidableEq (选项类型 α)] (s : 有限集 α)
  证明: by simpa only [map_eq_image] using! eraseNone_map_some s

@[simp]

Depends on / 依赖: eraseNone_map_some, map_eq_image
-/
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    eraseNone (s.image some) = s := by simpa only [map_eq_image] using! eraseNone_map_some s

@[simp]
/--
theorem `coe_eraseNone` / 定理 `coe_eraseNone`

English:
theorem coe_eraseNone
  given: (s : Finset (Option α))
  statement: (eraseNone s : Set α) = some ⁻¹' s
  proof: Set.ext fun _ => mem_eraseNone

@[simp]

中文:
定理 coe_eraseNone
  条件: (s : 有限集 (选项类型 α))
  结论: (eraseNone s : 集合 α) = some ⁻¹' s
  证明: Set.ext fun _ => mem_eraseNone

@[simp]

Depends on / 依赖: Set.ext, mem_eraseNone
-/
theorem coe_eraseNone (s : Finset (Option α)) : (eraseNone s : Set α) = some ⁻¹' s :=
  Set.ext fun _ => mem_eraseNone

@[simp]
/--
theorem `eraseNone_union` / 定理 `eraseNone_union`

English:
theorem eraseNone_union
  given: [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α))
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_union
  条件: [DecidableEq (选项类型 α)] [DecidableEq α] (s t : 有限集 (选项类型 α))
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s union t) = eraseNone s union eraseNone t := by
  ext
  simp

@[simp]
/--
theorem `eraseNone_inter` / 定理 `eraseNone_inter`

English:
theorem eraseNone_inter
  given: [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α))
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_inter
  条件: [DecidableEq (选项类型 α)] [DecidableEq α] (s t : 有限集 (选项类型 α))
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s inter t) = eraseNone s inter eraseNone t := by
  ext
  simp

@[simp]
/--
theorem `eraseNone_empty` / 定理 `eraseNone_empty`

English:
theorem eraseNone_empty
  statement: eraseNone (∅ : Finset (Option α)) = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_empty
  结论: eraseNone (∅ : 有限集 (选项类型 α)) = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_empty : eraseNone (∅ : Finset (Option α)) = ∅ := by
  ext
  simp

@[simp]
/--
theorem `eraseNone_none` / 定理 `eraseNone_none`

English:
theorem eraseNone_none
  statement: eraseNone ({none} : Finset (Option α)) = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 eraseNone_none
  结论: eraseNone ({none} : 有限集 (选项类型 α)) = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem eraseNone_none : eraseNone ({none} : Finset (Option α)) = ∅ := by
  ext
  simp

@[simp]
/--
theorem `image_some_eraseNone` / 定理 `image_some_eraseNone`

English:
theorem image_some_eraseNone
  given: [DecidableEq (Option α)] (s : Finset (Option α))
  proof: by ext (_ | x) <;> simp

@[simp]

中文:
定理 image_some_eraseNone
  条件: [DecidableEq (选项类型 α)] (s : 有限集 (选项类型 α))
  证明: by ext (_ | x) <;> simp

@[simp]
-/
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).image some = s.erase none := by ext (_ | x) <;> simp

@[simp]
/--
theorem `map_some_eraseNone` / 定理 `map_some_eraseNone`

English:
theorem map_some_eraseNone
  given: [DecidableEq (Option α)] (s : Finset (Option α))
  proof: by
  rw [map_eq_image]; rw [Embedding.some_apply]; rw [image_some_eraseNone]

@[simp]

中文:
定理 map_some_eraseNone
  条件: [DecidableEq (选项类型 α)] (s : 有限集 (选项类型 α))
  证明: by
  rw [map_eq_image]; rw [Embedding.some_apply]; rw [image_some_eraseNone]

@[simp]

Depends on / 依赖: Embedding, Embedding.some_apply, image_some_eraseNone, map_eq_image, some_apply
-/
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).map Embedding.some = s.erase none := by
  rw [map_eq_image]; rw [Embedding.some_apply]; rw [image_some_eraseNone]

@[simp]
/--
theorem `insertNone_eraseNone` / 定理 `insertNone_eraseNone`

English:
theorem insertNone_eraseNone
  given: [DecidableEq (Option α)] (s : Finset (Option α))
  proof: by ext (_ | x) <;> simp

@[simp]

中文:
定理 insertNone_eraseNone
  条件: [DecidableEq (选项类型 α)] (s : 有限集 (选项类型 α))
  证明: by ext (_ | x) <;> simp

@[simp]
-/
theorem insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp

@[simp]
/--
theorem `eraseNone_insertNone` / 定理 `eraseNone_insertNone`

English:
theorem eraseNone_insertNone
  given: (s : Finset α)
  statement: eraseNone (insertNone s) = s
  proof: by
  ext
  simp

中文:
定理 eraseNone_insertNone
  条件: (s : 有限集 α)
  结论: eraseNone (insertNone s) = s
  证明: by
  ext
  simp
-/
theorem eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s := by
  ext
  simp

/--
theorem `card_eraseNone_eq_card_erase` / 定理 `card_eraseNone_eq_card_erase`

English:
theorem card_eraseNone_eq_card_erase
  given: [DecidableEq (Option α)] (s : Finset (Option α))
  proof: by
  rw [← card_map Function.Embedding.some]; rw [map_some_eraseNone]

中文:
定理 card_eraseNone_eq_card_erase
  条件: [DecidableEq (选项类型 α)] (s : 有限集 (选项类型 α))
  证明: by
  rw [← card_map Function.Embedding.some]; rw [map_some_eraseNone]

Depends on / 依赖: Embedding, Function, Function.Embedding.some, card_map, map_some_eraseNone
-/
theorem card_eraseNone_eq_card_erase [DecidableEq (Option α)] (s : Finset (Option α)) :
    #s.eraseNone = #(s.erase none) := by
  rw [← card_map Function.Embedding.some]; rw [map_some_eraseNone]

/--
theorem `card_eraseNone_le` / 定理 `card_eraseNone_le`

English:
theorem card_eraseNone_le
  given: (s : Finset (Option α))
  statement: #s.eraseNone <= #s
  proof: by
  classical
  rw [card_eraseNone_eq_card_erase]
  apply card_erase_le

中文:
定理 card_eraseNone_le
  条件: (s : 有限集 (选项类型 α))
  结论: #s.eraseNone <= #s
  证明: by
  classical
  rw [card_eraseNone_eq_card_erase]
  apply card_erase_le

Depends on / 依赖: card_eraseNone_eq_card_erase, card_erase_le, classical
-/
theorem card_eraseNone_le (s : Finset (Option α)) : #s.eraseNone <= #s := by
  classical
  rw [card_eraseNone_eq_card_erase]
  apply card_erase_le

/--
theorem `card_eraseNone_of_mem` / 定理 `card_eraseNone_of_mem`

English:
theorem card_eraseNone_of_mem
  given: {s : Finset (Option α)} (h : none in s)
  statement: #s.eraseNone = #s - 1
  proof: by
  classical rw [card_eraseNone_eq_card_erase, card_erase_of_mem h]

中文:
定理 card_eraseNone_of_mem
  条件: {s : 有限集 (选项类型 α)} (h : none in s)
  结论: #s.eraseNone = #s - 1
  证明: by
  classical rw [card_eraseNone_eq_card_erase, card_erase_of_mem h]

Depends on / 依赖: card_eraseNone_eq_card_erase, card_erase_of_mem, classical
-/
theorem card_eraseNone_of_mem {s : Finset (Option α)} (h : none in s) : #s.eraseNone = #s - 1 := by
  classical rw [card_eraseNone_eq_card_erase, card_erase_of_mem h]

/--
theorem `card_eraseNone_of_not_mem` / 定理 `card_eraseNone_of_not_mem`

English:
theorem card_eraseNone_of_not_mem
  given: {s : Finset (Option α)} (h : none ∉ s)
  statement: #s.eraseNone = #s
  proof: by
  classical rw [card_eraseNone_eq_card_erase, erase_eq_of_notMem h]

中文:
定理 card_eraseNone_of_not_mem
  条件: {s : 有限集 (选项类型 α)} (h : none ∉ s)
  结论: #s.eraseNone = #s
  证明: by
  classical rw [card_eraseNone_eq_card_erase, erase_eq_of_notMem h]

Depends on / 依赖: card_eraseNone_eq_card_erase, classical, erase_eq_of_notMem
-/
theorem card_eraseNone_of_not_mem {s : Finset (Option α)} (h : none ∉ s) : #s.eraseNone = #s := by
  classical rw [card_eraseNone_eq_card_erase, erase_eq_of_notMem h]

end Finset
