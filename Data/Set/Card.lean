/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Finite.Powerset

/-!
# Noncomputable Set Cardinality

We define the cardinality of set `s` as a term `Set.encard s : ℕ∞` and a term `Set.ncard s : ℕ`.
The latter takes the junk value of zero if `s` is infinite. Both functions are noncomputable, and
are defined in terms of `ENat.card` (which takes a type as its argument); this file can be seen
as an API for the same function in the special case where the type is a coercion of a `Set`,
allowing for smoother interactions with the `Set` API.

`Set.encard` never takes junk values, so is more mathematically natural than `Set.ncard`, even
though it takes values in a less convenient type. It is probably the right choice in settings where
one is concerned with the cardinalities of sets that may or may not be infinite.

`Set.ncard` has a nicer codomain, but when using it, `Set.Finite` hypotheses are normally needed to
make sure its values are meaningful. More generally, `Set.ncard` is intended to be used over the
obvious alternative `Finset.card` when finiteness is 'propositional' rather than 'structural'.
When working with sets that are finite by virtue of their definition, then `Finset.card` probably
makes more sense. One setting where `Set.ncard` works nicely is in a type `α` with `[Finite α]`,
where every set is automatically finite. In this setting, we use default arguments and a simple
tactic so that finiteness goals are discharged automatically in `Set.ncard` theorems.

## Main Definitions

* `Set.encard s` is the cardinality of the set `s` as an extended natural number, with value `⊤` if
    `s` is infinite.
* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `Set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize a `Set.Finite s` argument with
  `Set.toFinite`. This will work for `s : Set α` where there is a `Finite α` instance.

## Implementation Notes

The theorems in this file are very similar to those in `Mathlib/Data/Finset/Card.lean`, but with
`Set` operations instead of `Finset`. We first prove all the theorems for `Set.encard`, and then
derive most of the `Set.ncard` results as a consequence. Things are done this way to avoid reliance
on the `Finset` API for theorems about infinite sets, and to allow for a refactor that removes or
modifies `Set.ncard` in the future.

Nearly all the theorems for `Set.ncard` require finiteness of one or more of their arguments. We
provide this assumption with a default argument of the form `(hs : s.Finite := by toFinite_tac)`,
where `toFinite_tac` will find an `s.Finite` term in the cases where `s` is a set in a `Finite`
type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the theorem, in which case we only include the ones that are needed, and derive
the other inside the proof. A few of the theorems, such as `ncard_union_le` do not require
finiteness arguments; they are true by coincidence due to junk values.
-/

@[expose] public section

namespace Set

variable {α β : Type*} {s t : Set α}

/--
Definition of `encard` / `encard` 的定义

English:
definition encard
  signature: (s : Set α)
  body: ENat.card s

中文:
定义 encard
  签名: (s : Set α)
  定义体: ENat.card s

Depends on / 依赖: ENat.card
-/
noncomputable def encard (s : Set α) : Nat∞ := ENat.card s

/--
theorem `encard_univ` / 定理 `encard_univ`

English:
theorem encard_univ
  given: (α : Type*)
  proof: by
  rw [encard]; rw [ENat.card_congr (Equiv.Set.univ α)]

中文:
定理 encard_univ
  条件: (α : 类型)
  证明: by
  rw [encard]; rw [ENat.card_congr (Equiv.Set.univ α)]
-/
@[simp] theorem encard_univ (α : Type*) :
    encard (univ : Set α) = ENat.card α := by
  rw [encard]; rw [ENat.card_congr (Equiv.Set.univ α)]

/--
theorem `_root_.ENat.card_coe_set_eq` / 定理 `_root_.ENat.card_coe_set_eq`

English:
theorem _root_.ENat.card_coe_set_eq
  given: (s : Set α)
  statement: ENat.card s = s.encard
  proof: rfl

中文:
定理 _root_.ENat.card_coe_set_eq
  条件: (s : Set α)
  结论: E自然数.card s = s.encard
  证明: rfl
-/
@[simp] theorem _root_.ENat.card_coe_set_eq (s : Set α) : ENat.card s = s.encard := rfl

/--
theorem `Finite.encard_eq_coe_toFinset_card` / 定理 `Finite.encard_eq_coe_toFinset_card`

English:
theorem Finite.encard_eq_coe_toFinset_card
  given: (h : s.Finite)
  statement: s.encard = h.toFinset.card
  proof: by
  have := h.fintype
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [toFinite_toFinset]; rw [toFinset_card]

中文:
定理 Finite.encard_eq_coe_toFinset_card
  条件: (h : s.Finite)
  结论: s.encard = h.toFinset.card
  证明: by
  have := h.fintype
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [toFinite_toFinset]; rw [toFinset_card]

Depends on / 依赖: ENat.card_eq_coe_fintype_card, card_eq_coe_fintype_card, encard, fintype, h.fintype, toFinite_toFinset, toFinset_card
-/
theorem Finite.encard_eq_coe_toFinset_card (h : s.Finite) : s.encard = h.toFinset.card := by
  have := h.fintype
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [toFinite_toFinset]; rw [toFinset_card]

/--
theorem `encard_eq_coe_toFinset_card` / 定理 `encard_eq_coe_toFinset_card`

English:
theorem encard_eq_coe_toFinset_card
  given: (s : Set α) [Fintype s]
  statement: encard s = s.toFinset.card
  proof: by
  have h := toFinite s
  rw [h.encard_eq_coe_toFinset_card]; rw [toFinite_toFinset]

中文:
定理 encard_eq_coe_toFinset_card
  条件: (s : Set α) [Fintype s]
  结论: encard s = s.toFinset.card
  证明: by
  have h := toFinite s
  rw [h.encard_eq_coe_toFinset_card]; rw [toFinite_toFinset]

Depends on / 依赖: encard_eq_coe_toFinset_card, h.encard_eq_coe_toFinset_card, toFinite, toFinite_toFinset
-/
theorem encard_eq_coe_toFinset_card (s : Set α) [Fintype s] : encard s = s.toFinset.card := by
  have h := toFinite s
  rw [h.encard_eq_coe_toFinset_card]; rw [toFinite_toFinset]

/--
theorem `toENat_cardinalMk` / 定理 `toENat_cardinalMk`

English:
theorem toENat_cardinalMk
  given: (s : Set α)
  statement: (Cardinal.mk s).toENat = s.encard
  proof: rfl

中文:
定理 toENat_cardinalMk
  条件: (s : Set α)
  结论: (Cardinal.mk s).toE自然数 = s.encard
  证明: rfl
-/
@[simp] theorem toENat_cardinalMk (s : Set α) : (Cardinal.mk s).toENat = s.encard := rfl

/--
theorem `toENat_cardinalMk_subtype` / 定理 `toENat_cardinalMk_subtype`

English:
theorem toENat_cardinalMk_subtype
  given: (P : α -> Prop)
  proof: rfl

中文:
定理 toENat_cardinalMk_subtype
  条件: (P : α -> 命题)
  证明: rfl
-/
theorem toENat_cardinalMk_subtype (P : α -> Prop) :
    (Cardinal.mk {x // P x}).toENat = {x | P x}.encard :=
  rfl

variable (s) in
/--
theorem `coe_fintypeCard` / 定理 `coe_fintypeCard`

English:
theorem coe_fintypeCard
  given: [Fintype s]
  statement: Fintype.card s = s.encard
  proof: by
  simp [encard_eq_coe_toFinset_card]

中文:
定理 coe_fintypeCard
  条件: [Fintype s]
  结论: Fintype.card s = s.encard
  证明: by
  simp [encard_eq_coe_toFinset_card]

Depends on / 依赖: encard_eq_coe_toFinset_card
-/
theorem coe_fintypeCard [Fintype s] : Fintype.card s = s.encard := by
  simp [encard_eq_coe_toFinset_card]

/--
theorem `encard_coe_eq_coe_finsetCard` / 定理 `encard_coe_eq_coe_finsetCard`

English:
theorem encard_coe_eq_coe_finsetCard
  given: (s : Finset α)
  proof: by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp

中文:
定理 encard_coe_eq_coe_finsetCard
  条件: (s : Finset α)
  证明: by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp
-/
@[simp, norm_cast] theorem encard_coe_eq_coe_finsetCard (s : Finset α) :
    encard (s : Set α) = s.card := by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp

/--
theorem `Infinite.encard_eq` / 定理 `Infinite.encard_eq`

English:
theorem Infinite.encard_eq
  given: {s : Set α} (h : s.Infinite)
  statement: s.encard = ⊤
  proof: by
  have := h.to_subtype
  rw [encard]; rw [ENat.card_eq_top_of_infinite]

中文:
定理 Infinite.encard_eq
  条件: {s : Set α} (h : s.Infinite)
  结论: s.encard = ⊤
  证明: by
  have := h.to_subtype
  rw [encard]; rw [ENat.card_eq_top_of_infinite]
-/
@[simp] theorem Infinite.encard_eq {s : Set α} (h : s.Infinite) : s.encard = ⊤ := by
  have := h.to_subtype
  rw [encard]; rw [ENat.card_eq_top_of_infinite]

/--
theorem `encard_eq_zero` / 定理 `encard_eq_zero`

English:
theorem encard_eq_zero
  statement: s.encard = 0 ↔ s = ∅
  proof: by
  rw [encard]; rw [ENat.card_eq_zero_iff_empty]; rw [isEmpty_subtype]; rw [eq_empty_iff_forall_notMem]

中文:
定理 encard_eq_zero
  结论: s.encard = 0 ↔ s = ∅
  证明: by
  rw [encard]; rw [ENat.card_eq_zero_iff_empty]; rw [isEmpty_subtype]; rw [eq_empty_iff_forall_notMem]
-/
@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard]; rw [ENat.card_eq_zero_iff_empty]; rw [isEmpty_subtype]; rw [eq_empty_iff_forall_notMem]

/--
theorem `encard_empty` / 定理 `encard_empty`

English:
theorem encard_empty
  statement: (∅ : Set α).encard = 0
  proof: by
  rw [encard_eq_zero]

中文:
定理 encard_empty
  结论: (∅ : Set α).encard = 0
  证明: by
  rw [encard_eq_zero]
-/
@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by
  rw [encard_eq_zero]

/--
theorem `nonempty_of_encard_ne_zero` / 定理 `nonempty_of_encard_ne_zero`

English:
theorem nonempty_of_encard_ne_zero
  given: (h : s.encard != 0)
  statement: s.Nonempty
  proof: by
  rwa [nonempty_iff_ne_empty, Ne, ← encard_eq_zero]

中文:
定理 nonempty_of_encard_ne_zero
  条件: (h : s.encard != 0)
  结论: s.Nonempty
  证明: by
  rwa [nonempty_iff_ne_empty, Ne, ← encard_eq_zero]

Depends on / 依赖: encard_eq_zero, nonempty_iff_ne_empty
-/
theorem nonempty_of_encard_ne_zero (h : s.encard != 0) : s.Nonempty := by
  rwa [nonempty_iff_ne_empty, Ne, ← encard_eq_zero]

/--
theorem `encard_ne_zero` / 定理 `encard_ne_zero`

English:
theorem encard_ne_zero
  statement: s.encard != 0 ↔ s.Nonempty
  proof: by
  rw [ne_eq]; rw [encard_eq_zero]; rw [nonempty_iff_ne_empty]

中文:
定理 encard_ne_zero
  结论: s.encard != 0 ↔ s.Nonempty
  证明: by
  rw [ne_eq]; rw [encard_eq_zero]; rw [nonempty_iff_ne_empty]

Depends on / 依赖: encard_eq_zero, ne_eq, nonempty_iff_ne_empty
-/
theorem encard_ne_zero : s.encard != 0 ↔ s.Nonempty := by
  rw [ne_eq]; rw [encard_eq_zero]; rw [nonempty_iff_ne_empty]

/--
theorem `encard_pos` / 定理 `encard_pos`

English:
theorem encard_pos
  statement: 0 < s.encard ↔ s.Nonempty
  proof: by
  rw [pos_iff_ne_zero]; rw [encard_ne_zero]

protected alias ⟨_, Nonempty.encard_pos⟩ := encard_pos

中文:
定理 encard_pos
  结论: 0 < s.encard ↔ s.Nonempty
  证明: by
  rw [pos_iff_ne_zero]; rw [encard_ne_zero]

protected alias ⟨_, Nonempty.encard_pos⟩ := encard_pos
-/
@[simp] theorem encard_pos : 0 < s.encard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero]; rw [encard_ne_zero]

protected alias ⟨_, Nonempty.encard_pos⟩ := encard_pos

/--
theorem `encard_ne_zero_of_mem` / 定理 `encard_ne_zero_of_mem`

English:
theorem encard_ne_zero_of_mem
  given: {a : α} (h : a in s)
  statement: s.encard != 0
  proof: (encard_pos.mpr ⟨a, h⟩).ne.symm

中文:
定理 encard_ne_zero_of_mem
  条件: {a : α} (h : a in s)
  结论: s.encard != 0
  证明: (encard_pos.mpr ⟨a, h⟩).ne.symm

Depends on / 依赖: encard_pos, encard_pos.mpr, ne.symm
-/
theorem encard_ne_zero_of_mem {a : α} (h : a in s) : s.encard != 0 :=
  (encard_pos.mpr ⟨a, h⟩).ne.symm

/--
theorem `encard_singleton` / 定理 `encard_singleton`

English:
theorem encard_singleton
  given: (e : α)
  statement: ({e} : Set α).encard = 1
  proof: by
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [card_singleton]; rw [Nat.cast_eq_one]

中文:
定理 encard_singleton
  条件: (e : α)
  结论: ({e} : Set α).encard = 1
  证明: by
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [card_singleton]; rw [Nat.cast_eq_one]
-/
@[simp] theorem encard_singleton (e : α) : ({e} : Set α).encard = 1 := by
  rw [encard]; rw [ENat.card_eq_coe_fintype_card]; rw [card_singleton]; rw [Nat.cast_eq_one]

/--
theorem `encard_union_eq` / 定理 `encard_union_eq`

English:
theorem encard_union_eq
  given: (h : Disjoint s t)
  statement: (s union t).encard = s.encard + t.encard
  proof: by
  classical
  unfold encard
  simp [ENat.card_congr (Equiv.Set.union h)]

中文:
定理 encard_union_eq
  条件: (h : Disjoint s t)
  结论: (s union t).encard = s.encard + t.encard
  证明: by
  classical
  unfold encard
  simp [ENat.card_congr (Equiv.Set.union h)]

Depends on / 依赖: ENat.card_congr, Equiv.Set.union, card_congr, classical, encard
-/
theorem encard_union_eq (h : Disjoint s t) : (s union t).encard = s.encard + t.encard := by
  classical
  unfold encard
  simp [ENat.card_congr (Equiv.Set.union h)]

/--
theorem `encard_ne_add_one` / 定理 `encard_ne_add_one`

English:
theorem encard_ne_add_one
  given: (a : α)
  proof: by
have : Disjoint {x | x != a} {a} := disjoint_singleton_right.mpr by simp
  replace this := (Set.encard_union_eq this).symm
  have aux : {x | x != a} union {a} = univ := by ext x; simp [eq_or_ne x a]
  rwa [encard_singleton, aux, encard_univ] at this

中文:
定理 encard_ne_add_one
  条件: (a : α)
  证明: by
have : Disjoint {x | x != a} {a} := disjoint_singleton_right.mpr by simp
  replace this := (Set.encard_union_eq this).symm
  have aux : {x | x != a} union {a} = univ := by ext x; simp [eq_or_ne x a]
  rwa [encard_singleton, aux, encard_univ] at this

Depends on / 依赖: Disjoint, Set.encard_union_eq, disjoint_singleton_right, disjoint_singleton_right.mpr, encard_singleton, encard_union_eq, encard_univ, eq_or_ne, replace
-/
theorem encard_ne_add_one (a : α) :
    ({x | x != a}).encard + 1 = ENat.card α := by
have : Disjoint {x | x != a} {a} := disjoint_singleton_right.mpr by simp
  replace this := (Set.encard_union_eq this).symm
  have aux : {x | x != a} union {a} = univ := by ext x; simp [eq_or_ne x a]
  rwa [encard_singleton, aux, encard_univ] at this

/--
theorem `encard_insert_of_notMem` / 定理 `encard_insert_of_notMem`

English:
theorem encard_insert_of_notMem
  given: {a : α} (has : a ∉ s)
  statement: (insert a s).encard = s.encard + 1
  proof: by
  rw [← union_singleton]; rw [encard_union_eq (by simpa)]; rw [encard_singleton]

中文:
定理 encard_insert_of_notMem
  条件: {a : α} (has : a ∉ s)
  结论: (insert a s).encard = s.encard + 1
  证明: by
  rw [← union_singleton]; rw [encard_union_eq (by simpa)]; rw [encard_singleton]

Depends on / 依赖: encard_singleton, encard_union_eq, union_singleton
-/
theorem encard_insert_of_notMem {a : α} (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by
  rw [← union_singleton]; rw [encard_union_eq (by simpa)]; rw [encard_singleton]

/--
theorem `Finite.encard_lt_top` / 定理 `Finite.encard_lt_top`

English:
theorem Finite.encard_lt_top
  given: (h : s.Finite)
  statement: s.encard < ⊤
  proof: by
  induction s, h using Set.Finite.induction_on with
  | empty => simp
  | insert hat _ ht' =>
    rw [encard_insert_of_notMem hat]
    exact lt_tsub_iff_right.1 ht'

中文:
定理 Finite.encard_lt_top
  条件: (h : s.Finite)
  结论: s.encard < ⊤
  证明: by
  induction s, h using Set.Finite.induction_on with
  | empty => simp
  | insert hat _ ht' =>
    rw [encard_insert_of_notMem hat]
    exact lt_tsub_iff_right.1 ht'

Depends on / 依赖: Finite, Set.Finite.induction_on, encard_insert_of_notMem, induction_on, insert, lt_tsub_iff_right
-/
theorem Finite.encard_lt_top (h : s.Finite) : s.encard < ⊤ := by
  induction s, h using Set.Finite.induction_on with
  | empty => simp
  | insert hat _ ht' =>
    rw [encard_insert_of_notMem hat]
    exact lt_tsub_iff_right.1 ht'

/--
theorem `Finite.encard_eq_coe` / 定理 `Finite.encard_eq_coe`

English:
theorem Finite.encard_eq_coe
  given: (h : s.Finite)
  statement: s.encard = ENat.toNat s.encard
  proof: (ENat.natCast_toNat h.encard_lt_top.ne).symm

中文:
定理 Finite.encard_eq_coe
  条件: (h : s.Finite)
  结论: s.encard = E自然数.to自然数 s.encard
  证明: (ENat.natCast_toNat h.encard_lt_top.ne).symm

Depends on / 依赖: ENat.natCast_toNat, encard_lt_top, h.encard_lt_top.ne, natCast_toNat
-/
theorem Finite.encard_eq_coe (h : s.Finite) : s.encard = ENat.toNat s.encard :=
  (ENat.natCast_toNat h.encard_lt_top.ne).symm

/--
theorem `Finite.exists_encard_eq_coe` / 定理 `Finite.exists_encard_eq_coe`

English:
theorem Finite.exists_encard_eq_coe
  given: (h : s.Finite)
  statement: exists (n : Nat), s.encard = n
  proof: ⟨_, h.encard_eq_coe⟩

中文:
定理 Finite.exists_encard_eq_coe
  条件: (h : s.Finite)
  结论: 存在 (n : 自然数), s.encard = n
  证明: ⟨_, h.encard_eq_coe⟩

Depends on / 依赖: encard_eq_coe, h.encard_eq_coe
-/
theorem Finite.exists_encard_eq_coe (h : s.Finite) : exists (n : Nat), s.encard = n :=
  ⟨_, h.encard_eq_coe⟩

/--
theorem `encard_lt_top_iff` / 定理 `encard_lt_top_iff`

English:
theorem encard_lt_top_iff
  statement: s.encard < ⊤ ↔ s.Finite
  proof: ⟨fun h => by_contra fun h' => h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩

中文:
定理 encard_lt_top_iff
  结论: s.encard < ⊤ ↔ s.Finite
  证明: ⟨fun h => by_contra fun h' => h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩
-/
@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite :=
  ⟨fun h => by_contra fun h' => h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩

/--
theorem `encard_eq_top_iff` / 定理 `encard_eq_top_iff`

English:
theorem encard_eq_top_iff
  statement: s.encard = ⊤ ↔ s.Infinite
  proof: by
  contrapose!
  rw [← lt_top_iff_ne_top]; rw [encard_lt_top_iff]

alias ⟨_, encard_eq_top⟩ := encard_eq_top_iff

中文:
定理 encard_eq_top_iff
  结论: s.encard = ⊤ ↔ s.Infinite
  证明: by
  contrapose!
  rw [← lt_top_iff_ne_top]; rw [encard_lt_top_iff]

alias ⟨_, encard_eq_top⟩ := encard_eq_top_iff
-/
@[simp] theorem encard_eq_top_iff : s.encard = ⊤ ↔ s.Infinite := by
  contrapose!
  rw [← lt_top_iff_ne_top]; rw [encard_lt_top_iff]

alias ⟨_, encard_eq_top⟩ := encard_eq_top_iff

/--
theorem `encard_ne_top_iff` / 定理 `encard_ne_top_iff`

English:
theorem encard_ne_top_iff
  statement: s.encard != ⊤ ↔ s.Finite
  proof: by
  simp

中文:
定理 encard_ne_top_iff
  结论: s.encard != ⊤ ↔ s.Finite
  证明: by
  simp
-/
theorem encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite := by
  simp

/--
theorem `finite_of_encard_le_coe` / 定理 `finite_of_encard_le_coe`

English:
theorem finite_of_encard_le_coe
  given: {k : Nat} (h : s.encard <= k)
  statement: s.Finite
  proof: by
  rw [← encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)

中文:
定理 finite_of_encard_le_coe
  条件: {k : 自然数} (h : s.encard <= k)
  结论: s.Finite
  证明: by
  rw [← encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)

Depends on / 依赖: WithTop, WithTop.coe_lt_top, coe_lt_top, encard_lt_top_iff, h.trans_lt, trans_lt
-/
theorem finite_of_encard_le_coe {k : Nat} (h : s.encard <= k) : s.Finite := by
  rw [← encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)

/--
theorem `finite_of_encard_eq_coe` / 定理 `finite_of_encard_eq_coe`

English:
theorem finite_of_encard_eq_coe
  given: {k : Nat} (h : s.encard = k)
  statement: s.Finite
  proof: finite_of_encard_le_coe h.le

中文:
定理 finite_of_encard_eq_coe
  条件: {k : 自然数} (h : s.encard = k)
  结论: s.Finite
  证明: finite_of_encard_le_coe h.le

Depends on / 依赖: finite_of_encard_le_coe, h.le
-/
theorem finite_of_encard_eq_coe {k : Nat} (h : s.encard = k) : s.Finite :=
  finite_of_encard_le_coe h.le

/--
theorem `encard_le_coe_iff` / 定理 `encard_le_coe_iff`

English:
theorem encard_le_coe_iff
  given: {k : Nat}
  statement: s.encard <= k ↔ s.Finite ∧ exists (n₀ : Nat), s.encard = n₀ ∧ n₀ <= k
  proof: ⟨fun h => ⟨finite_of_encard_le_coe h, by rwa [ENat.le_natCast_iff] at h⟩,
    fun ⟨_,⟨n₀,hs, hle⟩⟩ => by rwa [hs, Nat.cast_le]⟩

@[simp]

中文:
定理 encard_le_coe_iff
  条件: {k : 自然数}
  结论: s.encard <= k ↔ s.Finite ∧ 存在 (n₀ : 自然数), s.encard = n₀ ∧ n₀ <= k
  证明: ⟨fun h => ⟨finite_of_encard_le_coe h, by rwa [ENat.le_natCast_iff] at h⟩,
    fun ⟨_,⟨n₀,hs, hle⟩⟩ => by rwa [hs, Nat.cast_le]⟩

@[simp]

Depends on / 依赖: ENat.le_natCast_iff, Nat.cast_le, cast_le, finite_of_encard_le_coe, le_natCast_iff
-/
theorem encard_le_coe_iff {k : Nat} : s.encard <= k ↔ s.Finite ∧ exists (n₀ : Nat), s.encard = n₀ ∧ n₀ <= k :=
  ⟨fun h => ⟨finite_of_encard_le_coe h, by rwa [ENat.le_natCast_iff] at h⟩,
    fun ⟨_,⟨n₀,hs, hle⟩⟩ => by rwa [hs, Nat.cast_le]⟩

@[simp]
/--
theorem `encard_prod` / 定理 `encard_prod`

English:
theorem encard_prod
  given: {s : Set α} {t : Set β}
  statement: (s ×ˢ t).encard = s.encard * t.encard
  proof: by
  unfold encard
  simp [ENat.card_congr (Equiv.Set.prod ..)]

@[simp]

中文:
定理 encard_prod
  条件: {s : Set α} {t : Set β}
  结论: (s ×ˢ t).encard = s.encard * t.encard
  证明: by
  unfold encard
  simp [ENat.card_congr (Equiv.Set.prod ..)]

@[simp]

Depends on / 依赖: ENat.card_congr, Equiv.Set.prod, card_congr, encard
-/
theorem encard_prod {s : Set α} {t : Set β} : (s ×ˢ t).encard = s.encard * t.encard := by
  unfold encard
  simp [ENat.card_congr (Equiv.Set.prod ..)]

@[simp]
/--
theorem `encard_pi_eq_prod_encard` / 定理 `encard_pi_eq_prod_encard`

English:
theorem encard_pi_eq_prod_encard
  given: [h : Fintype α] {ι : α -> Type*} {s : forall i : α, Set (ι i)}
  proof: by
  unfold encard ENat.card
  simp [Cardinal.mk_congr (Equiv.Set.univPi s), Cardinal.prod_eq_of_fintype]

中文:
定理 encard_pi_eq_prod_encard
  条件: [h : Fintype α] {ι : α -> 类型} {s : 对任意 i : α, Set (ι i)}
  证明: by
  unfold encard ENat.card
  simp [Cardinal.mk_congr (Equiv.Set.univPi s), Cardinal.prod_eq_of_fintype]

Depends on / 依赖: Cardinal, Cardinal.mk_congr, Cardinal.prod_eq_of_fintype, ENat.card, Equiv.Set.univPi, encard, mk_congr, prod_eq_of_fintype, univPi
-/
theorem encard_pi_eq_prod_encard [h : Fintype α] {ι : α -> Type*} {s : forall i : α, Set (ι i)} :
    (Set.pi Set.univ s).encard = ∏ i, (s i).encard := by
  unfold encard ENat.card
  simp [Cardinal.mk_congr (Equiv.Set.univPi s), Cardinal.prod_eq_of_fintype]

section Lattice

@[gcongr]
/--
theorem `encard_le_encard` / 定理 `encard_le_encard`

English:
theorem encard_le_encard
  given: (h : s subseteq t)
  statement: s.encard <= t.encard
  proof: by
  rw [← union_sdiff_cancel h]; rw [encard_union_eq disjoint_sdiff_right]; exact le_self_add

中文:
定理 encard_le_encard
  条件: (h : s subseteq t)
  结论: s.encard <= t.encard
  证明: by
  rw [← union_sdiff_cancel h]; rw [encard_union_eq disjoint_sdiff_right]; exact le_self_add

Depends on / 依赖: disjoint_sdiff_right, encard_union_eq, le_self_add, union_sdiff_cancel
-/
theorem encard_le_encard (h : s subseteq t) : s.encard <= t.encard := by
  rw [← union_sdiff_cancel h]; rw [encard_union_eq disjoint_sdiff_right]; exact le_self_add

/--
theorem `encard_le_card` / 定理 `encard_le_card`

English:
theorem encard_le_card
  statement: s.encard <= ENat.card α
  proof: encard_univ _ ▸ encard_le_encard s.subset_univ

中文:
定理 encard_le_card
  结论: s.encard <= E自然数.card α
  证明: encard_univ _ ▸ encard_le_encard s.subset_univ

Depends on / 依赖: encard_le_encard, encard_univ, s.subset_univ, subset_univ
-/
theorem encard_le_card : s.encard <= ENat.card α :=
  encard_univ _ ▸ encard_le_encard s.subset_univ

/--
theorem `encard_mono` / 定理 `encard_mono`

English:
theorem encard_mono
  given: {α : Type*}
  statement: Monotone (encard : Set α -> Nat∞)
  proof: fun _ _ => encard_le_encard

中文:
定理 encard_mono
  条件: {α : 类型}
  结论: Monotone (encard : Set α -> 自然数∞)
  证明: fun _ _ => encard_le_encard

Depends on / 依赖: encard_le_encard
-/
theorem encard_mono {α : Type*} : Monotone (encard : Set α -> Nat∞) :=
  fun _ _ => encard_le_encard

/--
theorem `encard_sdiff_add_encard_of_subset` / 定理 `encard_sdiff_add_encard_of_subset`

English:
theorem encard_sdiff_add_encard_of_subset
  given: (h : s subseteq t)
  statement: (t \ s).encard + s.encard = t.encard
  proof: by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_of_subset h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_of_subset := encard_sdiff_add_encard_of_subset

中文:
定理 encard_sdiff_add_encard_of_subset
  条件: (h : s subseteq t)
  结论: (t \ s).encard + s.encard = t.encard
  证明: by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_of_subset h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_of_subset := encard_sdiff_add_encard_of_subset

Depends on / 依赖: disjoint_sdiff_left, encard_union_eq, sdiff_union_of_subset
-/
theorem encard_sdiff_add_encard_of_subset (h : s subseteq t) : (t \ s).encard + s.encard = t.encard := by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_of_subset h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_of_subset := encard_sdiff_add_encard_of_subset

/--
theorem `encard_sdiff` / 定理 `encard_sdiff`

English:
theorem encard_sdiff
  given: (h : s subseteq t) (hs : s.Finite)
  proof: by
  rw [← @Set.encard_sdiff_add_encard_of_subset _ s t h]
  exact (ENat.addLECancellable_of_ne_top <| encard_ne_top_iff.mpr hs).eq_tsub_of_add_eq rfl

@[deprecated (since := "2026-06-03")] alias encard_diff := encard_sdiff

中文:
定理 encard_sdiff
  条件: (h : s subseteq t) (hs : s.Finite)
  证明: by
  rw [← @Set.encard_sdiff_add_encard_of_subset _ s t h]
  exact (ENat.addLECancellable_of_ne_top <| encard_ne_top_iff.mpr hs).eq_tsub_of_add_eq rfl

@[deprecated (since := "2026-06-03")] alias encard_diff := encard_sdiff

Depends on / 依赖: ENat.addLECancellable_of_ne_top, Set.encard_sdiff_add_encard_of_subset, addLECancellable_of_ne_top, encard_ne_top_iff, encard_ne_top_iff.mpr, encard_sdiff_add_encard_of_subset, eq_tsub_of_add_eq
-/
theorem encard_sdiff (h : s subseteq t) (hs : s.Finite) :
    (t \ s).encard = t.encard - s.encard := by
  rw [← @Set.encard_sdiff_add_encard_of_subset _ s t h]
  exact (ENat.addLECancellable_of_ne_top <| encard_ne_top_iff.mpr hs).eq_tsub_of_add_eq rfl

@[deprecated (since := "2026-06-03")] alias encard_diff := encard_sdiff

/--
theorem `one_le_encard_iff_nonempty` / 定理 `one_le_encard_iff_nonempty`

English:
theorem one_le_encard_iff_nonempty
  statement: 1 <= s.encard ↔ s.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← encard_eq_zero]; rw [Order.one_le_iff_ne_zero]

中文:
定理 one_le_encard_iff_nonempty
  结论: 1 <= s.encard ↔ s.Nonempty
  证明: by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← encard_eq_zero]; rw [Order.one_le_iff_ne_zero]
-/
@[simp] theorem one_le_encard_iff_nonempty : 1 <= s.encard ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← encard_eq_zero]; rw [Order.one_le_iff_ne_zero]

/--
lemma `encard_lt_one` / 引理 `encard_lt_one`

English:
lemma encard_lt_one
  statement: s.encard < 1 ↔ s = ∅
  proof: by simp

中文:
引理 encard_lt_one
  结论: s.encard < 1 ↔ s = ∅
  证明: by simp
-/
lemma encard_lt_one : s.encard < 1 ↔ s = ∅ := by simp

/--
theorem `encard_sdiff_add_encard_inter` / 定理 `encard_sdiff_add_encard_inter`

English:
theorem encard_sdiff_add_encard_inter
  given: (s t : Set α)
  proof: by
  rw [← encard_union_eq disjoint_sdiff_inter]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_inter := encard_sdiff_add_encard_inter

中文:
定理 encard_sdiff_add_encard_inter
  条件: (s t : Set α)
  证明: by
  rw [← encard_union_eq disjoint_sdiff_inter]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_inter := encard_sdiff_add_encard_inter

Depends on / 依赖: disjoint_sdiff_inter, encard_union_eq, sdiff_union_inter
-/
theorem encard_sdiff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s inter t).encard = s.encard := by
  rw [← encard_union_eq disjoint_sdiff_inter]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias encard_diff_add_encard_inter := encard_sdiff_add_encard_inter

/--
theorem `encard_union_add_encard_inter` / 定理 `encard_union_add_encard_inter`

English:
theorem encard_union_add_encard_inter
  given: (s t : Set α)
  proof: by
  rw [← sdiff_union_self]; rw [encard_union_eq disjoint_sdiff_left]; rw [add_right_comm]; rw [encard_sdiff_add_encard_inter]

中文:
定理 encard_union_add_encard_inter
  条件: (s t : Set α)
  证明: by
  rw [← sdiff_union_self]; rw [encard_union_eq disjoint_sdiff_left]; rw [add_right_comm]; rw [encard_sdiff_add_encard_inter]

Depends on / 依赖: add_right_comm, disjoint_sdiff_left, encard_sdiff_add_encard_inter, encard_union_eq, sdiff_union_self
-/
theorem encard_union_add_encard_inter (s t : Set α) :
    (s union t).encard + (s inter t).encard = s.encard + t.encard := by
  rw [← sdiff_union_self]; rw [encard_union_eq disjoint_sdiff_left]; rw [add_right_comm]; rw [encard_sdiff_add_encard_inter]

/--
theorem `encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff` / 定理 `encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff`

English:
theorem encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff
  given: (h : (s inter t).Finite)
  proof: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [(ENat.addLECancellable_of_lt_top h.encard_lt_top).inj_left]

@[deprecated (since := "2026-06-03")]
alias encard_eq_encard_iff_encard_diff_eq_encard_diff :=
  encard_eq_encard_iff_encard_

中文:
定理 encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff
  条件: (h : (s inter t).Finite)
  证明: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [(ENat.addLECancellable_of_lt_top h.encard_lt_top).inj_left]

@[deprecated (since := "2026-06-03")]
alias encard_eq_encard_iff_encard_diff_eq_encard_diff :=
  encard_eq_encard_iff_encard_

Depends on / 依赖: ENat.addLECancellable_of_lt_top, addLECancellable_of_lt_top, encard_lt_top, encard_sdiff_add_encard_inter, h.encard_lt_top, inj_left, inter_comm
-/
theorem encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff (h : (s inter t).Finite) :
    s.encard = t.encard ↔ (s \ t).encard = (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [(ENat.addLECancellable_of_lt_top h.encard_lt_top).inj_left]

@[deprecated (since := "2026-06-03")]
alias encard_eq_encard_iff_encard_diff_eq_encard_diff :=
  encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff

/--
theorem `encard_le_encard_iff_encard_sdiff_le_encard_sdiff` / 定理 `encard_le_encard_iff_encard_sdiff_le_encard_sdiff`

English:
theorem encard_le_encard_iff_encard_sdiff_le_encard_sdiff
  given: (h : (s inter t).Finite)
  proof: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_le_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_iff_encard_diff_le_encard_diff :=
  encard_le_encard_iff_encard_sdiff_le_encar

中文:
定理 encard_le_encard_iff_encard_sdiff_le_encard_sdiff
  条件: (h : (s inter t).Finite)
  证明: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_le_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_iff_encard_diff_le_encard_diff :=
  encard_le_encard_iff_encard_sdiff_le_encar

Depends on / 依赖: ENat.add_le_add_iff_right, add_le_add_iff_right, encard_lt_top, encard_sdiff_add_encard_inter, h.encard_lt_top.ne, inter_comm
-/
theorem encard_le_encard_iff_encard_sdiff_le_encard_sdiff (h : (s inter t).Finite) :
    s.encard <= t.encard ↔ (s \ t).encard <= (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_le_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_iff_encard_diff_le_encard_diff :=
  encard_le_encard_iff_encard_sdiff_le_encard_sdiff

/--
theorem `encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff` / 定理 `encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff`

English:
theorem encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff
  given: (h : (s inter t).Finite)
  proof: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_lt_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_lt_encard_iff_encard_diff_lt_encard_diff :=
  encard_lt_encard_iff_encard_sdiff_lt_encar

中文:
定理 encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff
  条件: (h : (s inter t).Finite)
  证明: by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_lt_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_lt_encard_iff_encard_diff_lt_encard_diff :=
  encard_lt_encard_iff_encard_sdiff_lt_encar

Depends on / 依赖: ENat.add_lt_add_iff_right, add_lt_add_iff_right, encard_lt_top, encard_sdiff_add_encard_inter, h.encard_lt_top.ne, inter_comm
-/
theorem encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff (h : (s inter t).Finite) :
    s.encard < t.encard ↔ (s \ t).encard < (t \ s).encard := by
  rw [← encard_sdiff_add_encard_inter s t]; rw [← encard_sdiff_add_encard_inter t s]; rw [inter_comm t s]; rw [ENat.add_lt_add_iff_right h.encard_lt_top.ne]

@[deprecated (since := "2026-06-03")]
alias encard_lt_encard_iff_encard_diff_lt_encard_diff :=
  encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff

/--
theorem `encard_union_le` / 定理 `encard_union_le`

English:
theorem encard_union_le
  given: (s t : Set α)
  statement: (s union t).encard <= s.encard + t.encard
  proof: by
  rw [← encard_union_add_encard_inter]; exact le_self_add

中文:
定理 encard_union_le
  条件: (s t : Set α)
  结论: (s union t).encard <= s.encard + t.encard
  证明: by
  rw [← encard_union_add_encard_inter]; exact le_self_add

Depends on / 依赖: encard_union_add_encard_inter, le_self_add
-/
theorem encard_union_le (s t : Set α) : (s union t).encard <= s.encard + t.encard := by
  rw [← encard_union_add_encard_inter]; exact le_self_add

/--
theorem `finite_iff_finite_of_encard_eq_encard` / 定理 `finite_iff_finite_of_encard_eq_encard`

English:
theorem finite_iff_finite_of_encard_eq_encard
  given: (h : s.encard = t.encard)
  statement: s.Finite ↔ t.Finite
  proof: by
  rw [← encard_lt_top_iff]; rw [← encard_lt_top_iff]; rw [h]

中文:
定理 finite_iff_finite_of_encard_eq_encard
  条件: (h : s.encard = t.encard)
  结论: s.Finite ↔ t.Finite
  证明: by
  rw [← encard_lt_top_iff]; rw [← encard_lt_top_iff]; rw [h]

Depends on / 依赖: encard_lt_top_iff
-/
theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [← encard_lt_top_iff]; rw [← encard_lt_top_iff]; rw [h]

/--
theorem `infinite_iff_infinite_of_encard_eq_encard` / 定理 `infinite_iff_infinite_of_encard_eq_encard`

English:
theorem infinite_iff_infinite_of_encard_eq_encard
  given: (h : s.encard = t.encard)
  proof: by rw [← encard_eq_top_iff, h, encard_eq_top_iff]

中文:
定理 infinite_iff_infinite_of_encard_eq_encard
  条件: (h : s.encard = t.encard)
  证明: by rw [← encard_eq_top_iff, h, encard_eq_top_iff]

Depends on / 依赖: encard_eq_top_iff
-/
theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [← encard_eq_top_iff, h, encard_eq_top_iff]

/--
theorem `Finite.finite_of_encard_le` / 定理 `Finite.finite_of_encard_le`

English:
theorem Finite.finite_of_encard_le
  statement: {s : Set α} {t : Set β} (hs : s.Finite)
  proof: encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

中文:
定理 Finite.finite_of_encard_le
  结论: {s : Set α} {t : Set β} (hs : s.Finite)
  证明: encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

Depends on / 依赖: encard_lt_top, encard_lt_top_iff, h.trans_lt, hs.encard_lt_top, trans_lt
-/
theorem Finite.finite_of_encard_le {s : Set α} {t : Set β} (hs : s.Finite)
    (h : t.encard <= s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

/--
lemma `Finite.eq_of_subset_of_encard_le'` / 引理 `Finite.eq_of_subset_of_encard_le'`

English:
lemma Finite.eq_of_subset_of_encard_le'
  given: (ht : t.Finite) (hst : s subseteq t) (hts : t.encard <= s.encard)
  proof: by
  rw [← zero_add (a := encard s)]; rw [← encard_sdiff_add_encard_of_subset hst] at hts
  have hdiff :=
    (ENat.addLECancellable_of_lt_top (ht.subset hst).encard_lt_top).add_le_add_iff_right.mp hts
  rw [nonpos_iff_eq_zero]; rw [encard_eq_zero]; rw [sdiff_eq_empty] at hdiff
  exact hst.antisymm 

中文:
引理 Finite.eq_of_subset_of_encard_le'
  条件: (ht : t.Finite) (hst : s subseteq t) (hts : t.encard <= s.encard)
  证明: by
  rw [← zero_add (a := encard s)]; rw [← encard_sdiff_add_encard_of_subset hst] at hts
  have hdiff :=
    (ENat.addLECancellable_of_lt_top (ht.subset hst).encard_lt_top).add_le_add_iff_right.mp hts
  rw [nonpos_iff_eq_zero]; rw [encard_eq_zero]; rw [sdiff_eq_empty] at hdiff
  exact hst.antisymm 

Depends on / 依赖: ENat.addLECancellable_of_lt_top, addLECancellable_of_lt_top, add_le_add_iff_right, add_le_add_iff_right.mp, antisymm, encard, encard_eq_zero, encard_lt_top, encard_sdiff_add_encard_of_subset, hst.antisymm, ht.subset, nonpos_iff_eq_zero, sdiff_eq_empty, subset, zero_add
-/
lemma Finite.eq_of_subset_of_encard_le' (ht : t.Finite) (hst : s subseteq t) (hts : t.encard <= s.encard) :
    s = t := by
  rw [← zero_add (a := encard s)]; rw [← encard_sdiff_add_encard_of_subset hst] at hts
  have hdiff :=
    (ENat.addLECancellable_of_lt_top (ht.subset hst).encard_lt_top).add_le_add_iff_right.mp hts
  rw [nonpos_iff_eq_zero]; rw [encard_eq_zero]; rw [sdiff_eq_empty] at hdiff
  exact hst.antisymm hdiff

/--
theorem `Finite.eq_of_subset_of_encard_le` / 定理 `Finite.eq_of_subset_of_encard_le`

English:
theorem Finite.eq_of_subset_of_encard_le
  statement: (hs : s.Finite) (hst : s subseteq t)
  proof: (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le' hst hts

中文:
定理 Finite.eq_of_subset_of_encard_le
  结论: (hs : s.Finite) (hst : s subseteq t)
  证明: (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le' hst hts

Depends on / 依赖: eq_of_subset_of_encard_le, finite_of_encard_le, hs.finite_of_encard_le
-/
theorem Finite.eq_of_subset_of_encard_le (hs : s.Finite) (hst : s subseteq t)
    (hts : t.encard <= s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le' hst hts

/--
theorem `Finite.encard_lt_encard` / 定理 `Finite.encard_lt_encard`

English:
theorem Finite.encard_lt_encard
  given: (hs : s.Finite) (h : s ⊂ t)
  statement: s.encard < t.encard
  proof: (encard_mono h.subset).lt_of_ne fun he => h.ne (hs.eq_of_subset_of_encard_le h.subset he.symm.le)

中文:
定理 Finite.encard_lt_encard
  条件: (hs : s.Finite) (h : s ⊂ t)
  结论: s.encard < t.encard
  证明: (encard_mono h.subset).lt_of_ne fun he => h.ne (hs.eq_of_subset_of_encard_le h.subset he.symm.le)

Depends on / 依赖: encard_mono, eq_of_subset_of_encard_le, h.ne, h.subset, he.symm.le, hs.eq_of_subset_of_encard_le, lt_of_ne, subset
-/
theorem Finite.encard_lt_encard (hs : s.Finite) (h : s ⊂ t) : s.encard < t.encard :=
  (encard_mono h.subset).lt_of_ne fun he => h.ne (hs.eq_of_subset_of_encard_le h.subset he.symm.le)

/--
theorem `encard_strictMono` / 定理 `encard_strictMono`

English:
theorem encard_strictMono
  given: [Finite α]
  statement: StrictMono (encard : Set α -> Nat∞)
  proof: fun _ _ h => (toFinite _).encard_lt_encard h

中文:
定理 encard_strictMono
  条件: [Finite α]
  结论: StrictMono (encard : Set α -> 自然数∞)
  证明: fun _ _ h => (toFinite _).encard_lt_encard h

Depends on / 依赖: encard_lt_encard, toFinite
-/
theorem encard_strictMono [Finite α] : StrictMono (encard : Set α -> Nat∞) :=
  fun _ _ h => (toFinite _).encard_lt_encard h

/--
theorem `Finite.encard_strictMonoOn` / 定理 `Finite.encard_strictMonoOn`

English:
theorem Finite.encard_strictMonoOn
  statement: StrictMonoOn (α := Set α) encard (Set.ofPred Set.Finite)
  proof: fun _ hs _ _ hlt => hs.encard_lt_encard hlt

中文:
定理 Finite.encard_strictMonoOn
  结论: StrictMonoOn (α := Set α) encard (Set.ofPred Set.Finite)
  证明: fun _ hs _ _ hlt => hs.encard_lt_encard hlt

Depends on / 依赖: Finite, Set.Finite, Set.ofPred, encard, ofPred
-/
theorem Finite.encard_strictMonoOn : StrictMonoOn (α := Set α) encard (Set.ofPred Set.Finite) :=
  fun _ hs _ _ hlt => hs.encard_lt_encard hlt

/--
theorem `Finite.encard_lt_card` / 定理 `Finite.encard_lt_card`

English:
theorem Finite.encard_lt_card
  given: (hfin : s.Finite) (hne : s != univ)
  statement: s.encard < ENat.card α
  proof: encard_univ α ▸ hfin.encard_lt_encard (ssubset_univ_iff.mpr hne)

中文:
定理 Finite.encard_lt_card
  条件: (hfin : s.Finite) (hne : s != univ)
  结论: s.encard < E自然数.card α
  证明: encard_univ α ▸ hfin.encard_lt_encard (ssubset_univ_iff.mpr hne)

Depends on / 依赖: encard_lt_encard, encard_univ, hfin.encard_lt_encard, ssubset_univ_iff, ssubset_univ_iff.mpr
-/
theorem Finite.encard_lt_card (hfin : s.Finite) (hne : s != univ) : s.encard < ENat.card α :=
  encard_univ α ▸ hfin.encard_lt_encard (ssubset_univ_iff.mpr hne)

/--
theorem `encard_sdiff_add_encard` / 定理 `encard_sdiff_add_encard`

English:
theorem encard_sdiff_add_encard
  given: (s t : Set α)
  statement: (s \ t).encard + t.encard = (s union t).encard
  proof: by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias encard_diff_add_encard := encard_sdiff_add_encard

中文:
定理 encard_sdiff_add_encard
  条件: (s t : Set α)
  结论: (s \ t).encard + t.encard = (s union t).encard
  证明: by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias encard_diff_add_encard := encard_sdiff_add_encard

Depends on / 依赖: disjoint_sdiff_left, encard_union_eq, sdiff_union_self
-/
theorem encard_sdiff_add_encard (s t : Set α) : (s \ t).encard + t.encard = (s union t).encard := by
  rw [← encard_union_eq disjoint_sdiff_left]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias encard_diff_add_encard := encard_sdiff_add_encard

/--
theorem `encard_le_encard_sdiff_add_encard` / 定理 `encard_le_encard_sdiff_add_encard`

English:
theorem encard_le_encard_sdiff_add_encard
  given: (s t : Set α)
  statement: s.encard <= (s \ t).encard + t.encard
  proof: (encard_mono subset_union_left).trans_eq (encard_sdiff_add_encard _ _).symm

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_diff_add_encard := encard_le_encard_sdiff_add_encard

中文:
定理 encard_le_encard_sdiff_add_encard
  条件: (s t : Set α)
  结论: s.encard <= (s \ t).encard + t.encard
  证明: (encard_mono subset_union_left).trans_eq (encard_sdiff_add_encard _ _).symm

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_diff_add_encard := encard_le_encard_sdiff_add_encard

Depends on / 依赖: encard_mono, encard_sdiff_add_encard, subset_union_left, trans_eq
-/
theorem encard_le_encard_sdiff_add_encard (s t : Set α) : s.encard <= (s \ t).encard + t.encard :=
  (encard_mono subset_union_left).trans_eq (encard_sdiff_add_encard _ _).symm

@[deprecated (since := "2026-06-03")]
alias encard_le_encard_diff_add_encard := encard_le_encard_sdiff_add_encard

/--
theorem `tsub_encard_le_encard_sdiff` / 定理 `tsub_encard_le_encard_sdiff`

English:
theorem tsub_encard_le_encard_sdiff
  given: (s t : Set α)
  statement: s.encard - t.encard <= (s \ t).encard
  proof: by
  rw [tsub_le_iff_left]; rw [add_comm]; apply encard_le_encard_sdiff_add_encard

@[deprecated (since := "2026-06-03")]
alias tsub_encard_le_encard_diff := tsub_encard_le_encard_sdiff

中文:
定理 tsub_encard_le_encard_sdiff
  条件: (s t : Set α)
  结论: s.encard - t.encard <= (s \ t).encard
  证明: by
  rw [tsub_le_iff_left]; rw [add_comm]; apply encard_le_encard_sdiff_add_encard

@[deprecated (since := "2026-06-03")]
alias tsub_encard_le_encard_diff := tsub_encard_le_encard_sdiff

Depends on / 依赖: add_comm, encard_le_encard_sdiff_add_encard, tsub_le_iff_left
-/
theorem tsub_encard_le_encard_sdiff (s t : Set α) : s.encard - t.encard <= (s \ t).encard := by
  rw [tsub_le_iff_left]; rw [add_comm]; apply encard_le_encard_sdiff_add_encard

@[deprecated (since := "2026-06-03")]
alias tsub_encard_le_encard_diff := tsub_encard_le_encard_sdiff

/--
theorem `encard_add_encard_compl` / 定理 `encard_add_encard_compl`

English:
theorem encard_add_encard_compl
  given: (s : Set α)
  statement: s.encard + sᶜ.encard = (univ : Set α).encard
  proof: by
  rw [← encard_union_eq disjoint_compl_right]; rw [union_compl_self]

中文:
定理 encard_add_encard_compl
  条件: (s : Set α)
  结论: s.encard + sᶜ.encard = (univ : Set α).encard
  证明: by
  rw [← encard_union_eq disjoint_compl_right]; rw [union_compl_self]

Depends on / 依赖: disjoint_compl_right, encard_union_eq, union_compl_self
-/
theorem encard_add_encard_compl (s : Set α) : s.encard + sᶜ.encard = (univ : Set α).encard := by
  rw [← encard_union_eq disjoint_compl_right]; rw [union_compl_self]

end Lattice

section InsertErase

variable {a b : α}

/--
theorem `encard_insert_le` / 定理 `encard_insert_le`

English:
theorem encard_insert_le
  given: (s : Set α) (x : α)
  statement: (insert x s).encard <= s.encard + 1
  proof: by
  rw [← union_singleton]; rw [← encard_singleton x]; apply encard_union_le

中文:
定理 encard_insert_le
  条件: (s : Set α) (x : α)
  结论: (insert x s).encard <= s.encard + 1
  证明: by
  rw [← union_singleton]; rw [← encard_singleton x]; apply encard_union_le

Depends on / 依赖: encard_singleton, encard_union_le, union_singleton
-/
theorem encard_insert_le (s : Set α) (x : α) : (insert x s).encard <= s.encard + 1 := by
  rw [← union_singleton]; rw [← encard_singleton x]; apply encard_union_le

/--
theorem `one_le_encard_insert` / 定理 `one_le_encard_insert`

English:
theorem one_le_encard_insert
  given: (s : Set α)
  statement: 1 <= (insert a s).encard
  proof: Order.one_le_iff_ne_zero.mpr encard_ne_zero_of_mem (mem_insert a s)

中文:
定理 one_le_encard_insert
  条件: (s : Set α)
  结论: 1 <= (insert a s).encard
  证明: Order.one_le_iff_ne_zero.mpr encard_ne_zero_of_mem (mem_insert a s)

Depends on / 依赖: Order.one_le_iff_ne_zero.mpr, encard_ne_zero_of_mem, mem_insert, one_le_iff_ne_zero
-/
theorem one_le_encard_insert (s : Set α) : 1 <= (insert a s).encard :=
Order.one_le_iff_ne_zero.mpr encard_ne_zero_of_mem (mem_insert a s)

/--
theorem `encard_singleton_inter` / 定理 `encard_singleton_inter`

English:
theorem encard_singleton_inter
  given: (s : Set α) (x : α)
  statement: ({x} inter s).encard <= 1
  proof: by
  grw [← encard_singleton x, inter_subset_left]

中文:
定理 encard_singleton_inter
  条件: (s : Set α) (x : α)
  结论: ({x} inter s).encard <= 1
  证明: by
  grw [← encard_singleton x, inter_subset_left]

Depends on / 依赖: encard_singleton, inter_subset_left
-/
theorem encard_singleton_inter (s : Set α) (x : α) : ({x} inter s).encard <= 1 := by
  grw [← encard_singleton x, inter_subset_left]

/--
theorem `encard_sdiff_singleton_add_one` / 定理 `encard_sdiff_singleton_add_one`

English:
theorem encard_sdiff_singleton_add_one
  given: (h : a in s)
  proof: by
  rw [← encard_insert_of_notMem (fun h => h.2 rfl)]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_add_one := encard_sdiff_singleton_add_one

中文:
定理 encard_sdiff_singleton_add_one
  条件: (h : a in s)
  证明: by
  rw [← encard_insert_of_notMem (fun h => h.2 rfl)]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_add_one := encard_sdiff_singleton_add_one

Depends on / 依赖: encard_insert_of_notMem, insert_eq_of_mem, insert_sdiff_singleton
-/
theorem encard_sdiff_singleton_add_one (h : a in s) :
    (s \ {a}).encard + 1 = s.encard := by
  rw [← encard_insert_of_notMem (fun h => h.2 rfl)]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem h]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_add_one := encard_sdiff_singleton_add_one

/--
theorem `encard_sdiff_singleton_of_mem` / 定理 `encard_sdiff_singleton_of_mem`

English:
theorem encard_sdiff_singleton_of_mem
  given: (h : a in s)
  proof: by
  rw [← encard_sdiff_singleton_add_one h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_of_mem := encard_sdiff_singleton_of_mem

中文:
定理 encard_sdiff_singleton_of_mem
  条件: (h : a in s)
  证明: by
  rw [← encard_sdiff_singleton_add_one h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_of_mem := encard_sdiff_singleton_of_mem

Depends on / 依赖: ENat.addLECancellable_of_ne_top, ENat.one_ne_top, addLECancellable_of_ne_top, add_tsub_cancel_right, encard_sdiff_singleton_add_one, one_ne_top
-/
theorem encard_sdiff_singleton_of_mem (h : a in s) :
    (s \ {a}).encard = s.encard - 1 := by
  rw [← encard_sdiff_singleton_add_one h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")]
alias encard_diff_singleton_of_mem := encard_sdiff_singleton_of_mem

/--
theorem `encard_tsub_one_le_encard_sdiff_singleton` / 定理 `encard_tsub_one_le_encard_sdiff_singleton`

English:
theorem encard_tsub_one_le_encard_sdiff_singleton
  given: (s : Set α) (x : α)
  proof: by
  rw [← encard_singleton x]; apply tsub_encard_le_encard_sdiff

@[deprecated (since := "2026-06-03")]
alias encard_tsub_one_le_encard_diff_singleton := encard_tsub_one_le_encard_sdiff_singleton

中文:
定理 encard_tsub_one_le_encard_sdiff_singleton
  条件: (s : Set α) (x : α)
  证明: by
  rw [← encard_singleton x]; apply tsub_encard_le_encard_sdiff

@[deprecated (since := "2026-06-03")]
alias encard_tsub_one_le_encard_diff_singleton := encard_tsub_one_le_encard_sdiff_singleton

Depends on / 依赖: encard_singleton, tsub_encard_le_encard_sdiff
-/
theorem encard_tsub_one_le_encard_sdiff_singleton (s : Set α) (x : α) :
    s.encard - 1 <= (s \ {x}).encard := by
  rw [← encard_singleton x]; apply tsub_encard_le_encard_sdiff

@[deprecated (since := "2026-06-03")]
alias encard_tsub_one_le_encard_diff_singleton := encard_tsub_one_le_encard_sdiff_singleton

/--
theorem `encard_exchange` / 定理 `encard_exchange`

English:
theorem encard_exchange
  given: (ha : a ∉ s) (hb : b in s)
  statement: (insert a (s \ {b})).encard = s.encard
  proof: by
  rw [encard_insert_of_notMem]; rw [encard_sdiff_singleton_add_one hb]
  simp_all only [mem_sdiff, mem_singleton_iff, false_and, not_false_eq_true]

中文:
定理 encard_exchange
  条件: (ha : a ∉ s) (hb : b in s)
  结论: (insert a (s \ {b})).encard = s.encard
  证明: by
  rw [encard_insert_of_notMem]; rw [encard_sdiff_singleton_add_one hb]
  simp_all only [mem_sdiff, mem_singleton_iff, false_and, not_false_eq_true]

Depends on / 依赖: encard_insert_of_notMem, encard_sdiff_singleton_add_one, false_and, mem_sdiff, mem_singleton_iff, not_false_eq_true
-/
theorem encard_exchange (ha : a ∉ s) (hb : b in s) : (insert a (s \ {b})).encard = s.encard := by
  rw [encard_insert_of_notMem]; rw [encard_sdiff_singleton_add_one hb]
  simp_all only [mem_sdiff, mem_singleton_iff, false_and, not_false_eq_true]

/--
theorem `encard_exchange'` / 定理 `encard_exchange'`

English:
theorem encard_exchange'
  given: (ha : a ∉ s) (hb : b in s)
  statement: (insert a s \ {b}).encard = s.encard
  proof: by
  rw [← insert_sdiff_singleton_comm (by rintro rfl; exact ha hb)]; rw [encard_exchange ha hb]

中文:
定理 encard_exchange'
  条件: (ha : a ∉ s) (hb : b in s)
  结论: (insert a s \ {b}).encard = s.encard
  证明: by
  rw [← insert_sdiff_singleton_comm (by rintro rfl; exact ha hb)]; rw [encard_exchange ha hb]

Depends on / 依赖: encard_exchange, insert_sdiff_singleton_comm
-/
theorem encard_exchange' (ha : a ∉ s) (hb : b in s) : (insert a s \ {b}).encard = s.encard := by
  rw [← insert_sdiff_singleton_comm (by rintro rfl; exact ha hb)]; rw [encard_exchange ha hb]

/--
theorem `encard_eq_add_one_iff` / 定理 `encard_eq_add_one_iff`

English:
theorem encard_eq_add_one_iff
  given: {k : Nat∞}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    refine ⟨a, s \ {a}, fun h => h.2 rfl, by rwa [insert_sdiff_singleton, insert_eq_of_mem], ?_⟩
    rw [encard_sdiff_singleton_of_mem ha]; rw [h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_t

中文:
定理 encard_eq_add_one_iff
  条件: {k : 自然数∞}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    refine ⟨a, s \ {a}, fun h => h.2 rfl, by rwa [insert_sdiff_singleton, insert_eq_of_mem], ?_⟩
    rw [encard_sdiff_singleton_of_mem ha]; rw [h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_t

Depends on / 依赖: ENat.addLECancellable_of_ne_top, ENat.one_ne_top, addLECancellable_of_ne_top, add_tsub_cancel_right, encard_insert_of_notMem, encard_sdiff_singleton_of_mem, insert_eq_of_mem, insert_sdiff_singleton, nonempty_of_encard_ne_zero, one_ne_top
-/
theorem encard_eq_add_one_iff {k : Nat∞} :
    s.encard = k + 1 ↔ (exists a t, a ∉ t ∧ insert a t = s ∧ t.encard = k) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    refine ⟨a, s \ {a}, fun h => h.2 rfl, by rwa [insert_sdiff_singleton, insert_eq_of_mem], ?_⟩
    rw [encard_sdiff_singleton_of_mem ha]; rw [h]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right]
  rintro ⟨a, t, h, rfl, rfl⟩
  rw [encard_insert_of_notMem h]

/--
theorem `eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt` / 定理 `eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt`

English:
theorem eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  given: (s : Set α)
  proof: by
  refine s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ =>
    (s.finite_or_infinite.elim (fun hfin => Or.inr ⟨a, ha, ?_⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [← encard_sdiff_singleton_add_one ha]; nth_rw 1 [← add_zero (encard _)]
  exact ENat.add_lt_add_of_le_of_lt hfin.sdiff.encard_lt

中文:
定理 eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  条件: (s : Set α)
  证明: by
  refine s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ =>
    (s.finite_or_infinite.elim (fun hfin => Or.inr ⟨a, ha, ?_⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [← encard_sdiff_singleton_add_one ha]; nth_rw 1 [← add_zero (encard _)]
  exact ENat.add_lt_add_of_le_of_lt hfin.sdiff.encard_lt

Depends on / 依赖: ENat.add_lt_add_of_le_of_lt, Infinite, Infinite.encard_eq, Or.inl, Or.inr, add_lt_add_of_le_of_lt, add_zero, encard, encard_eq, encard_lt_top, encard_sdiff_singleton_add_one, eq_empty_or_nonempty, finite_or_infinite, hfin.sdiff.encard_lt_top.ne, le_rfl, nth_rw, s.eq_empty_or_nonempty.elim, s.finite_or_infinite.elim, zero_lt_one
-/
theorem eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt (s : Set α) :
    s = ∅ ∨ s.encard = ⊤ ∨ exists a in s, (s \ {a}).encard < s.encard := by
  refine s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ =>
    (s.finite_or_infinite.elim (fun hfin => Or.inr ⟨a, ha, ?_⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [← encard_sdiff_singleton_add_one ha]; nth_rw 1 [← add_zero (encard _)]
  exact ENat.add_lt_add_of_le_of_lt hfin.sdiff.encard_lt_top.ne le_rfl zero_lt_one

@[deprecated (since := "2026-06-03")]
alias eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt :=
  eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt

end InsertErase

section SmallSets

/--
theorem `encard_pair` / 定理 `encard_pair`

English:
theorem encard_pair
  given: {x y : α} (hne : x != y)
  statement: ({x, y} : Set α).encard = 2
  proof: by
  rw [encard_insert_of_notMem (by simpa)]; rw [← one_add_one_eq_two]; rw [encard_singleton]

中文:
定理 encard_pair
  条件: {x y : α} (hne : x != y)
  结论: ({x, y} : Set α).encard = 2
  证明: by
  rw [encard_insert_of_notMem (by simpa)]; rw [← one_add_one_eq_two]; rw [encard_singleton]

Depends on / 依赖: encard_insert_of_notMem, encard_singleton, one_add_one_eq_two
-/
theorem encard_pair {x y : α} (hne : x != y) : ({x, y} : Set α).encard = 2 := by
  rw [encard_insert_of_notMem (by simpa)]; rw [← one_add_one_eq_two]; rw [encard_singleton]

/--
theorem `encard_eq_one` / 定理 `encard_eq_one`

English:
theorem encard_eq_one
  statement: s.encard = 1 ↔ exists x, s = {x}
  proof: by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le (by simpa) (by simp [h])).symm⟩

中文:
定理 encard_eq_one
  结论: s.encard = 1 ↔ 存在 x, s = {x}
  证明: by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le (by simpa) (by simp [h])).symm⟩

Depends on / 依赖: encard_singleton, eq_of_subset_of_encard_le, finite_singleton, nonempty_of_encard_ne_zero
-/
theorem encard_eq_one : s.encard = 1 ↔ exists x, s = {x} := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le (by simpa) (by simp [h])).symm⟩

/--
theorem `encard_le_one_iff_eq` / 定理 `encard_le_one_iff_eq`

English:
theorem encard_le_one_iff_eq
  statement: s.encard <= 1 ↔ s = ∅ ∨ exists x, s = {x}
  proof: by
  rw [le_iff_lt_or_eq]; rw [lt_iff_not_ge]; rw [Order.one_le_iff_ne_zero]; rw [not_not]; rw [encard_eq_zero]; rw [encard_eq_one]

中文:
定理 encard_le_one_iff_eq
  结论: s.encard <= 1 ↔ s = ∅ ∨ 存在 x, s = {x}
  证明: by
  rw [le_iff_lt_or_eq]; rw [lt_iff_not_ge]; rw [Order.one_le_iff_ne_zero]; rw [not_not]; rw [encard_eq_zero]; rw [encard_eq_one]

Depends on / 依赖: Order.one_le_iff_ne_zero, encard_eq_one, encard_eq_zero, le_iff_lt_or_eq, lt_iff_not_ge, not_not, one_le_iff_ne_zero
-/
theorem encard_le_one_iff_eq : s.encard <= 1 ↔ s = ∅ ∨ exists x, s = {x} := by
  rw [le_iff_lt_or_eq]; rw [lt_iff_not_ge]; rw [Order.one_le_iff_ne_zero]; rw [not_not]; rw [encard_eq_zero]; rw [encard_eq_one]

/--
theorem `encard_le_one_iff` / 定理 `encard_le_one_iff`

English:
theorem encard_le_one_iff
  statement: s.encard <= 1 ↔ forall a b, a in s -> b in s -> a = b
  proof: by
  rw [encard_le_one_iff_eq]; rw [or_iff_not_imp_left]; rw [← Ne]; rw [← nonempty_iff_ne_empty]
  refine ⟨fun h a b has hbs => ?_,
    fun h ⟨x, hx⟩ => ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy => h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  rw [(has : a = x)]; rw [(hbs : b = x)]

中文:
定理 encard_le_one_iff
  结论: s.encard <= 1 ↔ 对任意 a b, a in s -> b in s -> a = b
  证明: by
  rw [encard_le_one_iff_eq]; rw [or_iff_not_imp_left]; rw [← Ne]; rw [← nonempty_iff_ne_empty]
  refine ⟨fun h a b has hbs => ?_,
    fun h ⟨x, hx⟩ => ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy => h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  rw [(has : a = x)]; rw [(hbs : b = x)]

Depends on / 依赖: antisymm, encard_le_one_iff_eq, nonempty_iff_ne_empty, or_iff_not_imp_left, singleton_subset_iff
-/
theorem encard_le_one_iff : s.encard <= 1 ↔ forall a b, a in s -> b in s -> a = b := by
  rw [encard_le_one_iff_eq]; rw [or_iff_not_imp_left]; rw [← Ne]; rw [← nonempty_iff_ne_empty]
  refine ⟨fun h a b has hbs => ?_,
    fun h ⟨x, hx⟩ => ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy => h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  rw [(has : a = x)]; rw [(hbs : b = x)]

/--
theorem `encard_le_one_iff_subsingleton` / 定理 `encard_le_one_iff_subsingleton`

English:
theorem encard_le_one_iff_subsingleton
  statement: s.encard <= 1 ↔ s.Subsingleton
  proof: by
  rw [encard_le_one_iff]; rw [Set.Subsingleton]
  tauto

中文:
定理 encard_le_one_iff_subsingleton
  结论: s.encard <= 1 ↔ s.Subsingleton
  证明: by
  rw [encard_le_one_iff]; rw [Set.Subsingleton]
  tauto

Depends on / 依赖: Set.Subsingleton, Subsingleton, encard_le_one_iff
-/
theorem encard_le_one_iff_subsingleton : s.encard <= 1 ↔ s.Subsingleton := by
  rw [encard_le_one_iff]; rw [Set.Subsingleton]
  tauto

/--
theorem `one_lt_encard_iff_nontrivial` / 定理 `one_lt_encard_iff_nontrivial`

English:
theorem one_lt_encard_iff_nontrivial
  statement: 1 < s.encard ↔ s.Nontrivial
  proof: by
  contrapose!; exact encard_le_one_iff_subsingleton

中文:
定理 one_lt_encard_iff_nontrivial
  结论: 1 < s.encard ↔ s.Nontrivial
  证明: by
  contrapose!; exact encard_le_one_iff_subsingleton

Depends on / 依赖: contrapose, encard_le_one_iff_subsingleton
-/
theorem one_lt_encard_iff_nontrivial : 1 < s.encard ↔ s.Nontrivial := by
  contrapose!; exact encard_le_one_iff_subsingleton

/--
theorem `one_lt_encard_iff` / 定理 `one_lt_encard_iff`

English:
theorem one_lt_encard_iff
  statement: 1 < s.encard ↔ exists a b, a in s ∧ b in s ∧ a != b
  proof: by
  contrapose!; exact encard_le_one_iff

中文:
定理 one_lt_encard_iff
  结论: 1 < s.encard ↔ 存在 a b, a in s ∧ b in s ∧ a != b
  证明: by
  contrapose!; exact encard_le_one_iff

Depends on / 依赖: contrapose, encard_le_one_iff
-/
theorem one_lt_encard_iff : 1 < s.encard ↔ exists a b, a in s ∧ b in s ∧ a != b := by
  contrapose!; exact encard_le_one_iff

/--
theorem `exists_ne_of_one_lt_encard` / 定理 `exists_ne_of_one_lt_encard`

English:
theorem exists_ne_of_one_lt_encard
  given: (h : 1 < s.encard) (a : α)
  statement: exists b in s, b != a
  proof: by
  by_contra! h'
  obtain ⟨b, b', hb, hb', hne⟩ := one_lt_encard_iff.1 h
  apply hne
  rw [h' b hb]; rw [h' b' hb']

中文:
定理 exists_ne_of_one_lt_encard
  条件: (h : 1 < s.encard) (a : α)
  结论: 存在 b in s, b != a
  证明: by
  by_contra! h'
  obtain ⟨b, b', hb, hb', hne⟩ := one_lt_encard_iff.1 h
  apply hne
  rw [h' b hb]; rw [h' b' hb']

Depends on / 依赖: one_lt_encard_iff
-/
theorem exists_ne_of_one_lt_encard (h : 1 < s.encard) (a : α) : exists b in s, b != a := by
  by_contra! h'
  obtain ⟨b, b', hb, hb', hne⟩ := one_lt_encard_iff.1 h
  apply hne
  rw [h' b hb]; rw [h' b' hb']

/--
theorem `encard_eq_two` / 定理 `encard_eq_two`

English:
theorem encard_eq_two
  statement: s.encard = 2 ↔ exists x y, x != y ∧ s = {x, y}
  proof: by
  refine ⟨fun h => ?_, fun ⟨x, y, hne, hs⟩ => by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [← one_add_one_eq_two]; rw [(ENat.a

中文:
定理 encard_eq_two
  结论: s.encard = 2 ↔ 存在 x y, x != y ∧ s = {x, y}
  证明: by
  refine ⟨fun h => ?_, fun ⟨x, y, hne, hs⟩ => by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [← one_add_one_eq_two]; rw [(ENat.a

Depends on / 依赖: ENat.addLECancellable_of_ne_top, ENat.one_ne_top, addLECancellable_of_ne_top, encard_eq_one, encard_insert_of_notMem, encard_pair, h.symm.subset, inj_left, insert_eq_of_mem, insert_sdiff_singleton, nonempty_of_encard_ne_zero, one_add_one_eq_two, one_ne_top, subset
-/
theorem encard_eq_two : s.encard = 2 ↔ exists x y, x != y ∧ s = {x, y} := by
  refine ⟨fun h => ?_, fun ⟨x, y, hne, hs⟩ => by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [← one_add_one_eq_two]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left]; rw [encard_eq_one] at h
  obtain ⟨y, h⟩ := h
  refine ⟨x, y, by rintro rfl; exact (h.symm.subset rfl).2 rfl, ?_⟩
  rw [← h]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem hx]

/--
theorem `encard_eq_three` / 定理 `encard_eq_three`

English:
theorem encard_eq_three
  given: {α : Type u_1} {s : Set α}
  proof: by
  refine ⟨fun h => ?_, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (3 : Nat∞) = 2 + 1)]; rw [

中文:
定理 encard_eq_three
  条件: {α : 类型u_1} {s : Set α}
  证明: by
  refine ⟨fun h => ?_, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (3 : Nat∞) = 2 + 1)]; rw [

Depends on / 依赖: ENat.addLECancellable_of_ne_top, ENat.one_ne_top, Or.inl, addLECancellable_of_ne_top, encard_eq_two, encard_insert_of_notMem, hs.symm.subset, inj_left, insert_eq_of_mem, insert_sdiff_singleton, nonempty_of_encard_ne_zero, one_ne_top, subset
-/
theorem encard_eq_three {α : Type u_1} {s : Set α} :
    encard s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z} := by
  refine ⟨fun h => ?_, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (3 : Nat∞) = 2 + 1)]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left]; rw [encard_eq_two] at h
    obtain ⟨y, z, hne, hs⟩ := h
    refine ⟨x, y, z, ?_, ?_, hne, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr rfl)).2 rfl
    rw [← hs]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem hx]
  rw [hs]; rw [encard_insert_of_notMem]; rw [encard_insert_of_notMem]; rw [encard_singleton] <;> aesop

/--
theorem `encard_eq_four` / 定理 `encard_eq_four`

English:
theorem encard_eq_four
  given: {α : Type u_1} {s : Set α}
  proof: by
  refine ⟨fun h => ?_, fun ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (4 : Nat

中文:
定理 encard_eq_four
  条件: {α : 类型u_1} {s : Set α}
  证明: by
  refine ⟨fun h => ?_, fun ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (4 : Nat

Depends on / 依赖: ENat.addLECancellable_of_ne_top, ENat.one_ne_top, addLECancellable_of_ne_top, encard_eq_three, encard_insert_of_notMem, inj_left, insert_eq_of_mem, insert_sdiff_singleton, nonempty_of_encard_ne_zero, one_ne_top
-/
theorem encard_eq_four {α : Type u_1} {s : Set α} :
    encard s = 4 ↔ exists x y z w, x != y ∧ x != z ∧ x != w ∧ y != z ∧ y != w ∧ z != w ∧ s = {x, y, z, w} := by
  refine ⟨fun h => ?_, fun ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hs⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx]; rw [← insert_sdiff_singleton]; rw [encard_insert_of_notMem (fun h => h.2 rfl)]; rw [(by exact rfl : (4 : Nat∞) = 3 + 1)]; rw [(ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left]; rw [encard_eq_three] at h
    obtain ⟨y, z, w, hyz, hyw, hzw, hs⟩ := h
    refine ⟨x, y, z, w, ?_, ?_, ?_, hyz, hyw, hzw, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inl rfl))).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inr rfl))).2 rfl
    rw [← hs]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem hx]
  rw [hs]; rw [encard_insert_of_notMem]; rw [encard_insert_of_notMem]; rw [encard_insert_of_notMem]; rw [encard_singleton] <;> grind

/--
theorem `Nat.encard_range` / 定理 `Nat.encard_range`

English:
theorem Nat.encard_range
  given: (k : Nat)
  statement: {i | i < k}.encard = k
  proof: by
  convert! encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  · rw [Finset.coe_range, Iio_def]
  rw [Finset.card_range]

中文:
定理 Nat.encard_range
  条件: (k : 自然数)
  结论: {i | i < k}.encard = k
  证明: by
  convert! encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  · rw [Finset.coe_range, Iio_def]
  rw [Finset.card_range]

Depends on / 依赖: Finset, Finset.card_range, Finset.coe_range, Finset.range, Iio_def, card_range, coe_range, convert, encard_coe_eq_coe_finsetCard
-/
theorem Nat.encard_range (k : Nat) : {i | i < k}.encard = k := by
  convert! encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  · rw [Finset.coe_range, Iio_def]
  rw [Finset.card_range]

end SmallSets

/--
theorem `Finite.eq_insert_of_subset_of_encard_eq_succ` / 定理 `Finite.eq_insert_of_subset_of_encard_eq_succ`

English:
theorem Finite.eq_insert_of_subset_of_encard_eq_succ
  statement: (hs : s.Finite) (h : s subseteq t)
  proof: by
  rw [← encard_sdiff_add_encard_of_subset h]; rw [add_comm _ 1]; rw [(ENat.addLECancellable_of_lt_top hs.encard_lt_top).inj_left]; rw [encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [← sdiff_union_of_subset h, hx, singleton_union]

中文:
定理 Finite.eq_insert_of_subset_of_encard_eq_succ
  结论: (hs : s.Finite) (h : s subseteq t)
  证明: by
  rw [← encard_sdiff_add_encard_of_subset h]; rw [add_comm _ 1]; rw [(ENat.addLECancellable_of_lt_top hs.encard_lt_top).inj_left]; rw [encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [← sdiff_union_of_subset h, hx, singleton_union]

Depends on / 依赖: ENat.addLECancellable_of_lt_top, addLECancellable_of_lt_top, add_comm, encard_eq_one, encard_lt_top, encard_sdiff_add_encard_of_subset, hs.encard_lt_top, inj_left, sdiff_union_of_subset, singleton_union
-/
theorem Finite.eq_insert_of_subset_of_encard_eq_succ (hs : s.Finite) (h : s subseteq t)
    (hst : t.encard = s.encard + 1) : exists a, t = insert a s := by
  rw [← encard_sdiff_add_encard_of_subset h]; rw [add_comm _ 1]; rw [(ENat.addLECancellable_of_lt_top hs.encard_lt_top).inj_left]; rw [encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [← sdiff_union_of_subset h, hx, singleton_union]

/--
theorem `exists_subset_encard_eq` / 定理 `exists_subset_encard_eq`

English:
theorem exists_subset_encard_eq
  given: {k : Nat∞} (hk : k <= s.encard)
  statement: exists t, t subseteq s ∧ t.encard = k
  proof: by
  induction k using ENat.nat_induction with
  | zero => exact ⟨∅, empty_subset _, by simp⟩
  | succ n IH =>
    obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hk)
    simp only [Nat.cast_succ] at *
    have hne : t₀ != s := by
      rintro rfl; rw [ht₀, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_

中文:
定理 exists_subset_encard_eq
  条件: {k : 自然数∞} (hk : k <= s.encard)
  结论: 存在 t, t subseteq s ∧ t.encard = k
  证明: by
  induction k using ENat.nat_induction with
  | zero => exact ⟨∅, empty_subset _, by simp⟩
  | succ n IH =>
    obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hk)
    simp only [Nat.cast_succ] at *
    have hne : t₀ != s := by
      rintro rfl; rw [ht₀, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_

Depends on / 依赖: ENat.nat_induction, Nat.cast_add, Nat.cast_le, Nat.cast_one, Nat.cast_succ, Subset, Subset.rfl, cast_add, cast_le, cast_one, cast_succ, empty_subset, encard_insert_of_notMem, exists_of_ssubset, insert, insert_subset, le_trans, nat_induction, s.ssubset_of_ne, ssubset_of_ne
-/
theorem exists_subset_encard_eq {k : Nat∞} (hk : k <= s.encard) : exists t, t subseteq s ∧ t.encard = k := by
  induction k using ENat.nat_induction with
  | zero => exact ⟨∅, empty_subset _, by simp⟩
  | succ n IH =>
    obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hk)
    simp only [Nat.cast_succ] at *
    have hne : t₀ != s := by
      rintro rfl; rw [ht₀, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at hk; simp at hk
    obtain ⟨x, hx⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
    exact ⟨insert x t₀, insert_subset hx.1 ht₀s, by rw [encard_insert_of_notMem hx.2, ht₀]⟩
  | top => rw [top_le_iff] at hk; exact ⟨s, Subset.rfl, hk⟩

/--
theorem `exists_superset_subset_encard_eq` / 定理 `exists_superset_subset_encard_eq`

English:
theorem exists_superset_subset_encard_eq
  statement: {k : Nat∞}
  proof: by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k <= encard (t \ s) := by
    rw [← encard_sdiff_add_encard_of_subset hst]; rw [add_

中文:
定理 exists_superset_subset_encard_eq
  结论: {k : 自然数∞}
  证明: by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k <= encard (t \ s) := by
    rw [← encard_sdiff_add_encard_of_subset hst]; rw [add_

Depends on / 依赖: Subset, Subset.rfl, WithTop, WithTop.le_of_add_le_add_right, add_comm, encard, encard_sdiff_add_encard_of_subset, encard_union_eq, eq_or_ne, exists_add_of_le, exists_subset_encard_eq, le_of_add_le_add_right, s.encard, sdiff_subset, subset_union_left, top_le_iff, union_subset
-/
theorem exists_superset_subset_encard_eq {k : Nat∞}
    (hst : s subseteq t) (hsk : s.encard <= k) (hkt : k <= t.encard) :
    exists r, s subseteq r ∧ r subseteq t ∧ r.encard = k := by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k <= encard (t \ s) := by
    rw [← encard_sdiff_add_encard_of_subset hst]; rw [add_comm] at hkt
    exact WithTop.le_of_add_le_add_right hs hkt
  obtain ⟨r', hr', rfl⟩ := exists_subset_encard_eq hk
  refine ⟨s union r', subset_union_left, union_subset hst (hr'.trans sdiff_subset), ?_⟩
  rw [encard_union_eq (disjoint_of_subset_right hr' disjoint_sdiff_right)]

section Function

variable {s : Set α} {t : Set β} {f : α -> β}

/--
theorem `InjOn.encard_image` / 定理 `InjOn.encard_image`

English:
theorem InjOn.encard_image
  given: (h : InjOn f s)
  statement: (f '' s).encard = s.encard
  proof: by
  rw [encard]; rw [ENat.card_image_of_injOn h]; rw [encard]

中文:
定理 InjOn.encard_image
  条件: (h : InjOn f s)
  结论: (f '' s).encard = s.encard
  证明: by
  rw [encard]; rw [ENat.card_image_of_injOn h]; rw [encard]

Depends on / 依赖: ENat.card_image_of_injOn, card_image_of_injOn, encard
-/
theorem InjOn.encard_image (h : InjOn f s) : (f '' s).encard = s.encard := by
  rw [encard]; rw [ENat.card_image_of_injOn h]; rw [encard]

/--
theorem `encard_congr` / 定理 `encard_congr`

English:
theorem encard_congr
  given: (e : s ≃ t)
  statement: s.encard = t.encard
  proof: ENat.card_congr e

中文:
定理 encard_congr
  条件: (e : s ≃ t)
  结论: s.encard = t.encard
  证明: ENat.card_congr e

Depends on / 依赖: ENat.card_congr, card_congr
-/
theorem encard_congr (e : s ≃ t) : s.encard = t.encard := ENat.card_congr e

/--
theorem `_root_.Function.Injective.encard_image` / 定理 `_root_.Function.Injective.encard_image`

English:
theorem _root_.Function.Injective.encard_image
  given: (hf : f.Injective) (s : Set α)
  proof: hf.injOn.encard_image

中文:
定理 _root_.Function.Injective.encard_image
  条件: (hf : f.Injective) (s : Set α)
  证明: hf.injOn.encard_image

Depends on / 依赖: encard_image, hf.injOn.encard_image
-/
theorem _root_.Function.Injective.encard_image (hf : f.Injective) (s : Set α) :
    (f '' s).encard = s.encard :=
  hf.injOn.encard_image

/--
theorem `_root_.Function.Injective.encard_range` / 定理 `_root_.Function.Injective.encard_range`

English:
theorem _root_.Function.Injective.encard_range
  given: (hf : f.Injective)
  proof: by
  rw [← image_univ]; rw [hf.encard_image]; rw [encard_univ]

中文:
定理 _root_.Function.Injective.encard_range
  条件: (hf : f.Injective)
  证明: by
  rw [← image_univ]; rw [hf.encard_image]; rw [encard_univ]

Depends on / 依赖: encard_image, encard_univ, hf.encard_image, image_univ
-/
theorem _root_.Function.Injective.encard_range (hf : f.Injective) :
    ENat.card α <= (range f).encard := by
  rw [← image_univ]; rw [hf.encard_image]; rw [encard_univ]

/--
theorem `_root_.Function.Embedding.encard_le` / 定理 `_root_.Function.Embedding.encard_le`

English:
theorem _root_.Function.Embedding.encard_le
  given: (e : s ↪ t)
  statement: s.encard <= t.encard
  proof: ENat.card_le_card_of_injective e.injective

中文:
定理 _root_.Function.Embedding.encard_le
  条件: (e : s ↪ t)
  结论: s.encard <= t.encard
  证明: ENat.card_le_card_of_injective e.injective

Depends on / 依赖: ENat.card_le_card_of_injective, card_le_card_of_injective, e.injective, injective
-/
theorem _root_.Function.Embedding.encard_le (e : s ↪ t) : s.encard <= t.encard :=
  ENat.card_le_card_of_injective e.injective

/--
theorem `encard_image_le` / 定理 `encard_image_le`

English:
theorem encard_image_le
  given: (f : α -> β) (s : Set α)
  statement: (f '' s).encard <= s.encard
  proof: by
  obtain (h | h) := isEmpty_or_nonempty α
  · rw [s.eq_empty_of_isEmpty]; simp
  grw [← (f.invFunOn_injOn_image s).encard_image, f.invFunOn_image_image_subset s]

中文:
定理 encard_image_le
  条件: (f : α -> β) (s : Set α)
  结论: (f '' s).encard <= s.encard
  证明: by
  obtain (h | h) := isEmpty_or_nonempty α
  · rw [s.eq_empty_of_isEmpty]; simp
  grw [← (f.invFunOn_injOn_image s).encard_image, f.invFunOn_image_image_subset s]

Depends on / 依赖: encard_image, eq_empty_of_isEmpty, f.invFunOn_image_image_subset, f.invFunOn_injOn_image, invFunOn_image_image_subset, invFunOn_injOn_image, isEmpty_or_nonempty, s.eq_empty_of_isEmpty
-/
theorem encard_image_le (f : α -> β) (s : Set α) : (f '' s).encard <= s.encard := by
  obtain (h | h) := isEmpty_or_nonempty α
  · rw [s.eq_empty_of_isEmpty]; simp
  grw [← (f.invFunOn_injOn_image s).encard_image, f.invFunOn_image_image_subset s]

/--
theorem `Finite.injOn_of_encard_image_eq` / 定理 `Finite.injOn_of_encard_image_eq`

English:
theorem Finite.injOn_of_encard_image_eq
  given: (hs : s.Finite) (h : (f '' s).encard = s.encard)
  proof: by
  obtain (h' | hne) := isEmpty_or_nonempty α
  · simp
  rw [← (f.invFunOn_injOn_image s).encard_image] at h
  rw [injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le' (f.invFunOn_image_image_subset s) h.symm.le

中文:
定理 Finite.injOn_of_encard_image_eq
  条件: (hs : s.Finite) (h : (f '' s).encard = s.encard)
  证明: by
  obtain (h' | hne) := isEmpty_or_nonempty α
  · simp
  rw [← (f.invFunOn_injOn_image s).encard_image] at h
  rw [injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le' (f.invFunOn_image_image_subset s) h.symm.le

Depends on / 依赖: encard_image, eq_of_subset_of_encard_le, f.invFunOn_image_image_subset, f.invFunOn_injOn_image, h.symm.le, hs.eq_of_subset_of_encard_le, injOn_iff_invFunOn_image_image_eq_self, invFunOn_image_image_subset, invFunOn_injOn_image, isEmpty_or_nonempty
-/
theorem Finite.injOn_of_encard_image_eq (hs : s.Finite) (h : (f '' s).encard = s.encard) :
    InjOn f s := by
  obtain (h' | hne) := isEmpty_or_nonempty α
  · simp
  rw [← (f.invFunOn_injOn_image s).encard_image] at h
  rw [injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le' (f.invFunOn_image_image_subset s) h.symm.le

/--
theorem `encard_preimage_of_injective_subset_range` / 定理 `encard_preimage_of_injective_subset_range`

English:
theorem encard_preimage_of_injective_subset_range
  given: (hf : f.Injective) (ht : t subseteq range f)
  proof: by
  rw [← hf.encard_image]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left ht]

中文:
定理 encard_preimage_of_injective_subset_range
  条件: (hf : f.Injective) (ht : t subseteq range f)
  证明: by
  rw [← hf.encard_image]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left ht]

Depends on / 依赖: encard_image, hf.encard_image, image_preimage_eq_inter_range, inter_eq_self_of_subset_left
-/
theorem encard_preimage_of_injective_subset_range (hf : f.Injective) (ht : t subseteq range f) :
    (f ⁻¹' t).encard = t.encard := by
  rw [← hf.encard_image]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left ht]

/--
lemma `encard_preimage_of_bijective` / 引理 `encard_preimage_of_bijective`

English:
lemma encard_preimage_of_bijective
  given: (hf : f.Bijective) (t : Set β)
  statement: (f ⁻¹' t).encard = t.encard
  proof: encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])

中文:
引理 encard_preimage_of_bijective
  条件: (hf : f.Bijective) (t : Set β)
  结论: (f ⁻¹' t).encard = t.encard
  证明: encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])

Depends on / 依赖: encard_preimage_of_injective_subset_range, hf.injective, hf.surjective.range_eq, injective, range_eq, surjective
-/
lemma encard_preimage_of_bijective (hf : f.Bijective) (t : Set β) : (f ⁻¹' t).encard = t.encard :=
  encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])

/--
theorem `encard_le_encard_of_injOn` / 定理 `encard_le_encard_of_injOn`

English:
theorem encard_le_encard_of_injOn
  given: (hf : MapsTo f s t) (f_inj : InjOn f s)
  proof: by
  grw [← f_inj.encard_image, hf.image_subset]

中文:
定理 encard_le_encard_of_injOn
  条件: (hf : MapsTo f s t) (f_inj : InjOn f s)
  证明: by
  grw [← f_inj.encard_image, hf.image_subset]

Depends on / 依赖: encard_image, f_inj, f_inj.encard_image, hf.image_subset, image_subset
-/
theorem encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) :
    s.encard <= t.encard := by
  grw [← f_inj.encard_image, hf.image_subset]

open Notation in
/--
lemma `encard_preimage_val_le_encard_left` / 引理 `encard_preimage_val_le_encard_left`

English:
lemma encard_preimage_val_le_encard_left
  given: (P Q : Set α)
  statement: (P ↓inter Q).encard <= P.encard
  proof: (Function.Embedding.subtype _).encard_le

中文:
引理 encard_preimage_val_le_encard_left
  条件: (P Q : Set α)
  结论: (P ↓inter Q).encard <= P.encard
  证明: (Function.Embedding.subtype _).encard_le

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, encard_le, subtype
-/
lemma encard_preimage_val_le_encard_left (P Q : Set α) : (P ↓inter Q).encard <= P.encard :=
  (Function.Embedding.subtype _).encard_le

set_option backward.isDefEq.respectTransparency false in
open Notation in
/--
lemma `encard_preimage_val_le_encard_right` / 引理 `encard_preimage_val_le_encard_right`

English:
lemma encard_preimage_val_le_encard_right
  given: (P Q : Set α)
  statement: (P ↓inter Q).encard <= Q.encard
  proof: Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, fun _ _ h => by
    simpa [Subtype.coe_inj] using h⟩

中文:
引理 encard_preimage_val_le_encard_right
  条件: (P Q : Set α)
  结论: (P ↓inter Q).encard <= Q.encard
  证明: Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, fun _ _ h => by
    simpa [Subtype.coe_inj] using h⟩

Depends on / 依赖: Embedding, Function, Function.Embedding.encard_le, Subtype, Subtype.coe_inj, coe_inj, encard_le
-/
lemma encard_preimage_val_le_encard_right (P Q : Set α) : (P ↓inter Q).encard <= Q.encard :=
  Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, fun _ _ h => by
    simpa [Subtype.coe_inj] using h⟩

/--
theorem `Finite.exists_injOn_of_encard_le` / 定理 `Finite.exists_injOn_of_encard_le`

English:
theorem Finite.exists_injOn_of_encard_le
  statement: [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
  proof: by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard <= (t \ {b}).encard := by
    rwa [

中文:
定理 Finite.exists_injOn_of_encard_le
  结论: [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
  证明: by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard <= (t \ {b}).encard := by
    rwa [

Depends on / 依赖: ENat.add_le_add_iff_right, ENat.one_ne_top, add_le_add_iff_right, classical, encard, encard_ne_top_iff, encard_ne_top_iff.mpr, encard_pos, encard_sdiff_singleton_add_one, eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt, exists_injOn_of_encard_le, hs.sdiff, one_ne_top, preimage_sdiff, s.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt, trans_le
-/
theorem Finite.exists_injOn_of_encard_le [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
    (hle : s.encard <= t.encard) : exists (f : α -> β), s subseteq f ⁻¹' t ∧ InjOn f s := by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard <= (t \ {b}).encard := by
    rwa [← ENat.add_le_add_iff_right ENat.one_ne_top,
    encard_sdiff_singleton_add_one has, encard_sdiff_singleton_add_one hbt]
  obtain ⟨f₀, hf₀s, hinj⟩ := exists_injOn_of_encard_le hs.sdiff hle'
  simp only [preimage_sdiff, subset_def, mem_sdiff, mem_singleton_iff, mem_preimage, and_imp]
    at hf₀s
  use Function.update f₀ a b
  rw [← insert_eq_of_mem has]; rw [← insert_sdiff_singleton]; rw [injOn_insert (fun h => h.2 rfl)]
  simp only [mem_sdiff, mem_singleton_iff, insert_sdiff_singleton, subset_def,
    mem_insert_iff, mem_preimage, Function.update_apply, forall_eq_or_imp, ite_true, and_imp,
    mem_image, ite_eq_left_iff, not_exists, not_and, not_forall, exists_prop, and_iff_right hbt]
  refine ⟨?_, ?_, fun x hxs hxa => ⟨hxa, (hf₀s x hxs hxa).2⟩⟩
  · rintro x hx; split_ifs with h
    · assumption
    · exact (hf₀s x hx h).1
  exact InjOn.congr hinj (fun x ⟨_, hxa⟩ => by rwa [Function.update_of_ne])
termination_by encard s

/--
theorem `Finite.exists_bijOn_of_encard_eq` / 定理 `Finite.exists_bijOn_of_encard_eq`

English:
theorem Finite.exists_bijOn_of_encard_eq
  given: [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard)
  proof: by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  convert! hinj.bijOn_image
  rw [(hs.image f).eq_of_subset_of_encard_le (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

中文:
定理 Finite.exists_bijOn_of_encard_eq
  条件: [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard)
  证明: by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  convert! hinj.bijOn_image
  rw [(hs.image f).eq_of_subset_of_encard_le (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

Depends on / 依赖: bijOn_image, convert, encard_image, eq_of_subset_of_encard_le, exists_injOn_of_encard_le, h.le, h.symm.trans, hinj.bijOn_image, hinj.encard_image.symm, hs.exists_injOn_of_encard_le, hs.image, image_subset_iff, image_subset_iff.mpr
-/
theorem Finite.exists_bijOn_of_encard_eq [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard) :
    exists (f : α -> β), BijOn f s t := by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  convert! hinj.bijOn_image
  rw [(hs.image f).eq_of_subset_of_encard_le (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

/--
lemma `exists_ne_map_eq_of_encard_lt_of_maps_to` / 引理 `exists_ne_map_eq_of_encard_lt_of_maps_to`

English:
lemma exists_ne_map_eq_of_encard_lt_of_maps_to
  given: (hc : t.encard < s.encard) (hf : MapsTo f s t)
  proof: by
  contrapose! hc
  suffices Function.Injective (hf.restrict f) by
    let f' : s ↪ t := ⟨hf.restrict, this⟩
    exact f'.encard_le
  simpa only [hf.restrict_inj, not_imp_not] using! hc

中文:
引理 exists_ne_map_eq_of_encard_lt_of_maps_to
  条件: (hc : t.encard < s.encard) (hf : MapsTo f s t)
  证明: by
  contrapose! hc
  suffices Function.Injective (hf.restrict f) by
    let f' : s ↪ t := ⟨hf.restrict, this⟩
    exact f'.encard_le
  simpa only [hf.restrict_inj, not_imp_not] using! hc

Depends on / 依赖: Function, Function.Injective, Injective, contrapose, encard_le, hf.restrict, hf.restrict_inj, not_imp_not, restrict, restrict_inj
-/
lemma exists_ne_map_eq_of_encard_lt_of_maps_to (hc : t.encard < s.encard) (hf : MapsTo f s t) :
    existsᵉ (a₁ in s) (a₂ in s), a₁ != a₂ ∧ f a₁ = f a₂ := by
  contrapose! hc
  suffices Function.Injective (hf.restrict f) by
    let f' : s ↪ t := ⟨hf.restrict, this⟩
    exact f'.encard_le
  simpa only [hf.restrict_inj, not_imp_not] using! hc

end Function

section ncard

/-- A tactic (for use in default params) that applies `Set.toFinite` to synthesize a `Set.Finite`
  term. -/
syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

/-- A tactic useful for transferring proofs for `encard` to their corresponding `card` statements -/
syntax "to_encard_tac" : tactic

macro_rules
  | `(tactic| to_encard_tac) => `(tactic|
      simp only [← Nat.cast_le (α := Nat∞), ← Nat.cast_inj (R := Nat∞), Nat.cast_add, Nat.cast_one])


/--
Definition of `ncard` / `ncard` 的定义

English:
definition ncard
  signature: (s : Set α)
  body: ENat.toNat s.encard

中文:
定义 ncard
  签名: (s : Set α)
  定义体: ENat.toNat s.encard

Depends on / 依赖: ENat.toNat, encard, s.encard
-/
noncomputable def ncard (s : Set α) : Nat := ENat.toNat s.encard

/--
theorem `ncard_def` / 定理 `ncard_def`

English:
theorem ncard_def
  given: (s : Set α)
  statement: s.ncard = ENat.toNat s.encard
  proof: rfl

中文:
定理 ncard_def
  条件: (s : Set α)
  结论: s.ncard = E自然数.to自然数 s.encard
  证明: rfl
-/
theorem ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard := rfl

/--
theorem `Finite.cast_ncard_eq` / 定理 `Finite.cast_ncard_eq`

English:
theorem Finite.cast_ncard_eq
  given: (hs : s.Finite)
  statement: s.ncard = s.encard
  proof: by
  rwa [ncard, ENat.natCast_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]

中文:
定理 Finite.cast_ncard_eq
  条件: (hs : s.Finite)
  结论: s.ncard = s.encard
  证明: by
  rwa [ncard, ENat.natCast_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]

Depends on / 依赖: ENat.natCast_toNat_eq_self, Infinite, Set.Infinite, encard_eq_top_iff, natCast_toNat_eq_self, ne_eq, not_not
-/
theorem Finite.cast_ncard_eq (hs : s.Finite) : s.ncard = s.encard := by
  rwa [ncard, ENat.natCast_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]

variable (s) in
@[simp]
/--
theorem `coe_ncard_eq_encard` / 定理 `coe_ncard_eq_encard`

English:
theorem coe_ncard_eq_encard
  given: [Finite s]
  statement: s.ncard = s.encard
  proof: s.toFinite.cast_ncard_eq

中文:
定理 coe_ncard_eq_encard
  条件: [Finite s]
  结论: s.ncard = s.encard
  证明: s.toFinite.cast_ncard_eq

Depends on / 依赖: cast_ncard_eq, s.toFinite.cast_ncard_eq, toFinite
-/
theorem coe_ncard_eq_encard [Finite s] : s.ncard = s.encard :=
  s.toFinite.cast_ncard_eq

/--
lemma `ncard_le_encard` / 引理 `ncard_le_encard`

English:
lemma ncard_le_encard
  given: (s : Set α)
  statement: s.ncard <= s.encard
  proof: ENat.natCast_toNat_le_self _

中文:
引理 ncard_le_encard
  条件: (s : Set α)
  结论: s.ncard <= s.encard
  证明: ENat.natCast_toNat_le_self _

Depends on / 依赖: ENat.natCast_toNat_le_self, natCast_toNat_le_self
-/
lemma ncard_le_encard (s : Set α) : s.ncard <= s.encard := ENat.natCast_toNat_le_self _

/--
theorem `_root_.Nat.card_coe_set_eq` / 定理 `_root_.Nat.card_coe_set_eq`

English:
theorem _root_.Nat.card_coe_set_eq
  given: (s : Set α)
  statement: Nat.card s = s.ncard
  proof: rfl

中文:
定理 _root_.Nat.card_coe_set_eq
  条件: (s : Set α)
  结论: 自然数.card s = s.ncard
  证明: rfl
-/
@[simp] theorem _root_.Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := rfl

/--
theorem `ncard_eq_toFinset_card` / 定理 `ncard_eq_toFinset_card`

English:
theorem ncard_eq_toFinset_card
  given: (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_fintype_card _ hs.fintype]; rw [@Finite.card_toFinset _ _ hs.fintype hs]

中文:
定理 ncard_eq_toFinset_card
  条件: (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_fintype_card _ hs.fintype]; rw [@Finite.card_toFinset _ _ hs.fintype hs]

Depends on / 依赖: Finite, Finite.card_toFinset, Nat.card_eq_fintype_card, _root_, _root_.Nat.card_coe_set_eq, card_coe_set_eq, card_eq_fintype_card, card_toFinset, fintype, hs.fintype, hs.toFinset.card, s.ncard, toFinite_tac, toFinset
-/
theorem ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_fintype_card _ hs.fintype]; rw [@Finite.card_toFinset _ _ hs.fintype hs]

/--
theorem `ncard_eq_toFinset_card'` / 定理 `ncard_eq_toFinset_card'`

English:
theorem ncard_eq_toFinset_card'
  given: (s : Set α) [Fintype s]
  proof: by
  simp [← _root_.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

中文:
定理 ncard_eq_toFinset_card'
  条件: (s : Set α) [Fintype s]
  证明: by
  simp [← _root_.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

Depends on / 依赖: Nat.card_eq_fintype_card, _root_, _root_.Nat.card_coe_set_eq, card_coe_set_eq, card_eq_fintype_card
-/
theorem ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [← _root_.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

variable (s) in
@[simp]
/--
theorem `fintypeCard_eq_ncard` / 定理 `fintypeCard_eq_ncard`

English:
theorem fintypeCard_eq_ncard
  given: [Fintype s]
  statement: Fintype.card s = s.ncard
  proof: by
  rw [ncard_eq_toFinset_card']; rw [toFinset_card]

中文:
定理 fintypeCard_eq_ncard
  条件: [Fintype s]
  结论: Fintype.card s = s.ncard
  证明: by
  rw [ncard_eq_toFinset_card']; rw [toFinset_card]

Depends on / 依赖: ncard_eq_toFinset_card, toFinset_card
-/
theorem fintypeCard_eq_ncard [Fintype s] : Fintype.card s = s.ncard := by
  rw [ncard_eq_toFinset_card']; rw [toFinset_card]

/--
lemma `cast_ncard` / 引理 `cast_ncard`

English:
lemma cast_ncard
  given: {s : Set α} (hs : s.Finite)
  proof: @Nat.cast_card _ hs

中文:
引理 cast_ncard
  条件: {s : Set α} (hs : s.Finite)
  证明: @Nat.cast_card _ hs

Depends on / 依赖: Nat.cast_card, cast_card
-/
lemma cast_ncard {s : Set α} (hs : s.Finite) :
    (s.ncard : Cardinal) = Cardinal.mk s := @Nat.cast_card _ hs

/--
theorem `encard_le_coe_iff_finite_ncard_le` / 定理 `encard_le_coe_iff_finite_ncard_le`

English:
theorem encard_le_coe_iff_finite_ncard_le
  given: {k : Nat}
  statement: s.encard <= k ↔ s.Finite ∧ s.ncard <= k
  proof: by
  rw [encard_le_coe_iff]; rw [and_congr_right_iff]
  exact fun hfin => ⟨fun ⟨n₀, hn₀, hle⟩ => by rwa [ncard_def, hn₀, ENat.toNat_natCast],
    fun h => ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩

中文:
定理 encard_le_coe_iff_finite_ncard_le
  条件: {k : 自然数}
  结论: s.encard <= k ↔ s.Finite ∧ s.ncard <= k
  证明: by
  rw [encard_le_coe_iff]; rw [and_congr_right_iff]
  exact fun hfin => ⟨fun ⟨n₀, hn₀, hle⟩ => by rwa [ncard_def, hn₀, ENat.toNat_natCast],
    fun h => ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩

Depends on / 依赖: ENat.toNat_natCast, and_congr_right_iff, cast_ncard_eq, encard_le_coe_iff, hfin.cast_ncard_eq, ncard_def, s.ncard, toNat_natCast
-/
theorem encard_le_coe_iff_finite_ncard_le {k : Nat} : s.encard <= k ↔ s.Finite ∧ s.ncard <= k := by
  rw [encard_le_coe_iff]; rw [and_congr_right_iff]
  exact fun hfin => ⟨fun ⟨n₀, hn₀, hle⟩ => by rwa [ncard_def, hn₀, ENat.toNat_natCast],
    fun h => ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩

/--
theorem `Infinite.ncard` / 定理 `Infinite.ncard`

English:
theorem Infinite.ncard
  given: (hs : s.Infinite)
  statement: s.ncard = 0
  proof: by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_zero_of_infinite _ hs.to_subtype]

@[gcongr]

中文:
定理 Infinite.ncard
  条件: (hs : s.Infinite)
  结论: s.ncard = 0
  证明: by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_zero_of_infinite _ hs.to_subtype]

@[gcongr]

Depends on / 依赖: Nat.card_eq_zero_of_infinite, _root_, _root_.Nat.card_coe_set_eq, card_coe_set_eq, card_eq_zero_of_infinite, hs.to_subtype, to_subtype
-/
theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 := by
  rw [← _root_.Nat.card_coe_set_eq]; rw [@Nat.card_eq_zero_of_infinite _ hs.to_subtype]

@[gcongr]
/--
theorem `ncard_le_ncard` / 定理 `ncard_le_ncard`

English:
theorem ncard_le_ncard
  given: (hst : s subseteq t) (ht : t.Finite := by toFinite_tac)
  proof: by
  rw [← Nat.cast_le (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset hst).cast_ncard_eq]
  exact encard_mono hst

中文:
定理 ncard_le_ncard
  条件: (hst : s subseteq t) (ht : t.Finite := by toFinite_tac)
  证明: by
  rw [← Nat.cast_le (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset hst).cast_ncard_eq]
  exact encard_mono hst

Depends on / 依赖: Nat.cast_le, cast_le, cast_ncard_eq, encard_mono, ht.cast_ncard_eq, ht.subset, s.ncard, subset, t.ncard, toFinite_tac
-/
theorem ncard_le_ncard (hst : s subseteq t) (ht : t.Finite := by toFinite_tac) :
    s.ncard <= t.ncard := by
  rw [← Nat.cast_le (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset hst).cast_ncard_eq]
  exact encard_mono hst

/--
theorem `ncard_mono` / 定理 `ncard_mono`

English:
theorem ncard_mono
  given: [Finite α]
  statement: @Monotone (Set α) _ _ _ ncard
  proof: fun _ _ => ncard_le_ncard

中文:
定理 ncard_mono
  条件: [Finite α]
  结论: @Monotone (Set α) _ _ _ ncard
  证明: fun _ _ => ncard_le_ncard

Depends on / 依赖: ncard_le_ncard
-/
theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ => ncard_le_ncard

/--
theorem `ncard_eq_zero` / 定理 `ncard_eq_zero`

English:
theorem ncard_eq_zero
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [Nat.cast_zero]; rw [encard_eq_zero]

中文:
定理 ncard_eq_zero
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [Nat.cast_zero]; rw [encard_eq_zero]
-/
@[simp] theorem ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [Nat.cast_zero]; rw [encard_eq_zero]

/--
theorem `ncard_coe_finset` / 定理 `ncard_coe_finset`

English:
theorem ncard_coe_finset
  given: (s : Finset α)
  statement: (s : Set α).ncard = s.card
  proof: by
  rw [ncard_eq_toFinset_card _]; rw [Finset.finite_toSet_toFinset]

中文:
定理 ncard_coe_finset
  条件: (s : Finset α)
  结论: (s : Set α).ncard = s.card
  证明: by
  rw [ncard_eq_toFinset_card _]; rw [Finset.finite_toSet_toFinset]
-/
@[simp, norm_cast] theorem ncard_coe_finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _]; rw [Finset.finite_toSet_toFinset]

/--
theorem `ncard_univ` / 定理 `ncard_univ`

English:
theorem ncard_univ
  given: (α : Type*)
  statement: (univ : Set α).ncard = Nat.card α
  proof: Nat.card_univ

中文:
定理 ncard_univ
  条件: (α : 类型)
  结论: (univ : Set α).ncard = 自然数.card α
  证明: Nat.card_univ
-/
@[simp] theorem ncard_univ (α : Type*) : (univ : Set α).ncard = Nat.card α := Nat.card_univ

/--
theorem `ncard_le_card` / 定理 `ncard_le_card`

English:
theorem ncard_le_card
  given: [Finite α] (s : Set α)
  statement: s.ncard <= Nat.card α
  proof: ncard_univ α ▸ ncard_le_ncard s.subset_univ

中文:
定理 ncard_le_card
  条件: [Finite α] (s : Set α)
  结论: s.ncard <= 自然数.card α
  证明: ncard_univ α ▸ ncard_le_ncard s.subset_univ

Depends on / 依赖: ncard_le_ncard, ncard_univ, s.subset_univ, subset_univ
-/
theorem ncard_le_card [Finite α] (s : Set α) : s.ncard <= Nat.card α :=
  ncard_univ α ▸ ncard_le_ncard s.subset_univ

/--
theorem `ncard_empty` / 定理 `ncard_empty`

English:
theorem ncard_empty
  given: (α : Type*)
  statement: (∅ : Set α).ncard = 0
  proof: by
  rw [ncard_eq_zero]

中文:
定理 ncard_empty
  条件: (α : 类型)
  结论: (∅ : Set α).ncard = 0
  证明: by
  rw [ncard_eq_zero]
-/
@[simp] theorem ncard_empty (α : Type*) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]

/--
theorem `ncard_pos` / 定理 `ncard_pos`

English:
theorem ncard_pos
  given: (hs : s.Finite := by toFinite_tac)
  statement: 0 < s.ncard ↔ s.Nonempty
  proof: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [ncard_eq_zero hs]; rw [nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.ncard_pos⟩ := ncard_pos

中文:
定理 ncard_pos
  条件: (hs : s.Finite := by toFinite_tac)
  结论: 0 < s.ncard ↔ s.Nonempty
  证明: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [ncard_eq_zero hs]; rw [nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.ncard_pos⟩ := ncard_pos

Depends on / 依赖: Nonempty, ncard_eq_zero, nonempty_iff_ne_empty, pos_iff_ne_zero, s.Nonempty, s.ncard, toFinite_tac
-/
theorem ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [ncard_eq_zero hs]; rw [nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.ncard_pos⟩ := ncard_pos

/--
theorem `ncard_ne_zero_of_mem` / 定理 `ncard_ne_zero_of_mem`

English:
theorem ncard_ne_zero_of_mem
  given: {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac)
  statement: s.ncard != 0
  proof: ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm

中文:
定理 ncard_ne_zero_of_mem
  条件: {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac)
  结论: s.ncard != 0
  证明: ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm

Depends on / 依赖: ncard_pos, ne.symm, s.ncard, toFinite_tac
-/
theorem ncard_ne_zero_of_mem {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac) : s.ncard != 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm

/--
theorem `finite_of_ncard_ne_zero` / 定理 `finite_of_ncard_ne_zero`

English:
theorem finite_of_ncard_ne_zero
  given: (hs : s.ncard != 0)
  statement: s.Finite
  proof: s.finite_or_infinite.elim id fun h => (hs h.ncard).elim

中文:
定理 finite_of_ncard_ne_zero
  条件: (hs : s.ncard != 0)
  结论: s.Finite
  证明: s.finite_or_infinite.elim id fun h => (hs h.ncard).elim

Depends on / 依赖: finite_or_infinite, h.ncard, s.finite_or_infinite.elim
-/
theorem finite_of_ncard_ne_zero (hs : s.ncard != 0) : s.Finite :=
  s.finite_or_infinite.elim id fun h => (hs h.ncard).elim

/--
theorem `finite_of_ncard_pos` / 定理 `finite_of_ncard_pos`

English:
theorem finite_of_ncard_pos
  given: (hs : 0 < s.ncard)
  statement: s.Finite
  proof: finite_of_ncard_ne_zero hs.ne.symm

中文:
定理 finite_of_ncard_pos
  条件: (hs : 0 < s.ncard)
  结论: s.Finite
  证明: finite_of_ncard_ne_zero hs.ne.symm

Depends on / 依赖: finite_of_ncard_ne_zero, hs.ne.symm
-/
theorem finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  finite_of_ncard_ne_zero hs.ne.symm

/--
theorem `nonempty_of_ncard_ne_zero` / 定理 `nonempty_of_ncard_ne_zero`

English:
theorem nonempty_of_ncard_ne_zero
  given: (hs : s.ncard != 0)
  statement: s.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

中文:
定理 nonempty_of_ncard_ne_zero
  条件: (hs : s.ncard != 0)
  结论: s.Nonempty
  证明: by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

Depends on / 依赖: nonempty_iff_ne_empty
-/
theorem nonempty_of_ncard_ne_zero (hs : s.ncard != 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

/--
theorem `ncard_singleton` / 定理 `ncard_singleton`

English:
theorem ncard_singleton
  given: (a : α)
  statement: ({a} : Set α).ncard = 1
  proof: by
  simp [ncard]

中文:
定理 ncard_singleton
  条件: (a : α)
  结论: ({a} : Set α).ncard = 1
  证明: by
  simp [ncard]
-/
@[simp] theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard]

/--
theorem `ncard_singleton_inter` / 定理 `ncard_singleton_inter`

English:
theorem ncard_singleton_inter
  given: (a : α) (s : Set α)
  statement: ({a} inter s).ncard <= 1
  proof: by
  rw [← Nat.cast_le (α := Nat∞)]; rw [(toFinite _).cast_ncard_eq]; rw [Nat.cast_one]
  apply encard_singleton_inter

@[simp]

中文:
定理 ncard_singleton_inter
  条件: (a : α) (s : Set α)
  结论: ({a} inter s).ncard <= 1
  证明: by
  rw [← Nat.cast_le (α := Nat∞)]; rw [(toFinite _).cast_ncard_eq]; rw [Nat.cast_one]
  apply encard_singleton_inter

@[simp]

Depends on / 依赖: Nat.cast_le, Nat.cast_one, cast_le, cast_ncard_eq, cast_one, encard_singleton_inter, toFinite
-/
theorem ncard_singleton_inter (a : α) (s : Set α) : ({a} inter s).ncard <= 1 := by
  rw [← Nat.cast_le (α := Nat∞)]; rw [(toFinite _).cast_ncard_eq]; rw [Nat.cast_one]
  apply encard_singleton_inter

@[simp]
/--
theorem `ncard_prod` / 定理 `ncard_prod`

English:
theorem ncard_prod
  given: {s : Set α} {t : Set β}
  statement: (s ×ˢ t).ncard = s.ncard * t.ncard
  proof: by
  simp [ncard, ENat.toNat_mul]

@[simp]

中文:
定理 ncard_prod
  条件: {s : Set α} {t : Set β}
  结论: (s ×ˢ t).ncard = s.ncard * t.ncard
  证明: by
  simp [ncard, ENat.toNat_mul]

@[simp]

Depends on / 依赖: ENat.toNat_mul, toNat_mul
-/
theorem ncard_prod {s : Set α} {t : Set β} : (s ×ˢ t).ncard = s.ncard * t.ncard := by
  simp [ncard, ENat.toNat_mul]

@[simp]
/--
theorem `ncard_powerset` / 定理 `ncard_powerset`

English:
theorem ncard_powerset
  given: (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  have h := Cardinal.mk_powerset s
  rw [← cast_ncard hs.powerset]; rw [← cast_ncard hs] at h
  norm_cast at h

中文:
定理 ncard_powerset
  条件: (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  have h := Cardinal.mk_powerset s
  rw [← cast_ncard hs.powerset]; rw [← cast_ncard hs] at h
  norm_cast at h

Depends on / 依赖: Cardinal, Cardinal.mk_powerset, cast_ncard, hs.powerset, mk_powerset, powerset, s.ncard, toFinite_tac
-/
theorem ncard_powerset (s : Set α) (hs : s.Finite := by toFinite_tac) :
    (𝒫 s).ncard = 2 ^ s.ncard := by
  have h := Cardinal.mk_powerset s
  rw [← cast_ncard hs.powerset]; rw [← cast_ncard hs] at h
  norm_cast at h

section InsertErase

/--
theorem `ncard_insert_of_notMem` / 定理 `ncard_insert_of_notMem`

English:
theorem ncard_insert_of_notMem
  given: {a : α} (h : a ∉ s) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [(hs.insert a).cast_ncard_eq]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [hs.cast_ncard_eq]; rw [encard_insert_of_notMem h]

中文:
定理 ncard_insert_of_notMem
  条件: {a : α} (h : a ∉ s) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [(hs.insert a).cast_ncard_eq]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [hs.cast_ncard_eq]; rw [encard_insert_of_notMem h]
-/
@[simp] theorem ncard_insert_of_notMem {a : α} (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [(hs.insert a).cast_ncard_eq]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [hs.cast_ncard_eq]; rw [encard_insert_of_notMem h]

/--
theorem `ncard_insert_of_mem` / 定理 `ncard_insert_of_mem`

English:
theorem ncard_insert_of_mem
  given: {a : α} (h : a in s)
  statement: ncard (insert a s) = s.ncard
  proof: by
  rw [insert_eq_of_mem h]

中文:
定理 ncard_insert_of_mem
  条件: {a : α} (h : a in s)
  结论: ncard (insert a s) = s.ncard
  证明: by
  rw [insert_eq_of_mem h]

Depends on / 依赖: insert_eq_of_mem
-/
theorem ncard_insert_of_mem {a : α} (h : a in s) : ncard (insert a s) = s.ncard := by
  rw [insert_eq_of_mem h]

/--
theorem `ncard_insert_le` / 定理 `ncard_insert_le`

English:
theorem ncard_insert_le
  given: (a : α) (s : Set α)
  statement: (insert a s).ncard <= s.ncard + 1
  proof: by
  obtain hs | hs := s.finite_or_infinite
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _

中文:
定理 ncard_insert_le
  条件: (a : α) (s : Set α)
  结论: (insert a s).ncard <= s.ncard + 1
  证明: by
  obtain hs | hs := s.finite_or_infinite
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _

Depends on / 依赖: Nat.zero_le, cast_ncard_eq, encard_insert_le, finite_or_infinite, hs.cast_ncard_eq, hs.insert, hs.mono, insert, s.finite_or_infinite, subset_insert, to_encard_tac, zero_le
-/
theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard <= s.ncard + 1 := by
  obtain hs | hs := s.finite_or_infinite
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _

/--
theorem `one_le_ncard_insert` / 定理 `one_le_ncard_insert`

English:
theorem one_le_ncard_insert
  given: (a : α) (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: Nat.one_le_iff_ne_zero.mpr ncard_ne_zero_of_mem (mem_insert a s) (by simp [hs])

中文:
定理 one_le_ncard_insert
  条件: (a : α) (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: Nat.one_le_iff_ne_zero.mpr ncard_ne_zero_of_mem (mem_insert a s) (by simp [hs])

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, insert, mem_insert, ncard_ne_zero_of_mem, one_le_iff_ne_zero, toFinite_tac
-/
theorem one_le_ncard_insert (a : α) (s : Set α) (hs : s.Finite := by toFinite_tac) :
    1 <= (insert a s).ncard :=
Nat.one_le_iff_ne_zero.mpr ncard_ne_zero_of_mem (mem_insert a s) (by simp [hs])

/--
theorem `ncard_insert_eq_ite` / 定理 `ncard_insert_eq_ite`

English:
theorem ncard_insert_eq_ite
  given: {a : α} [Decidable (a in s)] (hs : s.Finite := by toFinite_tac)
  proof: by
  by_cases h : a in s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_notMem h hs, if_neg h]

中文:
定理 ncard_insert_eq_ite
  条件: {a : α} [Decidable (a in s)] (hs : s.Finite := by toFinite_tac)
  证明: by
  by_cases h : a in s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_notMem h hs, if_neg h]

Depends on / 依赖: if_neg, if_pos, insert, ncard_insert_of_mem, ncard_insert_of_notMem, s.ncard, toFinite_tac
-/
theorem ncard_insert_eq_ite {a : α} [Decidable (a in s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a in s then s.ncard else s.ncard + 1 := by
  by_cases h : a in s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_notMem h hs, if_neg h]

/--
theorem `ncard_le_ncard_insert` / 定理 `ncard_le_ncard_insert`

English:
theorem ncard_le_ncard_insert
  given: (a : α) (s : Set α)
  statement: s.ncard <= (insert a s).ncard
  proof: by
  classical
  refine
    s.finite_or_infinite.elim (fun h => ?_) (fun h => by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp

中文:
定理 ncard_le_ncard_insert
  条件: (a : α) (s : Set α)
  结论: s.ncard <= (insert a s).ncard
  证明: by
  classical
  refine
    s.finite_or_infinite.elim (fun h => ?_) (fun h => by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp

Depends on / 依赖: Nat.zero_le, classical, finite_or_infinite, h.ncard, ncard_insert_eq_ite, s.finite_or_infinite.elim, split_ifs, zero_le
-/
theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard <= (insert a s).ncard := by
  classical
  refine
    s.finite_or_infinite.elim (fun h => ?_) (fun h => by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp

/--
theorem `ncard_pair` / 定理 `ncard_pair`

English:
theorem ncard_pair
  given: {a b : α} (h : a != b)
  statement: ({a, b} : Set α).ncard = 2
  proof: by
  simp [h]

中文:
定理 ncard_pair
  条件: {a b : α} (h : a != b)
  结论: ({a, b} : Set α).ncard = 2
  证明: by
  simp [h]
-/
theorem ncard_pair {a b : α} (h : a != b) : ({a, b} : Set α).ncard = 2 := by
  simp [h]

-- removing `@[simp]` because the LHS is not in simp normal form
/--
theorem `ncard_sdiff_singleton_add_one` / 定理 `ncard_sdiff_singleton_add_one`

English:
theorem ncard_sdiff_singleton_add_one
  statement: {a : α} (h : a in s)
  proof: by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]; rw [encard_sdiff_singleton_add_one h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_add_one := ncard_sdiff_singleton_add_one

中文:
定理 ncard_sdiff_singleton_add_one
  结论: {a : α} (h : a in s)
  证明: by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]; rw [encard_sdiff_singleton_add_one h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_add_one := ncard_sdiff_singleton_add_one

Depends on / 依赖: cast_ncard_eq, encard_sdiff_singleton_add_one, hs.cast_ncard_eq, hs.sdiff.cast_ncard_eq, s.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_sdiff_singleton_add_one {a : α} (h : a in s)
    (hs : s.Finite := by toFinite_tac) : (s \ {a}).ncard + 1 = s.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]; rw [encard_sdiff_singleton_add_one h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_add_one := ncard_sdiff_singleton_add_one

/--
theorem `ncard_sdiff_singleton_of_mem` / 定理 `ncard_sdiff_singleton_of_mem`

English:
theorem ncard_sdiff_singleton_of_mem
  given: {a : α} (h : a in s)
  proof: by
  rcases s.infinite_or_finite with hs | hs
  · simp_all [ncard, Infinite.sdiff hs (finite_singleton a)]
  · exact eq_tsub_of_add_eq (ncard_sdiff_singleton_add_one h hs)

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_of_mem := ncard_sdiff_singleton_of_mem

中文:
定理 ncard_sdiff_singleton_of_mem
  条件: {a : α} (h : a in s)
  证明: by
  rcases s.infinite_or_finite with hs | hs
  · simp_all [ncard, Infinite.sdiff hs (finite_singleton a)]
  · exact eq_tsub_of_add_eq (ncard_sdiff_singleton_add_one h hs)

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_of_mem := ncard_sdiff_singleton_of_mem
-/
@[simp] theorem ncard_sdiff_singleton_of_mem {a : α} (h : a in s) :
    (s \ {a}).ncard = s.ncard - 1 := by
  rcases s.infinite_or_finite with hs | hs
  · simp_all [ncard, Infinite.sdiff hs (finite_singleton a)]
  · exact eq_tsub_of_add_eq (ncard_sdiff_singleton_add_one h hs)

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_of_mem := ncard_sdiff_singleton_of_mem

/--
theorem `ncard_sdiff_singleton_lt_of_mem` / 定理 `ncard_sdiff_singleton_lt_of_mem`

English:
theorem ncard_sdiff_singleton_lt_of_mem
  given: {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_sdiff_singleton_add_one h hs]; apply lt_add_one

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_lt_of_mem := ncard_sdiff_singleton_lt_of_mem

中文:
定理 ncard_sdiff_singleton_lt_of_mem
  条件: {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_sdiff_singleton_add_one h hs]; apply lt_add_one

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_lt_of_mem := ncard_sdiff_singleton_lt_of_mem

Depends on / 依赖: lt_add_one, ncard_sdiff_singleton_add_one, s.ncard, toFinite_tac
-/
theorem ncard_sdiff_singleton_lt_of_mem {a : α} (h : a in s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_sdiff_singleton_add_one h hs]; apply lt_add_one

@[deprecated (since := "2026-06-03")]
alias ncard_diff_singleton_lt_of_mem := ncard_sdiff_singleton_lt_of_mem

/--
theorem `ncard_sdiff_singleton_le` / 定理 `ncard_sdiff_singleton_le`

English:
theorem ncard_sdiff_singleton_le
  given: (s : Set α) (a : α)
  statement: (s \ {a}).ncard <= s.ncard
  proof: by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_ncard sdiff_subset hs
  convert! Nat.zero_le _
  exact (hs.sdiff (by simp)).ncard

@[deprecated (since := "2026-06-03")] alias ncard_diff_singleton_le := ncard_sdiff_singleton_le

中文:
定理 ncard_sdiff_singleton_le
  条件: (s : Set α) (a : α)
  结论: (s \ {a}).ncard <= s.ncard
  证明: by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_ncard sdiff_subset hs
  convert! Nat.zero_le _
  exact (hs.sdiff (by simp)).ncard

@[deprecated (since := "2026-06-03")] alias ncard_diff_singleton_le := ncard_sdiff_singleton_le

Depends on / 依赖: Nat.zero_le, convert, finite_or_infinite, hs.sdiff, ncard_le_ncard, s.finite_or_infinite, sdiff_subset, zero_le
-/
theorem ncard_sdiff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard <= s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_ncard sdiff_subset hs
  convert! Nat.zero_le _
  exact (hs.sdiff (by simp)).ncard

@[deprecated (since := "2026-06-03")] alias ncard_diff_singleton_le := ncard_sdiff_singleton_le

/--
theorem `pred_ncard_le_ncard_sdiff_singleton` / 定理 `pred_ncard_le_ncard_sdiff_singleton`

English:
theorem pred_ncard_le_ncard_sdiff_singleton
  given: (s : Set α) (a : α)
  proof: by
  by_cases h : a in s
  · rw [ncard_sdiff_singleton_of_mem h]
  rw [sdiff_singleton_eq_self h]
  apply Nat.pred_le

@[deprecated (since := "2026-06-03")]
alias pred_ncard_le_ncard_diff_singleton := pred_ncard_le_ncard_sdiff_singleton

中文:
定理 pred_ncard_le_ncard_sdiff_singleton
  条件: (s : Set α) (a : α)
  证明: by
  by_cases h : a in s
  · rw [ncard_sdiff_singleton_of_mem h]
  rw [sdiff_singleton_eq_self h]
  apply Nat.pred_le

@[deprecated (since := "2026-06-03")]
alias pred_ncard_le_ncard_diff_singleton := pred_ncard_le_ncard_sdiff_singleton

Depends on / 依赖: Nat.pred_le, ncard_sdiff_singleton_of_mem, pred_le, sdiff_singleton_eq_self
-/
theorem pred_ncard_le_ncard_sdiff_singleton (s : Set α) (a : α) :
    s.ncard - 1 <= (s \ {a}).ncard := by
  by_cases h : a in s
  · rw [ncard_sdiff_singleton_of_mem h]
  rw [sdiff_singleton_eq_self h]
  apply Nat.pred_le

@[deprecated (since := "2026-06-03")]
alias pred_ncard_le_ncard_diff_singleton := pred_ncard_le_ncard_sdiff_singleton

/--
theorem `ncard_exchange` / 定理 `ncard_exchange`

English:
theorem ncard_exchange
  given: {a b : α} (ha : a ∉ s) (hb : b in s)
  statement: (insert a (s \ {b})).ncard = s.ncard
  proof: congr_arg ENat.toNat encard_exchange ha hb

中文:
定理 ncard_exchange
  条件: {a b : α} (ha : a ∉ s) (hb : b in s)
  结论: (insert a (s \ {b})).ncard = s.ncard
  证明: congr_arg ENat.toNat encard_exchange ha hb

Depends on / 依赖: ENat.toNat, congr_arg, encard_exchange
-/
theorem ncard_exchange {a b : α} (ha : a ∉ s) (hb : b in s) : (insert a (s \ {b})).ncard = s.ncard :=
congr_arg ENat.toNat encard_exchange ha hb

/--
theorem `ncard_exchange'` / 定理 `ncard_exchange'`

English:
theorem ncard_exchange'
  given: {a b : α} (ha : a ∉ s) (hb : b in s)
  proof: by
  rw [← ncard_exchange ha hb]; rw [← singleton_union]; rw [← singleton_union]; rw [union_sdiff_distrib]; rw [sdiff_singleton_eq_self fun h => ha (by rwa [← mem_singleton_iff.mp h])]

中文:
定理 ncard_exchange'
  条件: {a b : α} (ha : a ∉ s) (hb : b in s)
  证明: by
  rw [← ncard_exchange ha hb]; rw [← singleton_union]; rw [← singleton_union]; rw [union_sdiff_distrib]; rw [sdiff_singleton_eq_self fun h => ha (by rwa [← mem_singleton_iff.mp h])]

Depends on / 依赖: mem_singleton_iff, mem_singleton_iff.mp, ncard_exchange, sdiff_singleton_eq_self, singleton_union, union_sdiff_distrib
-/
theorem ncard_exchange' {a b : α} (ha : a ∉ s) (hb : b in s) :
    (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb]; rw [← singleton_union]; rw [← singleton_union]; rw [union_sdiff_distrib]; rw [sdiff_singleton_eq_self fun h => ha (by rwa [← mem_singleton_iff.mp h])]

/--
lemma `odd_card_insert_iff` / 引理 `odd_card_insert_iff`

English:
lemma odd_card_insert_iff
  given: {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.odd_add]
  simp only [← Nat.not_even_iff_odd, Nat.not_even_one, iff_false, Decidable.not_not]

中文:
引理 odd_card_insert_iff
  条件: {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.odd_add]
  simp only [← Nat.not_even_iff_odd, Nat.not_even_one, iff_false, Decidable.not_not]

Depends on / 依赖: Decidable, Decidable.not_not, Nat.not_even_iff_odd, Nat.not_even_one, Nat.odd_add, iff_false, insert, ncard_insert_of_notMem, not_even_iff_odd, not_even_one, not_not, odd_add, s.ncard, toFinite_tac
-/
lemma odd_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Odd (insert a s).ncard ↔ Even s.ncard := by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.odd_add]
  simp only [← Nat.not_even_iff_odd, Nat.not_even_one, iff_false, Decidable.not_not]

/--
lemma `even_card_insert_iff` / 引理 `even_card_insert_iff`

English:
lemma even_card_insert_iff
  given: {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

中文:
引理 even_card_insert_iff
  条件: {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

Depends on / 依赖: Nat.even_add_one, Nat.not_even_iff_odd, even_add_one, insert, ncard_insert_of_notMem, not_even_iff_odd, s.ncard, toFinite_tac
-/
lemma even_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Even (insert a s).ncard ↔ Odd s.ncard := by
  rw [ncard_insert_of_notMem ha hs]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

end InsertErase

variable {f : α -> β}

/--
theorem `ncard_image_le` / 定理 `ncard_image_le`

English:
theorem ncard_image_le
  given: (hs : s.Finite := by toFinite_tac)
  statement: (f '' s).ncard <= s.ncard
  proof: by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le

中文:
定理 ncard_image_le
  条件: (hs : s.Finite := by toFinite_tac)
  结论: (f '' s).ncard <= s.ncard
  证明: by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le

Depends on / 依赖: cast_ncard_eq, encard_image_le, hs.cast_ncard_eq, hs.image, s.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard <= s.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le

/--
theorem `InjOn.ncard_image` / 定理 `InjOn.ncard_image`

English:
theorem InjOn.ncard_image
  given: (H : Set.InjOn f s)
  statement: (f '' s).ncard = s.ncard
  proof: congr_arg ENat.toNat H.encard_image

@[deprecated (since := "2026-01-30")] alias ncard_image_of_injOn := InjOn.ncard_image

中文:
定理 InjOn.ncard_image
  条件: (H : Set.InjOn f s)
  结论: (f '' s).ncard = s.ncard
  证明: congr_arg ENat.toNat H.encard_image

@[deprecated (since := "2026-01-30")] alias ncard_image_of_injOn := InjOn.ncard_image

Depends on / 依赖: ENat.toNat, H.encard_image, congr_arg, encard_image
-/
theorem InjOn.ncard_image (H : Set.InjOn f s) : (f '' s).ncard = s.ncard :=
congr_arg ENat.toNat H.encard_image

@[deprecated (since := "2026-01-30")] alias ncard_image_of_injOn := InjOn.ncard_image

/--
theorem `injOn_of_ncard_image_eq` / 定理 `injOn_of_ncard_image_eq`

English:
theorem injOn_of_ncard_image_eq
  given: (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [(hs.image _).cast_ncard_eq] at h
  exact hs.injOn_of_encard_image_eq h

中文:
定理 injOn_of_ncard_image_eq
  条件: (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [(hs.image _).cast_ncard_eq] at h
  exact hs.injOn_of_encard_image_eq h

Depends on / 依赖: Nat.cast_inj, Set.InjOn, cast_inj, cast_ncard_eq, hs.cast_ncard_eq, hs.image, hs.injOn_of_encard_image_eq, injOn_of_encard_image_eq, toFinite_tac
-/
theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [hs.cast_ncard_eq]; rw [(hs.image _).cast_ncard_eq] at h
  exact hs.injOn_of_encard_image_eq h

/--
theorem `ncard_image_iff` / 定理 `ncard_image_iff`

English:
theorem ncard_image_iff
  given: (hs : s.Finite := by toFinite_tac)
  proof: ⟨fun h => injOn_of_ncard_image_eq h hs, InjOn.ncard_image⟩

中文:
定理 ncard_image_iff
  条件: (hs : s.Finite := by toFinite_tac)
  证明: ⟨fun h => injOn_of_ncard_image_eq h hs, InjOn.ncard_image⟩

Depends on / 依赖: InjOn.ncard_image, Set.InjOn, injOn_of_ncard_image_eq, ncard_image, s.ncard, toFinite_tac
-/
theorem ncard_image_iff (hs : s.Finite := by toFinite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨fun h => injOn_of_ncard_image_eq h hs, InjOn.ncard_image⟩

/--
theorem `ncard_image_of_injective` / 定理 `ncard_image_of_injective`

English:
theorem ncard_image_of_injective
  given: (s : Set α) (H : f.Injective)
  statement: (f '' s).ncard = s.ncard
  proof: H.injOn.ncard_image

中文:
定理 ncard_image_of_injective
  条件: (s : Set α) (H : f.Injective)
  结论: (f '' s).ncard = s.ncard
  证明: H.injOn.ncard_image

Depends on / 依赖: H.injOn.ncard_image, ncard_image
-/
theorem ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  H.injOn.ncard_image

/--
theorem `ncard_preimage_of_injective_subset_range` / 定理 `ncard_preimage_of_injective_subset_range`

English:
theorem ncard_preimage_of_injective_subset_range
  statement: {s : Set β} (H : f.Injective)
  proof: by
  rw [← ncard_image_of_injective _ H]; rw [image_preimage_eq_iff.mpr hs]

中文:
定理 ncard_preimage_of_injective_subset_range
  结论: {s : Set β} (H : f.Injective)
  证明: by
  rw [← ncard_image_of_injective _ H]; rw [image_preimage_eq_iff.mpr hs]

Depends on / 依赖: image_preimage_eq_iff, image_preimage_eq_iff.mpr, ncard_image_of_injective
-/
theorem ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
    (hs : s subseteq Set.range f) :
    (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H]; rw [image_preimage_eq_iff.mpr hs]

/--
theorem `fiber_ncard_ne_zero_iff_mem_image` / 定理 `fiber_ncard_ne_zero_iff_mem_image`

English:
theorem fiber_ncard_ne_zero_iff_mem_image
  given: {y : β} (hs : s.Finite := by toFinite_tac)
  proof: by
  refine ⟨nonempty_of_ncard_ne_zero, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x in s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))

中文:
定理 fiber_ncard_ne_zero_iff_mem_image
  条件: {y : β} (hs : s.Finite := by toFinite_tac)
  证明: by
  refine ⟨nonempty_of_ncard_ne_zero, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x in s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))

Depends on / 依赖: hs.subset, mem_sep, ncard_ne_zero_of_mem, nonempty_of_ncard_ne_zero, sep_subset, subset, toFinite_tac
-/
theorem fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x in s | f x = y }.ncard != 0 ↔ y in f '' s := by
  refine ⟨nonempty_of_ncard_ne_zero, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x in s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))

/--
theorem `ncard_map` / 定理 `ncard_map`

English:
theorem ncard_map
  given: (f : α ↪ β)
  statement: (f '' s).ncard = s.ncard
  proof: ncard_image_of_injective _ f.inj'

中文:
定理 ncard_map
  条件: (f : α ↪ β)
  结论: (f '' s).ncard = s.ncard
  证明: ncard_image_of_injective _ f.inj'
-/
@[simp] theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'

/--
theorem `ncard_subtype` / 定理 `ncard_subtype`

English:
theorem ncard_subtype
  given: (P : α -> Prop) (s : Set α)
  proof: by
  convert! (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [← and_assoc, exists_eq_right]

中文:
定理 ncard_subtype
  条件: (P : α -> 命题) (s : Set α)
  证明: by
  convert! (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [← and_assoc, exists_eq_right]
-/
@[simp] theorem ncard_subtype (P : α -> Prop) (s : Set α) :
    { x : Subtype P | (x : α) in s }.ncard = (s inter Set.ofPred P).ncard := by
  convert! (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [← and_assoc, exists_eq_right]

/--
theorem `ncard_inter_le_ncard_left` / 定理 `ncard_inter_le_ncard_left`

English:
theorem ncard_inter_le_ncard_left
  given: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  proof: ncard_le_ncard inter_subset_left hs

中文:
定理 ncard_inter_le_ncard_left
  条件: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  证明: ncard_le_ncard inter_subset_left hs

Depends on / 依赖: inter_subset_left, ncard_le_ncard, s.ncard, toFinite_tac
-/
theorem ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s inter t).ncard <= s.ncard :=
  ncard_le_ncard inter_subset_left hs

/--
theorem `ncard_inter_le_ncard_right` / 定理 `ncard_inter_le_ncard_right`

English:
theorem ncard_inter_le_ncard_right
  given: (s t : Set α) (ht : t.Finite := by toFinite_tac)
  proof: ncard_le_ncard inter_subset_right ht

中文:
定理 ncard_inter_le_ncard_right
  条件: (s t : Set α) (ht : t.Finite := by toFinite_tac)
  证明: ncard_le_ncard inter_subset_right ht

Depends on / 依赖: inter_subset_right, ncard_le_ncard, t.ncard, toFinite_tac
-/
theorem ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s inter t).ncard <= t.ncard :=
  ncard_le_ncard inter_subset_right ht

/--
theorem `eq_of_subset_of_ncard_le` / 定理 `eq_of_subset_of_ncard_le`

English:
theorem eq_of_subset_of_ncard_le
  statement: (h : s subseteq t) (h' : t.ncard <= s.ncard)
  proof: ht.eq_of_subset_of_encard_le' h
    (by rwa [← Nat.cast_le (α := Nat∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')

中文:
定理 eq_of_subset_of_ncard_le
  结论: (h : s subseteq t) (h' : t.ncard <= s.ncard)
  证明: ht.eq_of_subset_of_encard_le' h
    (by rwa [← Nat.cast_le (α := Nat∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')

Depends on / 依赖: Nat.cast_le, cast_le, cast_ncard_eq, eq_of_subset_of_encard_le, ht.cast_ncard_eq, ht.eq_of_subset_of_encard_le, ht.subset, subset, toFinite_tac
-/
theorem eq_of_subset_of_ncard_le (h : s subseteq t) (h' : t.ncard <= s.ncard)
    (ht : t.Finite := by toFinite_tac) : s = t :=
  ht.eq_of_subset_of_encard_le' h
    (by rwa [← Nat.cast_le (α := Nat∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')

/--
theorem `subset_iff_eq_of_ncard_le` / 定理 `subset_iff_eq_of_ncard_le`

English:
theorem subset_iff_eq_of_ncard_le
  given: (h : t.ncard <= s.ncard) (ht : t.Finite := by toFinite_tac)
  proof: ⟨fun hst => eq_of_subset_of_ncard_le hst h ht, Eq.subset⟩

中文:
定理 subset_iff_eq_of_ncard_le
  条件: (h : t.ncard <= s.ncard) (ht : t.Finite := by toFinite_tac)
  证明: ⟨fun hst => eq_of_subset_of_ncard_le hst h ht, Eq.subset⟩

Depends on / 依赖: Eq.subset, eq_of_subset_of_ncard_le, subset, subseteq, toFinite_tac
-/
theorem subset_iff_eq_of_ncard_le (h : t.ncard <= s.ncard) (ht : t.Finite := by toFinite_tac) :
    s subseteq t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_ncard_le hst h ht, Eq.subset⟩

/--
theorem `map_eq_of_subset` / 定理 `map_eq_of_subset`

English:
theorem map_eq_of_subset
  given: {f : α ↪ α} (h : f '' s subseteq s) (hs : s.Finite := by toFinite_tac)
  proof: eq_of_subset_of_ncard_le h (ncard_map _).ge hs

中文:
定理 map_eq_of_subset
  条件: {f : α ↪ α} (h : f '' s subseteq s) (hs : s.Finite := by toFinite_tac)
  证明: eq_of_subset_of_ncard_le h (ncard_map _).ge hs

Depends on / 依赖: eq_of_subset_of_ncard_le, ncard_map, toFinite_tac
-/
theorem map_eq_of_subset {f : α ↪ α} (h : f '' s subseteq s) (hs : s.Finite := by toFinite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs

/--
theorem `sep_of_ncard_eq` / 定理 `sep_of_ncard_eq`

English:
theorem sep_of_ncard_eq
  statement: {a : α} {P : α -> Prop} (h : { x in s | P x }.ncard = s.ncard) (ha : a in s)
  proof: sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

中文:
定理 sep_of_ncard_eq
  结论: {a : α} {P : α -> 命题} (h : { x in s | P x }.ncard = s.ncard) (ha : a in s)
  证明: sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

Depends on / 依赖: eq_of_subset_of_ncard_le, h.symm.le, sep_eq_self_iff_mem_true, sep_eq_self_iff_mem_true.mp, toFinite_tac
-/
theorem sep_of_ncard_eq {a : α} {P : α -> Prop} (h : { x in s | P x }.ncard = s.ncard) (ha : a in s)
    (hs : s.Finite := by toFinite_tac) : P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

/--
theorem `ncard_lt_ncard` / 定理 `ncard_lt_ncard`

English:
theorem ncard_lt_ncard
  given: (h : s ⊂ t) (ht : t.Finite := by toFinite_tac)
  proof: by
  rw [← Nat.cast_lt (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset h.subset).cast_ncard_eq]
  exact (ht.subset h.subset).encard_lt_encard h

中文:
定理 ncard_lt_ncard
  条件: (h : s ⊂ t) (ht : t.Finite := by toFinite_tac)
  证明: by
  rw [← Nat.cast_lt (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset h.subset).cast_ncard_eq]
  exact (ht.subset h.subset).encard_lt_encard h

Depends on / 依赖: Nat.cast_lt, cast_lt, cast_ncard_eq, encard_lt_encard, h.subset, ht.cast_ncard_eq, ht.subset, s.ncard, subset, t.ncard, toFinite_tac
-/
theorem ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [← Nat.cast_lt (α := Nat∞)]; rw [ht.cast_ncard_eq]; rw [(ht.subset h.subset).cast_ncard_eq]
  exact (ht.subset h.subset).encard_lt_encard h

/--
theorem `ncard_lt_card` / 定理 `ncard_lt_card`

English:
theorem ncard_lt_card
  given: [Finite α] (h : s != univ)
  statement: s.ncard < Nat.card α
  proof: ncard_univ α ▸ ncard_lt_ncard (ssubset_univ_iff.mpr h)

中文:
定理 ncard_lt_card
  条件: [Finite α] (h : s != univ)
  结论: s.ncard < 自然数.card α
  证明: ncard_univ α ▸ ncard_lt_ncard (ssubset_univ_iff.mpr h)

Depends on / 依赖: ncard_lt_ncard, ncard_univ, ssubset_univ_iff, ssubset_univ_iff.mpr
-/
theorem ncard_lt_card [Finite α] (h : s != univ) : s.ncard < Nat.card α :=
  ncard_univ α ▸ ncard_lt_ncard (ssubset_univ_iff.mpr h)

/--
theorem `ncard_strictMono` / 定理 `ncard_strictMono`

English:
theorem ncard_strictMono
  given: [Finite α]
  statement: @StrictMono (Set α) _ _ _ ncard
  proof: fun _ _ h => ncard_lt_ncard h

中文:
定理 ncard_strictMono
  条件: [Finite α]
  结论: @StrictMono (Set α) _ _ _ ncard
  证明: fun _ _ h => ncard_lt_ncard h

Depends on / 依赖: ncard_lt_ncard
-/
theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  fun _ _ h => ncard_lt_ncard h

/--
theorem `Finite.ncard_strictMonoOn` / 定理 `Finite.ncard_strictMonoOn`

English:
theorem Finite.ncard_strictMonoOn
  statement: StrictMonoOn (α := Set α) ncard (Set.ofPred Set.Finite)
  proof: fun _ _ _ ht hlt => ncard_lt_ncard hlt ht

中文:
定理 Finite.ncard_strictMonoOn
  结论: StrictMonoOn (α := Set α) ncard (Set.ofPred Set.Finite)
  证明: fun _ _ _ ht hlt => ncard_lt_ncard hlt ht

Depends on / 依赖: Finite, Set.Finite, Set.ofPred, ofPred
-/
theorem Finite.ncard_strictMonoOn : StrictMonoOn (α := Set α) ncard (Set.ofPred Set.Finite) :=
  fun _ _ _ ht hlt => ncard_lt_ncard hlt ht

/--
theorem `ncard_eq_of_bijective` / 定理 `ncard_eq_of_bijective`

English:
theorem ncard_eq_of_bijective
  statement: {n : Nat} (f : forall i, i < n -> α)
  proof: by
  let f' : Fin n -> α := fun i => f i.val i.is_lt
  suffices himage : s = f' '' Set.univ by
    rw [← Fintype.card_fin n]; rw [← Nat.card_eq_fintype_card]; rw [← Set.ncard_univ]; rw [himage]
exact InjOn.ncard_image fun i _hi j _hj h => Fin.ext f_inj i.val j.val i.is_lt j.is_lt h
  ext x
  simp on

中文:
定理 ncard_eq_of_bijective
  结论: {n : 自然数} (f : 对任意 i, i < n -> α)
  证明: by
  let f' : Fin n -> α := fun i => f i.val i.is_lt
  suffices himage : s = f' '' Set.univ by
    rw [← Fintype.card_fin n]; rw [← Nat.card_eq_fintype_card]; rw [← Set.ncard_univ]; rw [himage]
exact InjOn.ncard_image fun i _hi j _hj h => Fin.ext f_inj i.val j.val i.is_lt j.is_lt h
  ext x
  simp on

Depends on / 依赖: Fin.ext, Fintype, Fintype.card_fin, InjOn.ncard_image, Nat.card_eq_fintype_card, Set.ncard_univ, Set.univ, card_eq_fintype_card, card_fin, f_inj, himage, i.is_lt, i.val, image_univ, is_lt, j.is_lt, j.val, mem_range, ncard_image, ncard_univ
-/
theorem ncard_eq_of_bijective {n : Nat} (f : forall i, i < n -> α)
    (hf : forall a in s, exists i, exists h : i < n, f i h = a) (hf' : forall (i) (h : i < n), f i h in s)
    (f_inj : forall (i j) (hi : i < n) (hj : j < n), f i hi = f j hj -> i = j) : s.ncard = n := by
  let f' : Fin n -> α := fun i => f i.val i.is_lt
  suffices himage : s = f' '' Set.univ by
    rw [← Fintype.card_fin n]; rw [← Nat.card_eq_fintype_card]; rw [← Set.ncard_univ]; rw [himage]
exact InjOn.ncard_image fun i _hi j _hj h => Fin.ext f_inj i.val j.val i.is_lt j.is_lt h
  ext x
  simp only [image_univ, mem_range]
  refine ⟨fun hx => ?_, fun ⟨⟨i, hi⟩, hx⟩ => hx ▸ hf' i hi⟩
  obtain ⟨i, hi, rfl⟩ := hf x hx
  use ⟨i, hi⟩

/--
theorem `ncard_congr` / 定理 `ncard_congr`

English:
theorem ncard_congr
  statement: {t : Set β} (f : forall a in s, β) (h₁ : forall a ha, f a ha in t)
  proof: by
  set f' : s -> t := fun x => ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [f', Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.exists]
   

中文:
定理 ncard_congr
  结论: {t : Set β} (f : 对任意 a in s, β) (h₁ : 对任意 a ha, f a ha in t)
  证明: by
  set f' : s -> t := fun x => ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [f', Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.exists]
   

Depends on / 依赖: Bijective, Equiv.ofBijective, Nat.card_congr, Subtype, Subtype.exists, Subtype.mk.injEq, _root_, _root_.Nat.card_coe_set_eq, card_coe_set_eq, card_congr, ofBijective, simp_rw
-/
theorem ncard_congr {t : Set β} (f : forall a in s, β) (h₁ : forall a ha, f a ha in t)
    (h₂ : forall a b ha hb, f a ha = f b hb -> a = b) (h₃ : forall b in t, exists a ha, f a ha = b) :
    s.ncard = t.ncard := by
  set f' : s -> t := fun x => ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [f', Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  simp_rw [← _root_.Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective f' hbij)

/--
theorem `ncard_congr'` / 定理 `ncard_congr'`

English:
theorem ncard_congr'
  given: {S : Set α} {T : Set β} (f : S ≃ T)
  statement: Set.ncard S = Set.ncard T
  proof: Cardinal.toNat_congr f

中文:
定理 ncard_congr'
  条件: {S : Set α} {T : Set β} (f : S ≃ T)
  结论: Set.ncard S = Set.ncard T
  证明: Cardinal.toNat_congr f

Depends on / 依赖: Cardinal, Cardinal.toNat_congr, toNat_congr
-/
theorem ncard_congr' {S : Set α} {T : Set β} (f : S ≃ T) : Set.ncard S = Set.ncard T :=
  Cardinal.toNat_congr f

/--
theorem `ncard_le_ncard_of_injOn` / 定理 `ncard_le_ncard_of_injOn`

English:
theorem ncard_le_ncard_of_injOn
  statement: {t : Set β} (f : α -> β) (hf : forall a in s, f a in t) (f_inj : InjOn f s)
  proof: by
  have hle := encard_le_encard_of_injOn hf f_inj
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]

中文:
定理 ncard_le_ncard_of_injOn
  结论: {t : Set β} (f : α -> β) (hf : 对任意 a in s, f a in t) (f_inj : InjOn f s)
  证明: by
  have hle := encard_le_encard_of_injOn hf f_inj
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]

Depends on / 依赖: cast_ncard_eq, encard_le_encard_of_injOn, f_inj, finite_of_encard_le, ht.cast_ncard_eq, ht.finite_of_encard_le, s.ncard, t.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_le_ncard_of_injOn {t : Set β} (f : α -> β) (hf : forall a in s, f a in t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard <= t.ncard := by
  have hle := encard_le_encard_of_injOn hf f_inj
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]

/--
theorem `ncard_range_of_injective` / 定理 `ncard_range_of_injective`

English:
theorem ncard_range_of_injective
  given: (hf : Function.Injective f)
  proof: by
  rw [← image_univ]; rw [ncard_image_of_injective univ hf]; rw [ncard_univ]

中文:
定理 ncard_range_of_injective
  条件: (hf : Function.Injective f)
  证明: by
  rw [← image_univ]; rw [ncard_image_of_injective univ hf]; rw [ncard_univ]

Depends on / 依赖: image_univ, ncard_image_of_injective, ncard_univ
-/
theorem ncard_range_of_injective (hf : Function.Injective f) :
    (range f).ncard = Nat.card α := by
  rw [← image_univ]; rw [ncard_image_of_injective univ hf]; rw [ncard_univ]

/--
theorem `BijOn.ncard_eq` / 定理 `BijOn.ncard_eq`

English:
theorem BijOn.ncard_eq
  given: {t : Set β} (h : Set.BijOn f s t)
  statement: s.ncard = t.ncard
  proof: ncard_congr' h.equiv

中文:
定理 BijOn.ncard_eq
  条件: {t : Set β} (h : Set.BijOn f s t)
  结论: s.ncard = t.ncard
  证明: ncard_congr' h.equiv

Depends on / 依赖: h.equiv, ncard_congr
-/
theorem BijOn.ncard_eq {t : Set β} (h : Set.BijOn f s t) : s.ncard = t.ncard := ncard_congr' h.equiv

/--
theorem `exists_ne_map_eq_of_ncard_lt_of_maps_to` / 定理 `exists_ne_map_eq_of_ncard_lt_of_maps_to`

English:
theorem exists_ne_map_eq_of_ncard_lt_of_maps_to
  statement: {t : Set β} (hc : t.ncard < s.ncard) {f : α -> β}
  proof: by
  by_contra h'
  simp only [Ne, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_gt hc

中文:
定理 exists_ne_map_eq_of_ncard_lt_of_maps_to
  结论: {t : Set β} (hc : t.ncard < s.ncard) {f : α -> β}
  证明: by
  by_contra h'
  simp only [Ne, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_gt hc

Depends on / 依赖: ncard_le_ncard_of_injOn, not_and, not_exists, not_gt, not_imp_not, toFinite_tac
-/
theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α -> β}
    (hf : forall a in s, f a in t) (ht : t.Finite := by toFinite_tac) :
    exists x in s, exists y in s, x != y ∧ f x = f y := by
  by_contra h'
  simp only [Ne, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_gt hc

/--
theorem `le_ncard_of_inj_on_range` / 定理 `le_ncard_of_inj_on_range`

English:
theorem le_ncard_of_inj_on_range
  statement: {n : Nat} (f : Nat -> α) (hf : forall i < n, f i in s)
  proof: by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa

中文:
定理 le_ncard_of_inj_on_range
  结论: {n : 自然数} (f : 自然数 -> α) (hf : 对任意 i < n, f i in s)
  证明: by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa

Depends on / 依赖: Finset, Finset.le_card_of_inj_on_range, le_card_of_inj_on_range, ncard_eq_toFinset_card, s.ncard, toFinite_tac
-/
theorem le_ncard_of_inj_on_range {n : Nat} (f : Nat -> α) (hf : forall i < n, f i in s)
    (f_inj : forall i < n, forall j < n, f i = f j -> i = j) (hs : s.Finite := by toFinite_tac) :
    n <= s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa

/--
theorem `surj_on_of_inj_on_of_ncard_le` / 定理 `surj_on_of_inj_on_of_ncard_le`

English:
theorem surj_on_of_inj_on_of_ncard_le
  statement: {t : Set β} (f : forall a in s, β) (hf : forall a ha, f a ha in t)
  proof: by
  intro b hb
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  set f'' : forall a, a in 

中文:
定理 surj_on_of_inj_on_of_ncard_le
  结论: {t : Set β} (f : 对任意 a in s, β) (hf : 对任意 a ha, f a ha in t)
  证明: by
  intro b hb
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  set f'' : forall a, a in 

Depends on / 依赖: Finset, Finset.surj_on_of_inj_on_of_card_le, Fintype, Fintype.ofInjective, Injective, Subtype, Subtype.mk.injEq, convert, fintype, ht.fintype, ofInjective, s.toFinset, surj_on_of_inj_on_of_card_le, t.toFinset, toFinite_tac, toFinset
-/
theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : forall a in s, β) (hf : forall a ha, f a ha in t)
    (hinj : forall a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ = a₂) (hst : t.ncard <= s.ncard)
    (ht : t.Finite := by toFinite_tac) :
    forall b in t, exists a ha, b = f a ha := by
  intro b hb
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  set f'' : forall a, a in s.toFinset -> β := fun a h => f a (by simpa using h)
  convert! @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ _ (by simpa) using 1
  · simp [f'']
  · simp [f'', hf]
  · intro a₁ a₂ ha₁ ha₂ h
    rw [mem_toFinset] at ha₁ ha₂
    exact hinj _ _ ha₁ ha₂ h
  rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card']

/--
theorem `inj_on_of_surj_on_of_ncard_le` / 定理 `inj_on_of_surj_on_of_ncard_le`

English:
theorem inj_on_of_surj_on_of_ncard_le
  statement: {t : Set β} (f : forall a in s, β) (hf : forall a ha, f a ha in t)
  proof: by
  classical
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  have := hs.fintype
  have := Fintype.ofSurjective _ hsurj
  set f'' : forall a, a in s.

中文:
定理 inj_on_of_surj_on_of_ncard_le
  结论: {t : Set β} (f : 对任意 a in s, β) (hf : 对任意 a ha, f a ha in t)
  证明: by
  classical
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  have := hs.fintype
  have := Fintype.ofSurjective _ hsurj
  set f'' : forall a, a in s.

Depends on / 依赖: Finset, Finset.inj_on_of_surj_on_of_card_le, Fintype, Fintype.ofSurjective, Subtype, Subtype.exists, Surjective, classical, fintype, hs.fintype, inj_on_of_surj_on_of_card_le, mem_toFinset, ofSurjective, s.toFinset, t.toFinset, toFinite_tac, toFinset
-/
theorem inj_on_of_surj_on_of_ncard_le {t : Set β} (f : forall a in s, β) (hf : forall a ha, f a ha in t)
    (hsurj : forall b in t, exists a ha, f a ha = b) (hst : s.ncard <= t.ncard) ⦃a₁⦄ (ha₁ : a₁ in s) ⦃a₂⦄
    (ha₂ : a₂ in s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) (hs : s.Finite := by toFinite_tac) :
    a₁ = a₂ := by
  classical
  set f' : s -> t := fun x => ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  have := hs.fintype
  have := Fintype.ofSurjective _ hsurj
  set f'' : forall a, a in s.toFinset -> β := fun a h => f a (by simpa using h)
  exact
    @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.toFinset f''
      (fun a ha => by { rw [mem_toFinset] at ha ⊢; exact hf a ha }) (by simpa)
      (by { rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card'] }) a₁
      (by simpa) a₂ (by simpa) (by simpa)

/--
theorem `ncard_coe` / 定理 `ncard_coe`

English:
theorem ncard_coe
  given: {α : Type*} (s : Set α)
  proof: by simp

中文:
定理 ncard_coe
  条件: {α : 类型} (s : Set α)
  证明: by simp
-/
theorem ncard_coe {α : Type*} (s : Set α) :
    Set.ncard (Set.univ : Set (Set.Elem s)) = s.ncard := by simp

/--
lemma `ncard_graphOn` / 引理 `ncard_graphOn`

English:
lemma ncard_graphOn
  given: (s : Set α) (f : α -> β)
  statement: (s.graphOn f).ncard = s.ncard
  proof: by
  rw [← fst_injOn_graph.ncard_image]; rw [image_fst_graphOn]

中文:
引理 ncard_graphOn
  条件: (s : Set α) (f : α -> β)
  结论: (s.graphOn f).ncard = s.ncard
  证明: by
  rw [← fst_injOn_graph.ncard_image]; rw [image_fst_graphOn]
-/
@[simp] lemma ncard_graphOn (s : Set α) (f : α -> β) : (s.graphOn f).ncard = s.ncard := by
  rw [← fst_injOn_graph.ncard_image]; rw [image_fst_graphOn]

/--
lemma `ncard_powerset_ncard` / 引理 `ncard_powerset_ncard`

English:
lemma ncard_powerset_ncard
  given: (hs : s.Finite) (n : Nat)
  proof: by
  lift s to Finset α using hs
  have h₁ : {t subseteq (s : Set α) | t.ncard = n} subseteq range ((↑) : Finset α -> Set α) := by
    intro t ht
    rw [Finset.mem_range_coe_iff]
    exact s.finite_toSet.subset ht.1
  have h₂ : (↑) ⁻¹' {t subseteq (s : Set α) | t.ncard = n} = (s.powersetCard n : Se

中文:
引理 ncard_powerset_ncard
  条件: (hs : s.Finite) (n : 自然数)
  证明: by
  lift s to Finset α using hs
  have h₁ : {t subseteq (s : Set α) | t.ncard = n} subseteq range ((↑) : Finset α -> Set α) := by
    intro t ht
    rw [Finset.mem_range_coe_iff]
    exact s.finite_toSet.subset ht.1
  have h₂ : (↑) ⁻¹' {t subseteq (s : Set α) | t.ncard = n} = (s.powersetCard n : Se

Depends on / 依赖: Finset, Finset.card_powersetCard, Finset.mem_range_coe_iff, card_powersetCard, finite_toSet, mem_range_coe_iff, ncard_coe_finset, ncard_preimage_of_injective_subset_range, powersetCard, s.finite_toSet.subset, s.powersetCard, subset, subseteq, t.ncard
-/
lemma ncard_powerset_ncard (hs : s.Finite) (n : Nat) :
    {t subseteq s | t.ncard = n}.ncard = s.ncard.choose n := by
  lift s to Finset α using hs
  have h₁ : {t subseteq (s : Set α) | t.ncard = n} subseteq range ((↑) : Finset α -> Set α) := by
    intro t ht
    rw [Finset.mem_range_coe_iff]
    exact s.finite_toSet.subset ht.1
  have h₂ : (↑) ⁻¹' {t subseteq (s : Set α) | t.ncard = n} = (s.powersetCard n : Set (Finset α)) := by
    ext t
    simp
  grind [ncard_coe_finset, ncard_preimage_of_injective_subset_range, Finset.card_powersetCard]

section Lattice

/--
theorem `ncard_union_add_ncard_inter` / 定理 `ncard_union_add_ncard_inter`

English:
theorem ncard_union_add_ncard_inter
  statement: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
    (hs.subset inter_subset_left).cast_ncard_eq, encard_union_add_encard_inter]

中文:
定理 ncard_union_add_ncard_inter
  结论: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
    (hs.subset inter_subset_left).cast_ncard_eq, encard_union_add_encard_inter]

Depends on / 依赖: Finite, cast_ncard_eq, encard_union_add_encard_inter, hs.cast_ncard_eq, hs.subset, hs.union, ht.cast_ncard_eq, inter_subset_left, s.ncard, subset, t.Finite, t.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s union t).ncard + (s inter t).ncard = s.ncard + t.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
    (hs.subset inter_subset_left).cast_ncard_eq, encard_union_add_encard_inter]

/--
theorem `ncard_inter_add_ncard_union` / 定理 `ncard_inter_add_ncard_union`

English:
theorem ncard_inter_add_ncard_union
  statement: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [add_comm]; rw [ncard_union_add_ncard_inter _ _ hs ht]

中文:
定理 ncard_inter_add_ncard_union
  结论: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [add_comm]; rw [ncard_union_add_ncard_inter _ _ hs ht]

Depends on / 依赖: Finite, add_comm, ncard_union_add_ncard_inter, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s inter t).ncard + (s union t).ncard = s.ncard + t.ncard := by
  rw [add_comm]; rw [ncard_union_add_ncard_inter _ _ hs ht]

/--
theorem `ncard_union_le` / 定理 `ncard_union_le`

English:
theorem ncard_union_le
  given: (s t : Set α)
  statement: (s union t).ncard <= s.ncard + t.ncard
  proof: by
  obtain (h | h) := (s union t).finite_or_infinite
  · to_encard_tac
    rw [h.cast_ncard_eq]; rw [(h.subset subset_union_left).cast_ncard_eq]; rw [(h.subset subset_union_right).cast_ncard_eq]
    apply encard_union_le
  rw [h.ncard]
  apply zero_le

中文:
定理 ncard_union_le
  条件: (s t : Set α)
  结论: (s union t).ncard <= s.ncard + t.ncard
  证明: by
  obtain (h | h) := (s union t).finite_or_infinite
  · to_encard_tac
    rw [h.cast_ncard_eq]; rw [(h.subset subset_union_left).cast_ncard_eq]; rw [(h.subset subset_union_right).cast_ncard_eq]
    apply encard_union_le
  rw [h.ncard]
  apply zero_le

Depends on / 依赖: cast_ncard_eq, encard_union_le, finite_or_infinite, h.cast_ncard_eq, h.ncard, h.subset, subset, subset_union_left, subset_union_right, to_encard_tac, zero_le
-/
theorem ncard_union_le (s t : Set α) : (s union t).ncard <= s.ncard + t.ncard := by
  obtain (h | h) := (s union t).finite_or_infinite
  · to_encard_tac
    rw [h.cast_ncard_eq]; rw [(h.subset subset_union_left).cast_ncard_eq]; rw [(h.subset subset_union_right).cast_ncard_eq]
    apply encard_union_le
  rw [h.ncard]
  apply zero_le

/--
theorem `ncard_union_eq` / 定理 `ncard_union_eq`

English:
theorem ncard_union_eq
  statement: (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
  proof: by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [ht.cast_ncard_eq]; rw [(hs.union ht).cast_ncard_eq]; rw [encard_union_eq h]

中文:
定理 ncard_union_eq
  结论: (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
  证明: by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [ht.cast_ncard_eq]; rw [(hs.union ht).cast_ncard_eq]; rw [encard_union_eq h]

Depends on / 依赖: Finite, cast_ncard_eq, encard_union_eq, hs.cast_ncard_eq, hs.union, ht.cast_ncard_eq, s.ncard, t.Finite, t.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s union t).ncard = s.ncard + t.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq]; rw [ht.cast_ncard_eq]; rw [(hs.union ht).cast_ncard_eq]; rw [encard_union_eq h]

/--
theorem `ncard_union_eq_iff` / 定理 `ncard_union_eq_iff`

English:
theorem ncard_union_eq_iff
  statement: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_union_add_ncard_inter s t hs ht]; rw [left_eq_add]; rw [ncard_eq_zero (hs.inter_of_left t)]; rw [disjoint_iff_inter_eq_empty]

中文:
定理 ncard_union_eq_iff
  结论: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_union_add_ncard_inter s t hs ht]; rw [left_eq_add]; rw [ncard_eq_zero (hs.inter_of_left t)]; rw [disjoint_iff_inter_eq_empty]

Depends on / 依赖: Disjoint, Finite, disjoint_iff_inter_eq_empty, hs.inter_of_left, inter_of_left, left_eq_add, ncard_eq_zero, ncard_union_add_ncard_inter, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_union_eq_iff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s union t).ncard = s.ncard + t.ncard ↔ Disjoint s t := by
  rw [← ncard_union_add_ncard_inter s t hs ht]; rw [left_eq_add]; rw [ncard_eq_zero (hs.inter_of_left t)]; rw [disjoint_iff_inter_eq_empty]

/--
theorem `ncard_union_lt` / 定理 `ncard_union_lt`

English:
theorem ncard_union_lt
  statement: (hs : s.Finite := by toFinite_tac)
  proof: (ncard_union_le s t).lt_of_ne (mt (ncard_union_eq_iff hs ht).mp h)

中文:
定理 ncard_union_lt
  结论: (hs : s.Finite := by toFinite_tac)
  证明: (ncard_union_le s t).lt_of_ne (mt (ncard_union_eq_iff hs ht).mp h)

Depends on / 依赖: Disjoint, Finite, lt_of_ne, ncard_union_eq_iff, ncard_union_le, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_union_lt (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) (h : ¬ Disjoint s t) :
    (s union t).ncard < s.ncard + t.ncard :=
  (ncard_union_le s t).lt_of_ne (mt (ncard_union_eq_iff hs ht).mp h)

/--
theorem `ncard_sdiff_add_ncard_of_subset` / 定理 `ncard_sdiff_add_ncard_of_subset`

English:
theorem ncard_sdiff_add_ncard_of_subset
  given: (h : s subseteq t) (ht : t.Finite := by toFinite_tac)
  proof: by
  to_encard_tac
  rw [ht.cast_ncard_eq]; rw [(ht.subset h).cast_ncard_eq]; rw [ht.sdiff.cast_ncard_eq]; rw [encard_sdiff_add_encard_of_subset h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_add_ncard_of_subset := ncard_sdiff_add_ncard_of_subset

中文:
定理 ncard_sdiff_add_ncard_of_subset
  条件: (h : s subseteq t) (ht : t.Finite := by toFinite_tac)
  证明: by
  to_encard_tac
  rw [ht.cast_ncard_eq]; rw [(ht.subset h).cast_ncard_eq]; rw [ht.sdiff.cast_ncard_eq]; rw [encard_sdiff_add_encard_of_subset h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_add_ncard_of_subset := ncard_sdiff_add_ncard_of_subset

Depends on / 依赖: cast_ncard_eq, encard_sdiff_add_encard_of_subset, ht.cast_ncard_eq, ht.sdiff.cast_ncard_eq, ht.subset, s.ncard, subset, t.ncard, toFinite_tac, to_encard_tac
-/
theorem ncard_sdiff_add_ncard_of_subset (h : s subseteq t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  to_encard_tac
  rw [ht.cast_ncard_eq]; rw [(ht.subset h).cast_ncard_eq]; rw [ht.sdiff.cast_ncard_eq]; rw [encard_sdiff_add_encard_of_subset h]

@[deprecated (since := "2026-06-03")]
alias ncard_diff_add_ncard_of_subset := ncard_sdiff_add_ncard_of_subset

/--
theorem `ncard_sdiff'` / 定理 `ncard_sdiff'`

English:
theorem ncard_sdiff'
  given: (hst : s subseteq t) (ht : t.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_sdiff_add_ncard_of_subset hst ht]; rw [add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")] alias ncard_diff' := ncard_sdiff'

中文:
定理 ncard_sdiff'
  条件: (hst : s subseteq t) (ht : t.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_sdiff_add_ncard_of_subset hst ht]; rw [add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")] alias ncard_diff' := ncard_sdiff'

Depends on / 依赖: add_tsub_cancel_right, ncard_sdiff_add_ncard_of_subset, s.ncard, t.ncard, toFinite_tac
-/
theorem ncard_sdiff' (hst : s subseteq t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_sdiff_add_ncard_of_subset hst ht]; rw [add_tsub_cancel_right]

@[deprecated (since := "2026-06-03")] alias ncard_diff' := ncard_sdiff'

/--
theorem `ncard_sdiff` / 定理 `ncard_sdiff`

English:
theorem ncard_sdiff
  given: (hst : s subseteq t) (hs : s.Finite := by toFinite_tac)
  proof: by
  obtain ht | ht := t.finite_or_infinite
  · exact ncard_sdiff' hst ht
  · rw [ht.ncard, Nat.zero_sub, (ht.sdiff hs).ncard]

@[deprecated (since := "2026-06-03")] alias ncard_diff := ncard_sdiff

中文:
定理 ncard_sdiff
  条件: (hst : s subseteq t) (hs : s.Finite := by toFinite_tac)
  证明: by
  obtain ht | ht := t.finite_or_infinite
  · exact ncard_sdiff' hst ht
  · rw [ht.ncard, Nat.zero_sub, (ht.sdiff hs).ncard]

@[deprecated (since := "2026-06-03")] alias ncard_diff := ncard_sdiff

Depends on / 依赖: Nat.zero_sub, finite_or_infinite, ht.ncard, ht.sdiff, ncard_sdiff, s.ncard, t.finite_or_infinite, t.ncard, toFinite_tac, zero_sub
-/
theorem ncard_sdiff (hst : s subseteq t) (hs : s.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  obtain ht | ht := t.finite_or_infinite
  · exact ncard_sdiff' hst ht
  · rw [ht.ncard, Nat.zero_sub, (ht.sdiff hs).ncard]

@[deprecated (since := "2026-06-03")] alias ncard_diff := ncard_sdiff

/--
lemma `cast_ncard_sdiff` / 引理 `cast_ncard_sdiff`

English:
lemma cast_ncard_sdiff
  given: {R : Type*} [AddGroupWithOne R] (hst : s subseteq t) (ht : t.Finite)
  proof: by
  rw [ncard_sdiff hst (ht.subset hst)]; rw [Nat.cast_sub (ncard_le_ncard hst ht)]

中文:
引理 cast_ncard_sdiff
  条件: {R : 类型} [AddGroupWithOne R] (hst : s subseteq t) (ht : t.Finite)
  证明: by
  rw [ncard_sdiff hst (ht.subset hst)]; rw [Nat.cast_sub (ncard_le_ncard hst ht)]

Depends on / 依赖: Nat.cast_sub, cast_sub, ht.subset, ncard_le_ncard, ncard_sdiff, subset
-/
lemma cast_ncard_sdiff {R : Type*} [AddGroupWithOne R] (hst : s subseteq t) (ht : t.Finite) :
    ((t \ s).ncard : R) = t.ncard - s.ncard := by
  rw [ncard_sdiff hst (ht.subset hst)]; rw [Nat.cast_sub (ncard_le_ncard hst ht)]

/--
theorem `ncard_le_ncard_sdiff_add_ncard` / 定理 `ncard_le_ncard_sdiff_add_ncard`

English:
theorem ncard_le_ncard_sdiff_add_ncard
  given: (s t : Set α) (ht : t.Finite := by toFinite_tac)
  proof: by
  rcases s.finite_or_infinite with hs | hs
  · to_encard_tac
    rw [ht.cast_ncard_eq]; rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]
    apply encard_le_encard_sdiff_add_encard
  convert! Nat.zero_le _
  rw [hs.ncard]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_diff_add_ncar

中文:
定理 ncard_le_ncard_sdiff_add_ncard
  条件: (s t : Set α) (ht : t.Finite := by toFinite_tac)
  证明: by
  rcases s.finite_or_infinite with hs | hs
  · to_encard_tac
    rw [ht.cast_ncard_eq]; rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]
    apply encard_le_encard_sdiff_add_encard
  convert! Nat.zero_le _
  rw [hs.ncard]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_diff_add_ncar

Depends on / 依赖: Nat.zero_le, cast_ncard_eq, convert, encard_le_encard_sdiff_add_encard, finite_or_infinite, hs.cast_ncard_eq, hs.ncard, hs.sdiff.cast_ncard_eq, ht.cast_ncard_eq, s.finite_or_infinite, s.ncard, t.ncard, toFinite_tac, to_encard_tac, zero_le
-/
theorem ncard_le_ncard_sdiff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard <= (s \ t).ncard + t.ncard := by
  rcases s.finite_or_infinite with hs | hs
  · to_encard_tac
    rw [ht.cast_ncard_eq]; rw [hs.cast_ncard_eq]; rw [hs.sdiff.cast_ncard_eq]
    apply encard_le_encard_sdiff_add_encard
  convert! Nat.zero_le _
  rw [hs.ncard]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_diff_add_ncard := ncard_le_ncard_sdiff_add_ncard

/--
theorem `le_ncard_sdiff` / 定理 `le_ncard_sdiff`

English:
theorem le_ncard_sdiff
  given: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  proof: tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_sdiff_add_ncard _ _ hs)

@[deprecated (since := "2026-06-03")] alias le_ncard_diff := le_ncard_sdiff

中文:
定理 le_ncard_sdiff
  条件: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  证明: tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_sdiff_add_ncard _ _ hs)

@[deprecated (since := "2026-06-03")] alias le_ncard_diff := le_ncard_sdiff

Depends on / 依赖: add_comm, ncard_le_ncard_sdiff_add_ncard, s.ncard, t.ncard, toFinite_tac, tsub_le_iff_left, tsub_le_iff_left.mpr
-/
theorem le_ncard_sdiff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard <= (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_sdiff_add_ncard _ _ hs)

@[deprecated (since := "2026-06-03")] alias le_ncard_diff := le_ncard_sdiff

/--
theorem `ncard_sdiff_add_ncard` / 定理 `ncard_sdiff_add_ncard`

English:
theorem ncard_sdiff_add_ncard
  statement: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_union_eq disjoint_sdiff_left hs.sdiff ht]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias ncard_diff_add_ncard := ncard_sdiff_add_ncard

中文:
定理 ncard_sdiff_add_ncard
  结论: (s t : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_union_eq disjoint_sdiff_left hs.sdiff ht]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias ncard_diff_add_ncard := ncard_sdiff_add_ncard

Depends on / 依赖: Finite, disjoint_sdiff_left, hs.sdiff, ncard_union_eq, sdiff_union_self, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_sdiff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s union t).ncard := by
  rw [← ncard_union_eq disjoint_sdiff_left hs.sdiff ht]; rw [sdiff_union_self]

@[deprecated (since := "2026-06-03")] alias ncard_diff_add_ncard := ncard_sdiff_add_ncard

/--
theorem `sdiff_nonempty_of_ncard_lt_ncard` / 定理 `sdiff_nonempty_of_ncard_lt_ncard`

English:
theorem sdiff_nonempty_of_ncard_lt_ncard
  statement: (h : s.ncard < t.ncard)
  proof: by
  rw [Set.nonempty_iff_ne_empty]; rw [Ne]; rw [sdiff_eq_empty]
  exact fun h' => h.not_ge (ncard_le_ncard h' hs)

@[deprecated (since := "2026-06-03")]
alias diff_nonempty_of_ncard_lt_ncard := sdiff_nonempty_of_ncard_lt_ncard

中文:
定理 sdiff_nonempty_of_ncard_lt_ncard
  结论: (h : s.ncard < t.ncard)
  证明: by
  rw [Set.nonempty_iff_ne_empty]; rw [Ne]; rw [sdiff_eq_empty]
  exact fun h' => h.not_ge (ncard_le_ncard h' hs)

@[deprecated (since := "2026-06-03")]
alias diff_nonempty_of_ncard_lt_ncard := sdiff_nonempty_of_ncard_lt_ncard

Depends on / 依赖: Nonempty, Set.nonempty_iff_ne_empty, h.not_ge, ncard_le_ncard, nonempty_iff_ne_empty, not_ge, sdiff_eq_empty, toFinite_tac
-/
theorem sdiff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by toFinite_tac) : (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]; rw [Ne]; rw [sdiff_eq_empty]
  exact fun h' => h.not_ge (ncard_le_ncard h' hs)

@[deprecated (since := "2026-06-03")]
alias diff_nonempty_of_ncard_lt_ncard := sdiff_nonempty_of_ncard_lt_ncard

/--
theorem `exists_mem_notMem_of_ncard_lt_ncard` / 定理 `exists_mem_notMem_of_ncard_lt_ncard`

English:
theorem exists_mem_notMem_of_ncard_lt_ncard
  statement: (h : s.ncard < t.ncard)
  proof: sdiff_nonempty_of_ncard_lt_ncard h hs

中文:
定理 exists_mem_notMem_of_ncard_lt_ncard
  结论: (h : s.ncard < t.ncard)
  证明: sdiff_nonempty_of_ncard_lt_ncard h hs

Depends on / 依赖: sdiff_nonempty_of_ncard_lt_ncard, toFinite_tac
-/
theorem exists_mem_notMem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by toFinite_tac) : exists e, e in t ∧ e ∉ s :=
  sdiff_nonempty_of_ncard_lt_ncard h hs

/--
theorem `ncard_inter_add_ncard_sdiff_eq_ncard` / 定理 `ncard_inter_add_ncard_sdiff_eq_ncard`

English:
theorem ncard_inter_add_ncard_sdiff_eq_ncard
  statement: (s t : Set α)
  proof: by
  rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
    (hs.inter_of_left _) hs.sdiff]; rw [union_comm]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias ncard_inter_add_ncard_diff_eq_ncard := ncard_inter_add_ncard_sdiff_eq_ncard

中文:
定理 ncard_inter_add_ncard_sdiff_eq_ncard
  结论: (s t : Set α)
  证明: by
  rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
    (hs.inter_of_left _) hs.sdiff]; rw [union_comm]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias ncard_inter_add_ncard_diff_eq_ncard := ncard_inter_add_ncard_sdiff_eq_ncard
-/
@[simp] theorem ncard_inter_add_ncard_sdiff_eq_ncard (s t : Set α)
    (hs : s.Finite := by toFinite_tac) : (s inter t).ncard + (s \ t).ncard = s.ncard := by
  rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
    (hs.inter_of_left _) hs.sdiff]; rw [union_comm]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")]
alias ncard_inter_add_ncard_diff_eq_ncard := ncard_inter_add_ncard_sdiff_eq_ncard

/--
theorem `ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff` / 定理 `ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff`

English:
theorem ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff
  statement: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_right_inj]

@[deprecated (since := "2026-06-03")]
alias ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff := ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff

中文:
定理 ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff
  结论: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_right_inj]

@[deprecated (since := "2026-06-03")]
alias ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff := ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff

Depends on / 依赖: Finite, add_right_inj, inter_comm, ncard_inter_add_ncard_sdiff_eq_ncard, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_right_inj]

@[deprecated (since := "2026-06-03")]
alias ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff := ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff

/--
theorem `ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff` / 定理 `ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff`

English:
theorem ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff
  statement: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_le_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_iff_ncard_diff_le_ncard_diff := ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff

中文:
定理 ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff
  结论: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_le_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_iff_ncard_diff_le_ncard_diff := ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff

Depends on / 依赖: Finite, add_le_add_iff_left, inter_comm, ncard_inter_add_ncard_sdiff_eq_ncard, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard <= t.ncard ↔ (s \ t).ncard <= (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_le_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_le_ncard_iff_ncard_diff_le_ncard_diff := ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff

/--
theorem `ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff` / 定理 `ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff`

English:
theorem ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff
  statement: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_lt_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff := ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff

中文:
定理 ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff
  结论: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_lt_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff := ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff

Depends on / 依赖: Finite, add_lt_add_iff_left, inter_comm, ncard_inter_add_ncard_sdiff_eq_ncard, s.ncard, t.Finite, t.ncard, toFinite_tac
-/
theorem ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard s t hs]; rw [← ncard_inter_add_ncard_sdiff_eq_ncard t s ht]; rw [inter_comm]; rw [add_lt_add_iff_left]

@[deprecated (since := "2026-06-03")]
alias ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff := ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff

/--
theorem `ncard_add_ncard_compl` / 定理 `ncard_add_ncard_compl`

English:
theorem ncard_add_ncard_compl
  statement: (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_univ]; rw [← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc]; rw [union_compl_self]

中文:
定理 ncard_add_ncard_compl
  结论: (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_univ]; rw [← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc]; rw [union_compl_self]

Depends on / 依赖: Finite, Nat.card, disjoint_compl_right, ncard_union_eq, ncard_univ, s.ncard, toFinite_tac, union_compl_self
-/
theorem ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ]; rw [← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc]; rw [union_compl_self]

/--
theorem `ncard_compl_add_ncard` / 定理 `ncard_compl_add_ncard`

English:
theorem ncard_compl_add_ncard
  statement: (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [add_comm]; rw [ncard_add_ncard_compl s hs hsc]

中文:
定理 ncard_compl_add_ncard
  结论: (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [add_comm]; rw [ncard_add_ncard_compl s hs hsc]

Depends on / 依赖: Finite, Nat.card, add_comm, ncard_add_ncard_compl, s.ncard, toFinite_tac
-/
theorem ncard_compl_add_ncard (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : sᶜ.ncard + s.ncard = Nat.card α := by
  rw [add_comm]; rw [ncard_add_ncard_compl s hs hsc]

/--
theorem `ncard_compl` / 定理 `ncard_compl`

English:
theorem ncard_compl
  statement: (s : Set α) (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [← ncard_add_ncard_compl s hs hsc]; rw [Nat.add_sub_cancel_left]

中文:
定理 ncard_compl
  结论: (s : Set α) (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [← ncard_add_ncard_compl s hs hsc]; rw [Nat.add_sub_cancel_left]

Depends on / 依赖: Finite, Nat.add_sub_cancel_left, Nat.card, add_sub_cancel_left, ncard_add_ncard_compl, s.ncard, toFinite_tac
-/
theorem ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : sᶜ.ncard = Nat.card α - s.ncard := by
  rw [← ncard_add_ncard_compl s hs hsc]; rw [Nat.add_sub_cancel_left]

/--
theorem `ncard_compl_of_ncard_eq_add` / 定理 `ncard_compl_of_ncard_eq_add`

English:
theorem ncard_compl_of_ncard_eq_add
  statement: [Finite α] (s : Set α) {n : Nat}
  proof: by
  rwa [← ncard_compl_add_ncard s, Nat.add_right_cancel_iff] at h

中文:
定理 ncard_compl_of_ncard_eq_add
  结论: [Finite α] (s : Set α) {n : 自然数}
  证明: by
  rwa [← ncard_compl_add_ncard s, Nat.add_right_cancel_iff] at h

Depends on / 依赖: Nat.add_right_cancel_iff, add_right_cancel_iff, ncard_compl_add_ncard
-/
theorem ncard_compl_of_ncard_eq_add [Finite α] (s : Set α) {n : Nat}
    (h : Nat.card α = n + s.ncard) :
    sᶜ.ncard = n := by
  rwa [← ncard_compl_add_ncard s, Nat.add_right_cancel_iff] at h

/--
theorem `eq_univ_iff_ncard` / 定理 `eq_univ_iff_ncard`

English:
theorem eq_univ_iff_ncard
  given: [Finite α] (s : Set α)
  proof: by
  rw [← compl_empty_iff]; rw [← ncard_eq_zero]; rw [← ncard_add_ncard_compl s]; rw [left_eq_add]

中文:
定理 eq_univ_iff_ncard
  条件: [Finite α] (s : Set α)
  证明: by
  rw [← compl_empty_iff]; rw [← ncard_eq_zero]; rw [← ncard_add_ncard_compl s]; rw [left_eq_add]

Depends on / 依赖: compl_empty_iff, left_eq_add, ncard_add_ncard_compl, ncard_eq_zero
-/
theorem eq_univ_iff_ncard [Finite α] (s : Set α) :
    s = univ ↔ ncard s = Nat.card α := by
  rw [← compl_empty_iff]; rw [← ncard_eq_zero]; rw [← ncard_add_ncard_compl s]; rw [left_eq_add]

/--
lemma `even_ncard_compl_iff` / 引理 `even_ncard_compl_iff`

English:
lemma even_ncard_compl_iff
  given: [Finite α] (heven : Even (Nat.card α)) (s : Set α)
  proof: by
  rwa [iff_comm, ← Nat.even_add, ncard_add_ncard_compl]

中文:
引理 even_ncard_compl_iff
  条件: [Finite α] (heven : Even (自然数.card α)) (s : Set α)
  证明: by
  rwa [iff_comm, ← Nat.even_add, ncard_add_ncard_compl]

Depends on / 依赖: Nat.even_add, even_add, iff_comm, ncard_add_ncard_compl
-/
lemma even_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Even sᶜ.ncard ↔ Even s.ncard := by
  rwa [iff_comm, ← Nat.even_add, ncard_add_ncard_compl]

/--
lemma `odd_ncard_compl_iff` / 引理 `odd_ncard_compl_iff`

English:
lemma odd_ncard_compl_iff
  given: [Finite α] (heven : Even (Nat.card α)) (s : Set α)
  proof: by
  rw [← Nat.not_even_iff_odd]; rw [even_ncard_compl_iff heven]; rw [Nat.not_even_iff_odd]

中文:
引理 odd_ncard_compl_iff
  条件: [Finite α] (heven : Even (自然数.card α)) (s : Set α)
  证明: by
  rw [← Nat.not_even_iff_odd]; rw [even_ncard_compl_iff heven]; rw [Nat.not_even_iff_odd]

Depends on / 依赖: Nat.not_even_iff_odd, even_ncard_compl_iff, not_even_iff_odd
-/
lemma odd_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Odd sᶜ.ncard ↔ Odd s.ncard := by
  rw [← Nat.not_even_iff_odd]; rw [even_ncard_compl_iff heven]; rw [Nat.not_even_iff_odd]

/--
theorem `nonempty_inter_of_lt_ncard_add_ncard` / 定理 `nonempty_inter_of_lt_ncard_add_ncard`

English:
theorem nonempty_inter_of_lt_ncard_add_ncard
  statement: [Finite α]
  proof: by
  rw [← ncard_union_add_ncard_inter s t] at h
  replace h := (s union t).ncard_le_card.trans_lt h
  rwa [lt_add_iff_pos_right, ncard_pos] at h

中文:
定理 nonempty_inter_of_lt_ncard_add_ncard
  结论: [Finite α]
  证明: by
  rw [← ncard_union_add_ncard_inter s t] at h
  replace h := (s union t).ncard_le_card.trans_lt h
  rwa [lt_add_iff_pos_right, ncard_pos] at h

Depends on / 依赖: lt_add_iff_pos_right, ncard_le_card, ncard_le_card.trans_lt, ncard_pos, ncard_union_add_ncard_inter, replace, trans_lt
-/
theorem nonempty_inter_of_lt_ncard_add_ncard [Finite α]
    (h : Nat.card α < s.ncard + t.ncard) : (s inter t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h
  replace h := (s union t).ncard_le_card.trans_lt h
  rwa [lt_add_iff_pos_right, ncard_pos] at h

/--
theorem `nonempty_inter_of_le_ncard_add_ncard` / 定理 `nonempty_inter_of_le_ncard_add_ncard`

English:
theorem nonempty_inter_of_le_ncard_add_ncard
  statement: [Finite α]
  proof: by
  rw [← ncard_union_add_ncard_inter s t] at h'
  replace h := (ncard_lt_card h).trans_le h'
  rwa [lt_add_iff_pos_right, ncard_pos] at h

中文:
定理 nonempty_inter_of_le_ncard_add_ncard
  结论: [Finite α]
  证明: by
  rw [← ncard_union_add_ncard_inter s t] at h'
  replace h := (ncard_lt_card h).trans_le h'
  rwa [lt_add_iff_pos_right, ncard_pos] at h

Depends on / 依赖: lt_add_iff_pos_right, ncard_lt_card, ncard_pos, ncard_union_add_ncard_inter, replace, trans_le
-/
theorem nonempty_inter_of_le_ncard_add_ncard [Finite α]
    (h' : Nat.card α <= s.ncard + t.ncard) (h : s union t != univ) :
    (s inter t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h'
  replace h := (ncard_lt_card h).trans_le h'
  rwa [lt_add_iff_pos_right, ncard_pos] at h

/--
theorem `union_ne_univ_of_ncard_add_ncard_lt` / 定理 `union_ne_univ_of_ncard_add_ncard_lt`

English:
theorem union_ne_univ_of_ncard_add_ncard_lt
  proof: by
  contrapose! h
  rw [← ncard_univ]; rw [← h]
  exact ncard_union_le s t

中文:
定理 union_ne_univ_of_ncard_add_ncard_lt
  证明: by
  contrapose! h
  rw [← ncard_univ]; rw [← h]
  exact ncard_union_le s t

Depends on / 依赖: contrapose, ncard_union_le, ncard_univ
-/
theorem union_ne_univ_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : s union t != univ := by
  contrapose! h
  rw [← ncard_univ]; rw [← h]
  exact ncard_union_le s t

/--
theorem `nonempty_inter_compl_of_ncard_add_ncard_lt` / 定理 `nonempty_inter_compl_of_ncard_add_ncard_lt`

English:
theorem nonempty_inter_compl_of_ncard_add_ncard_lt
  proof: by
  rw [← compl_union]; rw [nonempty_compl]
  exact union_ne_univ_of_ncard_add_ncard_lt h

中文:
定理 nonempty_inter_compl_of_ncard_add_ncard_lt
  证明: by
  rw [← compl_union]; rw [nonempty_compl]
  exact union_ne_univ_of_ncard_add_ncard_lt h

Depends on / 依赖: compl_union, nonempty_compl, union_ne_univ_of_ncard_add_ncard_lt
-/
theorem nonempty_inter_compl_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : (sᶜ inter tᶜ).Nonempty := by
  rw [← compl_union]; rw [nonempty_compl]
  exact union_ne_univ_of_ncard_add_ncard_lt h

end Lattice

/--
lemma `exists_subsuperset_card_eq` / 引理 `exists_subsuperset_card_eq`

English:
lemma exists_subsuperset_card_eq
  given: {n : Nat} (hst : s subseteq t) (hsn : s.ncard <= n) (hnt : n <= t.ncard)
  proof: by
  obtain ht | ht := t.infinite_or_finite
  · rw [ht.ncard, Nat.le_zero, ← ht.ncard] at hnt
    exact ⟨t, hst, Subset.rfl, hnt.symm⟩
  lift s to Finset α using ht.subset hst
  lift t to Finset α using ht
  obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq (mod_cast hst) (by simpa using

中文:
引理 exists_subsuperset_card_eq
  条件: {n : 自然数} (hst : s subseteq t) (hsn : s.ncard <= n) (hnt : n <= t.ncard)
  证明: by
  obtain ht | ht := t.infinite_or_finite
  · rw [ht.ncard, Nat.le_zero, ← ht.ncard] at hnt
    exact ⟨t, hst, Subset.rfl, hnt.symm⟩
  lift s to Finset α using ht.subset hst
  lift t to Finset α using ht
  obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq (mod_cast hst) (by simpa using

Depends on / 依赖: Finset, Finset.exists_subsuperset_card_eq, Nat.le_zero, Subset, Subset.rfl, exists_subsuperset_card_eq, hnt.symm, ht.ncard, ht.subset, infinite_or_finite, le_zero, mod_cast, subset, t.infinite_or_finite
-/
lemma exists_subsuperset_card_eq {n : Nat} (hst : s subseteq t) (hsn : s.ncard <= n) (hnt : n <= t.ncard) :
    exists u, s subseteq u ∧ u subseteq t ∧ u.ncard = n := by
  obtain ht | ht := t.infinite_or_finite
  · rw [ht.ncard, Nat.le_zero, ← ht.ncard] at hnt
    exact ⟨t, hst, Subset.rfl, hnt.symm⟩
  lift s to Finset α using ht.subset hst
  lift t to Finset α using ht
  obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq (mod_cast hst) (by simpa using hsn)
    (mod_cast hnt)
  exact ⟨u, mod_cast hsu, mod_cast hut, mod_cast hu⟩

/--
lemma `exists_subset_card_eq` / 引理 `exists_subset_card_eq`

English:
lemma exists_subset_card_eq
  given: {n : Nat} (hns : n <= s.ncard)
  statement: exists t subseteq s, t.ncard = n
  proof: by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

中文:
引理 exists_subset_card_eq
  条件: {n : 自然数} (hns : n <= s.ncard)
  结论: 存在 t subseteq s, t.ncard = n
  证明: by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

Depends on / 依赖: empty_subset, exists_subsuperset_card_eq, s.empty_subset
-/
lemma exists_subset_card_eq {n : Nat} (hns : n <= s.ncard) : exists t subseteq s, t.ncard = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

/--
theorem `Infinite.exists_subset_ncard_eq` / 定理 `Infinite.exists_subset_ncard_eq`

English:
theorem Infinite.exists_subset_ncard_eq
  given: {s : Set α} (hs : s.Infinite) (k : Nat)
  proof: by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), ?_⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp

中文:
定理 Infinite.exists_subset_ncard_eq
  条件: {s : Set α} (hs : s.Infinite) (k : 自然数)
  证明: by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), ?_⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp

Depends on / 依赖: Finite, Finite.image, Infinite, Infinite.exists_subset_card_eq, Subtype, Subtype.coe_injective, Subtype.val, coe_injective, exists_subset_card_eq, hs.to_subtype, infinite_univ, ncard_image_of_injective, to_subtype
-/
theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : Nat) :
    exists t, t subseteq s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), ?_⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp

/--
theorem `Infinite.exists_superset_ncard_eq` / 定理 `Infinite.exists_superset_ncard_eq`

English:
theorem Infinite.exists_superset_ncard_eq
  statement: {s t : Set α} (ht : t.Infinite) (hst : s subseteq t)
  proof: by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.sdiff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s union s₁, subset_union_left, union_subset hst (hs₁.trans sdiff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le

中文:
定理 Infinite.exists_superset_ncard_eq
  结论: {s t : Set α} (ht : t.Infinite) (hst : s subseteq t)
  证明: by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.sdiff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s union s₁, subset_union_left, union_subset hst (hs₁.trans sdiff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le

Depends on / 依赖: add_tsub_cancel_of_le, disjoint_of_subset_right, disjoint_sdiff_right, exists_subset_ncard_eq, ht.sdiff, ncard_union_eq, s.ncard, sdiff_subset, subset_union_left, union_subset
-/
theorem Infinite.exists_superset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s subseteq t)
    (hs : s.Finite) {k : Nat} (hsk : s.ncard <= k) : exists s', s subseteq s' ∧ s' subseteq t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.sdiff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s union s₁, subset_union_left, union_subset hst (hs₁.trans sdiff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]

/--
theorem `exists_subset_or_subset_of_two_mul_lt_ncard` / 定理 `exists_subset_or_subset_of_two_mul_lt_ncard`

English:
theorem exists_subset_or_subset_of_two_mul_lt_ncard
  given: {n : Nat} (hst : 2 * n < (s union t).ncard)
  proof: by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu]; rw [Finite.toFinset_union (hu.subset subset_union_left)
      (hu.subset subset_union_right)] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt

中文:
定理 exists_subset_or_subset_of_two_mul_lt_ncard
  条件: {n : 自然数} (hst : 2 * n < (s union t).ncard)
  证明: by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu]; rw [Finite.toFinset_union (hu.subset subset_union_left)
      (hu.subset subset_union_right)] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt

Depends on / 依赖: Finite, Finite.toFinset_union, Finset, Finset.exists_subset_or_subset_of_two_mul_lt_card, Nat.zero_le, classical, exists_subset_or_subset_of_two_mul_lt_card, finite_of_ncard_ne_zero, hu.subset, ncard_eq_toFinset_card, ne.symm, subset, subset_union_left, subset_union_right, toFinset_union, trans_lt, zero_le
-/
theorem exists_subset_or_subset_of_two_mul_lt_ncard {n : Nat} (hst : 2 * n < (s union t).ncard) :
    exists r : Set α, n < r.ncard ∧ (r subseteq s ∨ r subseteq t) := by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu]; rw [Finite.toFinset_union (hu.subset subset_union_left)
      (hu.subset subset_union_right)] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
  exact ⟨r', by simpa, by simpa using hr'⟩

/--
lemma `_root_.Finset.exists_not_mem_of_card_lt_enatCard` / 引理 `_root_.Finset.exists_not_mem_of_card_lt_enatCard`

English:
lemma _root_.Finset.exists_not_mem_of_card_lt_enatCard
  given: {s : Finset α} (hs : s.card < ENat.card α)
  proof: by
  contrapose! hs
  simp [← Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall (α := α) (s := s) hs]

中文:
引理 _root_.Finset.exists_not_mem_of_card_lt_enatCard
  条件: {s : Finset α} (hs : s.card < E自然数.card α)
  证明: by
  contrapose! hs
  simp [← Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall (α := α) (s := s) hs]

Depends on / 依赖: Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall, contrapose, encard_coe_eq_coe_finsetCard, eq_univ_of_forall
-/
lemma _root_.Finset.exists_not_mem_of_card_lt_enatCard {s : Finset α} (hs : s.card < ENat.card α) :
    exists a, a ∉ s := by
  contrapose! hs
  simp [← Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall (α := α) (s := s) hs]


/--
theorem `ncard_eq_one` / 定理 `ncard_eq_one`

English:
theorem ncard_eq_one
  statement: s.ncard = 1 ↔ exists a, s = {a}
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine h.imp fun a ha => ?_
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only 

中文:
定理 ncard_eq_one
  结论: s.ncard = 1 ↔ 存在 a, s = {a}
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine h.imp fun a ha => ?_
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only 
-/
@[simp] theorem ncard_eq_one : s.ncard = 1 ↔ exists a, s = {a} := by
  refine ⟨fun h => ?_, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine h.imp fun a ha => ?_
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  exact ha

/--
theorem `exists_eq_insert_iff_ncard` / 定理 `exists_eq_insert_iff_ncard`

English:
theorem exists_eq_insert_iff_ncard
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  classical
  rcases t.finite_or_infinite with ht | ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ← @Finite.toFinset_subset_toFinset _ _ _ hs ht, ← Finset.exists_eq_insert_iff]
    convert! Iff.rfl using 2; simp only [Finite.mem_toFinset]
    ext x
    simp [Finset.ex

中文:
定理 exists_eq_insert_iff_ncard
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  classical
  rcases t.finite_or_infinite with ht | ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ← @Finite.toFinset_subset_toFinset _ _ _ hs ht, ← Finset.exists_eq_insert_iff]
    convert! Iff.rfl using 2; simp only [Finite.mem_toFinset]
    ext x
    simp [Finset.ex

Depends on / 依赖: Finite, Finite.mem_toFinset, Finite.toFinset_subset_toFinset, Finset, Finset.exists_eq_insert_iff, Finset.ext_iff, Iff.rfl, Set.ext_iff, add_eq_zero, and_false, classical, convert, exists_eq_insert_iff, ext_iff, finite_or_infinite, ht.ncard, iff_false, insert, mem_toFinset, ncard_eq_toFinset_card
-/
theorem exists_eq_insert_iff_ncard (hs : s.Finite := by toFinite_tac) :
    (exists a ∉ s, insert a s = t) ↔ s subseteq t ∧ s.ncard + 1 = t.ncard := by
  classical
  rcases t.finite_or_infinite with ht | ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ← @Finite.toFinset_subset_toFinset _ _ _ hs ht, ← Finset.exists_eq_insert_iff]
    convert! Iff.rfl using 2; simp only [Finite.mem_toFinset]
    ext x
    simp [Finset.ext_iff, Set.ext_iff]
  simp only [ht.ncard, add_eq_zero, and_false, iff_false, not_exists, not_and,
    reduceCtorEq]
  rintro x - rfl
  exact ht (hs.insert x)

/--
theorem `ncard_le_one` / 定理 `ncard_le_one`

English:
theorem ncard_le_one
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]

中文:
定理 ncard_le_one
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.card_le_one, card_le_one, mem_toFinset, ncard_eq_toFinset_card, s.ncard, simp_rw, toFinite_tac
-/
theorem ncard_le_one (hs : s.Finite := by toFinite_tac) :
    s.ncard <= 1 ↔ forall a in s, forall b in s, a = b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]

/--
theorem `ncard_le_one_iff_subsingleton` / 定理 `ncard_le_one_iff_subsingleton`

English:
theorem ncard_le_one_iff_subsingleton
  given: [Finite s]
  proof: ncard_le_one inferInstanceAs (Finite s)

中文:
定理 ncard_le_one_iff_subsingleton
  条件: [Finite s]
  证明: ncard_le_one inferInstanceAs (Finite s)
-/
@[simp] theorem ncard_le_one_iff_subsingleton [Finite s] :
    s.ncard <= 1 ↔ s.Subsingleton :=
ncard_le_one inferInstanceAs (Finite s)

/--
theorem `ncard_le_one_iff` / 定理 `ncard_le_one_iff`

English:
theorem ncard_le_one_iff
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [ncard_le_one hs]
  tauto

中文:
定理 ncard_le_one_iff
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [ncard_le_one hs]
  tauto

Depends on / 依赖: ncard_le_one, s.ncard, toFinite_tac
-/
theorem ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard <= 1 ↔ forall {a b}, a in s -> b in s -> a = b := by
  rw [ncard_le_one hs]
  tauto

/--
theorem `ncard_le_one_iff_eq` / 定理 `ncard_le_one_iff_eq`

English:
theorem ncard_le_one_iff_eq
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine ⟨fun h => Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy => h hy hx⟩, ?_⟩
  grind

中文:
定理 ncard_le_one_iff_eq
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine ⟨fun h => Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy => h hy hx⟩, ?_⟩
  grind

Depends on / 依赖: Or.inl, Or.inr, antisymm, eq_empty_or_nonempty, iff_of_true, ncard_le_one_iff, s.eq_empty_or_nonempty, s.ncard, singleton_subset_iff, singleton_subset_iff.mpr, toFinite_tac
-/
theorem ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard <= 1 ↔ s = ∅ ∨ exists a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine ⟨fun h => Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy => h hy hx⟩, ?_⟩
  grind

/--
theorem `ncard_le_one_iff_subset_singleton` / 定理 `ncard_le_one_iff_subset_singleton`

English:
theorem ncard_le_one_iff_subset_singleton
  statement: [Nonempty α]
  proof: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

中文:
定理 ncard_le_one_iff_subset_singleton
  结论: [Nonempty α]
  证明: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

Depends on / 依赖: Finite, Finite.toFinset_subset, Finset, Finset.card_le_one_iff_subset_singleton, Finset.coe_singleton, card_le_one_iff_subset_singleton, coe_singleton, ncard_eq_toFinset_card, s.ncard, simp_rw, subseteq, toFinite_tac, toFinset_subset
-/
theorem ncard_le_one_iff_subset_singleton [Nonempty α]
    (hs : s.Finite := by toFinite_tac) :
    s.ncard <= 1 ↔ exists x : α, s subseteq {x} := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

/--
theorem `ncard_le_one_of_subsingleton` / 定理 `ncard_le_one_of_subsingleton`

English:
theorem ncard_le_one_of_subsingleton
  given: [Subsingleton α] (s : Set α)
  statement: s.ncard <= 1
  proof: by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _

中文:
定理 ncard_le_one_of_subsingleton
  条件: [Subsingleton α] (s : Set α)
  结论: s.ncard <= 1
  证明: by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _

Depends on / 依赖: Finset, Finset.card_le_one_of_subsingleton, card_le_one_of_subsingleton, ncard_eq_toFinset_card
-/
theorem ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard <= 1 := by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _

/--
theorem `one_lt_ncard_iff_nontrivial` / 定理 `one_lt_ncard_iff_nontrivial`

English:
theorem one_lt_ncard_iff_nontrivial
  given: [Finite s]
  proof: by
  rw [← not_subsingleton_iff]; rw [← ncard_le_one_iff_subsingleton]; rw [not_le]

中文:
定理 one_lt_ncard_iff_nontrivial
  条件: [Finite s]
  证明: by
  rw [← not_subsingleton_iff]; rw [← ncard_le_one_iff_subsingleton]; rw [not_le]

Depends on / 依赖: ncard_le_one_iff_subsingleton, not_le, not_subsingleton_iff
-/
theorem one_lt_ncard_iff_nontrivial [Finite s] :
    1 < s.ncard ↔ s.Nontrivial := by
  rw [← not_subsingleton_iff]; rw [← ncard_le_one_iff_subsingleton]; rw [not_le]

/--
theorem `one_lt_ncard_iff_nontrivial_and_finite` / 定理 `one_lt_ncard_iff_nontrivial_and_finite`

English:
theorem one_lt_ncard_iff_nontrivial_and_finite
  proof: by
  refine ⟨fun hs => ?_, fun ⟨hs_nontrivial, hs_finite⟩ => ?_⟩
  · have := finite_of_ncard_pos (Nat.zero_lt_of_lt hs)
    rw [← Set.finite_coe_iff] at this
    exact ⟨one_lt_ncard_iff_nontrivial.mp hs, this⟩
  · rw [← Set.finite_coe_iff] at hs_finite
    rwa [one_lt_ncard_iff_nontrivial]

中文:
定理 one_lt_ncard_iff_nontrivial_and_finite
  证明: by
  refine ⟨fun hs => ?_, fun ⟨hs_nontrivial, hs_finite⟩ => ?_⟩
  · have := finite_of_ncard_pos (Nat.zero_lt_of_lt hs)
    rw [← Set.finite_coe_iff] at this
    exact ⟨one_lt_ncard_iff_nontrivial.mp hs, this⟩
  · rw [← Set.finite_coe_iff] at hs_finite
    rwa [one_lt_ncard_iff_nontrivial]

Depends on / 依赖: Nat.zero_lt_of_lt, Set.finite_coe_iff, finite_coe_iff, finite_of_ncard_pos, hs_finite, hs_nontrivial, one_lt_ncard_iff_nontrivial, one_lt_ncard_iff_nontrivial.mp, zero_lt_of_lt
-/
theorem one_lt_ncard_iff_nontrivial_and_finite :
    1 < s.ncard ↔ s.Nontrivial ∧ s.Finite := by
  refine ⟨fun hs => ?_, fun ⟨hs_nontrivial, hs_finite⟩ => ?_⟩
  · have := finite_of_ncard_pos (Nat.zero_lt_of_lt hs)
    rw [← Set.finite_coe_iff] at this
    exact ⟨one_lt_ncard_iff_nontrivial.mp hs, this⟩
  · rw [← Set.finite_coe_iff] at hs_finite
    rwa [one_lt_ncard_iff_nontrivial]

/--
theorem `one_lt_ncard` / 定理 `one_lt_ncard`

English:
theorem one_lt_ncard
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]

中文:
定理 one_lt_ncard
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.one_lt_card, mem_toFinset, ncard_eq_toFinset_card, one_lt_card, s.ncard, simp_rw, toFinite_tac
-/
theorem one_lt_ncard (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ exists a in s, exists b in s, a != b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]

/--
theorem `one_lt_ncard_iff` / 定理 `one_lt_ncard_iff`

English:
theorem one_lt_ncard_iff
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  rw [one_lt_ncard hs]
  simp only [exists_and_left]

中文:
定理 one_lt_ncard_iff
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  rw [one_lt_ncard hs]
  simp only [exists_and_left]

Depends on / 依赖: exists_and_left, one_lt_ncard, s.ncard, toFinite_tac
-/
theorem one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ exists a b, a in s ∧ b in s ∧ a != b := by
  rw [one_lt_ncard hs]
  simp only [exists_and_left]

/--
lemma `one_lt_ncard_of_nonempty_of_even` / 引理 `one_lt_ncard_of_nonempty_of_even`

English:
lemma one_lt_ncard_of_nonempty_of_even
  statement: (hs : Set.Finite s) (hn : Set.Nonempty s := by toFinite_tac)
  proof: by
  rw [← Set.ncard_pos hs] at hn
  have : s.ncard != 1 := fun h => by simp [h] at he
  lia

中文:
引理 one_lt_ncard_of_nonempty_of_even
  结论: (hs : Set.Finite s) (hn : Set.Nonempty s := by toFinite_tac)
  证明: by
  rw [← Set.ncard_pos hs] at hn
  have : s.ncard != 1 := fun h => by simp [h] at he
  lia

Depends on / 依赖: Set.ncard_pos, ncard_pos, s.ncard, toFinite_tac
-/
lemma one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s := by toFinite_tac)
    (he : Even (s.ncard)) : 1 < s.ncard := by
  rw [← Set.ncard_pos hs] at hn
  have : s.ncard != 1 := fun h => by simp [h] at he
  lia

/--
theorem `two_lt_ncard_iff` / 定理 `two_lt_ncard_iff`

English:
theorem two_lt_ncard_iff
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]

中文:
定理 two_lt_ncard_iff
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.two_lt_card_iff, mem_toFinset, ncard_eq_toFinset_card, s.ncard, simp_rw, toFinite_tac, two_lt_card_iff
-/
theorem two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ exists a b c, a in s ∧ b in s ∧ c in s ∧ a != b ∧ a != c ∧ b != c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]

/--
theorem `two_lt_ncard` / 定理 `two_lt_ncard`

English:
theorem two_lt_ncard
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp only [two_lt_ncard_iff hs, exists_and_left]

中文:
定理 two_lt_ncard
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp only [two_lt_ncard_iff hs, exists_and_left]

Depends on / 依赖: exists_and_left, s.ncard, toFinite_tac, two_lt_ncard_iff
-/
theorem two_lt_ncard (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ exists a in s, exists b in s, exists c in s, a != b ∧ a != c ∧ b != c := by
  simp only [two_lt_ncard_iff hs, exists_and_left]

/--
theorem `three_lt_ncard_iff` / 定理 `three_lt_ncard_iff`

English:
theorem three_lt_ncard_iff
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.three_lt_card_iff, Finite.mem_toFinset]

中文:
定理 three_lt_ncard_iff
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.three_lt_card_iff, Finite.mem_toFinset]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.three_lt_card_iff, mem_toFinset, ncard_eq_toFinset_card, s.ncard, simp_rw, three_lt_card_iff, toFinite_tac
-/
theorem three_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    exists a b c d, a in s ∧ b in s ∧ c in s ∧ d in s ∧ a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.three_lt_card_iff, Finite.mem_toFinset]

/--
theorem `three_lt_ncard` / 定理 `three_lt_ncard`

English:
theorem three_lt_ncard
  given: (hs : s.Finite := by toFinite_tac)
  proof: by
  simp only [three_lt_ncard_iff hs, exists_and_left]

中文:
定理 three_lt_ncard
  条件: (hs : s.Finite := by toFinite_tac)
  证明: by
  simp only [three_lt_ncard_iff hs, exists_and_left]

Depends on / 依赖: exists_and_left, s.ncard, three_lt_ncard_iff, toFinite_tac
-/
theorem three_lt_ncard (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    exists a in s, exists b in s, exists c in s, exists d in s, a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d := by
  simp only [three_lt_ncard_iff hs, exists_and_left]

/--
theorem `exists_ne_of_one_lt_ncard` / 定理 `exists_ne_of_one_lt_ncard`

English:
theorem exists_ne_of_one_lt_ncard
  given: (hs : 1 < s.ncard) (a : α)
  statement: exists b, b in s ∧ b != a
  proof: by
  have hsf := finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_mem_ne hs a

中文:
定理 exists_ne_of_one_lt_ncard
  条件: (hs : 1 < s.ncard) (a : α)
  结论: 存在 b, b in s ∧ b != a
  证明: by
  have hsf := finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_mem_ne hs a

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.exists_mem_ne, exists_mem_ne, finite_of_ncard_ne_zero, mem_toFinset, ncard_eq_toFinset_card, ne.symm, zero_lt_one, zero_lt_one.trans
-/
theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : exists b, b in s ∧ b != a := by
  have hsf := finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_mem_ne hs a

/--
theorem `eq_insert_of_ncard_eq_succ` / 定理 `eq_insert_of_ncard_eq_succ`

English:
theorem eq_insert_of_ncard_eq_succ
  given: {n : Nat} (h : s.ncard = n + 1)
  proof: by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf]; rw [Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine ⟨a, t, hat, ?_, ?_⟩
  · simp [

中文:
定理 eq_insert_of_ncard_eq_succ
  条件: {n : 自然数} (h : s.ncard = n + 1)
  证明: by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf]; rw [Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine ⟨a, t, hat, ?_, ?_⟩
  · simp [

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.card_eq_succ, Finset.ext_iff, Finset.mem_insert, Set.ext_iff, card_eq_succ, classical, ext_iff, finite_of_ncard_pos, h.symm, mem_insert, mem_toFinset, n.zero_lt_succ.trans_eq, ncard_eq_toFinset_card, trans_eq, zero_lt_succ
-/
theorem eq_insert_of_ncard_eq_succ {n : Nat} (h : s.ncard = n + 1) :
    exists a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf]; rw [Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine ⟨a, t, hat, ?_, ?_⟩
  · simp [Set.ext_iff, hts]
  · simp

/--
theorem `ncard_eq_succ` / 定理 `ncard_eq_succ`

English:
theorem ncard_eq_succ
  given: {n : Nat} (hs : s.Finite := by toFinite_tac)
  proof: by
  refine ⟨eq_insert_of_ncard_eq_succ, ?_⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h]; rw [ncard_insert_of_notMem hat (hs.subset ((subset_insert a t).trans_eq h))]

中文:
定理 ncard_eq_succ
  条件: {n : 自然数} (hs : s.Finite := by toFinite_tac)
  证明: by
  refine ⟨eq_insert_of_ncard_eq_succ, ?_⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h]; rw [ncard_insert_of_notMem hat (hs.subset ((subset_insert a t).trans_eq h))]

Depends on / 依赖: eq_insert_of_ncard_eq_succ, hs.subset, insert, ncard_insert_of_notMem, s.ncard, subset, subset_insert, t.ncard, toFinite_tac, trans_eq
-/
theorem ncard_eq_succ {n : Nat} (hs : s.Finite := by toFinite_tac) :
    s.ncard = n + 1 ↔ exists a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  refine ⟨eq_insert_of_ncard_eq_succ, ?_⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h]; rw [ncard_insert_of_notMem hat (hs.subset ((subset_insert a t).trans_eq h))]

/--
theorem `ncard_eq_two` / 定理 `ncard_eq_two`

English:
theorem ncard_eq_two
  statement: s.ncard = 2 ↔ exists x y, x != y ∧ s = {x, y}
  proof: by
  rw [← encard_eq_two]; rw [ncard_def]
  simp

中文:
定理 ncard_eq_two
  结论: s.ncard = 2 ↔ 存在 x y, x != y ∧ s = {x, y}
  证明: by
  rw [← encard_eq_two]; rw [ncard_def]
  simp

Depends on / 依赖: encard_eq_two, ncard_def
-/
theorem ncard_eq_two : s.ncard = 2 ↔ exists x y, x != y ∧ s = {x, y} := by
  rw [← encard_eq_two]; rw [ncard_def]
  simp

/--
theorem `ncard_eq_three` / 定理 `ncard_eq_three`

English:
theorem ncard_eq_three
  statement: s.ncard = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
  proof: by
  rw [← encard_eq_three]; rw [ncard_def]
  simp

中文:
定理 ncard_eq_three
  结论: s.ncard = 3 ↔ 存在 x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
  证明: by
  rw [← encard_eq_three]; rw [ncard_def]
  simp

Depends on / 依赖: encard_eq_three, ncard_def
-/
theorem ncard_eq_three : s.ncard = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z} := by
  rw [← encard_eq_three]; rw [ncard_def]
  simp

/--
theorem `ncard_eq_four` / 定理 `ncard_eq_four`

English:
theorem ncard_eq_four
  statement: s.ncard = 4 ↔
  proof: by
  rw [← encard_eq_four]; rw [ncard_def]
  simp

中文:
定理 ncard_eq_four
  结论: s.ncard = 4 ↔
  证明: by
  rw [← encard_eq_four]; rw [ncard_def]
  simp

Depends on / 依赖: encard_eq_four, ncard_def
-/
theorem ncard_eq_four : s.ncard = 4 ↔
    exists x y z w, x != y ∧ x != z ∧ x != w ∧ y != z ∧ y != w ∧ z != w ∧ s = {x, y, z, w} := by
  rw [← encard_eq_four]; rw [ncard_def]
  simp

/--
theorem `ncard_sumEquiv_symm_apply` / 定理 `ncard_sumEquiv_symm_apply`

English:
theorem ncard_sumEquiv_symm_apply
  given: {α : Type*} (s : Set α)
  proof: by
  by_cases hs : s.Finite
  · simp [(ncard_union_eq_iff (.image _ hs) (.image _ hs)).2 disjoint_image_inl_image_inr,
      ncard_image_of_injective _ Sum.inl_injective, ncard_image_of_injective _ Sum.inr_injective]
  · simp [(infinite_union.2 <| .inl <| .image Sum.inl_injective.injOn hs).ncard, In

中文:
定理 ncard_sumEquiv_symm_apply
  条件: {α : 类型} (s : Set α)
  证明: by
  by_cases hs : s.Finite
  · simp [(ncard_union_eq_iff (.image _ hs) (.image _ hs)).2 disjoint_image_inl_image_inr,
      ncard_image_of_injective _ Sum.inl_injective, ncard_image_of_injective _ Sum.inr_injective]
  · simp [(infinite_union.2 <| .inl <| .image Sum.inl_injective.injOn hs).ncard, In

Depends on / 依赖: Finite, Infinite, Infinite.ncard, Sum.inl_injective, Sum.inl_injective.injOn, Sum.inr_injective, disjoint_image_inl_image_inr, infinite_union, inl_injective, inr_injective, ncard_image_of_injective, ncard_union_eq_iff, s.Finite
-/
theorem ncard_sumEquiv_symm_apply {α : Type*} (s : Set α) :
    (Set.sumEquiv.symm (s, s)).ncard = s.ncard + s.ncard := by
  by_cases hs : s.Finite
  · simp [(ncard_union_eq_iff (.image _ hs) (.image _ hs)).2 disjoint_image_inl_image_inr,
      ncard_image_of_injective _ Sum.inl_injective, ncard_image_of_injective _ Sum.inr_injective]
  · simp [(infinite_union.2 <| .inl <| .image Sum.inl_injective.injOn hs).ncard, Infinite.ncard hs]

end ncard
end Set

/--
theorem `Function.Surjective.card_le_card_add_one_iff` / 定理 `Function.Surjective.card_le_card_add_one_iff`

English:
theorem Function.Surjective.card_le_card_add_one_iff
  proof: by
  rcases isEmpty_or_nonempty α
  · simp
  -- pick an inverse `g` to `f`
  let g := Function.surjInv hf
  -- the "decreases cardinality by at most one condition" becomes "`g` misses at most one element"
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf)]; rw [← Set.ncard_add_ncar

中文:
定理 Function.Surjective.card_le_card_add_one_iff
  证明: by
  rcases isEmpty_or_nonempty α
  · simp
  -- pick an inverse `g` to `f`
  let g := Function.surjInv hf
  -- the "decreases cardinality by at most one condition" becomes "`g` misses at most one element"
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf)]; rw [← Set.ncard_add_ncar

Depends on / 依赖: isEmpty_or_nonempty
-/
theorem Function.Surjective.card_le_card_add_one_iff
    {α β : Type*} [Finite α] {f : α -> β} (hf : Function.Surjective f) :
    Nat.card α <= Nat.card β + 1 ↔ forall a b c d,
      f a = f b -> f c = f d -> a != b -> c != d -> {a, b} = ({c, d} : Set α) := by
  rcases isEmpty_or_nonempty α
  · simp
  -- pick an inverse `g` to `f`
  let g := Function.surjInv hf
  -- the "decreases cardinality by at most one condition" becomes "`g` misses at most one element"
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf)]; rw [← Set.ncard_add_ncard_compl (Set.range g)]; rw [add_le_add_iff_left]
  replace hf : forall b, f (g b) = b := Function.surjInv_eq hf
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Set.ncard_le_one_iff_subset_singleton] at h
    -- if `g` misses at most one element, let `x` be this element
    obtain ⟨x, hx⟩ := h
    simp only [Set.subset_def, Set.mem_compl_iff] at hx
    -- we show that the only possible collision is between `x` and `g (f x)`
    suffices forall a b : α, f a = f b -> a != b -> a = x ∨ a = g (f x) by grind
    intro a b
    by_cases ha : a in Set.range g <;> by_cases hb : b in Set.range g <;> grind
  · -- we must show that any two elements `a` and `b` missed by `g` are equal
    rw [Set.ncard_le_one]
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, ← ne_eq]
    intro a ha b hb
    -- there is a collision between `a` and `g (f a)`, and between `b` and `g (f b)`
    simpa [(ha (f b)).symm] using congrArg (a in ·) (h a (g (f a)) b (g (f b))
      (hf (f a)).symm (hf (f b)).symm (ha (f a)).symm (hb (f b)).symm)

/--
theorem `Set.ncard_le_ncard_image_add_one_iff` / 定理 `Set.ncard_le_ncard_image_add_one_iff`

English:
theorem Set.ncard_le_ncard_image_add_one_iff
  given: {α β : Type*} (s : Set α) [Finite s] (f : α -> β)
  proof: by
  simpa [Subtype.ext_iff, ← (Set.image_injective.mpr Subtype.val_injective).eq_iff,
     Set.image_insert_eq, Set.image_singleton] using
      (Set.surjective_mapsTo_image_restrict f s).card_le_card_add_one_iff

中文:
定理 Set.ncard_le_ncard_image_add_one_iff
  条件: {α β : 类型} (s : Set α) [Finite s] (f : α -> β)
  证明: by
  simpa [Subtype.ext_iff, ← (Set.image_injective.mpr Subtype.val_injective).eq_iff,
     Set.image_insert_eq, Set.image_singleton] using
      (Set.surjective_mapsTo_image_restrict f s).card_le_card_add_one_iff

Depends on / 依赖: Set.image_injective.mpr, Set.image_insert_eq, Set.image_singleton, Set.surjective_mapsTo_image_restrict, Subtype, Subtype.ext_iff, Subtype.val_injective, card_le_card_add_one_iff, eq_iff, ext_iff, image_injective, image_insert_eq, image_singleton, surjective_mapsTo_image_restrict, val_injective
-/
theorem Set.ncard_le_ncard_image_add_one_iff {α β : Type*} (s : Set α) [Finite s] (f : α -> β) :
    s.ncard <= (f '' s).ncard + 1 ↔ forall a in s, forall b in s, forall c in s, forall d in s,
      f a = f b -> f c = f d -> a != b -> c != d -> {a, b} = ({c, d} : Set α) := by
  simpa [Subtype.ext_iff, ← (Set.image_injective.mpr Subtype.val_injective).eq_iff,
     Set.image_insert_eq, Set.image_singleton] using
      (Set.surjective_mapsTo_image_restrict f s).card_le_card_add_one_iff
