/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `#s : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
* `Finset.eraseInduction`
-/

@[expose] public section

assert_not_exists Monoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b c : α}

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (s : Finset α)
  body: Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

中文:
定义 card
  签名: (s : 有限集 α)
  定义体: Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

Depends on / 依赖: Multiset, Multiset.card
-/
def card (s : Finset α) : Nat :=
  Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

/--
theorem `card_def` / 定理 `card_def`

English:
theorem card_def
  given: (s : Finset α)
  statement: #s = Multiset.card s.1
  proof: rfl

中文:
定理 card_def
  条件: (s : 有限集 α)
  结论: #s = Multiset.card s.1
  证明: rfl
-/
theorem card_def (s : Finset α) : #s = Multiset.card s.1 :=
  rfl

/--
lemma `card_val` / 引理 `card_val`

English:
lemma card_val
  given: (s : Finset α)
  statement: Multiset.card s.1 = #s
  proof: rfl

@[simp]

中文:
引理 card_val
  条件: (s : 有限集 α)
  结论: Multiset.card s.1 = #s
  证明: rfl

@[simp]
-/
@[simp] lemma card_val (s : Finset α) : Multiset.card s.1 = #s := rfl

@[simp]
/--
theorem `card_mk` / 定理 `card_mk`

English:
theorem card_mk
  given: {m nodup}
  statement: #(⟨m, nodup⟩ : Finset α) = Multiset.card m
  proof: rfl

@[simp, grind =]

中文:
定理 card_mk
  条件: {m nodup}
  结论: #(⟨m, nodup⟩ : 有限集 α) = Multiset.card m
  证明: rfl

@[simp, grind =]
-/
theorem card_mk {m nodup} : #(⟨m, nodup⟩ : Finset α) = Multiset.card m :=
  rfl

@[simp, grind =]
/--
theorem `card_empty` / 定理 `card_empty`

English:
theorem card_empty
  statement: #(∅ : Finset α) = 0
  proof: rfl

@[gcongr]

中文:
定理 card_empty
  结论: #(∅ : 有限集 α) = 0
  证明: rfl

@[gcongr]
-/
theorem card_empty : #(∅ : Finset α) = 0 :=
  rfl

@[gcongr]
/--
theorem `card_le_card` / 定理 `card_le_card`

English:
theorem card_le_card
  statement: s subseteq t -> #s <= #t
  proof: Multiset.card_le_card ∘ val_le_iff.mpr

中文:
定理 card_le_card
  结论: s subseteq t -> #s <= #t
  证明: Multiset.card_le_card ∘ val_le_iff.mpr

Depends on / 依赖: Multiset, Multiset.card_le_card, card_le_card, val_le_iff, val_le_iff.mpr
-/
theorem card_le_card : s subseteq t -> #s <= #t :=
  Multiset.card_le_card ∘ val_le_iff.mpr

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we turn it on again later in this file.)
local grind_pattern card_le_card => #s, #t

@[mono]
/--
theorem `card_mono` / 定理 `card_mono`

English:
theorem card_mono
  statement: Monotone (@card α)
  proof: by apply card_le_card

中文:
定理 card_mono
  结论: 递增 (@card α)
  证明: by apply card_le_card

Depends on / 依赖: card_le_card
-/
theorem card_mono : Monotone (@card α) := by apply card_le_card

/--
lemma `card_eq_zero` / 引理 `card_eq_zero`

English:
lemma card_eq_zero
  statement: #s = 0 ↔ s = ∅
  proof: Multiset.card_eq_zero.trans val_eq_zero

中文:
引理 card_eq_zero
  结论: #s = 0 ↔ s = ∅
  证明: Multiset.card_eq_zero.trans val_eq_zero
-/
@[simp] lemma card_eq_zero : #s = 0 ↔ s = ∅ := Multiset.card_eq_zero.trans val_eq_zero
/--
lemma `card_ne_zero` / 引理 `card_ne_zero`

English:
lemma card_ne_zero
  statement: #s != 0 ↔ s.Nonempty
  proof: card_eq_zero.ne.trans nonempty_iff_ne_empty.symm

中文:
引理 card_ne_zero
  结论: #s != 0 ↔ s.非空
  证明: card_eq_zero.ne.trans nonempty_iff_ne_empty.symm

Depends on / 依赖: card_eq_zero, card_eq_zero.ne.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
lemma card_ne_zero : #s != 0 ↔ s.Nonempty := card_eq_zero.ne.trans nonempty_iff_ne_empty.symm
/--
lemma `card_pos` / 引理 `card_pos`

English:
lemma card_pos
  statement: 0 < #s ↔ s.Nonempty
  proof: Nat.pos_iff_ne_zero.trans card_ne_zero

中文:
引理 card_pos
  结论: 0 < #s ↔ s.非空
  证明: Nat.pos_iff_ne_zero.trans card_ne_zero
-/
@[simp] lemma card_pos : 0 < #s ↔ s.Nonempty := Nat.pos_iff_ne_zero.trans card_ne_zero
/--
lemma `one_le_card` / 引理 `one_le_card`

English:
lemma one_le_card
  statement: 1 <= #s ↔ s.Nonempty
  proof: card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero

中文:
引理 one_le_card
  结论: 1 <= #s ↔ s.非空
  证明: card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero
-/
@[simp] lemma one_le_card : 1 <= #s ↔ s.Nonempty := card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero

/--
theorem `card_ne_zero_of_mem` / 定理 `card_ne_zero_of_mem`

English:
theorem card_ne_zero_of_mem
  given: (h : a in s)
  statement: #s != 0
  proof: (not_congr card_eq_zero).2 ne_empty_of_mem h

grind_pattern card_ne_zero_of_mem => a in s, #s

@[simp, grind =]

中文:
定理 card_ne_zero_of_mem
  条件: (h : a in s)
  结论: #s != 0
  证明: (not_congr card_eq_zero).2 ne_empty_of_mem h

grind_pattern card_ne_zero_of_mem => a in s, #s

@[simp, grind =]

Depends on / 依赖: card_eq_zero, ne_empty_of_mem, not_congr
-/
theorem card_ne_zero_of_mem (h : a in s) : #s != 0 :=
(not_congr card_eq_zero).2 ne_empty_of_mem h

grind_pattern card_ne_zero_of_mem => a in s, #s

@[simp, grind =]
/--
theorem `card_singleton` / 定理 `card_singleton`

English:
theorem card_singleton
  given: (a : α)
  statement: #{a} = 1
  proof: Multiset.card_singleton _

中文:
定理 card_singleton
  条件: (a : α)
  结论: #{a} = 1
  证明: Multiset.card_singleton _

Depends on / 依赖: Multiset, Multiset.card_singleton, card_singleton
-/
theorem card_singleton (a : α) : #{a} = 1 :=
  Multiset.card_singleton _

/--
theorem `card_singleton_inter` / 定理 `card_singleton_inter`

English:
theorem card_singleton_inter
  given: [DecidableEq α]
  statement: #({a} inter s) <= 1
  proof: by grind

@[simp, grind =]

中文:
定理 card_singleton_inter
  条件: [DecidableEq α]
  结论: #({a} inter s) <= 1
  证明: by grind

@[simp, grind =]
-/
theorem card_singleton_inter [DecidableEq α] : #({a} inter s) <= 1 := by grind

@[simp, grind =]
/--
theorem `card_cons` / 定理 `card_cons`

English:
theorem card_cons
  given: (h : a ∉ s)
  statement: #(s.cons a h) = #s + 1
  proof: Multiset.card_cons _ _

中文:
定理 card_cons
  条件: (h : a ∉ s)
  结论: #(s.cons a h) = #s + 1
  证明: Multiset.card_cons _ _

Depends on / 依赖: Multiset, Multiset.card_cons, card_cons
-/
theorem card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1 :=
  Multiset.card_cons _ _

section InsertErase

variable [DecidableEq α]

@[simp, grind =]
/--
theorem `card_insert_of_notMem` / 定理 `card_insert_of_notMem`

English:
theorem card_insert_of_notMem
  given: (h : a ∉ s)
  statement: #(insert a s) = #s + 1
  proof: by
  grind [=_ cons_eq_insert]

中文:
定理 card_insert_of_notMem
  条件: (h : a ∉ s)
  结论: #(insert a s) = #s + 1
  证明: by
  grind [=_ cons_eq_insert]

Depends on / 依赖: cons_eq_insert
-/
theorem card_insert_of_notMem (h : a ∉ s) : #(insert a s) = #s + 1 := by
  grind [=_ cons_eq_insert]

/--
theorem `card_insert_of_mem` / 定理 `card_insert_of_mem`

English:
theorem card_insert_of_mem
  given: (h : a in s)
  statement: #(insert a s) = #s
  proof: by rw [insert_eq_of_mem h]

中文:
定理 card_insert_of_mem
  条件: (h : a in s)
  结论: #(insert a s) = #s
  证明: by rw [insert_eq_of_mem h]

Depends on / 依赖: insert_eq_of_mem
-/
theorem card_insert_of_mem (h : a in s) : #(insert a s) = #s := by rw [insert_eq_of_mem h]

/--
theorem `card_insert_le` / 定理 `card_insert_le`

English:
theorem card_insert_le
  given: (a : α) (s : Finset α)
  statement: #(insert a s) <= #s + 1
  proof: by grind

中文:
定理 card_insert_le
  条件: (a : α) (s : 有限集 α)
  结论: #(insert a s) <= #s + 1
  证明: by grind
-/
theorem card_insert_le (a : α) (s : Finset α) : #(insert a s) <= #s + 1 := by grind

section

variable {a b c d e f : α}

/--
theorem `card_le_two` / 定理 `card_le_two`

English:
theorem card_le_two
  statement: #{a, b} <= 2
  proof: card_insert_le _ _

中文:
定理 card_le_two
  结论: #{a, b} <= 2
  证明: card_insert_le _ _

Depends on / 依赖: card_insert_le
-/
theorem card_le_two : #{a, b} <= 2 := card_insert_le _ _

/--
theorem `card_le_three` / 定理 `card_le_three`

English:
theorem card_le_three
  statement: #{a, b, c} <= 3
  proof: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

中文:
定理 card_le_three
  结论: #{a, b, c} <= 3
  证明: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

Depends on / 依赖: Nat.succ_le_succ, card_insert_le, card_le_two, succ_le_succ
-/
theorem card_le_three : #{a, b, c} <= 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

/--
theorem `card_le_four` / 定理 `card_le_four`

English:
theorem card_le_four
  statement: #{a, b, c, d} <= 4
  proof: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)

中文:
定理 card_le_four
  结论: #{a, b, c, d} <= 4
  证明: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)

Depends on / 依赖: Nat.succ_le_succ, card_insert_le, card_le_three, succ_le_succ
-/
theorem card_le_four : #{a, b, c, d} <= 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)

/--
theorem `card_le_five` / 定理 `card_le_five`

English:
theorem card_le_five
  statement: #{a, b, c, d, e} <= 5
  proof: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)

中文:
定理 card_le_five
  结论: #{a, b, c, d, e} <= 5
  证明: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)

Depends on / 依赖: Nat.succ_le_succ, card_insert_le, card_le_four, succ_le_succ
-/
theorem card_le_five : #{a, b, c, d, e} <= 5 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)

/--
theorem `card_le_six` / 定理 `card_le_six`

English:
theorem card_le_six
  statement: #{a, b, c, d, e, f} <= 6
  proof: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

中文:
定理 card_le_six
  结论: #{a, b, c, d, e, f} <= 6
  证明: (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

Depends on / 依赖: Nat.succ_le_succ, card_insert_le, card_le_five, succ_le_succ
-/
theorem card_le_six : #{a, b, c, d, e, f} <= 6 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

end

/--
theorem `card_insert_eq_ite` / 定理 `card_insert_eq_ite`

English:
theorem card_insert_eq_ite
  statement: #(insert a s) = if a in s then #s else #s + 1
  proof: by grind

@[simp]

中文:
定理 card_insert_eq_ite
  结论: #(insert a s) = if a in s then #s else #s + 1
  证明: by grind

@[simp]
-/
theorem card_insert_eq_ite : #(insert a s) = if a in s then #s else #s + 1 := by grind

@[simp]
/--
theorem `card_pair_eq_one_or_two` / 定理 `card_pair_eq_one_or_two`

English:
theorem card_pair_eq_one_or_two
  statement: #{a, b} = 1 ∨ #{a, b} = 2
  proof: by grind

中文:
定理 card_pair_eq_one_or_two
  结论: #{a, b} = 1 ∨ #{a, b} = 2
  证明: by grind
-/
theorem card_pair_eq_one_or_two : #{a, b} = 1 ∨ #{a, b} = 2 := by grind

/--
theorem `card_pair_eq_two_iff` / 定理 `card_pair_eq_two_iff`

English:
theorem card_pair_eq_two_iff
  statement: #{a, b} = 2 ↔ a != b
  proof: by
  aesop (add simp card_insert_eq_ite)

alias ⟨_, card_pair⟩ := card_pair_eq_two_iff

中文:
定理 card_pair_eq_two_iff
  结论: #{a, b} = 2 ↔ a != b
  证明: by
  aesop (add simp card_insert_eq_ite)

alias ⟨_, card_pair⟩ := card_pair_eq_two_iff

Depends on / 依赖: card_insert_eq_ite
-/
theorem card_pair_eq_two_iff : #{a, b} = 2 ↔ a != b := by
  aesop (add simp card_insert_eq_ite)

alias ⟨_, card_pair⟩ := card_pair_eq_two_iff

/--
theorem `card_triple_eq_three_iff` / 定理 `card_triple_eq_three_iff`

English:
theorem card_triple_eq_three_iff
  statement: #{a, b, c} = 3 ↔ a != b ∧ a != c ∧ b != c
  proof: by
  aesop (add simp card_insert_eq_ite)

中文:
定理 card_triple_eq_three_iff
  结论: #{a, b, c} = 3 ↔ a != b ∧ a != c ∧ b != c
  证明: by
  aesop (add simp card_insert_eq_ite)

Depends on / 依赖: card_insert_eq_ite
-/
theorem card_triple_eq_three_iff : #{a, b, c} = 3 ↔ a != b ∧ a != c ∧ b != c := by
  aesop (add simp card_insert_eq_ite)

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp, grind =]
/--
theorem `card_erase_of_mem` / 定理 `card_erase_of_mem`

English:
theorem card_erase_of_mem
  statement: a in s -> #(s.erase a) = #s - 1
  proof: Multiset.card_erase_of_mem

中文:
定理 card_erase_of_mem
  结论: a in s -> #(s.erase a) = #s - 1
  证明: Multiset.card_erase_of_mem

Depends on / 依赖: Multiset, Multiset.card_erase_of_mem, card_erase_of_mem
-/
theorem card_erase_of_mem : a in s -> #(s.erase a) = #s - 1 :=
  Multiset.card_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
/--
theorem `card_erase_add_one` / 定理 `card_erase_add_one`

English:
theorem card_erase_add_one
  statement: a in s -> #(s.erase a) + 1 = #s
  proof: Multiset.card_erase_add_one

中文:
定理 card_erase_add_one
  结论: a in s -> #(s.erase a) + 1 = #s
  证明: Multiset.card_erase_add_one

Depends on / 依赖: Multiset, Multiset.card_erase_add_one, card_erase_add_one
-/
theorem card_erase_add_one : a in s -> #(s.erase a) + 1 = #s :=
  Multiset.card_erase_add_one

/--
theorem `card_erase_lt_of_mem` / 定理 `card_erase_lt_of_mem`

English:
theorem card_erase_lt_of_mem
  statement: a in s -> #(s.erase a) < #s
  proof: Multiset.card_erase_lt_of_mem

中文:
定理 card_erase_lt_of_mem
  结论: a in s -> #(s.erase a) < #s
  证明: Multiset.card_erase_lt_of_mem

Depends on / 依赖: Multiset, Multiset.card_erase_lt_of_mem, card_erase_lt_of_mem
-/
theorem card_erase_lt_of_mem : a in s -> #(s.erase a) < #s :=
  Multiset.card_erase_lt_of_mem

/--
theorem `card_erase_le` / 定理 `card_erase_le`

English:
theorem card_erase_le
  statement: #(s.erase a) <= #s
  proof: Multiset.card_erase_le

中文:
定理 card_erase_le
  结论: #(s.erase a) <= #s
  证明: Multiset.card_erase_le

Depends on / 依赖: Multiset, Multiset.card_erase_le, card_erase_le
-/
theorem card_erase_le : #(s.erase a) <= #s :=
  Multiset.card_erase_le

/--
theorem `pred_card_le_card_erase` / 定理 `pred_card_le_card_erase`

English:
theorem pred_card_le_card_erase
  statement: #s - 1 <= #(s.erase a)
  proof: by grind

中文:
定理 pred_card_le_card_erase
  结论: #s - 1 <= #(s.erase a)
  证明: by grind
-/
theorem pred_card_le_card_erase : #s - 1 <= #(s.erase a) := by grind

/--
theorem `card_erase_eq_ite` / 定理 `card_erase_eq_ite`

English:
theorem card_erase_eq_ite
  statement: #(s.erase a) = if a in s then #s - 1 else #s
  proof: Multiset.card_erase_eq_ite

中文:
定理 card_erase_eq_ite
  结论: #(s.erase a) = if a in s then #s - 1 else #s
  证明: Multiset.card_erase_eq_ite

Depends on / 依赖: Multiset, Multiset.card_erase_eq_ite, card_erase_eq_ite
-/
theorem card_erase_eq_ite : #(s.erase a) = if a in s then #s - 1 else #s :=
  Multiset.card_erase_eq_ite

end InsertErase

@[simp, grind =]
/--
theorem `card_range` / 定理 `card_range`

English:
theorem card_range
  given: (n : Nat)
  statement: #(range n) = n
  proof: Multiset.card_range n

@[simp, grind =]

中文:
定理 card_range
  条件: (n : 自然数)
  结论: #(range n) = n
  证明: Multiset.card_range n

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.card_range, card_range
-/
theorem card_range (n : Nat) : #(range n) = n :=
  Multiset.card_range n

@[simp, grind =]
/--
theorem `card_attach` / 定理 `card_attach`

English:
theorem card_attach
  statement: #s.attach = #s
  proof: Multiset.card_attach

中文:
定理 card_attach
  结论: #s.attach = #s
  证明: Multiset.card_attach

Depends on / 依赖: Multiset, Multiset.card_attach, card_attach
-/
theorem card_attach : #s.attach = #s :=
  Multiset.card_attach

end Finset

open scoped Finset

section ToMultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

/--
theorem `Multiset.card_toFinset` / 定理 `Multiset.card_toFinset`

English:
theorem Multiset.card_toFinset
  statement: #m.toFinset = Multiset.card m.dedup
  proof: rfl

中文:
定理 Multiset.card_toFinset
  结论: #m.toFinset = Multiset.card m.dedup
  证明: rfl
-/
theorem Multiset.card_toFinset : #m.toFinset = Multiset.card m.dedup :=
  rfl

/--
theorem `Multiset.toFinset_card_le` / 定理 `Multiset.toFinset_card_le`

English:
theorem Multiset.toFinset_card_le
  statement: #m.toFinset <= Multiset.card m
  proof: card_le_card dedup_le _

中文:
定理 Multiset.toFinset_card_le
  结论: #m.toFinset <= Multiset.card m
  证明: card_le_card dedup_le _

Depends on / 依赖: card_le_card, dedup_le
-/
theorem Multiset.toFinset_card_le : #m.toFinset <= Multiset.card m :=
card_le_card dedup_le _

/--
theorem `Multiset.toFinset_card_of_nodup` / 定理 `Multiset.toFinset_card_of_nodup`

English:
theorem Multiset.toFinset_card_of_nodup
  given: {m : Multiset α} (h : m.Nodup)
  proof: congr_arg card Multiset.dedup_eq_self.mpr h

中文:
定理 Multiset.toFinset_card_of_nodup
  条件: {m : Multiset α} (h : m.Nodup)
  证明: congr_arg card Multiset.dedup_eq_self.mpr h

Depends on / 依赖: Multiset, Multiset.dedup_eq_self.mpr, congr_arg, dedup_eq_self
-/
theorem Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) :
    #m.toFinset = Multiset.card m :=
congr_arg card Multiset.dedup_eq_self.mpr h

/--
theorem `Multiset.dedup_card_eq_card_iff_nodup` / 定理 `Multiset.dedup_card_eq_card_iff_nodup`

English:
theorem Multiset.dedup_card_eq_card_iff_nodup
  given: {m : Multiset α}
  proof: .trans ⟨fun h => eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

中文:
定理 Multiset.dedup_card_eq_card_iff_nodup
  条件: {m : Multiset α}
  证明: .trans ⟨fun h => eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

Depends on / 依赖: congr_arg, dedup_eq_self, dedup_le, eq_of_le_of_card_le, h.ge
-/
theorem Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α} :
    card m.dedup = card m ↔ m.Nodup :=
  .trans ⟨fun h => eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

/--
theorem `Multiset.toFinset_card_eq_card_iff_nodup` / 定理 `Multiset.toFinset_card_eq_card_iff_nodup`

English:
theorem Multiset.toFinset_card_eq_card_iff_nodup
  given: {m : Multiset α}
  proof: dedup_card_eq_card_iff_nodup

中文:
定理 Multiset.toFinset_card_eq_card_iff_nodup
  条件: {m : Multiset α}
  证明: dedup_card_eq_card_iff_nodup

Depends on / 依赖: dedup_card_eq_card_iff_nodup
-/
theorem Multiset.toFinset_card_eq_card_iff_nodup {m : Multiset α} :
    #m.toFinset = card m ↔ m.Nodup := dedup_card_eq_card_iff_nodup

/--
theorem `List.card_toFinset` / 定理 `List.card_toFinset`

English:
theorem List.card_toFinset
  statement: #l.toFinset = l.dedup.length
  proof: rfl

中文:
定理 列表.card_toFinset
  结论: #l.toFinset = l.dedup.length
  证明: rfl
-/
theorem List.card_toFinset : #l.toFinset = l.dedup.length :=
  rfl

/--
theorem `List.toFinset_card_le` / 定理 `List.toFinset_card_le`

English:
theorem List.toFinset_card_le
  statement: #l.toFinset <= l.length
  proof: Multiset.toFinset_card_le ⟦l⟧

中文:
定理 列表.toFinset_card_le
  结论: #l.toFinset <= l.length
  证明: Multiset.toFinset_card_le ⟦l⟧

Depends on / 依赖: Multiset, Multiset.toFinset_card_le, toFinset_card_le
-/
theorem List.toFinset_card_le : #l.toFinset <= l.length :=
  Multiset.toFinset_card_le ⟦l⟧

/--
theorem `List.toFinset_card_of_nodup` / 定理 `List.toFinset_card_of_nodup`

English:
theorem List.toFinset_card_of_nodup
  given: {l : List α} (h : l.Nodup)
  statement: #l.toFinset = l.length
  proof: Multiset.toFinset_card_of_nodup h

中文:
定理 列表.toFinset_card_of_nodup
  条件: {l : 列表 α} (h : l.Nodup)
  结论: #l.toFinset = l.length
  证明: Multiset.toFinset_card_of_nodup h

Depends on / 依赖: Multiset, Multiset.toFinset_card_of_nodup, toFinset_card_of_nodup
-/
theorem List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : #l.toFinset = l.length :=
  Multiset.toFinset_card_of_nodup h

/--
lemma `List.Nodup.card_eq_countP` / 引理 `List.Nodup.card_eq_countP`

English:
lemma List.Nodup.card_eq_countP
  given: {l : List α} {P : α -> Prop} [DecidablePred P] (h : l.Nodup)
  proof: by
  rw [l.countP_eq_length_filter]; rw [l.filter_toFinset P]
  exact toFinset_card_of_nodup (h.filter P)

中文:
引理 列表.Nodup.card_eq_countP
  条件: {l : 列表 α} {P : α -> 命题} [DecidablePred P] (h : l.Nodup)
  证明: by
  rw [l.countP_eq_length_filter]; rw [l.filter_toFinset P]
  exact toFinset_card_of_nodup (h.filter P)

Depends on / 依赖: countP_eq_length_filter, filter, filter_toFinset, h.filter, l.countP_eq_length_filter, l.filter_toFinset, toFinset_card_of_nodup
-/
lemma List.Nodup.card_eq_countP {l : List α} {P : α -> Prop} [DecidablePred P] (h : l.Nodup) :
    (l.toFinset.filter P).card = countP P l := by
  rw [l.countP_eq_length_filter]; rw [l.filter_toFinset P]
  exact toFinset_card_of_nodup (h.filter P)

end ToMultiset

namespace Finset

variable {s t u : Finset α} {f : α -> β} {n : Nat}

@[simp, grind =]
/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  given: (s : Finset α)
  statement: s.toList.length = #s
  proof: by
  rw [toList]; rw [← Multiset.coe_card]; rw [Multiset.coe_toList]; rw [card_def]

中文:
定理 length_toList
  条件: (s : 有限集 α)
  结论: s.toList.length = #s
  证明: by
  rw [toList]; rw [← Multiset.coe_card]; rw [Multiset.coe_toList]; rw [card_def]

Depends on / 依赖: Multiset, Multiset.coe_card, Multiset.coe_toList, card_def, coe_card, coe_toList, toList
-/
theorem length_toList (s : Finset α) : s.toList.length = #s := by
  rw [toList]; rw [← Multiset.coe_card]; rw [Multiset.coe_toList]; rw [card_def]

/--
theorem `card_image_le` / 定理 `card_image_le`

English:
theorem card_image_le
  given: [DecidableEq β]
  statement: #(s.image f) <= #s
  proof: by
  simpa only [card_map] using! (s.1.map f).toFinset_card_le

grind_pattern card_image_le => #(s.image f)
grind_pattern card_image_le => s.image f, #s

中文:
定理 card_image_le
  条件: [DecidableEq β]
  结论: #(s.像 f) <= #s
  证明: by
  simpa only [card_map] using! (s.1.map f).toFinset_card_le

grind_pattern card_image_le => #(s.image f)
grind_pattern card_image_le => s.image f, #s

Depends on / 依赖: card_map, toFinset_card_le
-/
theorem card_image_le [DecidableEq β] : #(s.image f) <= #s := by
  simpa only [card_map] using! (s.1.map f).toFinset_card_le

grind_pattern card_image_le => #(s.image f)
grind_pattern card_image_le => s.image f, #s

/--
theorem `card_image_of_injOn` / 定理 `card_image_of_injOn`

English:
theorem card_image_of_injOn
  given: [DecidableEq β] (H : Set.InjOn f s)
  statement: #(s.image f) = #s
  proof: by
  simp only [card, image_val_of_injOn H, card_map]

中文:
定理 card_image_of_injOn
  条件: [DecidableEq β] (H : 集合.单射限制 f s)
  结论: #(s.像 f) = #s
  证明: by
  simp only [card, image_val_of_injOn H, card_map]

Depends on / 依赖: card_map, image_val_of_injOn
-/
theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s := by
  simp only [card, image_val_of_injOn H, card_map]

/--
theorem `injOn_of_card_image_eq` / 定理 `injOn_of_card_image_eq`

English:
theorem injOn_of_card_image_eq
  given: [DecidableEq β] (H : #(s.image f) = #s)
  statement: Set.InjOn f s
  proof: by
  rw [card_def]; rw [card_def]; rw [image]; rw [toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

中文:
定理 injOn_of_card_image_eq
  条件: [DecidableEq β] (H : #(s.像 f) = #s)
  结论: 集合.单射限制 f s
  证明: by
  rw [card_def]; rw [card_def]; rw [image]; rw [toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

Depends on / 依赖: Multiset, Multiset.card_map, Multiset.dedup_eq_self, Multiset.dedup_le, Multiset.eq_of_le_of_card_le, card_def, card_map, dedup_eq_self, dedup_le, eq_of_le_of_card_le, inj_on_of_nodup_map, le_rfl, toFinset
-/
theorem injOn_of_card_image_eq [DecidableEq β] (H : #(s.image f) = #s) : Set.InjOn f s := by
  rw [card_def]; rw [card_def]; rw [image]; rw [toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

/--
theorem `card_image_iff` / 定理 `card_image_iff`

English:
theorem card_image_iff
  given: [DecidableEq β]
  statement: #(s.image f) = #s ↔ Set.InjOn f s
  proof: ⟨injOn_of_card_image_eq, card_image_of_injOn⟩

grind_pattern card_image_iff => #(s.image f)
grind_pattern card_image_iff => s.image f, #s

中文:
定理 card_image_iff
  条件: [DecidableEq β]
  结论: #(s.像 f) = #s ↔ 集合.单射限制 f s
  证明: ⟨injOn_of_card_image_eq, card_image_of_injOn⟩

grind_pattern card_image_iff => #(s.image f)
grind_pattern card_image_iff => s.image f, #s

Depends on / 依赖: card_image_of_injOn, injOn_of_card_image_eq
-/
theorem card_image_iff [DecidableEq β] : #(s.image f) = #s ↔ Set.InjOn f s :=
  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩

grind_pattern card_image_iff => #(s.image f)
grind_pattern card_image_iff => s.image f, #s

/--
theorem `card_image_of_injective` / 定理 `card_image_of_injective`

English:
theorem card_image_of_injective
  given: [DecidableEq β] (s : Finset α) (H : Injective f)
  proof: card_image_of_injOn fun _ _ _ _ h => H h

中文:
定理 card_image_of_injective
  条件: [DecidableEq β] (s : 有限集 α) (H : 单射 f)
  证明: card_image_of_injOn fun _ _ _ _ h => H h

Depends on / 依赖: card_image_of_injOn
-/
theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
  card_image_of_injOn fun _ _ _ _ h => H h

/--
theorem `fiber_card_ne_zero_iff_mem_image` / 定理 `fiber_card_ne_zero_iff_mem_image`

English:
theorem fiber_card_ne_zero_iff_mem_image
  given: (s : Finset α) (f : α -> β) [DecidableEq β] (y : β)
  proof: by
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]; rw [fiber_nonempty_iff_mem_image]

中文:
定理 fiber_card_ne_zero_iff_mem_image
  条件: (s : 有限集 α) (f : α -> β) [DecidableEq β] (y : β)
  证明: by
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]; rw [fiber_nonempty_iff_mem_image]

Depends on / 依赖: Nat.pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image, pos_iff_ne_zero
-/
theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α -> β) [DecidableEq β] (y : β) :
    #(s.filter fun x => f x = y) != 0 ↔ y in s.image f := by
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]; rw [fiber_nonempty_iff_mem_image]

/--
lemma `card_filter_le_iff` / 引理 `card_filter_le_iff`

English:
lemma card_filter_le_iff
  given: (s : Finset α) (P : α -> Prop) [DecidablePred P] (n : Nat)
  proof: (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h => H s'.1 (by simp_all) h,
    fun H s' hs' h => H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx => Multiset.subset_of_le hs' hx) h⟩

@[simp, grind =]

中文:
引理 card_filter_le_iff
  条件: (s : 有限集 α) (P : α -> 命题) [DecidablePred P] (n : 自然数)
  证明: (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h => H s'.1 (by simp_all) h,
    fun H s' hs' h => H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx => Multiset.subset_of_le hs' hx) h⟩

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.subset_of_le, card_filter_le_iff, nodup_of_le, subset_of_le
-/
lemma card_filter_le_iff (s : Finset α) (P : α -> Prop) [DecidablePred P] (n : Nat) :
    #(s.filter P) <= n ↔ forall s' subseteq s, n < #s' -> exists a in s', ¬ P a :=
  (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h => H s'.1 (by simp_all) h,
    fun H s' hs' h => H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx => Multiset.subset_of_le hs' hx) h⟩

@[simp, grind =]
/--
theorem `card_map` / 定理 `card_map`

English:
theorem card_map
  given: (f : α ↪ β)
  statement: #(s.map f) = #s
  proof: Multiset.card_map _ _

@[simp, grind =]

中文:
定理 card_map
  条件: (f : α ↪ β)
  结论: #(s.map f) = #s
  证明: Multiset.card_map _ _

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.card_map, card_map
-/
theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
  Multiset.card_map _ _

@[simp, grind =]
/--
theorem `card_subtype` / 定理 `card_subtype`

English:
theorem card_subtype
  given: (p : α -> Prop) [DecidablePred p] (s : Finset α)
  proof: by simp [Finset.subtype]

中文:
定理 card_subtype
  条件: (p : α -> 命题) [DecidablePred p] (s : 有限集 α)
  证明: by simp [Finset.subtype]

Depends on / 依赖: Finset, Finset.subtype, subtype
-/
theorem card_subtype (p : α -> Prop) [DecidablePred p] (s : Finset α) :
    #(s.subtype p) = #(s.filter p) := by simp [Finset.subtype]

/--
theorem `card_filter_le` / 定理 `card_filter_le`

English:
theorem card_filter_le
  given: (s : Finset α) (p : α -> Prop) [DecidablePred p]
  proof: card_le_card filter_subset _ _

grind_pattern card_filter_le => #(s.filter p)
grind_pattern card_filter_le => s.filter p, #s

中文:
定理 card_filter_le
  条件: (s : 有限集 α) (p : α -> 命题) [DecidablePred p]
  证明: card_le_card filter_subset _ _

grind_pattern card_filter_le => #(s.filter p)
grind_pattern card_filter_le => s.filter p, #s

Depends on / 依赖: card_le_card, filter_subset
-/
theorem card_filter_le (s : Finset α) (p : α -> Prop) [DecidablePred p] :
    #(s.filter p) <= #s :=
card_le_card filter_subset _ _

grind_pattern card_filter_le => #(s.filter p)
grind_pattern card_filter_le => s.filter p, #s

/--
theorem `eq_of_subset_of_card_le` / 定理 `eq_of_subset_of_card_le`

English:
theorem eq_of_subset_of_card_le
  given: (h : s subseteq t) (h₂ : #t <= #s)
  statement: s = t
  proof: eq_of_veq Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

中文:
定理 eq_of_subset_of_card_le
  条件: (h : s subseteq t) (h₂ : #t <= #s)
  结论: s = t
  证明: eq_of_veq Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

Depends on / 依赖: Multiset, Multiset.eq_of_le_of_card_le, eq_of_le_of_card_le, eq_of_veq, val_le_iff, val_le_iff.mpr
-/
theorem eq_of_subset_of_card_le (h : s subseteq t) (h₂ : #t <= #s) : s = t :=
eq_of_veq Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

/--
theorem `eq_iff_card_le_of_subset` / 定理 `eq_iff_card_le_of_subset`

English:
theorem eq_iff_card_le_of_subset
  given: (hst : s subseteq t)
  statement: #t <= #s ↔ s = t
  proof: ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩

中文:
定理 eq_iff_card_le_of_subset
  条件: (hst : s subseteq t)
  结论: #t <= #s ↔ s = t
  证明: ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩

Depends on / 依赖: congr_arg, eq_of_subset_of_card_le, ge_of_eq
-/
theorem eq_iff_card_le_of_subset (hst : s subseteq t) : #t <= #s ↔ s = t :=
  ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩

/--
theorem `eq_of_superset_of_card_ge` / 定理 `eq_of_superset_of_card_ge`

English:
theorem eq_of_superset_of_card_ge
  given: (hst : s subseteq t) (hts : #t <= #s)
  statement: t = s
  proof: (eq_of_subset_of_card_le hst hts).symm

中文:
定理 eq_of_superset_of_card_ge
  条件: (hst : s subseteq t) (hts : #t <= #s)
  结论: t = s
  证明: (eq_of_subset_of_card_le hst hts).symm

Depends on / 依赖: eq_of_subset_of_card_le
-/
theorem eq_of_superset_of_card_ge (hst : s subseteq t) (hts : #t <= #s) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm

/--
theorem `eq_iff_card_ge_of_superset` / 定理 `eq_iff_card_ge_of_superset`

English:
theorem eq_iff_card_ge_of_superset
  given: (hst : s subseteq t)
  statement: #t <= #s ↔ t = s
  proof: (eq_iff_card_le_of_subset hst).trans eq_comm

中文:
定理 eq_iff_card_ge_of_superset
  条件: (hst : s subseteq t)
  结论: #t <= #s ↔ t = s
  证明: (eq_iff_card_le_of_subset hst).trans eq_comm

Depends on / 依赖: eq_comm, eq_iff_card_le_of_subset
-/
theorem eq_iff_card_ge_of_superset (hst : s subseteq t) : #t <= #s ↔ t = s :=
  (eq_iff_card_le_of_subset hst).trans eq_comm

/--
theorem `subset_iff_eq_of_card_le` / 定理 `subset_iff_eq_of_card_le`

English:
theorem subset_iff_eq_of_card_le
  given: (h : #t <= #s)
  statement: s subseteq t ↔ s = t
  proof: ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset⟩

中文:
定理 subset_iff_eq_of_card_le
  条件: (h : #t <= #s)
  结论: s subseteq t ↔ s = t
  证明: ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset⟩

Depends on / 依赖: Eq.subset, eq_of_subset_of_card_le, subset
-/
theorem subset_iff_eq_of_card_le (h : #t <= #s) : s subseteq t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset⟩

/--
theorem `map_eq_of_subset` / 定理 `map_eq_of_subset`

English:
theorem map_eq_of_subset
  given: {f : α ↪ α} (hs : s.map f subseteq s)
  statement: s.map f = s
  proof: eq_of_subset_of_card_le hs (card_map _).ge

中文:
定理 map_eq_of_subset
  条件: {f : α ↪ α} (hs : s.map f subseteq s)
  结论: s.map f = s
  证明: eq_of_subset_of_card_le hs (card_map _).ge

Depends on / 依赖: card_map, eq_of_subset_of_card_le
-/
theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f subseteq s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge

/--
theorem `card_filter_eq_iff` / 定理 `card_filter_eq_iff`

English:
theorem card_filter_eq_iff
  given: {p : α -> Prop} [DecidablePred p]
  proof: by
  rw [← (card_filter_le s p).ge_iff_eq]; rw [eq_iff_card_le_of_subset (filter_subset p s)]; rw [filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff

中文:
定理 card_filter_eq_iff
  条件: {p : α -> 命题} [DecidablePred p]
  证明: by
  rw [← (card_filter_le s p).ge_iff_eq]; rw [eq_iff_card_le_of_subset (filter_subset p s)]; rw [filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff

Depends on / 依赖: card_filter_le, eq_iff_card_le_of_subset, filter_eq_self, filter_subset, ge_iff_eq
-/
theorem card_filter_eq_iff {p : α -> Prop} [DecidablePred p] :
    #(s.filter p) = #s ↔ forall x in s, p x := by
  rw [← (card_filter_le s p).ge_iff_eq]; rw [eq_iff_card_le_of_subset (filter_subset p s)]; rw [filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff

/--
theorem `card_filter_eq_zero_iff` / 定理 `card_filter_eq_zero_iff`

English:
theorem card_filter_eq_zero_iff
  given: {p : α -> Prop} [DecidablePred p]
  proof: by
  rw [card_eq_zero]; rw [filter_eq_empty_iff]

@[gcongr]
nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card val_lt_iff.2 h

中文:
定理 card_filter_eq_zero_iff
  条件: {p : α -> 命题} [DecidablePred p]
  证明: by
  rw [card_eq_zero]; rw [filter_eq_empty_iff]

@[gcongr]
nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card val_lt_iff.2 h

Depends on / 依赖: card_eq_zero, filter_eq_empty_iff
-/
theorem card_filter_eq_zero_iff {p : α -> Prop} [DecidablePred p] :
    #(s.filter p) = 0 ↔ forall x in s, ¬ p x := by
  rw [card_eq_zero]; rw [filter_eq_empty_iff]

@[gcongr]
nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card val_lt_iff.2 h

/--
lemma `card_strictMono` / 引理 `card_strictMono`

English:
lemma card_strictMono
  statement: StrictMono (card : Finset α -> Nat)
  proof: fun _ _ => card_lt_card

中文:
引理 card_strictMono
  结论: 严格递增 (card : 有限集 α -> 自然数)
  证明: fun _ _ => card_lt_card

Depends on / 依赖: card_lt_card
-/
lemma card_strictMono : StrictMono (card : Finset α -> Nat) := fun _ _ => card_lt_card

section bij

/--
theorem `card_eq_of_bijective` / 定理 `card_eq_of_bijective`

English:
theorem card_eq_of_bijective
  statement: (f : forall i, i < n -> α) (hf : forall a in s, exists i, exists h : i < n, f i h = a)
  proof: by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a in s ↔ exists (i : _) (hi : i in range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    #s = #((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
    _ = #(range n).attach := ?_
    _ = #(range n) := card_attach
    _ = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
exact Subtype.ext f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

中文:
定理 card_eq_of_bijective
  结论: (f : 对任意 i, i < n -> α) (hf : 对任意 a in s, 存在 i, 存在 h : i < n, f i h = a)
  证明: by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a in s ↔ exists (i : _) (hi : i in range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    #s = #((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
    _ = #(range n).attach := ?_
    _ = #(range n) := card_attach
    _ = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
exact Subtype.ext f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

Depends on / 依赖: Subtype, Subtype.exists, attach, attach.image, card_attach, classical, mem_attach, mem_image, mem_range, true_and
-/
theorem card_eq_of_bijective (f : forall i, i < n -> α) (hf : forall a in s, exists i, exists h : i < n, f i h = a)
    (hf' : forall i (h : i < n), f i h in s)
    (f_inj : forall i j (hi : i < n) (hj : j < n), f i hi = f j hj -> i = j) : #s = n := by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a in s ↔ exists (i : _) (hi : i in range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    #s = #((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
    _ = #(range n).attach := ?_
    _ = #(range n) := card_attach
    _ = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
exact Subtype.ext f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

variable {t : Finset β}

/--
lemma `card_bij` / 引理 `card_bij`

English:
lemma card_bij
  statement: (i : forall a in s, β) (hi : forall a ha, i a ha in t)
  proof: by
  classical
  calc
    #s = #s.attach := card_attach.symm
    _ = #(s.attach.image fun a => i a.1 a.2) := Eq.symm ?_
    _ = #t := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

中文:
引理 card_bij
  结论: (i : 对任意 a in s, β) (hi : 对任意 a ha, i a ha in t)
  证明: by
  classical
  calc
    #s = #s.attach := card_attach.symm
    _ = #(s.attach.image fun a => i a.1 a.2) := Eq.symm ?_
    _ = #t := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

Depends on / 依赖: Eq.symm, attach, card_attach, card_attach.symm, card_image_of_injective, classical, i_inj, i_surj, mem_image, s.attach, s.attach.image
-/
lemma card_bij (i : forall a in s, β) (hi : forall a ha, i a ha in t)
    (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂)
    (i_surj : forall b in t, exists a ha, i a ha = b) : #s = #t := by
  classical
  calc
    #s = #s.attach := card_attach.symm
    _ = #(s.attach.image fun a => i a.1 a.2) := Eq.symm ?_
    _ = #t := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

/--
lemma `card_bij'` / 引理 `card_bij'`

English:
lemma card_bij'
  statement: (i : forall a in s, β) (j : forall a in t, α) (hi : forall a ha, i a ha in t)
  proof: by
  refine card_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

中文:
引理 card_bij'
  结论: (i : 对任意 a in s, β) (j : 对任意 a in t, α) (hi : 对任意 a ha, i a ha in t)
  证明: by
  refine card_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

Depends on / 依赖: card_bij, left_inv, right_inv
-/
lemma card_bij' (i : forall a in s, β) (j : forall a in t, α) (hi : forall a ha, i a ha in t)
    (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a ha) (hi a ha) = a)
    (right_inv : forall a ha, i (j a ha) (hj a ha) = a) : #s = #t := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

/--
lemma `card_nbij` / 引理 `card_nbij`

English:
lemma card_nbij
  statement: (i : α -> β) (hi : Set.MapsTo i s t) (i_inj : (s : Set α).InjOn i)
  proof: card_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj)

中文:
引理 card_nbij
  结论: (i : α -> β) (hi : 集合.映射到 i s t) (i_inj : (s : 集合 α).单射限制 i)
  证明: card_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj)

Depends on / 依赖: card_bij, i_inj, i_surj
-/
lemma card_nbij (i : α -> β) (hi : Set.MapsTo i s t) (i_inj : (s : Set α).InjOn i)
    (i_surj : (s : Set α).SurjOn i t) : #s = #t :=
  card_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj)

/--
lemma `card_nbij'` / 引理 `card_nbij'`

English:
lemma card_nbij'
  statement: (i : α -> β) (j : β -> α) (hi : Set.MapsTo i s t) (hj : Set.MapsTo j t s)
  proof: card_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv

中文:
引理 card_nbij'
  结论: (i : α -> β) (j : β -> α) (hi : 集合.映射到 i s t) (hj : 集合.映射到 j t s)
  证明: card_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv

Depends on / 依赖: card_bij, left_inv, right_inv
-/
lemma card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo i s t) (hj : Set.MapsTo j t s)
    (left_inv : Set.LeftInvOn j i s) (right_inv : Set.RightInvOn j i t) : #s = #t :=
  card_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv

/--
lemma `card_equiv` / 引理 `card_equiv`

English:
lemma card_equiv
  given: (e : α ≃ β) (hst : forall i, i in s ↔ e i in t)
  statement: #s = #t
  proof: by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]

中文:
引理 card_equiv
  条件: (e : α ≃ β) (hst : 对任意 i, i in s ↔ e i in t)
  结论: #s = #t
  证明: by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]

Depends on / 依赖: LeftInvOn, MapsTo, RightInvOn, Set.LeftInvOn, Set.MapsTo, Set.RightInvOn, card_nbij, e.symm
-/
lemma card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i in t) : #s = #t := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]

/--
lemma `card_bijective` / 引理 `card_bijective`

English:
lemma card_bijective
  given: (e : α -> β) (he : e.Bijective) (hst : forall i, i in s ↔ e i in t)
  proof: card_equiv (.ofBijective e he) hst

中文:
引理 card_bijective
  条件: (e : α -> β) (he : e.双射) (hst : 对任意 i, i in s ↔ e i in t)
  证明: card_equiv (.ofBijective e he) hst

Depends on / 依赖: card_equiv, ofBijective
-/
lemma card_bijective (e : α -> β) (he : e.Bijective) (hst : forall i, i in s ↔ e i in t) :
    #s = #t := card_equiv (.ofBijective e he) hst

/--
lemma `_root_.Set.BijOn.finsetCard_eq` / 引理 `_root_.Set.BijOn.finsetCard_eq`

English:
lemma _root_.Set.BijOn.finsetCard_eq
  given: (e : α -> β) (he : Set.BijOn e s t)
  statement: #s = #t
  proof: card_nbij e he.mapsTo he.injOn he.surjOn

中文:
引理 _root_.集合.双射限制.finsetCard_eq
  条件: (e : α -> β) (he : 集合.双射限制 e s t)
  结论: #s = #t
  证明: card_nbij e he.mapsTo he.injOn he.surjOn

Depends on / 依赖: card_nbij, he.injOn, he.mapsTo, he.surjOn, mapsTo, surjOn
-/
lemma _root_.Set.BijOn.finsetCard_eq (e : α -> β) (he : Set.BijOn e s t) : #s = #t :=
  card_nbij e he.mapsTo he.injOn he.surjOn

/--
lemma `card_le_card_of_injOn` / 引理 `card_le_card_of_injOn`

English:
lemma card_le_card_of_injOn
  given: (f : α -> β) (hf : Set.MapsTo f s t) (f_inj : (s : Set α).InjOn f)
  proof: by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
_ <= #t := card_le_card image_subset_iff.2 hf

中文:
引理 card_le_card_of_injOn
  条件: (f : α -> β) (hf : 集合.映射到 f s t) (f_inj : (s : 集合 α).单射限制 f)
  证明: by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
_ <= #t := card_le_card image_subset_iff.2 hf

Depends on / 依赖: card_image_of_injOn, card_le_card, classical, f_inj, image_subset_iff, s.image
-/
lemma card_le_card_of_injOn (f : α -> β) (hf : Set.MapsTo f s t) (f_inj : (s : Set α).InjOn f) :
    #s <= #t := by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
_ <= #t := card_le_card image_subset_iff.2 hf

/--
lemma `card_le_card_of_injective` / 引理 `card_le_card_of_injective`

English:
lemma card_le_card_of_injective
  given: {f : s -> t} (hf : f.Injective)
  statement: #s <= #t
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · classical
    let f' : α -> β := fun a => f (if ha : a in s then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply card_le_card_of_injOn f'
    · aesop (add safe unfold Set.MapsTo)
    · intro a₁ ha₁ a₂ ha₂ haa
      rw [mem_coe] at ha₁ ha₂
      simp only [f', ha₁, ha₂, ← Subtype.ext_iff] at haa
      exact Subtype.ext_iff.mp (hf haa)

grind_pattern card_le_card_of_injective => f.Injective, #s
grind_pattern card_le_card_of_injective => f.Injective, #t

中文:
引理 card_le_card_of_injective
  条件: {f : s -> t} (hf : f.单射)
  结论: #s <= #t
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · classical
    let f' : α -> β := fun a => f (if ha : a in s then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply card_le_card_of_injOn f'
    · aesop (add safe unfold Set.MapsTo)
    · intro a₁ ha₁ a₂ ha₂ haa
      rw [mem_coe] at ha₁ ha₂
      simp only [f', ha₁, ha₂, ← Subtype.ext_iff] at haa
      exact Subtype.ext_iff.mp (hf haa)

grind_pattern card_le_card_of_injective => f.Injective, #s
grind_pattern card_le_card_of_injective => f.Injective, #t

Depends on / 依赖: MapsTo, Set.MapsTo, Subtype, Subtype.ext_iff, Subtype.ext_iff.mp, card_le_card_of_injOn, classical, eq_empty_or_nonempty, ext_iff, mem_coe, s.eq_empty_or_nonempty
-/
lemma card_le_card_of_injective {f : s -> t} (hf : f.Injective) : #s <= #t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · classical
    let f' : α -> β := fun a => f (if ha : a in s then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply card_le_card_of_injOn f'
    · aesop (add safe unfold Set.MapsTo)
    · intro a₁ ha₁ a₂ ha₂ haa
      rw [mem_coe] at ha₁ ha₂
      simp only [f', ha₁, ha₂, ← Subtype.ext_iff] at haa
      exact Subtype.ext_iff.mp (hf haa)

grind_pattern card_le_card_of_injective => f.Injective, #s
grind_pattern card_le_card_of_injective => f.Injective, #t

/--
lemma `card_le_card_of_surjOn` / 引理 `card_le_card_of_surjOn`

English:
lemma card_le_card_of_surjOn
  given: (f : α -> β) (hf : Set.SurjOn f s t)
  statement: #t <= #s
  proof: by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

中文:
引理 card_le_card_of_surjOn
  条件: (f : α -> β) (hf : 集合.满射限制 f s t)
  结论: #t <= #s
  证明: by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

Depends on / 依赖: Set.SurjOn, SurjOn, card_image_le, card_le_card, classical, mod_cast
-/
lemma card_le_card_of_surjOn (f : α -> β) (hf : Set.SurjOn f s t) : #t <= #s := by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

/--
theorem `exists_ne_map_eq_of_card_lt_of_maps_to` / 定理 `exists_ne_map_eq_of_card_lt_of_maps_to`

English:
theorem exists_ne_map_eq_of_card_lt_of_maps_to
  statement: (hc : #t < #s) {f : α -> β}
  proof: by
  by_contra! hz
  refine hc.not_ge (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

中文:
定理 存在_ne_map_eq_of_card_lt_of_maps_to
  结论: (hc : #t < #s) {f : α -> β}
  证明: by
  by_contra! hz
  refine hc.not_ge (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

Depends on / 依赖: card_le_card_of_injOn, contrapose, hc.not_ge, not_ge
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to (hc : #t < #s) {f : α -> β}
    (hf : Set.MapsTo f s t) : exists x in s, exists y in s, x != y ∧ f x = f y := by
  by_contra! hz
  refine hc.not_ge (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

/--
theorem `exists_ne_map_eq_of_card_image_lt` / 定理 `exists_ne_map_eq_of_card_image_lt`

English:
theorem exists_ne_map_eq_of_card_image_lt
  given: [DecidableEq β] {f : α -> β} (hc : #(s.image f) < #s)
  proof: exists_ne_map_eq_of_card_lt_of_maps_to hc (coe_image (β := β) ▸ Set.mapsTo_image f s)

中文:
定理 存在_ne_map_eq_of_card_image_lt
  条件: [DecidableEq β] {f : α -> β} (hc : #(s.像 f) < #s)
  证明: exists_ne_map_eq_of_card_lt_of_maps_to hc (coe_image (β := β) ▸ Set.mapsTo_image f s)

Depends on / 依赖: Set.mapsTo_image, coe_image, exists_ne_map_eq_of_card_lt_of_maps_to, mapsTo_image
-/
theorem exists_ne_map_eq_of_card_image_lt [DecidableEq β] {f : α -> β} (hc : #(s.image f) < #s) :
    exists x in s, exists y in s, x != y ∧ f x = f y :=
  exists_ne_map_eq_of_card_lt_of_maps_to hc (coe_image (β := β) ▸ Set.mapsTo_image f s)

/--
theorem `not_injOn_of_card_image_lt` / 定理 `not_injOn_of_card_image_lt`

English:
theorem not_injOn_of_card_image_lt
  given: [DecidableEq β] {f : α -> β} (hc : #(s.image f) < #s)
  proof: mt card_image_of_injOn hc.ne

中文:
定理 not_injOn_of_card_image_lt
  条件: [DecidableEq β] {f : α -> β} (hc : #(s.像 f) < #s)
  证明: mt card_image_of_injOn hc.ne

Depends on / 依赖: card_image_of_injOn, hc.ne
-/
theorem not_injOn_of_card_image_lt [DecidableEq β] {f : α -> β} (hc : #(s.image f) < #s) :
    ¬ Set.InjOn f s :=
  mt card_image_of_injOn hc.ne

/--
lemma `le_card_of_inj_on_range` / 引理 `le_card_of_inj_on_range`

English:
lemma le_card_of_inj_on_range
  statement: (f : Nat -> α) (hf : forall i < n, f i in s)
  proof: calc
    n = #(range n) := (card_range n).symm
    _ <= #s := card_le_card_of_injOn f (by simpa [Set.MapsTo, mem_range] using hf) (by simpa)

中文:
引理 le_card_of_inj_on_range
  结论: (f : 自然数 -> α) (hf : 对任意 i < n, f i in s)
  证明: calc
    n = #(range n) := (card_range n).symm
    _ <= #s := card_le_card_of_injOn f (by simpa [Set.MapsTo, mem_range] using hf) (by simpa)

Depends on / 依赖: MapsTo, Set.MapsTo, card_le_card_of_injOn, card_range, mem_range
-/
lemma le_card_of_inj_on_range (f : Nat -> α) (hf : forall i < n, f i in s)
    (f_inj : forall i < n, forall j < n, f i = f j -> i = j) : n <= #s :=
  calc
    n = #(range n) := (card_range n).symm
    _ <= #s := card_le_card_of_injOn f (by simpa [Set.MapsTo, mem_range] using hf) (by simpa)

/--
lemma `surjOn_of_injOn_of_card_le` / 引理 `surjOn_of_injOn_of_card_le`

English:
lemma surjOn_of_injOn_of_card_le
  statement: (f : α -> β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s)
  proof: by
  classical
  suffices s.image f = t by rw [Finset.surjOn_iff_subset_image, this]
  have : s.image f subseteq t := hf.finsetImage_subset
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

中文:
引理 surjOn_of_injOn_of_card_le
  结论: (f : α -> β) (hf : 集合.映射到 f s t) (hinj : 集合.单射限制 f s)
  证明: by
  classical
  suffices s.image f = t by rw [Finset.surjOn_iff_subset_image, this]
  have : s.image f subseteq t := hf.finsetImage_subset
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

Depends on / 依赖: Finset, Finset.surjOn_iff_subset_image, card_image_of_injOn, classical, eq_of_subset_of_card_le, finsetImage_subset, hf.finsetImage_subset, hst.trans_eq, s.image, subseteq, surjOn_iff_subset_image, trans_eq
-/
lemma surjOn_of_injOn_of_card_le (f : α -> β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s)
    (hst : #t <= #s) : Set.SurjOn f s t := by
  classical
  suffices s.image f = t by rw [Finset.surjOn_iff_subset_image, this]
  have : s.image f subseteq t := hf.finsetImage_subset
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

/--
lemma `surj_on_of_inj_on_of_card_le` / 引理 `surj_on_of_inj_on_of_card_le`

English:
lemma surj_on_of_inj_on_of_card_le
  statement: (f : forall a in s, β) (hf : forall a ha, f a ha in t)
  proof: by
  let f' : s -> β := fun a => f a a.2
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy => Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx => hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le _ hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

中文:
引理 surj_on_of_inj_on_of_card_le
  结论: (f : 对任意 a in s, β) (hf : 对任意 a ha, f a ha in t)
  证明: by
  let f' : s -> β := fun a => f a a.2
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy => Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx => hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le _ hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

Depends on / 依赖: MapsTo, Set.InjOn, Set.MapsTo, Subtype, Subtype.ext, attach, card_attach, hmapsto, s.attach, surjOn_of_injOn_of_card_le
-/
lemma surj_on_of_inj_on_of_card_le (f : forall a in s, β) (hf : forall a ha, f a ha in t)
    (hinj : forall a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ -> a₁ = a₂) (hst : #t <= #s) :
    forall b in t, exists a ha, b = f a ha := by
  let f' : s -> β := fun a => f a a.2
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy => Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx => hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le _ hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

/--
lemma `injOn_of_surjOn_of_card_le` / 引理 `injOn_of_surjOn_of_card_le`

English:
lemma injOn_of_surjOn_of_card_le
  statement: (f : α -> β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
  proof: by
  classical
have : s.image f = t := Finset.coe_injective by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) <= #s := card_image_le
  rw [← card_image_iff]
  lia

中文:
引理 injOn_of_surjOn_of_card_le
  结论: (f : α -> β) (hf : 集合.映射到 f s t) (hsurj : 集合.满射限制 f s t)
  证明: by
  classical
have : s.image f = t := Finset.coe_injective by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) <= #s := card_image_le
  rw [← card_image_iff]
  lia

Depends on / 依赖: Finset, Finset.coe_injective, card_image_iff, card_image_le, classical, coe_injective, hsurj.image_eq_of_mapsTo, image_eq_of_mapsTo, s.image
-/
lemma injOn_of_surjOn_of_card_le (f : α -> β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (hst : #s <= #t) : Set.InjOn f s := by
  classical
have : s.image f = t := Finset.coe_injective by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) <= #s := card_image_le
  rw [← card_image_iff]
  lia

/--
theorem `inj_on_of_surj_on_of_card_le` / 定理 `inj_on_of_surj_on_of_card_le`

English:
theorem inj_on_of_surj_on_of_card_le
  statement: (f : forall a in s, β) (hf : forall a ha, f a ha in t)
  proof: by
  let f' : s -> β := fun a => f a a.2
  have hsurj' : Set.SurjOn f' s.attach t := fun x hx => by simpa [f'] using hsurj x hx
  have hinj' := injOn_of_surjOn_of_card_le f' (fun x hx => hf _ _) hsurj' (by simpa)
  exact congrArg Subtype.val (@hinj' ⟨a₁, ha₁⟩ (by simp) ⟨a₂, ha₂⟩ (by simp) ha₁a₂)

中文:
定理 inj_on_of_surj_on_of_card_le
  结论: (f : 对任意 a in s, β) (hf : 对任意 a ha, f a ha in t)
  证明: by
  let f' : s -> β := fun a => f a a.2
  have hsurj' : Set.SurjOn f' s.attach t := fun x hx => by simpa [f'] using hsurj x hx
  have hinj' := injOn_of_surjOn_of_card_le f' (fun x hx => hf _ _) hsurj' (by simpa)
  exact congrArg Subtype.val (@hinj' ⟨a₁, ha₁⟩ (by simp) ⟨a₂, ha₂⟩ (by simp) ha₁a₂)

Depends on / 依赖: Set.SurjOn, Subtype, Subtype.val, SurjOn, attach, injOn_of_surjOn_of_card_le, s.attach
-/
theorem inj_on_of_surj_on_of_card_le (f : forall a in s, β) (hf : forall a ha, f a ha in t)
    (hsurj : forall b in t, exists a ha, f a ha = b) (hst : #s <= #t) ⦃a₁⦄ (ha₁ : a₁ in s) ⦃a₂⦄
    (ha₂ : a₂ in s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ := by
  let f' : s -> β := fun a => f a a.2
  have hsurj' : Set.SurjOn f' s.attach t := fun x hx => by simpa [f'] using hsurj x hx
  have hinj' := injOn_of_surjOn_of_card_le f' (fun x hx => hf _ _) hsurj' (by simpa)
  exact congrArg Subtype.val (@hinj' ⟨a₁, ha₁⟩ (by simp) ⟨a₂, ha₂⟩ (by simp) ha₁a₂)

/--
lemma `image_eq_iff_bijOn_of_card` / 引理 `image_eq_iff_bijOn_of_card`

English:
lemma image_eq_iff_bijOn_of_card
  given: [DecidableEq β] (h : #s <= #t)
  proof: by
  grind [injOn_of_surjOn_of_card_le, Set.BijOn, image_eq_iff_surjOn_mapsTo]

中文:
引理 image_eq_iff_bijOn_of_card
  条件: [DecidableEq β] (h : #s <= #t)
  证明: by
  grind [injOn_of_surjOn_of_card_le, Set.BijOn, image_eq_iff_surjOn_mapsTo]

Depends on / 依赖: Set.BijOn, image_eq_iff_surjOn_mapsTo, injOn_of_surjOn_of_card_le
-/
lemma image_eq_iff_bijOn_of_card [DecidableEq β] (h : #s <= #t) :
    s.image f = t ↔ Set.BijOn f s t := by
  grind [injOn_of_surjOn_of_card_le, Set.BijOn, image_eq_iff_surjOn_mapsTo]

end bij

@[simp, grind =]
/--
theorem `card_disjUnion` / 定理 `card_disjUnion`

English:
theorem card_disjUnion
  given: (s t : Finset α) (h)
  statement: #(s.disjUnion t h) = #s + #t
  proof: Multiset.card_add _ _

中文:
定理 card_disjUnion
  条件: (s t : 有限集 α) (h)
  结论: #(s.disjUnion t h) = #s + #t
  证明: Multiset.card_add _ _

Depends on / 依赖: Multiset, Multiset.card_add, card_add
-/
theorem card_disjUnion (s t : Finset α) (h) : #(s.disjUnion t h) = #s + #t :=
  Multiset.card_add _ _

/-! ### Lattice structure -/

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we've already turned it on earlier in this file, but need to redo it now.)
local grind_pattern card_le_card => #s, #t

section Lattice

variable [DecidableEq α]

/--
theorem `card_union_add_card_inter` / 定理 `card_union_add_card_inter`

English:
theorem card_union_add_card_inter
  given: (s t : Finset α)
  proof: Finset.induction_on t (by simp) (by grind)

grind_pattern card_union_add_card_inter => #(s union t), s inter t
grind_pattern card_union_add_card_inter => s union t, #(s inter t)
grind_pattern card_union_add_card_inter => #(s union t), #s
grind_pattern card_union_add_card_inter => #(s union t), #t
grind_pattern card_union_add_card_inter => #(s inter t), #s
grind_pattern card_union_add_card_inter => #(s inter t), #t

中文:
定理 card_union_add_card_inter
  条件: (s t : 有限集 α)
  证明: Finset.induction_on t (by simp) (by grind)

grind_pattern card_union_add_card_inter => #(s union t), s inter t
grind_pattern card_union_add_card_inter => s union t, #(s inter t)
grind_pattern card_union_add_card_inter => #(s union t), #s
grind_pattern card_union_add_card_inter => #(s union t), #t
grind_pattern card_union_add_card_inter => #(s inter t), #s
grind_pattern card_union_add_card_inter => #(s inter t), #t

Depends on / 依赖: Finset, Finset.induction_on, induction_on
-/
theorem card_union_add_card_inter (s t : Finset α) :
    #(s union t) + #(s inter t) = #s + #t :=
  Finset.induction_on t (by simp) (by grind)

grind_pattern card_union_add_card_inter => #(s union t), s inter t
grind_pattern card_union_add_card_inter => s union t, #(s inter t)
grind_pattern card_union_add_card_inter => #(s union t), #s
grind_pattern card_union_add_card_inter => #(s union t), #t
grind_pattern card_union_add_card_inter => #(s inter t), #s
grind_pattern card_union_add_card_inter => #(s inter t), #t

/--
theorem `card_inter_add_card_union` / 定理 `card_inter_add_card_union`

English:
theorem card_inter_add_card_union
  given: (s t : Finset α)
  proof: by grind

中文:
定理 card_inter_add_card_union
  条件: (s t : 有限集 α)
  证明: by grind
-/
theorem card_inter_add_card_union (s t : Finset α) :
    #(s inter t) + #(s union t) = #s + #t := by grind

/--
lemma `card_union` / 引理 `card_union`

English:
lemma card_union
  given: (s t : Finset α)
  statement: #(s union t) = #s + #t - #(s inter t)
  proof: by grind

中文:
引理 card_union
  条件: (s t : 有限集 α)
  结论: #(s union t) = #s + #t - #(s inter t)
  证明: by grind
-/
lemma card_union (s t : Finset α) : #(s union t) = #s + #t - #(s inter t) := by grind

/--
lemma `card_inter` / 引理 `card_inter`

English:
lemma card_inter
  given: (s t : Finset α)
  statement: #(s inter t) = #s + #t - #(s union t)
  proof: by grind

中文:
引理 card_inter
  条件: (s t : 有限集 α)
  结论: #(s inter t) = #s + #t - #(s union t)
  证明: by grind
-/
lemma card_inter (s t : Finset α) : #(s inter t) = #s + #t - #(s union t) := by grind

/--
theorem `card_union_le` / 定理 `card_union_le`

English:
theorem card_union_le
  given: (s t : Finset α)
  statement: #(s union t) <= #s + #t
  proof: by grind

中文:
定理 card_union_le
  条件: (s t : 有限集 α)
  结论: #(s union t) <= #s + #t
  证明: by grind
-/
theorem card_union_le (s t : Finset α) : #(s union t) <= #s + #t := by grind

/--
lemma `card_union_eq_card_add_card` / 引理 `card_union_eq_card_add_card`

English:
lemma card_union_eq_card_add_card
  statement: #(s union t) = #s + #t ↔ Disjoint s t
  proof: by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[grind =]

中文:
引理 card_union_eq_card_add_card
  结论: #(s union t) = #s + #t ↔ Disjoint s t
  证明: by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[grind =]

Depends on / 依赖: card_union_add_card_inter, disjoint_iff_inter_eq_empty
-/
lemma card_union_eq_card_add_card : #(s union t) = #s + #t ↔ Disjoint s t := by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[grind =]
/--
theorem `card_sdiff_of_subset` / 定理 `card_sdiff_of_subset`

English:
theorem card_sdiff_of_subset
  given: (h : s subseteq t)
  statement: #(t \ s) = #t - #s
  proof: by
  suffices #(t \ s) = #(t \ s union s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint]; rw [Nat.add_sub_cancel_right]

@[grind =]

中文:
定理 card_sdiff_of_subset
  条件: (h : s subseteq t)
  结论: #(t \ s) = #t - #s
  证明: by
  suffices #(t \ s) = #(t \ s union s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint]; rw [Nat.add_sub_cancel_right]

@[grind =]

Depends on / 依赖: Nat.add_sub_cancel_right, add_sub_cancel_right, card_union_of_disjoint, sdiff_disjoint, sdiff_union_of_subset
-/
theorem card_sdiff_of_subset (h : s subseteq t) : #(t \ s) = #t - #s := by
  suffices #(t \ s) = #(t \ s union s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint]; rw [Nat.add_sub_cancel_right]

@[grind =]
/--
theorem `card_sdiff` / 定理 `card_sdiff`

English:
theorem card_sdiff
  statement: #(t \ s) = #t - #(s inter t)
  proof: by
  rw [← card_sdiff_of_subset] <;> grind

中文:
定理 card_sdiff
  结论: #(t \ s) = #t - #(s inter t)
  证明: by
  rw [← card_sdiff_of_subset] <;> grind

Depends on / 依赖: card_sdiff_of_subset
-/
theorem card_sdiff : #(t \ s) = #t - #(s inter t) := by
  rw [← card_sdiff_of_subset] <;> grind

/--
theorem `card_sdiff_add_card_eq_card` / 定理 `card_sdiff_add_card_eq_card`

English:
theorem card_sdiff_add_card_eq_card
  given: (h : s subseteq t)
  statement: #(t \ s) + #s = #t
  proof: by grind

中文:
定理 card_sdiff_add_card_eq_card
  条件: (h : s subseteq t)
  结论: #(t \ s) + #s = #t
  证明: by grind
-/
theorem card_sdiff_add_card_eq_card (h : s subseteq t) : #(t \ s) + #s = #t := by grind

/--
lemma `card_sub_card_eq` / 引理 `card_sub_card_eq`

English:
lemma card_sub_card_eq
  given: (s t : Finset α)
  statement: #t - #s = #(t \ s) - #(s \ t)
  proof: calc
    #t - #s = #t - #(s inter t) - #(s \ t) := by grind
    _ = #(t \ (s inter t)) - #(s \ t) := by grind
    _ = #(t \ s) - #(s \ t) := by grind

中文:
引理 card_sub_card_eq
  条件: (s t : 有限集 α)
  结论: #t - #s = #(t \ s) - #(s \ t)
  证明: calc
    #t - #s = #t - #(s inter t) - #(s \ t) := by grind
    _ = #(t \ (s inter t)) - #(s \ t) := by grind
    _ = #(t \ s) - #(s \ t) := by grind
-/
lemma card_sub_card_eq (s t : Finset α) : #t - #s = #(t \ s) - #(s \ t) :=
  calc
    #t - #s = #t - #(s inter t) - #(s \ t) := by grind
    _ = #(t \ (s inter t)) - #(s \ t) := by grind
    _ = #(t \ s) - #(s \ t) := by grind

/--
theorem `le_card_sdiff` / 定理 `le_card_sdiff`

English:
theorem le_card_sdiff
  given: (s t : Finset α)
  statement: #t - #s <= #(t \ s)
  proof: by grind

grind_pattern le_card_sdiff => #(t \ s), #t
grind_pattern le_card_sdiff => #(t \ s), #s

中文:
定理 le_card_sdiff
  条件: (s t : 有限集 α)
  结论: #t - #s <= #(t \ s)
  证明: by grind

grind_pattern le_card_sdiff => #(t \ s), #t
grind_pattern le_card_sdiff => #(t \ s), #s
-/
theorem le_card_sdiff (s t : Finset α) : #t - #s <= #(t \ s) := by grind

grind_pattern le_card_sdiff => #(t \ s), #t
grind_pattern le_card_sdiff => #(t \ s), #s

/--
theorem `card_le_card_sdiff_add_card` / 定理 `card_le_card_sdiff_add_card`

English:
theorem card_le_card_sdiff_add_card
  statement: #s <= #(s \ t) + #t
  proof: by grind

中文:
定理 card_le_card_sdiff_add_card
  结论: #s <= #(s \ t) + #t
  证明: by grind
-/
theorem card_le_card_sdiff_add_card : #s <= #(s \ t) + #t := by grind

/--
theorem `card_sdiff_add_card` / 定理 `card_sdiff_add_card`

English:
theorem card_sdiff_add_card
  given: (s t : Finset α)
  statement: #(s \ t) + #t = #(s union t)
  proof: by
  rw [← card_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

中文:
定理 card_sdiff_add_card
  条件: (s t : 有限集 α)
  结论: #(s \ t) + #t = #(s union t)
  证明: by
  rw [← card_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

Depends on / 依赖: card_union_of_disjoint, sdiff_disjoint, sdiff_union_self_eq_union
-/
theorem card_sdiff_add_card (s t : Finset α) : #(s \ t) + #t = #(s union t) := by
  rw [← card_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

/--
theorem `sdiff_nonempty_of_card_lt_card` / 定理 `sdiff_nonempty_of_card_lt_card`

English:
theorem sdiff_nonempty_of_card_lt_card
  given: (h : #s < #t)
  statement: (t \ s).Nonempty
  proof: by
  grind

omit [DecidableEq α] in

中文:
定理 sdiff_nonempty_of_card_lt_card
  条件: (h : #s < #t)
  结论: (t \ s).非空
  证明: by
  grind

omit [DecidableEq α] in
-/
theorem sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty := by
  grind

omit [DecidableEq α] in
/--
theorem `exists_mem_notMem_of_card_lt_card` / 定理 `exists_mem_notMem_of_card_lt_card`

English:
theorem exists_mem_notMem_of_card_lt_card
  given: (h : #s < #t)
  statement: exists e, e in t ∧ e ∉ s
  proof: by
  classical simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h

@[simp]

中文:
定理 存在_mem_notMem_of_card_lt_card
  条件: (h : #s < #t)
  结论: 存在 e, e in t ∧ e ∉ s
  证明: by
  classical simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h

@[simp]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, classical, sdiff_nonempty_of_card_lt_card
-/
theorem exists_mem_notMem_of_card_lt_card (h : #s < #t) : exists e, e in t ∧ e ∉ s := by
  classical simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h

@[simp]
/--
lemma `card_sdiff_add_card_inter` / 引理 `card_sdiff_add_card_inter`

English:
lemma card_sdiff_add_card_inter
  given: (s t : Finset α)
  proof: by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

grind_pattern card_sdiff_add_card_inter => #(s \ t), #(s inter t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s

@[simp]

中文:
引理 card_sdiff_add_card_inter
  条件: (s t : 有限集 α)
  证明: by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

grind_pattern card_sdiff_add_card_inter => #(s \ t), #(s inter t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s

@[simp]

Depends on / 依赖: card_union_of_disjoint, disjoint_sdiff_inter, sdiff_union_inter
-/
lemma card_sdiff_add_card_inter (s t : Finset α) :
    #(s \ t) + #(s inter t) = #s := by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

grind_pattern card_sdiff_add_card_inter => #(s \ t), #(s inter t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s

@[simp]
/--
lemma `card_inter_add_card_sdiff` / 引理 `card_inter_add_card_sdiff`

English:
lemma card_inter_add_card_sdiff
  given: (s t : Finset α)
  proof: by grind

中文:
引理 card_inter_add_card_sdiff
  条件: (s t : 有限集 α)
  证明: by grind
-/
lemma card_inter_add_card_sdiff (s t : Finset α) :
    #(s inter t) + #(s \ t) = #s := by grind

/--
lemma `card_sdiff_le_card_sdiff_iff` / 引理 `card_sdiff_le_card_sdiff_iff`

English:
lemma card_sdiff_le_card_sdiff_iff
  statement: #(s \ t) <= #(t \ s) ↔ #s <= #t
  proof: by grind

中文:
引理 card_sdiff_le_card_sdiff_iff
  结论: #(s \ t) <= #(t \ s) ↔ #s <= #t
  证明: by grind
-/
lemma card_sdiff_le_card_sdiff_iff : #(s \ t) <= #(t \ s) ↔ #s <= #t := by grind

/--
lemma `card_sdiff_lt_card_sdiff_iff` / 引理 `card_sdiff_lt_card_sdiff_iff`

English:
lemma card_sdiff_lt_card_sdiff_iff
  statement: #(s \ t) < #(t \ s) ↔ #s < #t
  proof: by grind

中文:
引理 card_sdiff_lt_card_sdiff_iff
  结论: #(s \ t) < #(t \ s) ↔ #s < #t
  证明: by grind
-/
lemma card_sdiff_lt_card_sdiff_iff : #(s \ t) < #(t \ s) ↔ #s < #t := by grind

/--
lemma `card_sdiff_eq_card_sdiff_iff` / 引理 `card_sdiff_eq_card_sdiff_iff`

English:
lemma card_sdiff_eq_card_sdiff_iff
  statement: #(s \ t) = #(t \ s) ↔ #s = #t
  proof: by grind

alias ⟨_, card_sdiff_comm⟩ := card_sdiff_eq_card_sdiff_iff

中文:
引理 card_sdiff_eq_card_sdiff_iff
  结论: #(s \ t) = #(t \ s) ↔ #s = #t
  证明: by grind

alias ⟨_, card_sdiff_comm⟩ := card_sdiff_eq_card_sdiff_iff
-/
lemma card_sdiff_eq_card_sdiff_iff : #(s \ t) = #(t \ s) ↔ #s = #t := by grind

alias ⟨_, card_sdiff_comm⟩ := card_sdiff_eq_card_sdiff_iff

/--
theorem `inter_nonempty_of_card_lt_card_add_card` / 定理 `inter_nonempty_of_card_lt_card_add_card`

English:
theorem inter_nonempty_of_card_lt_card_add_card
  statement: (hts : t subseteq s) (hus : u subseteq s)
  proof: by
  contrapose! hstu
  calc
    _ = #(t union u) := by simp [← card_union_add_card_inter, hstu]
    _ <= #s := by gcongr; exact union_subset hts hus

中文:
定理 inter_nonempty_of_card_lt_card_add_card
  结论: (hts : t subseteq s) (hus : u subseteq s)
  证明: by
  contrapose! hstu
  calc
    _ = #(t union u) := by simp [← card_union_add_card_inter, hstu]
    _ <= #s := by gcongr; exact union_subset hts hus

Depends on / 依赖: card_union_add_card_inter, contrapose, union_subset
-/
theorem inter_nonempty_of_card_lt_card_add_card (hts : t subseteq s) (hus : u subseteq s)
    (hstu : #s < #t + #u) : (t inter u).Nonempty := by
  contrapose! hstu
  calc
    _ = #(t union u) := by simp [← card_union_add_card_inter, hstu]
    _ <= #s := by gcongr; exact union_subset hts hus

end Lattice

/--
theorem `card_filter_add_card_filter_not` / 定理 `card_filter_add_card_filter_not`

English:
theorem card_filter_add_card_filter_not
  proof: by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _)]; rw [filter_union_filter_not_eq]

中文:
定理 card_filter_add_card_filter_not
  证明: by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _)]; rw [filter_union_filter_not_eq]

Depends on / 依赖: card_union_of_disjoint, classical, disjoint_filter_filter_not, filter_union_filter_not_eq, not_le, psub_eq_none, psub_eq_sub, split_ifs
-/
theorem card_filter_add_card_filter_not
    (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] :
    #(s.filter p) + #(s.filter fun a => ¬ p a) = #s := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _)]; rw [filter_union_filter_not_eq]

/--
lemma `exists_subsuperset_card_eq` / 引理 `exists_subsuperset_card_eq`

English:
lemma exists_subsuperset_card_eq
  given: (hst : s subseteq t) (hsn : #s <= n) (hnt : n <= #t)
  proof: by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by grind
  exact ⟨u.erase a, by grind⟩

中文:
引理 存在_subsuperset_card_eq
  条件: (hst : s subseteq t) (hsn : #s <= n) (hnt : n <= #t)
  证明: by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by grind
  exact ⟨u.erase a, by grind⟩

Depends on / 依赖: Nat.decreasingInduction, Nonempty, classical, decreasingInduction, u.erase
-/
lemma exists_subsuperset_card_eq (hst : s subseteq t) (hsn : #s <= n) (hnt : n <= #t) :
    exists u, s subseteq u ∧ u subseteq t ∧ #u = n := by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by grind
  exact ⟨u.erase a, by grind⟩

/--
lemma `exists_subset_card_eq` / 引理 `exists_subset_card_eq`

English:
lemma exists_subset_card_eq
  given: (hns : n <= #s)
  statement: exists t subseteq s, #t = n
  proof: by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

中文:
引理 存在_subset_card_eq
  条件: (hns : n <= #s)
  结论: 存在 t subseteq s, #t = n
  证明: by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

Depends on / 依赖: empty_subset, exists_subsuperset_card_eq, s.empty_subset
-/
lemma exists_subset_card_eq (hns : n <= #s) : exists t subseteq s, #t = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

/--
theorem `le_card_iff_exists_subset_card` / 定理 `le_card_iff_exists_subset_card`

English:
theorem le_card_iff_exists_subset_card
  statement: n <= #s ↔ exists t subseteq s, #t = n
  proof: by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h

中文:
定理 le_card_iff_存在_subset_card
  结论: n <= #s ↔ 存在 t subseteq s, #t = n
  证明: by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h

Depends on / 依赖: card_le_card, exists_subset_card_eq
-/
theorem le_card_iff_exists_subset_card : n <= #s ↔ exists t subseteq s, #t = n := by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h

/--
theorem `exists_subset_or_subset_of_two_mul_lt_card` / 定理 `exists_subset_or_subset_of_two_mul_lt_card`

English:
theorem exists_subset_or_subset_of_two_mul_lt_card
  statement: [DecidableEq α] {X Y : Finset α} {n : Nat}
  proof: by
  grind =>
    have : #(X union Y) = #X + #(Y \ X)
    finish

中文:
定理 存在_subset_or_subset_of_two_mul_lt_card
  结论: [DecidableEq α] {X Y : 有限集 α} {n : 自然数}
  证明: by
  grind =>
    have : #(X union Y) = #X + #(Y \ X)
    finish

Depends on / 依赖: finish
-/
theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : Nat}
    (hXY : 2 * n < #(X union Y)) : exists C : Finset α, n < #C ∧ (C subseteq X ∨ C subseteq Y) := by
  grind =>
    have : #(X union Y) = #X + #(Y \ X)
    finish



/--
theorem `card_eq_one` / 定理 `card_eq_one`

English:
theorem card_eq_one
  statement: #s = 1 ↔ exists a, s = {a}
  proof: by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]

中文:
定理 card_eq_one
  结论: #s = 1 ↔ 存在 a, s = {a}
  证明: by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]

Depends on / 依赖: Finset, Finset.card, Multiset, Multiset.card_eq_one, card_eq_one, singleton_val, val_inj
-/
theorem card_eq_one : #s = 1 ↔ exists a, s = {a} := by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]

/--
theorem `card_eq_one_iff_existsUnique` / 定理 `card_eq_one_iff_existsUnique`

English:
theorem card_eq_one_iff_existsUnique
  statement: #s = 1 ↔ exists! a, a in s
  proof: by
  simp [card_eq_one, Finset.singleton_iff_unique_mem]

中文:
定理 card_eq_one_iff_存在Unique
  结论: #s = 1 ↔ 存在! a, a in s
  证明: by
  simp [card_eq_one, Finset.singleton_iff_unique_mem]

Depends on / 依赖: Finset, Finset.singleton_iff_unique_mem, card_eq_one, singleton_iff_unique_mem
-/
theorem card_eq_one_iff_existsUnique : #s = 1 ↔ exists! a, a in s := by
  simp [card_eq_one, Finset.singleton_iff_unique_mem]

/--
theorem `exists_eq_insert_iff` / 定理 `exists_eq_insert_iff`

English:
theorem exists_eq_insert_iff
  given: [DecidableEq α]
  proof: by
  constructor
  · grind
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : exists a, t \ s = {a} := card_eq_one.mp (by grind)
    grind =>
      have : a in t \ s
      have h : insert a s subseteq t
      have := eq_of_subset_of_card_le h
      instantiate

中文:
定理 存在_eq_insert_iff
  条件: [DecidableEq α]
  证明: by
  constructor
  · grind
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : exists a, t \ s = {a} := card_eq_one.mp (by grind)
    grind =>
      have : a in t \ s
      have h : insert a s subseteq t
      have := eq_of_subset_of_card_le h
      instantiate

Depends on / 依赖: card_eq_one, card_eq_one.mp, eq_of_subset_of_card_le, insert, instantiate, subseteq
-/
theorem exists_eq_insert_iff [DecidableEq α] :
    (exists a ∉ s, insert a s = t) ↔ s subseteq t ∧ #s + 1 = #t := by
  constructor
  · grind
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : exists a, t \ s = {a} := card_eq_one.mp (by grind)
    grind =>
      have : a in t \ s
      have h : insert a s subseteq t
      have := eq_of_subset_of_card_le h
      instantiate

/--
theorem `card_le_one` / 定理 `card_le_one`

English:
theorem card_le_one
  statement: #s <= 1 ↔ forall a in s, forall b in s, a = b
  proof: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).ge_iff_eq'.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · grind
  · exact fun h => ⟨x, by grind⟩

中文:
定理 card_le_one
  结论: #s <= 1 ↔ 对任意 a in s, 对任意 b in s, a = b
  证明: by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).ge_iff_eq'.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · grind
  · exact fun h => ⟨x, by grind⟩

Depends on / 依赖: Nat.succ_le_of_lt, card_eq_one, card_eq_one.trans, card_pos, eq_empty_or_nonempty, ge_iff_eq, s.eq_empty_or_nonempty, succ_le_of_lt
-/
theorem card_le_one : #s <= 1 ↔ forall a in s, forall b in s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).ge_iff_eq'.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · grind
  · exact fun h => ⟨x, by grind⟩

/--
theorem `card_le_one_iff` / 定理 `card_le_one_iff`

English:
theorem card_le_one_iff
  statement: #s <= 1 ↔ forall {a b}, a in s -> b in s -> a = b
  proof: by
  grind [card_le_one]

中文:
定理 card_le_one_iff
  结论: #s <= 1 ↔ 对任意 {a b}, a in s -> b in s -> a = b
  证明: by
  grind [card_le_one]

Depends on / 依赖: card_le_one
-/
theorem card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s -> b in s -> a = b := by
  grind [card_le_one]

/--
theorem `card_le_one_iff_subsingleton_coe` / 定理 `card_le_one_iff_subsingleton_coe`

English:
theorem card_le_one_iff_subsingleton_coe
  statement: #s <= 1 ↔ Subsingleton (s : Type _)
  proof: card_le_one.trans (s : Set α).subsingleton_coe.symm

中文:
定理 card_le_one_iff_subsingleton_coe
  结论: #s <= 1 ↔ 子单例 (s : 类型 _)
  证明: card_le_one.trans (s : Set α).subsingleton_coe.symm

Depends on / 依赖: card_le_one, card_le_one.trans, subsingleton_coe, subsingleton_coe.symm
-/
theorem card_le_one_iff_subsingleton_coe : #s <= 1 ↔ Subsingleton (s : Type _) :=
  card_le_one.trans (s : Set α).subsingleton_coe.symm

/--
theorem `card_le_one_iff_subsingleton` / 定理 `card_le_one_iff_subsingleton`

English:
theorem card_le_one_iff_subsingleton
  statement: #s <= 1 ↔ (s : Set α).Subsingleton
  proof: by
  rw [card_le_one_iff_subsingleton_coe]; rw [← Set.subsingleton_coe]; rw [SetLike.coe_sort_coe]

中文:
定理 card_le_one_iff_subsingleton
  结论: #s <= 1 ↔ (s : 集合 α).子单例
  证明: by
  rw [card_le_one_iff_subsingleton_coe]; rw [← Set.subsingleton_coe]; rw [SetLike.coe_sort_coe]

Depends on / 依赖: Set.subsingleton_coe, SetLike, SetLike.coe_sort_coe, card_le_one_iff_subsingleton_coe, coe_sort_coe, subsingleton_coe
-/
theorem card_le_one_iff_subsingleton : #s <= 1 ↔ (s : Set α).Subsingleton := by
  rw [card_le_one_iff_subsingleton_coe]; rw [← Set.subsingleton_coe]; rw [SetLike.coe_sort_coe]

/--
theorem `card_le_one_iff_subset_singleton` / 定理 `card_le_one_iff_subset_singleton`

English:
theorem card_le_one_iff_subset_singleton
  given: [Nonempty α]
  statement: #s <= 1 ↔ exists x : α, s subseteq {x}
  proof: by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx

中文:
定理 card_le_one_iff_subset_singleton
  条件: [非空 α]
  结论: #s <= 1 ↔ 存在 x : α, s subseteq {x}
  证明: by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, card_le_card, card_le_one, card_singleton, empty_subset, eq_empty_or_nonempty, mem_singleton, s.eq_empty_or_nonempty
-/
theorem card_le_one_iff_subset_singleton [Nonempty α] : #s <= 1 ↔ exists x : α, s subseteq {x} := by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx

/--
lemma `exists_mem_ne` / 引理 `exists_mem_ne`

English:
lemma exists_mem_ne
  given: (hs : 1 < #s) (a : α)
  statement: exists b in s, b != a
  proof: by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_ge (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

中文:
引理 存在_mem_ne
  条件: (hs : 1 < #s) (a : α)
  结论: 存在 b in s, b != a
  证明: by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_ge (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

Depends on / 依赖: Nonempty, card_le_one_iff_subset_singleton, hs.not_ge, not_ge, subset_singleton_iff
-/
lemma exists_mem_ne (hs : 1 < #s) (a : α) : exists b in s, b != a := by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_ge (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

/--
theorem `card_le_one_of_subsingleton` / 定理 `card_le_one_of_subsingleton`

English:
theorem card_le_one_of_subsingleton
  given: [Subsingleton α] (s : Finset α)
  statement: #s <= 1
  proof: Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

中文:
定理 card_le_one_of_subsingleton
  条件: [子单例 α] (s : 有限集 α)
  结论: #s <= 1
  证明: Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

Depends on / 依赖: Finset, Finset.card_le_one_iff, Subsingleton, Subsingleton.elim, card_le_one_iff
-/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : #s <= 1 :=
  Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

/--
theorem `one_lt_card` / 定理 `one_lt_card`

English:
theorem one_lt_card
  statement: 1 < #s ↔ exists a in s, exists b in s, a != b
  proof: by
  contrapose!; exact card_le_one

中文:
定理 one_lt_card
  结论: 1 < #s ↔ 存在 a in s, 存在 b in s, a != b
  证明: by
  contrapose!; exact card_le_one

Depends on / 依赖: card_le_one, contrapose
-/
theorem one_lt_card : 1 < #s ↔ exists a in s, exists b in s, a != b := by
  contrapose!; exact card_le_one

/--
theorem `one_lt_card_iff` / 定理 `one_lt_card_iff`

English:
theorem one_lt_card_iff
  statement: 1 < #s ↔ exists a b, a in s ∧ b in s ∧ a != b
  proof: by
  rw [one_lt_card]
  simp only [exists_and_left]

中文:
定理 one_lt_card_iff
  结论: 1 < #s ↔ 存在 a b, a in s ∧ b in s ∧ a != b
  证明: by
  rw [one_lt_card]
  simp only [exists_and_left]

Depends on / 依赖: exists_and_left, one_lt_card
-/
theorem one_lt_card_iff : 1 < #s ↔ exists a b, a in s ∧ b in s ∧ a != b := by
  rw [one_lt_card]
  simp only [exists_and_left]

/--
theorem `one_lt_card_iff_nontrivial` / 定理 `one_lt_card_iff_nontrivial`

English:
theorem one_lt_card_iff_nontrivial
  statement: 1 < #s ↔ s.Nontrivial
  proof: by
  rw [← not_iff_not]; rw [not_lt]; rw [Finset.Nontrivial]; rw [← Set.nontrivial_coe_sort]; rw [not_nontrivial_iff_subsingleton]; rw [card_le_one_iff_subsingleton_coe]; rw [coe_sort_coe]

中文:
定理 one_lt_card_iff_nontrivial
  结论: 1 < #s ↔ s.非平凡
  证明: by
  rw [← not_iff_not]; rw [not_lt]; rw [Finset.Nontrivial]; rw [← Set.nontrivial_coe_sort]; rw [not_nontrivial_iff_subsingleton]; rw [card_le_one_iff_subsingleton_coe]; rw [coe_sort_coe]

Depends on / 依赖: Finset, Finset.Nontrivial, Nontrivial, Set.nontrivial_coe_sort, card_le_one_iff_subsingleton_coe, coe_sort_coe, nontrivial_coe_sort, not_iff_not, not_lt, not_nontrivial_iff_subsingleton
-/
theorem one_lt_card_iff_nontrivial : 1 < #s ↔ s.Nontrivial := by
  rw [← not_iff_not]; rw [not_lt]; rw [Finset.Nontrivial]; rw [← Set.nontrivial_coe_sort]; rw [not_nontrivial_iff_subsingleton]; rw [card_le_one_iff_subsingleton_coe]; rw [coe_sort_coe]

/--
theorem `existsUnique_notMem_image_of_injOn_of_card_eq_add_one` / 定理 `existsUnique_notMem_image_of_injOn_of_card_eq_add_one`

English:
theorem existsUnique_notMem_image_of_injOn_of_card_eq_add_one
  proof: by
  have : #(t \ s.image f) = 1 := by
    grind [card_sdiff_of_subset hf'.finsetImage_subset, card_image_of_injOn hf]
  simpa [card_eq_one_iff_existsUnique] using this

中文:
定理 存在Unique_notMem_image_of_injOn_of_card_eq_add_one
  证明: by
  have : #(t \ s.image f) = 1 := by
    grind [card_sdiff_of_subset hf'.finsetImage_subset, card_image_of_injOn hf]
  simpa [card_eq_one_iff_existsUnique] using this

Depends on / 依赖: card_eq_one_iff_existsUnique, card_image_of_injOn, card_sdiff_of_subset, finsetImage_subset, s.image
-/
theorem existsUnique_notMem_image_of_injOn_of_card_eq_add_one
    {t : Finset β} [DecidableEq β]
    (hf : Set.InjOn f s) (hf' : Set.MapsTo f s t) (h : #t = #s + 1) :
    exists! x, x in t ∧ x ∉ s.image f := by
  have : #(t \ s.image f) = 1 := by
    grind [card_sdiff_of_subset hf'.finsetImage_subset, card_image_of_injOn hf]
  simpa [card_eq_one_iff_existsUnique] using this

/--
lemma `exists_of_one_lt_card_pi` / 引理 `exists_of_one_lt_card_pi`

English:
lemma exists_of_one_lt_card_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, DecidableEq (α i)]
  proof: by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

中文:
引理 存在_of_one_lt_card_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, DecidableEq (α i)]
  证明: by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

Depends on / 依赖: Function, Function.ne_iff, eq_or_ne, exacts, filter_ssubset, mem_image_of_mem, ne_iff, one_lt_card_iff, simp_rw
-/
lemma exists_of_one_lt_card_pi {ι : Type*} {α : ι -> Type*} [forall i, DecidableEq (α i)]
    {s : Finset (forall i, α i)} (h : 1 < #s) :
    exists i, 1 < #(s.image (· i)) ∧ forall ai, s.filter (· i = ai) ⊂ s := by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

/--
theorem `card_eq_succ_iff_cons` / 定理 `card_eq_succ_iff_cons`

English:
theorem card_eq_succ_iff_cons
  proof: ⟨cons_induction_on s (by simp) fun a s _ _ _ => ⟨a, s, by simp_all⟩,
   fun ⟨a, t, _, hs, _⟩ => by simpa [← hs]⟩

中文:
定理 card_eq_succ_iff_cons
  证明: ⟨cons_induction_on s (by simp) fun a s _ _ _ => ⟨a, s, by simp_all⟩,
   fun ⟨a, t, _, hs, _⟩ => by simpa [← hs]⟩

Depends on / 依赖: cons_induction_on
-/
theorem card_eq_succ_iff_cons :
    #s = n + 1 ↔ exists a t, exists (h : a ∉ t), cons a t h = s ∧ #t = n :=
  ⟨cons_induction_on s (by simp) fun a s _ _ _ => ⟨a, s, by simp_all⟩,
   fun ⟨a, t, _, hs, _⟩ => by simpa [← hs]⟩

section DecidableEq
variable [DecidableEq α]

/--
theorem `card_eq_succ` / 定理 `card_eq_succ`

English:
theorem card_eq_succ
  statement: #s = n + 1 ↔ exists a t, a ∉ t ∧ insert a t = s ∧ #t = n
  proof: ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < #s)
    ⟨a, s.erase a, s.notMem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_notMem hat⟩

中文:
定理 card_eq_succ
  结论: #s = n + 1 ↔ 存在 a t, a ∉ t ∧ insert a t = s ∧ #t = n
  证明: ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < #s)
    ⟨a, s.erase a, s.notMem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_notMem hat⟩

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.zero_lt_succ, add_sub_cancel_right, card_erase_of_mem, card_insert_of_notMem, card_pos, card_pos.mp, h.symm, insert_erase, n_eq, notMem_erase, s.erase, s.notMem_erase, s_eq, zero_lt_succ
-/
theorem card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ insert a t = s ∧ #t = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < #s)
    ⟨a, s.erase a, s.notMem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_notMem hat⟩

/--
theorem `card_eq_two` / 定理 `card_eq_two`

English:
theorem card_eq_two
  statement: #s = 2 ↔ exists x y, x != y ∧ s = {x, y}
  proof: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_one]
  · grind

中文:
定理 card_eq_two
  结论: #s = 2 ↔ 存在 x y, x != y ∧ s = {x, y}
  证明: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_one]
  · grind

Depends on / 依赖: card_eq_one, card_eq_succ
-/
theorem card_eq_two : #s = 2 ↔ exists x y, x != y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_one]
  · grind

/--
theorem `card_eq_three` / 定理 `card_eq_three`

English:
theorem card_eq_three
  statement: #s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
  proof: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_two]
  · grind

中文:
定理 card_eq_three
  结论: #s = 3 ↔ 存在 x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z}
  证明: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_two]
  · grind

Depends on / 依赖: card_eq_succ, card_eq_two
-/
theorem card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x != z ∧ y != z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_two]
  · grind

/--
theorem `card_eq_four` / 定理 `card_eq_four`

English:
theorem card_eq_four
  statement: #s = 4 ↔
  proof: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_three]
  · grind

中文:
定理 card_eq_four
  结论: #s = 4 ↔
  证明: by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_three]
  · grind

Depends on / 依赖: card_eq_succ, card_eq_three
-/
theorem card_eq_four : #s = 4 ↔
    exists x y z w, x != y ∧ x != z ∧ x != w ∧ y != z ∧ y != w ∧ z != w ∧ s = {x, y, z, w} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_three]
  · grind

end DecidableEq

/--
theorem `two_lt_card_iff` / 定理 `two_lt_card_iff`

English:
theorem two_lt_card_iff
  statement: 2 < #s ↔ exists a b c, a in s ∧ b in s ∧ c in s ∧ a != b ∧ a != c ∧ b != c
  proof: by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩

中文:
定理 two_lt_card_iff
  结论: 2 < #s ↔ 存在 a b c, a in s ∧ b in s ∧ c in s ∧ a != b ∧ a != c ∧ b != c
  证明: by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩

Depends on / 依赖: Finset, card_eq_three, classical, exists_and_left, exists_comm, insert_subset_iff, le_card_iff_exists_subset_card, lt_iff_add_one_le, reduceAdd, simp_rw
-/
theorem two_lt_card_iff : 2 < #s ↔ exists a b c, a in s ∧ b in s ∧ c in s ∧ a != b ∧ a != c ∧ b != c := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩

/--
theorem `two_lt_card` / 定理 `two_lt_card`

English:
theorem two_lt_card
  statement: 2 < #s ↔ exists a in s, exists b in s, exists c in s, a != b ∧ a != c ∧ b != c
  proof: by
  simp_rw [two_lt_card_iff, exists_and_left]

中文:
定理 two_lt_card
  结论: 2 < #s ↔ 存在 a in s, 存在 b in s, 存在 c in s, a != b ∧ a != c ∧ b != c
  证明: by
  simp_rw [two_lt_card_iff, exists_and_left]

Depends on / 依赖: exists_and_left, simp_rw, two_lt_card_iff
-/
theorem two_lt_card : 2 < #s ↔ exists a in s, exists b in s, exists c in s, a != b ∧ a != c ∧ b != c := by
  simp_rw [two_lt_card_iff, exists_and_left]

/--
theorem `three_lt_card_iff` / 定理 `three_lt_card_iff`

English:
theorem three_lt_card_iff
  statement: 3 < #s ↔
  proof: by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_four,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, d, t, hsub, hab, hac, had, hbc, hbd, hcd, rfl⟩
      exact ⟨a, b, c, d, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨a, b, c, d, {a, b, c, d}, by simp_all [insert_subset_iff]⟩

中文:
定理 three_lt_card_iff
  结论: 3 < #s ↔
  证明: by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_four,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, d, t, hsub, hab, hac, had, hbc, hbd, hcd, rfl⟩
      exact ⟨a, b, c, d, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨a, b, c, d, {a, b, c, d}, by simp_all [insert_subset_iff]⟩

Depends on / 依赖: Finset, card_eq_four, classical, exists_and_left, exists_comm, insert_subset_iff, le_card_iff_exists_subset_card, lt_iff_add_one_le, reduceAdd, simp_rw
-/
theorem three_lt_card_iff : 3 < #s ↔
    exists a b c d, a in s ∧ b in s ∧ c in s ∧ d in s ∧
    a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_four,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, d, t, hsub, hab, hac, had, hbc, hbd, hcd, rfl⟩
      exact ⟨a, b, c, d, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨a, b, c, d, {a, b, c, d}, by simp_all [insert_subset_iff]⟩

/--
theorem `three_lt_card` / 定理 `three_lt_card`

English:
theorem three_lt_card
  statement: 3 < #s ↔ exists a in s, exists b in s, exists c in s, exists d in s,
  proof: by
  simp_rw [three_lt_card_iff, exists_and_left]

中文:
定理 three_lt_card
  结论: 3 < #s ↔ 存在 a in s, 存在 b in s, 存在 c in s, 存在 d in s,
  证明: by
  simp_rw [three_lt_card_iff, exists_and_left]

Depends on / 依赖: exists_and_left, simp_rw, three_lt_card_iff
-/
theorem three_lt_card : 3 < #s ↔ exists a in s, exists b in s, exists c in s, exists d in s,
    a != b ∧ a != c ∧ a != d ∧ b != c ∧ b != d ∧ c != d := by
  simp_rw [three_lt_card_iff, exists_and_left]

/-! ### Inductions -/


/--
Definition of `strongInduction` / `strongInduction` 的定义

English:
definition strongInduction
  signature: {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p t) -> p s)
  body: card_lt_card h
      strongInduction H t
  termination_by s => #s

中文:
定义 strongInduction
  签名: {p : 有限集 α -> 类型层*} (H : 对任意 s, (对任意 t ⊂ s, p t) -> p s)
  定义体: card_lt_card h
      strongInduction H t
  termination_by s => #s

Depends on / 依赖: card_lt_card
-/
def strongInduction {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p t) -> p s) :
    forall s : Finset α, p s
  | s =>
    H s fun t h =>
      have : #t < #s := card_lt_card h
      strongInduction H t
  termination_by s => #s

/--
theorem `strongInduction_eq` / 定理 `strongInduction_eq`

English:
theorem strongInduction_eq
  statement: {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p t) -> p s)
  proof: by
  rw [strongInduction]

中文:
定理 strongInduction_eq
  结论: {p : 有限集 α -> 类型层*} (H : 对任意 s, (对任意 t ⊂ s, p t) -> p s)
  证明: by
  rw [strongInduction]

Depends on / 依赖: strongInduction
-/
theorem strongInduction_eq {p : Finset α -> Sort*} (H : forall s, (forall t ⊂ s, p t) -> p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
/--
Definition of `strongInductionOn` / `strongInductionOn` 的定义

English:
definition strongInductionOn
  signature: {p : Finset α -> Sort*} (s : Finset α)
  body: fun H => strongInduction H s

中文:
定义 strongInductionOn
  签名: {p : 有限集 α -> 类型层*} (s : 有限集 α)
  定义体: fun H => strongInduction H s

Depends on / 依赖: strongInduction
-/
def strongInductionOn {p : Finset α -> Sort*} (s : Finset α) :
    (forall s, (forall t ⊂ s, p t) -> p s) -> p s := fun H => strongInduction H s

/--
theorem `strongInductionOn_eq` / 定理 `strongInductionOn_eq`

English:
theorem strongInductionOn_eq
  statement: {p : Finset α -> Sort*} (s : Finset α)
  proof: by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]

中文:
定理 strongInductionOn_eq
  结论: {p : 有限集 α -> 类型层*} (s : 有限集 α)
  证明: by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]

Depends on / 依赖: strongInduction, strongInductionOn
-/
theorem strongInductionOn_eq {p : Finset α -> Sort*} (s : Finset α)
    (H : forall s, (forall t ⊂ s, p t) -> p s) :
    s.strongInductionOn H = H s fun t _ => t.strongInductionOn H := by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]
/--
theorem `case_strong_induction_on` / 定理 `case_strong_induction_on`

English:
theorem case_strong_induction_on
  statement: [DecidableEq α] {p : Finset α -> Prop} (s : Finset α) (h₀ : p ∅)
  proof: Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

中文:
定理 case_strong_induction_on
  结论: [DecidableEq α] {p : 有限集 α -> 命题} (s : 有限集 α) (h₀ : p ∅)
  证明: Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

Depends on / 依赖: Finset, Finset.induction_on, Finset.strongInductionOn, induction_on, lt_of_le_of_lt, ssubset_insert, strongInductionOn
-/
theorem case_strong_induction_on [DecidableEq α] {p : Finset α -> Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : forall a s, a ∉ s -> (forall t subseteq s, p t) -> p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

/-- Suppose that, given objects defined on all nonempty strict subsets of any nontrivial finset `s`,
one knows how to define an object on `s`. Then one can inductively define an object on all finsets,
starting from singletons and iterating.

TODO: Currently this can only be used to prove properties.
Replace `Finset.Nonempty.exists_eq_singleton_or_nontrivial` with computational content
in order to let `p` be `Sort`-valued. -/
@[elab_as_elim]
/--
lemma `Nonempty.strong_induction` / 引理 `Nonempty.strong_induction`

English:
lemma Nonempty.strong_induction
  statement: {p : forall s, s.Nonempty -> Prop}
  proof: hs.exists_eq_singleton_or_nontrivial
    · exact h₀ _
    · refine h₁ hs fun t ht hts => ?_
      have := card_lt_card hts
      exact ht.strong_induction h₀ h₁
termination_by s => #s

中文:
引理 非空.strong_induction
  结论: {p : 对任意 s, s.非空 -> 命题}
  证明: hs.exists_eq_singleton_or_nontrivial
    · exact h₀ _
    · refine h₁ hs fun t ht hts => ?_
      have := card_lt_card hts
      exact ht.strong_induction h₀ h₁
termination_by s => #s
-/
protected lemma Nonempty.strong_induction {p : forall s, s.Nonempty -> Prop}
    (h₀ : forall a, p {a} (singleton_nonempty _))
    (h₁ : forall ⦃s⦄ (hs : s.Nontrivial), (forall t ht, t ⊂ s -> p t ht) -> p s hs.nonempty) :
    forall ⦃s : Finset α⦄ (hs), p s hs
  | s, hs => by
    obtain ⟨a, rfl⟩ | hs := hs.exists_eq_singleton_or_nontrivial
    · exact h₀ _
    · refine h₁ hs fun t ht hts => ?_
      have := card_lt_card hts
      exact ht.strong_induction h₀ h₁
termination_by s => #s

/--
Definition of `strongDownwardInduction` / `strongDownwardInduction` 的定义

English:
definition strongDownwardInduction
  signature: {p : Finset α -> Sort*} {n : Nat}
  body: Finset.card_lt_card h
      have : n - #t < n - #s := by lia
      strongDownwardInduction H t ht
  termination_by s => n - #s

中文:
定义 strongDownwardInduction
  签名: {p : 有限集 α -> 类型层*} {n : 自然数}
  定义体: Finset.card_lt_card h
      have : n - #t < n - #s := by lia
      strongDownwardInduction H t ht
  termination_by s => n - #s

Depends on / 依赖: Finset, Finset.card_lt_card, card_lt_card
-/
def strongDownwardInduction {p : Finset α -> Sort*} {n : Nat}
    (H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁) :
    forall s : Finset α, #s <= n -> p s
  | s =>
    H s fun {t} ht h =>
      have := Finset.card_lt_card h
      have : n - #t < n - #s := by lia
      strongDownwardInduction H t ht
  termination_by s => n - #s

/--
theorem `strongDownwardInduction_eq` / 定理 `strongDownwardInduction_eq`

English:
theorem strongDownwardInduction_eq
  statement: {p : Finset α -> Sort*}
  proof: by
  rw [strongDownwardInduction]

中文:
定理 strongDownwardInduction_eq
  结论: {p : 有限集 α -> 类型层*}
  证明: by
  rw [strongDownwardInduction]

Depends on / 依赖: strongDownwardInduction
-/
theorem strongDownwardInduction_eq {p : Finset α -> Sort*}
    (H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H t ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
/--
Definition of `strongDownwardInductionOn` / `strongDownwardInductionOn` 的定义

English:
definition strongDownwardInductionOn
  signature: {p : Finset α -> Sort*} (s : Finset α)
  body: strongDownwardInduction H s

中文:
定义 strongDownwardInductionOn
  签名: {p : 有限集 α -> 类型层*} (s : 有限集 α)
  定义体: strongDownwardInduction H s

Depends on / 依赖: strongDownwardInduction
-/
def strongDownwardInductionOn {p : Finset α -> Sort*} (s : Finset α)
    (H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁) :
    #s <= n -> p s :=
  strongDownwardInduction H s

/--
theorem `strongDownwardInductionOn_eq` / 定理 `strongDownwardInductionOn_eq`

English:
theorem strongDownwardInductionOn_eq
  statement: {p : Finset α -> Sort*} (s : Finset α)
  proof: by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

中文:
定理 strongDownwardInductionOn_eq
  结论: {p : 有限集 α -> 类型层*} (s : 有限集 α)
  证明: by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

Depends on / 依赖: strongDownwardInduction, strongDownwardInductionOn
-/
theorem strongDownwardInductionOn_eq {p : Finset α -> Sort*} (s : Finset α)
    (H : forall t₁, (forall {t₂ : Finset α}, #t₂ <= n -> t₁ ⊂ t₂ -> p t₂) -> #t₁ <= n -> p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

/--
theorem `lt_wf` / 定理 `lt_wf`

English:
theorem lt_wf
  given: {α}
  statement: WellFounded (@LT.lt (Finset α) _)
  proof: have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
Subrelation.wf H InvImage.wf _ (Nat.lt_wfRel).2

中文:
定理 lt_wf
  条件: {α}
  结论: 良基 (@LT.lt (有限集 α) _)
  证明: have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
Subrelation.wf H InvImage.wf _ (Nat.lt_wfRel).2

Depends on / 依赖: Finset, InvImage, InvImage.wf, LT.lt, Nat.lt_wfRel, Subrelation, Subrelation.wf, card_lt_card, lt_wfRel
-/
theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
Subrelation.wf H InvImage.wf _ (Nat.lt_wfRel).2

/--
theorem `eraseInduction` / 定理 `eraseInduction`

English:
theorem eraseInduction
  statement: [DecidableEq α] {p : Finset α -> Prop}
  proof: S.strongInduction fun S ih => H S fun _ hs => ih _ (erase_ssubset hs)

中文:
定理 eraseInduction
  结论: [DecidableEq α] {p : 有限集 α -> 命题}
  证明: S.strongInduction fun S ih => H S fun _ hs => ih _ (erase_ssubset hs)

Depends on / 依赖: S.strongInduction, erase_ssubset, strongInduction
-/
theorem eraseInduction [DecidableEq α] {p : Finset α -> Prop}
    (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α) : p S :=
  S.strongInduction fun S ih => H S fun _ hs => ih _ (erase_ssubset hs)

/--
theorem `image_iterate_stabilises_lt_card` / 定理 `image_iterate_stabilises_lt_card`

English:
theorem image_iterate_stabilises_lt_card
  statement: [DecidableEq α] {f : α -> α} {s : Finset α}
  proof: by
  let g (i : Nat) : Finset α := s.image f^[i]
  have (i : Nat) : 0 < #(g i) := (hs₀.image _).card_pos
have hg : Antitone g := antitone_nat_of_succ_le fun i => by
    simp_rw [g, Function.iterate_succ, ← image_image]
    grw [hs.finsetImage_subset]
  have eq_iff (i j : Nat) : #(g i) - 1 = #(g j) - 1 ↔ g i = g j := by
    wlog hij : j <= i generalizing i j
    · grind
    exact ⟨fun h => eq_of_subset_of_card_le (hg hij) (by grind), by grind⟩
  have hG : Antitone (fun i => #(g i) - 1) := fun i j h => by dsimp; gcongr #?_ - 1; exact hg h
  rcases Nat.stabilises_of_antitone hG (by grind [=_ image_image, iterate_succ']) with ⟨n, hn, hn'⟩
  exact ⟨n, by grind⟩

中文:
定理 image_iterate_stabilises_lt_card
  结论: [DecidableEq α] {f : α -> α} {s : 有限集 α}
  证明: by
  let g (i : Nat) : Finset α := s.image f^[i]
  have (i : Nat) : 0 < #(g i) := (hs₀.image _).card_pos
have hg : Antitone g := antitone_nat_of_succ_le fun i => by
    simp_rw [g, Function.iterate_succ, ← image_image]
    grw [hs.finsetImage_subset]
  have eq_iff (i j : Nat) : #(g i) - 1 = #(g j) - 1 ↔ g i = g j := by
    wlog hij : j <= i generalizing i j
    · grind
    exact ⟨fun h => eq_of_subset_of_card_le (hg hij) (by grind), by grind⟩
  have hG : Antitone (fun i => #(g i) - 1) := fun i j h => by dsimp; gcongr #?_ - 1; exact hg h
  rcases Nat.stabilises_of_antitone hG (by grind [=_ image_image, iterate_succ']) with ⟨n, hn, hn'⟩
  exact ⟨n, by grind⟩

Depends on / 依赖: Antitone, Finset, Function, Function.iterate_succ, antitone_nat_of_succ_le, card_pos, eq_iff, eq_of_subset_of_card_le, finsetImage_subset, generalizing, hs.finsetImage_subset, image_image, iterate_succ, s.image, simp_rw
-/
theorem image_iterate_stabilises_lt_card [DecidableEq α] {f : α -> α} {s : Finset α}
    (hs : Set.MapsTo f s s) (hs₀ : s.Nonempty) :
    exists n < #s, forall m, n <= m -> s.image f^[m] = s.image f^[n] := by
  let g (i : Nat) : Finset α := s.image f^[i]
  have (i : Nat) : 0 < #(g i) := (hs₀.image _).card_pos
have hg : Antitone g := antitone_nat_of_succ_le fun i => by
    simp_rw [g, Function.iterate_succ, ← image_image]
    grw [hs.finsetImage_subset]
  have eq_iff (i j : Nat) : #(g i) - 1 = #(g j) - 1 ↔ g i = g j := by
    wlog hij : j <= i generalizing i j
    · grind
    exact ⟨fun h => eq_of_subset_of_card_le (hg hij) (by grind), by grind⟩
  have hG : Antitone (fun i => #(g i) - 1) := fun i j h => by dsimp; gcongr #?_ - 1; exact hg h
  rcases Nat.stabilises_of_antitone hG (by grind [=_ image_image, iterate_succ']) with ⟨n, hn, hn'⟩
  exact ⟨n, by grind⟩

/--
theorem `image_iterate_stabilises_le_card` / 定理 `image_iterate_stabilises_le_card`

English:
theorem image_iterate_stabilises_le_card
  statement: [DecidableEq α] {f : α -> α} {s : Finset α}
  proof: by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨n, hn', hn⟩ := image_iterate_stabilises_lt_card hs hs₀
  exact ⟨n, hn'.le, hn⟩

中文:
定理 image_iterate_stabilises_le_card
  结论: [DecidableEq α] {f : α -> α} {s : 有限集 α}
  证明: by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨n, hn', hn⟩ := image_iterate_stabilises_lt_card hs hs₀
  exact ⟨n, hn'.le, hn⟩

Depends on / 依赖: eq_empty_or_nonempty, image_iterate_stabilises_lt_card, s.eq_empty_or_nonempty
-/
theorem image_iterate_stabilises_le_card [DecidableEq α] {f : α -> α} {s : Finset α}
    (hs : Set.MapsTo f s s) :
    exists n <= #s, forall m, n <= m -> s.image f^[m] = s.image f^[n] := by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨n, hn', hn⟩ := image_iterate_stabilises_lt_card hs hs₀
  exact ⟨n, hn'.le, hn⟩

end Finset
