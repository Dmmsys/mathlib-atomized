/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.AddSub

/-!
# Repeating elements in multisets

## Main definitions

* `replicate n a` is the multiset containing only `a` with multiplicity `n`

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.replicate` -/

/--
Definition of `replicate` / `replicate` 的定义

English:
definition replicate
  signature: (n : Nat) (a : α)
  body: List.replicate n a

中文:
定义 replicate
  签名: (n : 自然数) (a : α)
  定义体: List.replicate n a

Depends on / 依赖: List.replicate, replicate
-/
def replicate (n : Nat) (a : α) : Multiset α :=
  List.replicate n a

/--
theorem `coe_replicate` / 定理 `coe_replicate`

English:
theorem coe_replicate
  given: (n : Nat) (a : α)
  statement: (List.replicate n a : Multiset α) = replicate n a
  proof: rfl

中文:
定理 coe_replicate
  条件: (n : 自然数) (a : α)
  结论: (List.replicate n a : Multiset α) = replicate n a
  证明: rfl

Depends on / 依赖: Computation, Computation.exists_of_mem_map, Or.inl, _tail, eq_or_mem_iff_mem, exists_of_mem_map, generalizing, injection, mem_of_mem_tail
-/
theorem coe_replicate (n : Nat) (a : α) : (List.replicate n a : Multiset α) = replicate n a := rfl

/--
theorem `replicate_zero` / 定理 `replicate_zero`

English:
theorem replicate_zero
  given: (a : α)
  statement: replicate 0 a = 0
  proof: rfl

中文:
定理 replicate_zero
  条件: (a : α)
  结论: replicate 0 a = 0
  证明: rfl
-/
@[simp] theorem replicate_zero (a : α) : replicate 0 a = 0 := rfl

/--
theorem `replicate_succ` / 定理 `replicate_succ`

English:
theorem replicate_succ
  given: (a : α) (n)
  statement: replicate (n + 1) a = a ::ₘ replicate n a
  proof: rfl

中文:
定理 replicate_succ
  条件: (a : α) (n)
  结论: replicate (n + 1) a = a ::ₘ replicate n a
  证明: rfl
-/
@[simp] theorem replicate_succ (a : α) (n) : replicate (n + 1) a = a ::ₘ replicate n a := rfl

/--
theorem `replicate_add` / 定理 `replicate_add`

English:
theorem replicate_add
  given: (m n : Nat) (a : α)
  statement: replicate (m + n) a = replicate m a + replicate n a
  proof: congr_arg _ List.replicate_add ..

中文:
定理 replicate_add
  条件: (m n : 自然数) (a : α)
  结论: replicate (m + n) a = replicate m a + replicate n a
  证明: congr_arg _ List.replicate_add ..

Depends on / 依赖: List.replicate_add, congr_arg, replicate_add
-/
theorem replicate_add (m n : Nat) (a : α) : replicate (m + n) a = replicate m a + replicate n a :=
congr_arg _ List.replicate_add ..

/--
theorem `replicate_one` / 定理 `replicate_one`

English:
theorem replicate_one
  given: (a : α)
  statement: replicate 1 a = {a}
  proof: rfl

中文:
定理 replicate_one
  条件: (a : α)
  结论: replicate 1 a = {a}
  证明: rfl
-/
theorem replicate_one (a : α) : replicate 1 a = {a} := rfl

/--
theorem `card_replicate` / 定理 `card_replicate`

English:
theorem card_replicate
  given: (n) (a : α)
  statement: card (replicate n a) = n
  proof: length_replicate

中文:
定理 card_replicate
  条件: (n) (a : α)
  结论: card (replicate n a) = n
  证明: length_replicate
-/
@[simp] theorem card_replicate (n) (a : α) : card (replicate n a) = n :=
  length_replicate

/--
theorem `mem_replicate` / 定理 `mem_replicate`

English:
theorem mem_replicate
  given: {a b : α} {n : Nat}
  statement: b in replicate n a ↔ n != 0 ∧ b = a
  proof: List.mem_replicate

中文:
定理 mem_replicate
  条件: {a b : α} {n : 自然数}
  结论: b in replicate n a ↔ n != 0 ∧ b = a
  证明: List.mem_replicate

Depends on / 依赖: List.mem_replicate, mem_replicate
-/
theorem mem_replicate {a b : α} {n : Nat} : b in replicate n a ↔ n != 0 ∧ b = a :=
  List.mem_replicate

/--
theorem `eq_of_mem_replicate` / 定理 `eq_of_mem_replicate`

English:
theorem eq_of_mem_replicate
  given: {a b : α} {n}
  statement: b in replicate n a -> b = a
  proof: List.eq_of_mem_replicate

中文:
定理 eq_of_mem_replicate
  条件: {a b : α} {n}
  结论: b in replicate n a -> b = a
  证明: List.eq_of_mem_replicate

Depends on / 依赖: List.eq_of_mem_replicate, eq_of_mem_replicate
-/
theorem eq_of_mem_replicate {a b : α} {n} : b in replicate n a -> b = a :=
  List.eq_of_mem_replicate

/--
theorem `eq_replicate_card` / 定理 `eq_replicate_card`

English:
theorem eq_replicate_card
  given: {a : α} {s : Multiset α}
  statement: s = replicate (card s) a ↔ forall b in s, b = a
  proof: Quot.inductionOn s fun _l => coe_eq_coe.trans perm_replicate.trans eq_replicate_length

alias ⟨_, eq_replicate_of_mem⟩ := eq_replicate_card

中文:
定理 eq_replicate_card
  条件: {a : α} {s : Multiset α}
  结论: s = replicate (card s) a ↔ 对任意 b in s, b = a
  证明: Quot.inductionOn s fun _l => coe_eq_coe.trans perm_replicate.trans eq_replicate_length

alias ⟨_, eq_replicate_of_mem⟩ := eq_replicate_card

Depends on / 依赖: Quot.inductionOn, coe_eq_coe, coe_eq_coe.trans, eq_replicate_length, inductionOn, perm_replicate, perm_replicate.trans
-/
theorem eq_replicate_card {a : α} {s : Multiset α} : s = replicate (card s) a ↔ forall b in s, b = a :=
Quot.inductionOn s fun _l => coe_eq_coe.trans perm_replicate.trans eq_replicate_length

alias ⟨_, eq_replicate_of_mem⟩ := eq_replicate_card

/--
theorem `eq_replicate` / 定理 `eq_replicate`

English:
theorem eq_replicate
  given: {a : α} {n} {s : Multiset α}
  proof: ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun _b => eq_of_mem_replicate⟩,
    fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

中文:
定理 eq_replicate
  条件: {a : α} {n} {s : Multiset α}
  证明: ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun _b => eq_of_mem_replicate⟩,
    fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

Depends on / 依赖: card_replicate, eq_of_mem_replicate, eq_replicate_of_mem, h.symm
-/
theorem eq_replicate {a : α} {n} {s : Multiset α} :
    s = replicate n a ↔ card s = n ∧ forall b in s, b = a :=
  ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun _b => eq_of_mem_replicate⟩,
    fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

/--
theorem `replicate_right_injective` / 定理 `replicate_right_injective`

English:
theorem replicate_right_injective
  given: {n : Nat} (hn : n != 0)
  statement: Injective (@replicate α n)
  proof: fun _ _ h => (eq_replicate.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

中文:
定理 replicate_right_injective
  条件: {n : 自然数} (hn : n != 0)
  结论: Injective (@replicate α n)
  证明: fun _ _ h => (eq_replicate.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

Depends on / 依赖: destruct_eq_think, eq_replicate, mem_replicate
-/
theorem replicate_right_injective {n : Nat} (hn : n != 0) : Injective (@replicate α n) :=
fun _ _ h => (eq_replicate.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

/--
theorem `replicate_right_inj` / 定理 `replicate_right_inj`

English:
theorem replicate_right_inj
  given: {a b : α} {n : Nat} (h : n != 0)
  proof: (replicate_right_injective h).eq_iff

中文:
定理 replicate_right_inj
  条件: {a b : α} {n : 自然数} (h : n != 0)
  证明: (replicate_right_injective h).eq_iff

Depends on / 依赖: destruct_eq_think
-/
@[simp] theorem replicate_right_inj {a b : α} {n : Nat} (h : n != 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective h).eq_iff

/--
theorem `replicate_left_injective` / 定理 `replicate_left_injective`

English:
theorem replicate_left_injective
  given: (a : α)
  statement: Injective (replicate · a)
  proof: LeftInverse.injective (card_replicate · a)

中文:
定理 replicate_left_injective
  条件: (a : α)
  结论: Injective (replicate · a)
  证明: LeftInverse.injective (card_replicate · a)

Depends on / 依赖: Computation, Computation.corec, Computation.eq_of_bisim, Computation.map, LeftInverse, LeftInverse.injective, Seq.destruct, Sum.inl, Sum.inr, card_replicate, destruct, eq_of_bisim, injective, l.reverse, reverse
-/
theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (card_replicate · a)

/--
theorem `replicate_subset_singleton` / 定理 `replicate_subset_singleton`

English:
theorem replicate_subset_singleton
  given: (n : Nat) (a : α)
  statement: replicate n a subseteq {a}
  proof: List.replicate_subset_singleton n a

中文:
定理 replicate_subset_singleton
  条件: (n : 自然数) (a : α)
  结论: replicate n a subseteq {a}
  证明: List.replicate_subset_singleton n a

Depends on / 依赖: List.replicate_subset_singleton, replicate_subset_singleton
-/
theorem replicate_subset_singleton (n : Nat) (a : α) : replicate n a subseteq {a} :=
  List.replicate_subset_singleton n a

/--
theorem `replicate_le_coe` / 定理 `replicate_le_coe`

English:
theorem replicate_le_coe
  given: {a : α} {n} {l : List α}
  statement: replicate n a <= l ↔ List.replicate n a <+ l
  proof: ⟨fun ⟨_l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩

中文:
定理 replicate_le_coe
  条件: {a : α} {n} {l : List α}
  结论: replicate n a <= l ↔ List.replicate n a <+ l
  证明: ⟨fun ⟨_l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩

Depends on / 依赖: Sublist, Sublist.subperm, perm_replicate, subperm
-/
theorem replicate_le_coe {a : α} {n} {l : List α} : replicate n a <= l ↔ List.replicate n a <+ l :=
  ⟨fun ⟨_l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩

/--
theorem `replicate_le_replicate` / 定理 `replicate_le_replicate`

English:
theorem replicate_le_replicate
  given: (a : α) {k n : Nat}
  statement: replicate k a <= replicate n a ↔ k <= n
  proof: _root_.trans (by rw [← replicate_le_coe, coe_replicate]) (List.replicate_sublist_replicate a)

@[gcongr]

中文:
定理 replicate_le_replicate
  条件: (a : α) {k n : 自然数}
  结论: replicate k a <= replicate n a ↔ k <= n
  证明: _root_.trans (by rw [← replicate_le_coe, coe_replicate]) (List.replicate_sublist_replicate a)

@[gcongr]

Depends on / 依赖: List.replicate_sublist_replicate, _root_, _root_.trans, coe_replicate, replicate_le_coe, replicate_sublist_replicate
-/
theorem replicate_le_replicate (a : α) {k n : Nat} : replicate k a <= replicate n a ↔ k <= n :=
  _root_.trans (by rw [← replicate_le_coe, coe_replicate]) (List.replicate_sublist_replicate a)

@[gcongr]
/--
theorem `replicate_mono` / 定理 `replicate_mono`

English:
theorem replicate_mono
  given: (a : α) {k n : Nat} (h : k <= n)
  statement: replicate k a <= replicate n a
  proof: (replicate_le_replicate a).2 h

中文:
定理 replicate_mono
  条件: (a : α) {k n : 自然数} (h : k <= n)
  结论: replicate k a <= replicate n a
  证明: (replicate_le_replicate a).2 h

Depends on / 依赖: replicate_le_replicate
-/
theorem replicate_mono (a : α) {k n : Nat} (h : k <= n) : replicate k a <= replicate n a :=
  (replicate_le_replicate a).2 h

/--
theorem `le_replicate_iff` / 定理 `le_replicate_iff`

English:
theorem le_replicate_iff
  given: {m : Multiset α} {a : α} {n : Nat}
  proof: ⟨fun h => ⟨card m, (card_mono h).trans_eq (card_replicate _ _),
eq_replicate_card.2 fun _ hb => eq_of_mem_replicate subset_of_le h hb⟩,
    fun ⟨_, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩

中文:
定理 le_replicate_iff
  条件: {m : Multiset α} {a : α} {n : 自然数}
  证明: ⟨fun h => ⟨card m, (card_mono h).trans_eq (card_replicate _ _),
eq_replicate_card.2 fun _ hb => eq_of_mem_replicate subset_of_le h hb⟩,
    fun ⟨_, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩

Depends on / 依赖: card_mono, card_replicate, eq_of_mem_replicate, eq_replicate_card, hm.symm, replicate_le_replicate, subset_of_le, trans_eq
-/
theorem le_replicate_iff {m : Multiset α} {a : α} {n : Nat} :
    m <= replicate n a ↔ exists k <= n, m = replicate k a :=
  ⟨fun h => ⟨card m, (card_mono h).trans_eq (card_replicate _ _),
eq_replicate_card.2 fun _ hb => eq_of_mem_replicate subset_of_le h hb⟩,
    fun ⟨_, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩

/--
theorem `lt_replicate_succ` / 定理 `lt_replicate_succ`

English:
theorem lt_replicate_succ
  given: {m : Multiset α} {x : α} {n : Nat}
  proof: by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩

中文:
定理 lt_replicate_succ
  条件: {m : Multiset α} {x : α} {n : 自然数}
  证明: by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩

Depends on / 依赖: cons_le_cons, cons_le_cons_iff, eq_of_mem_replicate, lt_iff_cons_le, mem_cons_self, mem_of_le, replicate_succ
-/
theorem lt_replicate_succ {m : Multiset α} {x : α} {n : Nat} :
    m < replicate (n + 1) x ↔ m <= replicate n x := by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩

/-! ### Multiplicity of an element -/

section

variable [DecidableEq α] {s t u : Multiset α}

@[simp]
/--
theorem `count_replicate_self` / 定理 `count_replicate_self`

English:
theorem count_replicate_self
  given: (a : α) (n : Nat)
  statement: count a (replicate n a) = n
  proof: by
  convert! List.count_replicate_self (a := a)
  rw [← coe_count]; rw [coe_replicate]

中文:
定理 count_replicate_self
  条件: (a : α) (n : 自然数)
  结论: count a (replicate n a) = n
  证明: by
  convert! List.count_replicate_self (a := a)
  rw [← coe_count]; rw [coe_replicate]

Depends on / 依赖: List.count_replicate_self, Seq.head_dropn, coe_count, coe_replicate, convert, count_replicate_self, dropn_ofSeq, head_dropn, head_ofSeq
-/
theorem count_replicate_self (a : α) (n : Nat) : count a (replicate n a) = n := by
  convert! List.count_replicate_self (a := a)
  rw [← coe_count]; rw [coe_replicate]

/--
theorem `count_replicate` / 定理 `count_replicate`

English:
theorem count_replicate
  given: (a b : α) (n : Nat)
  statement: count a (replicate n b) = if b = a then n else 0
  proof: by
  convert! List.count_replicate (a := a)
  · rw [← coe_count, coe_replicate]
  · simp

中文:
定理 count_replicate
  条件: (a b : α) (n : 自然数)
  结论: count a (replicate n b) = if b = a then n else 0
  证明: by
  convert! List.count_replicate (a := a)
  · rw [← coe_count, coe_replicate]
  · simp

Depends on / 依赖: List.count_replicate, coe_count, coe_replicate, convert, count_replicate
-/
theorem count_replicate (a b : α) (n : Nat) : count a (replicate n b) = if b = a then n else 0 := by
  convert! List.count_replicate (a := a)
  · rw [← coe_count, coe_replicate]
  · simp

/--
theorem `le_count_iff_replicate_le` / 定理 `le_count_iff_replicate_le`

English:
theorem le_count_iff_replicate_le
  given: {a : α} {s : Multiset α} {n : Nat}
  proof: Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', coe_count]
    exact replicate_sublist_iff.symm.trans replicate_le_coe.symm

中文:
定理 le_count_iff_replicate_le
  条件: {a : α} {s : Multiset α} {n : 自然数}
  证明: Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', coe_count]
    exact replicate_sublist_iff.symm.trans replicate_le_coe.symm

Depends on / 依赖: Quot.inductionOn, coe_count, inductionOn, quot_mk_to_coe, replicate_le_coe, replicate_le_coe.symm, replicate_sublist_iff, replicate_sublist_iff.symm.trans
-/
theorem le_count_iff_replicate_le {a : α} {s : Multiset α} {n : Nat} :
    n <= count a s ↔ replicate n a <= s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', coe_count]
    exact replicate_sublist_iff.symm.trans replicate_le_coe.symm

end

/-! ### Lift a relation to `Multiset`s -/

section Rel

variable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}

/--
theorem `rel_replicate_left` / 定理 `rel_replicate_left`

English:
theorem rel_replicate_left
  given: {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat}
  proof: ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun _ _ hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
    

中文:
定理 rel_replicate_left
  条件: {m : Multiset α} {a : α} {r : α -> α -> 命题} {n : 自然数}
  证明: ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun _ _ hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
    

Depends on / 依赖: Eq.trans, card_eq_card_of_rel, card_replicate, eq_of_mem_replicate, exists_mem_of_rel_of_mem, rel_flip, rel_of_forall, symm.trans
-/
theorem rel_replicate_left {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat} :
    (replicate n a).Rel r m ↔ card m = n ∧ forall x, x in m -> r a x :=
  ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun _ _ hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
      (Eq.trans (card_replicate _ _) h.1.symm)⟩

/--
theorem `rel_replicate_right` / 定理 `rel_replicate_right`

English:
theorem rel_replicate_right
  given: {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat}
  proof: rel_flip.trans rel_replicate_left

中文:
定理 rel_replicate_right
  条件: {m : Multiset α} {a : α} {r : α -> α -> 命题} {n : 自然数}
  证明: rel_flip.trans rel_replicate_left

Depends on / 依赖: rel_flip, rel_flip.trans, rel_replicate_left
-/
theorem rel_replicate_right {m : Multiset α} {a : α} {r : α -> α -> Prop} {n : Nat} :
    m.Rel r (replicate n a) ↔ card m = n ∧ forall x, x in m -> r x a :=
  rel_flip.trans rel_replicate_left

end Rel

section Replicate

variable {r : α -> α -> Prop} {s : Multiset α}

/--
theorem `nodup_iff_le` / 定理 `nodup_iff_le`

English:
theorem nodup_iff_le
  given: {s : Multiset α}
  statement: Nodup s ↔ forall a : α, ¬a ::ₘ a ::ₘ 0 <= s
  proof: Quot.induction_on s fun _ =>
nodup_iff_sublist.trans forall_congr' fun a => not_congr (@replicate_le_coe _ a 2 _).symm

中文:
定理 nodup_iff_le
  条件: {s : Multiset α}
  结论: Nodup s ↔ 对任意 a : α, ¬a ::ₘ a ::ₘ 0 <= s
  证明: Quot.induction_on s fun _ =>
nodup_iff_sublist.trans forall_congr' fun a => not_congr (@replicate_le_coe _ a 2 _).symm

Depends on / 依赖: Quot.induction_on, forall_congr, induction_on, nodup_iff_sublist, nodup_iff_sublist.trans, not_congr, replicate_le_coe
-/
theorem nodup_iff_le {s : Multiset α} : Nodup s ↔ forall a : α, ¬a ::ₘ a ::ₘ 0 <= s :=
  Quot.induction_on s fun _ =>
nodup_iff_sublist.trans forall_congr' fun a => not_congr (@replicate_le_coe _ a 2 _).symm

/--
theorem `nodup_iff_ne_cons_cons` / 定理 `nodup_iff_ne_cons_cons`

English:
theorem nodup_iff_ne_cons_cons
  given: {s : Multiset α}
  statement: s.Nodup ↔ forall a t, s != a ::ₘ a ::ₘ t
  proof: nodup_iff_le.trans
    ⟨fun h a _ s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, Multiset.zero_add] at s_eq)⟩

中文:
定理 nodup_iff_ne_cons_cons
  条件: {s : Multiset α}
  结论: s.Nodup ↔ 对任意 a t, s != a ::ₘ a ::ₘ t
  证明: nodup_iff_le.trans
    ⟨fun h a _ s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, Multiset.zero_add] at s_eq)⟩

Depends on / 依赖: Multiset, Multiset.zero_add, cons_add, cons_le_cons, le_iff_exists_add, le_iff_exists_add.mp, nodup_iff_le, nodup_iff_le.trans, s_eq, s_eq.symm, zero_add, zero_le
-/
theorem nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ forall a t, s != a ::ₘ a ::ₘ t :=
  nodup_iff_le.trans
    ⟨fun h a _ s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, Multiset.zero_add] at s_eq)⟩

/--
theorem `nodup_iff_pairwise` / 定理 `nodup_iff_pairwise`

English:
theorem nodup_iff_pairwise
  given: {α} {s : Multiset α}
  statement: Nodup s ↔ Pairwise (· != ·) s
  proof: Quotient.inductionOn s fun _ => pairwise_coe_iff_pairwise.symm

中文:
定理 nodup_iff_pairwise
  条件: {α} {s : Multiset α}
  结论: Nodup s ↔ Pairwise (· != ·) s
  证明: Quotient.inductionOn s fun _ => pairwise_coe_iff_pairwise.symm

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, pairwise_coe_iff_pairwise, pairwise_coe_iff_pairwise.symm
-/
theorem nodup_iff_pairwise {α} {s : Multiset α} : Nodup s ↔ Pairwise (· != ·) s :=
  Quotient.inductionOn s fun _ => pairwise_coe_iff_pairwise.symm

/--
theorem `Nodup.pairwise` / 定理 `Nodup.pairwise`

English:
theorem Nodup.pairwise
  statement: (forall a in s, forall b in s, a != b -> r a b) -> Nodup s -> Pairwise r s
  proof: Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun {a b} ha hb => h a ha b hb⟩

中文:
定理 Nodup.pairwise
  结论: (对任意 a in s, 对任意 b in s, a != b -> r a b) -> Nodup s -> Pairwise r s
  证明: Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun {a b} ha hb => h a ha b hb⟩
-/
protected theorem Nodup.pairwise : (forall a in s, forall b in s, a != b -> r a b) -> Nodup s -> Pairwise r s :=
  Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun {a b} ha hb => h a ha b hb⟩

end Replicate

end Multiset
