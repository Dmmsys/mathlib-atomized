/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.Cycle
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.List

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [Fintype α] [DecidableEq α]`.

## Main definitions

* `Cycle.formPerm`: the cyclic permutation created by looping over a `Cycle α`
* `Equiv.Perm.toList`: the list formed by iterating application of a permutation
* `Equiv.Perm.toCycle`: the cycle formed by iterating application of a permutation
* `Equiv.Perm.isoCycle`: the equivalence between cyclic permutations `f : Perm α`
  and the terms of `Cycle α` that correspond to them
* `Equiv.Perm.isoCycle'`: the same equivalence as `Equiv.Perm.isoCycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `Repr` instance for any `Perm α`, by representing the `Finset` of
  `Cycle α` that correspond to the cycle factors.

## Main results

* `List.isCycle_formPerm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `Equiv.Perm.IsCycle.existsUnique_cycle`: there is only one nontrivial `Cycle α`
  corresponding to each cyclic `f : Perm α`

## Implementation details

The forward direction of `Equiv.Perm.isoCycle'` uses `Fintype.choose` of the uniqueness
result, relying on the `Fintype` instance of a `Cycle.Nodup` subtype.
It is unclear if this works faster than the `Equiv.Perm.toCycle`, which relies
on recursion over `Finset.univ`.

-/

@[expose] public section


open Equiv Equiv.Perm List

variable {α : Type*}

namespace List

variable [DecidableEq α] {l l' : List α}

/--
theorem `formPerm_disjoint_iff` / 定理 `formPerm_disjoint_iff`

English:
theorem formPerm_disjoint_iff
  statement: (hl : Nodup l) (hl' : Nodup l') (hn : 2 <= l.length)
  proof: by
  rw [disjoint_iff_eq_or_eq]; rw [List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx]; rw [formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    lia
  · intro h x
    by_cases hx : x in l
    on_goal 1 => by_cases hx' : x in l'
  

中文:
定理 formPerm_disjoint_iff
  结论: (hl : Nodup l) (hl' : Nodup l') (hn : 2 <= l.length)
  证明: by
  rw [disjoint_iff_eq_or_eq]; rw [List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx]; rw [formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    lia
  · intro h x
    by_cases hx : x in l
    on_goal 1 => by_cases hx' : x in l'
  

Depends on / 依赖: Disjoint, List.Disjoint, List.formPerm_apply_of_notMem, all_goals, disjoint_iff_eq_or_eq, formPerm_apply_mem_eq_self_iff, formPerm_apply_of_notMem, on_goal, specialize
-/
theorem formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 <= l.length)
    (hn' : 2 <= l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l' := by
  rw [disjoint_iff_eq_or_eq]; rw [List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx]; rw [formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    lia
  · intro h x
    by_cases hx : x in l
    on_goal 1 => by_cases hx' : x in l'
    · exact (h hx hx').elim
    all_goals have := List.formPerm_apply_of_notMem ‹_›; tauto

/--
theorem `isCycle_formPerm` / 定理 `isCycle_formPerm`

English:
theorem isCycle_formPerm
  given: (hl : Nodup l) (hn : 2 <= l.length)
  statement: IsCycle (formPerm l)
  proof: by
  rcases l with - | ⟨x, l⟩
  · norm_num at hn
  induction l generalizing x with
  | nil => norm_num at hn
  | cons y l =>
    use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ mem_cons_self]
    · intro w hw
      have : w in x::y::l := mem_of_formPerm_apply_ne hw
      obtai

中文:
定理 isCycle_formPerm
  条件: (hl : Nodup l) (hn : 2 <= l.length)
  结论: 是环 (formPerm l)
  证明: by
  rcases l with - | ⟨x, l⟩
  · norm_num at hn
  induction l generalizing x with
  | nil => norm_num at hn
  | cons y l =>
    use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ mem_cons_self]
    · intro w hw
      have : w in x::y::l := mem_of_formPerm_apply_ne hw
      obtai

Depends on / 依赖: Nat.mod_eq_of_lt, formPerm_apply_mem_ne_self_iff, formPerm_pow_apply_head, generalizing, getElem_of_mem, mem_cons_self, mem_of_formPerm_apply_ne, mod_eq_of_lt, zpow_natCast
-/
theorem isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.length) : IsCycle (formPerm l) := by
  rcases l with - | ⟨x, l⟩
  · norm_num at hn
  induction l generalizing x with
  | nil => norm_num at hn
  | cons y l =>
    use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ mem_cons_self]
    · intro w hw
      have : w in x::y::l := mem_of_formPerm_apply_ne hw
      obtain ⟨k, hk, rfl⟩ := getElem_of_mem this
      use k
      simp only [zpow_natCast, formPerm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt hk]

/--
theorem `pairwise_sameCycle_formPerm` / 定理 `pairwise_sameCycle_formPerm`

English:
theorem pairwise_sameCycle_formPerm
  given: (hl : Nodup l) (hn : 2 <= l.length)
  proof: Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))

中文:
定理 pairwise_sameCycle_formPerm
  条件: (hl : Nodup l) (hn : 2 <= l.length)
  证明: Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))

Depends on / 依赖: Pairwise, Pairwise.imp_mem.mpr, formPerm_apply_mem_ne_self_iff, imp_mem, isCycle_formPerm, pairwise_of_forall, sameCycle
-/
theorem pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 <= l.length) :
    Pairwise l.formPerm.SameCycle l :=
  Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))

/--
theorem `cycleOf_formPerm` / 定理 `cycleOf_formPerm`

English:
theorem cycleOf_formPerm
  given: (hl : Nodup l) (hn : 2 <= l.length) (x)
  proof: have hn : 2 <= l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

中文:
定理 cycleOf_formPerm
  条件: (hl : Nodup l) (hn : 2 <= l.length) (x)
  证明: have hn : 2 <= l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

Depends on / 依赖: attach, cycleOf_eq, formPerm_apply_mem_ne_self_iff, isCycle_formPerm, l.attach.Nodup, l.attach.length, length, length_attach, mem_attach, nodup_attach
-/
theorem cycleOf_formPerm (hl : Nodup l) (hn : 2 <= l.length) (x) :
    cycleOf l.attach.formPerm x = l.attach.formPerm :=
  have hn : 2 <= l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

/--
theorem `cycleType_formPerm` / 定理 `cycleType_formPerm`

English:
theorem cycleType_formPerm
  given: (hl : Nodup l) (hn : 2 <= l.length)
  proof: by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl]; rw [card_toFinset]; rw [dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h] at hn
  · simp
  · simpa using

中文:
定理 cycleType_formPerm
  条件: (hl : Nodup l) (hn : 2 <= l.length)
  证明: by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl]; rw [card_toFinset]; rw [dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h] at hn
  · simp
  · simpa using

Depends on / 依赖: Function, Function.comp_apply, attach, card_toFinset, comp_apply, cycleType_eq, dedup_eq_self, dedup_eq_self.mpr, formPerm, isCycle_formPerm, l.attach.formPerm, length_attach, nodup_attach, support_formPerm_of_nodup
-/
theorem cycleType_formPerm (hl : Nodup l) (hn : 2 <= l.length) :
    cycleType l.attach.formPerm = {l.length} := by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl]; rw [card_toFinset]; rw [dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h] at hn
  · simp
  · simpa using isCycle_formPerm hl hn
  · simp

/--
theorem `formPerm_apply_mem_eq_next` / 定理 `formPerm_apply_mem_eq_next`

English:
theorem formPerm_apply_mem_eq_next
  given: (hl : Nodup l) (x : α) (hx : x in l)
  proof: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [next_getElem _ hl]; rw [formPerm_apply_getElem _ hl]

中文:
定理 formPerm_apply_mem_eq_next
  条件: (hl : Nodup l) (x : α) (hx : x in l)
  证明: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [next_getElem _ hl]; rw [formPerm_apply_getElem _ hl]

Depends on / 依赖: formPerm_apply_getElem, getElem_of_mem, next_getElem
-/
theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x in l) :
    formPerm l x = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [next_getElem _ hl]; rw [formPerm_apply_getElem _ hl]

end List

namespace Cycle

variable [DecidableEq α] (s : Cycle α)

/--
Definition of `formPerm` / `formPerm` 的定义

English:
definition formPerm
  signature: : forall s : Cycle α, Nodup s -> Equiv.Perm α
  body: fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)

@[simp]

中文:
定义 formPerm
  签名: : 对任意 s : 环 α, Nodup s -> 等价.置换 α
  定义体: fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)

@[simp]

Depends on / 依赖: Function, Function.hfunext, List.formPerm, Quotient, Quotient.hrecOn, formPerm, formPerm_eq_of_isRotated, h.nodup_iff, heq_of_eq, hfunext, hrecOn, nodup_iff
-/
def formPerm : forall s : Cycle α, Nodup s -> Equiv.Perm α :=
  fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)

@[simp]
/--
theorem `formPerm_coe` / 定理 `formPerm_coe`

English:
theorem formPerm_coe
  given: (l : List α) (hl : l.Nodup)
  statement: formPerm (l : Cycle α) hl = l.formPerm
  proof: rfl

中文:
定理 formPerm_coe
  条件: (l : 列表 α) (hl : l.Nodup)
  结论: formPerm (l : 环 α) hl = l.formPerm
  证明: rfl
-/
theorem formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.formPerm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `formPerm_subsingleton` / 定理 `formPerm_subsingleton`

English:
theorem formPerm_subsingleton
  given: (s : Cycle α) (h : Subsingleton s)
  statement: formPerm s h.nodup = 1
  proof: by
  obtain ⟨s⟩ := s
  simp only [formPerm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  obtain - | ⟨hd, tl⟩ := s
  · simp
  · simp only [length_eq_zero_iff, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]

中文:
定理 formPerm_subsingleton
  条件: (s : 环 α) (h : 子单例 s)
  结论: formPerm s h.nodup = 1
  证明: by
  obtain ⟨s⟩ := s
  simp only [formPerm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  obtain - | ⟨hd, tl⟩ := s
  · simp
  · simp only [length_eq_zero_iff, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]

Depends on / 依赖: List.length, add_le_iff_nonpos_left, formPerm_coe, length, length_coe, length_eq_zero_iff, length_subsingleton_iff, mk_eq_coe, nonpos_iff_eq_zero
-/
theorem formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.nodup = 1 := by
  obtain ⟨s⟩ := s
  simp only [formPerm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  obtain - | ⟨hd, tl⟩ := s
  · simp
  · simp only [length_eq_zero_iff, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]

/--
theorem `isCycle_formPerm` / 定理 `isCycle_formPerm`

English:
theorem isCycle_formPerm
  given: (s : Cycle α) (h : Nodup s) (hn : Nontrivial s)
  proof: by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)

中文:
定理 isCycle_formPerm
  条件: (s : 环 α) (h : Nodup s) (hn : 非平凡 s)
  证明: by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)

Depends on / 依赖: List.isCycle_formPerm, Quot.inductionOn, inductionOn, isCycle_formPerm, length_nontrivial
-/
theorem isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    IsCycle (formPerm s h) := by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)

/--
theorem `support_formPerm` / 定理 `support_formPerm`

English:
theorem support_formPerm
  given: [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s)
  proof: by
  obtain ⟨s⟩ := s
  refine support_formPerm_of_nodup s h ?_
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn

中文:
定理 support_formPerm
  条件: [有限类型 α] (s : 环 α) (h : Nodup s) (hn : 非平凡 s)
  证明: by
  obtain ⟨s⟩ := s
  refine support_formPerm_of_nodup s h ?_
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn

Depends on / 依赖: Nat.succ_le_succ_iff, length_nontrivial, succ_le_succ_iff, support_formPerm_of_nodup
-/
theorem support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    support (formPerm s h) = s.toFinset := by
  obtain ⟨s⟩ := s
  refine support_formPerm_of_nodup s h ?_
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `formPerm_eq_self_of_notMem` / 定理 `formPerm_eq_self_of_notMem`

English:
theorem formPerm_eq_self_of_notMem
  given: (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s)
  proof: by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_of_notMem hx

中文:
定理 formPerm_eq_self_of_notMem
  条件: (s : 环 α) (h : Nodup s) (x : α) (hx : x ∉ s)
  证明: by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_of_notMem hx

Depends on / 依赖: List.formPerm_apply_of_notMem, Quot.inductionOn, formPerm_apply_of_notMem, inductionOn
-/
theorem formPerm_eq_self_of_notMem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s) :
    formPerm s h x = x := by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_of_notMem hx

/--
theorem `formPerm_apply_mem_eq_next` / 定理 `formPerm_apply_mem_eq_next`

English:
theorem formPerm_apply_mem_eq_next
  given: (s : Cycle α) (h : Nodup s) (x : α) (hx : x in s)
  proof: by
  induction s using Quot.inductionOn
  simpa using! List.formPerm_apply_mem_eq_next h _ (by simp_all)

中文:
定理 formPerm_apply_mem_eq_next
  条件: (s : 环 α) (h : Nodup s) (x : α) (hx : x in s)
  证明: by
  induction s using Quot.inductionOn
  simpa using! List.formPerm_apply_mem_eq_next h _ (by simp_all)

Depends on / 依赖: List.formPerm_apply_mem_eq_next, Quot.inductionOn, formPerm_apply_mem_eq_next, inductionOn
-/
theorem formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x in s) :
    formPerm s h x = next s h x hx := by
  induction s using Quot.inductionOn
  simpa using! List.formPerm_apply_mem_eq_next h _ (by simp_all)

set_option backward.isDefEq.respectTransparency.types false in
nonrec theorem formPerm_reverse (s : Cycle α) (h : Nodup s) :
    formPerm s.reverse (nodup_reverse_iff.mpr h) = (formPerm s h)⁻¹ := by
  induction s using Quot.inductionOn
  simpa using formPerm_reverse _

set_option backward.isDefEq.respectTransparency.types false in
nonrec theorem formPerm_eq_formPerm_iff {α : Type*} [DecidableEq α] {s s' : Cycle α} {hs : s.Nodup}
    {hs' : s'.Nodup} :
    s.formPerm hs = s'.formPerm hs' ↔ s = s' ∨ s.Subsingleton ∧ s'.Subsingleton := by
  rw [Cycle.length_subsingleton_iff]; rw [Cycle.length_subsingleton_iff]
  induction s, s' using Quotient.inductionOn₂'
  simpa using formPerm_eq_formPerm_iff hs hs'

end Cycle

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : List α
  body: List.iterate p x (cycleOf p x).support.card

@[simp]

中文:
定义 toList
  签名: : 列表 α
  定义体: List.iterate p x (cycleOf p x).support.card

@[simp]

Depends on / 依赖: List.iterate, cycleOf, iterate, support, support.card
-/
def toList : List α :=
  List.iterate p x (cycleOf p x).support.card

@[simp]
/--
theorem `toList_one` / 定理 `toList_one`

English:
theorem toList_one
  statement: toList (1 : Perm α) x = []
  proof: by simp [toList, cycleOf_one]

@[simp]

中文:
定理 toList_one
  结论: toList (1 : 置换 α) x = []
  证明: by simp [toList, cycleOf_one]

@[simp]

Depends on / 依赖: cycleOf_one, toList
-/
theorem toList_one : toList (1 : Perm α) x = [] := by simp [toList, cycleOf_one]

@[simp]
/--
theorem `toList_eq_nil_iff` / 定理 `toList_eq_nil_iff`

English:
theorem toList_eq_nil_iff
  given: {p : Perm α} {x}
  statement: toList p x = [] ↔ x ∉ p.support
  proof: by simp [toList]

@[simp]

中文:
定理 toList_eq_nil_iff
  条件: {p : 置换 α} {x}
  结论: toList p x = [] ↔ x ∉ p.support
  证明: by simp [toList]

@[simp]

Depends on / 依赖: toList
-/
theorem toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support := by simp [toList]

@[simp]
/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  statement: length (toList p x) = (cycleOf p x).support.card
  proof: by simp [toList]

中文:
定理 length_toList
  结论: length (toList p x) = (cycleOf p x).support.card
  证明: by simp [toList]

Depends on / 依赖: toList
-/
theorem length_toList : length (toList p x) = (cycleOf p x).support.card := by simp [toList]

/--
theorem `toList_ne_singleton` / 定理 `toList_ne_singleton`

English:
theorem toList_ne_singleton
  given: (y : α)
  statement: toList p x != [y]
  proof: by
  intro H
  simpa [card_support_ne_one] using congr_arg length H

中文:
定理 toList_ne_singleton
  条件: (y : α)
  结论: toList p x != [y]
  证明: by
  intro H
  simpa [card_support_ne_one] using congr_arg length H

Depends on / 依赖: card_support_ne_one, congr_arg, length
-/
theorem toList_ne_singleton (y : α) : toList p x != [y] := by
  intro H
  simpa [card_support_ne_one] using congr_arg length H

/--
theorem `two_le_length_toList_iff_mem_support` / 定理 `two_le_length_toList_iff_mem_support`

English:
theorem two_le_length_toList_iff_mem_support
  given: {p : Perm α} {x : α}
  proof: by simp

中文:
定理 two_le_length_toList_iff_mem_support
  条件: {p : 置换 α} {x : α}
  证明: by simp
-/
theorem two_le_length_toList_iff_mem_support {p : Perm α} {x : α} :
    2 <= length (toList p x) ↔ x in p.support := by simp

/--
theorem `length_toList_pos_of_mem_support` / 定理 `length_toList_pos_of_mem_support`

English:
theorem length_toList_pos_of_mem_support
  given: (h : x in p.support)
  statement: 0 < length (toList p x)
  proof: zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)

中文:
定理 length_toList_pos_of_mem_support
  条件: (h : x in p.support)
  结论: 0 < length (toList p x)
  证明: zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)

Depends on / 依赖: trans_le, two_le_length_toList_iff_mem_support, two_le_length_toList_iff_mem_support.mpr, zero_lt_two, zero_lt_two.trans_le
-/
theorem length_toList_pos_of_mem_support (h : x in p.support) : 0 < length (toList p x) :=
  zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)

/--
theorem `getElem_toList` / 定理 `getElem_toList`

English:
theorem getElem_toList
  given: (n : Nat) (hn : n < length (toList p x))
  proof: by simp [toList, pull_end]

中文:
定理 getElem_toList
  条件: (n : 自然数) (hn : n < length (toList p x))
  证明: by simp [toList, pull_end]

Depends on / 依赖: pull_end, toList
-/
theorem getElem_toList (n : Nat) (hn : n < length (toList p x)) :
    (toList p x)[n] = (p ^ n) x := by simp [toList, pull_end]

/--
theorem `toList_getElem_zero` / 定理 `toList_getElem_zero`

English:
theorem toList_getElem_zero
  given: (h : x in p.support)
  proof: by simp [toList]

中文:
定理 toList_getElem_zero
  条件: (h : x in p.support)
  证明: by simp [toList]

Depends on / 依赖: toList
-/
theorem toList_getElem_zero (h : x in p.support) :
    (toList p x)[0]'(length_toList_pos_of_mem_support _ _ h) = x := by simp [toList]

variable {p} {x}

/--
theorem `mem_toList_iff` / 定理 `mem_toList_iff`

English:
theorem mem_toList_iff
  given: {y : α}
  statement: y in toList p x ↔ SameCycle p x y ∧ x in p.support
  proof: by
  simp only [toList, mem_iterate, iterate_eq_pow, eq_comm (a := y)]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    contrapose! hx
    rw [← support_cycleOf_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx

中文:
定理 mem_toList_iff
  条件: {y : α}
  结论: y in toList p x ↔ SameCycle p x y ∧ x in p.support
  证明: by
  simp only [toList, mem_iterate, iterate_eq_pow, eq_comm (a := y)]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    contrapose! hx
    rw [← support_cycleOf_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx

Depends on / 依赖: contrapose, eq_comm, exists_pow_eq_of_mem_support, h.exists_pow_eq_of_mem_support, iterate_eq_pow, mem_iterate, support_cycleOf_eq_nil_iff, toList
-/
theorem mem_toList_iff {y : α} : y in toList p x ↔ SameCycle p x y ∧ x in p.support := by
  simp only [toList, mem_iterate, iterate_eq_pow, eq_comm (a := y)]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    contrapose! hx
    rw [← support_cycleOf_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx

/--
theorem `nodup_toList` / 定理 `nodup_toList`

English:
theorem nodup_toList
  given: (p : Perm α) (x : α)
  statement: Nodup (toList p x)
  proof: by
  by_cases hx : p x = x
  · rw [← notMem_support, ← toList_eq_nil_iff] at hx
    simp [hx]
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  rw [nodup_iff_injective_getElem]
  intro ⟨n, hn⟩ ⟨m, hm⟩
  rw [length_toList]; rw [← hc.orderOf] at hm hn
  rw [← cycleOf_apply_self]; rw [← Ne]; 

中文:
定理 nodup_toList
  条件: (p : 置换 α) (x : α)
  结论: Nodup (toList p x)
  证明: by
  by_cases hx : p x = x
  · rw [← notMem_support, ← toList_eq_nil_iff] at hx
    simp [hx]
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  rw [nodup_iff_injective_getElem]
  intro ⟨n, hn⟩ ⟨m, hm⟩
  rw [length_toList]; rw [← hc.orderOf] at hm hn
  rw [← cycleOf_apply_self]; rw [← Ne]; 

Depends on / 依赖: Fin.mk.injEq, IsCycle, cycleOf, cycleOf_apply_self, cycleOf_pow_apply_self, getElem_toList, hc.orderOf, isCycle_cycleOf, length_toList, mem_support, nodup_iff_injective_getElem, notMem_support, orderOf, toList_eq_nil_iff
-/
theorem nodup_toList (p : Perm α) (x : α) : Nodup (toList p x) := by
  by_cases hx : p x = x
  · rw [← notMem_support, ← toList_eq_nil_iff] at hx
    simp [hx]
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  rw [nodup_iff_injective_getElem]
  intro ⟨n, hn⟩ ⟨m, hm⟩
  rw [length_toList]; rw [← hc.orderOf] at hm hn
  rw [← cycleOf_apply_self]; rw [← Ne]; rw [← mem_support] at hx
  simp only [Fin.mk.injEq]
  rw [getElem_toList]; rw [getElem_toList]; rw [← cycleOf_pow_apply_self p x n]; rw [←
    cycleOf_pow_apply_self p x m]
  rcases n with - | n <;> rcases m with - | m
  · simp
  · rw [← hc.support_pow_of_pos_of_lt_orderOf m.zero_lt_succ hm, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx.symm]
  · rw [← hc.support_pow_of_pos_of_lt_orderOf n.zero_lt_succ hn, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx]
  intro h
  have hn' : ¬orderOf (p.cycleOf x) ∣ n.succ := Nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn
  have hm' : ¬orderOf (p.cycleOf x) ∣ m.succ := Nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm
  rw [← hc.support_pow_eq_iff] at hn' hm'
  rw [← Nat.mod_eq_of_lt hn]; rw [← Nat.mod_eq_of_lt hm]; rw [← pow_inj_mod]
  refine support_congr ?_ ?_
  · rw [hm', hn']
  · rw [hm']
    intro y hy
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)
    rw [← mul_apply]; rw [(Commute.pow_pow_self _ _ _).eq]; rw [mul_apply]; rw [h]; rw [← mul_apply]; rw [← mul_apply]; rw [(Commute.pow_pow_self _ _ _).eq]

/--
theorem `next_toList_eq_apply` / 定理 `next_toList_eq_apply`

English:
theorem next_toList_eq_apply
  given: (p : Perm α) (x y : α) (hy : y in toList p x)
  proof: by
  rw [mem_toList_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← getElem_toList p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_getElem _ (nodup_toList _ _)]; rw [getElem_toList]; rw [getElem_toList]; rw [← mul_apply]; rw [← pow_succ']
  si

中文:
定理 next_toList_eq_apply
  条件: (p : 置换 α) (x y : α) (hy : y in toList p x)
  证明: by
  rw [mem_toList_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← getElem_toList p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_getElem _ (nodup_toList _ _)]; rw [getElem_toList]; rw [getElem_toList]; rw [← mul_apply]; rw [← pow_succ']
  si

Depends on / 依赖: IsCycle, IsCycle.orderOf, exists_pow_eq_of_mem_support, getElem_toList, hy.left.exists_pow_eq_of_mem_support, hy.right, isCycle_cycleOf, length_toList, mem_support, mem_support.mp, mem_toList_iff, mul_apply, next_getElem, nodup_toList, orderOf, pow_mod_orderOf_cycleOf_apply, pow_succ, simp_rw
-/
theorem next_toList_eq_apply (p : Perm α) (x y : α) (hy : y in toList p x) :
    next (toList p x) y hy = p y := by
  rw [mem_toList_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← getElem_toList p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_getElem _ (nodup_toList _ _)]; rw [getElem_toList]; rw [getElem_toList]; rw [← mul_apply]; rw [← pow_succ']
  simp_rw [length_toList]
  rw [← pow_mod_orderOf_cycleOf_apply p (k + 1)]; rw [IsCycle.orderOf]
  exact isCycle_cycleOf _ (mem_support.mp hy.right)

/--
theorem `toList_pow_apply_eq_rotate` / 定理 `toList_pow_apply_eq_rotate`

English:
theorem toList_pow_apply_eq_rotate
  given: (p : Perm α) (x : α) (k : Nat)
  proof: by
  apply ext_getElem
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [getElem_toList]; rw [getElem_rotate]; rw [getElem_toList]; rw [length_toList]; rw [pow_mod_card_support_cycleOf_self_apply]; rw [pow_add]; rw [mul_apply]

中文:
定理 toList_pow_apply_eq_rotate
  条件: (p : 置换 α) (x : α) (k : 自然数)
  证明: by
  apply ext_getElem
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [getElem_toList]; rw [getElem_rotate]; rw [getElem_toList]; rw [length_toList]; rw [pow_mod_card_support_cycleOf_self_apply]; rw [pow_add]; rw [mul_apply]

Depends on / 依赖: cycleOf_self_apply_pow, ext_getElem, getElem_rotate, getElem_toList, length_rotate, length_toList, mul_apply, pow_add, pow_mod_card_support_cycleOf_self_apply
-/
theorem toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : Nat) :
    p.toList ((p ^ k) x) = (p.toList x).rotate k := by
  apply ext_getElem
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [getElem_toList]; rw [getElem_rotate]; rw [getElem_toList]; rw [length_toList]; rw [pow_mod_card_support_cycleOf_self_apply]; rw [pow_add]; rw [mul_apply]

/--
theorem `SameCycle.toList_isRotated` / 定理 `SameCycle.toList_isRotated`

English:
theorem SameCycle.toList_isRotated
  given: {f : Perm α} {x y : α} (h : SameCycle f x y)
  proof: by
  by_cases hx : x in f.support
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id, pow_zero] at hy
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
    use k.succ
    rw [← toList_pow_apply_eq_rotate]; rw [hy]
  · rw [toList_eq

中文:
定理 SameCycle.toList_isRotated
  条件: {f : 置换 α} {x y : α} (h : SameCycle f x y)
  证明: by
  by_cases hx : x in f.support
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id, pow_zero] at hy
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
    use k.succ
    rw [← toList_pow_apply_eq_rotate]; rw [hy]
  · rw [toList_eq

Depends on / 依赖: coe_one, exists_pow_eq_of_mem_support, f.support, h.exists_pow_eq_of_mem_support, pow_zero, support
-/
theorem SameCycle.toList_isRotated {f : Perm α} {x y : α} (h : SameCycle f x y) :
    toList f x ~r toList f y := by
  by_cases hx : x in f.support
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id, pow_zero] at hy
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
    use k.succ
    rw [← toList_pow_apply_eq_rotate]; rw [hy]
  · rw [toList_eq_nil_iff.mpr hx, isRotated_nil_iff', eq_comm, toList_eq_nil_iff]
    rwa [← h.mem_support_iff]

/--
theorem `pow_apply_mem_toList_iff_mem_support` / 定理 `pow_apply_mem_toList_iff_mem_support`

English:
theorem pow_apply_mem_toList_iff_mem_support
  given: {n : Nat}
  statement: (p ^ n) x in p.toList x ↔ x in p.support
  proof: by
  rw [mem_toList_iff]; rw [and_iff_right_iff_imp]
  refine fun _ => SameCycle.symm ?_
  rw [sameCycle_pow_left]

中文:
定理 pow_apply_mem_toList_iff_mem_support
  条件: {n : 自然数}
  结论: (p ^ n) x in p.toList x ↔ x in p.support
  证明: by
  rw [mem_toList_iff]; rw [and_iff_right_iff_imp]
  refine fun _ => SameCycle.symm ?_
  rw [sameCycle_pow_left]

Depends on / 依赖: SameCycle, SameCycle.symm, and_iff_right_iff_imp, mem_toList_iff, sameCycle_pow_left
-/
theorem pow_apply_mem_toList_iff_mem_support {n : Nat} : (p ^ n) x in p.toList x ↔ x in p.support := by
  rw [mem_toList_iff]; rw [and_iff_right_iff_imp]
  refine fun _ => SameCycle.symm ?_
  rw [sameCycle_pow_left]

/--
theorem `toList_formPerm_nil` / 定理 `toList_formPerm_nil`

English:
theorem toList_formPerm_nil
  given: (x : α)
  statement: toList (formPerm ([] : List α)) x = []
  proof: by simp

中文:
定理 toList_formPerm_nil
  条件: (x : α)
  结论: toList (formPerm ([] : 列表 α)) x = []
  证明: by simp
-/
theorem toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = [] := by simp

/--
theorem `toList_formPerm_singleton` / 定理 `toList_formPerm_singleton`

English:
theorem toList_formPerm_singleton
  given: (x y : α)
  statement: toList (formPerm [x]) y = []
  proof: by simp

中文:
定理 toList_formPerm_singleton
  条件: (x y : α)
  结论: toList (formPerm [x]) y = []
  证明: by simp
-/
theorem toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = [] := by simp

/--
theorem `toList_formPerm_nontrivial` / 定理 `toList_formPerm_nontrivial`

English:
theorem toList_formPerm_nontrivial
  given: (l : List α) (hl : 2 <= l.length) (hn : Nodup l)
  proof: by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  have hs : l.formPerm.support = l.toFinset := by
    refine support_formPerm_of_nodup _ hn ?_
    rintro _ rfl
    simp at hl
  rw [toList]; rw [hc.cycleOf_eq (mem_support.mp _)]; rw [hs]; rw [card_toFinset]; rw [dedup_eq_self.mpr hn]

中文:
定理 toList_formPerm_nontrivial
  条件: (l : 列表 α) (hl : 2 <= l.length) (hn : Nodup l)
  证明: by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  have hs : l.formPerm.support = l.toFinset := by
    refine support_formPerm_of_nodup _ hn ?_
    rintro _ rfl
    simp at hl
  rw [toList]; rw [hc.cycleOf_eq (mem_support.mp _)]; rw [hs]; rw [card_toFinset]; rw [dedup_eq_self.mpr hn]

Depends on / 依赖: IsCycle, List.isCycle_formPerm, Nat.mod_eq_of_lt, card_toFinset, cycleOf_eq, dedup_eq_self, dedup_eq_self.mpr, ext_getElem, formPerm, formPerm_pow_apply_getElem, getElem_iterate, get_eq_getElem, hc.cycleOf_eq, isCycle_formPerm, iterate_eq_pow, l.formPerm.IsCycle, l.formPerm.support, l.toFinset, mem_support, mem_support.mp
-/
theorem toList_formPerm_nontrivial (l : List α) (hl : 2 <= l.length) (hn : Nodup l) :
    toList (formPerm l) (l.get ⟨0, (zero_lt_two.trans_le hl)⟩) = l := by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  have hs : l.formPerm.support = l.toFinset := by
    refine support_formPerm_of_nodup _ hn ?_
    rintro _ rfl
    simp at hl
  rw [toList]; rw [hc.cycleOf_eq (mem_support.mp _)]; rw [hs]; rw [card_toFinset]; rw [dedup_eq_self.mpr hn]
  · refine ext_getElem (by simp) fun k hk hk' => ?_
    simp only [get_eq_getElem, getElem_iterate, iterate_eq_pow, formPerm_pow_apply_getElem _ hn,
      zero_add, Nat.mod_eq_of_lt hk']
  · simp [hs]

/--
theorem `toList_formPerm_isRotated_self` / 定理 `toList_formPerm_isRotated_self`

English:
theorem toList_formPerm_isRotated_self
  statement: (l : List α) (hl : 2 <= l.length) (hn : Nodup l) (x : α)
  proof: by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  rw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl


中文:
定理 toList_formPerm_isRotated_self
  结论: (l : 列表 α) (hl : 2 <= l.length) (hn : Nodup l) (x : α)
  证明: by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  rw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl


Depends on / 依赖: Nat.mod_eq_of_lt, Nat.mod_self, formPerm_eq_of_isRotated, get_eq_get_rotate, get_of_mem, l.rotate, le_of_lt, mod_eq_of_lt, mod_self, rotate, toList_formPerm_nontrivial, tsub_add_cancel_of_le
-/
theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 <= l.length) (hn : Nodup l) (x : α)
    (hx : x in l) : toList (formPerm l) x ~r l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  rw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl
  · simpa using hn

/--
theorem `formPerm_toList` / 定理 `formPerm_toList`

English:
theorem formPerm_toList
  given: (f : Perm α) (x : α)
  statement: formPerm (toList f x) = f.cycleOf x
  proof: by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (notMem_support.mpr hx),
      formPerm_nil]
  ext y
  by_cases hy : SameCycle f x y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycleOf_apply_apply_pow_self]; rw [List.

中文:
定理 formPerm_toList
  条件: (f : 置换 α) (x : α)
  结论: formPerm (toList f x) = f.cycleOf x
  证明: by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (notMem_support.mpr hx),
      formPerm_nil]
  ext y
  by_cases hy : SameCycle f x y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycleOf_apply_apply_pow_self]; rw [List.

Depends on / 依赖: List.formPerm_apply_mem_eq_next, SameCycle, cycleOf_apply_apply_pow_self, cycleOf_apply_of_not_sameCycle, cycleOf_eq_one_iff, exists_pow_eq_of_mem_support, formPerm_apply_mem_eq_next, formPerm_apply_o, formPerm_nil, hy.exists_pow_eq_of_mem_support, mem_support, mem_support.mpr, mem_toList_iff, mul_apply, next_toList_eq_apply, nodup_toList, notMem_support, notMem_support.mpr, pow_succ, toList_eq_nil_iff
-/
theorem formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (notMem_support.mpr hx),
      formPerm_nil]
  ext y
  by_cases hy : SameCycle f x y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycleOf_apply_apply_pow_self]; rw [List.formPerm_apply_mem_eq_next (nodup_toList f x)]; rw [next_toList_eq_apply]; rw [pow_succ']; rw [mul_apply]
    rw [mem_toList_iff]
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
  · rw [cycleOf_apply_of_not_sameCycle hy, formPerm_apply_of_notMem]
    simp [mem_toList_iff, hy]

/--
Definition of `toCycle` / `toCycle` 的定义

English:
definition toCycle
  signature: (f : Perm α) (hf : IsCycle f)
  body: Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x _ l => if f x = x then l else toList f x)
    (by
      intro x y _ s
      refine heq_of_eq ?_
      split_ifs with hx hy hy <;> try rfl
      have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
      exact Quotient.sound' hc

中文:
定义 toCycle
  签名: (f : 置换 α) (hf : 是环 f)
  定义体: Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x _ l => if f x = x then l else toList f x)
    (by
      intro x y _ s
      refine heq_of_eq ?_
      split_ifs with hx hy hy <;> try rfl
      have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
      exact Quotient.sound' hc

Depends on / 依赖: Finset, Finset.univ, IsCycle, IsCycle.sameCycle, Multiset, Multiset.recOn, Quot.mk, Quotient, Quotient.sound, SameCycle, hc.toList_isRotated, heq_of_eq, sameCycle, split_ifs, toList, toList_isRotated
-/
def toCycle (f : Perm α) (hf : IsCycle f) : Cycle α :=
  Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x _ l => if f x = x then l else toList f x)
    (by
      intro x y _ s
      refine heq_of_eq ?_
      split_ifs with hx hy hy <;> try rfl
      have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
      exact Quotient.sound' hc.toList_isRotated)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toCycle_eq_toList` / 定理 `toCycle_eq_toList`

English:
theorem toCycle_eq_toList
  given: (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x != x)
  proof: by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  rw [toCycle]; rw [key]
  simp [hx]

中文:
定理 toCycle_eq_toList
  条件: (f : 置换 α) (hf : 是环 f) (x : α) (hx : f x != x)
  证明: by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  rw [toCycle]; rw [key]
  simp [hx]

Depends on / 依赖: Finset, Finset.univ, Finset.univ.val.erase, toCycle
-/
theorem toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x != x) :
    toCycle f hf = toList f x := by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  rw [toCycle]; rw [key]
  simp [hx]

/--
theorem `exists_toCycle_toList` / 定理 `exists_toCycle_toList`

English:
theorem exists_toCycle_toList
  given: (f : Perm α) (hf : IsCycle f)
  statement: exists x, toCycle f hf = toList f x
  proof: Exists.casesOn hf (fun x h => ⟨x, Perm.toCycle_eq_toList f hf x h.1⟩)

中文:
定理 存在_toCycle_toList
  条件: (f : 置换 α) (hf : 是环 f)
  结论: 存在 x, toCycle f hf = toList f x
  证明: Exists.casesOn hf (fun x h => ⟨x, Perm.toCycle_eq_toList f hf x h.1⟩)

Depends on / 依赖: Exists, Exists.casesOn, Perm.toCycle_eq_toList, casesOn, toCycle_eq_toList
-/
theorem exists_toCycle_toList (f : Perm α) (hf : IsCycle f) : exists x, toCycle f hf = toList f x :=
  Exists.casesOn hf (fun x h => ⟨x, Perm.toCycle_eq_toList f hf x h.1⟩)

/--
theorem `nodup_toCycle` / 定理 `nodup_toCycle`

English:
theorem nodup_toCycle
  given: (f : Perm α) (hf : IsCycle f)
  statement: (toCycle f hf).Nodup
  proof: by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _

中文:
定理 nodup_toCycle
  条件: (f : 置换 α) (hf : 是环 f)
  结论: (toCycle f hf).Nodup
  证明: by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _

Depends on / 依赖: nodup_toList, toCycle_eq_toList
-/
theorem nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup := by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _

/--
theorem `nontrivial_toCycle` / 定理 `nontrivial_toCycle`

English:
theorem nontrivial_toCycle
  given: (f : Perm α) (hf : IsCycle f)
  statement: (toCycle f hf).Nontrivial
  proof: by
  obtain ⟨x, hx, -⟩ := id hf
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]

@[simp]

中文:
定理 nontrivial_toCycle
  条件: (f : 置换 α) (hf : 是环 f)
  结论: (toCycle f hf).非平凡
  证明: by
  obtain ⟨x, hx, -⟩ := id hf
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]

@[simp]

Depends on / 依赖: Cycle.nontrivial_coe_nodup_iff, nodup_toList, nontrivial_coe_nodup_iff, toCycle_eq_toList
-/
theorem nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivial := by
  obtain ⟨x, hx, -⟩ := id hf
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]

@[simp]
/--
theorem `mem_toCycle_iff_support` / 定理 `mem_toCycle_iff_support`

English:
theorem mem_toCycle_iff_support
  given: (f : Perm α) (hf : f.IsCycle)
  statement: x in f.toCycle hf ↔ f x != x
  proof: by
  constructor
  · have ⟨l, hl⟩ := exists_toCycle_toList f hf
    simp only [hl, Cycle.mem_coe_iff, ne_eq]
    intro h
    have ⟨h1, h2⟩ := mem_toList_iff.mp h
    exact ((isCycle_iff_sameCycle (mem_support.mp h2)).mp (y := x) hf).mp h1
  · intro h
    simp only [toCycle_eq_toList f hf x h, Cycle.

中文:
定理 mem_toCycle_iff_support
  条件: (f : 置换 α) (hf : f.是环)
  结论: x in f.toCycle hf ↔ f x != x
  证明: by
  constructor
  · have ⟨l, hl⟩ := exists_toCycle_toList f hf
    simp only [hl, Cycle.mem_coe_iff, ne_eq]
    intro h
    have ⟨h1, h2⟩ := mem_toList_iff.mp h
    exact ((isCycle_iff_sameCycle (mem_support.mp h2)).mp (y := x) hf).mp h1
  · intro h
    simp only [toCycle_eq_toList f hf x h, Cycle.

Depends on / 依赖: Cycle.mem_coe_iff, exists_toCycle_toList, isCycle_iff_sameCycle, iterate_eq_pow, mem_coe_iff, mem_iterate, mem_support, mem_support.mp, mem_toList_iff, mem_toList_iff.mp, ne_eq, toCycle_eq_toList, toList
-/
theorem mem_toCycle_iff_support (f : Perm α) (hf : f.IsCycle) : x in f.toCycle hf ↔ f x != x := by
  constructor
  · have ⟨l, hl⟩ := exists_toCycle_toList f hf
    simp only [hl, Cycle.mem_coe_iff, ne_eq]
    intro h
    have ⟨h1, h2⟩ := mem_toList_iff.mp h
    exact ((isCycle_iff_sameCycle (mem_support.mp h2)).mp (y := x) hf).mp h1
  · intro h
    simp only [toCycle_eq_toList f hf x h, Cycle.mem_coe_iff, toList, mem_iterate, iterate_eq_pow]
    use 0
    exact ⟨by simpa, by simp⟩

@[simp]
/--
theorem `toCycle_next` / 定理 `toCycle_next`

English:
theorem toCycle_next
  given: (f : Perm α) (hf : f.IsCycle) (hx : x in toCycle f hf)
  proof: by
  have ⟨l, hl⟩ := exists_toCycle_toList f hf
  simp only [hl, Cycle.mem_coe_iff] at ⊢ hx
  exact Equiv.Perm.next_toList_eq_apply f l x hx

中文:
定理 toCycle_next
  条件: (f : 置换 α) (hf : f.是环) (hx : x in toCycle f hf)
  证明: by
  have ⟨l, hl⟩ := exists_toCycle_toList f hf
  simp only [hl, Cycle.mem_coe_iff] at ⊢ hx
  exact Equiv.Perm.next_toList_eq_apply f l x hx

Depends on / 依赖: Cycle.mem_coe_iff, Equiv.Perm.next_toList_eq_apply, exists_toCycle_toList, mem_coe_iff, next_toList_eq_apply
-/
theorem toCycle_next (f : Perm α) (hf : f.IsCycle) (hx : x in toCycle f hf) :
    (toCycle f hf).next (nodup_toCycle f hf) x hx = f x := by
  have ⟨l, hl⟩ := exists_toCycle_toList f hf
  simp only [hl, Cycle.mem_coe_iff] at ⊢ hx
  exact Equiv.Perm.next_toList_eq_apply f l x hx

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoCycle` / `isoCycle` 的定义

English:
definition isoCycle
  signature: : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } where
  body: ⟨toCycle (f : Perm α) f.prop, nodup_toCycle (f : Perm α) f.prop,
    nontrivial_toCycle _ f.prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    simpa [toCycle_eq_toList (f : Perm α) f.prop x

中文:
定义 isoCycle
  签名: : { f : 置换 α // 是环 f } ≃ { s : 环 α // s.Nodup ∧ s.非平凡 } where
  定义体: ⟨toCycle (f : Perm α) f.prop, nodup_toCycle (f : Perm α) f.prop,
    nontrivial_toCycle _ f.prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    simpa [toCycle_eq_toList (f : Perm α) f.prop x

Depends on / 依赖: f.prop, nodup_toCycle, toCycle
-/
def isoCycle : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } where
  toFun f := ⟨toCycle (f : Perm α) f.prop, nodup_toCycle (f : Perm α) f.prop,
    nontrivial_toCycle _ f.prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    simpa [toCycle_eq_toList (f : Perm α) f.prop x hx, formPerm_toList, Subtype.ext_iff] using
      f.prop.cycleOf_eq hx
  right_inv s := by
    rcases s with ⟨⟨s⟩, hn, ht⟩
    obtain ⟨x, -, -, hx, -⟩ := id ht
    have hl : 2 <= s.length := by simpa using Cycle.length_nontrivial ht
    simp only [Cycle.mk_eq_coe, Cycle.nodup_coe_iff, Cycle.mem_coe_iff,
      Cycle.formPerm_coe] at hn hx ⊢
    apply Subtype.ext
    dsimp
    rw [toCycle_eq_toList _ _ x]
    · refine Quotient.sound' ?_
      exact toList_formPerm_isRotated_self _ hl hn _ hx
    · rw [← mem_support, support_formPerm_of_nodup _ hn]
      · simpa using hx
      · rintro _ rfl
        simp at hl

end Fintype

section Finite

variable [Finite α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsCycle.existsUnique_cycle` / 定理 `IsCycle.existsUnique_cycle`

English:
theorem IsCycle.existsUnique_cycle
  given: {f : Perm α} (hf : IsCycle f)
  proof: by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine ⟨f.toList x, ⟨nodup_toList f x, ?_⟩, ?_⟩
  · simp [formPerm_toList, hf.cycleOf_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Cycle.formPerm_coe]
    refine (toList_formPerm_isRotated_self _ ?_ hn

中文:
定理 是环.存在Unique_cycle
  条件: {f : 置换 α} (hf : 是环 f)
  证明: by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine ⟨f.toList x, ⟨nodup_toList f x, ?_⟩, ?_⟩
  · simp [formPerm_toList, hf.cycleOf_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Cycle.formPerm_coe]
    refine (toList_formPerm_isRotated_self _ ?_ hn

Depends on / 依赖: Cycle.coe_eq_coe, Cycle.formPerm_coe, Cycle.mk_eq_coe, Nat.le_of_lt_succ, coe_eq_coe, contrapose, cycleOf_eq, f.toList, formPerm, formPerm_coe, formPerm_eq_one_iff, formPerm_toList, hf.cycleOf_eq, le_of_lt_succ, mem_toFinset, mk_eq_coe, nodup_toList, nonempty_fintype, support_formPerm_le, toList
-/
theorem IsCycle.existsUnique_cycle {f : Perm α} (hf : IsCycle f) :
    exists! s : Cycle α, exists h : s.Nodup, s.formPerm h = f := by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine ⟨f.toList x, ⟨nodup_toList f x, ?_⟩, ?_⟩
  · simp [formPerm_toList, hf.cycleOf_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Cycle.formPerm_coe]
    refine (toList_formPerm_isRotated_self _ ?_ hn _ ?_).symm
    · contrapose! hx
      suffices formPerm l = 1 by simp [this]
      rw [formPerm_eq_one_iff _ hn]
      exact Nat.le_of_lt_succ hx
    · rw [← mem_toFinset]
      refine support_formPerm_le l ?_
      simpa using hx

/--
theorem `IsCycle.existsUnique_cycle_subtype` / 定理 `IsCycle.existsUnique_cycle_subtype`

English:
theorem IsCycle.existsUnique_cycle_subtype
  given: {f : Perm α} (hf : IsCycle f)
  proof: by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  refine ⟨⟨s, hs⟩, rfl, ?_⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩

中文:
定理 是环.存在Unique_cycle_subtype
  条件: {f : 置换 α} (hf : 是环 f)
  证明: by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  refine ⟨⟨s, hs⟩, rfl, ?_⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩

Depends on / 依赖: existsUnique_cycle, hf.existsUnique_cycle
-/
theorem IsCycle.existsUnique_cycle_subtype {f : Perm α} (hf : IsCycle f) :
    exists! s : { s : Cycle α // s.Nodup }, (s : Cycle α).formPerm s.prop = f := by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  refine ⟨⟨s, hs⟩, rfl, ?_⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩

/--
theorem `IsCycle.existsUnique_cycle_nontrivial_subtype` / 定理 `IsCycle.existsUnique_cycle_nontrivial_subtype`

English:
theorem IsCycle.existsUnique_cycle_nontrivial_subtype
  given: {f : Perm α} (hf : IsCycle f)
  proof: by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''

中文:
定理 是环.存在Unique_cycle_nontrivial_subtype
  条件: {f : 置换 α} (hf : 是环 f)
  证明: by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''

Depends on / 依赖: Cycle.formPerm_subsingleton, existsUnique_cycle_subtype, formPerm_subsingleton, hf.existsUnique_cycle_subtype, hf.ne_one, hn.nontrivial_iff, ne_one, nontrivial_iff
-/
theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    exists! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.prop.left = f := by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''

end Finite

variable [Fintype α] [DecidableEq α]

/--
Definition of `isoCycle'` / `isoCycle'` 的定义

English:
definition isoCycle'
  signature: : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial }
  body: let f : { s : Cycle α // s.Nodup ∧ s.Nontrivial } -> { f : Perm α // IsCycle f } :=
    fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  { toFun := Fintype.bijInv (show Function.Bijective f by
      rw [Function.bijective_iff_existsUnique]
      rintro ⟨

中文:
定义 isoCycle'
  签名: : { f : 置换 α // 是环 f } ≃ { s : 环 α // s.Nodup ∧ s.非平凡 }
  定义体: let f : { s : Cycle α // s.Nodup ∧ s.Nontrivial } -> { f : Perm α // IsCycle f } :=
    fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  { toFun := Fintype.bijInv (show Function.Bijective f by
      rw [Function.bijective_iff_existsUnique]
      rintro ⟨

Depends on / 依赖: Bijective, Fintype, Fintype.bijInv, Fintype.leftInverse_bijInv, Fintype.rightInverse_bijInv, Function, Function.Bijective, Function.bijective_iff_existsUnique, IsCycle, Nontrivial, Subtype, Subtype.ext_iff, bijInv, bijective_iff_existsUnique, existsUnique_cycle_nontrivial_subtype, ext_iff, formPerm, hf.existsUnique_cycle_nontrivial_subtype, invFun, isCycle_formPerm
-/
def isoCycle' : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  let f : { s : Cycle α // s.Nodup ∧ s.Nontrivial } -> { f : Perm α // IsCycle f } :=
    fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  { toFun := Fintype.bijInv (show Function.Bijective f by
      rw [Function.bijective_iff_existsUnique]
      rintro ⟨f, hf⟩
      simp only [Subtype.ext_iff]
      exact hf.existsUnique_cycle_nontrivial_subtype)
    invFun := f
    left_inv := Fintype.rightInverse_bijInv _
    right_inv := Fintype.leftInverse_bijInv _ }

-- mutes `'decide' tactic does nothing [linter.unusedTactic]`
set_option linter.unusedTactic false in
@[inherit_doc Cycle.formPerm]
notation3 (prettyPrint := false) "c[" (l", "* => foldr (h t => List.cons h t) List.nil) "]" =>
  Cycle.formPerm (Cycle.ofList l) (Iff.mpr Cycle.nodup_coe_iff (by decide))

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Represents a permutation as product of disjoint cycles:
```
#eval (c[0, 1, 2, 3] : Perm (Fin 4))
-- c[0, 1, 2, 3]

#eval (c[3, 1] * c[0, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] * c[3, 1] * c[0, 2] : Perm (Fin 4))
-- 1
```
-/
unsafe instance instRepr [Repr α] : Repr (Perm α) where
  reprPrec f prec :=
    -- Obtain a list of formats which represents disjoint cycles.
letI l := Quot.unquot Multiset.map repr Multiset.pmap toCycle
      (Perm.cycleFactorsFinset f).val
      fun _ hg => (mem_cycleFactorsFinset_iff.mp (Finset.mem_def.mpr hg)).left
    -- And intercalate `*`s.
    match l with
    | [] => "1"
    | [f] => f
    | l =>
      -- multiple terms, use `*` precedence
      (if prec >= 70 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep l (" *" ++ Lean.Format.line)))

end Equiv.Perm
