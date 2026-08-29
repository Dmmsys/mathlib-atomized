/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Order.GameAdd

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `CutExpand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `CutExpand r` on `Multiset α`:
`CutExpand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

We follow the proof by Peter LeFanu Lumsdaine at https://mathoverflow.net/a/229084/3332.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/

@[expose] public section


namespace Relation

open Multiset Prod

variable {α : Type*}

/--
Definition of `CutExpand` / `CutExpand` 的定义

English:
definition CutExpand
  signature: (r : α -> α -> Prop) (s' s : Multiset α)
  body: exists (t : Multiset α) (a : α), (forall a' in t, r a' a) ∧ s' + {a} = s + t

中文:
定义 CutExpand
  签名: (r : α -> α -> 命题) (s' s : Multiset α)
  定义体: exists (t : Multiset α) (a : α), (forall a' in t, r a' a) ∧ s' + {a} = s + t

Depends on / 依赖: Multiset
-/
def CutExpand (r : α -> α -> Prop) (s' s : Multiset α) : Prop :=
  exists (t : Multiset α) (a : α), (forall a' in t, r a' a) ∧ s' + {a} = s + t

variable {r : α -> α -> Prop}

/--
theorem `cutExpand_le_invImage_lex` / 定理 `cutExpand_le_invImage_lex`

English:
theorem cutExpand_le_invImage_lex
  given: [DecidableEq α] [Std.Irrefl r]
  proof: by
  rintro s t ⟨u, a, hr, he⟩
  replace hr := fun a' => mt (hr a')
  refine ⟨a, fun b h => ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, if_neg h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _

中文:
定理 cutExpand_le_invImage_lex
  条件: [DecidableEq α] [Std.Irrefl r]
  证明: by
  rintro s t ⟨u, a, hr, he⟩
  replace hr := fun a' => mt (hr a')
  refine ⟨a, fun b h => ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, if_neg h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _

Depends on / 依赖: Nat.lt_succ_self, add_zero, apply_fun, count_add, count_eq_zero, count_singleton, count_singleton_self, if_neg, irrefl_of, lt_succ_self, replace, simp_rw, toFinsupp_apply
-/
theorem cutExpand_le_invImage_lex [DecidableEq α] [Std.Irrefl r] :
    CutExpand r <= InvImage (Finsupp.Lex (rᶜ ⊓ (· != ·)) (· < ·)) toFinsupp := by
  rintro s t ⟨u, a, hr, he⟩
  replace hr := fun a' => mt (hr a')
  refine ⟨a, fun b h => ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, if_neg h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _

/--
theorem `cutExpand_singleton` / 定理 `cutExpand_singleton`

English:
theorem cutExpand_singleton
  given: {s x} (h : forall x' in s, r x' x)
  statement: CutExpand r s {x}
  proof: ⟨s, x, h, add_comm s _⟩

中文:
定理 cutExpand_singleton
  条件: {s x} (h : 对任意 x' in s, r x' x)
  结论: CutExpand r s {x}
  证明: ⟨s, x, h, add_comm s _⟩

Depends on / 依赖: add_comm
-/
theorem cutExpand_singleton {s x} (h : forall x' in s, r x' x) : CutExpand r s {x} :=
  ⟨s, x, h, add_comm s _⟩

/--
theorem `cutExpand_singleton_singleton` / 定理 `cutExpand_singleton_singleton`

English:
theorem cutExpand_singleton_singleton
  given: {x' x} (h : r x' x)
  statement: CutExpand r {x'} {x}
  proof: cutExpand_singleton fun a h => by rwa [mem_singleton.1 h]

中文:
定理 cutExpand_singleton_singleton
  条件: {x' x} (h : r x' x)
  结论: CutExpand r {x'} {x}
  证明: cutExpand_singleton fun a h => by rwa [mem_singleton.1 h]

Depends on / 依赖: cutExpand_singleton, mem_singleton
-/
theorem cutExpand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x} :=
  cutExpand_singleton fun a h => by rwa [mem_singleton.1 h]

/--
theorem `cutExpand_add_left` / 定理 `cutExpand_add_left`

English:
theorem cutExpand_add_left
  given: {t u} (s)
  statement: CutExpand r (s + t) (s + u) ↔ CutExpand r t u
  proof: exists₂_congr fun _ _ => and_congr Iff.rfl by rw [add_assoc, add_assoc, add_left_cancel_iff]

中文:
定理 cutExpand_add_left
  条件: {t u} (s)
  结论: CutExpand r (s + t) (s + u) ↔ CutExpand r t u
  证明: exists₂_congr fun _ _ => and_congr Iff.rfl by rw [add_assoc, add_assoc, add_left_cancel_iff]

Depends on / 依赖: Iff.rfl, add_assoc, add_left_cancel_iff, and_congr
-/
theorem cutExpand_add_left {t u} (s) : CutExpand r (s + t) (s + u) ↔ CutExpand r t u :=
exists₂_congr fun _ _ => and_congr Iff.rfl by rw [add_assoc, add_assoc, add_left_cancel_iff]

/--
lemma `cutExpand_add_right` / 引理 `cutExpand_add_right`

English:
lemma cutExpand_add_right
  given: {s' s} (t)
  statement: CutExpand r (s' + t) (s + t) ↔ CutExpand r s' s
  proof: by
  convert! cutExpand_add_left t using 2 <;> apply add_comm

中文:
引理 cutExpand_add_right
  条件: {s' s} (t)
  结论: CutExpand r (s' + t) (s + t) ↔ CutExpand r s' s
  证明: by
  convert! cutExpand_add_left t using 2 <;> apply add_comm

Depends on / 依赖: add_comm, convert, cutExpand_add_left
-/
lemma cutExpand_add_right {s' s} (t) : CutExpand r (s' + t) (s + t) ↔ CutExpand r s' s := by
  convert! cutExpand_add_left t using 2 <;> apply add_comm

/--
theorem `cutExpand_add_single` / 定理 `cutExpand_add_single`

English:
theorem cutExpand_add_single
  given: {a' a : α} (s : Multiset α) (h : r a' a)
  proof: (cutExpand_add_left s).2 cutExpand_singleton_singleton h

中文:
定理 cutExpand_add_single
  条件: {a' a : α} (s : Multiset α) (h : r a' a)
  证明: (cutExpand_add_left s).2 cutExpand_singleton_singleton h

Depends on / 依赖: cutExpand_add_left, cutExpand_singleton_singleton
-/
theorem cutExpand_add_single {a' a : α} (s : Multiset α) (h : r a' a) :
    CutExpand r (s + {a'}) (s + {a}) :=
(cutExpand_add_left s).2 cutExpand_singleton_singleton h

/--
theorem `cutExpand_single_add` / 定理 `cutExpand_single_add`

English:
theorem cutExpand_single_add
  given: {a' a : α} (h : r a' a) (s : Multiset α)
  proof: (cutExpand_add_right s).2 cutExpand_singleton_singleton h

中文:
定理 cutExpand_single_add
  条件: {a' a : α} (h : r a' a) (s : Multiset α)
  证明: (cutExpand_add_right s).2 cutExpand_singleton_singleton h

Depends on / 依赖: cutExpand_add_right, cutExpand_singleton_singleton
-/
theorem cutExpand_single_add {a' a : α} (h : r a' a) (s : Multiset α) :
    CutExpand r ({a'} + s) ({a} + s) :=
(cutExpand_add_right s).2 cutExpand_singleton_singleton h

/--
theorem `cutExpand_iff` / 定理 `cutExpand_iff`

English:
theorem cutExpand_iff
  given: [DecidableEq α] [Std.Irrefl r] {s' s : Multiset α}
  proof: by
  simp_rw [CutExpand, add_singleton_eq_iff]
  refine exists₂_congr fun t a => ⟨?_, ?_⟩
  · rintro ⟨ht, ha, rfl⟩
    obtain h | h := mem_add.1 ha
    exacts [⟨ht, h, erase_add_left_pos t h⟩, (@irrefl α r _ a (ht a h)).elim]
  · rintro ⟨ht, h, rfl⟩
    exact ⟨ht, mem_add.2 (Or.inl h), (erase_add_left_pos t h).symm⟩

中文:
定理 cutExpand_iff
  条件: [DecidableEq α] [Std.Irrefl r] {s' s : Multiset α}
  证明: by
  simp_rw [CutExpand, add_singleton_eq_iff]
  refine exists₂_congr fun t a => ⟨?_, ?_⟩
  · rintro ⟨ht, ha, rfl⟩
    obtain h | h := mem_add.1 ha
    exacts [⟨ht, h, erase_add_left_pos t h⟩, (@irrefl α r _ a (ht a h)).elim]
  · rintro ⟨ht, h, rfl⟩
    exact ⟨ht, mem_add.2 (Or.inl h), (erase_add_left_pos t h).symm⟩

Depends on / 依赖: CutExpand, Or.inl, add_singleton_eq_iff, erase_add_left_pos, exacts, irrefl, mem_add, simp_rw
-/
theorem cutExpand_iff [DecidableEq α] [Std.Irrefl r] {s' s : Multiset α} :
    CutExpand r s' s ↔
      exists (t : Multiset α) (a : α), (forall a' in t, r a' a) ∧ a in s ∧ s' = s.erase a + t := by
  simp_rw [CutExpand, add_singleton_eq_iff]
  refine exists₂_congr fun t a => ⟨?_, ?_⟩
  · rintro ⟨ht, ha, rfl⟩
    obtain h | h := mem_add.1 ha
    exacts [⟨ht, h, erase_add_left_pos t h⟩, (@irrefl α r _ a (ht a h)).elim]
  · rintro ⟨ht, h, rfl⟩
    exact ⟨ht, mem_add.2 (Or.inl h), (erase_add_left_pos t h).symm⟩

/--
theorem `not_cutExpand_zero` / 定理 `not_cutExpand_zero`

English:
theorem not_cutExpand_zero
  given: [Std.Irrefl r] (s)
  statement: ¬CutExpand r s 0
  proof: by
  classical
  rw [cutExpand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩

中文:
定理 not_cutExpand_zero
  条件: [Std.Irrefl r] (s)
  结论: ¬CutExpand r s 0
  证明: by
  classical
  rw [cutExpand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩

Depends on / 依赖: classical, cutExpand_iff
-/
theorem not_cutExpand_zero [Std.Irrefl r] (s) : ¬CutExpand r s 0 := by
  classical
  rw [cutExpand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩

/--
lemma `cutExpand_zero` / 引理 `cutExpand_zero`

English:
lemma cutExpand_zero
  given: {x}
  statement: CutExpand r 0 {x}
  proof: ⟨0, x, nofun, add_comm 0 _⟩

中文:
引理 cutExpand_zero
  条件: {x}
  结论: CutExpand r 0 {x}
  证明: ⟨0, x, nofun, add_comm 0 _⟩

Depends on / 依赖: add_comm
-/
lemma cutExpand_zero {x} : CutExpand r 0 {x} := ⟨0, x, nofun, add_comm 0 _⟩

/--
theorem `cutExpand_fibration` / 定理 `cutExpand_fibration`

English:
theorem cutExpand_fibration
  given: (r : α -> α -> Prop)
  proof: by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩; dsimp at he ⊢
  classical
  obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he
  rw [add_assoc]; rw [mem_add] at ha
  obtain h | h := ha
  · refine ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc]
  · refine ⟨(s₁, (s₂ + t).erase a), GameAdd.snd ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, singleton_add, cons_erase h]
    · rw [add_assoc, erase_add_right_pos _ h]

中文:
定理 cutExpand_fibration
  条件: (r : α -> α -> 命题)
  证明: by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩; dsimp at he ⊢
  classical
  obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he
  rw [add_assoc]; rw [mem_add] at ha
  obtain h | h := ha
  · refine ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc]
  · refine ⟨(s₁, (s₂ + t).erase a), GameAdd.snd ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, singleton_add, cons_erase h]
    · rw [add_assoc, erase_add_right_pos _ h]

Depends on / 依赖: GameAdd, GameAdd.fst, GameAdd.snd, add_assoc, add_comm, add_right_comm, add_singleton_eq_iff, classical, cons_erase, erase_add_left_pos, erase_add_right_po, mem_add, singleton_add
-/
theorem cutExpand_fibration (r : α -> α -> Prop) :
    Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s => s.1 + s.2 := by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩; dsimp at he ⊢
  classical
  obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he
  rw [add_assoc]; rw [mem_add] at ha
  obtain h | h := ha
  · refine ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc]
  · refine ⟨(s₁, (s₂ + t).erase a), GameAdd.snd ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, singleton_add, cons_erase h]
    · rw [add_assoc, erase_add_right_pos _ h]

/--
lemma `cutExpand_closed` / 引理 `cutExpand_closed`

English:
lemma cutExpand_closed
  statement: [Std.Irrefl r] (p : α -> Prop)
  proof: by
  classical
  rw [cutExpand_iff]
  rintro ⟨t, a, hr, ha, rfl⟩ hsp a' h'
  obtain (h' | h') := mem_add.1 h'
  exacts [hsp a' (mem_of_mem_erase h'), h (hr a' h') (hsp a ha)]

中文:
引理 cutExpand_closed
  结论: [Std.Irrefl r] (p : α -> 命题)
  证明: by
  classical
  rw [cutExpand_iff]
  rintro ⟨t, a, hr, ha, rfl⟩ hsp a' h'
  obtain (h' | h') := mem_add.1 h'
  exacts [hsp a' (mem_of_mem_erase h'), h (hr a' h') (hsp a ha)]

Depends on / 依赖: classical, cutExpand_iff, exacts, mem_add, mem_of_mem_erase
-/
lemma cutExpand_closed [Std.Irrefl r] (p : α -> Prop)
    (h : forall {a' a}, r a' a -> p a -> p a') {s' s : Multiset α} :
    CutExpand r s' s -> (forall a in s, p a) -> forall a in s', p a := by
  classical
  rw [cutExpand_iff]
  rintro ⟨t, a, hr, ha, rfl⟩ hsp a' h'
  obtain (h' | h') := mem_add.1 h'
  exacts [hsp a' (mem_of_mem_erase h'), h (hr a' h') (hsp a ha)]

/--
lemma `cutExpand_double` / 引理 `cutExpand_double`

English:
lemma cutExpand_double
  given: {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a)
  statement: CutExpand r {a₁, a₂} {a}
  proof: cutExpand_singleton by
    simp only [insert_eq_cons, mem_cons, mem_singleton, forall_eq_or_imp, forall_eq]
    tauto

中文:
引理 cutExpand_double
  条件: {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a)
  结论: CutExpand r {a₁, a₂} {a}
  证明: cutExpand_singleton by
    simp only [insert_eq_cons, mem_cons, mem_singleton, forall_eq_or_imp, forall_eq]
    tauto

Depends on / 依赖: cutExpand_singleton, forall_eq, forall_eq_or_imp, insert_eq_cons, mem_cons, mem_singleton
-/
lemma cutExpand_double {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a) : CutExpand r {a₁, a₂} {a} :=
cutExpand_singleton by
    simp only [insert_eq_cons, mem_cons, mem_singleton, forall_eq_or_imp, forall_eq]
    tauto

/--
lemma `cutExpand_pair_left` / 引理 `cutExpand_pair_left`

English:
lemma cutExpand_pair_left
  given: {a' a b} (hr : r a' a)
  statement: CutExpand r {a', b} {a, b}
  proof: (cutExpand_add_right {b}).2 (cutExpand_singleton_singleton hr)

中文:
引理 cutExpand_pair_left
  条件: {a' a b} (hr : r a' a)
  结论: CutExpand r {a', b} {a, b}
  证明: (cutExpand_add_right {b}).2 (cutExpand_singleton_singleton hr)

Depends on / 依赖: cutExpand_add_right, cutExpand_singleton_singleton
-/
lemma cutExpand_pair_left {a' a b} (hr : r a' a) : CutExpand r {a', b} {a, b} :=
  (cutExpand_add_right {b}).2 (cutExpand_singleton_singleton hr)

/--
lemma `cutExpand_pair_right` / 引理 `cutExpand_pair_right`

English:
lemma cutExpand_pair_right
  given: {a b' b} (hr : r b' b)
  statement: CutExpand r {a, b'} {a, b}
  proof: (cutExpand_add_left {a}).2 (cutExpand_singleton_singleton hr)

中文:
引理 cutExpand_pair_right
  条件: {a b' b} (hr : r b' b)
  结论: CutExpand r {a, b'} {a, b}
  证明: (cutExpand_add_left {a}).2 (cutExpand_singleton_singleton hr)

Depends on / 依赖: cutExpand_add_left, cutExpand_singleton_singleton
-/
lemma cutExpand_pair_right {a b' b} (hr : r b' b) : CutExpand r {a, b'} {a, b} :=
  (cutExpand_add_left {a}).2 (cutExpand_singleton_singleton hr)

/--
lemma `cutExpand_double_left` / 引理 `cutExpand_double_left`

English:
lemma cutExpand_double_left
  given: {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a)
  proof: (cutExpand_add_right {b}).2 (cutExpand_double h₁ h₂)

中文:
引理 cutExpand_double_left
  条件: {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a)
  证明: (cutExpand_add_right {b}).2 (cutExpand_double h₁ h₂)

Depends on / 依赖: cutExpand_add_right, cutExpand_double
-/
lemma cutExpand_double_left {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a) :
    CutExpand r {a₁, a₂, b} {a, b} :=
  (cutExpand_add_right {b}).2 (cutExpand_double h₁ h₂)

/--
theorem `acc_of_singleton` / 定理 `acc_of_singleton`

English:
theorem acc_of_singleton
  given: [Std.Irrefl r] {s : Multiset α} (hs : forall a in s, Acc (CutExpand r) {a})
  proof: by
  induction s using Multiset.induction with
  | empty => exact Acc.intro 0 fun s h => (not_cutExpand_zero s h).elim
  | cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha => hs.2 a ha).of_fibration _ (cutExpand_fibration r)

中文:
定理 acc_of_singleton
  条件: [Std.Irrefl r] {s : Multiset α} (hs : 对任意 a in s, Acc (CutExpand r) {a})
  证明: by
  induction s using Multiset.induction with
  | empty => exact Acc.intro 0 fun s h => (not_cutExpand_zero s h).elim
  | cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha => hs.2 a ha).of_fibration _ (cutExpand_fibration r)

Depends on / 依赖: Acc.intro, Multiset, Multiset.induction, cutExpand_fibration, forall_mem_cons, not_cutExpand_zero, of_fibration, prod_gameAdd, s.singleton_add, singleton_add
-/
theorem acc_of_singleton [Std.Irrefl r] {s : Multiset α} (hs : forall a in s, Acc (CutExpand r) {a}) :
    Acc (CutExpand r) s := by
  induction s using Multiset.induction with
  | empty => exact Acc.intro 0 fun s h => (not_cutExpand_zero s h).elim
  | cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha => hs.2 a ha).of_fibration _ (cutExpand_fibration r)

/--
theorem `_root_.Acc.cutExpand` / 定理 `_root_.Acc.cutExpand`

English:
theorem _root_.Acc.cutExpand
  given: [Std.Irrefl r] {a : α} (hacc : Acc r a)
  statement: Acc (CutExpand r) {a}
  proof: by
  induction hacc with | _ a h ih
  refine Acc.intro _ fun s => ?_
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine acc_of_singleton fun a' => ?_
  rw [erase_singleton]; rw [zero_add]
  exact ih a' ∘ hr a'

中文:
定理 _root_.Acc.cutExpand
  条件: [Std.Irrefl r] {a : α} (hacc : Acc r a)
  结论: Acc (CutExpand r) {a}
  证明: by
  induction hacc with | _ a h ih
  refine Acc.intro _ fun s => ?_
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine acc_of_singleton fun a' => ?_
  rw [erase_singleton]; rw [zero_add]
  exact ih a' ∘ hr a'

Depends on / 依赖: Acc.intro, acc_of_singleton, classical, cutExpand_iff, erase_singleton, mem_singleton, zero_add
-/
theorem _root_.Acc.cutExpand [Std.Irrefl r] {a : α} (hacc : Acc r a) : Acc (CutExpand r) {a} := by
  induction hacc with | _ a h ih
  refine Acc.intro _ fun s => ?_
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine acc_of_singleton fun a' => ?_
  rw [erase_singleton]; rw [zero_add]
  exact ih a' ∘ hr a'

/--
theorem `_root_.WellFounded.cutExpand` / 定理 `_root_.WellFounded.cutExpand`

English:
theorem _root_.WellFounded.cutExpand
  given: (hr : WellFounded r)
  statement: WellFounded (CutExpand r)
  proof: ⟨have := hr.irrefl; fun _ => acc_of_singleton fun a _ => (hr.apply a).cutExpand⟩

中文:
定理 _root_.良基.cutExpand
  条件: (hr : 良基 r)
  结论: 良基 (CutExpand r)
  证明: ⟨have := hr.irrefl; fun _ => acc_of_singleton fun a _ => (hr.apply a).cutExpand⟩

Depends on / 依赖: acc_of_singleton, cutExpand, hr.apply, hr.irrefl, irrefl
-/
theorem _root_.WellFounded.cutExpand (hr : WellFounded r) : WellFounded (CutExpand r) :=
  ⟨have := hr.irrefl; fun _ => acc_of_singleton fun a _ => (hr.apply a).cutExpand⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : IsWellFounded α r] : IsWellFounded _ (CutExpand r)
  body: ⟨h.wf.cutExpand⟩

中文:
实例 [h
  签名: : 是良基 α r] : 是良基 _ (CutExpand r)
  定义体: ⟨h.wf.cutExpand⟩

Depends on / 依赖: cutExpand, h.wf.cutExpand
-/
instance [h : IsWellFounded α r] : IsWellFounded _ (CutExpand r) :=
  ⟨h.wf.cutExpand⟩

end Relation
