/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.List.Count

/-!
# Sum and difference of multisets

This file defines the following operations on multisets:

* `Add (Multiset α)` instance: `s + t` adds the multiplicities of the elements of `s` and `t`
* `Sub (Multiset α)` instance: `s - t` subtracts the multiplicities of the elements of `s` and `t`
* `Multiset.erase`: `s.erase x` reduces the multiplicity of `x` in `s` by one.

## Notation (defined later)

* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Additive monoid -/

section add
variable {s t u : Multiset α}

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (s₁ s₂ : Multiset α)
  body: (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.append p₂

中文:
定义 add
  签名: (s₁ s₂ : Multiset α)
  定义体: (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.append p₂
-/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.append p₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Multiset α)
  body: ⟨Multiset.add⟩

@[simp]

中文:
实例 :
  签名: 加法 (Multiset α)
  定义体: ⟨Multiset.add⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.add
-/
instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (s t : List α)
  statement: (s + t : Multiset α) = (s ++ t : List α)
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (s t : 列表 α)
  结论: (s + t : Multiset α) = (s ++ t : 列表 α)
  证明: rfl

@[simp]
-/
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

@[simp]
/--
theorem `singleton_add` / 定理 `singleton_add`

English:
theorem singleton_add
  given: (a : α) (s : Multiset α)
  statement: {a} + s = a ::ₘ s
  proof: rfl

中文:
定理 singleton_add
  条件: (a : α) (s : Multiset α)
  结论: {a} + s = a ::ₘ s
  证明: rfl
-/
theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl

/--
lemma `add_le_add_iff_left` / 引理 `add_le_add_iff_left`

English:
lemma add_le_add_iff_left
  statement: s + t <= s + u ↔ t <= u
  proof: Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _

中文:
引理 add_le_add_iff_left
  结论: s + t <= s + u ↔ t <= u
  证明: Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _
-/
protected lemma add_le_add_iff_left : s + t <= s + u ↔ t <= u :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _

/--
lemma `add_le_add_iff_right` / 引理 `add_le_add_iff_right`

English:
lemma add_le_add_iff_right
  statement: s + u <= t + u ↔ s <= t
  proof: Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right

中文:
引理 add_le_add_iff_right
  结论: s + u <= t + u ↔ s <= t
  证明: Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right
-/
protected lemma add_le_add_iff_right : s + u <= t + u ↔ s <= t :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right

/--
lemma `add_comm` / 引理 `add_comm`

English:
lemma add_comm
  given: (s t : Multiset α)
  statement: s + t = t + s
  proof: Quotient.inductionOn₂ s t fun _ _ => Quot.sound perm_append_comm

中文:
引理 add_comm
  条件: (s t : Multiset α)
  结论: s + t = t + s
  证明: Quotient.inductionOn₂ s t fun _ _ => Quot.sound perm_append_comm
-/
protected lemma add_comm (s t : Multiset α) : s + t = t + s :=
  Quotient.inductionOn₂ s t fun _ _ => Quot.sound perm_append_comm

/--
lemma `add_assoc` / 引理 `add_assoc`

English:
lemma add_assoc
  given: (s t u : Multiset α)
  statement: s + t + u = s + (t + u)
  proof: Quotient.inductionOn₃ s t u fun _ _ _ => congr_arg _ append_assoc ..

@[simp high]

中文:
引理 add_assoc
  条件: (s t u : Multiset α)
  结论: s + t + u = s + (t + u)
  证明: Quotient.inductionOn₃ s t u fun _ _ _ => congr_arg _ append_assoc ..

@[simp high]
-/
protected lemma add_assoc (s t u : Multiset α) : s + t + u = s + (t + u) :=
Quotient.inductionOn₃ s t u fun _ _ _ => congr_arg _ append_assoc ..

@[simp high]
/--
lemma `zero_add` / 引理 `zero_add`

English:
lemma zero_add
  given: (s : Multiset α)
  statement: 0 + s = s
  proof: Quotient.inductionOn s fun _ => rfl

@[simp high]

中文:
引理 zero_add
  条件: (s : Multiset α)
  结论: 0 + s = s
  证明: Quotient.inductionOn s fun _ => rfl

@[simp high]
-/
protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ => rfl

@[simp high]
/--
lemma `add_zero` / 引理 `add_zero`

English:
lemma add_zero
  given: (s : Multiset α)
  statement: s + 0 = s
  proof: Quotient.inductionOn s fun l => congr_arg _ append_nil l

中文:
引理 add_zero
  条件: (s : Multiset α)
  结论: s + 0 = s
  证明: Quotient.inductionOn s fun l => congr_arg _ append_nil l
-/
protected lemma add_zero (s : Multiset α) : s + 0 = s :=
Quotient.inductionOn s fun l => congr_arg _ append_nil l

/--
lemma `le_add_right` / 引理 `le_add_right`

English:
lemma le_add_right
  given: (s t : Multiset α)
  statement: s <= s + t
  proof: by
  simpa using Multiset.add_le_add_left (zero_le t)

中文:
引理 le_add_right
  条件: (s t : Multiset α)
  结论: s <= s + t
  证明: by
  simpa using Multiset.add_le_add_left (zero_le t)

Depends on / 依赖: Multiset, Multiset.add_le_add_left, add_le_add_left, zero_le
-/
lemma le_add_right (s t : Multiset α) : s <= s + t := by
  simpa using Multiset.add_le_add_left (zero_le t)

/--
lemma `le_add_left` / 引理 `le_add_left`

English:
lemma le_add_left
  given: (s t : Multiset α)
  statement: s <= t + s
  proof: by
  simpa using Multiset.add_le_add_right (zero_le t)

中文:
引理 le_add_left
  条件: (s t : Multiset α)
  结论: s <= t + s
  证明: by
  simpa using Multiset.add_le_add_right (zero_le t)

Depends on / 依赖: Multiset, Multiset.add_le_add_right, add_le_add_right, zero_le
-/
lemma le_add_left (s t : Multiset α) : s <= t + s := by
  simpa using Multiset.add_le_add_right (zero_le t)

/--
lemma `subset_add_left` / 引理 `subset_add_left`

English:
lemma subset_add_left
  given: {s t : Multiset α}
  statement: s subseteq s + t
  proof: subset_of_le le_add_right s t

中文:
引理 subset_add_left
  条件: {s t : Multiset α}
  结论: s subseteq s + t
  证明: subset_of_le le_add_right s t

Depends on / 依赖: le_add_right, subset_of_le
-/
lemma subset_add_left {s t : Multiset α} : s subseteq s + t := subset_of_le le_add_right s t

/--
lemma `subset_add_right` / 引理 `subset_add_right`

English:
lemma subset_add_right
  given: {s t : Multiset α}
  statement: s subseteq t + s
  proof: subset_of_le le_add_left s t

中文:
引理 subset_add_right
  条件: {s t : Multiset α}
  结论: s subseteq t + s
  证明: subset_of_le le_add_left s t

Depends on / 依赖: le_add_left, subset_of_le
-/
lemma subset_add_right {s t : Multiset α} : s subseteq t + s := subset_of_le le_add_left s t

/--
theorem `le_iff_exists_add` / 定理 `le_iff_exists_add`

English:
theorem le_iff_exists_add
  given: {s t : Multiset α}
  statement: s <= t ↔ exists u, t = s + u
  proof: ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]

中文:
定理 le_iff_存在_add
  条件: {s t : Multiset α}
  结论: s <= t ↔ 存在 u, t = s + u
  证明: ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]

Depends on / 依赖: Quot.sound, e.symm, exists_perm_append, leInductionOn, le_add_right, s.exists_perm_append
-/
theorem le_iff_exists_add {s t : Multiset α} : s <= t ↔ exists u, t = s + u :=
  ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]
/--
theorem `cons_add` / 定理 `cons_add`

English:
theorem cons_add
  given: (a : α) (s t : Multiset α)
  statement: a ::ₘ s + t = a ::ₘ (s + t)
  proof: by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_assoc]

@[simp]

中文:
定理 cons_add
  条件: (a : α) (s t : Multiset α)
  结论: a ::ₘ s + t = a ::ₘ (s + t)
  证明: by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_assoc]

@[simp]

Depends on / 依赖: Multiset, Multiset.add_assoc, add_assoc, singleton_add
-/
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_assoc]

@[simp]
/--
theorem `add_cons` / 定理 `add_cons`

English:
theorem add_cons
  given: (a : α) (s t : Multiset α)
  statement: s + a ::ₘ t = a ::ₘ (s + t)
  proof: by
  rw [Multiset.add_comm]; rw [cons_add]; rw [Multiset.add_comm]

@[simp, grind =]

中文:
定理 add_cons
  条件: (a : α) (s t : Multiset α)
  结论: s + a ::ₘ t = a ::ₘ (s + t)
  证明: by
  rw [Multiset.add_comm]; rw [cons_add]; rw [Multiset.add_comm]

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, cons_add
-/
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [Multiset.add_comm]; rw [cons_add]; rw [Multiset.add_comm]

@[simp, grind =]
/--
theorem `mem_add` / 定理 `mem_add`

English:
theorem mem_add
  given: {a : α} {s t : Multiset α}
  statement: a in s + t ↔ a in s ∨ a in t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

中文:
定理 mem_add
  条件: {a : α} {s t : Multiset α}
  结论: a in s + t ↔ a in s ∨ a in t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

Depends on / 依赖: Quotient, Quotient.inductionOn, mem_append
-/
theorem mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in s ∨ a in t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

variable (p : α -> Prop) [DecidablePred p]

@[simp]
/--
theorem `countP_add` / 定理 `countP_add`

English:
theorem countP_add
  given: (s t)
  statement: countP p (s + t) = countP p s + countP p t
  proof: Quotient.inductionOn₂ s t fun _ _ => countP_append

中文:
定理 countP_add
  条件: (s t)
  结论: countP p (s + t) = countP p s + countP p t
  证明: Quotient.inductionOn₂ s t fun _ _ => countP_append

Depends on / 依赖: Quotient, Quotient.inductionOn, countP_append
-/
theorem countP_add (s t) : countP p (s + t) = countP p s + countP p t :=
  Quotient.inductionOn₂ s t fun _ _ => countP_append

variable [DecidableEq α] in
@[simp]
/--
theorem `count_add` / 定理 `count_add`

English:
theorem count_add
  given: (a : α)
  statement: forall s t, count a (s + t) = count a s + count a t
  proof: countP_add _

中文:
定理 count_add
  条件: (a : α)
  结论: 对任意 s t, count a (s + t) = count a s + count a t
  证明: countP_add _

Depends on / 依赖: countP_add
-/
theorem count_add (a : α) : forall s t, count a (s + t) = count a s + count a t :=
  countP_add _

/--
lemma `add_left_inj` / 引理 `add_left_inj`

English:
lemma add_left_inj
  statement: s + u = t + u ↔ s = t
  proof: by classical simp [Multiset.ext]

中文:
引理 add_left_inj
  结论: s + u = t + u ↔ s = t
  证明: by classical simp [Multiset.ext]
-/
protected lemma add_left_inj : s + u = t + u ↔ s = t := by classical simp [Multiset.ext]

/--
lemma `add_right_inj` / 引理 `add_right_inj`

English:
lemma add_right_inj
  statement: s + t = s + u ↔ t = u
  proof: by classical simp [Multiset.ext]

@[simp]

中文:
引理 add_right_inj
  结论: s + t = s + u ↔ t = u
  证明: by classical simp [Multiset.ext]

@[simp]
-/
protected lemma add_right_inj : s + t = s + u ↔ t = u := by classical simp [Multiset.ext]

@[simp]
/--
theorem `card_add` / 定理 `card_add`

English:
theorem card_add
  given: (s t : Multiset α)
  statement: card (s + t) = card s + card t
  proof: Quotient.inductionOn₂ s t fun _ _ => length_append

中文:
定理 card_add
  条件: (s t : Multiset α)
  结论: card (s + t) = card s + card t
  证明: Quotient.inductionOn₂ s t fun _ _ => length_append

Depends on / 依赖: Quotient, Quotient.inductionOn, length_append
-/
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append

end add

/-! ### Erasing one copy of an element -/

section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (s : Multiset α) (a : α)
  body: Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]

中文:
定义 erase
  签名: (s : Multiset α) (a : α)
  定义体: Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, l.erase, liftOn, p.erase
-/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]
/--
theorem `coe_erase` / 定理 `coe_erase`

English:
theorem coe_erase
  given: (l : List α) (a : α)
  statement: erase (l : Multiset α) a = l.erase a
  proof: rfl

@[simp]

中文:
定理 coe_erase
  条件: (l : 列表 α) (a : α)
  结论: erase (l : Multiset α) a = l.erase a
  证明: rfl

@[simp]
-/
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a :=
  rfl

@[simp]
/--
theorem `erase_zero` / 定理 `erase_zero`

English:
theorem erase_zero
  given: (a : α)
  statement: (0 : Multiset α).erase a = 0
  proof: rfl

@[simp]

中文:
定理 erase_zero
  条件: (a : α)
  结论: (0 : Multiset α).erase a = 0
  证明: rfl

@[simp]
-/
theorem erase_zero (a : α) : (0 : Multiset α).erase a = 0 :=
  rfl

@[simp]
/--
theorem `erase_cons_head` / 定理 `erase_cons_head`

English:
theorem erase_cons_head
  given: (a : α) (s : Multiset α)
  statement: (a ::ₘ s).erase a = s
  proof: Quot.inductionOn s fun l => congr_arg _ List.erase_cons_head a l

@[simp]

中文:
定理 erase_cons_head
  条件: (a : α) (s : Multiset α)
  结论: (a ::ₘ s).erase a = s
  证明: Quot.inductionOn s fun l => congr_arg _ List.erase_cons_head a l

@[simp]

Depends on / 依赖: List.erase_cons_head, Quot.inductionOn, congr_arg, erase_cons_head, inductionOn
-/
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s :=
Quot.inductionOn s fun l => congr_arg _ List.erase_cons_head a l

@[simp]
/--
theorem `erase_cons_tail` / 定理 `erase_cons_tail`

English:
theorem erase_cons_tail
  given: {a b : α} (s : Multiset α) (h : b != a)
  proof: Quot.inductionOn s fun _ => congr_arg _ List.erase_cons_tail (not_beq_of_ne h)

@[simp]

中文:
定理 erase_cons_tail
  条件: {a b : α} (s : Multiset α) (h : b != a)
  证明: Quot.inductionOn s fun _ => congr_arg _ List.erase_cons_tail (not_beq_of_ne h)

@[simp]

Depends on / 依赖: List.erase_cons_tail, Quot.inductionOn, congr_arg, erase_cons_tail, inductionOn, not_beq_of_ne
-/
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b != a) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a :=
Quot.inductionOn s fun _ => congr_arg _ List.erase_cons_tail (not_beq_of_ne h)

@[simp]
/--
theorem `erase_singleton` / 定理 `erase_singleton`

English:
theorem erase_singleton
  given: (a : α)
  statement: ({a} : Multiset α).erase a = 0
  proof: erase_cons_head a 0

@[simp]

中文:
定理 erase_singleton
  条件: (a : α)
  结论: ({a} : Multiset α).erase a = 0
  证明: erase_cons_head a 0

@[simp]

Depends on / 依赖: erase_cons_head
-/
theorem erase_singleton (a : α) : ({a} : Multiset α).erase a = 0 :=
  erase_cons_head a 0

@[simp]
/--
theorem `erase_of_notMem` / 定理 `erase_of_notMem`

English:
theorem erase_of_notMem
  given: {a : α} {s : Multiset α}
  statement: a ∉ s -> s.erase a = s
  proof: Quot.inductionOn s fun _l h => congr_arg _ List.erase_of_not_mem h

@[simp]

中文:
定理 erase_of_notMem
  条件: {a : α} {s : Multiset α}
  结论: a ∉ s -> s.erase a = s
  证明: Quot.inductionOn s fun _l h => congr_arg _ List.erase_of_not_mem h

@[simp]

Depends on / 依赖: List.erase_of_not_mem, Quot.inductionOn, congr_arg, erase_of_not_mem, inductionOn
-/
theorem erase_of_notMem {a : α} {s : Multiset α} : a ∉ s -> s.erase a = s :=
Quot.inductionOn s fun _l h => congr_arg _ List.erase_of_not_mem h

@[simp]
/--
theorem `cons_erase` / 定理 `cons_erase`

English:
theorem cons_erase
  given: {s : Multiset α} {a : α}
  statement: a in s -> a ::ₘ s.erase a = s
  proof: Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm

中文:
定理 cons_erase
  条件: {s : Multiset α} {a : α}
  结论: a in s -> a ::ₘ s.erase a = s
  证明: Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm

Depends on / 依赖: Quot.inductionOn, Quot.sound, inductionOn, perm_cons_erase
-/
theorem cons_erase {s : Multiset α} {a : α} : a in s -> a ::ₘ s.erase a = s :=
  Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm

/--
theorem `erase_cons_tail_of_mem` / 定理 `erase_cons_tail_of_mem`

English:
theorem erase_cons_tail_of_mem
  given: (h : a in s)
  proof: by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm

中文:
定理 erase_cons_tail_of_mem
  条件: (h : a in s)
  证明: by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm

Depends on / 依赖: cons_erase, eq_or_ne, erase_cons_tail, hab.symm, s.erase_cons_tail
-/
theorem erase_cons_tail_of_mem (h : a in s) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a := by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm

/--
theorem `le_cons_erase` / 定理 `le_cons_erase`

English:
theorem le_cons_erase
  given: (s : Multiset α) (a : α)
  statement: s <= a ::ₘ s.erase a
  proof: if h : a in s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_notMem h]; apply le_cons_self

中文:
定理 le_cons_erase
  条件: (s : Multiset α) (a : α)
  结论: s <= a ::ₘ s.erase a
  证明: if h : a in s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_notMem h]; apply le_cons_self

Depends on / 依赖: cons_erase, erase_of_notMem, le_cons_self, le_of_eq
-/
theorem le_cons_erase (s : Multiset α) (a : α) : s <= a ::ₘ s.erase a :=
  if h : a in s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_notMem h]; apply le_cons_self

/--
theorem `add_singleton_eq_iff` / 定理 `add_singleton_eq_iff`

English:
theorem add_singleton_eq_iff
  given: {s t : Multiset α} {a : α}
  statement: s + {a} = t ↔ a in t ∧ s = t.erase a
  proof: by
  rw [Multiset.add_comm]; rw [singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h

中文:
定理 add_singleton_eq_iff
  条件: {s t : Multiset α} {a : α}
  结论: s + {a} = t ↔ a in t ∧ s = t.erase a
  证明: by
  rw [Multiset.add_comm]; rw [singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, cons_erase, erase_cons_head, mem_cons_self, s.erase_cons_head, s.mem_cons_self, singleton_add
-/
theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a in t ∧ s = t.erase a := by
  rw [Multiset.add_comm]; rw [singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h

/--
theorem `erase_add_left_pos` / 定理 `erase_add_left_pos`

English:
theorem erase_add_left_pos
  given: {a : α} {s : Multiset α} (t)
  statement: a in s -> (s + t).erase a = s.erase a + t
  proof: Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_left l₂ h

中文:
定理 erase_add_left_pos
  条件: {a : α} {s : Multiset α} (t)
  结论: a in s -> (s + t).erase a = s.erase a + t
  证明: Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_left l₂ h

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, erase_append_left
-/
theorem erase_add_left_pos {a : α} {s : Multiset α} (t) : a in s -> (s + t).erase a = s.erase a + t :=
Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_left l₂ h

/--
theorem `erase_add_right_pos` / 定理 `erase_add_right_pos`

English:
theorem erase_add_right_pos
  given: {a : α} (s) (h : a in t)
  statement: (s + t).erase a = s + t.erase a
  proof: by
  rw [Multiset.add_comm]; rw [erase_add_left_pos s h]; rw [Multiset.add_comm]

中文:
定理 erase_add_right_pos
  条件: {a : α} (s) (h : a in t)
  结论: (s + t).erase a = s + t.erase a
  证明: by
  rw [Multiset.add_comm]; rw [erase_add_left_pos s h]; rw [Multiset.add_comm]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, erase_add_left_pos
-/
theorem erase_add_right_pos {a : α} (s) (h : a in t) : (s + t).erase a = s + t.erase a := by
  rw [Multiset.add_comm]; rw [erase_add_left_pos s h]; rw [Multiset.add_comm]

/--
theorem `erase_add_right_neg` / 定理 `erase_add_right_neg`

English:
theorem erase_add_right_neg
  given: {a : α} {s : Multiset α} (t)
  proof: Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_right l₂ h

中文:
定理 erase_add_right_neg
  条件: {a : α} {s : Multiset α} (t)
  证明: Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_right l₂ h

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, erase_append_right
-/
theorem erase_add_right_neg {a : α} {s : Multiset α} (t) :
    a ∉ s -> (s + t).erase a = s + t.erase a :=
Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ erase_append_right l₂ h

/--
theorem `erase_add_left_neg` / 定理 `erase_add_left_neg`

English:
theorem erase_add_left_neg
  given: {a : α} (s) (h : a ∉ t)
  statement: (s + t).erase a = s.erase a + t
  proof: by
  rw [Multiset.add_comm]; rw [erase_add_right_neg s h]; rw [Multiset.add_comm]

中文:
定理 erase_add_left_neg
  条件: {a : α} (s) (h : a ∉ t)
  结论: (s + t).erase a = s.erase a + t
  证明: by
  rw [Multiset.add_comm]; rw [erase_add_right_neg s h]; rw [Multiset.add_comm]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, erase_add_right_neg
-/
theorem erase_add_left_neg {a : α} (s) (h : a ∉ t) : (s + t).erase a = s.erase a + t := by
  rw [Multiset.add_comm]; rw [erase_add_right_neg s h]; rw [Multiset.add_comm]

/--
theorem `erase_le` / 定理 `erase_le`

English:
theorem erase_le
  given: (a : α) (s : Multiset α)
  statement: s.erase a <= s
  proof: Quot.inductionOn s fun _ => erase_sublist.subperm

@[simp]

中文:
定理 erase_le
  条件: (a : α) (s : Multiset α)
  结论: s.erase a <= s
  证明: Quot.inductionOn s fun _ => erase_sublist.subperm

@[simp]

Depends on / 依赖: Quot.inductionOn, erase_sublist, erase_sublist.subperm, inductionOn, subperm
-/
theorem erase_le (a : α) (s : Multiset α) : s.erase a <= s :=
  Quot.inductionOn s fun _ => erase_sublist.subperm

@[simp]
/--
theorem `erase_lt` / 定理 `erase_lt`

English:
theorem erase_lt
  given: {a : α} {s : Multiset α}
  statement: s.erase a < s ↔ a in s
  proof: ⟨fun h => not_imp_comm.1 erase_of_notMem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩

中文:
定理 erase_lt
  条件: {a : α} {s : Multiset α}
  结论: s.erase a < s ↔ a in s
  证明: ⟨fun h => not_imp_comm.1 erase_of_notMem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩

Depends on / 依赖: erase_of_notMem, lt_cons_self, ne_of_lt, not_imp_comm, s.erase
-/
theorem erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a in s :=
  ⟨fun h => not_imp_comm.1 erase_of_notMem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩

/--
theorem `erase_subset` / 定理 `erase_subset`

English:
theorem erase_subset
  given: (a : α) (s : Multiset α)
  statement: s.erase a subseteq s
  proof: subset_of_le (erase_le a s)

中文:
定理 erase_subset
  条件: (a : α) (s : Multiset α)
  结论: s.erase a subseteq s
  证明: subset_of_le (erase_le a s)

Depends on / 依赖: erase_le, subset_of_le
-/
theorem erase_subset (a : α) (s : Multiset α) : s.erase a subseteq s :=
  subset_of_le (erase_le a s)

/--
theorem `mem_erase_of_ne` / 定理 `mem_erase_of_ne`

English:
theorem mem_erase_of_ne
  given: {a b : α} {s : Multiset α} (ab : a != b)
  statement: a in s.erase b ↔ a in s
  proof: Quot.inductionOn s fun _l => List.mem_erase_of_ne ab

中文:
定理 mem_erase_of_ne
  条件: {a b : α} {s : Multiset α} (ab : a != b)
  结论: a in s.erase b ↔ a in s
  证明: Quot.inductionOn s fun _l => List.mem_erase_of_ne ab

Depends on / 依赖: List.mem_erase_of_ne, Quot.inductionOn, inductionOn, mem_erase_of_ne
-/
theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a != b) : a in s.erase b ↔ a in s :=
  Quot.inductionOn s fun _l => List.mem_erase_of_ne ab

/--
theorem `mem_of_mem_erase` / 定理 `mem_of_mem_erase`

English:
theorem mem_of_mem_erase
  given: {a b : α} {s : Multiset α}
  statement: a in s.erase b -> a in s
  proof: mem_of_subset (erase_subset _ _)

中文:
定理 mem_of_mem_erase
  条件: {a b : α} {s : Multiset α}
  结论: a in s.erase b -> a in s
  证明: mem_of_subset (erase_subset _ _)

Depends on / 依赖: erase_subset, mem_of_subset
-/
theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a in s.erase b -> a in s :=
  mem_of_subset (erase_subset _ _)

/--
theorem `erase_comm` / 定理 `erase_comm`

English:
theorem erase_comm
  given: (s : Multiset α) (a b : α)
  statement: (s.erase a).erase b = (s.erase b).erase a
  proof: Quot.inductionOn s fun l => congr_arg _ l.erase_comm a b

中文:
定理 erase_comm
  条件: (s : Multiset α) (a b : α)
  结论: (s.erase a).erase b = (s.erase b).erase a
  证明: Quot.inductionOn s fun l => congr_arg _ l.erase_comm a b

Depends on / 依赖: Quot.inductionOn, congr_arg, erase_comm, inductionOn, l.erase_comm
-/
theorem erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
Quot.inductionOn s fun l => congr_arg _ l.erase_comm a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RightCommutative erase (α := α)
  body: ⟨erase_comm⟩

@[gcongr]

中文:
实例 :
  签名: 右交换 erase (α := α)
  定义体: ⟨erase_comm⟩

@[gcongr]

Depends on / 依赖: erase_comm
-/
instance : RightCommutative erase (α := α) := ⟨erase_comm⟩

@[gcongr]
/--
theorem `erase_le_erase` / 定理 `erase_le_erase`

English:
theorem erase_le_erase
  given: {s t : Multiset α} (a : α) (h : s <= t)
  statement: s.erase a <= t.erase a
  proof: leInductionOn h fun h => (h.erase _).subperm

中文:
定理 erase_le_erase
  条件: {s t : Multiset α} (a : α) (h : s <= t)
  结论: s.erase a <= t.erase a
  证明: leInductionOn h fun h => (h.erase _).subperm

Depends on / 依赖: h.erase, leInductionOn, subperm
-/
theorem erase_le_erase {s t : Multiset α} (a : α) (h : s <= t) : s.erase a <= t.erase a :=
  leInductionOn h fun h => (h.erase _).subperm

/--
theorem `erase_le_iff_le_cons` / 定理 `erase_le_iff_le_cons`

English:
theorem erase_le_iff_le_cons
  given: {s t : Multiset α} {a : α}
  statement: s.erase a <= t ↔ s <= a ::ₘ t
  proof: ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a in s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_notMem m).1 h)⟩

@[simp]

中文:
定理 erase_le_iff_le_cons
  条件: {s t : Multiset α} {a : α}
  结论: s.erase a <= t ↔ s <= a ::ₘ t
  证明: ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a in s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_notMem m).1 h)⟩

@[simp]

Depends on / 依赖: cons_erase, cons_le_cons, cons_le_cons_iff, erase_le, le_cons_erase, le_cons_of_notMem, le_trans
-/
theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a <= t ↔ s <= a ::ₘ t :=
  ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a in s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_notMem m).1 h)⟩

@[simp]
/--
theorem `card_erase_of_mem` / 定理 `card_erase_of_mem`

English:
theorem card_erase_of_mem
  given: {a : α} {s : Multiset α}
  statement: a in s -> card (s.erase a) = pred (card s)
  proof: Quot.inductionOn s fun _l => length_erase_of_mem

中文:
定理 card_erase_of_mem
  条件: {a : α} {s : Multiset α}
  结论: a in s -> card (s.erase a) = pred (card s)
  证明: Quot.inductionOn s fun _l => length_erase_of_mem

Depends on / 依赖: Quot.inductionOn, inductionOn, length_erase_of_mem
-/
theorem card_erase_of_mem {a : α} {s : Multiset α} : a in s -> card (s.erase a) = pred (card s) :=
  Quot.inductionOn s fun _l => length_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
/--
theorem `card_erase_add_one` / 定理 `card_erase_add_one`

English:
theorem card_erase_add_one
  given: {a : α} {s : Multiset α}
  statement: a in s -> card (s.erase a) + 1 = card s
  proof: Quot.inductionOn s fun _l => length_erase_add_one

中文:
定理 card_erase_add_one
  条件: {a : α} {s : Multiset α}
  结论: a in s -> card (s.erase a) + 1 = card s
  证明: Quot.inductionOn s fun _l => length_erase_add_one

Depends on / 依赖: Quot.inductionOn, inductionOn, length_erase_add_one
-/
theorem card_erase_add_one {a : α} {s : Multiset α} : a in s -> card (s.erase a) + 1 = card s :=
  Quot.inductionOn s fun _l => length_erase_add_one

/--
theorem `card_erase_lt_of_mem` / 定理 `card_erase_lt_of_mem`

English:
theorem card_erase_lt_of_mem
  given: {a : α} {s : Multiset α}
  statement: a in s -> card (s.erase a) < card s
  proof: fun h => card_lt_card (erase_lt.mpr h)

中文:
定理 card_erase_lt_of_mem
  条件: {a : α} {s : Multiset α}
  结论: a in s -> card (s.erase a) < card s
  证明: fun h => card_lt_card (erase_lt.mpr h)

Depends on / 依赖: card_lt_card, erase_lt, erase_lt.mpr
-/
theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a in s -> card (s.erase a) < card s :=
  fun h => card_lt_card (erase_lt.mpr h)

/--
theorem `card_erase_le` / 定理 `card_erase_le`

English:
theorem card_erase_le
  given: {a : α} {s : Multiset α}
  statement: card (s.erase a) <= card s
  proof: card_le_card (erase_le a s)

中文:
定理 card_erase_le
  条件: {a : α} {s : Multiset α}
  结论: card (s.erase a) <= card s
  证明: card_le_card (erase_le a s)

Depends on / 依赖: card_le_card, erase_le
-/
theorem card_erase_le {a : α} {s : Multiset α} : card (s.erase a) <= card s :=
  card_le_card (erase_le a s)

/--
theorem `card_erase_eq_ite` / 定理 `card_erase_eq_ite`

English:
theorem card_erase_eq_ite
  given: {a : α} {s : Multiset α}
  proof: by
  by_cases h : a in s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_notMem h, if_neg]

@[simp]

中文:
定理 card_erase_eq_ite
  条件: {a : α} {s : Multiset α}
  证明: by
  by_cases h : a in s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_notMem h, if_neg]

@[simp]

Depends on / 依赖: card_erase_of_mem, erase_of_notMem, if_neg, if_pos
-/
theorem card_erase_eq_ite {a : α} {s : Multiset α} :
    card (s.erase a) = if a in s then pred (card s) else card s := by
  by_cases h : a in s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_notMem h, if_neg]

@[simp]
/--
theorem `count_erase_self` / 定理 `count_erase_self`

English:
theorem count_erase_self
  given: (a : α) (s : Multiset α)
  statement: count a (erase s a) = count a s - 1
  proof: Quotient.inductionOn s fun l => by
    convert! List.count_erase_self (a := a) (l := l) <;> rw [← coe_count] <;> simp

@[simp]

中文:
定理 count_erase_self
  条件: (a : α) (s : Multiset α)
  结论: count a (erase s a) = count a s - 1
  证明: Quotient.inductionOn s fun l => by
    convert! List.count_erase_self (a := a) (l := l) <;> rw [← coe_count] <;> simp

@[simp]

Depends on / 依赖: List.count_erase_self, Quotient, Quotient.inductionOn, coe_count, convert, count_erase_self, inductionOn
-/
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = count a s - 1 :=
  Quotient.inductionOn s fun l => by
    convert! List.count_erase_self (a := a) (l := l) <;> rw [← coe_count] <;> simp

@[simp]
/--
theorem `count_erase_of_ne` / 定理 `count_erase_of_ne`

English:
theorem count_erase_of_ne
  given: {a b : α} (ab : a != b) (s : Multiset α)
  proof: Quotient.inductionOn s fun l => by
    convert! List.count_erase_of_ne ab (l := l) <;> rw [← coe_count] <;> simp

中文:
定理 count_erase_of_ne
  条件: {a b : α} (ab : a != b) (s : Multiset α)
  证明: Quotient.inductionOn s fun l => by
    convert! List.count_erase_of_ne ab (l := l) <;> rw [← coe_count] <;> simp

Depends on / 依赖: List.count_erase_of_ne, Quotient, Quotient.inductionOn, coe_count, convert, count_erase_of_ne, inductionOn
-/
theorem count_erase_of_ne {a b : α} (ab : a != b) (s : Multiset α) :
    count a (erase s b) = count a s :=
  Quotient.inductionOn s fun l => by
    convert! List.count_erase_of_ne ab (l := l) <;> rw [← coe_count] <;> simp

end Erase

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (s t : Multiset α)
  body: (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.diff p₂

中文:
定义 sub
  签名: (s t : Multiset α)
  定义体: (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.diff p₂
-/
protected def sub (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.diff p₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Multiset α)
  body: ⟨.sub⟩

@[simp]

中文:
实例 :
  签名: 减法 (Multiset α)
  定义体: ⟨.sub⟩

@[simp]
-/
instance : Sub (Multiset α) := ⟨.sub⟩

@[simp]
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (s t : List α)
  statement: (s - t : Multiset α) = s.diff t
  proof: rfl

中文:
引理 coe_sub
  条件: (s t : 列表 α)
  结论: (s - t : Multiset α) = s.diff t
  证明: rfl
-/
lemma coe_sub (s t : List α) : (s - t : Multiset α) = s.diff t :=
  rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
@[simp high]
/--
lemma `sub_zero` / 引理 `sub_zero`

English:
lemma sub_zero
  given: (s : Multiset α)
  statement: s - 0 = s
  proof: Quot.inductionOn s fun _l => rfl

@[simp]

中文:
引理 sub_zero
  条件: (s : Multiset α)
  结论: s - 0 = s
  证明: Quot.inductionOn s fun _l => rfl

@[simp]
-/
protected lemma sub_zero (s : Multiset α) : s - 0 = s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/--
lemma `sub_cons` / 引理 `sub_cons`

English:
lemma sub_cons
  given: (a : α) (s t : Multiset α)
  statement: s - a ::ₘ t = s.erase a - t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ diff_cons _ _ _

中文:
引理 sub_cons
  条件: (a : α) (s t : Multiset α)
  结论: s - a ::ₘ t = s.erase a - t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ diff_cons _ _ _

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, diff_cons
-/
lemma sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ diff_cons _ _ _

/--
lemma `zero_sub` / 引理 `zero_sub`

English:
lemma zero_sub
  given: (t : Multiset α)
  statement: 0 - t = 0
  proof: Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]

中文:
引理 zero_sub
  条件: (t : Multiset α)
  结论: 0 - t = 0
  证明: Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]
-/
protected lemma zero_sub (t : Multiset α) : 0 - t = 0 :=
  Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]
/--
lemma `countP_sub` / 引理 `countP_sub`

English:
lemma countP_sub
  given: {s t : Multiset α}
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ => List.countP_diff hl _

@[simp]

中文:
引理 countP_sub
  条件: {s t : Multiset α}
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ => List.countP_diff hl _

@[simp]

Depends on / 依赖: List.countP_diff, Quotient, Quotient.inductionOn, countP_diff
-/
lemma countP_sub {s t : Multiset α} :
    t <= s -> forall (p : α -> Prop) [DecidablePred p], countP p (s - t) = countP p s - countP p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ => List.countP_diff hl _

@[simp]
/--
lemma `count_sub` / 引理 `count_sub`

English:
lemma count_sub
  given: (a : α) (s t : Multiset α)
  statement: count a (s - t) = count a s - count a t
  proof: Quotient.inductionOn₂ s t by simp [List.count_diff]

中文:
引理 count_sub
  条件: (a : α) (s t : Multiset α)
  结论: count a (s - t) = count a s - count a t
  证明: Quotient.inductionOn₂ s t by simp [List.count_diff]

Depends on / 依赖: List.count_diff, Quotient, Quotient.inductionOn, count_diff
-/
lemma count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t :=
Quotient.inductionOn₂ s t by simp [List.count_diff]

/--
lemma `sub_le_iff_le_add` / 引理 `sub_le_iff_le_add`

English:
lemma sub_le_iff_le_add
  statement: s - t <= u ↔ s <= u + t
  proof: by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]

中文:
引理 sub_le_iff_le_add
  结论: s - t <= u ↔ s <= u + t
  证明: by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]
-/
protected lemma sub_le_iff_le_add : s - t <= u ↔ s <= u + t := by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]

/--
lemma `sub_le_iff_le_add'` / 引理 `sub_le_iff_le_add'`

English:
lemma sub_le_iff_le_add'
  statement: s - t <= u ↔ s <= t + u
  proof: by
  rw [Multiset.sub_le_iff_le_add]; rw [Multiset.add_comm]

中文:
引理 sub_le_iff_le_add'
  结论: s - t <= u ↔ s <= t + u
  证明: by
  rw [Multiset.sub_le_iff_le_add]; rw [Multiset.add_comm]
-/
protected lemma sub_le_iff_le_add' : s - t <= u ↔ s <= t + u := by
  rw [Multiset.sub_le_iff_le_add]; rw [Multiset.add_comm]

/--
theorem `sub_le_self` / 定理 `sub_le_self`

English:
theorem sub_le_self
  given: (s t : Multiset α)
  statement: s - t <= s
  proof: by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _

中文:
定理 sub_le_self
  条件: (s t : Multiset α)
  结论: s - t <= s
  证明: by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _
-/
protected theorem sub_le_self (s t : Multiset α) : s - t <= s := by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _

/--
lemma `add_sub_assoc` / 引理 `add_sub_assoc`

English:
lemma add_sub_assoc
  given: (hut : u <= t)
  statement: s + t - u = s + (t - u)
  proof: by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]

中文:
引理 add_sub_assoc
  条件: (hut : u <= t)
  结论: s + t - u = s + (t - u)
  证明: by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]
-/
protected lemma add_sub_assoc (hut : u <= t) : s + t - u = s + (t - u) := by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]

/--
lemma `add_sub_cancel` / 引理 `add_sub_cancel`

English:
lemma add_sub_cancel
  given: (hts : t <= s)
  statement: s - t + t = s
  proof: by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

中文:
引理 add_sub_cancel
  条件: (hts : t <= s)
  结论: s - t + t = s
  证明: by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]
-/
protected lemma add_sub_cancel (hts : t <= s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

/--
lemma `sub_add_cancel` / 引理 `sub_add_cancel`

English:
lemma sub_add_cancel
  given: (hts : t <= s)
  statement: s - t + t = s
  proof: by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

中文:
引理 sub_add_cancel
  条件: (hts : t <= s)
  结论: s - t + t = s
  证明: by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]
-/
protected lemma sub_add_cancel (hts : t <= s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

/--
lemma `sub_add_eq_sub_sub` / 引理 `sub_add_eq_sub_sub`

English:
lemma sub_add_eq_sub_sub
  statement: s - (t + u) = s - t - u
  proof: by ext; simp [Nat.sub_add_eq]

中文:
引理 sub_add_eq_sub_sub
  结论: s - (t + u) = s - t - u
  证明: by ext; simp [Nat.sub_add_eq]
-/
protected lemma sub_add_eq_sub_sub : s - (t + u) = s - t - u := by ext; simp [Nat.sub_add_eq]

/--
lemma `le_sub_add` / 引理 `le_sub_add`

English:
lemma le_sub_add
  statement: s <= s - t + t
  proof: Multiset.sub_le_iff_le_add.1 le_rfl

中文:
引理 le_sub_add
  结论: s <= s - t + t
  证明: Multiset.sub_le_iff_le_add.1 le_rfl
-/
protected lemma le_sub_add : s <= s - t + t := Multiset.sub_le_iff_le_add.1 le_rfl
/--
lemma `le_add_sub` / 引理 `le_add_sub`

English:
lemma le_add_sub
  statement: s <= t + (s - t)
  proof: Multiset.sub_le_iff_le_add'.1 le_rfl

中文:
引理 le_add_sub
  结论: s <= t + (s - t)
  证明: Multiset.sub_le_iff_le_add'.1 le_rfl
-/
protected lemma le_add_sub : s <= t + (s - t) := Multiset.sub_le_iff_le_add'.1 le_rfl

/--
lemma `sub_le_sub_right` / 引理 `sub_le_sub_right`

English:
lemma sub_le_sub_right
  given: (hst : s <= t)
  statement: s - u <= t - u
  proof: Multiset.sub_le_iff_le_add'.mpr hst.trans Multiset.le_add_sub

中文:
引理 sub_le_sub_right
  条件: (hst : s <= t)
  结论: s - u <= t - u
  证明: Multiset.sub_le_iff_le_add'.mpr hst.trans Multiset.le_add_sub
-/
protected lemma sub_le_sub_right (hst : s <= t) : s - u <= t - u :=
Multiset.sub_le_iff_le_add'.mpr hst.trans Multiset.le_add_sub

/--
lemma `add_sub_cancel_right` / 引理 `add_sub_cancel_right`

English:
lemma add_sub_cancel_right
  statement: s + t - t = s
  proof: by ext a; simp

中文:
引理 add_sub_cancel_right
  结论: s + t - t = s
  证明: by ext a; simp
-/
protected lemma add_sub_cancel_right : s + t - t = s := by ext a; simp

/--
lemma `eq_sub_of_add_eq` / 引理 `eq_sub_of_add_eq`

English:
lemma eq_sub_of_add_eq
  given: (hstu : s + t = u)
  statement: s = u - t
  proof: by
  rw [← hstu]; rw [Multiset.add_sub_cancel_right]

中文:
引理 eq_sub_of_add_eq
  条件: (hstu : s + t = u)
  结论: s = u - t
  证明: by
  rw [← hstu]; rw [Multiset.add_sub_cancel_right]
-/
protected lemma eq_sub_of_add_eq (hstu : s + t = u) : s = u - t := by
  rw [← hstu]; rw [Multiset.add_sub_cancel_right]

/--
lemma `cons_sub_of_le` / 引理 `cons_sub_of_le`

English:
lemma cons_sub_of_le
  given: (a : α) {s t : Multiset α} (h : t <= s)
  statement: a ::ₘ s - t = a ::ₘ (s - t)
  proof: by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_sub_assoc h]

@[simp]

中文:
引理 cons_sub_of_le
  条件: (a : α) {s t : Multiset α} (h : t <= s)
  结论: a ::ₘ s - t = a ::ₘ (s - t)
  证明: by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_sub_assoc h]

@[simp]

Depends on / 依赖: Multiset, Multiset.add_sub_assoc, add_sub_assoc, singleton_add
-/
lemma cons_sub_of_le (a : α) {s t : Multiset α} (h : t <= s) : a ::ₘ s - t = a ::ₘ (s - t) := by
  rw [← singleton_add]; rw [← singleton_add]; rw [Multiset.add_sub_assoc h]

@[simp]
/--
lemma `card_sub` / 引理 `card_sub`

English:
lemma card_sub
  given: {s t : Multiset α} (h : t <= s)
  statement: card (s - t) = card s - card t
  proof: Nat.eq_sub_of_add_eq by rw [← card_add, Multiset.sub_add_cancel h]

中文:
引理 card_sub
  条件: {s t : Multiset α} (h : t <= s)
  结论: card (s - t) = card s - card t
  证明: Nat.eq_sub_of_add_eq by rw [← card_add, Multiset.sub_add_cancel h]

Depends on / 依赖: Multiset, Multiset.sub_add_cancel, Nat.eq_sub_of_add_eq, card_add, eq_sub_of_add_eq, sub_add_cancel
-/
lemma card_sub {s t : Multiset α} (h : t <= s) : card (s - t) = card s - card t :=
Nat.eq_sub_of_add_eq by rw [← card_add, Multiset.sub_add_cancel h]

/--
theorem `sub_singleton` / 定理 `sub_singleton`

English:
theorem sub_singleton
  given: (a : α) (s : Multiset α)
  statement: s - {a} = s.erase a
  proof: by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all

中文:
定理 sub_singleton
  条件: (a : α) (s : Multiset α)
  结论: s - {a} = s.erase a
  证明: by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all
-/
@[simp] theorem sub_singleton (a : α) (s : Multiset α) : s - {a} = s.erase a := by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all

/--
theorem `mem_sub` / 定理 `mem_sub`

English:
theorem mem_sub
  given: {a : α} {s t : Multiset α}
  proof: by
  rw [← count_pos]; rw [count_sub]; rw [Nat.sub_pos_iff_lt]

中文:
定理 mem_sub
  条件: {a : α} {s t : Multiset α}
  证明: by
  rw [← count_pos]; rw [count_sub]; rw [Nat.sub_pos_iff_lt]

Depends on / 依赖: Nat.sub_pos_iff_lt, count_pos, count_sub, sub_pos_iff_lt
-/
theorem mem_sub {a : α} {s t : Multiset α} :
    a in s - t ↔ t.count a < s.count a := by
  rw [← count_pos]; rw [count_sub]; rw [Nat.sub_pos_iff_lt]

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}

/--
theorem `Rel.add` / 定理 `Rel.add`

English:
theorem Rel.add
  given: {s t u v} (hst : Rel r s t) (huv : Rel r u v)
  statement: Rel r (s + u) (t + v)
  proof: by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab

中文:
定理 关系.add
  条件: {s t u v} (hst : 关系 r s t) (huv : 关系 r u v)
  结论: 关系 r (s + u) (t + v)
  证明: by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab

Depends on / 依赖: ih.cons
-/
theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab

/--
theorem `rel_add_left` / 定理 `rel_add_left`

English:
theorem rel_add_left
  given: {as₀ as₁}
  proof: @(Multiset.induction_on as₀ (by simp) fun a s ih bs => by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
    

中文:
定理 rel_add_left
  条件: {as₀ as₁}
  证明: @(Multiset.induction_on as₀ (by simp) fun a s ih bs => by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
    

Depends on / 依赖: Multiset, Multiset.induction_on, cons_add, induction_on, rel_cons_left
-/
theorem rel_add_left {as₀ as₁} :
    forall {bs}, Rel r (as₀ + as₁) bs ↔ exists bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  @(Multiset.induction_on as₀ (by simp) fun a s ih bs => by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩)

/--
theorem `rel_add_right` / 定理 `rel_add_right`

English:
theorem rel_add_right
  given: {as bs₀ bs₁}
  proof: by
  rw [← rel_flip]; rw [rel_add_left]; simp [rel_flip]

中文:
定理 rel_add_right
  条件: {as bs₀ bs₁}
  证明: by
  rw [← rel_flip]; rw [rel_add_left]; simp [rel_flip]

Depends on / 依赖: rel_add_left, rel_flip
-/
theorem rel_add_right {as bs₀ bs₁} :
    Rel r as (bs₀ + bs₁) ↔ exists as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ := by
  rw [← rel_flip]; rw [rel_add_left]; simp [rel_flip]

end Rel

section Nodup

@[simp]
/--
theorem `nodup_singleton` / 定理 `nodup_singleton`

English:
theorem nodup_singleton
  statement: forall a : α, Nodup ({a} : Multiset α)
  proof: List.nodup_singleton

中文:
定理 nodup_singleton
  结论: 对任意 a : α, Nodup ({a} : Multiset α)
  证明: List.nodup_singleton

Depends on / 依赖: List.nodup_singleton, nodup_singleton
-/
theorem nodup_singleton : forall a : α, Nodup ({a} : Multiset α) :=
  List.nodup_singleton

/--
theorem `not_nodup_pair` / 定理 `not_nodup_pair`

English:
theorem not_nodup_pair
  statement: forall a : α, ¬Nodup (a ::ₘ a ::ₘ 0)
  proof: List.not_nodup_pair

中文:
定理 not_nodup_pair
  结论: 对任意 a : α, ¬Nodup (a ::ₘ a ::ₘ 0)
  证明: List.not_nodup_pair

Depends on / 依赖: List.not_nodup_pair, not_nodup_pair
-/
theorem not_nodup_pair : forall a : α, ¬Nodup (a ::ₘ a ::ₘ 0) :=
  List.not_nodup_pair

/--
theorem `Nodup.erase` / 定理 `Nodup.erase`

English:
theorem Nodup.erase
  given: [DecidableEq α] (a : α) {l}
  statement: Nodup l -> Nodup (l.erase a)
  proof: nodup_of_le (erase_le _ _)

中文:
定理 Nodup.erase
  条件: [DecidableEq α] (a : α) {l}
  结论: Nodup l -> Nodup (l.erase a)
  证明: nodup_of_le (erase_le _ _)

Depends on / 依赖: erase_le, nodup_of_le
-/
theorem Nodup.erase [DecidableEq α] (a : α) {l} : Nodup l -> Nodup (l.erase a) :=
  nodup_of_le (erase_le _ _)

/--
theorem `mem_sub_of_nodup` / 定理 `mem_sub_of_nodup`

English:
theorem mem_sub_of_nodup
  given: [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s)
  proof: ⟨fun h =>
    ⟨mem_of_le (Multiset.sub_le_self ..) h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t]; rw [Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le Multiset.le

中文:
定理 mem_sub_of_nodup
  条件: [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s)
  证明: ⟨fun h =>
    ⟨mem_of_le (Multiset.sub_le_self ..) h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t]; rw [Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le Multiset.le

Depends on / 依赖: Multiset, Multiset.le_sub_add, Multiset.sub_le_self, Nat.sub_eq_zero_iff_le, Or.resolve_right, count_eq_zero, count_pos, count_sub, le_sub_add, le_trans, mem_add, mem_of_le, nodup_iff_count_le_one, resolve_right, sub_eq_zero_iff_le, sub_le_self
-/
theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) :
    a in s - t ↔ a in s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le (Multiset.sub_le_self ..) h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t]; rw [Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le Multiset.le_sub_add h₁) h₂⟩

end Nodup

end Multiset
