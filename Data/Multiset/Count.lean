/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Multiset.ZeroCons

/-!
# Counting multiplicity in a multiset

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section

variable (p : α -> Prop) [DecidablePred p]


/-! ### countP -/


/--
Definition of `countP` / `countP` 的定义

English:
definition countP
  signature: (s : Multiset α)
  body: Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]

中文:
定义 countP
  签名: (s : Multiset α)
  定义体: Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]

Depends on / 依赖: List.countP, Perm.countP_eq, Quot.liftOn, countP, countP_eq, liftOn
-/
def countP (s : Multiset α) : Nat :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]
/--
theorem `coe_countP` / 定理 `coe_countP`

English:
theorem coe_countP
  given: (l : List α)
  statement: countP p l = l.countP p
  proof: rfl

@[simp]

中文:
定理 coe_countP
  条件: (l : 列表 α)
  结论: countP p l = l.countP p
  证明: rfl

@[simp]
-/
theorem coe_countP (l : List α) : countP p l = l.countP p :=
  rfl

@[simp]
/--
theorem `countP_zero` / 定理 `countP_zero`

English:
theorem countP_zero
  statement: countP p 0 = 0
  proof: rfl

中文:
定理 countP_zero
  结论: countP p 0 = 0
  证明: rfl
-/
theorem countP_zero : countP p 0 = 0 :=
  rfl

variable {p}

@[simp]
/--
theorem `countP_cons_of_pos` / 定理 `countP_cons_of_pos`

English:
theorem countP_cons_of_pos
  given: {a : α} (s)
  statement: p a -> countP p (a ::ₘ s) = countP p s + 1
  proof: Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_pos (p := (p ·))

@[simp]

中文:
定理 countP_cons_of_pos
  条件: {a : α} (s)
  结论: p a -> countP p (a ::ₘ s) = countP p s + 1
  证明: Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_pos (p := (p ·))

@[simp]

Depends on / 依赖: List.countP_cons_of_pos, Quot.inductionOn, countP_cons_of_pos, inductionOn
-/
theorem countP_cons_of_pos {a : α} (s) : p a -> countP p (a ::ₘ s) = countP p s + 1 :=
Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_pos (p := (p ·))

@[simp]
/--
theorem `countP_cons_of_neg` / 定理 `countP_cons_of_neg`

English:
theorem countP_cons_of_neg
  given: {a : α} (s)
  statement: ¬p a -> countP p (a ::ₘ s) = countP p s
  proof: Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_neg (p := (p ·))

中文:
定理 countP_cons_of_neg
  条件: {a : α} (s)
  结论: ¬p a -> countP p (a ::ₘ s) = countP p s
  证明: Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_neg (p := (p ·))

Depends on / 依赖: List.countP_cons_of_neg, Quot.inductionOn, countP_cons_of_neg, inductionOn
-/
theorem countP_cons_of_neg {a : α} (s) : ¬p a -> countP p (a ::ₘ s) = countP p s :=
Quot.inductionOn s by simpa using fun _ => List.countP_cons_of_neg (p := (p ·))

variable (p)

/--
theorem `countP_cons` / 定理 `countP_cons`

English:
theorem countP_cons
  given: (b : α) (s)
  statement: countP p (b ::ₘ s) = countP p s + if p b then 1 else 0
  proof: Quot.inductionOn s by simp [List.countP_cons]

中文:
定理 countP_cons
  条件: (b : α) (s)
  结论: countP p (b ::ₘ s) = countP p s + if p b then 1 else 0
  证明: Quot.inductionOn s by simp [List.countP_cons]

Depends on / 依赖: List.countP_cons, Quot.inductionOn, countP_cons, inductionOn
-/
theorem countP_cons (b : α) (s) : countP p (b ::ₘ s) = countP p s + if p b then 1 else 0 :=
Quot.inductionOn s by simp [List.countP_cons]

/--
theorem `countP_le_card` / 定理 `countP_le_card`

English:
theorem countP_le_card
  given: (s)
  statement: countP p s <= card s
  proof: Quot.inductionOn s fun _l => countP_le_length (p := (p ·))

中文:
定理 countP_le_card
  条件: (s)
  结论: countP p s <= card s
  证明: Quot.inductionOn s fun _l => countP_le_length (p := (p ·))

Depends on / 依赖: Quot.inductionOn, countP_le_length, inductionOn
-/
theorem countP_le_card (s) : countP p s <= card s :=
  Quot.inductionOn s fun _l => countP_le_length (p := (p ·))

/--
theorem `card_eq_countP_add_countP` / 定理 `card_eq_countP_add_countP`

English:
theorem card_eq_countP_add_countP
  given: (s)
  statement: card s = countP p s + countP (fun x => ¬p x) s
  proof: Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]

中文:
定理 card_eq_countP_add_countP
  条件: (s)
  结论: card s = countP p s + countP (fun x => ¬p x) s
  证明: Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]

Depends on / 依赖: Quot.inductionOn, inductionOn, l.length_eq_countP_add_countP, length_eq_countP_add_countP
-/
theorem card_eq_countP_add_countP (s) : card s = countP p s + countP (fun x => ¬p x) s :=
  Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]
/--
theorem `countP_le_of_le` / 定理 `countP_le_of_le`

English:
theorem countP_le_of_le
  given: {s t} (h : s <= t)
  statement: countP p s <= countP p t
  proof: leInductionOn h fun s => s.countP_le

@[simp]

中文:
定理 countP_le_of_le
  条件: {s t} (h : s <= t)
  结论: countP p s <= countP p t
  证明: leInductionOn h fun s => s.countP_le

@[simp]

Depends on / 依赖: countP_le, leInductionOn, s.countP_le
-/
theorem countP_le_of_le {s t} (h : s <= t) : countP p s <= countP p t :=
  leInductionOn h fun s => s.countP_le

@[simp]
/--
theorem `countP_True` / 定理 `countP_True`

English:
theorem countP_True
  given: {s : Multiset α}
  statement: countP (fun _ => True) s = card s
  proof: Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]

中文:
定理 countP_True
  条件: {s : Multiset α}
  结论: countP (fun _ => 真) s = card s
  证明: Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]

Depends on / 依赖: List.countP_true, Quot.inductionOn, countP_true, inductionOn
-/
theorem countP_True {s : Multiset α} : countP (fun _ => True) s = card s :=
  Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]
/--
theorem `countP_False` / 定理 `countP_False`

English:
theorem countP_False
  given: {s : Multiset α}
  statement: countP (fun _ => False) s = 0
  proof: Quot.inductionOn s fun _l => congrFun List.countP_false _

中文:
定理 countP_False
  条件: {s : Multiset α}
  结论: countP (fun _ => 假) s = 0
  证明: Quot.inductionOn s fun _l => congrFun List.countP_false _

Depends on / 依赖: List.countP_false, Quot.inductionOn, countP_false, inductionOn
-/
theorem countP_False {s : Multiset α} : countP (fun _ => False) s = 0 :=
  Quot.inductionOn s fun _l => congrFun List.countP_false _

/--
lemma `countP_attach` / 引理 `countP_attach`

English:
lemma countP_attach
  given: (s : Multiset α)
  statement: s.attach.countP (fun a : {a // a in s} => p a) = s.countP p
  proof: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP, coe_attach, coe_countP, ← List.countP_attach (l := l)]
    rfl

中文:
引理 countP_attach
  条件: (s : Multiset α)
  结论: s.attach.countP (fun a : {a // a in s} => p a) = s.countP p
  证明: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP, coe_attach, coe_countP, ← List.countP_attach (l := l)]
    rfl

Depends on / 依赖: List.countP_attach, Quotient, Quotient.inductionOn, coe_attach, coe_countP, countP_attach, inductionOn, quot_mk_to_coe
-/
lemma countP_attach (s : Multiset α) : s.attach.countP (fun a : {a // a in s} => p a) = s.countP p :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP, coe_attach, coe_countP, ← List.countP_attach (l := l)]
    rfl

variable {p}

/--
theorem `countP_pos` / 定理 `countP_pos`

English:
theorem countP_pos
  given: {s}
  statement: 0 < countP p s ↔ exists a in s, p a
  proof: Quot.inductionOn s fun _l => by simp

中文:
定理 countP_pos
  条件: {s}
  结论: 0 < countP p s ↔ 存在 a in s, p a
  证明: Quot.inductionOn s fun _l => by simp

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem countP_pos {s} : 0 < countP p s ↔ exists a in s, p a :=
  Quot.inductionOn s fun _l => by simp

/--
theorem `countP_eq_zero` / 定理 `countP_eq_zero`

English:
theorem countP_eq_zero
  given: {s}
  statement: countP p s = 0 ↔ forall a in s, ¬p a
  proof: Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]

中文:
定理 countP_eq_zero
  条件: {s}
  结论: countP p s = 0 ↔ 对任意 a in s, ¬p a
  证明: Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]

Depends on / 依赖: List.countP_eq_zero, Quot.inductionOn, countP_eq_zero, inductionOn
-/
theorem countP_eq_zero {s} : countP p s = 0 ↔ forall a in s, ¬p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]

/--
theorem `countP_eq_card` / 定理 `countP_eq_card`

English:
theorem countP_eq_card
  given: {s}
  statement: countP p s = card s ↔ forall a in s, p a
  proof: Quot.inductionOn s fun _l => by simp [List.countP_eq_length]

中文:
定理 countP_eq_card
  条件: {s}
  结论: countP p s = card s ↔ 对任意 a in s, p a
  证明: Quot.inductionOn s fun _l => by simp [List.countP_eq_length]

Depends on / 依赖: List.countP_eq_length, Quot.inductionOn, countP_eq_length, inductionOn
-/
theorem countP_eq_card {s} : countP p s = card s ↔ forall a in s, p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_length]

/--
theorem `countP_pos_of_mem` / 定理 `countP_pos_of_mem`

English:
theorem countP_pos_of_mem
  given: {s a} (h : a in s) (pa : p a)
  statement: 0 < countP p s
  proof: countP_pos.2 ⟨_, h, pa⟩

@[congr]

中文:
定理 countP_pos_of_mem
  条件: {s a} (h : a in s) (pa : p a)
  结论: 0 < countP p s
  证明: countP_pos.2 ⟨_, h, pa⟩

@[congr]

Depends on / 依赖: countP_pos
-/
theorem countP_pos_of_mem {s a} (h : a in s) (pa : p a) : 0 < countP p s :=
  countP_pos.2 ⟨_, h, pa⟩

@[congr]
/--
theorem `countP_congr` / 定理 `countP_congr`

English:
theorem countP_congr
  statement: {s s' : Multiset α} (hs : s = s')
  proof: by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

中文:
定理 countP_congr
  结论: {s s' : Multiset α} (hs : s = s')
  证明: by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

Depends on / 依赖: Quot.induction_on, coe_eq_coe, countP_congr, hs.countP_congr, quot_mk_to_coe, revert
-/
theorem countP_congr {s s' : Multiset α} (hs : s = s')
    {p p' : α -> Prop} [DecidablePred p] [DecidablePred p']
    (hp : forall x in s, p x = p' x) : s.countP p = s'.countP p' := by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: (a : α)
  body: countP (a = ·)

@[simp]

中文:
定义 count
  签名: (a : α)
  定义体: countP (a = ·)

@[simp]

Depends on / 依赖: countP
-/
def count (a : α) : Multiset α -> Nat :=
  countP (a = ·)

@[simp]
/--
theorem `coe_count` / 定理 `coe_count`

English:
theorem coe_count
  given: (a : α) (l : List α)
  statement: count a (ofList l) = l.count a
  proof: by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]

中文:
定理 coe_count
  条件: (a : α) (l : 列表 α)
  结论: count a (ofList l) = l.count a
  证明: by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]

Depends on / 依赖: List.count, coe_countP, eq_comm, simp_rw
-/
theorem coe_count (a : α) (l : List α) : count a (ofList l) = l.count a := by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]
/--
theorem `count_zero` / 定理 `count_zero`

English:
theorem count_zero
  given: (a : α)
  statement: count a 0 = 0
  proof: rfl

@[simp]

中文:
定理 count_zero
  条件: (a : α)
  结论: count a 0 = 0
  证明: rfl

@[simp]
-/
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl

@[simp]
/--
theorem `count_cons_self` / 定理 `count_cons_self`

English:
theorem count_cons_self
  given: (a : α) (s : Multiset α)
  statement: count a (a ::ₘ s) = count a s + 1
  proof: countP_cons_of_pos _ rfl

@[simp]

中文:
定理 count_cons_self
  条件: (a : α) (s : Multiset α)
  结论: count a (a ::ₘ s) = count a s + 1
  证明: countP_cons_of_pos _ rfl

@[simp]

Depends on / 依赖: countP_cons_of_pos
-/
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = count a s + 1 :=
countP_cons_of_pos _ rfl

@[simp]
/--
theorem `count_cons_of_ne` / 定理 `count_cons_of_ne`

English:
theorem count_cons_of_ne
  given: {a b : α} (h : a != b) (s : Multiset α)
  statement: count a (b ::ₘ s) = count a s
  proof: countP_cons_of_neg _ h

中文:
定理 count_cons_of_ne
  条件: {a b : α} (h : a != b) (s : Multiset α)
  结论: count a (b ::ₘ s) = count a s
  证明: countP_cons_of_neg _ h

Depends on / 依赖: countP_cons_of_neg
-/
theorem count_cons_of_ne {a b : α} (h : a != b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
countP_cons_of_neg _ h

/--
theorem `count_le_card` / 定理 `count_le_card`

English:
theorem count_le_card
  given: (a : α) (s)
  statement: count a s <= card s
  proof: countP_le_card _ _

@[gcongr]

中文:
定理 count_le_card
  条件: (a : α) (s)
  结论: count a s <= card s
  证明: countP_le_card _ _

@[gcongr]

Depends on / 依赖: countP_le_card
-/
theorem count_le_card (a : α) (s) : count a s <= card s :=
  countP_le_card _ _

@[gcongr]
/--
theorem `count_le_of_le` / 定理 `count_le_of_le`

English:
theorem count_le_of_le
  given: (a : α) {s t}
  statement: s <= t -> count a s <= count a t
  proof: countP_le_of_le _

中文:
定理 count_le_of_le
  条件: (a : α) {s t}
  结论: s <= t -> count a s <= count a t
  证明: countP_le_of_le _

Depends on / 依赖: countP_le_of_le
-/
theorem count_le_of_le (a : α) {s t} : s <= t -> count a s <= count a t :=
  countP_le_of_le _

/--
theorem `count_le_count_cons` / 定理 `count_le_count_cons`

English:
theorem count_le_count_cons
  given: (a b : α) (s : Multiset α)
  statement: count a s <= count a (b ::ₘ s)
  proof: count_le_of_le _ (le_cons_self _ _)

中文:
定理 count_le_count_cons
  条件: (a b : α) (s : Multiset α)
  结论: count a s <= count a (b ::ₘ s)
  证明: count_le_of_le _ (le_cons_self _ _)

Depends on / 依赖: count_le_of_le, le_cons_self
-/
theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s <= count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)

/--
theorem `count_cons` / 定理 `count_cons`

English:
theorem count_cons
  given: (a b : α) (s : Multiset α)
  proof: countP_cons (a = ·) _ _

中文:
定理 count_cons
  条件: (a b : α) (s : Multiset α)
  证明: countP_cons (a = ·) _ _

Depends on / 依赖: countP_cons
-/
theorem count_cons (a b : α) (s : Multiset α) :
    count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countP_cons (a = ·) _ _

/--
theorem `count_singleton_self` / 定理 `count_singleton_self`

English:
theorem count_singleton_self
  given: (a : α)
  statement: count a ({a} : Multiset α) = 1
  proof: count_eq_one_of_mem (nodup_singleton a) mem_singleton_self a

中文:
定理 count_singleton_self
  条件: (a : α)
  结论: count a ({a} : Multiset α) = 1
  证明: count_eq_one_of_mem (nodup_singleton a) mem_singleton_self a

Depends on / 依赖: count_eq_one_of_mem, mem_singleton_self, nodup_singleton
-/
theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 :=
count_eq_one_of_mem (nodup_singleton a) mem_singleton_self a

/--
theorem `count_singleton` / 定理 `count_singleton`

English:
theorem count_singleton
  given: (a b : α)
  statement: count a ({b} : Multiset α) = if a = b then 1 else 0
  proof: by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]

中文:
定理 count_singleton
  条件: (a b : α)
  结论: count a ({b} : Multiset α) = if a = b then 1 else 0
  证明: by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]

Depends on / 依赖: Nat.zero_add, cons_zero, count_cons, count_zero, zero_add
-/
theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]
/--
lemma `count_attach` / 引理 `count_attach`

English:
lemma count_attach
  given: (a : {x // x in s})
  statement: s.attach.count a = s.count ↑a
  proof: Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) countP_attach _ _

中文:
引理 count_attach
  条件: (a : {x // x in s})
  结论: s.attach.count a = s.count ↑a
  证明: Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) countP_attach _ _

Depends on / 依赖: Eq.trans, Subtype, Subtype.ext_iff, countP_attach, countP_congr, ext_iff
-/
lemma count_attach (a : {x // x in s}) : s.attach.count a = s.count ↑a :=
Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) countP_attach _ _

/--
theorem `count_pos` / 定理 `count_pos`

English:
theorem count_pos
  given: {a : α} {s : Multiset α}
  statement: 0 < count a s ↔ a in s
  proof: by simp [count, countP_pos]

中文:
定理 count_pos
  条件: {a : α} {s : Multiset α}
  结论: 0 < count a s ↔ a in s
  证明: by simp [count, countP_pos]

Depends on / 依赖: countP_pos
-/
theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a in s := by simp [count, countP_pos]

/--
theorem `one_le_count_iff_mem` / 定理 `one_le_count_iff_mem`

English:
theorem one_le_count_iff_mem
  given: {a : α} {s : Multiset α}
  statement: 1 <= count a s ↔ a in s
  proof: by
  rw [succ_le_iff]; rw [count_pos]

@[simp]

中文:
定理 one_le_count_iff_mem
  条件: {a : α} {s : Multiset α}
  结论: 1 <= count a s ↔ a in s
  证明: by
  rw [succ_le_iff]; rw [count_pos]

@[simp]

Depends on / 依赖: count_pos, succ_le_iff
-/
theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 <= count a s ↔ a in s := by
  rw [succ_le_iff]; rw [count_pos]

@[simp]
/--
theorem `count_eq_zero_of_notMem` / 定理 `count_eq_zero_of_notMem`

English:
theorem count_eq_zero_of_notMem
  given: {a : α} {s : Multiset α} (h : a ∉ s)
  statement: count a s = 0
  proof: by_contradiction fun h' => h count_pos.1 (Nat.pos_of_ne_zero h')

中文:
定理 count_eq_zero_of_notMem
  条件: {a : α} {s : Multiset α} (h : a ∉ s)
  结论: count a s = 0
  证明: by_contradiction fun h' => h count_pos.1 (Nat.pos_of_ne_zero h')

Depends on / 依赖: Nat.pos_of_ne_zero, by_contradiction, count_pos, pos_of_ne_zero
-/
theorem count_eq_zero_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
by_contradiction fun h' => h count_pos.1 (Nat.pos_of_ne_zero h')

/--
lemma `count_ne_zero` / 引理 `count_ne_zero`

English:
lemma count_ne_zero
  given: {a : α}
  statement: count a s != 0 ↔ a in s
  proof: Nat.pos_iff_ne_zero.symm.trans count_pos

中文:
引理 count_ne_zero
  条件: {a : α}
  结论: count a s != 0 ↔ a in s
  证明: Nat.pos_iff_ne_zero.symm.trans count_pos

Depends on / 依赖: Nat.pos_iff_ne_zero.symm.trans, count_pos, pos_iff_ne_zero
-/
lemma count_ne_zero {a : α} : count a s != 0 ↔ a in s := Nat.pos_iff_ne_zero.symm.trans count_pos

/--
lemma `count_eq_zero` / 引理 `count_eq_zero`

English:
lemma count_eq_zero
  given: {a : α}
  statement: count a s = 0 ↔ a ∉ s
  proof: count_ne_zero.not_right

中文:
引理 count_eq_zero
  条件: {a : α}
  结论: count a s = 0 ↔ a ∉ s
  证明: count_ne_zero.not_right
-/
@[simp] lemma count_eq_zero {a : α} : count a s = 0 ↔ a ∉ s := count_ne_zero.not_right

/--
theorem `count_eq_card` / 定理 `count_eq_card`

English:
theorem count_eq_card
  given: {a : α} {s}
  statement: count a s = card s ↔ forall x in s, a = x
  proof: by
  simp [countP_eq_card, count, @eq_comm _ a]

中文:
定理 count_eq_card
  条件: {a : α} {s}
  结论: count a s = card s ↔ 对任意 x in s, a = x
  证明: by
  simp [countP_eq_card, count, @eq_comm _ a]

Depends on / 依赖: countP_eq_card, eq_comm
-/
theorem count_eq_card {a : α} {s} : count a s = card s ↔ forall x in s, a = x := by
  simp [countP_eq_card, count, @eq_comm _ a]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : Multiset α}
  statement: s = t ↔ forall a, count a s = count a t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans by
    simp only [quot_mk_to_coe, coe_count]
    apply perm_iff_count

@[ext]

中文:
定理 ext
  条件: {s t : Multiset α}
  结论: s = t ↔ 对任意 a, count a s = count a t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans by
    simp only [quot_mk_to_coe, coe_count]
    apply perm_iff_count

@[ext]

Depends on / 依赖: Quotient, Quotient.eq.trans, Quotient.inductionOn, coe_count, perm_iff_count, quot_mk_to_coe
-/
theorem ext {s t : Multiset α} : s = t ↔ forall a, count a s = count a t :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans by
    simp only [quot_mk_to_coe, coe_count]
    apply perm_iff_count

@[ext]
/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {s t : Multiset α}
  statement: (forall a, count a s = count a t) -> s = t
  proof: ext.2

中文:
定理 ext'
  条件: {s t : Multiset α}
  结论: (对任意 a, count a s = count a t) -> s = t
  证明: ext.2
-/
theorem ext' {s t : Multiset α} : (forall a, count a s = count a t) -> s = t :=
  ext.2

/--
lemma `count_injective` / 引理 `count_injective`

English:
lemma count_injective
  statement: Injective fun (s : Multiset α) a => s.count a
  proof: fun _s _t hst => ext' congr_fun hst

中文:
引理 count_injective
  结论: 单射 fun (s : Multiset α) a => s.count a
  证明: fun _s _t hst => ext' congr_fun hst

Depends on / 依赖: congr_fun
-/
lemma count_injective : Injective fun (s : Multiset α) a => s.count a :=
fun _s _t hst => ext' congr_fun hst

/--
theorem `le_iff_count` / 定理 `le_iff_count`

English:
theorem le_iff_count
  given: {s t : Multiset α}
  statement: s <= t ↔ forall a, count a s <= count a t
  proof: Quotient.inductionOn₂ s t fun _ _ => by simp [subperm_iff_count]

中文:
定理 le_iff_count
  条件: {s t : Multiset α}
  结论: s <= t ↔ 对任意 a, count a s <= count a t
  证明: Quotient.inductionOn₂ s t fun _ _ => by simp [subperm_iff_count]

Depends on / 依赖: Quotient, Quotient.inductionOn, subperm_iff_count
-/
theorem le_iff_count {s t : Multiset α} : s <= t ↔ forall a, count a s <= count a t :=
  Quotient.inductionOn₂ s t fun _ _ => by simp [subperm_iff_count]

end

/-! ### Lift a relation to `Multiset`s -/

section Rel

variable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}

/--
theorem `Rel.countP_eq` / 定理 `Rel.countP_eq`

English:
theorem Rel.countP_eq
  statement: (r : α -> α -> Prop) [IsTrans α r] [Std.Symm r] {s t : Multiset α} (x : α)
  proof: by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [rel_zero_left.mp h]
  | cons y s ih =>
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons]; rw [countP_cons]; rw [ih hb2]
    simp only [Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

中文:
定理 关系.countP_eq
  结论: (r : α -> α -> 命题) [是Trans α r] [Std.Symm r] {s t : Multiset α} (x : α)
  证明: by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [rel_zero_left.mp h]
  | cons y s ih =>
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons]; rw [countP_cons]; rw [ih hb2]
    simp only [Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

Depends on / 依赖: Multiset, Multiset.induction_on, Nat.add_right_inj, _root_, _root_.trans, add_right_inj, countP_cons, generalizing, if_congr, induction_on, rel_cons_left, rel_cons_left.mp, rel_zero_left, rel_zero_left.mp
-/
theorem Rel.countP_eq (r : α -> α -> Prop) [IsTrans α r] [Std.Symm r] {s t : Multiset α} (x : α)
    [DecidablePred (r x)] (h : Rel r s t) : countP (r x) s = countP (r x) t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [rel_zero_left.mp h]
  | cons y s ih =>
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons]; rw [countP_cons]; rw [ih hb2]
    simp only [Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

end Rel

section Nodup

variable {s : Multiset α} {a : α}

/--
theorem `nodup_iff_count_le_one` / 定理 `nodup_iff_count_le_one`

English:
theorem nodup_iff_count_le_one
  given: [DecidableEq α] {s : Multiset α}
  statement: Nodup s ↔ forall a, count a s <= 1
  proof: Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, coe_count]
    exact List.nodup_iff_count_le_one

中文:
定理 nodup_iff_count_le_one
  条件: [DecidableEq α] {s : Multiset α}
  结论: Nodup s ↔ 对任意 a, count a s <= 1
  证明: Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, coe_count]
    exact List.nodup_iff_count_le_one

Depends on / 依赖: List.nodup_iff_count_le_one, Quot.induction_on, coe_count, coe_nodup, induction_on, nodup_iff_count_le_one, quot_mk_to_coe
-/
theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ forall a, count a s <= 1 :=
  Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, coe_count]
    exact List.nodup_iff_count_le_one

/--
theorem `nodup_iff_count_eq_one` / 定理 `nodup_iff_count_eq_one`

English:
theorem nodup_iff_count_eq_one
  given: [DecidableEq α]
  statement: Nodup s ↔ forall a in s, count a s = 1
  proof: Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]

中文:
定理 nodup_iff_count_eq_one
  条件: [DecidableEq α]
  结论: Nodup s ↔ 对任意 a in s, count a s = 1
  证明: Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]

Depends on / 依赖: List.nodup_iff_count_eq_one, Quot.induction_on, induction_on, nodup_iff_count_eq_one
-/
theorem nodup_iff_count_eq_one [DecidableEq α] : Nodup s ↔ forall a in s, count a s = 1 :=
  Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]
/--
theorem `count_eq_one_of_mem` / 定理 `count_eq_one_of_mem`

English:
theorem count_eq_one_of_mem
  given: [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a in s)
  proof: nodup_iff_count_eq_one.mp d a h

中文:
定理 count_eq_one_of_mem
  条件: [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a in s)
  证明: nodup_iff_count_eq_one.mp d a h

Depends on / 依赖: nodup_iff_count_eq_one, nodup_iff_count_eq_one.mp
-/
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a in s) :
    count a s = 1 :=
  nodup_iff_count_eq_one.mp d a h

/--
theorem `count_eq_of_nodup` / 定理 `count_eq_of_nodup`

English:
theorem count_eq_of_nodup
  given: [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s)
  proof: by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_notMem h

中文:
定理 count_eq_of_nodup
  条件: [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s)
  证明: by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_notMem h

Depends on / 依赖: count_eq_one_of_mem, count_eq_zero_of_notMem, exists_mem, isEmptyElim, split_ifs
-/
theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
    count a s = if a in s then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_notMem h

end Nodup

end Multiset
