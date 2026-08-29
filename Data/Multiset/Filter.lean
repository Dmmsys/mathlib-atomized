/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Rudy Peterson
-/
module

public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Hom.Basic

/-!
# Filtering multisets by a predicate

## Main definitions

* `Multiset.filter`: `filter p s` is the multiset of elements in `s` that satisfy `p`.
* `Multiset.filterMap`: `filterMap f s` is the multiset of `b`s where `some b ∈ map f s`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.filter` -/


section

variable (p : α -> Prop) [DecidablePred p]

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (s : Multiset α)
  body: Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound h.filter p

中文:
定义 filter
  签名: (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound h.filter p

Depends on / 依赖: List.filter, Multiset, Quot.liftOn, Quot.sound, filter, h.filter, liftOn
-/
def filter (s : Multiset α) : Multiset α :=
Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound h.filter p

/--
lemma `filter_coe` / 引理 `filter_coe`

English:
lemma filter_coe
  given: (l : List α)
  statement: filter p l = l.filter p
  proof: rfl

@[simp]

中文:
引理 filter_coe
  条件: (l : 列表 α)
  结论: filter p l = l.filter p
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma filter_coe (l : List α) : filter p l = l.filter p := rfl

@[simp]
/--
theorem `filter_zero` / 定理 `filter_zero`

English:
theorem filter_zero
  statement: filter p 0 = 0
  proof: rfl

@[congr]

中文:
定理 filter_zero
  结论: filter p 0 = 0
  证明: rfl

@[congr]
-/
theorem filter_zero : filter p 0 = 0 :=
  rfl

@[congr]
/--
theorem `filter_congr` / 定理 `filter_congr`

English:
theorem filter_congr
  given: {p q : α -> Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α}
  proof: Quot.inductionOn s fun _l h => congr_arg ofList List.filter_congr by simpa using h

@[simp]

中文:
定理 filter_congr
  条件: {p q : α -> 命题} [DecidablePred p] [DecidablePred q] {s : Multiset α}
  证明: Quot.inductionOn s fun _l h => congr_arg ofList List.filter_congr by simpa using h

@[simp]

Depends on / 依赖: List.filter_congr, Quot.inductionOn, congr_arg, filter_congr, inductionOn, ofList
-/
theorem filter_congr {p q : α -> Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (forall x in s, p x ↔ q x) -> filter p s = filter q s :=
Quot.inductionOn s fun _l h => congr_arg ofList List.filter_congr by simpa using h

@[simp]
/--
theorem `filter_add` / 定理 `filter_add`

English:
theorem filter_add
  given: (s t : Multiset α)
  statement: filter p (s + t) = filter p s + filter p t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filter_append _ _

@[simp]

中文:
定理 filter_add
  条件: (s t : Multiset α)
  结论: filter p (s + t) = filter p s + filter p t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filter_append _ _

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, filter_append, ofList
-/
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filter_append _ _

@[simp]
/--
theorem `filter_le` / 定理 `filter_le`

English:
theorem filter_le
  given: (s : Multiset α)
  statement: filter p s <= s
  proof: Quot.inductionOn s fun _l => filter_sublist.subperm

@[simp]

中文:
定理 filter_le
  条件: (s : Multiset α)
  结论: filter p s <= s
  证明: Quot.inductionOn s fun _l => filter_sublist.subperm

@[simp]

Depends on / 依赖: Quot.inductionOn, filter_sublist, filter_sublist.subperm, inductionOn, subperm
-/
theorem filter_le (s : Multiset α) : filter p s <= s :=
  Quot.inductionOn s fun _l => filter_sublist.subperm

@[simp]
/--
theorem `filter_subset` / 定理 `filter_subset`

English:
theorem filter_subset
  given: (s : Multiset α)
  statement: filter p s subseteq s
  proof: subset_of_le filter_le _ _

@[gcongr]

中文:
定理 filter_subset
  条件: (s : Multiset α)
  结论: filter p s subseteq s
  证明: subset_of_le filter_le _ _

@[gcongr]

Depends on / 依赖: filter_le, subset_of_le
-/
theorem filter_subset (s : Multiset α) : filter p s subseteq s :=
subset_of_le filter_le _ _

@[gcongr]
/--
theorem `filter_le_filter` / 定理 `filter_le_filter`

English:
theorem filter_le_filter
  given: {s t} (h : s <= t)
  statement: filter p s <= filter p t
  proof: leInductionOn h fun h => (h.filter (p ·)).subperm

中文:
定理 filter_le_filter
  条件: {s t} (h : s <= t)
  结论: filter p s <= filter p t
  证明: leInductionOn h fun h => (h.filter (p ·)).subperm

Depends on / 依赖: filter, h.filter, leInductionOn, subperm
-/
theorem filter_le_filter {s t} (h : s <= t) : filter p s <= filter p t :=
  leInductionOn h fun h => (h.filter (p ·)).subperm

/--
theorem `monotone_filter_left` / 定理 `monotone_filter_left`

English:
theorem monotone_filter_left
  statement: Monotone (filter p)
  proof: fun _s _t => filter_le_filter p

中文:
定理 monotone_filter_left
  结论: 递增 (filter p)
  证明: fun _s _t => filter_le_filter p

Depends on / 依赖: filter_le_filter
-/
theorem monotone_filter_left : Monotone (filter p) := fun _s _t => filter_le_filter p

/--
theorem `monotone_filter_right` / 定理 `monotone_filter_right`

English:
theorem monotone_filter_right
  given: (s : Multiset α) ⦃p q
  statement: α -> Prop⦄ [DecidablePred p] [DecidablePred q]
  proof: Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

中文:
定理 monotone_filter_right
  条件: (s : Multiset α) ⦃p q
  结论: α -> 命题⦄ [DecidablePred p] [DecidablePred q]
  证明: Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, l.monotone_filter_right, monotone_filter_right, subperm
-/
theorem monotone_filter_right (s : Multiset α) ⦃p q : α -> Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : forall b, p b -> q b) :
    s.filter p <= s.filter q :=
  Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

variable {p}

@[simp]
/--
theorem `filter_cons_of_pos` / 定理 `filter_cons_of_pos`

English:
theorem filter_cons_of_pos
  given: {a : α} (s)
  statement: p a -> filter p (a ::ₘ s) = a ::ₘ filter p s
  proof: Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_pos by simpa using h

@[simp]

中文:
定理 filter_cons_of_pos
  条件: {a : α} (s)
  结论: p a -> filter p (a ::ₘ s) = a ::ₘ filter p s
  证明: Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_pos by simpa using h

@[simp]

Depends on / 依赖: List.filter_cons_of_pos, Quot.inductionOn, congr_arg, filter_cons_of_pos, inductionOn, ofList
-/
theorem filter_cons_of_pos {a : α} (s) : p a -> filter p (a ::ₘ s) = a ::ₘ filter p s :=
Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_pos by simpa using h

@[simp]
/--
theorem `filter_cons_of_neg` / 定理 `filter_cons_of_neg`

English:
theorem filter_cons_of_neg
  given: {a : α} (s)
  statement: ¬p a -> filter p (a ::ₘ s) = filter p s
  proof: Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_neg by simpa using h

@[simp]

中文:
定理 filter_cons_of_neg
  条件: {a : α} (s)
  结论: ¬p a -> filter p (a ::ₘ s) = filter p s
  证明: Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_neg by simpa using h

@[simp]

Depends on / 依赖: List.filter_cons_of_neg, Quot.inductionOn, congr_arg, filter_cons_of_neg, inductionOn, ofList
-/
theorem filter_cons_of_neg {a : α} (s) : ¬p a -> filter p (a ::ₘ s) = filter p s :=
Quot.inductionOn s fun _ h => congr_arg ofList List.filter_cons_of_neg by simpa using h

@[simp]
/--
theorem `mem_filter` / 定理 `mem_filter`

English:
theorem mem_filter
  given: {a : α} {s}
  statement: a in filter p s ↔ a in s ∧ p a
  proof: Quot.inductionOn s fun _l => by simp

中文:
定理 mem_filter
  条件: {a : α} {s}
  结论: a in filter p s ↔ a in s ∧ p a
  证明: Quot.inductionOn s fun _l => by simp

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧ p a :=
  Quot.inductionOn s fun _l => by simp

/--
theorem `of_mem_filter` / 定理 `of_mem_filter`

English:
theorem of_mem_filter
  given: {a : α} {s} (h : a in filter p s)
  statement: p a
  proof: (mem_filter.1 h).2

中文:
定理 of_mem_filter
  条件: {a : α} {s} (h : a in filter p s)
  结论: p a
  证明: (mem_filter.1 h).2

Depends on / 依赖: mem_filter
-/
theorem of_mem_filter {a : α} {s} (h : a in filter p s) : p a :=
  (mem_filter.1 h).2

/--
theorem `mem_of_mem_filter` / 定理 `mem_of_mem_filter`

English:
theorem mem_of_mem_filter
  given: {a : α} {s} (h : a in filter p s)
  statement: a in s
  proof: (mem_filter.1 h).1

中文:
定理 mem_of_mem_filter
  条件: {a : α} {s} (h : a in filter p s)
  结论: a in s
  证明: (mem_filter.1 h).1

Depends on / 依赖: mem_filter
-/
theorem mem_of_mem_filter {a : α} {s} (h : a in filter p s) : a in s :=
  (mem_filter.1 h).1

/--
theorem `mem_filter_of_mem` / 定理 `mem_filter_of_mem`

English:
theorem mem_filter_of_mem
  given: {a : α} {l} (m : a in l) (h : p a)
  statement: a in filter p l
  proof: mem_filter.2 ⟨m, h⟩

@[simp]

中文:
定理 mem_filter_of_mem
  条件: {a : α} {l} (m : a in l) (h : p a)
  结论: a in filter p l
  证明: mem_filter.2 ⟨m, h⟩

@[simp]

Depends on / 依赖: mem_filter
-/
theorem mem_filter_of_mem {a : α} {l} (m : a in l) (h : p a) : a in filter p l :=
  mem_filter.2 ⟨m, h⟩

@[simp]
/--
theorem `filter_eq_self` / 定理 `filter_eq_self`

English:
theorem filter_eq_self
  given: {s}
  statement: filter p s = s ↔ forall a in s, p a
  proof: Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => filter_sublist.eq_of_length (congr_arg card h),
congr_arg ofList⟩ by simp

@[simp]

中文:
定理 filter_eq_self
  条件: {s}
  结论: filter p s = s ↔ 对任意 a in s, p a
  证明: Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => filter_sublist.eq_of_length (congr_arg card h),
congr_arg ofList⟩ by simp

@[simp]

Depends on / 依赖: Iff.trans, Quot.inductionOn, congr_arg, eq_of_length, filter_sublist, filter_sublist.eq_of_length, inductionOn, ofList
-/
theorem filter_eq_self {s} : filter p s = s ↔ forall a in s, p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => filter_sublist.eq_of_length (congr_arg card h),
congr_arg ofList⟩ by simp

@[simp]
/--
theorem `filter_eq_nil` / 定理 `filter_eq_nil`

English:
theorem filter_eq_nil
  given: {s}
  statement: filter p s = 0 ↔ forall a in s, ¬p a
  proof: Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

@[simp]

中文:
定理 filter_eq_nil
  条件: {s}
  结论: filter p s = 0 ↔ 对任意 a in s, ¬p a
  证明: Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

@[simp]

Depends on / 依赖: Iff.trans, Quot.inductionOn, congr_arg, eq_nil_of_length_eq_zero, inductionOn, ofList
-/
theorem filter_eq_nil {s} : filter p s = 0 ↔ forall a in s, ¬p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

@[simp]
/--
lemma `filter_true` / 引理 `filter_true`

English:
lemma filter_true
  given: (s : Multiset α)
  statement: s.filter (fun _ => True) = s
  proof: by simp

@[simp]

中文:
引理 filter_true
  条件: (s : Multiset α)
  结论: s.filter (fun _ => 真) = s
  证明: by simp

@[simp]
-/
lemma filter_true (s : Multiset α) : s.filter (fun _ => True) = s := by simp

@[simp]
/--
lemma `filter_false` / 引理 `filter_false`

English:
lemma filter_false
  given: (s : Multiset α)
  statement: s.filter (fun _ => False) = 0
  proof: by simp

中文:
引理 filter_false
  条件: (s : Multiset α)
  结论: s.filter (fun _ => 假) = 0
  证明: by simp
-/
lemma filter_false (s : Multiset α) : s.filter (fun _ => False) = 0 := by simp

/--
theorem `le_filter` / 定理 `le_filter`

English:
theorem le_filter
  given: {s t}
  statement: s <= filter p t ↔ s <= t ∧ forall a in s, p a
  proof: ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

中文:
定理 le_filter
  条件: {s t}
  结论: s <= filter p t ↔ s <= t ∧ 对任意 a in s, p a
  证明: ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

Depends on / 依赖: filter_eq_self, filter_le, filter_le_filter, le_trans, mem_of_le, of_mem_filter
-/
theorem le_filter {s t} : s <= filter p t ↔ s <= t ∧ forall a in s, p a :=
  ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

/--
theorem `filter_cons` / 定理 `filter_cons`

English:
theorem filter_cons
  given: {a : α} (s : Multiset α)
  proof: by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]

中文:
定理 filter_cons
  条件: {a : α} (s : Multiset α)
  证明: by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]

Depends on / 依赖: Multiset, Multiset.zero_add, filter_cons_of_neg, filter_cons_of_pos, singleton_add, split_ifs, zero_add
-/
theorem filter_cons {a : α} (s : Multiset α) :
    filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]

/--
theorem `filter_singleton` / 定理 `filter_singleton`

English:
theorem filter_singleton
  given: {a : α} (p : α -> Prop) [DecidablePred p]
  proof: by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

中文:
定理 filter_singleton
  条件: {a : α} (p : α -> 命题) [DecidablePred p]
  证明: by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

Depends on / 依赖: Multiset, Multiset.add_zero, add_zero, empty_eq_zero, filter_cons, filter_zero, singleton
-/
theorem filter_singleton {a : α} (p : α -> Prop) [DecidablePred p] :
    filter p {a} = if p a then {a} else ∅ := by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

variable (p)

@[simp]
/--
theorem `filter_filter` / 定理 `filter_filter`

English:
theorem filter_filter
  given: (q) [DecidablePred q] (s : Multiset α)
  proof: Quot.inductionOn s fun l => by simp

中文:
定理 filter_filter
  条件: (q) [DecidablePred q] (s : Multiset α)
  证明: Quot.inductionOn s fun l => by simp

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  Quot.inductionOn s fun l => by simp

/--
lemma `filter_comm` / 引理 `filter_comm`

English:
lemma filter_comm
  given: (q) [DecidablePred q] (s : Multiset α)
  proof: by simp [and_comm]

中文:
引理 filter_comm
  条件: (q) [DecidablePred q] (s : Multiset α)
  证明: by simp [and_comm]

Depends on / 依赖: and_comm
-/
lemma filter_comm (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter q (filter p s) := by simp [and_comm]

/--
theorem `filter_add_filter` / 定理 `filter_add_filter`

English:
theorem filter_add_filter
  given: (q) [DecidablePred q] (s : Multiset α)
  proof: Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]

中文:
定理 filter_add_filter
  条件: (q) [DecidablePred q] (s : Multiset α)
  证明: Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]

/--
theorem `filter_add_not` / 定理 `filter_add_not`

English:
theorem filter_add_not
  given: (s : Multiset α)
  statement: filter p s + filter (fun a => ¬p a) s = s
  proof: by
  rw [filter_add_filter]; rw [filter_eq_self.2]; rw [filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [-Bool.not_eq_true, -not_and]
  · simp only [implies_true, Decidable.em]

中文:
定理 filter_add_not
  条件: (s : Multiset α)
  结论: filter p s + filter (fun a => ¬p a) s = s
  证明: by
  rw [filter_add_filter]; rw [filter_eq_self.2]; rw [filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [-Bool.not_eq_true, -not_and]
  · simp only [implies_true, Decidable.em]

Depends on / 依赖: Bool.not_eq_true, Decidable, Decidable.em, Multiset, Multiset.add_zero, add_zero, filter_add_filter, filter_eq_nil, filter_eq_self, implies_true, not_and, not_eq_true
-/
theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter]; rw [filter_eq_self.2]; rw [filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [-Bool.not_eq_true, -not_and]
  · simp only [implies_true, Decidable.em]

/--
theorem `filter_map` / 定理 `filter_map`

English:
theorem filter_map
  given: (f : β -> α) (s : Multiset β)
  statement: filter p (map f s) = map f (filter (p ∘ f) s)
  proof: Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

中文:
定理 filter_map
  条件: (f : β -> α) (s : Multiset β)
  结论: filter p (map f s) = map f (filter (p ∘ f) s)
  证明: Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

Depends on / 依赖: List.filter_map, Quot.inductionOn, filter_map, inductionOn
-/
theorem filter_map (f : β -> α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

-- TODO: rename to `map_filter` when the deprecated alias above is removed.
/--
lemma `map_filter'` / 引理 `map_filter'`

English:
lemma map_filter'
  statement: {f : α -> β} (hf : Injective f) (s : Multiset α)
  proof: by
  simp [filter_map, hf.eq_iff]

中文:
引理 map_filter'
  结论: {f : α -> β} (hf : 单射 f) (s : Multiset α)
  证明: by
  simp [filter_map, hf.eq_iff]

Depends on / 依赖: eq_iff, filter_map, hf.eq_iff
-/
lemma map_filter' {f : α -> β} (hf : Injective f) (s : Multiset α)
    [DecidablePred fun b => exists a, p a ∧ f a = b] :
    (s.filter p).map f = (s.map f).filter fun b => exists a, p a ∧ f a = b := by
  simp [filter_map, hf.eq_iff]

/--
lemma `card_filter_le_iff` / 引理 `card_filter_le_iff`

English:
lemma card_filter_le_iff
  given: (s : Multiset α) (P : α -> Prop) [DecidablePred P] (n : Nat)
  proof: by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
.trans H have card := card_le_card (monotone_filter_left P hs')
    exact s'_card.not_ge (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H => ⟨s.filter P, filter_le _ _, H, fun a ha => (mem_filter.mp ha).2⟩

中文:
引理 card_filter_le_iff
  条件: (s : Multiset α) (P : α -> 命题) [DecidablePred P] (n : 自然数)
  证明: by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
.trans H have card := card_le_card (monotone_filter_left P hs')
    exact s'_card.not_ge (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H => ⟨s.filter P, filter_le _ _, H, fun a ha => (mem_filter.mp ha).2⟩

Depends on / 依赖: _card, _card.not_ge, card_le_card, contrapose, fconstructor, filter, filter_eq_self, filter_eq_self.mpr, filter_le, mem_filter, mem_filter.mp, monotone_filter_left, not_ge, s.filter
-/
lemma card_filter_le_iff (s : Multiset α) (P : α -> Prop) [DecidablePred P] (n : Nat) :
    card (s.filter P) <= n ↔ forall s' <= s, n < card s' -> exists a in s', ¬ P a := by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
.trans H have card := card_le_card (monotone_filter_left P hs')
    exact s'_card.not_ge (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H => ⟨s.filter P, filter_le _ _, H, fun a ha => (mem_filter.mp ha).2⟩

/-! ### Simultaneously filter and map elements of a multiset -/


/--
Definition of `filterMap` / `filterMap` 的定义

English:
definition filterMap
  signature: (f : α -> Option β) (s : Multiset α)
  body: Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
fun _l₁ _l₂ h => Quot.sound h.filterMap f

@[simp, norm_cast]

中文:
定义 filterMap
  签名: (f : α -> 选项类型 β) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
fun _l₁ _l₂ h => Quot.sound h.filterMap f

@[simp, norm_cast]

Depends on / 依赖: List.filterMap, Multiset, Quot.liftOn, Quot.sound, filterMap, h.filterMap, liftOn
-/
def filterMap (f : α -> Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
fun _l₁ _l₂ h => Quot.sound h.filterMap f

@[simp, norm_cast]
/--
lemma `filterMap_coe` / 引理 `filterMap_coe`

English:
lemma filterMap_coe
  given: (f : α -> Option β) (l : List α)
  statement: filterMap f l = l.filterMap f
  proof: rfl

@[simp]

中文:
引理 filterMap_coe
  条件: (f : α -> 选项类型 β) (l : 列表 α)
  结论: filterMap f l = l.filterMap f
  证明: rfl

@[simp]
-/
lemma filterMap_coe (f : α -> Option β) (l : List α) : filterMap f l = l.filterMap f := rfl

@[simp]
/--
theorem `filterMap_zero` / 定理 `filterMap_zero`

English:
theorem filterMap_zero
  given: (f : α -> Option β)
  statement: filterMap f 0 = 0
  proof: rfl

@[simp]

中文:
定理 filterMap_zero
  条件: (f : α -> 选项类型 β)
  结论: filterMap f 0 = 0
  证明: rfl

@[simp]
-/
theorem filterMap_zero (f : α -> Option β) : filterMap f 0 = 0 :=
  rfl

@[simp]
/--
theorem `filterMap_cons_none` / 定理 `filterMap_cons_none`

English:
theorem filterMap_cons_none
  given: {f : α -> Option β} (a : α) (s : Multiset α) (h : f a = none)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_none h

@[simp]

中文:
定理 filterMap_cons_none
  条件: {f : α -> 选项类型 β} (a : α) (s : Multiset α) (h : f a = none)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_none h

@[simp]

Depends on / 依赖: List.filterMap_cons_none, Quot.inductionOn, congr_arg, filterMap_cons_none, inductionOn, ofList
-/
theorem filterMap_cons_none {f : α -> Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_none h

@[simp]
/--
theorem `filterMap_cons_some` / 定理 `filterMap_cons_some`

English:
theorem filterMap_cons_some
  statement: (f : α -> Option β) (a : α) (s : Multiset α) {b : β}
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_some h

中文:
定理 filterMap_cons_some
  结论: (f : α -> 选项类型 β) (a : α) (s : Multiset α) {b : β}
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_some h

Depends on / 依赖: List.filterMap_cons_some, Quot.inductionOn, congr_arg, filterMap_cons_some, inductionOn, ofList
-/
theorem filterMap_cons_some (f : α -> Option β) (a : α) (s : Multiset α) {b : β}
    (h : f a = some b) : filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_cons_some h

/--
theorem `filterMap_cons` / 定理 `filterMap_cons`

English:
theorem filterMap_cons
  given: (f : α -> Option β) (a : α) (s : Multiset α)
  proof: by
  cases h : f a with
  | none => simp [filterMap_cons_none a s h]
  | some b => simp [filterMap_cons_some f a s h]

@[simp]

中文:
定理 filterMap_cons
  条件: (f : α -> 选项类型 β) (a : α) (s : Multiset α)
  证明: by
  cases h : f a with
  | none => simp [filterMap_cons_none a s h]
  | some b => simp [filterMap_cons_some f a s h]

@[simp]

Depends on / 依赖: filterMap_cons_none, filterMap_cons_some
-/
theorem filterMap_cons (f : α -> Option β) (a : α) (s : Multiset α) :
    filterMap f (a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap f s := by
  cases h : f a with
  | none => simp [filterMap_cons_none a s h]
  | some b => simp [filterMap_cons_some f a s h]

@[simp]
/--
theorem `filterMap_add` / 定理 `filterMap_add`

English:
theorem filterMap_add
  given: (f : α -> Option β) (s t : Multiset α)
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filterMap_append

中文:
定理 filterMap_add
  条件: (f : α -> 选项类型 β) (s t : Multiset α)
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filterMap_append

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, filterMap_append, ofList
-/
theorem filterMap_add (f : α -> Option β) (s t : Multiset α) :
    filterMap f (s + t) = filterMap f s + filterMap f t :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList filterMap_append

/--
theorem `filterMap_eq_map` / 定理 `filterMap_eq_map`

English:
theorem filterMap_eq_map
  given: (f : α -> β)
  statement: filterMap (some ∘ f) = map f
  proof: funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList congr_fun List.filterMap_eq_map l

中文:
定理 filterMap_eq_map
  条件: (f : α -> β)
  结论: filterMap (some ∘ f) = map f
  证明: funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList congr_fun List.filterMap_eq_map l

Depends on / 依赖: List.filterMap_eq_map, Quot.inductionOn, congr_arg, congr_fun, filterMap_eq_map, inductionOn, ofList
-/
theorem filterMap_eq_map (f : α -> β) : filterMap (some ∘ f) = map f :=
  funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList congr_fun List.filterMap_eq_map l

/--
theorem `filterMap_eq_filter` / 定理 `filterMap_eq_filter`

English:
theorem filterMap_eq_filter
  statement: filterMap (Option.guard p) = filter p
  proof: funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList by
      rw [← List.filterMap_eq_filter]

中文:
定理 filterMap_eq_filter
  结论: filterMap (选项类型.guard p) = filter p
  证明: funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList by
      rw [← List.filterMap_eq_filter]

Depends on / 依赖: List.filterMap_eq_filter, Quot.inductionOn, congr_arg, filterMap_eq_filter, inductionOn, ofList
-/
theorem filterMap_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s =>
Quot.inductionOn s fun l => congr_arg ofList by
      rw [← List.filterMap_eq_filter]

/--
theorem `filterMap_filterMap` / 定理 `filterMap_filterMap`

English:
theorem filterMap_filterMap
  given: (f : α -> Option β) (g : β -> Option γ) (s : Multiset α)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_filterMap

中文:
定理 filterMap_filterMap
  条件: (f : α -> 选项类型 β) (g : β -> 选项类型 γ) (s : Multiset α)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_filterMap

Depends on / 依赖: List.filterMap_filterMap, Quot.inductionOn, congr_arg, filterMap_filterMap, inductionOn, ofList
-/
theorem filterMap_filterMap (f : α -> Option β) (g : β -> Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_filterMap

/--
theorem `map_filterMap` / 定理 `map_filterMap`

English:
theorem map_filterMap
  given: (f : α -> Option β) (g : β -> γ) (s : Multiset α)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap

中文:
定理 map_filterMap
  条件: (f : α -> 选项类型 β) (g : β -> γ) (s : Multiset α)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap

Depends on / 依赖: List.map_filterMap, Quot.inductionOn, congr_arg, inductionOn, map_filterMap, ofList
-/
theorem map_filterMap (f : α -> Option β) (g : β -> γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap

/--
theorem `filterMap_map` / 定理 `filterMap_map`

English:
theorem filterMap_map
  given: (f : α -> β) (g : β -> Option γ) (s : Multiset α)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_map

中文:
定理 filterMap_map
  条件: (f : α -> β) (g : β -> 选项类型 γ) (s : Multiset α)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_map

Depends on / 依赖: List.filterMap_map, Quot.inductionOn, congr_arg, filterMap_map, inductionOn, ofList
-/
theorem filterMap_map (f : α -> β) (g : β -> Option γ) (s : Multiset α) :
    filterMap g (map f s) = filterMap (g ∘ f) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_map

/--
theorem `filter_filterMap` / 定理 `filter_filterMap`

English:
theorem filter_filterMap
  given: (f : α -> Option β) (p : β -> Prop) [DecidablePred p] (s : Multiset α)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filter_filterMap

中文:
定理 filter_filterMap
  条件: (f : α -> 选项类型 β) (p : β -> 命题) [DecidablePred p] (s : Multiset α)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filter_filterMap

Depends on / 依赖: List.filter_filterMap, Quot.inductionOn, congr_arg, filter_filterMap, inductionOn, ofList
-/
theorem filter_filterMap (f : α -> Option β) (p : β -> Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filter_filterMap

/--
theorem `filterMap_filter` / 定理 `filterMap_filter`

English:
theorem filterMap_filter
  given: (f : α -> Option β) (s : Multiset α)
  proof: Quot.inductionOn s fun l => congr_arg ofList by
    simpa using List.filterMap_filter (f := f) (p := p)

@[simp]

中文:
定理 filterMap_filter
  条件: (f : α -> 选项类型 β) (s : Multiset α)
  证明: Quot.inductionOn s fun l => congr_arg ofList by
    simpa using List.filterMap_filter (f := f) (p := p)

@[simp]

Depends on / 依赖: List.filterMap_filter, Quot.inductionOn, congr_arg, filterMap_filter, inductionOn, ofList
-/
theorem filterMap_filter (f : α -> Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
Quot.inductionOn s fun l => congr_arg ofList by
    simpa using List.filterMap_filter (f := f) (p := p)

@[simp]
/--
theorem `filterMap_some` / 定理 `filterMap_some`

English:
theorem filterMap_some
  given: (s : Multiset α)
  statement: filterMap some s = s
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_some

@[simp]

中文:
定理 filterMap_some
  条件: (s : Multiset α)
  结论: filterMap some s = s
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_some

@[simp]

Depends on / 依赖: List.filterMap_some, Quot.inductionOn, congr_arg, filterMap_some, inductionOn, ofList
-/
theorem filterMap_some (s : Multiset α) : filterMap some s = s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_some

@[simp]
/--
theorem `mem_filterMap` / 定理 `mem_filterMap`

English:
theorem mem_filterMap
  given: (f : α -> Option β) (s : Multiset α) {b : β}
  proof: Quot.inductionOn s fun _ => List.mem_filterMap

中文:
定理 mem_filterMap
  条件: (f : α -> 选项类型 β) (s : Multiset α) {b : β}
  证明: Quot.inductionOn s fun _ => List.mem_filterMap

Depends on / 依赖: List.mem_filterMap, Quot.inductionOn, inductionOn, mem_filterMap
-/
theorem mem_filterMap (f : α -> Option β) (s : Multiset α) {b : β} :
    b in filterMap f s ↔ exists a, a in s ∧ f a = some b :=
  Quot.inductionOn s fun _ => List.mem_filterMap

/--
theorem `map_filterMap_of_inv` / 定理 `map_filterMap_of_inv`

English:
theorem map_filterMap_of_inv
  statement: (f : α -> Option β) (g : β -> α) (H : forall x : α, (f x).map g = some x)
  proof: Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap_of_inv H

@[gcongr]

中文:
定理 map_filterMap_of_inv
  结论: (f : α -> 选项类型 β) (g : β -> α) (H : 对任意 x : α, (f x).map g = some x)
  证明: Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap_of_inv H

@[gcongr]

Depends on / 依赖: List.map_filterMap_of_inv, Quot.inductionOn, congr_arg, inductionOn, map_filterMap_of_inv, ofList
-/
theorem map_filterMap_of_inv (f : α -> Option β) (g : β -> α) (H : forall x : α, (f x).map g = some x)
    (s : Multiset α) : map g (filterMap f s) = s :=
Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap_of_inv H

@[gcongr]
/--
theorem `filterMap_le_filterMap` / 定理 `filterMap_le_filterMap`

English:
theorem filterMap_le_filterMap
  given: (f : α -> Option β) {s t : Multiset α} (h : s <= t)
  proof: leInductionOn h fun h => (h.filterMap _).subperm

中文:
定理 filterMap_le_filterMap
  条件: (f : α -> 选项类型 β) {s t : Multiset α} (h : s <= t)
  证明: leInductionOn h fun h => (h.filterMap _).subperm

Depends on / 依赖: filterMap, h.filterMap, leInductionOn, subperm
-/
theorem filterMap_le_filterMap (f : α -> Option β) {s t : Multiset α} (h : s <= t) :
    filterMap f s <= filterMap f t :=
  leInductionOn h fun h => (h.filterMap _).subperm

/--
theorem `map_filter_eq_filterMap` / 定理 `map_filter_eq_filterMap`

English:
theorem map_filter_eq_filterMap
  given: (f : α -> β) (p : α -> Prop) [DecidablePred p] (s : Multiset α)
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [filter_cons, map_add, ih, filterMap_cons, Option.map_if]; clear ih; congr
    split_ifs <;> simp

中文:
定理 map_filter_eq_filterMap
  条件: (f : α -> β) (p : α -> 命题) [DecidablePred p] (s : Multiset α)
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [filter_cons, map_add, ih, filterMap_cons, Option.map_if]; clear ih; congr
    split_ifs <;> simp

Depends on / 依赖: Multiset, Multiset.induction, Option.map_if, filterMap_cons, filter_cons, map_add, map_if, split_ifs
-/
theorem map_filter_eq_filterMap (f : α -> β) (p : α -> Prop) [DecidablePred p] (s : Multiset α) :
    map f (filter p s) = filterMap (fun a => if p a then .some (f a) else .none) s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [filter_cons, map_add, ih, filterMap_cons, Option.map_if]; clear ih; congr
    split_ifs <;> simp


/--
theorem `countP_eq_card_filter` / 定理 `countP_eq_card_filter`

English:
theorem countP_eq_card_filter
  given: (s)
  statement: countP p s = card (filter p s)
  proof: Quot.inductionOn s fun l => l.countP_eq_length_filter (p := (p ·))

@[simp]

中文:
定理 countP_eq_card_filter
  条件: (s)
  结论: countP p s = card (filter p s)
  证明: Quot.inductionOn s fun l => l.countP_eq_length_filter (p := (p ·))

@[simp]

Depends on / 依赖: Quot.inductionOn, countP_eq_length_filter, inductionOn, l.countP_eq_length_filter
-/
theorem countP_eq_card_filter (s) : countP p s = card (filter p s) :=
  Quot.inductionOn s fun l => l.countP_eq_length_filter (p := (p ·))

@[simp]
/--
theorem `countP_filter` / 定理 `countP_filter`

English:
theorem countP_filter
  given: (q) [DecidablePred q] (s : Multiset α)
  proof: by simp [countP_eq_card_filter]

中文:
定理 countP_filter
  条件: (q) [DecidablePred q] (s : Multiset α)
  证明: by simp [countP_eq_card_filter]

Depends on / 依赖: countP_eq_card_filter
-/
theorem countP_filter (q) [DecidablePred q] (s : Multiset α) :
    countP p (filter q s) = countP (fun a => p a ∧ q a) s := by simp [countP_eq_card_filter]

/--
theorem `countP_eq_countP_filter_add` / 定理 `countP_eq_countP_filter_add`

English:
theorem countP_eq_countP_filter_add
  given: (s) (p q : α -> Prop) [DecidablePred p] [DecidablePred q]
  proof: Quot.inductionOn s fun l => by
    convert! l.countP_eq_countP_filter_add (p ·) (q ·)
    simp

中文:
定理 countP_eq_countP_filter_add
  条件: (s) (p q : α -> 命题) [DecidablePred p] [DecidablePred q]
  证明: Quot.inductionOn s fun l => by
    convert! l.countP_eq_countP_filter_add (p ·) (q ·)
    simp

Depends on / 依赖: Quot.inductionOn, convert, countP_eq_countP_filter_add, inductionOn, l.countP_eq_countP_filter_add
-/
theorem countP_eq_countP_filter_add (s) (p q : α -> Prop) [DecidablePred p] [DecidablePred q] :
    countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).countP p :=
  Quot.inductionOn s fun l => by
    convert! l.countP_eq_countP_filter_add (p ·) (q ·)
    simp

/--
theorem `countP_map` / 定理 `countP_map`

English:
theorem countP_map
  given: (f : α -> β) (s : Multiset α) (p : β -> Prop) [DecidablePred p]
  proof: by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]

中文:
定理 countP_map
  条件: (f : α -> β) (s : Multiset α) (p : β -> 命题) [DecidablePred p]
  证明: by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]

Depends on / 依赖: Multiset, Multiset.induction_on, Nat.add_comm, add_comm, apply_ite, card_add, card_singleton, card_zero, countP_cons, countP_zero, filter_cons, filter_zero, induction_on, map_cons, map_zero
-/
theorem countP_map (f : α -> β) (s : Multiset α) (p : β -> Prop) [DecidablePred p] :
    countP p (map f s) = card (s.filter fun a => p (f a)) := by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]

/--
lemma `filter_attach` / 引理 `filter_attach`

English:
lemma filter_attach
  given: (s : Multiset α) (p : α -> Prop) [DecidablePred p]
  proof: Quotient.inductionOn s fun l => congr_arg _ (List.filter_attach l p)

中文:
引理 filter_attach
  条件: (s : Multiset α) (p : α -> 命题) [DecidablePred p]
  证明: Quotient.inductionOn s fun l => congr_arg _ (List.filter_attach l p)

Depends on / 依赖: List.filter_attach, Quotient, Quotient.inductionOn, congr_arg, filter_attach, inductionOn
-/
lemma filter_attach (s : Multiset α) (p : α -> Prop) [DecidablePred p] :
    (s.attach.filter fun a : {a // a in s} => p ↑a) =
      (s.filter p).attach.map (Subtype.map id fun _ => Multiset.mem_of_mem_filter) :=
  Quotient.inductionOn s fun l => congr_arg _ (List.filter_attach l p)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

@[simp]
/--
theorem `count_filter_of_pos` / 定理 `count_filter_of_pos`

English:
theorem count_filter_of_pos
  given: {p} [DecidablePred p] {a} {s : Multiset α} (h : p a)
  proof: Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, coe_count]
    apply count_filter
    simpa using h

中文:
定理 count_filter_of_pos
  条件: {p} [DecidablePred p] {a} {s : Multiset α} (h : p a)
  证明: Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, coe_count]
    apply count_filter
    simpa using h

Depends on / 依赖: Quot.inductionOn, coe_count, count_filter, filter_coe, inductionOn, quot_mk_to_coe
-/
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
    count a (filter p s) = count a s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, coe_count]
    apply count_filter
    simpa using h

/--
theorem `count_filter_of_neg` / 定理 `count_filter_of_neg`

English:
theorem count_filter_of_neg
  given: {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a)
  proof: by
  simp [h]

中文:
定理 count_filter_of_neg
  条件: {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a)
  证明: by
  simp [h]
-/
theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) :
    count a (filter p s) = 0 := by
  simp [h]

/--
theorem `count_filter` / 定理 `count_filter`

English:
theorem count_filter
  given: {p} [DecidablePred p] {a} {s : Multiset α}
  proof: by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h

中文:
定理 count_filter
  条件: {p} [DecidablePred p] {a} {s : Multiset α}
  证明: by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h

Depends on / 依赖: count_filter_of_neg, count_filter_of_pos, split_ifs
-/
theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} :
    count a (filter p s) = if p a then count a s else 0 := by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h

/--
theorem `count_map` / 定理 `count_map`

English:
theorem count_map
  given: {α β : Type*} (f : α -> β) (s : Multiset α) [DecidableEq β] (b : β)
  proof: by
  simp [count, countP_map]

中文:
定理 count_map
  条件: {α β : 类型} (f : α -> β) (s : Multiset α) [DecidableEq β] (b : β)
  证明: by
  simp [count, countP_map]

Depends on / 依赖: countP_map
-/
theorem count_map {α β : Type*} (f : α -> β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = card (s.filter fun a => b = f a) := by
  simp [count, countP_map]

/--
theorem `count_map_eq_count` / 定理 `count_map_eq_count`

English:
theorem count_map_eq_count
  statement: [DecidableEq β] (f : α -> β) (s : Multiset α)
  proof: by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count]; rw [countP_map]; rw [← this]
exact count_filter_of_pos rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp
    · simp only [mem_filter, and

中文:
定理 count_map_eq_count
  结论: [DecidableEq β] (f : α -> β) (s : Multiset α)
  证明: by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count]; rw [countP_map]; rw [← this]
exact count_filter_of_pos rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp
    · simp only [mem_filter, and

Depends on / 依赖: and_imp, countP_map, count_filter_of_pos, eq_comm, eq_replicate_card, filter, imp_self, implies_true, mem_filter
-/
theorem count_map_eq_count [DecidableEq β] (f : α -> β) (s : Multiset α)
    (hf : Set.InjOn f { x : α | x in s }) (x) (H : x in s) : (s.map f).count (f x) = s.count x := by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count]; rw [countP_map]; rw [← this]
exact count_filter_of_pos rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp
    · simp only [mem_filter, and_imp, @eq_comm _ (f x), imp_self, implies_true]

/--
theorem `count_map_eq_count'` / 定理 `count_map_eq_count'`

English:
theorem count_map_eq_count'
  statement: [DecidableEq β] (f : α -> β) (s : Multiset α) (hf : Function.Injective f)
  proof: by
  by_cases H : x in s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_notMem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction

中文:
定理 count_map_eq_count'
  结论: [DecidableEq β] (f : α -> β) (s : Multiset α) (hf : 函数.单射 f)
  证明: by
  by_cases H : x in s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_notMem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction

Depends on / 依赖: count_eq_zero, count_eq_zero_of_notMem, count_map_eq_count, hf.injOn, mem_map
-/
theorem count_map_eq_count' [DecidableEq β] (f : α -> β) (s : Multiset α) (hf : Function.Injective f)
    (x : α) : (s.map f).count (f x) = s.count x := by
  by_cases H : x in s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_notMem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction

/--
theorem `filter_eq'` / 定理 `filter_eq'`

English:
theorem filter_eq'
  given: (s : Multiset α) (b : α)
  statement: s.filter (· = b) = replicate (count b s) b
  proof: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, coe_count]
    rw [List.filter_eq]; rw [coe_replicate]

中文:
定理 filter_eq'
  条件: (s : Multiset α) (b : α)
  结论: s.filter (· = b) = replicate (count b s) b
  证明: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, coe_count]
    rw [List.filter_eq]; rw [coe_replicate]

Depends on / 依赖: List.filter_eq, Quotient, Quotient.inductionOn, coe_count, coe_replicate, filter_coe, filter_eq, inductionOn, quot_mk_to_coe
-/
theorem filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = replicate (count b s) b :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, coe_count]
    rw [List.filter_eq]; rw [coe_replicate]

/--
theorem `filter_eq` / 定理 `filter_eq`

English:
theorem filter_eq
  given: (s : Multiset α) (b : α)
  statement: s.filter (Eq b) = replicate (count b s) b
  proof: by
  simp_rw [← filter_eq', eq_comm]

中文:
定理 filter_eq
  条件: (s : Multiset α) (b : α)
  结论: s.filter (相等 b) = replicate (count b s) b
  证明: by
  simp_rw [← filter_eq', eq_comm]

Depends on / 依赖: eq_comm, filter_eq, simp_rw
-/
theorem filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = replicate (count b s) b := by
  simp_rw [← filter_eq', eq_comm]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

@[simp]
/--
lemma `filter_sub` / 引理 `filter_sub`

English:
lemma filter_sub
  given: (p : α -> Prop) [DecidablePred p] (s t : Multiset α)
  proof: by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons]; rw [IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a in s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_

中文:
引理 filter_sub
  条件: (p : α -> 命题) [DecidablePred p] (s t : Multiset α)
  证明: by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons]; rw [IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a in s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_

Depends on / 依赖: Multiset, Multiset.induction_on, cons_erase, cons_inj_right, erase_of_notMem, filter, filter_cons_of_neg, filter_cons_of_pos, induction_on, mem_filter_of_mem, mem_of_mem_filter, revert, sub_cons
-/
lemma filter_sub (p : α -> Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s - t) = filter p s - filter p t := by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons]; rw [IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a in s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_erase m]
    · rw [erase_of_notMem m, erase_of_notMem (mt mem_of_mem_filter m)]
  · rw [filter_cons_of_neg _ h]
    by_cases m : a in s
    · rw [(by rw [filter_cons_of_neg _ h] : filter p (erase s a) = filter p (a ::ₘ erase s a)),
        cons_erase m]
    · rw [erase_of_notMem m]

@[simp]
/--
lemma `sub_filter_eq_filter_not` / 引理 `sub_filter_eq_filter_not`

English:
lemma sub_filter_eq_filter_not
  given: (p : α -> Prop) [DecidablePred p] (s : Multiset α)
  proof: by ext a; by_cases h : p a <;> simp [h]

中文:
引理 sub_filter_eq_filter_not
  条件: (p : α -> 命题) [DecidablePred p] (s : Multiset α)
  证明: by ext a; by_cases h : p a <;> simp [h]
-/
lemma sub_filter_eq_filter_not (p : α -> Prop) [DecidablePred p] (s : Multiset α) :
    s - s.filter p = s.filter fun a => ¬ p a := by ext a; by_cases h : p a <;> simp [h]

end sub

section Embedding

@[simp]
/--
theorem `map_le_map_iff` / 定理 `map_le_map_iff`

English:
theorem map_le_map_iff
  given: {f : α -> β} (hf : Function.Injective f) {s t : Multiset α}
  proof: by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

中文:
定理 map_le_map_iff
  条件: {f : α -> β} (hf : 函数.单射 f) {s t : Multiset α}
  证明: by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

Depends on / 依赖: classical, count_map_eq_count, le_iff_count, le_iff_count.mp, le_iff_count.mpr, map_le_map
-/
theorem map_le_map_iff {f : α -> β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f <= t.map f ↔ s <= t := by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps!]
/--
Definition of `mapEmbedding` / `mapEmbedding` 的定义

English:
definition mapEmbedding
  signature: (f : α ↪ β)
  body: OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

中文:
定义 mapEmbedding
  签名: (f : α ↪ β)
  定义体: OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofMapLEIff, f.inj, map_le_map_iff, ofMapLEIff
-/
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

end Embedding

/--
theorem `count_eq_card_filter_eq` / 定理 `count_eq_card_filter_eq`

English:
theorem count_eq_card_filter_eq
  given: [DecidableEq α] (s : Multiset α) (a : α)
  proof: by rw [count, countP_eq_card_filter]

中文:
定理 count_eq_card_filter_eq
  条件: [DecidableEq α] (s : Multiset α) (a : α)
  证明: by rw [count, countP_eq_card_filter]

Depends on / 依赖: countP_eq_card_filter
-/
theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) :
    s.count a = card (s.filter (a = ·)) := by rw [count, countP_eq_card_filter]

/--
Mapping a multiset through a predicate and counting the `True`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `Classical.decEq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
/--
theorem `map_count_True_eq_filter_card` / 定理 `map_count_True_eq_filter_card`

English:
theorem map_count_True_eq_filter_card
  given: (s : Multiset α) (p : α -> Prop) [DecidablePred p]
  proof: by
  simp only [count_eq_card_filter_eq, eq_iff_iff, true_iff, filter_map, comp_apply, card_map]

中文:
定理 map_count_True_eq_filter_card
  条件: (s : Multiset α) (p : α -> 命题) [DecidablePred p]
  证明: by
  simp only [count_eq_card_filter_eq, eq_iff_iff, true_iff, filter_map, comp_apply, card_map]

Depends on / 依赖: card_map, comp_apply, count_eq_card_filter_eq, eq_iff_iff, filter_map, true_iff
-/
theorem map_count_True_eq_filter_card (s : Multiset α) (p : α -> Prop) [DecidablePred p] :
    (s.map p).count True = card (s.filter p) := by
  simp only [count_eq_card_filter_eq, eq_iff_iff, true_iff, filter_map, comp_apply, card_map]

section Map

set_option backward.isDefEq.respectTransparency false in
/--
lemma `filter_attach'` / 引理 `filter_attach'`

English:
lemma filter_attach'
  statement: (s : Multiset α) (p : {a // a in s} -> Prop) [DecidableEq α]
  proof: by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Subtype.exists, exists_and_right, exists_eq_right, attach_map_val, Subtype.map, id,
    map_map, comp]

中文:
引理 filter_attach'
  结论: (s : Multiset α) (p : {a // a in s} -> 命题) [DecidableEq α]
  证明: by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Subtype.exists, exists_and_right, exists_eq_right, attach_map_val, Subtype.map, id,
    map_map, comp]

Depends on / 依赖: Multiset, Multiset.map_injective, Subtype, Subtype.exists, Subtype.map, Subtype.val_injective, attach_map_val, classical, exists_and_right, exists_eq_right, map_filter, map_injective, map_map, val_injective
-/
lemma filter_attach' (s : Multiset α) (p : {a // a in s} -> Prop) [DecidableEq α]
    [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x => exists h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ => mem_of_mem_filter) := by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Subtype.exists, exists_and_right, exists_eq_right, attach_map_val, Subtype.map, id,
    map_map, comp]

end Map

section Nodup

variable {s : Multiset α}

/--
theorem `Nodup.filter` / 定理 `Nodup.filter`

English:
theorem Nodup.filter
  given: (p : α -> Prop) [DecidablePred p] {s}
  statement: Nodup s -> Nodup (filter p s)
  proof: Quot.induction_on s fun _ => List.Nodup.filter (p ·)

中文:
定理 Nodup.filter
  条件: (p : α -> 命题) [DecidablePred p] {s}
  结论: Nodup s -> Nodup (filter p s)
  证明: Quot.induction_on s fun _ => List.Nodup.filter (p ·)
-/
theorem Nodup.filter (p : α -> Prop) [DecidablePred p] {s} : Nodup s -> Nodup (filter p s) :=
  Quot.induction_on s fun _ => List.Nodup.filter (p ·)

/--
theorem `Nodup.erase_eq_filter` / 定理 `Nodup.erase_eq_filter`

English:
theorem Nodup.erase_eq_filter
  given: [DecidableEq α] (a : α) {s}
  proof: Quot.induction_on s fun _ d =>
congr_arg ((↑) : List α -> Multiset α) by simpa using! List.Nodup.erase_eq_filter d a

中文:
定理 Nodup.erase_eq_filter
  条件: [DecidableEq α] (a : α) {s}
  证明: Quot.induction_on s fun _ d =>
congr_arg ((↑) : List α -> Multiset α) by simpa using! List.Nodup.erase_eq_filter d a

Depends on / 依赖: List.Nodup.erase_eq_filter, Multiset, Quot.induction_on, congr_arg, erase_eq_filter, induction_on
-/
theorem Nodup.erase_eq_filter [DecidableEq α] (a : α) {s} :
    Nodup s -> s.erase a = Multiset.filter (· != a) s :=
  Quot.induction_on s fun _ d =>
congr_arg ((↑) : List α -> Multiset α) by simpa using! List.Nodup.erase_eq_filter d a

/--
theorem `Nodup.filterMap` / 定理 `Nodup.filterMap`

English:
theorem Nodup.filterMap
  given: (f : α -> Option β) (H : forall a a' b, b in f a -> b in f a' -> a = a')
  proof: Quot.induction_on s fun _ => List.Nodup.filterMap H

中文:
定理 Nodup.filterMap
  条件: (f : α -> 选项类型 β) (H : 对任意 a a' b, b in f a -> b in f a' -> a = a')
  证明: Quot.induction_on s fun _ => List.Nodup.filterMap H
-/
protected theorem Nodup.filterMap (f : α -> Option β) (H : forall a a' b, b in f a -> b in f a' -> a = a') :
    Nodup s -> Nodup (filterMap f s) :=
  Quot.induction_on s fun _ => List.Nodup.filterMap H

/--
theorem `Nodup.mem_erase_iff` / 定理 `Nodup.mem_erase_iff`

English:
theorem Nodup.mem_erase_iff
  given: [DecidableEq α] {a b : α} {l} (d : Nodup l)
  proof: by
  rw [d.erase_eq_filter b]; rw [mem_filter]; rw [and_comm]

中文:
定理 Nodup.mem_erase_iff
  条件: [DecidableEq α] {a b : α} {l} (d : Nodup l)
  证明: by
  rw [d.erase_eq_filter b]; rw [mem_filter]; rw [and_comm]

Depends on / 依赖: and_comm, d.erase_eq_filter, erase_eq_filter, mem_filter
-/
theorem Nodup.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodup l) :
    a in l.erase b ↔ a != b ∧ a in l := by
  rw [d.erase_eq_filter b]; rw [mem_filter]; rw [and_comm]

/--
theorem `Nodup.notMem_erase` / 定理 `Nodup.notMem_erase`

English:
theorem Nodup.notMem_erase
  given: [DecidableEq α] {a : α} {s} (h : Nodup s)
  statement: a ∉ s.erase a
  proof: fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

中文:
定理 Nodup.notMem_erase
  条件: [DecidableEq α] {a : α} {s} (h : Nodup s)
  结论: a ∉ s.erase a
  证明: fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl
-/
theorem Nodup.notMem_erase [DecidableEq α] {a : α} {s} (h : Nodup s) : a ∉ s.erase a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

end Nodup

end Multiset
