/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Lattice
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.MinMax
public import Mathlib.Logic.Pairwise

/-!
# Distributive lattice structure on multisets

This file defines an instance `DistribLattice (Multiset α)` using the union and intersection
operators:

* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-! ### Union -/

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (s t : Multiset α)
  body: s - t + t

中文:
定义 union
  签名: (s t : Multiset α)
  定义体: s - t + t
-/
def union (s t : Multiset α) : Multiset α := s - t + t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union (Multiset α)
  body: ⟨union⟩

中文:
实例 :
  签名: 并集 (Multiset α)
  定义体: ⟨union⟩

Depends on / 依赖: Computation, Computation.LiftRel.refl, LiftRel
-/
instance : Union (Multiset α) :=
  ⟨union⟩

/--
lemma `union_def` / 引理 `union_def`

English:
lemma union_def
  given: (s t : Multiset α)
  statement: s union t = s - t + t
  proof: rfl

中文:
引理 union_def
  条件: (s t : Multiset α)
  结论: s union t = s - t + t
  证明: rfl

Depends on / 依赖: LiftRel, LiftRel.swap, Std.Symm.swap_eq, swap_eq
-/
lemma union_def (s t : Multiset α) : s union t = s - t + t := rfl

/--
lemma `le_union_left` / 引理 `le_union_left`

English:
lemma le_union_left
  statement: s <= s union t
  proof: Multiset.le_sub_add

中文:
引理 le_union_left
  结论: s <= s union t
  证明: Multiset.le_sub_add

Depends on / 依赖: Computation, Computation.liftRel_def, Computation.rel_of_liftRel, Computation.terminates_of_liftRel, LiftRel, Multiset, Multiset.le_sub_add, h1.left, le_sub_add, liftRel_def, liftRel_destruct, rel_of_liftRel, terminates_of_liftRel
-/
lemma le_union_left : s <= s union t := Multiset.le_sub_add
/--
lemma `le_union_right` / 引理 `le_union_right`

English:
lemma le_union_right
  statement: t <= s union t
  proof: le_add_left _ _

中文:
引理 le_union_right
  结论: t <= s union t
  证明: le_add_left _ _

Depends on / 依赖: H.stdRefl, LiftRel, LiftRel.refl, le_add_left, stdRefl
-/
lemma le_union_right : t <= s union t := le_add_left _ _
/--
lemma `eq_union_left` / 引理 `eq_union_left`

English:
lemma eq_union_left
  statement: t <= s -> s union t = s
  proof: Multiset.sub_add_cancel

@[gcongr]

中文:
引理 eq_union_left
  结论: t <= s -> s union t = s
  证明: Multiset.sub_add_cancel

@[gcongr]

Depends on / 依赖: Multiset, Multiset.sub_add_cancel, sub_add_cancel
-/
lemma eq_union_left : t <= s -> s union t = s := Multiset.sub_add_cancel

@[gcongr]
/--
lemma `union_le_union_right` / 引理 `union_le_union_right`

English:
lemma union_le_union_right
  given: (h : s <= t) (u)
  statement: s union u <= t union u
  proof: Multiset.add_le_add_right Multiset.sub_le_sub_right h

中文:
引理 union_le_union_right
  条件: (h : s <= t) (u)
  结论: s union u <= t union u
  证明: Multiset.add_le_add_right Multiset.sub_le_sub_right h

Depends on / 依赖: LiftRel, LiftRel.refl, Multiset, Multiset.add_le_add_right, Multiset.sub_le_sub_right, add_le_add_right, sub_le_sub_right
-/
lemma union_le_union_right (h : s <= t) (u) : s union u <= t union u :=
Multiset.add_le_add_right Multiset.sub_le_sub_right h

/--
lemma `union_le` / 引理 `union_le`

English:
lemma union_le
  given: (h₁ : s <= u) (h₂ : t <= u)
  statement: s union t <= u
  proof: by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]

中文:
引理 union_le
  条件: (h₁ : s <= u) (h₂ : t <= u)
  结论: s union t <= u
  证明: by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]

Depends on / 依赖: LiftRel, LiftRel.symm, eq_union_left, union_le_union_right
-/
lemma union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u := by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]
/--
lemma `mem_union` / 引理 `mem_union`

English:
lemma mem_union
  statement: a in s union t ↔ a in s ∨ a in t
  proof: ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]

中文:
引理 mem_union
  结论: a in s union t ↔ a in s ∨ a in t
  证明: ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]

Depends on / 依赖: LiftRel, LiftRel.trans, Multiset, Multiset.sub_le_self, Or.elim, imp_left, le_union_left, le_union_right, mem_add, mem_of_le, sub_le_self
-/
lemma mem_union : a in s union t ↔ a in s ∨ a in t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]
/--
lemma `map_union` / 引理 `map_union`

English:
lemma map_union
  given: [DecidableEq β] {f : α -> β} (finj : Function.Injective f) {s t : Multiset α}
  proof: Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append, List.map_diff finj])

中文:
引理 map_union
  条件: [DecidableEq β] {f : α -> β} (finj : 函数.单射 f) {s t : Multiset α}
  证明: Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append, List.map_diff finj])

Depends on / 依赖: Equiv.refl, Equiv.symm, Equiv.trans, List.map_append, List.map_diff, Quotient, Quotient.inductionOn, congr_arg, map_append, map_diff, ofList
-/
lemma map_union [DecidableEq β] {f : α -> β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s union t) = map f s union map f t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append, List.map_diff finj])

/--
lemma `zero_union` / 引理 `zero_union`

English:
lemma zero_union
  statement: 0 union s = s
  proof: by simp [union_def, Multiset.zero_sub]

中文:
引理 zero_union
  结论: 0 union s = s
  证明: by simp [union_def, Multiset.zero_sub]
-/
@[simp] lemma zero_union : 0 union s = s := by simp [union_def, Multiset.zero_sub]
/--
lemma `union_zero` / 引理 `union_zero`

English:
lemma union_zero
  statement: s union 0 = s
  proof: by simp [union_def]

@[simp]

中文:
引理 union_zero
  结论: s union 0 = s
  证明: by simp [union_def]

@[simp]
-/
@[simp] lemma union_zero : s union 0 = s := by simp [union_def]

@[simp]
/--
lemma `count_union` / 引理 `count_union`

English:
lemma count_union
  given: (a : α) (s t : Multiset α)
  statement: count a (s union t) = max (count a s) (count a t)
  proof: by
  simp [(· union ·), union, Nat.sub_add_eq_max]

中文:
引理 count_union
  条件: (a : α) (s t : Multiset α)
  结论: count a (s union t) = 最大值 (count a s) (count a t)
  证明: by
  simp [(· union ·), union, Nat.sub_add_eq_max]

Depends on / 依赖: Nat.sub_add_eq_max, sub_add_eq_max
-/
lemma count_union (a : α) (s t : Multiset α) : count a (s union t) = max (count a s) (count a t) := by
  simp [(· union ·), union, Nat.sub_add_eq_max]

/--
lemma `filter_union` / 引理 `filter_union`

English:
lemma filter_union
  given: (p : α -> Prop) [DecidablePred p] (s t : Multiset α)
  proof: by simp [(· union ·), union]

中文:
引理 filter_union
  条件: (p : α -> 命题) [DecidablePred p] (s t : Multiset α)
  证明: by simp [(· union ·), union]
-/
@[simp] lemma filter_union (p : α -> Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s union t) = filter p s union filter p t := by simp [(· union ·), union]

/-! ### Intersection -/

/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (s t : Multiset α)
  body: Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.bagInter p₂

中文:
定义 inter
  签名: (s t : Multiset α)
  定义体: Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.bagInter p₂

Depends on / 依赖: Multiset, Quot.sound, Quotient, Quotient.liftOn, bagInter
-/
def inter (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
Quot.sound p₁.bagInter p₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inter (Multiset α)
  body: ⟨inter⟩

中文:
实例 :
  签名: 交集 (Multiset α)
  定义体: ⟨inter⟩
-/
instance : Inter (Multiset α) := ⟨inter⟩

/--
lemma `inter_zero` / 引理 `inter_zero`

English:
lemma inter_zero
  given: (s : Multiset α)
  statement: s inter 0 = 0
  proof: Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil

中文:
引理 inter_zero
  条件: (s : Multiset α)
  结论: s inter 0 = 0
  证明: Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil
-/
@[simp] lemma inter_zero (s : Multiset α) : s inter 0 = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil

/--
lemma `zero_inter` / 引理 `zero_inter`

English:
lemma zero_inter
  given: (s : Multiset α)
  statement: 0 inter s = 0
  proof: Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]

中文:
引理 zero_inter
  条件: (s : Multiset α)
  结论: 0 inter s = 0
  证明: Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]
-/
@[simp] lemma zero_inter (s : Multiset α) : 0 inter s = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]
/--
lemma `cons_inter_of_pos` / 引理 `cons_inter_of_pos`

English:
lemma cons_inter_of_pos
  given: (s : Multiset α)
  statement: a in t -> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_mem _ h

@[simp]

中文:
引理 cons_inter_of_pos
  条件: (s : Multiset α)
  结论: a in t -> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_mem _ h

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, cons_bagInter_of_mem, ofList
-/
lemma cons_inter_of_pos (s : Multiset α) : a in t -> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_mem _ h

@[simp]
/--
lemma `cons_inter_of_neg` / 引理 `cons_inter_of_neg`

English:
lemma cons_inter_of_neg
  given: (s : Multiset α)
  statement: a ∉ t -> (a ::ₘ s) inter t = s inter t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_not_mem _ h

中文:
引理 cons_inter_of_neg
  条件: (s : Multiset α)
  结论: a ∉ t -> (a ::ₘ s) inter t = s inter t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_not_mem _ h

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, cons_bagInter_of_not_mem, ofList
-/
lemma cons_inter_of_neg (s : Multiset α) : a ∉ t -> (a ::ₘ s) inter t = s inter t :=
Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList cons_bagInter_of_not_mem _ h

/--
lemma `inter_le_left` / 引理 `inter_le_left`

English:
lemma inter_le_left
  statement: s inter t <= s
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => bagInter_sublist_left.subperm

中文:
引理 inter_le_left
  结论: s inter t <= s
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => bagInter_sublist_left.subperm

Depends on / 依赖: Quotient, Quotient.inductionOn, bagInter_sublist_left, bagInter_sublist_left.subperm, subperm
-/
lemma inter_le_left : s inter t <= s :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => bagInter_sublist_left.subperm

/--
lemma `inter_le_right` / 引理 `inter_le_right`

English:
lemma inter_le_right
  statement: s inter t <= t
  proof: by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (zero_inter t).symm ▸ zero_le _
  | cons a s IH =>
    by_cases h : a in t
    · simpa [h] using cons_le_cons a (IH (t := t.erase a))
    · simp [h, IH]

中文:
引理 inter_le_right
  结论: s inter t <= t
  证明: by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (zero_inter t).symm ▸ zero_le _
  | cons a s IH =>
    by_cases h : a in t
    · simpa [h] using cons_le_cons a (IH (t := t.erase a))
    · simp [h, IH]

Depends on / 依赖: Multiset, Multiset.induction_on, cons_le_cons, generalizing, induction_on, t.erase, zero_inter, zero_le
-/
lemma inter_le_right : s inter t <= t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (zero_inter t).symm ▸ zero_le _
  | cons a s IH =>
    by_cases h : a in t
    · simpa [h] using cons_le_cons a (IH (t := t.erase a))
    · simp [h, IH]

/--
lemma `le_inter` / 引理 `le_inter`

English:
lemma le_inter
  given: (h₁ : s <= t) (h₂ : s <= u)
  statement: s <= t inter u
  proof: by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intro s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a in u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
 

中文:
引理 le_inter
  条件: (h₁ : s <= t) (h₂ : s <= u)
  结论: s <= t inter u
  证明: by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intro s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a in u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
 

Depends on / 依赖: Multiset, Multiset.induction_on, cons_inter_of_neg, cons_inter_of_pos, erase_le_erase, erase_le_iff_le_cons, induction_on, le_cons_of_notMem, mem_of_le, revert, zero_inter
-/
lemma le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u := by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intro s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a in u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_notMem <| mt (mem_of_le h₂) h).1 h₁) h₂

@[simp]
/--
lemma `mem_inter` / 引理 `mem_inter`

English:
lemma mem_inter
  statement: a in s inter t ↔ a in s ∧ a in t
  proof: ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁]; rw [cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

中文:
引理 mem_inter
  结论: a in s inter t ↔ a in s ∧ a in t
  证明: ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁]; rw [cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

Depends on / 依赖: cons_erase, cons_inter_of_pos, inter_le_left, inter_le_right, mem_cons_self, mem_of_le
-/
lemma mem_inter : a in s inter t ↔ a in s ∧ a in t :=
  ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁]; rw [cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (Multiset α) where
  body: (· union ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· inter ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right

中文:
实例 instLattice
  签名: : 格 (Multiset α) where
  定义体: (· union ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· inter ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right
-/
instance instLattice : Lattice (Multiset α) where
  sup := (· union ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· inter ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right

/--
lemma `sup_eq_union` / 引理 `sup_eq_union`

English:
lemma sup_eq_union
  given: (s t : Multiset α)
  statement: s ⊔ t = s union t
  proof: rfl

中文:
引理 sup_eq_union
  条件: (s t : Multiset α)
  结论: s ⊔ t = s union t
  证明: rfl
-/
@[simp] lemma sup_eq_union (s t : Multiset α) : s ⊔ t = s union t := rfl
/--
lemma `inf_eq_inter` / 引理 `inf_eq_inter`

English:
lemma inf_eq_inter
  given: (s t : Multiset α)
  statement: s ⊓ t = s inter t
  proof: rfl

中文:
引理 inf_eq_inter
  条件: (s t : Multiset α)
  结论: s ⊓ t = s inter t
  证明: rfl
-/
@[simp] lemma inf_eq_inter (s t : Multiset α) : s ⊓ t = s inter t := rfl

/--
lemma `le_inter_iff` / 引理 `le_inter_iff`

English:
lemma le_inter_iff
  statement: s <= t inter u ↔ s <= t ∧ s <= u
  proof: le_inf_iff

中文:
引理 le_inter_iff
  结论: s <= t inter u ↔ s <= t ∧ s <= u
  证明: le_inf_iff

Depends on / 依赖: dropn_congr, head_congr
-/
@[simp] lemma le_inter_iff : s <= t inter u ↔ s <= t ∧ s <= u := le_inf_iff
/--
lemma `union_le_iff` / 引理 `union_le_iff`

English:
lemma union_le_iff
  statement: s union t <= u ↔ s <= u ∧ t <= u
  proof: sup_le_iff

中文:
引理 union_le_iff
  结论: s union t <= u ↔ s <= u ∧ t <= u
  证明: sup_le_iff
-/
@[simp] lemma union_le_iff : s union t <= u ↔ s <= u ∧ t <= u := sup_le_iff

/--
lemma `union_comm` / 引理 `union_comm`

English:
lemma union_comm
  given: (s t : Multiset α)
  statement: s union t = t union s
  proof: sup_comm ..

中文:
引理 union_comm
  条件: (s t : Multiset α)
  结论: s union t = t union s
  证明: sup_comm ..

Depends on / 依赖: sup_comm
-/
lemma union_comm (s t : Multiset α) : s union t = t union s := sup_comm ..
/--
lemma `inter_comm` / 引理 `inter_comm`

English:
lemma inter_comm
  given: (s t : Multiset α)
  statement: s inter t = t inter s
  proof: inf_comm ..

中文:
引理 inter_comm
  条件: (s t : Multiset α)
  结论: s inter t = t inter s
  证明: inf_comm ..

Depends on / 依赖: inf_comm
-/
lemma inter_comm (s t : Multiset α) : s inter t = t inter s := inf_comm ..

/--
lemma `eq_union_right` / 引理 `eq_union_right`

English:
lemma eq_union_right
  given: (h : s <= t)
  statement: s union t = t
  proof: by rw [union_comm, eq_union_left h]

中文:
引理 eq_union_right
  条件: (h : s <= t)
  结论: s union t = t
  证明: by rw [union_comm, eq_union_left h]

Depends on / 依赖: eq_union_left, union_comm
-/
lemma eq_union_right (h : s <= t) : s union t = t := by rw [union_comm, eq_union_left h]

/--
lemma `union_le_union_left` / 引理 `union_le_union_left`

English:
lemma union_le_union_left
  given: (h : s <= t) (u)
  statement: u union s <= u union t
  proof: sup_le_sup_left h _

中文:
引理 union_le_union_left
  条件: (h : s <= t) (u)
  结论: u union s <= u union t
  证明: sup_le_sup_left h _
-/
@[gcongr] lemma union_le_union_left (h : s <= t) (u) : u union s <= u union t := sup_le_sup_left h _

/--
lemma `union_le_add` / 引理 `union_le_add`

English:
lemma union_le_add
  given: (s t : Multiset α)
  statement: s union t <= s + t
  proof: union_le (le_add_right ..) (le_add_left ..)

中文:
引理 union_le_add
  条件: (s t : Multiset α)
  结论: s union t <= s + t
  证明: union_le (le_add_right ..) (le_add_left ..)

Depends on / 依赖: le_add_left, le_add_right, union_le
-/
lemma union_le_add (s t : Multiset α) : s union t <= s + t := union_le (le_add_right ..) (le_add_left ..)

/--
lemma `union_add_distrib` / 引理 `union_add_distrib`

English:
lemma union_add_distrib
  given: (s t u : Multiset α)
  statement: s union t + u = s + u union (t + u)
  proof: by
  simpa [(· union ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm]; rw [Multiset.sub_add_eq_sub_sub]; rw [Multiset.add_sub_cancel_right]

中文:
引理 union_add_distrib
  条件: (s t u : Multiset α)
  结论: s union t + u = s + u union (t + u)
  证明: by
  simpa [(· union ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm]; rw [Multiset.sub_add_eq_sub_sub]; rw [Multiset.add_sub_cancel_right]

Depends on / 依赖: Multiset, Multiset.add_assoc, Multiset.add_left_inj, Multiset.add_sub_cancel_right, Multiset.sub_add_eq_sub_sub, add_assoc, add_comm, add_left_inj, add_sub_cancel_right, eq_comm, sub_add_eq_sub_sub, t.add_comm
-/
lemma union_add_distrib (s t u : Multiset α) : s union t + u = s + u union (t + u) := by
  simpa [(· union ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm]; rw [Multiset.sub_add_eq_sub_sub]; rw [Multiset.add_sub_cancel_right]

/--
lemma `add_union_distrib` / 引理 `add_union_distrib`

English:
lemma add_union_distrib
  given: (s t u : Multiset α)
  statement: s + (t union u) = s + t union (s + u)
  proof: by
  rw [Multiset.add_comm]; rw [union_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

中文:
引理 add_union_distrib
  条件: (s t u : Multiset α)
  结论: s + (t union u) = s + t union (s + u)
  证明: by
  rw [Multiset.add_comm]; rw [union_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, s.add_comm, union_add_distrib
-/
lemma add_union_distrib (s t u : Multiset α) : s + (t union u) = s + t union (s + u) := by
  rw [Multiset.add_comm]; rw [union_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

/--
lemma `cons_union_distrib` / 引理 `cons_union_distrib`

English:
lemma cons_union_distrib
  given: (a : α) (s t : Multiset α)
  statement: a ::ₘ (s union t) = a ::ₘ s union a ::ₘ t
  proof: by
  simpa using add_union_distrib (a ::ₘ 0) s t

中文:
引理 cons_union_distrib
  条件: (a : α) (s t : Multiset α)
  结论: a ::ₘ (s union t) = a ::ₘ s union a ::ₘ t
  证明: by
  simpa using add_union_distrib (a ::ₘ 0) s t

Depends on / 依赖: add_union_distrib
-/
lemma cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s union t) = a ::ₘ s union a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t

/--
lemma `inter_add_distrib` / 引理 `inter_add_distrib`

English:
lemma inter_add_distrib
  given: (s t u : Multiset α)
  statement: s inter t + u = (s + u) inter (t + u)
  proof: by
  by_contra! h
obtain ⟨a, ha⟩ := lt_iff_cons_le.1 h.lt_of_le le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
exact (lt_cons_self (s inter t) a).not_ge le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))


中文:
引理 inter_add_distrib
  条件: (s t u : Multiset α)
  结论: s inter t + u = (s + u) inter (t + u)
  证明: by
  by_contra! h
obtain ⟨a, ha⟩ := lt_iff_cons_le.1 h.lt_of_le le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
exact (lt_cons_self (s inter t) a).not_ge le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))


Depends on / 依赖: Multiset, Multiset.add_le_add_right, Multiset.le_of_add_le_add_right, add_le_add_right, cons_add, h.lt_of_le, ha.trans, inter_le_left, inter_le_right, le_inter, le_of_add_le_add_right, lt_cons_self, lt_iff_cons_le, lt_of_le, not_ge
-/
lemma inter_add_distrib (s t u : Multiset α) : s inter t + u = (s + u) inter (t + u) := by
  by_contra! h
obtain ⟨a, ha⟩ := lt_iff_cons_le.1 h.lt_of_le le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
exact (lt_cons_self (s inter t) a).not_ge le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_right))

/--
lemma `add_inter_distrib` / 引理 `add_inter_distrib`

English:
lemma add_inter_distrib
  given: (s t u : Multiset α)
  statement: s + t inter u = (s + t) inter (s + u)
  proof: by
  rw [Multiset.add_comm]; rw [inter_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

中文:
引理 add_inter_distrib
  条件: (s t u : Multiset α)
  结论: s + t inter u = (s + t) inter (s + u)
  证明: by
  rw [Multiset.add_comm]; rw [inter_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, inter_add_distrib, s.add_comm
-/
lemma add_inter_distrib (s t u : Multiset α) : s + t inter u = (s + t) inter (s + u) := by
  rw [Multiset.add_comm]; rw [inter_add_distrib]; rw [s.add_comm]; rw [s.add_comm]

/--
lemma `cons_inter_distrib` / 引理 `cons_inter_distrib`

English:
lemma cons_inter_distrib
  given: (a : α) (s t : Multiset α)
  statement: a ::ₘ s inter t = (a ::ₘ s) inter (a ::ₘ t)
  proof: by
  simp

中文:
引理 cons_inter_distrib
  条件: (a : α) (s t : Multiset α)
  结论: a ::ₘ s inter t = (a ::ₘ s) inter (a ::ₘ t)
  证明: by
  simp
-/
lemma cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s inter t = (a ::ₘ s) inter (a ::ₘ t) := by
  simp

/--
lemma `union_add_inter` / 引理 `union_add_inter`

English:
lemma union_add_inter
  given: (s t : Multiset α)
  statement: s union t + s inter t = s + t
  proof: by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union

中文:
引理 union_add_inter
  条件: (s t : Multiset α)
  结论: s union t + s inter t = s + t
  证明: by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union

Depends on / 依赖: Multiset, Multiset.add_comm, Multiset.add_le_add_left, Multiset.add_le_add_right, _root_, _root_.le_antisymm, add_comm, add_inter_distrib, add_le_add_left, add_le_add_right, inter_le_left, inter_le_right, le_antisymm, le_inter, le_union_left, le_union_right, union_add_distrib, union_le
-/
lemma union_add_inter (s t : Multiset α) : s union t + s inter t = s + t := by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right le_union_left

/--
lemma `sub_add_inter` / 引理 `sub_add_inter`

English:
lemma sub_add_inter
  given: (s t : Multiset α)
  statement: s - t + s inter t = s
  proof: by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a in s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_notMem h, IH]

中文:
引理 sub_add_inter
  条件: (s t : Multiset α)
  结论: s - t + s inter t = s
  证明: by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a in s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_notMem h, IH]

Depends on / 依赖: Multiset, Multiset.induction_on, add_cons, cons_erase, cons_inter_of_neg, cons_inter_of_pos, erase_of_notMem, induction_on, inter_comm, revert, sub_cons
-/
lemma sub_add_inter (s t : Multiset α) : s - t + s inter t = s := by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a in s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_notMem h, IH]

/--
lemma `sub_inter` / 引理 `sub_inter`

English:
lemma sub_inter
  given: (s t : Multiset α)
  statement: s - s inter t = s - t
  proof: (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]

中文:
引理 sub_inter
  条件: (s t : Multiset α)
  结论: s - s inter t = s - t
  证明: (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]

Depends on / 依赖: Multiset, Multiset.eq_sub_of_add_eq, eq_sub_of_add_eq, sub_add_inter
-/
lemma sub_inter (s t : Multiset α) : s - s inter t = s - t :=
  (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]
/--
lemma `count_inter` / 引理 `count_inter`

English:
lemma count_inter
  given: (a : α) (s t : Multiset α)
  statement: count a (s inter t) = min (count a s) (count a t)
  proof: by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add]; rw [sub_add_inter]; rw [count_sub]; rw [Nat.sub_add_min_cancel]

@[simp]

中文:
引理 count_inter
  条件: (a : α) (s t : Multiset α)
  结论: count a (s inter t) = 最小值 (count a s) (count a t)
  证明: by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add]; rw [sub_add_inter]; rw [count_sub]; rw [Nat.sub_add_min_cancel]

@[simp]

Depends on / 依赖: Nat.add_left_cancel, Nat.sub_add_min_cancel, add_left_cancel, count_add, count_sub, sub_add_inter, sub_add_min_cancel
-/
lemma count_inter (a : α) (s t : Multiset α) : count a (s inter t) = min (count a s) (count a t) := by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add]; rw [sub_add_inter]; rw [count_sub]; rw [Nat.sub_add_min_cancel]

@[simp]
/--
lemma `coe_inter` / 引理 `coe_inter`

English:
lemma coe_inter
  given: (s t : List α)
  statement: (s inter t : Multiset α) = (s.bagInter t : List α)
  proof: by ext; simp

中文:
引理 coe_inter
  条件: (s t : 列表 α)
  结论: (s inter t : Multiset α) = (s.bag整数er t : 列表 α)
  证明: by ext; simp
-/
lemma coe_inter (s t : List α) : (s inter t : Multiset α) = (s.bagInter t : List α) := by ext; simp

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: : DistribLattice (Multiset α) where
  body: ge_of_eq ext.2 fun a => by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]

中文:
实例 instDistribLattice
  签名: : Distrib格 (Multiset α) where
  定义体: ge_of_eq ext.2 fun a => by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]

Depends on / 依赖: Multiset, Multiset.count_inter, Multiset.count_union, Multiset.inf_eq_inter, Multiset.sup_eq_union, count_inter, count_union, ge_of_eq, inf_eq_inter, max_min_distrib_left, sup_eq_union
-/
instance instDistribLattice : DistribLattice (Multiset α) where
le_sup_inf s t u := ge_of_eq ext.2 fun a => by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]

/--
lemma `filter_inter` / 引理 `filter_inter`

English:
lemma filter_inter
  given: (p : α -> Prop) [DecidablePred p] (s t : Multiset α)
  proof: le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right))
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]

中文:
引理 filter_inter
  条件: (p : α -> 命题) [DecidablePred p] (s t : Multiset α)
  证明: le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right))
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]
-/
@[simp] lemma filter_inter (p : α -> Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s inter t) = filter p s inter filter p t :=
le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right))
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]
/--
theorem `replicate_inter` / 定理 `replicate_inter`

English:
theorem replicate_inter
  given: (n : Nat) (x : α) (s : Multiset α)
  proof: by
  ext y
  rw [count_inter]; rw [count_replicate]; rw [count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]

中文:
定理 replicate_inter
  条件: (n : 自然数) (x : α) (s : Multiset α)
  证明: by
  ext y
  rw [count_inter]; rw [count_replicate]; rw [count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]

Depends on / 依赖: Nat.zero_min, count_inter, count_replicate, if_false, if_true, zero_min
-/
theorem replicate_inter (n : Nat) (x : α) (s : Multiset α) :
    replicate n x inter s = replicate (min n (s.count x)) x := by
  ext y
  rw [count_inter]; rw [count_replicate]; rw [count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]
/--
theorem `inter_replicate` / 定理 `inter_replicate`

English:
theorem inter_replicate
  given: (s : Multiset α) (n : Nat) (x : α)
  proof: by
  rw [inter_comm]; rw [replicate_inter]; rw [min_comm]

中文:
定理 inter_replicate
  条件: (s : Multiset α) (n : 自然数) (x : α)
  证明: by
  rw [inter_comm]; rw [replicate_inter]; rw [min_comm]

Depends on / 依赖: inter_comm, min_comm, replicate_inter
-/
theorem inter_replicate (s : Multiset α) (n : Nat) (x : α) :
    s inter replicate n x = replicate (min (s.count x) n) x := by
  rw [inter_comm]; rw [replicate_inter]; rw [min_comm]

end sub

/--
theorem `inter_add_sub_of_add_eq_add` / 定理 `inter_add_sub_of_add_eq_add`

English:
theorem inter_add_sub_of_add_eq_add
  given: [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q)
  proof: by
  ext x
  rw [Multiset.count_add]; rw [Multiset.count_inter]; rw [Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.count_add]
  omega

中文:
定理 inter_add_sub_of_add_eq_add
  条件: [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q)
  证明: by
  ext x
  rw [Multiset.count_add]; rw [Multiset.count_inter]; rw [Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.count_add]
  omega

Depends on / 依赖: M.count, Multiset, Multiset.count_add, Multiset.count_inter, Multiset.count_sub, Multiset.ext, N.count, P.count, Q.count, count_add, count_inter, count_sub
-/
theorem inter_add_sub_of_add_eq_add [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q) :
    (N inter Q) + (P - M) = N := by
  ext x
  rw [Multiset.count_add]; rw [Multiset.count_inter]; rw [Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.count_add]
  omega


/--
theorem `disjoint_left` / 定理 `disjoint_left`

English:
theorem disjoint_left
  given: {s t : Multiset α}
  statement: Disjoint s t ↔ forall {a}, a in s -> a ∉ t
  proof: by
  refine ⟨fun h a hs ht => ?_, fun h u hs ht => ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha => h (subset_of_le hs ha) (subset_of_le ht ha)

alias ⟨_root_.Disjoint.notMem_of_mem_left_multiset, _⟩ :

中文:
定理 disjoint_left
  条件: {s t : Multiset α}
  结论: Disjoint s t ↔ 对任意 {a}, a in s -> a ∉ t
  证明: by
  refine ⟨fun h a hs ht => ?_, fun h u hs ht => ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha => h (subset_of_le hs ha) (subset_of_le ht ha)

alias ⟨_root_.Disjoint.notMem_of_mem_left_multiset, _⟩ :

Depends on / 依赖: bot_eq_zero, eq_zero_iff_forall_notMem, le_bot_iff, singleton_le, singleton_le.mpr, subset_of_le
-/
theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ forall {a}, a in s -> a ∉ t := by
  refine ⟨fun h a hs ht => ?_, fun h u hs ht => ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha => h (subset_of_le hs ha) (subset_of_le ht ha)

alias ⟨_root_.Disjoint.notMem_of_mem_left_multiset, _⟩ := disjoint_left

@[simp, norm_cast]
/--
theorem `coe_disjoint` / 定理 `coe_disjoint`

English:
theorem coe_disjoint
  given: (l₁ l₂ : List α)
  statement: Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂
  proof: disjoint_left

中文:
定理 coe_disjoint
  条件: (l₁ l₂ : 列表 α)
  结论: Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂
  证明: disjoint_left

Depends on / 依赖: disjoint_left
-/
theorem coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂ :=
  disjoint_left

/--
theorem `disjoint_right` / 定理 `disjoint_right`

English:
theorem disjoint_right
  given: {s t : Multiset α}
  statement: Disjoint s t ↔ forall {a}, a in t -> a ∉ s
  proof: disjoint_comm.trans disjoint_left

alias ⟨_root_.Disjoint.notMem_of_mem_right_multiset, _⟩ := disjoint_right

中文:
定理 disjoint_right
  条件: {s t : Multiset α}
  结论: Disjoint s t ↔ 对任意 {a}, a in t -> a ∉ s
  证明: disjoint_comm.trans disjoint_left

alias ⟨_root_.Disjoint.notMem_of_mem_right_multiset, _⟩ := disjoint_right

Depends on / 依赖: disjoint_comm, disjoint_comm.trans, disjoint_left
-/
theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ forall {a}, a in t -> a ∉ s :=
  disjoint_comm.trans disjoint_left

alias ⟨_root_.Disjoint.notMem_of_mem_right_multiset, _⟩ := disjoint_right

/--
theorem `disjoint_iff_ne` / 定理 `disjoint_iff_ne`

English:
theorem disjoint_iff_ne
  given: {s t : Multiset α}
  statement: Disjoint s t ↔ forall a in s, forall b in t, a != b
  proof: by
  simp [disjoint_left, imp_not_comm]

中文:
定理 disjoint_iff_ne
  条件: {s t : Multiset α}
  结论: Disjoint s t ↔ 对任意 a in s, 对任意 b in t, a != b
  证明: by
  simp [disjoint_left, imp_not_comm]

Depends on / 依赖: disjoint_left, imp_not_comm
-/
theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ forall a in s, forall b in t, a != b := by
  simp [disjoint_left, imp_not_comm]

/--
theorem `disjoint_of_subset_left` / 定理 `disjoint_of_subset_left`

English:
theorem disjoint_of_subset_left
  given: {s t u : Multiset α} (h : s subseteq u) (d : Disjoint u t)
  proof: disjoint_left.mpr fun ha => disjoint_left.mp d h ha

中文:
定理 disjoint_of_subset_left
  条件: {s t u : Multiset α} (h : s subseteq u) (d : Disjoint u t)
  证明: disjoint_left.mpr fun ha => disjoint_left.mp d h ha

Depends on / 依赖: disjoint_left, disjoint_left.mp, disjoint_left.mpr
-/
theorem disjoint_of_subset_left {s t u : Multiset α} (h : s subseteq u) (d : Disjoint u t) :
    Disjoint s t :=
disjoint_left.mpr fun ha => disjoint_left.mp d h ha

/--
theorem `disjoint_of_subset_right` / 定理 `disjoint_of_subset_right`

English:
theorem disjoint_of_subset_right
  given: {s t u : Multiset α} (h : t subseteq u) (d : Disjoint s u)
  proof: (disjoint_of_subset_left h d.symm).symm

@[simp]

中文:
定理 disjoint_of_subset_right
  条件: {s t u : Multiset α} (h : t subseteq u) (d : Disjoint s u)
  证明: (disjoint_of_subset_left h d.symm).symm

@[simp]

Depends on / 依赖: d.symm, disjoint_of_subset_left
-/
theorem disjoint_of_subset_right {s t u : Multiset α} (h : t subseteq u) (d : Disjoint s u) :
    Disjoint s t :=
  (disjoint_of_subset_left h d.symm).symm

@[simp]
/--
theorem `zero_disjoint` / 定理 `zero_disjoint`

English:
theorem zero_disjoint
  given: (l : Multiset α)
  statement: Disjoint 0 l
  proof: disjoint_bot_left

@[simp]

中文:
定理 zero_disjoint
  条件: (l : Multiset α)
  结论: Disjoint 0 l
  证明: disjoint_bot_left

@[simp]

Depends on / 依赖: disjoint_bot_left
-/
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l := disjoint_bot_left

@[simp]
/--
theorem `singleton_disjoint` / 定理 `singleton_disjoint`

English:
theorem singleton_disjoint
  given: {l : Multiset α} {a : α}
  statement: Disjoint {a} l ↔ a ∉ l
  proof: by
  simp [disjoint_left]

@[simp]

中文:
定理 singleton_disjoint
  条件: {l : Multiset α} {a : α}
  结论: Disjoint {a} l ↔ a ∉ l
  证明: by
  simp [disjoint_left]

@[simp]

Depends on / 依赖: disjoint_left
-/
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [disjoint_left]

@[simp]
/--
theorem `disjoint_singleton` / 定理 `disjoint_singleton`

English:
theorem disjoint_singleton
  given: {l : Multiset α} {a : α}
  statement: Disjoint l {a} ↔ a ∉ l
  proof: by
  rw [_root_.disjoint_comm]; rw [singleton_disjoint]

@[simp]

中文:
定理 disjoint_singleton
  条件: {l : Multiset α} {a : α}
  结论: Disjoint l {a} ↔ a ∉ l
  证明: by
  rw [_root_.disjoint_comm]; rw [singleton_disjoint]

@[simp]

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, singleton_disjoint
-/
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [_root_.disjoint_comm]; rw [singleton_disjoint]

@[simp]
/--
theorem `disjoint_add_left` / 定理 `disjoint_add_left`

English:
theorem disjoint_add_left
  given: {s t u : Multiset α}
  proof: by simp [disjoint_left, or_imp, forall_and]

@[simp]

中文:
定理 disjoint_add_left
  条件: {s t u : Multiset α}
  证明: by simp [disjoint_left, or_imp, forall_and]

@[simp]

Depends on / 依赖: disjoint_left, forall_and, or_imp
-/
theorem disjoint_add_left {s t u : Multiset α} :
    Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u := by simp [disjoint_left, or_imp, forall_and]

@[simp]
/--
theorem `disjoint_add_right` / 定理 `disjoint_add_right`

English:
theorem disjoint_add_right
  given: {s t u : Multiset α}
  proof: by
  rw [_root_.disjoint_comm]; rw [disjoint_add_left]; tauto

@[simp]

中文:
定理 disjoint_add_right
  条件: {s t u : Multiset α}
  证明: by
  rw [_root_.disjoint_comm]; rw [disjoint_add_left]; tauto

@[simp]

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_add_left, disjoint_comm
-/
theorem disjoint_add_right {s t u : Multiset α} :
    Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [_root_.disjoint_comm]; rw [disjoint_add_left]; tauto

@[simp]
/--
theorem `disjoint_cons_left` / 定理 `disjoint_cons_left`

English:
theorem disjoint_cons_left
  given: {a : α} {s t : Multiset α}
  proof: (@disjoint_add_left _ {a} s t).trans by rw [singleton_disjoint]

@[simp]

中文:
定理 disjoint_cons_left
  条件: {a : α} {s t : Multiset α}
  证明: (@disjoint_add_left _ {a} s t).trans by rw [singleton_disjoint]

@[simp]

Depends on / 依赖: disjoint_add_left, singleton_disjoint
-/
theorem disjoint_cons_left {a : α} {s t : Multiset α} :
    Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
(@disjoint_add_left _ {a} s t).trans by rw [singleton_disjoint]

@[simp]
/--
theorem `disjoint_cons_right` / 定理 `disjoint_cons_right`

English:
theorem disjoint_cons_right
  given: {a : α} {s t : Multiset α}
  proof: by
  rw [_root_.disjoint_comm]; rw [disjoint_cons_left]; tauto

中文:
定理 disjoint_cons_right
  条件: {a : α} {s t : Multiset α}
  证明: by
  rw [_root_.disjoint_comm]; rw [disjoint_cons_left]; tauto

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, disjoint_cons_left
-/
theorem disjoint_cons_right {a : α} {s t : Multiset α} :
    Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm]; rw [disjoint_cons_left]; tauto

/--
theorem `inter_eq_zero_iff_disjoint` / 定理 `inter_eq_zero_iff_disjoint`

English:
theorem inter_eq_zero_iff_disjoint
  given: [DecidableEq α] {s t : Multiset α}
  proof: by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]

中文:
定理 inter_eq_zero_iff_disjoint
  条件: [DecidableEq α] {s t : Multiset α}
  证明: by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]

Depends on / 依赖: disjoint_left, subset_iff, subset_zero
-/
theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s inter t = 0 ↔ Disjoint s t := by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]
/--
theorem `disjoint_union_left` / 定理 `disjoint_union_left`

English:
theorem disjoint_union_left
  given: [DecidableEq α] {s t u : Multiset α}
  proof: disjoint_sup_left

@[simp]

中文:
定理 disjoint_union_left
  条件: [DecidableEq α] {s t u : Multiset α}
  证明: disjoint_sup_left

@[simp]

Depends on / 依赖: disjoint_sup_left
-/
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} :
    Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left

@[simp]
/--
theorem `disjoint_union_right` / 定理 `disjoint_union_right`

English:
theorem disjoint_union_right
  given: [DecidableEq α] {s t u : Multiset α}
  proof: disjoint_sup_right

中文:
定理 disjoint_union_right
  条件: [DecidableEq α] {s t u : Multiset α}
  证明: disjoint_sup_right

Depends on / 依赖: disjoint_sup_right
-/
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} :
    Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right

/--
theorem `add_eq_union_iff_disjoint` / 定理 `add_eq_union_iff_disjoint`

English:
theorem add_eq_union_iff_disjoint
  given: [DecidableEq α] {s t : Multiset α}
  proof: by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]

中文:
定理 add_eq_union_iff_disjoint
  条件: [DecidableEq α] {s t : Multiset α}
  证明: by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]

Depends on / 依赖: Nat.add_eq_max_iff, Nat.min_eq_zero_iff, add_eq_max_iff, count_add, count_inter, count_union, count_zero, inter_eq_zero_iff_disjoint, min_eq_zero_iff, simp_rw
-/
theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s + t = s union t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]

/--
lemma `add_eq_union_left_of_le` / 引理 `add_eq_union_left_of_le`

English:
lemma add_eq_union_left_of_le
  given: [DecidableEq α] {s t u : Multiset α} (h : t <= s)
  proof: by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

中文:
引理 add_eq_union_left_of_le
  条件: [DecidableEq α] {s t u : Multiset α} (h : t <= s)
  证明: by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

Depends on / 依赖: Multiset, Multiset.le_of_add_le_add_left, add_eq_union_iff_disjoint, and_iff_right_of_imp, antisymm, h0.trans_le, le_of_add_le_add_left, trans_le, union_le_add
-/
lemma add_eq_union_left_of_le [DecidableEq α] {s t u : Multiset α} (h : t <= s) :
    u + s = u union t ↔ Disjoint u s ∧ s = t := by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

/--
lemma `add_eq_union_right_of_le` / 引理 `add_eq_union_right_of_le`

English:
lemma add_eq_union_right_of_le
  given: [DecidableEq α] {x y z : Multiset α} (h : z <= y)
  proof: by
  simpa only [and_comm] using add_eq_union_left_of_le h

中文:
引理 add_eq_union_right_of_le
  条件: [DecidableEq α] {x y z : Multiset α} (h : z <= y)
  证明: by
  simpa only [and_comm] using add_eq_union_left_of_le h

Depends on / 依赖: add_eq_union_left_of_le, and_comm
-/
lemma add_eq_union_right_of_le [DecidableEq α] {x y z : Multiset α} (h : z <= y) :
    x + y = x union z ↔ y = z ∧ Disjoint x y := by
  simpa only [and_comm] using add_eq_union_left_of_le h

/--
theorem `disjoint_map_map` / 定理 `disjoint_map_map`

English:
theorem disjoint_map_map
  given: {f : α -> γ} {g : β -> γ} {s : Multiset α} {t : Multiset β}
  proof: by
  simp [disjoint_iff_ne]

中文:
定理 disjoint_map_map
  条件: {f : α -> γ} {g : β -> γ} {s : Multiset α} {t : Multiset β}
  证明: by
  simp [disjoint_iff_ne]

Depends on / 依赖: disjoint_iff_ne
-/
theorem disjoint_map_map {f : α -> γ} {g : β -> γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ forall a in s, forall b in t, f a != g b := by
  simp [disjoint_iff_ne]

/--
theorem `map_set_pairwise` / 定理 `map_set_pairwise`

English:
theorem map_set_pairwise
  statement: {f : α -> β} {r : β -> β -> Prop} {m : Multiset α}
  proof: fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

中文:
定理 map_set_pairwise
  结论: {f : α -> β} {r : β -> β -> 命题} {m : Multiset α}
  证明: fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

Depends on / 依赖: Multiset, Multiset.mem_map, congr_arg, mem_map
-/
theorem map_set_pairwise {f : α -> β} {r : β -> β -> Prop} {m : Multiset α}
    (h : { a | a in m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b in m.map f }.Pairwise r :=
  fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

section Nodup

variable {s t : Multiset α} {a : α}

/--
theorem `nodup_add` / 定理 `nodup_add`

English:
theorem nodup_add
  given: {s t : Multiset α}
  statement: Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t
  proof: Quotient.inductionOn₂ s t fun _ _ => by simp [nodup_append, disjoint_iff_ne]

中文:
定理 nodup_add
  条件: {s t : Multiset α}
  结论: Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t
  证明: Quotient.inductionOn₂ s t fun _ _ => by simp [nodup_append, disjoint_iff_ne]

Depends on / 依赖: Quotient, Quotient.inductionOn, disjoint_iff_ne, nodup_append
-/
theorem nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t :=
  Quotient.inductionOn₂ s t fun _ _ => by simp [nodup_append, disjoint_iff_ne]

/--
theorem `disjoint_of_nodup_add` / 定理 `disjoint_of_nodup_add`

English:
theorem disjoint_of_nodup_add
  given: {s t : Multiset α} (d : Nodup (s + t))
  statement: Disjoint s t
  proof: (nodup_add.1 d).2.2

中文:
定理 disjoint_of_nodup_add
  条件: {s t : Multiset α} (d : Nodup (s + t))
  结论: Disjoint s t
  证明: (nodup_add.1 d).2.2

Depends on / 依赖: nodup_add
-/
theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2

/--
theorem `Nodup.add_iff` / 定理 `Nodup.add_iff`

English:
theorem Nodup.add_iff
  given: (d₁ : Nodup s) (d₂ : Nodup t)
  statement: Nodup (s + t) ↔ Disjoint s t
  proof: by
  simp [nodup_add, d₁, d₂]

中文:
定理 Nodup.add_iff
  条件: (d₁ : Nodup s) (d₂ : Nodup t)
  结论: Nodup (s + t) ↔ Disjoint s t
  证明: by
  simp [nodup_add, d₁, d₂]

Depends on / 依赖: nodup_add
-/
theorem Nodup.add_iff (d₁ : Nodup s) (d₂ : Nodup t) : Nodup (s + t) ↔ Disjoint s t := by
  simp [nodup_add, d₁, d₂]

/--
lemma `Nodup.inter_left` / 引理 `Nodup.inter_left`

English:
lemma Nodup.inter_left
  given: [DecidableEq α] (t)
  statement: Nodup s -> Nodup (s inter t)
  proof: nodup_of_le inter_le_left

中文:
引理 Nodup.inter_left
  条件: [DecidableEq α] (t)
  结论: Nodup s -> Nodup (s inter t)
  证明: nodup_of_le inter_le_left

Depends on / 依赖: inter_le_left, nodup_of_le
-/
lemma Nodup.inter_left [DecidableEq α] (t) : Nodup s -> Nodup (s inter t) := nodup_of_le inter_le_left
/--
lemma `Nodup.inter_right` / 引理 `Nodup.inter_right`

English:
lemma Nodup.inter_right
  given: [DecidableEq α] (s)
  statement: Nodup t -> Nodup (s inter t)
  proof: nodup_of_le inter_le_right

@[simp]

中文:
引理 Nodup.inter_right
  条件: [DecidableEq α] (s)
  结论: Nodup t -> Nodup (s inter t)
  证明: nodup_of_le inter_le_right

@[simp]

Depends on / 依赖: inter_le_right, nodup_of_le
-/
lemma Nodup.inter_right [DecidableEq α] (s) : Nodup t -> Nodup (s inter t) := nodup_of_le inter_le_right

@[simp]
/--
theorem `nodup_union` / 定理 `nodup_union`

English:
theorem nodup_union
  given: [DecidableEq α] {s t : Multiset α}
  statement: Nodup (s union t) ↔ Nodup s ∧ Nodup t
  proof: ⟨fun h => ⟨nodup_of_le le_union_left h, nodup_of_le le_union_right h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

中文:
定理 nodup_union
  条件: [DecidableEq α] {s t : Multiset α}
  结论: Nodup (s union t) ↔ Nodup s ∧ Nodup t
  证明: ⟨fun h => ⟨nodup_of_le le_union_left h, nodup_of_le le_union_right h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

Depends on / 依赖: count_union, le_union_left, le_union_right, max_le, nodup_iff_count_le_one, nodup_of_le
-/
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s union t) ↔ Nodup s ∧ Nodup t :=
  ⟨fun h => ⟨nodup_of_le le_union_left h, nodup_of_le le_union_right h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

end Nodup

end Multiset
