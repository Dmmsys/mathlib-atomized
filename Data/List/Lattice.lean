/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Kim Morrison
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lattice structure of lists

This file proves basic properties about `List.disjoint`, `List.union`, `List.inter` and
`List.bagInter`, which are defined in core Lean and `Data.List.Defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [1, 2, 4, 3, 3, 0]`.

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 0, 1, 2, 2, 3] ∩ [4, 3, 3, 0] = [0, 0, 3]`.

`List.bagInter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`,
counted with multiplicity and in the order they appear in `l₁`.
As opposed to `List.inter`, `List.bagInter` copes well with multiplicity. For example,
`bagInter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`.
-/

public section


open Nat

namespace List

variable {α : Type*} {l₁ l₂ : List α} {p : α -> Prop} {a : α}

/-! ### `Disjoint` -/


section Disjoint

@[symm]
/--
theorem `Disjoint.symm` / 定理 `Disjoint.symm`

English:
theorem Disjoint.symm
  given: (d : Disjoint l₁ l₂)
  statement: Disjoint l₂ l₁
  proof: fun _ i₂ i₁ => d i₁ i₂

中文:
定理 Disjoint.symm
  条件: (d : Disjoint l₁ l₂)
  结论: Disjoint l₂ l₁
  证明: fun _ i₂ i₁ => d i₁ i₂
-/
theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂

end Disjoint

variable [DecidableEq α]

/-! ### `union` -/


section Union

/--
theorem `mem_union_left` / 定理 `mem_union_left`

English:
theorem mem_union_left
  given: (h : a in l₁) (l₂ : List α)
  statement: a in l₁ union l₂
  proof: mem_union_iff.2 (Or.inl h)

中文:
定理 mem_union_left
  条件: (h : a in l₁) (l₂ : 列表 α)
  结论: a in l₁ union l₂
  证明: mem_union_iff.2 (Or.inl h)

Depends on / 依赖: Or.inl, mem_union_iff
-/
theorem mem_union_left (h : a in l₁) (l₂ : List α) : a in l₁ union l₂ :=
  mem_union_iff.2 (Or.inl h)

/--
theorem `mem_union_right` / 定理 `mem_union_right`

English:
theorem mem_union_right
  given: (l₁ : List α) (h : a in l₂)
  statement: a in l₁ union l₂
  proof: mem_union_iff.2 (Or.inr h)

中文:
定理 mem_union_right
  条件: (l₁ : 列表 α) (h : a in l₂)
  结论: a in l₁ union l₂
  证明: mem_union_iff.2 (Or.inr h)

Depends on / 依赖: Or.inr, mem_union_iff
-/
theorem mem_union_right (l₁ : List α) (h : a in l₂) : a in l₁ union l₂ :=
  mem_union_iff.2 (Or.inr h)

/--
theorem `sublist_suffix_of_union` / 定理 `sublist_suffix_of_union`

English:
theorem sublist_suffix_of_union
  statement: forall l₁ l₂ : List α, exists t, t <+ l₁ ∧ t ++ l₂ = l₁ union l₂
  proof: sublist_suffix_of_union l₁ l₂
    if h : a in l₁ union l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩

中文:
定理 sublist_suffix_of_union
  结论: 对任意 l₁ l₂ : 列表 α, 存在 t, t <+ l₁ ∧ t ++ l₂ = l₁ union l₂
  证明: sublist_suffix_of_union l₁ l₂
    if h : a in l₁ union l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩

Depends on / 依赖: sublist_suffix_of_union
-/
theorem sublist_suffix_of_union : forall l₁ l₂ : List α, exists t, t <+ l₁ ∧ t ++ l₂ = l₁ union l₂
  | [], _ => ⟨[], by rfl, rfl⟩
  | a :: l₁, l₂ =>
    let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
    if h : a in l₁ union l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩

/--
theorem `suffix_union_right` / 定理 `suffix_union_right`

English:
theorem suffix_union_right
  given: (l₁ l₂ : List α)
  statement: l₂ <:+ l₁ union l₂
  proof: (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right

中文:
定理 suffix_union_right
  条件: (l₁ l₂ : 列表 α)
  结论: l₂ <:+ l₁ union l₂
  证明: (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right

Depends on / 依赖: And.right, sublist_suffix_of_union
-/
theorem suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ union l₂ :=
  (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right

/--
theorem `union_sublist_append` / 定理 `union_sublist_append`

English:
theorem union_sublist_append
  given: (l₁ l₂ : List α)
  statement: l₁ union l₂ <+ l₁ ++ l₂
  proof: let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s

中文:
定理 union_sublist_append
  条件: (l₁ l₂ : 列表 α)
  结论: l₁ union l₂ <+ l₁ ++ l₂
  证明: let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s

Depends on / 依赖: append_sublist_append_right, sublist_suffix_of_union
-/
theorem union_sublist_append (l₁ l₂ : List α) : l₁ union l₂ <+ l₁ ++ l₂ :=
  let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s

/--
theorem `forall_mem_union` / 定理 `forall_mem_union`

English:
theorem forall_mem_union
  statement: (forall x in l₁ union l₂, p x) ↔ (forall x in l₁, p x) ∧ forall x in l₂, p x
  proof: by
  simp only [mem_union_iff, or_imp, forall_and]

中文:
定理 对任意_mem_union
  结论: (对任意 x in l₁ union l₂, p x) ↔ (对任意 x in l₁, p x) ∧ 对任意 x in l₂, p x
  证明: by
  simp only [mem_union_iff, or_imp, forall_and]

Depends on / 依赖: forall_and, mem_union_iff, or_imp
-/
theorem forall_mem_union : (forall x in l₁ union l₂, p x) ↔ (forall x in l₁, p x) ∧ forall x in l₂, p x := by
  simp only [mem_union_iff, or_imp, forall_and]

/--
theorem `forall_mem_of_forall_mem_union_left` / 定理 `forall_mem_of_forall_mem_union_left`

English:
theorem forall_mem_of_forall_mem_union_left
  given: (h : forall x in l₁ union l₂, p x)
  statement: forall x in l₁, p x
  proof: (forall_mem_union.1 h).1

中文:
定理 对任意_mem_of_对任意_mem_union_left
  条件: (h : 对任意 x in l₁ union l₂, p x)
  结论: 对任意 x in l₁, p x
  证明: (forall_mem_union.1 h).1

Depends on / 依赖: forall_mem_union
-/
theorem forall_mem_of_forall_mem_union_left (h : forall x in l₁ union l₂, p x) : forall x in l₁, p x :=
  (forall_mem_union.1 h).1

/--
theorem `forall_mem_of_forall_mem_union_right` / 定理 `forall_mem_of_forall_mem_union_right`

English:
theorem forall_mem_of_forall_mem_union_right
  given: (h : forall x in l₁ union l₂, p x)
  statement: forall x in l₂, p x
  proof: (forall_mem_union.1 h).2

中文:
定理 对任意_mem_of_对任意_mem_union_right
  条件: (h : 对任意 x in l₁ union l₂, p x)
  结论: 对任意 x in l₂, p x
  证明: (forall_mem_union.1 h).2

Depends on / 依赖: forall_mem_union
-/
theorem forall_mem_of_forall_mem_union_right (h : forall x in l₁ union l₂, p x) : forall x in l₂, p x :=
  (forall_mem_union.1 h).2

/--
theorem `Subset.union_eq_right` / 定理 `Subset.union_eq_right`

English:
theorem Subset.union_eq_right
  given: {xs ys : List α} (h : xs subseteq ys)
  statement: xs union ys = ys
  proof: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]; rw [insert_of_mem <| mem_union_right _ <| h mem_cons_self]; rw [ih subset_of_cons_subset h]

中文:
定理 子集.union_eq_right
  条件: {xs ys : 列表 α} (h : xs subseteq ys)
  结论: xs union ys = ys
  证明: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]; rw [insert_of_mem <| mem_union_right _ <| h mem_cons_self]; rw [ih subset_of_cons_subset h]

Depends on / 依赖: cons_union, insert_of_mem, mem_cons_self, mem_union_right, subset_of_cons_subset
-/
theorem Subset.union_eq_right {xs ys : List α} (h : xs subseteq ys) : xs union ys = ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]; rw [insert_of_mem <| mem_union_right _ <| h mem_cons_self]; rw [ih subset_of_cons_subset h]

end Union

/-! ### `inter` -/


section Inter

@[simp, grind =]
/--
theorem `inter_nil` / 定理 `inter_nil`

English:
theorem inter_nil
  given: (l : List α)
  statement: [] inter l = []
  proof: rfl

@[simp]

中文:
定理 inter_nil
  条件: (l : 列表 α)
  结论: [] inter l = []
  证明: rfl

@[simp]
-/
theorem inter_nil (l : List α) : [] inter l = [] :=
  rfl

@[simp]
/--
theorem `inter_cons_of_mem` / 定理 `inter_cons_of_mem`

English:
theorem inter_cons_of_mem
  given: (l₁ : List α) (h : a in l₂)
  statement: (a :: l₁) inter l₂ = a :: l₁ inter l₂
  proof: by
  simp [Inter.inter, List.inter, h]

@[simp]

中文:
定理 inter_cons_of_mem
  条件: (l₁ : 列表 α) (h : a in l₂)
  结论: (a :: l₁) inter l₂ = a :: l₁ inter l₂
  证明: by
  simp [Inter.inter, List.inter, h]

@[simp]

Depends on / 依赖: Inter.inter, List.inter
-/
theorem inter_cons_of_mem (l₁ : List α) (h : a in l₂) : (a :: l₁) inter l₂ = a :: l₁ inter l₂ := by
  simp [Inter.inter, List.inter, h]

@[simp]
/--
theorem `inter_cons_of_notMem` / 定理 `inter_cons_of_notMem`

English:
theorem inter_cons_of_notMem
  given: (l₁ : List α) (h : a ∉ l₂)
  statement: (a :: l₁) inter l₂ = l₁ inter l₂
  proof: by
  simp [Inter.inter, List.inter, h]

@[grind =]

中文:
定理 inter_cons_of_notMem
  条件: (l₁ : 列表 α) (h : a ∉ l₂)
  结论: (a :: l₁) inter l₂ = l₁ inter l₂
  证明: by
  simp [Inter.inter, List.inter, h]

@[grind =]

Depends on / 依赖: Inter.inter, List.inter
-/
theorem inter_cons_of_notMem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) inter l₂ = l₁ inter l₂ := by
  simp [Inter.inter, List.inter, h]

@[grind =]
/--
theorem `inter_cons` / 定理 `inter_cons`

English:
theorem inter_cons
  given: (l₁ : List α)
  proof: by
  split_ifs <;> simp_all

@[simp, grind =]

中文:
定理 inter_cons
  条件: (l₁ : 列表 α)
  证明: by
  split_ifs <;> simp_all

@[simp, grind =]

Depends on / 依赖: split_ifs
-/
theorem inter_cons (l₁ : List α) :
    (a :: l₁) inter l₂ = if a in l₂ then a :: l₁ inter l₂ else l₁ inter l₂ := by
  split_ifs <;> simp_all

@[simp, grind =]
/--
theorem `inter_nil'` / 定理 `inter_nil'`

English:
theorem inter_nil'
  given: (l : List α)
  statement: l inter [] = []
  proof: by
  induction l with grind

中文:
定理 inter_nil'
  条件: (l : 列表 α)
  结论: l inter [] = []
  证明: by
  induction l with grind
-/
theorem inter_nil' (l : List α) : l inter [] = [] := by
  induction l with grind

/--
theorem `mem_of_mem_inter_left` / 定理 `mem_of_mem_inter_left`

English:
theorem mem_of_mem_inter_left
  statement: a in l₁ inter l₂ -> a in l₁
  proof: mem_of_mem_filter

中文:
定理 mem_of_mem_inter_left
  结论: a in l₁ inter l₂ -> a in l₁
  证明: mem_of_mem_filter

Depends on / 依赖: mem_of_mem_filter
-/
theorem mem_of_mem_inter_left : a in l₁ inter l₂ -> a in l₁ :=
  mem_of_mem_filter

/--
theorem `mem_of_mem_inter_right` / 定理 `mem_of_mem_inter_right`

English:
theorem mem_of_mem_inter_right
  given: (h : a in l₁ inter l₂)
  statement: a in l₂
  proof: by simpa using of_mem_filter h

中文:
定理 mem_of_mem_inter_right
  条件: (h : a in l₁ inter l₂)
  结论: a in l₂
  证明: by simpa using of_mem_filter h

Depends on / 依赖: of_mem_filter
-/
theorem mem_of_mem_inter_right (h : a in l₁ inter l₂) : a in l₂ := by simpa using of_mem_filter h

/--
theorem `mem_inter_of_mem_of_mem` / 定理 `mem_inter_of_mem_of_mem`

English:
theorem mem_inter_of_mem_of_mem
  given: (h₁ : a in l₁) (h₂ : a in l₂)
  statement: a in l₁ inter l₂
  proof: mem_filter_of_mem h₁ by simpa using h₂

中文:
定理 mem_inter_of_mem_of_mem
  条件: (h₁ : a in l₁) (h₂ : a in l₂)
  结论: a in l₁ inter l₂
  证明: mem_filter_of_mem h₁ by simpa using h₂

Depends on / 依赖: mem_filter_of_mem
-/
theorem mem_inter_of_mem_of_mem (h₁ : a in l₁) (h₂ : a in l₂) : a in l₁ inter l₂ :=
mem_filter_of_mem h₁ by simpa using h₂

/--
theorem `inter_subset_left` / 定理 `inter_subset_left`

English:
theorem inter_subset_left
  given: {l₁ l₂ : List α}
  statement: l₁ inter l₂ subseteq l₁
  proof: filter_subset_self _

中文:
定理 inter_subset_left
  条件: {l₁ l₂ : 列表 α}
  结论: l₁ inter l₂ subseteq l₁
  证明: filter_subset_self _

Depends on / 依赖: filter_subset_self
-/
theorem inter_subset_left {l₁ l₂ : List α} : l₁ inter l₂ subseteq l₁ :=
  filter_subset_self _

/--
theorem `inter_subset_right` / 定理 `inter_subset_right`

English:
theorem inter_subset_right
  given: {l₁ l₂ : List α}
  statement: l₁ inter l₂ subseteq l₂
  proof: fun _ => mem_of_mem_inter_right

中文:
定理 inter_subset_right
  条件: {l₁ l₂ : 列表 α}
  结论: l₁ inter l₂ subseteq l₂
  证明: fun _ => mem_of_mem_inter_right

Depends on / 依赖: mem_of_mem_inter_right
-/
theorem inter_subset_right {l₁ l₂ : List α} : l₁ inter l₂ subseteq l₂ := fun _ => mem_of_mem_inter_right

/--
theorem `subset_inter` / 定理 `subset_inter`

English:
theorem subset_inter
  given: {l l₁ l₂ : List α} (h₁ : l subseteq l₁) (h₂ : l subseteq l₂)
  statement: l subseteq l₁ inter l₂
  proof: fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩

中文:
定理 subset_inter
  条件: {l l₁ l₂ : 列表 α} (h₁ : l subseteq l₁) (h₂ : l subseteq l₂)
  结论: l subseteq l₁ inter l₂
  证明: fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩
-/
theorem subset_inter {l l₁ l₂ : List α} (h₁ : l subseteq l₁) (h₂ : l subseteq l₂) : l subseteq l₁ inter l₂ := fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩

/--
theorem `inter_eq_nil_iff_disjoint` / 定理 `inter_eq_nil_iff_disjoint`

English:
theorem inter_eq_nil_iff_disjoint
  statement: l₁ inter l₂ = [] ↔ Disjoint l₁ l₂
  proof: by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  rfl

alias ⟨_, Disjoint.inter_eq_nil⟩ := inter_eq_nil_iff_disjoint

中文:
定理 inter_eq_nil_iff_disjoint
  结论: l₁ inter l₂ = [] ↔ Disjoint l₁ l₂
  证明: by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  rfl

alias ⟨_, Disjoint.inter_eq_nil⟩ := inter_eq_nil_iff_disjoint

Depends on / 依赖: eq_nil_iff_forall_not_mem, mem_inter_iff, not_and
-/
theorem inter_eq_nil_iff_disjoint : l₁ inter l₂ = [] ↔ Disjoint l₁ l₂ := by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  rfl

alias ⟨_, Disjoint.inter_eq_nil⟩ := inter_eq_nil_iff_disjoint

/--
theorem `forall_mem_inter_of_forall_left` / 定理 `forall_mem_inter_of_forall_left`

English:
theorem forall_mem_inter_of_forall_left
  given: (h : forall x in l₁, p x) (l₂ : List α)
  proof: BAll.imp_left (fun _ => mem_of_mem_inter_left) h

中文:
定理 对任意_mem_inter_of_对任意_left
  条件: (h : 对任意 x in l₁, p x) (l₂ : 列表 α)
  证明: BAll.imp_left (fun _ => mem_of_mem_inter_left) h

Depends on / 依赖: BAll.imp_left, imp_left, mem_of_mem_inter_left
-/
theorem forall_mem_inter_of_forall_left (h : forall x in l₁, p x) (l₂ : List α) :
    forall x, x in l₁ inter l₂ -> p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_left) h

/--
theorem `forall_mem_inter_of_forall_right` / 定理 `forall_mem_inter_of_forall_right`

English:
theorem forall_mem_inter_of_forall_right
  given: (l₁ : List α) (h : forall x in l₂, p x)
  proof: BAll.imp_left (fun _ => mem_of_mem_inter_right) h

@[simp]

中文:
定理 对任意_mem_inter_of_对任意_right
  条件: (l₁ : 列表 α) (h : 对任意 x in l₂, p x)
  证明: BAll.imp_left (fun _ => mem_of_mem_inter_right) h

@[simp]

Depends on / 依赖: BAll.imp_left, imp_left, mem_of_mem_inter_right
-/
theorem forall_mem_inter_of_forall_right (l₁ : List α) (h : forall x in l₂, p x) :
    forall x, x in l₁ inter l₂ -> p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_right) h

@[simp]
/--
theorem `inter_reverse` / 定理 `inter_reverse`

English:
theorem inter_reverse
  given: {xs ys : List α}
  statement: xs inter ys.reverse = xs inter ys
  proof: by
  simp only [List.inter_def, elem_eq_mem, mem_reverse]

中文:
定理 inter_reverse
  条件: {xs ys : 列表 α}
  结论: xs inter ys.reverse = xs inter ys
  证明: by
  simp only [List.inter_def, elem_eq_mem, mem_reverse]

Depends on / 依赖: List.inter_def, elem_eq_mem, inter_def, mem_reverse
-/
theorem inter_reverse {xs ys : List α} : xs inter ys.reverse = xs inter ys := by
  simp only [List.inter_def, elem_eq_mem, mem_reverse]

/--
theorem `Subset.inter_eq_left` / 定理 `Subset.inter_eq_left`

English:
theorem Subset.inter_eq_left
  given: {xs ys : List α} (h : xs subseteq ys)
  statement: xs inter ys = xs
  proof: List.filter_eq_self.mpr fun _ ha => elem_eq_true_of_mem (h ha)

中文:
定理 子集.inter_eq_left
  条件: {xs ys : 列表 α} (h : xs subseteq ys)
  结论: xs inter ys = xs
  证明: List.filter_eq_self.mpr fun _ ha => elem_eq_true_of_mem (h ha)

Depends on / 依赖: List.filter_eq_self.mpr, elem_eq_true_of_mem, filter_eq_self
-/
theorem Subset.inter_eq_left {xs ys : List α} (h : xs subseteq ys) : xs inter ys = xs :=
  List.filter_eq_self.mpr fun _ ha => elem_eq_true_of_mem (h ha)

/--
theorem `Sublist.inter_left` / 定理 `Sublist.inter_left`

English:
theorem Sublist.inter_left
  given: {l₁ l₂ l₃ : List α} (h : l₂.Sublist l₃)
  proof: by
  grind [inter_def, monotone_filter_right]

中文:
定理 子表.inter_left
  条件: {l₁ l₂ l₃ : 列表 α} (h : l₂.子表 l₃)
  证明: by
  grind [inter_def, monotone_filter_right]

Depends on / 依赖: inter_def, monotone_filter_right
-/
theorem Sublist.inter_left {l₁ l₂ l₃ : List α} (h : l₂.Sublist l₃) :
    (l₁ inter l₂).Sublist (l₁ inter l₃) := by
  grind [inter_def, monotone_filter_right]

/--
theorem `Sublist.inter_right` / 定理 `Sublist.inter_right`

English:
theorem Sublist.inter_right
  given: {l₁ l₂ l₃ : List α} (h : l₁.Sublist l₂)
  proof: by
  grind [inter_def]

中文:
定理 子表.inter_right
  条件: {l₁ l₂ l₃ : 列表 α} (h : l₁.子表 l₂)
  证明: by
  grind [inter_def]

Depends on / 依赖: inter_def
-/
theorem Sublist.inter_right {l₁ l₂ l₃ : List α} (h : l₁.Sublist l₂) :
    (l₁ inter l₃).Sublist (l₂ inter l₃) := by
  grind [inter_def]

end Inter

/-! ### `bagInter` -/


section BagInter

@[simp, grind =]
/--
theorem `nil_bagInter` / 定理 `nil_bagInter`

English:
theorem nil_bagInter
  given: (l : List α)
  statement: [].bagInter l = []
  proof: by cases l <;> rfl

@[simp, grind =]

中文:
定理 nil_bag整数er
  条件: (l : 列表 α)
  结论: [].bag整数er l = []
  证明: by cases l <;> rfl

@[simp, grind =]
-/
theorem nil_bagInter (l : List α) : [].bagInter l = [] := by cases l <;> rfl

@[simp, grind =]
/--
theorem `bagInter_nil` / 定理 `bagInter_nil`

English:
theorem bagInter_nil
  given: (l : List α)
  statement: l.bagInter [] = []
  proof: by cases l <;> rfl

@[simp]

中文:
定理 bag整数er_nil
  条件: (l : 列表 α)
  结论: l.bag整数er [] = []
  证明: by cases l <;> rfl

@[simp]
-/
theorem bagInter_nil (l : List α) : l.bagInter [] = [] := by cases l <;> rfl

@[simp]
/--
theorem `cons_bagInter_of_mem` / 定理 `cons_bagInter_of_mem`

English:
theorem cons_bagInter_of_mem
  given: (l₁ : List α) (h : a in l₂)
  proof: by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_pos := cons_bagInter_of_mem

@[simp]

中文:
定理 cons_bag整数er_of_mem
  条件: (l₁ : 列表 α) (h : a in l₂)
  证明: by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_pos := cons_bagInter_of_mem

@[simp]

Depends on / 依赖: List.bagInter, bagInter
-/
theorem cons_bagInter_of_mem (l₁ : List α) (h : a in l₂) :
    (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_pos := cons_bagInter_of_mem

@[simp]
/--
theorem `cons_bagInter_of_not_mem` / 定理 `cons_bagInter_of_not_mem`

English:
theorem cons_bagInter_of_not_mem
  given: (l₁ : List α) (h : a ∉ l₂)
  proof: by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_neg := cons_bagInter_of_not_mem

@[grind =]

中文:
定理 cons_bag整数er_of_not_mem
  条件: (l₁ : 列表 α) (h : a ∉ l₂)
  证明: by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_neg := cons_bagInter_of_not_mem

@[grind =]

Depends on / 依赖: List.bagInter, bagInter
-/
theorem cons_bagInter_of_not_mem (l₁ : List α) (h : a ∉ l₂) :
    (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_neg := cons_bagInter_of_not_mem

@[grind =]
/--
theorem `cons_bagInter` / 定理 `cons_bagInter`

English:
theorem cons_bagInter
  proof: by
  split_ifs <;> simp_all

@[deprecated (since := "2026-05-13")]
alias cons_bagInteger := cons_bagInter

@[simp]

中文:
定理 cons_bag整数er
  证明: by
  split_ifs <;> simp_all

@[deprecated (since := "2026-05-13")]
alias cons_bagInteger := cons_bagInter

@[simp]

Depends on / 依赖: split_ifs
-/
theorem cons_bagInter :
    (a :: l₁).bagInter l₂ = if a in l₂ then a :: l₁.bagInter (l₂.erase a) else l₁.bagInter l₂ := by
  split_ifs <;> simp_all

@[deprecated (since := "2026-05-13")]
alias cons_bagInteger := cons_bagInter

@[simp]
/--
theorem `bagInter_cons_of_not_mem` / 定理 `bagInter_cons_of_not_mem`

English:
theorem bagInter_cons_of_not_mem
  given: (l₂ : List α) (h : a ∉ l₁)
  proof: by
  induction l₁ generalizing l₂ <;> grind

@[simp]

中文:
定理 bag整数er_cons_of_not_mem
  条件: (l₂ : 列表 α) (h : a ∉ l₁)
  证明: by
  induction l₁ generalizing l₂ <;> grind

@[simp]

Depends on / 依赖: generalizing
-/
theorem bagInter_cons_of_not_mem (l₂ : List α) (h : a ∉ l₁) :
    l₁.bagInter (a :: l₂) = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind

@[simp]
/--
theorem `mem_bagInter` / 定理 `mem_bagInter`

English:
theorem mem_bagInter
  given: {a : α} {l₁ l₂ : List α}
  statement: a in l₁.bagInter l₂ ↔ a in l₁ ∧ a in l₂
  proof: by
  fun_induction List.bagInter with grind

@[simp]

中文:
定理 mem_bag整数er
  条件: {a : α} {l₁ l₂ : 列表 α}
  结论: a in l₁.bag整数er l₂ ↔ a in l₁ ∧ a in l₂
  证明: by
  fun_induction List.bagInter with grind

@[simp]

Depends on / 依赖: List.bagInter, bagInter, fun_induction
-/
theorem mem_bagInter {a : α} {l₁ l₂ : List α} : a in l₁.bagInter l₂ ↔ a in l₁ ∧ a in l₂ := by
  fun_induction List.bagInter with grind

@[simp]
/--
theorem `count_bagInter` / 定理 `count_bagInter`

English:
theorem count_bagInter
  given: {a : α} {l₁ l₂ : List α}
  proof: by
  fun_induction List.bagInter with grind

中文:
定理 count_bag整数er
  条件: {a : α} {l₁ l₂ : 列表 α}
  证明: by
  fun_induction List.bagInter with grind

Depends on / 依赖: List.bagInter, bagInter, fun_induction
-/
theorem count_bagInter {a : α} {l₁ l₂ : List α} :
    count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂) := by
  fun_induction List.bagInter with grind

/--
theorem `bagInter_sublist_left` / 定理 `bagInter_sublist_left`

English:
theorem bagInter_sublist_left
  given: {l₁ l₂ : List α}
  statement: l₁.bagInter l₂ <+ l₁
  proof: by
  fun_induction List.bagInter with grind

中文:
定理 bag整数er_sublist_left
  条件: {l₁ l₂ : 列表 α}
  结论: l₁.bag整数er l₂ <+ l₁
  证明: by
  fun_induction List.bagInter with grind

Depends on / 依赖: List.bagInter, bagInter, fun_induction
-/
theorem bagInter_sublist_left {l₁ l₂ : List α} : l₁.bagInter l₂ <+ l₁ := by
  fun_induction List.bagInter with grind

/--
theorem `singleton_bagInter` / 定理 `singleton_bagInter`

English:
theorem singleton_bagInter
  given: (a : α)
  statement: [a].bagInter l₁ = if a in l₁ then [a] else []
  proof: by
  grind

中文:
定理 singleton_bag整数er
  条件: (a : α)
  结论: [a].bag整数er l₁ = if a in l₁ then [a] else []
  证明: by
  grind
-/
theorem singleton_bagInter (a : α) : [a].bagInter l₁ = if a in l₁ then [a] else [] := by
  grind

/--
theorem `bagInter_singleton` / 定理 `bagInter_singleton`

English:
theorem bagInter_singleton
  given: (a : α)
  statement: l₁.bagInter [a] = if a in l₁ then [a] else []
  proof: by
  induction l₁ <;> grind

@[simp]

中文:
定理 bag整数er_singleton
  条件: (a : α)
  结论: l₁.bag整数er [a] = if a in l₁ then [a] else []
  证明: by
  induction l₁ <;> grind

@[simp]
-/
theorem bagInter_singleton (a : α) : l₁.bagInter [a] = if a in l₁ then [a] else [] := by
  induction l₁ <;> grind

@[simp]
/--
theorem `bagInter_erase_of_not_mem` / 定理 `bagInter_erase_of_not_mem`

English:
theorem bagInter_erase_of_not_mem
  given: (h : a ∉ l₁)
  proof: by
  induction l₁ generalizing l₂ <;> grind

@[simp]

中文:
定理 bag整数er_erase_of_not_mem
  条件: (h : a ∉ l₁)
  证明: by
  induction l₁ generalizing l₂ <;> grind

@[simp]

Depends on / 依赖: generalizing
-/
theorem bagInter_erase_of_not_mem (h : a ∉ l₁) :
    l₁.bagInter (l₂.erase a) = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind

@[simp]
/--
theorem `erase_bagInter_of_not_mem` / 定理 `erase_bagInter_of_not_mem`

English:
theorem erase_bagInter_of_not_mem
  given: (h : a ∉ l₂)
  proof: by
  induction l₁ generalizing l₂ <;> grind

中文:
定理 erase_bag整数er_of_not_mem
  条件: (h : a ∉ l₂)
  证明: by
  induction l₁ generalizing l₂ <;> grind

Depends on / 依赖: generalizing
-/
theorem erase_bagInter_of_not_mem (h : a ∉ l₂) :
    (l₁.erase a).bagInter l₂ = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind

/--
theorem `bagInter_nil_iff_inter_nil` / 定理 `bagInter_nil_iff_inter_nil`

English:
theorem bagInter_nil_iff_inter_nil
  statement: forall l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ inter l₂ = []

中文:
定理 bag整数er_nil_iff_inter_nil
  结论: 对任意 l₁ l₂ : 列表 α, l₁.bag整数er l₂ = [] ↔ l₁ inter l₂ = []
-/
theorem bagInter_nil_iff_inter_nil : forall l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ inter l₂ = []
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    by_cases h : b in l₂
    · simp [h]
    · simpa [h] using bagInter_nil_iff_inter_nil l₁ l₂

@[simp]
/--
theorem `bagInter_eq_nil_iff_disjoint` / 定理 `bagInter_eq_nil_iff_disjoint`

English:
theorem bagInter_eq_nil_iff_disjoint
  statement: l₁.bagInter l₂ = [] ↔ l₁.Disjoint l₂
  proof: (bagInter_nil_iff_inter_nil _ _).trans inter_eq_nil_iff_disjoint

中文:
定理 bag整数er_eq_nil_iff_disjoint
  结论: l₁.bag整数er l₂ = [] ↔ l₁.Disjoint l₂
  证明: (bagInter_nil_iff_inter_nil _ _).trans inter_eq_nil_iff_disjoint

Depends on / 依赖: bagInter_nil_iff_inter_nil, inter_eq_nil_iff_disjoint
-/
theorem bagInter_eq_nil_iff_disjoint : l₁.bagInter l₂ = [] ↔ l₁.Disjoint l₂ :=
  (bagInter_nil_iff_inter_nil _ _).trans inter_eq_nil_iff_disjoint

/--
theorem `Nodup.bagInter_right` / 定理 `Nodup.bagInter_right`

English:
theorem Nodup.bagInter_right
  given: (h : l₁.Nodup)
  statement: (l₁.bagInter l₂).Nodup
  proof: nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

中文:
定理 Nodup.bag整数er_right
  条件: (h : l₁.Nodup)
  结论: (l₁.bag整数er l₂).Nodup
  证明: nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

Depends on / 依赖: List.count_bagInter, count_bagInter, nodup_iff_count, nodup_iff_count.mpr
-/
theorem Nodup.bagInter_right (h : l₁.Nodup) : (l₁.bagInter l₂).Nodup :=
  nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

/--
theorem `Nodup.bagInter_left` / 定理 `Nodup.bagInter_left`

English:
theorem Nodup.bagInter_left
  given: (h : l₂.Nodup)
  statement: (l₁.bagInter l₂).Nodup
  proof: nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

中文:
定理 Nodup.bag整数er_left
  条件: (h : l₂.Nodup)
  结论: (l₁.bag整数er l₂).Nodup
  证明: nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

Depends on / 依赖: List.count_bagInter, count_bagInter, nodup_iff_count, nodup_iff_count.mpr
-/
theorem Nodup.bagInter_left (h : l₂.Nodup) : (l₁.bagInter l₂).Nodup :=
  nodup_iff_count.mpr fun x => (by grind [List.count_bagInter])

/--
theorem `Sublist.bagInter_inter` / 定理 `Sublist.bagInter_inter`

English:
theorem Sublist.bagInter_inter
  statement: (l₁.bagInter l₂).Sublist (l₁ inter l₂)
  proof: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih =>
    rw [cons_bagInter]
    split
    · rw [inter_cons_of_mem _ (by assumption), cons_sublist_cons]
exact ih.trans Sublist.inter_left (by grind [erase_sublist])
    · simp_all

中文:
定理 子表.bag整数er_inter
  结论: (l₁.bag整数er l₂).子表 (l₁ inter l₂)
  证明: by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih =>
    rw [cons_bagInter]
    split
    · rw [inter_cons_of_mem _ (by assumption), cons_sublist_cons]
exact ih.trans Sublist.inter_left (by grind [erase_sublist])
    · simp_all

Depends on / 依赖: Sublist, Sublist.inter_left, cons_bagInter, cons_sublist_cons, erase_sublist, generalizing, ih.trans, inter_cons_of_mem, inter_left
-/
theorem Sublist.bagInter_inter : (l₁.bagInter l₂).Sublist (l₁ inter l₂) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih =>
    rw [cons_bagInter]
    split
    · rw [inter_cons_of_mem _ (by assumption), cons_sublist_cons]
exact ih.trans Sublist.inter_left (by grind [erase_sublist])
    · simp_all

end BagInter

end List
