/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.SymmDiff

/-! # Symmetric differences of sets -/

public section

assert_not_exists RelIso

namespace Set

universe u
variable {α : Type u} {a : α} {s t u v : Set α}

open scoped symmDiff

/--
theorem `mem_symmDiff` / 定理 `mem_symmDiff`

English:
theorem mem_symmDiff
  statement: a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s
  proof: .rfl

中文:
定理 mem_symmDiff
  结论: a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s
  证明: .rfl
-/
@[grind =] theorem mem_symmDiff : a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s := .rfl

/--
theorem `symmDiff_def` / 定理 `symmDiff_def`

English:
theorem symmDiff_def
  given: (s t : Set α)
  statement: s ∆ t = s \ t union t \ s
  proof: rfl

中文:
定理 symmDiff_def
  条件: (s t : Set α)
  结论: s ∆ t = s \ t union t \ s
  证明: rfl
-/
protected theorem symmDiff_def (s t : Set α) : s ∆ t = s \ t union t \ s := rfl

/--
theorem `mem_bihimp_iff` / 定理 `mem_bihimp_iff`

English:
theorem mem_bihimp_iff
  statement: a in s ⇔ t ↔ (a in s ↔ a in t)
  proof: by simp [bihimp, iff_def']

中文:
定理 mem_bihimp_iff
  结论: a in s ⇔ t ↔ (a in s ↔ a in t)
  证明: by simp [bihimp, iff_def']
-/
@[simp] theorem mem_bihimp_iff : a in s ⇔ t ↔ (a in s ↔ a in t) := by simp [bihimp, iff_def']

/--
theorem `bihimp_def` / 定理 `bihimp_def`

English:
theorem bihimp_def
  statement: s ⇔ t = (s union tᶜ) inter (t union sᶜ)
  proof: bihimp_eq ..

中文:
定理 bihimp_def
  结论: s ⇔ t = (s union tᶜ) inter (t union sᶜ)
  证明: bihimp_eq ..
-/
protected theorem bihimp_def : s ⇔ t = (s union tᶜ) inter (t union sᶜ) := bihimp_eq ..

/--
theorem `symmDiff_subset_union` / 定理 `symmDiff_subset_union`

English:
theorem symmDiff_subset_union
  statement: s ∆ t subseteq s union t
  proof: @symmDiff_le_sup (Set α) _ _ _

@[simp]

中文:
定理 symmDiff_subset_union
  结论: s ∆ t subseteq s union t
  证明: @symmDiff_le_sup (Set α) _ _ _

@[simp]

Depends on / 依赖: symmDiff_le_sup
-/
theorem symmDiff_subset_union : s ∆ t subseteq s union t :=
  @symmDiff_le_sup (Set α) _ _ _

@[simp]
/--
theorem `symmDiff_eq_empty` / 定理 `symmDiff_eq_empty`

English:
theorem symmDiff_eq_empty
  statement: s ∆ t = ∅ ↔ s = t
  proof: symmDiff_eq_bot

@[simp]

中文:
定理 symmDiff_eq_empty
  结论: s ∆ t = ∅ ↔ s = t
  证明: symmDiff_eq_bot

@[simp]

Depends on / 依赖: symmDiff_eq_bot
-/
theorem symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t :=
  symmDiff_eq_bot

@[simp]
/--
theorem `symmDiff_nonempty` / 定理 `symmDiff_nonempty`

English:
theorem symmDiff_nonempty
  statement: (s ∆ t).Nonempty ↔ s != t
  proof: nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

中文:
定理 symmDiff_nonempty
  结论: (s ∆ t).Nonempty ↔ s != t
  证明: nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

Depends on / 依赖: nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans, symmDiff_eq_empty, symmDiff_eq_empty.not
-/
theorem symmDiff_nonempty : (s ∆ t).Nonempty ↔ s != t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

/--
theorem `inter_symmDiff_distrib_left` / 定理 `inter_symmDiff_distrib_left`

English:
theorem inter_symmDiff_distrib_left
  given: (s t u : Set α)
  statement: s inter t ∆ u = (s inter t) ∆ (s inter u)
  proof: inf_symmDiff_distrib_left _ _ _

中文:
定理 inter_symmDiff_distrib_left
  条件: (s t u : Set α)
  结论: s inter t ∆ u = (s inter t) ∆ (s inter u)
  证明: inf_symmDiff_distrib_left _ _ _

Depends on / 依赖: inf_symmDiff_distrib_left
-/
theorem inter_symmDiff_distrib_left (s t u : Set α) : s inter t ∆ u = (s inter t) ∆ (s inter u) :=
  inf_symmDiff_distrib_left _ _ _

/--
theorem `inter_symmDiff_distrib_right` / 定理 `inter_symmDiff_distrib_right`

English:
theorem inter_symmDiff_distrib_right
  given: (s t u : Set α)
  statement: s ∆ t inter u = (s inter u) ∆ (t inter u)
  proof: inf_symmDiff_distrib_right _ _ _

中文:
定理 inter_symmDiff_distrib_right
  条件: (s t u : Set α)
  结论: s ∆ t inter u = (s inter u) ∆ (t inter u)
  证明: inf_symmDiff_distrib_right _ _ _

Depends on / 依赖: inf_symmDiff_distrib_right
-/
theorem inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t inter u = (s inter u) ∆ (t inter u) :=
  inf_symmDiff_distrib_right _ _ _

/--
theorem `subset_symmDiff_union_symmDiff_left` / 定理 `subset_symmDiff_union_symmDiff_left`

English:
theorem subset_symmDiff_union_symmDiff_left
  given: (h : Disjoint s t)
  statement: u subseteq s ∆ u union t ∆ u
  proof: h.le_symmDiff_sup_symmDiff_left

中文:
定理 subset_symmDiff_union_symmDiff_left
  条件: (h : Disjoint s t)
  结论: u subseteq s ∆ u union t ∆ u
  证明: h.le_symmDiff_sup_symmDiff_left

Depends on / 依赖: h.le_symmDiff_sup_symmDiff_left, le_symmDiff_sup_symmDiff_left
-/
theorem subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u subseteq s ∆ u union t ∆ u :=
  h.le_symmDiff_sup_symmDiff_left

/--
theorem `subset_symmDiff_union_symmDiff_right` / 定理 `subset_symmDiff_union_symmDiff_right`

English:
theorem subset_symmDiff_union_symmDiff_right
  given: (h : Disjoint t u)
  statement: s subseteq s ∆ t union s ∆ u
  proof: h.le_symmDiff_sup_symmDiff_right

中文:
定理 subset_symmDiff_union_symmDiff_right
  条件: (h : Disjoint t u)
  结论: s subseteq s ∆ t union s ∆ u
  证明: h.le_symmDiff_sup_symmDiff_right

Depends on / 依赖: h.le_symmDiff_sup_symmDiff_right, le_symmDiff_sup_symmDiff_right
-/
theorem subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s subseteq s ∆ t union s ∆ u :=
  h.le_symmDiff_sup_symmDiff_right

/--
lemma `union_symmDiff_subset` / 引理 `union_symmDiff_subset`

English:
lemma union_symmDiff_subset
  statement: (s union t) ∆ u subseteq s ∆ u union t ∆ u
  proof: by
  grind

中文:
引理 union_symmDiff_subset
  结论: (s union t) ∆ u subseteq s ∆ u union t ∆ u
  证明: by
  grind
-/
lemma union_symmDiff_subset : (s union t) ∆ u subseteq s ∆ u union t ∆ u := by
  grind

/--
lemma `symmDiff_union_subset` / 引理 `symmDiff_union_subset`

English:
lemma symmDiff_union_subset
  statement: s ∆ (t union u) subseteq s ∆ t union s ∆ u
  proof: by
  grind

中文:
引理 symmDiff_union_subset
  结论: s ∆ (t union u) subseteq s ∆ t union s ∆ u
  证明: by
  grind
-/
lemma symmDiff_union_subset : s ∆ (t union u) subseteq s ∆ t union s ∆ u := by
  grind

/--
lemma `union_symmDiff_union_subset` / 引理 `union_symmDiff_union_subset`

English:
lemma union_symmDiff_union_subset
  statement: (s union t) ∆ (u union v) subseteq s ∆ u union t ∆ v
  proof: by
  grind

中文:
引理 union_symmDiff_union_subset
  结论: (s union t) ∆ (u union v) subseteq s ∆ u union t ∆ v
  证明: by
  grind
-/
lemma union_symmDiff_union_subset : (s union t) ∆ (u union v) subseteq s ∆ u union t ∆ v := by
  grind

end Set
