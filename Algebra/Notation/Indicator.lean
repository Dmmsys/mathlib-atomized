/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Piecewise

/-!
# Indicator function

This file defines the indicator function of a set. More lemmas can be found in
`Mathlib/Algebra/Group/Indicator.lean`.

## Main declarations

- `Set.indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `Set.mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `fun _ ↦ 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.single` or `Set.piecewise`.

## Tags

indicator, characteristic
-/

@[expose] public section

assert_not_exists Monoid

open Function

variable {α β M N : Type*}

namespace Set
variable [One M] [One N] {s t : Set α} {f g : α -> M} {a : α}

/-- `Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise. -/
@[to_additive /-- `Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise. -/]
/--
Definition of `mulIndicator` / `mulIndicator` 的定义

English:
definition mulIndicator
  signature: (s : Set α) (f : α -> M) (x : α)
  body: haveI := Classical.decPred (· in s)
  if x in s then f x else 1

@[to_additive (attr := simp)]

中文:
定义 mulIndicator
  签名: (s : Set α) (f : α -> M) (x : α)
  定义体: haveI := Classical.decPred (· in s)
  if x in s then f x else 1

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.decPred, decPred
-/
noncomputable def mulIndicator (s : Set α) (f : α -> M) (x : α) : M :=
  haveI := Classical.decPred (· in s)
  if x in s then f x else 1

@[to_additive (attr := simp)]
/--
lemma `piecewise_eq_mulIndicator` / 引理 `piecewise_eq_mulIndicator`

English:
lemma piecewise_eq_mulIndicator
  given: [DecidablePred (· in s)]
  statement: s.piecewise f 1 = s.mulIndicator f
  proof: funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]

中文:
引理 piecewise_eq_mulIndicator
  条件: [DecidablePred (· in s)]
  结论: s.piecewise f 1 = s.mulIndicator f
  证明: funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]

Depends on / 依赖: Iff.rfl, if_congr
-/
lemma piecewise_eq_mulIndicator [DecidablePred (· in s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]
/--
lemma `mulIndicator_apply` / 引理 `mulIndicator_apply`

English:
lemma mulIndicator_apply
  given: (s : Set α) (f : α -> M) (a : α) [Decidable (a in s)]
  proof: by
  unfold mulIndicator
  congr

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_apply
  条件: (s : Set α) (f : α -> M) (a : α) [Decidable (a in s)]
  证明: by
  unfold mulIndicator
  congr

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator
-/
lemma mulIndicator_apply (s : Set α) (f : α -> M) (a : α) [Decidable (a in s)] :
    mulIndicator s f a = if a in s then f a else 1 := by
  unfold mulIndicator
  congr

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_of_mem` / 引理 `mulIndicator_of_mem`

English:
lemma mulIndicator_of_mem
  given: (h : a in s) (f : α -> M)
  statement: mulIndicator s f a = f a
  proof: if_pos h

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_of_mem
  条件: (h : a in s) (f : α -> M)
  结论: mulIndicator s f a = f a
  证明: if_pos h

@[to_additive (attr := simp)]

Depends on / 依赖: if_pos
-/
lemma mulIndicator_of_mem (h : a in s) (f : α -> M) : mulIndicator s f a = f a := if_pos h

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_of_notMem` / 引理 `mulIndicator_of_notMem`

English:
lemma mulIndicator_of_notMem
  given: (h : a ∉ s) (f : α -> M)
  statement: mulIndicator s f a = 1
  proof: if_neg h

@[to_additive]

中文:
引理 mulIndicator_of_notMem
  条件: (h : a ∉ s) (f : α -> M)
  结论: mulIndicator s f a = 1
  证明: if_neg h

@[to_additive]

Depends on / 依赖: if_neg
-/
lemma mulIndicator_of_notMem (h : a ∉ s) (f : α -> M) : mulIndicator s f a = 1 := if_neg h

@[to_additive]
/--
lemma `mulIndicator_eq_one_or_self` / 引理 `mulIndicator_eq_one_or_self`

English:
lemma mulIndicator_eq_one_or_self
  given: (s : Set α) (f : α -> M) (a : α)
  proof: by
  by_cases h : a in s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_notMem h f)

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_eq_one_or_self
  条件: (s : Set α) (f : α -> M) (a : α)
  证明: by
  by_cases h : a in s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_notMem h f)

@[to_additive (attr := simp)]

Depends on / 依赖: Or.inl, Or.inr, mulIndicator_of_mem, mulIndicator_of_notMem
-/
lemma mulIndicator_eq_one_or_self (s : Set α) (f : α -> M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases h : a in s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_notMem h f)

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_apply_eq_self` / 引理 `mulIndicator_apply_eq_self`

English:
lemma mulIndicator_apply_eq_self
  statement: s.mulIndicator f a = f a ↔ a ∉ s -> f a = 1
  proof: letI := Classical.dec (a in s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_apply_eq_self
  结论: s.mulIndicator f a = f a ↔ a ∉ s -> f a = 1
  证明: letI := Classical.dec (a in s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.dec, eq_comm, ite_eq_left_iff, ite_eq_left_iff.trans
-/
lemma mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s -> f a = 1 :=
  letI := Classical.dec (a in s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_eq_self` / 引理 `mulIndicator_eq_self`

English:
lemma mulIndicator_eq_self
  statement: s.mulIndicator f = f ↔ mulSupport f subseteq s
  proof: by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]

中文:
引理 mulIndicator_eq_self
  结论: s.mulIndicator f = f ↔ mulSupport f subseteq s
  证明: by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]

Depends on / 依赖: funext_iff, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm, subset_def
-/
lemma mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f subseteq s := by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]
/--
lemma `mulIndicator_eq_self_of_superset` / 引理 `mulIndicator_eq_self_of_superset`

English:
lemma mulIndicator_eq_self_of_superset
  given: (h1 : s.mulIndicator f = f) (h2 : s subseteq t)
  proof: by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_eq_self_of_superset
  条件: (h1 : s.mulIndicator f = f) (h2 : s subseteq t)
  证明: by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := simp)]

Depends on / 依赖: Subset, Subset.trans, mulIndicator_eq_self
-/
lemma mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s subseteq t) :
    t.mulIndicator f = f := by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_apply_eq_one` / 引理 `mulIndicator_apply_eq_one`

English:
lemma mulIndicator_apply_eq_one
  statement: mulIndicator s f a = 1 ↔ a in s -> f a = 1
  proof: letI := Classical.dec (a in s)
  ite_eq_right_iff

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_apply_eq_one
  结论: mulIndicator s f a = 1 ↔ a in s -> f a = 1
  证明: letI := Classical.dec (a in s)
  ite_eq_right_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.dec, ite_eq_right_iff
-/
lemma mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a in s -> f a = 1 :=
  letI := Classical.dec (a in s)
  ite_eq_right_iff

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_eq_one` / 引理 `mulIndicator_eq_one`

English:
lemma mulIndicator_eq_one
  statement: (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s
  proof: by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_eq_one
  结论: (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s
  证明: by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.disjoint_left, disjoint_left, funext_iff, mem_mulSupport, mulIndicator_apply_eq_one, not_imp_not
-/
lemma mulIndicator_eq_one : (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_eq_one'` / 引理 `mulIndicator_eq_one'`

English:
lemma mulIndicator_eq_one'
  statement: mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s
  proof: mulIndicator_eq_one

@[to_additive]

中文:
引理 mulIndicator_eq_one'
  结论: mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s
  证明: mulIndicator_eq_one

@[to_additive]

Depends on / 依赖: mulIndicator_eq_one
-/
lemma mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one

@[to_additive]
/--
lemma `mulIndicator_apply_ne_one` / 引理 `mulIndicator_apply_ne_one`

English:
lemma mulIndicator_apply_ne_one
  given: {a : α}
  statement: s.mulIndicator f a != 1 ↔ a in s inter mulSupport f
  proof: by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_apply_ne_one
  条件: {a : α}
  结论: s.mulIndicator f a != 1 ↔ a in s inter mulSupport f
  证明: by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.not_imp, mem_inter_iff, mem_mulSupport, mulIndicator_apply_eq_one, not_imp
-/
lemma mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a != 1 ↔ a in s inter mulSupport f := by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]
/--
lemma `mulSupport_mulIndicator` / 引理 `mulSupport_mulIndicator`

English:
lemma mulSupport_mulIndicator
  proof: ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

中文:
引理 mulSupport_mulIndicator
  证明: ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

Depends on / 依赖: Function, Function.mem_mulSupport, mem_mulSupport, mulIndicator_apply_eq_one
-/
lemma mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s inter Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive
/-- If an additive indicator function is not equal to `0` at a point, then that point is in the set.
-/]
/--
lemma `mem_of_mulIndicator_ne_one` / 引理 `mem_of_mulIndicator_ne_one`

English:
lemma mem_of_mulIndicator_ne_one
  given: (h : mulIndicator s f a != 1)
  statement: a in s
  proof: not_imp_comm.1 (fun hn => mulIndicator_of_notMem hn f) h

中文:
引理 mem_of_mulIndicator_ne_one
  条件: (h : mulIndicator s f a != 1)
  结论: a in s
  证明: not_imp_comm.1 (fun hn => mulIndicator_of_notMem hn f) h

Depends on / 依赖: mulIndicator_of_notMem, not_imp_comm
-/
lemma mem_of_mulIndicator_ne_one (h : mulIndicator s f a != 1) : a in s :=
  not_imp_comm.1 (fun hn => mulIndicator_of_notMem hn f) h

/-- See `Set.eqOn_mulIndicator'` for the version with `sᶜ`. -/
@[to_additive /-- See `Set.eqOn_indicator'` for the version with `sᶜ`. -/]
/--
lemma `eqOn_mulIndicator` / 引理 `eqOn_mulIndicator`

English:
lemma eqOn_mulIndicator
  statement: EqOn (mulIndicator s f) f s
  proof: fun _ hx => mulIndicator_of_mem hx f

中文:
引理 eqOn_mulIndicator
  结论: EqOn (mulIndicator s f) f s
  证明: fun _ hx => mulIndicator_of_mem hx f

Depends on / 依赖: mulIndicator_of_mem
-/
lemma eqOn_mulIndicator : EqOn (mulIndicator s f) f s := fun _ hx => mulIndicator_of_mem hx f

/-- See `Set.eqOn_mulIndicator` for the version with `s`. -/
@[to_additive /-- See `Set.eqOn_indicator` for the version with `s`. -/]
/--
lemma `eqOn_mulIndicator'` / 引理 `eqOn_mulIndicator'`

English:
lemma eqOn_mulIndicator'
  statement: EqOn (mulIndicator s f) 1 sᶜ
  proof: fun _ hx => mulIndicator_of_notMem hx f

@[to_additive]

中文:
引理 eqOn_mulIndicator'
  结论: EqOn (mulIndicator s f) 1 sᶜ
  证明: fun _ hx => mulIndicator_of_notMem hx f

@[to_additive]

Depends on / 依赖: mulIndicator_of_notMem
-/
lemma eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 sᶜ :=
  fun _ hx => mulIndicator_of_notMem hx f

@[to_additive]
/--
lemma `mulSupport_mulIndicator_subset` / 引理 `mulSupport_mulIndicator_subset`

English:
lemma mulSupport_mulIndicator_subset
  statement: mulSupport (s.mulIndicator f) subseteq s
  proof: fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_notMem h f

@[to_additive (attr := simp)]

中文:
引理 mulSupport_mulIndicator_subset
  结论: mulSupport (s.mulIndicator f) subseteq s
  证明: fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_notMem h f

@[to_additive (attr := simp)]
-/
lemma mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) subseteq s := fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_notMem h f

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_mulSupport` / 引理 `mulIndicator_mulSupport`

English:
lemma mulIndicator_mulSupport
  statement: mulIndicator (mulSupport f) f = f
  proof: mulIndicator_eq_self.2 Subset.rfl

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_mulSupport
  结论: mulIndicator (mulSupport f) f = f
  证明: mulIndicator_eq_self.2 Subset.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Subset, Subset.rfl, mulIndicator_eq_self
-/
lemma mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f :=
  mulIndicator_eq_self.2 Subset.rfl

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_range_comp` / 引理 `mulIndicator_range_comp`

English:
lemma mulIndicator_range_comp
  given: {ι : Sort*} (f : ι -> α) (g : α -> M)
  proof: letI := Classical.decPred (· in range f)
  piecewise_range_comp _ _ _

@[to_additive]

中文:
引理 mulIndicator_range_comp
  条件: {ι : Sort*} (f : ι -> α) (g : α -> M)
  证明: letI := Classical.decPred (· in range f)
  piecewise_range_comp _ _ _

@[to_additive]

Depends on / 依赖: Classical, Classical.decPred, decPred, piecewise_range_comp
-/
lemma mulIndicator_range_comp {ι : Sort*} (f : ι -> α) (g : α -> M) :
    mulIndicator (range f) g ∘ f = g ∘ f :=
  letI := Classical.decPred (· in range f)
  piecewise_range_comp _ _ _

@[to_additive]
/--
lemma `mulIndicator_congr` / 引理 `mulIndicator_congr`

English:
lemma mulIndicator_congr
  given: (h : EqOn f g s)
  statement: mulIndicator s f = mulIndicator s g
  proof: funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

@[to_additive]

中文:
引理 mulIndicator_congr
  条件: (h : EqOn f g s)
  结论: mulIndicator s f = mulIndicator s g
  证明: funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

@[to_additive]

Depends on / 依赖: mulIndicator, split_ifs
-/
lemma mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

@[to_additive]
/--
lemma `mulIndicator_eq_mulIndicator` / 引理 `mulIndicator_eq_mulIndicator`

English:
lemma mulIndicator_eq_mulIndicator
  statement: {t : Set β} {g : β -> M} {b : β}
  proof: by
  by_cases a in s <;> simp_all

@[to_additive]

中文:
引理 mulIndicator_eq_mulIndicator
  结论: {t : Set β} {g : β -> M} {b : β}
  证明: by
  by_cases a in s <;> simp_all

@[to_additive]
-/
lemma mulIndicator_eq_mulIndicator {t : Set β} {g : β -> M} {b : β}
    (h1 : a in s ↔ b in t) (h2 : f a = g b) :
    s.mulIndicator f a = t.mulIndicator g b := by
  by_cases a in s <;> simp_all

@[to_additive]
/--
lemma `mulIndicator_const_eq_mulIndicator_const` / 引理 `mulIndicator_const_eq_mulIndicator_const`

English:
lemma mulIndicator_const_eq_mulIndicator_const
  given: {t : Set β} {b : β} {c : M} (h : a in s ↔ b in t)
  proof: mulIndicator_eq_mulIndicator h rfl

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_const_eq_mulIndicator_const
  条件: {t : Set β} {b : β} {c : M} (h : a in s ↔ b in t)
  证明: mulIndicator_eq_mulIndicator h rfl

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator_eq_mulIndicator
-/
lemma mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : a in s ↔ b in t) :
    s.mulIndicator (fun _ => c) a = t.mulIndicator (fun _ => c) b :=
  mulIndicator_eq_mulIndicator h rfl

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_univ` / 引理 `mulIndicator_univ`

English:
lemma mulIndicator_univ
  given: (f : α -> M)
  statement: mulIndicator (univ : Set α) f = f
  proof: mulIndicator_eq_self.2 subset_univ _

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_univ
  条件: (f : α -> M)
  结论: mulIndicator (univ : Set α) f = f
  证明: mulIndicator_eq_self.2 subset_univ _

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator_eq_self, subset_univ
-/
lemma mulIndicator_univ (f : α -> M) : mulIndicator (univ : Set α) f = f :=
mulIndicator_eq_self.2 subset_univ _

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_empty` / 引理 `mulIndicator_empty`

English:
lemma mulIndicator_empty
  given: (f : α -> M)
  statement: mulIndicator (∅ : Set α) f = fun _ => 1
  proof: mulIndicator_eq_one.2 disjoint_empty _

@[to_additive]

中文:
引理 mulIndicator_empty
  条件: (f : α -> M)
  结论: mulIndicator (∅ : Set α) f = fun _ => 1
  证明: mulIndicator_eq_one.2 disjoint_empty _

@[to_additive]

Depends on / 依赖: disjoint_empty, mulIndicator_eq_one
-/
lemma mulIndicator_empty (f : α -> M) : mulIndicator (∅ : Set α) f = fun _ => 1 :=
mulIndicator_eq_one.2 disjoint_empty _

@[to_additive]
/--
lemma `mulIndicator_empty'` / 引理 `mulIndicator_empty'`

English:
lemma mulIndicator_empty'
  given: (f : α -> M)
  statement: mulIndicator (∅ : Set α) f = 1
  proof: mulIndicator_empty f

中文:
引理 mulIndicator_empty'
  条件: (f : α -> M)
  结论: mulIndicator (∅ : Set α) f = 1
  证明: mulIndicator_empty f

Depends on / 依赖: mulIndicator_empty
-/
lemma mulIndicator_empty' (f : α -> M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f

variable (M)

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_one` / 引理 `mulIndicator_one`

English:
lemma mulIndicator_one
  given: (s : Set α)
  statement: (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M)
  proof: mulIndicator_eq_one.2 by simp only [mulSupport_fun_one, empty_disjoint]

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_one
  条件: (s : Set α)
  结论: (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M)
  证明: mulIndicator_eq_one.2 by simp only [mulSupport_fun_one, empty_disjoint]

@[to_additive (attr := simp)]

Depends on / 依赖: empty_disjoint, mulIndicator_eq_one, mulSupport_fun_one
-/
lemma mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) :=
mulIndicator_eq_one.2 by simp only [mulSupport_fun_one, empty_disjoint]

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_one'` / 引理 `mulIndicator_one'`

English:
lemma mulIndicator_one'
  given: {s : Set α}
  statement: s.mulIndicator (1 : α -> M) = 1
  proof: mulIndicator_one M s

中文:
引理 mulIndicator_one'
  条件: {s : Set α}
  结论: s.mulIndicator (1 : α -> M) = 1
  证明: mulIndicator_one M s

Depends on / 依赖: mulIndicator_one
-/
lemma mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α -> M) = 1 :=
  mulIndicator_one M s

variable {M}

@[to_additive]
/--
lemma `mulIndicator_mulIndicator` / 引理 `mulIndicator_mulIndicator`

English:
lemma mulIndicator_mulIndicator
  given: (s t : Set α) (f : α -> M)
  proof: funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]

中文:
引理 mulIndicator_mulIndicator
  条件: (s t : Set α) (f : α -> M)
  证明: funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]

Depends on / 依赖: contextual, mulIndicator, split_ifs
-/
lemma mulIndicator_mulIndicator (s t : Set α) (f : α -> M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s inter t) f :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]
/--
lemma `mulIndicator_inter_mulSupport` / 引理 `mulIndicator_inter_mulSupport`

English:
lemma mulIndicator_inter_mulSupport
  given: (s : Set α) (f : α -> M)
  proof: by
  rw [← mulIndicator_mulIndicator]; rw [mulIndicator_mulSupport]

@[to_additive]

中文:
引理 mulIndicator_inter_mulSupport
  条件: (s : Set α) (f : α -> M)
  证明: by
  rw [← mulIndicator_mulIndicator]; rw [mulIndicator_mulSupport]

@[to_additive]

Depends on / 依赖: mulIndicator_mulIndicator, mulIndicator_mulSupport
-/
lemma mulIndicator_inter_mulSupport (s : Set α) (f : α -> M) :
    mulIndicator (s inter mulSupport f) f = mulIndicator s f := by
  rw [← mulIndicator_mulIndicator]; rw [mulIndicator_mulSupport]

@[to_additive]
/--
lemma `comp_mulIndicator` / 引理 `comp_mulIndicator`

English:
lemma comp_mulIndicator
  given: (h : M -> β) (f : α -> M) {s : Set α} {x : α} [DecidablePred (· in s)]
  proof: by
  let := Classical.decPred (· in s)
  convert! s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

@[to_additive]

中文:
引理 comp_mulIndicator
  条件: (h : M -> β) (f : α -> M) {s : Set α} {x : α} [DecidablePred (· in s)]
  证明: by
  let := Classical.decPred (· in s)
  convert! s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

@[to_additive]

Depends on / 依赖: Classical, Classical.decPred, apply_piecewise, convert, decPred, s.apply_piecewise
-/
lemma comp_mulIndicator (h : M -> β) (f : α -> M) {s : Set α} {x : α} [DecidablePred (· in s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  let := Classical.decPred (· in s)
  convert! s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

@[to_additive]
/--
lemma `mulIndicator_comp_right` / 引理 `mulIndicator_comp_right`

English:
lemma mulIndicator_comp_right
  given: {s : Set α} (f : β -> α) {g : α -> M} {x : β}
  proof: by
  tauto

@[to_additive]

中文:
引理 mulIndicator_comp_right
  条件: {s : Set α} (f : β -> α) {g : α -> M} {x : β}
  证明: by
  tauto

@[to_additive]
-/
lemma mulIndicator_comp_right {s : Set α} (f : β -> α) {g : α -> M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  tauto

@[to_additive]
/--
lemma `mulIndicator_image` / 引理 `mulIndicator_image`

English:
lemma mulIndicator_image
  given: {s : Set α} {f : β -> M} {g : α -> β} (hg : Injective g) {x : α}
  proof: by
  rw [← mulIndicator_comp_right]; rw [preimage_image_eq _ hg]

@[to_additive]

中文:
引理 mulIndicator_image
  条件: {s : Set α} {f : β -> M} {g : α -> β} (hg : Injective g) {x : α}
  证明: by
  rw [← mulIndicator_comp_right]; rw [preimage_image_eq _ hg]

@[to_additive]

Depends on / 依赖: mulIndicator_comp_right, preimage_image_eq
-/
lemma mulIndicator_image {s : Set α} {f : β -> M} {g : α -> β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mulIndicator_comp_right]; rw [preimage_image_eq _ hg]

@[to_additive]
/--
lemma `mulIndicator_comp_of_one` / 引理 `mulIndicator_comp_of_one`

English:
lemma mulIndicator_comp_of_one
  given: {g : M -> N} (hg : g 1 = 1)
  proof: by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]

中文:
引理 mulIndicator_comp_of_one
  条件: {g : M -> N} (hg : g 1 = 1)
  证明: by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]

Depends on / 依赖: mulIndicator, split_ifs
-/
lemma mulIndicator_comp_of_one {g : M -> N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]
/--
lemma `comp_mulIndicator_const` / 引理 `comp_mulIndicator_const`

English:
lemma comp_mulIndicator_const
  given: (c : M) (f : M -> N) (hf : f 1 = 1)
  proof: (mulIndicator_comp_of_one hf).symm

中文:
引理 comp_mulIndicator_const
  条件: (c : M) (f : M -> N) (hf : f 1 = 1)
  证明: (mulIndicator_comp_of_one hf).symm

Depends on / 依赖: mulIndicator_comp_of_one
-/
lemma comp_mulIndicator_const (c : M) (f : M -> N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c :=
  (mulIndicator_comp_of_one hf).symm

/-- Evaluating the indicator of a family of functions at a point commutes with the indicator:
`s.mulIndicator f a b = s.mulIndicator (f · b) a`. -/
@[to_additive]
/--
lemma `mulIndicator_apply_apply` / 引理 `mulIndicator_apply_apply`

English:
lemma mulIndicator_apply_apply
  given: (f : α -> β -> M) (b : β)
  proof: by
  by_cases h : a in s <;> simp [h]

@[to_additive]

中文:
引理 mulIndicator_apply_apply
  条件: (f : α -> β -> M) (b : β)
  证明: by
  by_cases h : a in s <;> simp [h]

@[to_additive]
-/
lemma mulIndicator_apply_apply (f : α -> β -> M) (b : β) :
    s.mulIndicator f a b = s.mulIndicator (fun i => f i b) a := by
  by_cases h : a in s <;> simp [h]

@[to_additive]
/--
lemma `mulIndicator_preimage` / 引理 `mulIndicator_preimage`

English:
lemma mulIndicator_preimage
  given: (s : Set α) (f : α -> M) (B : Set M)
  proof: letI := Classical.decPred (· in s)
  piecewise_preimage s f 1 B

@[to_additive]

中文:
引理 mulIndicator_preimage
  条件: (s : Set α) (f : α -> M) (B : Set M)
  证明: letI := Classical.decPred (· in s)
  piecewise_preimage s f 1 B

@[to_additive]

Depends on / 依赖: Classical, Classical.decPred, decPred, piecewise_preimage
-/
lemma mulIndicator_preimage (s : Set α) (f : α -> M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· in s)
  piecewise_preimage s f 1 B

@[to_additive]
/--
lemma `mulIndicator_one_preimage` / 引理 `mulIndicator_one_preimage`

English:
lemma mulIndicator_one_preimage
  given: (s : Set M)
  proof: by
  classical
  rw [mulIndicator_one']; rw [Pi.one_def]; rw [Set.preimage_const]
  split_ifs <;> simp

@[to_additive]

中文:
引理 mulIndicator_one_preimage
  条件: (s : Set M)
  证明: by
  classical
  rw [mulIndicator_one']; rw [Pi.one_def]; rw [Set.preimage_const]
  split_ifs <;> simp

@[to_additive]

Depends on / 依赖: Pi.one_def, Set.preimage_const, classical, mulIndicator_one, one_def, preimage_const, split_ifs
-/
lemma mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s in ({Set.univ, ∅} : Set (Set α)) := by
  classical
  rw [mulIndicator_one']; rw [Pi.one_def]; rw [Set.preimage_const]
  split_ifs <;> simp

@[to_additive]
/--
lemma `mulIndicator_const_preimage_eq_union` / 引理 `mulIndicator_const_preimage_eq_union`

English:
lemma mulIndicator_const_preimage_eq_union
  statement: (U : Set α) (s : Set M) (a : M) [Decidable (a in s)]
  proof: by
  rw [mulIndicator_preimage]; rw [Pi.one_def]; rw [Set.preimage_const]; rw [preimage_const]
  split_ifs <;> simp [← compl_eq_univ_sdiff]

@[to_additive]

中文:
引理 mulIndicator_const_preimage_eq_union
  结论: (U : Set α) (s : Set M) (a : M) [Decidable (a in s)]
  证明: by
  rw [mulIndicator_preimage]; rw [Pi.one_def]; rw [Set.preimage_const]; rw [preimage_const]
  split_ifs <;> simp [← compl_eq_univ_sdiff]

@[to_additive]

Depends on / 依赖: Pi.one_def, Set.preimage_const, compl_eq_univ_sdiff, mulIndicator_preimage, one_def, preimage_const, split_ifs
-/
lemma mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a in s)]
    [Decidable ((1 : M) in s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
      (if a in s then U else ∅) union if (1 : M) in s then Uᶜ else ∅ := by
  rw [mulIndicator_preimage]; rw [Pi.one_def]; rw [Set.preimage_const]; rw [preimage_const]
  split_ifs <;> simp [← compl_eq_univ_sdiff]

@[to_additive]
/--
lemma `mulIndicator_const_preimage` / 引理 `mulIndicator_const_preimage`

English:
lemma mulIndicator_const_preimage
  given: (U : Set α) (s : Set M) (a : M)
  proof: by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[to_additive]

中文:
引理 mulIndicator_const_preimage
  条件: (U : Set α) (s : Set M) (a : M)
  证明: by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[to_additive]

Depends on / 依赖: classical, mulIndicator_const_preimage_eq_union, split_ifs
-/
lemma mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s in ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[to_additive]
/--
lemma `mulIndicator_preimage_of_notMem` / 引理 `mulIndicator_preimage_of_notMem`

English:
lemma mulIndicator_preimage_of_notMem
  given: (s : Set α) (f : α -> M) {t : Set M} (ht : (1 : M) ∉ t)
  proof: by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

@[to_additive]

中文:
引理 mulIndicator_preimage_of_notMem
  条件: (s : Set α) (f : α -> M) {t : Set M} (ht : (1 : M) ∉ t)
  证明: by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

@[to_additive]

Depends on / 依赖: Pi.one_def, Set.preimage_const_of_notMem, mulIndicator_preimage, one_def, preimage_const_of_notMem
-/
lemma mulIndicator_preimage_of_notMem (s : Set α) (f : α -> M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t inter s := by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

@[to_additive]
/--
lemma `mem_range_mulIndicator` / 引理 `mem_range_mulIndicator`

English:
lemma mem_range_mulIndicator
  given: {r : M} {s : Set α} {f : α -> M}
  proof: by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[to_additive]

中文:
引理 mem_range_mulIndicator
  条件: {r : M} {s : Set α} {f : α -> M}
  证明: by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[to_additive]

Depends on / 依赖: and_comm, eq_comm, eq_univ_iff_forall, exists_or, ite_eq_iff, mulIndicator, or_comm
-/
lemma mem_range_mulIndicator {r : M} {s : Set α} {f : α -> M} :
    r in range (mulIndicator s f) ↔ r = 1 ∧ s != univ ∨ r in f '' s := by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[to_additive]
/--
lemma `mulIndicator_rel_mulIndicator` / 引理 `mulIndicator_rel_mulIndicator`

English:
lemma mulIndicator_rel_mulIndicator
  given: {r : M -> M -> Prop} (h1 : r 1 1) (ha : a in s -> r (f a) (g a))
  proof: by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]

中文:
引理 mulIndicator_rel_mulIndicator
  条件: {r : M -> M -> 命题} (h1 : r 1 1) (ha : a in s -> r (f a) (g a))
  证明: by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]

Depends on / 依赖: exacts, mulIndicator, split_ifs
-/
lemma mulIndicator_rel_mulIndicator {r : M -> M -> Prop} (h1 : r 1 1) (ha : a in s -> r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]

/--
lemma `indicator_one_preimage` / 引理 `indicator_one_preimage`

English:
lemma indicator_one_preimage
  given: [Zero M] (U : Set α) (s : Set M)
  proof: indicator_const_preimage _ _ 1

中文:
引理 indicator_one_preimage
  条件: [Zero M] (U : Set α) (s : Set M)
  证明: indicator_const_preimage _ _ 1

Depends on / 依赖: indicator_const_preimage
-/
lemma indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s in ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) :=
  indicator_const_preimage _ _ 1

end Set
