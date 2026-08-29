/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FastInstance

/-!
# Boolean algebra of sets

This file proves that `Set α` is a Boolean algebra, and proves results about set difference and
complement.

## Notation

* `sᶜ` for the complement of `s`

## Tags

set, sets, subset, subsets, complement
-/

@[expose] public section

assert_not_exists RelIso

open Function

namespace Set
variable {α β : Type*} {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HImp (Set α)
  body: {x | x in s -> x in t}

中文:
实例 :
  签名: HImp (集合 α)
  定义体: {x | x in s -> x in t}
-/
instance : HImp (Set α) where
  himp s t := {x | x in s -> x in t}

/--
theorem `mem_himp_iff` / 定理 `mem_himp_iff`

English:
theorem mem_himp_iff
  statement: a in s ⇨ t ↔ a in s -> a in t
  proof: .rfl

中文:
定理 mem_himp_iff
  结论: a in s ⇨ t ↔ a in s -> a in t
  证明: .rfl
-/
@[simp] theorem mem_himp_iff : a in s ⇨ t ↔ a in s -> a in t := .rfl

/--
Instance `instBooleanAlgebra` / 实例 `instBooleanAlgebra`

English:
instance instBooleanAlgebra
  signature: : BooleanAlgebra (Set α)
  body: fast_instance% { (inferInstance : BooleanAlgebra (α -> Prop)) with }

中文:
实例 inst布尔eanAlgebra
  签名: : 布尔代数 (集合 α)
  定义体: fast_instance% { (inferInstance : BooleanAlgebra (α -> Prop)) with }

Depends on / 依赖: BooleanAlgebra, fast_instance
-/
instance instBooleanAlgebra : BooleanAlgebra (Set α) :=
  fast_instance% { (inferInstance : BooleanAlgebra (α -> Prop)) with }

/--
theorem `himp_def` / 定理 `himp_def`

English:
theorem himp_def
  statement: s ⇨ t = t union sᶜ
  proof: himp_eq

中文:
定理 himp_def
  结论: s ⇨ t = t union sᶜ
  证明: himp_eq

Depends on / 依赖: himp_eq
-/
theorem himp_def : s ⇨ t = t union sᶜ := himp_eq

/--
lemma `inter_sdiff_assoc` / 引理 `inter_sdiff_assoc`

English:
lemma inter_sdiff_assoc
  given: (a b c : Set α)
  statement: (a inter b) \ c = a inter (b \ c)
  proof: inf_sdiff_assoc ..

@[deprecated (since := "2026-06-03")] alias inter_diff_assoc := inter_sdiff_assoc

中文:
引理 inter_sdiff_assoc
  条件: (a b c : 集合 α)
  结论: (a inter b) \ c = a inter (b \ c)
  证明: inf_sdiff_assoc ..

@[deprecated (since := "2026-06-03")] alias inter_diff_assoc := inter_sdiff_assoc

Depends on / 依赖: inf_sdiff_assoc
-/
lemma inter_sdiff_assoc (a b c : Set α) : (a inter b) \ c = a inter (b \ c) := inf_sdiff_assoc ..

@[deprecated (since := "2026-06-03")] alias inter_diff_assoc := inter_sdiff_assoc

/--
lemma `sdiff_inter_right_comm` / 引理 `sdiff_inter_right_comm`

English:
lemma sdiff_inter_right_comm
  given: (s t u : Set α)
  statement: s \ t inter u = (s inter u) \ t
  proof: sdiff_inf_right_comm ..

中文:
引理 sdiff_inter_right_comm
  条件: (s t u : 集合 α)
  结论: s \ t inter u = (s inter u) \ t
  证明: sdiff_inf_right_comm ..

Depends on / 依赖: sdiff_inf_right_comm
-/
lemma sdiff_inter_right_comm (s t u : Set α) : s \ t inter u = (s inter u) \ t := sdiff_inf_right_comm ..

/--
lemma `inter_sdiff_left_comm` / 引理 `inter_sdiff_left_comm`

English:
lemma inter_sdiff_left_comm
  given: (s t u : Set α)
  statement: s inter (t \ u) = t inter (s \ u)
  proof: inf_sdiff_left_comm ..

中文:
引理 inter_sdiff_left_comm
  条件: (s t u : 集合 α)
  结论: s inter (t \ u) = t inter (s \ u)
  证明: inf_sdiff_left_comm ..

Depends on / 依赖: inf_sdiff_left_comm
-/
lemma inter_sdiff_left_comm (s t u : Set α) : s inter (t \ u) = t inter (s \ u) := inf_sdiff_left_comm ..

/--
theorem `sdiff_union_sdiff_cancel` / 定理 `sdiff_union_sdiff_cancel`

English:
theorem sdiff_union_sdiff_cancel
  given: (hts : t subseteq s) (hut : u subseteq t)
  statement: s \ t union t \ u = s \ u
  proof: sdiff_sup_sdiff_cancel hts hut

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel := sdiff_union_sdiff_cancel

中文:
定理 sdiff_union_sdiff_cancel
  条件: (hts : t subseteq s) (hut : u subseteq t)
  结论: s \ t union t \ u = s \ u
  证明: sdiff_sup_sdiff_cancel hts hut

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel := sdiff_union_sdiff_cancel

Depends on / 依赖: sdiff_sup_sdiff_cancel
-/
theorem sdiff_union_sdiff_cancel (hts : t subseteq s) (hut : u subseteq t) : s \ t union t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel := sdiff_union_sdiff_cancel

/--
theorem `sdiff_union_sdiff_cancel'` / 定理 `sdiff_union_sdiff_cancel'`

English:
theorem sdiff_union_sdiff_cancel'
  given: (hi : s inter u subseteq t) (hu : t subseteq s union u)
  statement: (s \ t) union (t \ u) = s \ u
  proof: sdiff_sup_sdiff_cancel' hi hu

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel' := sdiff_union_sdiff_cancel'

中文:
定理 sdiff_union_sdiff_cancel'
  条件: (hi : s inter u subseteq t) (hu : t subseteq s union u)
  结论: (s \ t) union (t \ u) = s \ u
  证明: sdiff_sup_sdiff_cancel' hi hu

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel' := sdiff_union_sdiff_cancel'

Depends on / 依赖: sdiff_sup_sdiff_cancel
-/
theorem sdiff_union_sdiff_cancel' (hi : s inter u subseteq t) (hu : t subseteq s union u) : (s \ t) union (t \ u) = s \ u :=
  sdiff_sup_sdiff_cancel' hi hu

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel' := sdiff_union_sdiff_cancel'

/--
theorem `sdiff_sdiff_eq_sdiff_union` / 定理 `sdiff_sdiff_eq_sdiff_union`

English:
theorem sdiff_sdiff_eq_sdiff_union
  given: (h : u subseteq s)
  statement: s \ (t \ u) = s \ t union u
  proof: sdiff_sdiff_eq_sdiff_sup h

@[deprecated (since := "2026-06-03")] alias diff_diff_eq_sdiff_union := sdiff_sdiff_eq_sdiff_union

中文:
定理 sdiff_sdiff_eq_sdiff_union
  条件: (h : u subseteq s)
  结论: s \ (t \ u) = s \ t union u
  证明: sdiff_sdiff_eq_sdiff_sup h

@[deprecated (since := "2026-06-03")] alias diff_diff_eq_sdiff_union := sdiff_sdiff_eq_sdiff_union

Depends on / 依赖: sdiff_sdiff_eq_sdiff_sup
-/
theorem sdiff_sdiff_eq_sdiff_union (h : u subseteq s) : s \ (t \ u) = s \ t union u :=
  sdiff_sdiff_eq_sdiff_sup h

@[deprecated (since := "2026-06-03")] alias diff_diff_eq_sdiff_union := sdiff_sdiff_eq_sdiff_union

/--
theorem `inter_sdiff_distrib_left` / 定理 `inter_sdiff_distrib_left`

English:
theorem inter_sdiff_distrib_left
  given: (s t u : Set α)
  statement: s inter (t \ u) = (s inter t) \ (s inter u)
  proof: inf_sdiff_distrib_left _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_left := inter_sdiff_distrib_left

中文:
定理 inter_sdiff_distrib_left
  条件: (s t u : 集合 α)
  结论: s inter (t \ u) = (s inter t) \ (s inter u)
  证明: inf_sdiff_distrib_left _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_left := inter_sdiff_distrib_left

Depends on / 依赖: inf_sdiff_distrib_left
-/
theorem inter_sdiff_distrib_left (s t u : Set α) : s inter (t \ u) = (s inter t) \ (s inter u) :=
  inf_sdiff_distrib_left _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_left := inter_sdiff_distrib_left

/--
theorem `inter_sdiff_distrib_right` / 定理 `inter_sdiff_distrib_right`

English:
theorem inter_sdiff_distrib_right
  given: (s t u : Set α)
  statement: (s \ t) inter u = (s inter u) \ (t inter u)
  proof: inf_sdiff_distrib_right _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_right := inter_sdiff_distrib_right

中文:
定理 inter_sdiff_distrib_right
  条件: (s t u : 集合 α)
  结论: (s \ t) inter u = (s inter u) \ (t inter u)
  证明: inf_sdiff_distrib_right _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_right := inter_sdiff_distrib_right

Depends on / 依赖: inf_sdiff_distrib_right
-/
theorem inter_sdiff_distrib_right (s t u : Set α) : (s \ t) inter u = (s inter u) \ (t inter u) :=
  inf_sdiff_distrib_right _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_right := inter_sdiff_distrib_right

/--
theorem `sdiff_inter_distrib_right` / 定理 `sdiff_inter_distrib_right`

English:
theorem sdiff_inter_distrib_right
  given: (s t r : Set α)
  statement: (t inter r) \ s = (t \ s) inter (r \ s)
  proof: inf_sdiff

@[deprecated (since := "2026-06-03")] alias diff_inter_distrib_right := sdiff_inter_distrib_right

中文:
定理 sdiff_inter_distrib_right
  条件: (s t r : 集合 α)
  结论: (t inter r) \ s = (t \ s) inter (r \ s)
  证明: inf_sdiff

@[deprecated (since := "2026-06-03")] alias diff_inter_distrib_right := sdiff_inter_distrib_right

Depends on / 依赖: inf_sdiff
-/
theorem sdiff_inter_distrib_right (s t r : Set α) : (t inter r) \ s = (t \ s) inter (r \ s) :=
  inf_sdiff

@[deprecated (since := "2026-06-03")] alias diff_inter_distrib_right := sdiff_inter_distrib_right


/--
theorem `compl_def` / 定理 `compl_def`

English:
theorem compl_def
  given: (s : Set α)
  statement: sᶜ = { x | x ∉ s }
  proof: rfl

中文:
定理 compl_def
  条件: (s : 集合 α)
  结论: sᶜ = { x | x ∉ s }
  证明: rfl
-/
theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl

/--
theorem `mem_compl` / 定理 `mem_compl`

English:
theorem mem_compl
  given: {s : Set α} {x : α} (h : x ∉ s)
  statement: x in sᶜ
  proof: h

中文:
定理 mem_compl
  条件: {s : 集合 α} {x : α} (h : x ∉ s)
  结论: x in sᶜ
  证明: h
-/
theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ :=
  h

/--
theorem `compl_ofPred` / 定理 `compl_ofPred`

English:
theorem compl_ofPred
  given: {α} (p : α -> Prop)
  statement: { a | p a }ᶜ = { a | ¬p a }
  proof: rfl

@[deprecated (since := "2026-07-09")] alias compl_setOf := compl_ofPred

中文:
定理 compl_ofPred
  条件: {α} (p : α -> 命题)
  结论: { a | p a }ᶜ = { a | ¬p a }
  证明: rfl

@[deprecated (since := "2026-07-09")] alias compl_setOf := compl_ofPred
-/
theorem compl_ofPred {α} (p : α -> Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias compl_setOf := compl_ofPred

/--
theorem `notMem_of_mem_compl` / 定理 `notMem_of_mem_compl`

English:
theorem notMem_of_mem_compl
  given: {s : Set α} {x : α} (h : x in sᶜ)
  statement: x ∉ s
  proof: h

中文:
定理 notMem_of_mem_compl
  条件: {s : 集合 α} {x : α} (h : x in sᶜ)
  结论: x ∉ s
  证明: h
-/
theorem notMem_of_mem_compl {s : Set α} {x : α} (h : x in sᶜ) : x ∉ s :=
  h

/--
theorem `notMem_compl_iff` / 定理 `notMem_compl_iff`

English:
theorem notMem_compl_iff
  given: {x : α}
  statement: x ∉ sᶜ ↔ x in s
  proof: not_not

@[simp]

中文:
定理 notMem_compl_iff
  条件: {x : α}
  结论: x ∉ sᶜ ↔ x in s
  证明: not_not

@[simp]

Depends on / 依赖: not_not
-/
theorem notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s :=
  not_not

@[simp]
/--
theorem `inter_compl_self` / 定理 `inter_compl_self`

English:
theorem inter_compl_self
  given: (s : Set α)
  statement: s inter sᶜ = ∅
  proof: inf_compl_eq_bot

@[simp]

中文:
定理 inter_compl_self
  条件: (s : 集合 α)
  结论: s inter sᶜ = ∅
  证明: inf_compl_eq_bot

@[simp]

Depends on / 依赖: inf_compl_eq_bot
-/
theorem inter_compl_self (s : Set α) : s inter sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
/--
theorem `compl_inter_self` / 定理 `compl_inter_self`

English:
theorem compl_inter_self
  given: (s : Set α)
  statement: sᶜ inter s = ∅
  proof: compl_inf_eq_bot

@[simp]

中文:
定理 compl_inter_self
  条件: (s : 集合 α)
  结论: sᶜ inter s = ∅
  证明: compl_inf_eq_bot

@[simp]

Depends on / 依赖: compl_inf_eq_bot
-/
theorem compl_inter_self (s : Set α) : sᶜ inter s = ∅ :=
  compl_inf_eq_bot

@[simp]
/--
theorem `compl_empty` / 定理 `compl_empty`

English:
theorem compl_empty
  statement: (∅ : Set α)ᶜ = univ
  proof: compl_bot

@[simp]

中文:
定理 compl_empty
  结论: (∅ : 集合 α)ᶜ = univ
  证明: compl_bot

@[simp]

Depends on / 依赖: compl_bot
-/
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot

@[simp]
/--
theorem `compl_union` / 定理 `compl_union`

English:
theorem compl_union
  given: (s t : Set α)
  statement: (s union t)ᶜ = sᶜ inter tᶜ
  proof: compl_sup

中文:
定理 compl_union
  条件: (s t : 集合 α)
  结论: (s union t)ᶜ = sᶜ inter tᶜ
  证明: compl_sup

Depends on / 依赖: compl_sup
-/
theorem compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ :=
  compl_sup

/--
theorem `compl_inter` / 定理 `compl_inter`

English:
theorem compl_inter
  given: (s t : Set α)
  statement: (s inter t)ᶜ = sᶜ union tᶜ
  proof: compl_inf

@[simp]

中文:
定理 compl_inter
  条件: (s t : 集合 α)
  结论: (s inter t)ᶜ = sᶜ union tᶜ
  证明: compl_inf

@[simp]

Depends on / 依赖: compl_inf
-/
theorem compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ :=
  compl_inf

@[simp]
/--
theorem `compl_univ` / 定理 `compl_univ`

English:
theorem compl_univ
  statement: (univ : Set α)ᶜ = ∅
  proof: compl_top

@[simp]

中文:
定理 compl_univ
  结论: (univ : 集合 α)ᶜ = ∅
  证明: compl_top

@[simp]

Depends on / 依赖: compl_top
-/
theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  compl_top

@[simp]
/--
theorem `compl_empty_iff` / 定理 `compl_empty_iff`

English:
theorem compl_empty_iff
  given: {s : Set α}
  statement: sᶜ = ∅ ↔ s = univ
  proof: compl_eq_bot

@[simp]

中文:
定理 compl_empty_iff
  条件: {s : 集合 α}
  结论: sᶜ = ∅ ↔ s = univ
  证明: compl_eq_bot

@[simp]

Depends on / 依赖: compl_eq_bot
-/
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
/--
theorem `compl_univ_iff` / 定理 `compl_univ_iff`

English:
theorem compl_univ_iff
  given: {s : Set α}
  statement: sᶜ = univ ↔ s = ∅
  proof: compl_eq_top

中文:
定理 compl_univ_iff
  条件: {s : 集合 α}
  结论: sᶜ = univ ↔ s = ∅
  证明: compl_eq_top

Depends on / 依赖: compl_eq_top
-/
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

/--
theorem `compl_ne_univ` / 定理 `compl_ne_univ`

English:
theorem compl_ne_univ
  statement: sᶜ != univ ↔ s.Nonempty
  proof: compl_univ_iff.not.trans nonempty_iff_ne_empty.symm

中文:
定理 compl_ne_univ
  结论: sᶜ != univ ↔ s.非空
  证明: compl_univ_iff.not.trans nonempty_iff_ne_empty.symm

Depends on / 依赖: compl_univ_iff, compl_univ_iff.not.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
theorem compl_ne_univ : sᶜ != univ ↔ s.Nonempty :=
  compl_univ_iff.not.trans nonempty_iff_ne_empty.symm

/--
lemma `inl_compl_union_inr_compl` / 引理 `inl_compl_union_inr_compl`

English:
lemma inl_compl_union_inr_compl
  given: {s : Set α} {t : Set β}
  proof: by
  grind

中文:
引理 inl_compl_union_inr_compl
  条件: {s : 集合 α} {t : 集合 β}
  证明: by
  grind
-/
lemma inl_compl_union_inr_compl {s : Set α} {t : Set β} :
    Sum.inl '' sᶜ union Sum.inr '' tᶜ = (Sum.inl '' s union Sum.inr '' t)ᶜ := by
  grind

/--
theorem `nonempty_compl` / 定理 `nonempty_compl`

English:
theorem nonempty_compl
  statement: sᶜ.Nonempty ↔ s != univ
  proof: (ne_univ_iff_exists_notMem s).symm

中文:
定理 nonempty_compl
  结论: sᶜ.非空 ↔ s != univ
  证明: (ne_univ_iff_exists_notMem s).symm

Depends on / 依赖: ne_univ_iff_exists_notMem
-/
theorem nonempty_compl : sᶜ.Nonempty ↔ s != univ :=
  (ne_univ_iff_exists_notMem s).symm

/--
theorem `union_eq_compl_compl_inter_compl` / 定理 `union_eq_compl_compl_inter_compl`

English:
theorem union_eq_compl_compl_inter_compl
  given: (s t : Set α)
  statement: s union t = (sᶜ inter tᶜ)ᶜ
  proof: ext fun _ => or_iff_not_and_not

中文:
定理 union_eq_compl_compl_inter_compl
  条件: (s t : 集合 α)
  结论: s union t = (sᶜ inter tᶜ)ᶜ
  证明: ext fun _ => or_iff_not_and_not

Depends on / 依赖: or_iff_not_and_not
-/
theorem union_eq_compl_compl_inter_compl (s t : Set α) : s union t = (sᶜ inter tᶜ)ᶜ :=
  ext fun _ => or_iff_not_and_not

/--
theorem `inter_eq_compl_compl_union_compl` / 定理 `inter_eq_compl_compl_union_compl`

English:
theorem inter_eq_compl_compl_union_compl
  given: (s t : Set α)
  statement: s inter t = (sᶜ union tᶜ)ᶜ
  proof: ext fun _ => and_iff_not_or_not

@[simp]

中文:
定理 inter_eq_compl_compl_union_compl
  条件: (s t : 集合 α)
  结论: s inter t = (sᶜ union tᶜ)ᶜ
  证明: ext fun _ => and_iff_not_or_not

@[simp]

Depends on / 依赖: and_iff_not_or_not
-/
theorem inter_eq_compl_compl_union_compl (s t : Set α) : s inter t = (sᶜ union tᶜ)ᶜ :=
  ext fun _ => and_iff_not_or_not

@[simp]
/--
theorem `union_compl_self` / 定理 `union_compl_self`

English:
theorem union_compl_self
  given: (s : Set α)
  statement: s union sᶜ = univ
  proof: eq_univ_iff_forall.2 fun _ => em _

@[simp]

中文:
定理 union_compl_self
  条件: (s : 集合 α)
  结论: s union sᶜ = univ
  证明: eq_univ_iff_forall.2 fun _ => em _

@[simp]

Depends on / 依赖: eq_univ_iff_forall
-/
theorem union_compl_self (s : Set α) : s union sᶜ = univ :=
  eq_univ_iff_forall.2 fun _ => em _

@[simp]
/--
theorem `compl_union_self` / 定理 `compl_union_self`

English:
theorem compl_union_self
  given: (s : Set α)
  statement: sᶜ union s = univ
  proof: by rw [union_comm, union_compl_self]

中文:
定理 compl_union_self
  条件: (s : 集合 α)
  结论: sᶜ union s = univ
  证明: by rw [union_comm, union_compl_self]

Depends on / 依赖: union_comm, union_compl_self
-/
theorem compl_union_self (s : Set α) : sᶜ union s = univ := by rw [union_comm, union_compl_self]

/--
theorem `compl_subset_comm` / 定理 `compl_subset_comm`

English:
theorem compl_subset_comm
  statement: sᶜ subseteq t ↔ tᶜ subseteq s
  proof: compl_le_iff_compl_le

中文:
定理 compl_subset_comm
  结论: sᶜ subseteq t ↔ tᶜ subseteq s
  证明: compl_le_iff_compl_le

Depends on / 依赖: compl_le_iff_compl_le
-/
theorem compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s :=
  compl_le_iff_compl_le

/--
theorem `subset_compl_comm` / 定理 `subset_compl_comm`

English:
theorem subset_compl_comm
  statement: s subseteq tᶜ ↔ t subseteq sᶜ
  proof: le_compl_iff_le_compl

中文:
定理 subset_compl_comm
  结论: s subseteq tᶜ ↔ t subseteq sᶜ
  证明: le_compl_iff_le_compl

Depends on / 依赖: le_compl_iff_le_compl
-/
theorem subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ :=
  le_compl_iff_le_compl

/--
theorem `compl_subset_compl` / 定理 `compl_subset_compl`

English:
theorem compl_subset_compl
  statement: sᶜ subseteq tᶜ ↔ t subseteq s
  proof: compl_le_compl_iff_le

中文:
定理 compl_subset_compl
  结论: sᶜ subseteq tᶜ ↔ t subseteq s
  证明: compl_le_compl_iff_le

Depends on / 依赖: compl_le_compl_iff_le
-/
theorem compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq s :=
  compl_le_compl_iff_le

/--
theorem `compl_subset_compl_of_subset` / 定理 `compl_subset_compl_of_subset`

English:
theorem compl_subset_compl_of_subset
  given: (h : t subseteq s)
  statement: sᶜ subseteq tᶜ
  proof: by gcongr

中文:
定理 compl_subset_compl_of_subset
  条件: (h : t subseteq s)
  结论: sᶜ subseteq tᶜ
  证明: by gcongr
-/
theorem compl_subset_compl_of_subset (h : t subseteq s) : sᶜ subseteq tᶜ := by gcongr

/--
theorem `subset_union_compl_iff_inter_subset` / 定理 `subset_union_compl_iff_inter_subset`

English:
theorem subset_union_compl_iff_inter_subset
  given: {s t u : Set α}
  statement: s subseteq t union uᶜ ↔ s inter u subseteq t
  proof: (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le

中文:
定理 subset_union_compl_iff_inter_subset
  条件: {s t u : 集合 α}
  结论: s subseteq t union uᶜ ↔ s inter u subseteq t
  证明: (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le

Depends on / 依赖: isCompl_compl, le_sup_right_iff_inf_left_le
-/
theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s subseteq t union uᶜ ↔ s inter u subseteq t :=
  (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le

/--
theorem `compl_subset_iff_union` / 定理 `compl_subset_iff_union`

English:
theorem compl_subset_iff_union
  given: {s t : Set α}
  statement: sᶜ subseteq t ↔ s union t = univ
  proof: Iff.symm eq_univ_iff_forall.trans forall_congr' fun _ => or_iff_not_imp_left

中文:
定理 compl_subset_iff_union
  条件: {s t : 集合 α}
  结论: sᶜ subseteq t ↔ s union t = univ
  证明: Iff.symm eq_univ_iff_forall.trans forall_congr' fun _ => or_iff_not_imp_left

Depends on / 依赖: Iff.symm, eq_univ_iff_forall, eq_univ_iff_forall.trans, forall_congr, or_iff_not_imp_left
-/
theorem compl_subset_iff_union {s t : Set α} : sᶜ subseteq t ↔ s union t = univ :=
Iff.symm eq_univ_iff_forall.trans forall_congr' fun _ => or_iff_not_imp_left

/--
theorem `inter_subset` / 定理 `inter_subset`

English:
theorem inter_subset
  given: (a b c : Set α)
  statement: a inter b subseteq c ↔ a subseteq bᶜ union c
  proof: forall_congr' fun _ => and_imp.trans imp_congr_right fun _ => imp_iff_not_or

中文:
定理 inter_subset
  条件: (a b c : 集合 α)
  结论: a inter b subseteq c ↔ a subseteq bᶜ union c
  证明: forall_congr' fun _ => and_imp.trans imp_congr_right fun _ => imp_iff_not_or

Depends on / 依赖: and_imp, and_imp.trans, forall_congr, imp_congr_right, imp_iff_not_or
-/
theorem inter_subset (a b c : Set α) : a inter b subseteq c ↔ a subseteq bᶜ union c :=
forall_congr' fun _ => and_imp.trans imp_congr_right fun _ => imp_iff_not_or

/--
theorem `inter_compl_nonempty_iff` / 定理 `inter_compl_nonempty_iff`

English:
theorem inter_compl_nonempty_iff
  given: {s t : Set α}
  statement: (s inter tᶜ).Nonempty ↔ ¬s subseteq t
  proof: (not_subset.trans <| exists_congr fun x => by simp).symm

中文:
定理 inter_compl_nonempty_iff
  条件: {s t : 集合 α}
  结论: (s inter tᶜ).非空 ↔ ¬s subseteq t
  证明: (not_subset.trans <| exists_congr fun x => by simp).symm

Depends on / 依赖: exists_congr, not_subset, not_subset.trans
-/
theorem inter_compl_nonempty_iff {s t : Set α} : (s inter tᶜ).Nonempty ↔ ¬s subseteq t :=
  (not_subset.trans <| exists_congr fun x => by simp).symm

/--
lemma `subset_compl_iff_disjoint_left` / 引理 `subset_compl_iff_disjoint_left`

English:
lemma subset_compl_iff_disjoint_left
  statement: s subseteq tᶜ ↔ Disjoint t s
  proof: le_compl_iff_disjoint_left

中文:
引理 subset_compl_iff_disjoint_left
  结论: s subseteq tᶜ ↔ Disjoint t s
  证明: le_compl_iff_disjoint_left

Depends on / 依赖: le_compl_iff_disjoint_left
-/
lemma subset_compl_iff_disjoint_left : s subseteq tᶜ ↔ Disjoint t s := le_compl_iff_disjoint_left
/--
lemma `subset_compl_iff_disjoint_right` / 引理 `subset_compl_iff_disjoint_right`

English:
lemma subset_compl_iff_disjoint_right
  statement: s subseteq tᶜ ↔ Disjoint s t
  proof: le_compl_iff_disjoint_right

中文:
引理 subset_compl_iff_disjoint_right
  结论: s subseteq tᶜ ↔ Disjoint s t
  证明: le_compl_iff_disjoint_right

Depends on / 依赖: le_compl_iff_disjoint_right
-/
lemma subset_compl_iff_disjoint_right : s subseteq tᶜ ↔ Disjoint s t := le_compl_iff_disjoint_right
/--
lemma `disjoint_compl_left_iff_subset` / 引理 `disjoint_compl_left_iff_subset`

English:
lemma disjoint_compl_left_iff_subset
  statement: Disjoint sᶜ t ↔ t subseteq s
  proof: disjoint_compl_left_iff

中文:
引理 disjoint_compl_left_iff_subset
  结论: Disjoint sᶜ t ↔ t subseteq s
  证明: disjoint_compl_left_iff

Depends on / 依赖: disjoint_compl_left_iff
-/
lemma disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t subseteq s := disjoint_compl_left_iff
/--
lemma `disjoint_compl_right_iff_subset` / 引理 `disjoint_compl_right_iff_subset`

English:
lemma disjoint_compl_right_iff_subset
  statement: Disjoint s tᶜ ↔ s subseteq t
  proof: disjoint_compl_right_iff

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
@[deprecated LE.le.disjoint_compl_left (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_l

中文:
引理 disjoint_compl_right_iff_subset
  结论: Disjoint s tᶜ ↔ s subseteq t
  证明: disjoint_compl_right_iff

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
@[deprecated LE.le.disjoint_compl_left (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_l

Depends on / 依赖: disjoint_compl_right_iff
-/
lemma disjoint_compl_right_iff_subset : Disjoint s tᶜ ↔ s subseteq t := disjoint_compl_right_iff

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
@[deprecated LE.le.disjoint_compl_left (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_left⟩ := disjoint_compl_left_iff_subset
@[deprecated LE.le.disjoint_compl_right (since := "2026-06-05")]
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_right⟩ := disjoint_compl_right_iff_subset

/--
lemma `nonempty_compl_of_nontrivial` / 引理 `nonempty_compl_of_nontrivial`

English:
lemma nonempty_compl_of_nontrivial
  given: [Nontrivial α] (x : α)
  statement: Set.Nonempty {x}ᶜ
  proof: exists_ne x

中文:
引理 nonempty_compl_of_nontrivial
  条件: [非平凡 α] (x : α)
  结论: 集合.非空 {x}ᶜ
  证明: exists_ne x
-/
@[simp] lemma nonempty_compl_of_nontrivial [Nontrivial α] (x : α) : Set.Nonempty {x}ᶜ := exists_ne x

/--
lemma `mem_compl_singleton_iff` / 引理 `mem_compl_singleton_iff`

English:
lemma mem_compl_singleton_iff
  statement: a in ({b} : Set α)ᶜ ↔ a != b
  proof: .rfl

中文:
引理 mem_compl_singleton_iff
  结论: a in ({b} : 集合 α)ᶜ ↔ a != b
  证明: .rfl
-/
lemma mem_compl_singleton_iff : a in ({b} : Set α)ᶜ ↔ a != b := .rfl

/--
lemma `compl_singleton_eq` / 引理 `compl_singleton_eq`

English:
lemma compl_singleton_eq
  given: (a : α)
  statement: {a}ᶜ = {x | x != a}
  proof: rfl

@[simp]

中文:
引理 compl_singleton_eq
  条件: (a : α)
  结论: {a}ᶜ = {x | x != a}
  证明: rfl

@[simp]
-/
lemma compl_singleton_eq (a : α) : {a}ᶜ = {x | x != a} := rfl

@[simp]
/--
lemma `compl_ne_eq_singleton` / 引理 `compl_ne_eq_singleton`

English:
lemma compl_ne_eq_singleton
  given: (a : α)
  statement: {x | x != a}ᶜ = {a}
  proof: compl_compl _

@[simp]

中文:
引理 compl_ne_eq_singleton
  条件: (a : α)
  结论: {x | x != a}ᶜ = {a}
  证明: compl_compl _

@[simp]

Depends on / 依赖: compl_compl
-/
lemma compl_ne_eq_singleton (a : α) : {x | x != a}ᶜ = {a} := compl_compl _

@[simp]
/--
lemma `subset_compl_singleton_iff` / 引理 `subset_compl_singleton_iff`

English:
lemma subset_compl_singleton_iff
  statement: s subseteq {a}ᶜ ↔ a ∉ s
  proof: subset_compl_comm.trans singleton_subset_iff

中文:
引理 subset_compl_singleton_iff
  结论: s subseteq {a}ᶜ ↔ a ∉ s
  证明: subset_compl_comm.trans singleton_subset_iff

Depends on / 依赖: singleton_subset_iff, subset_compl_comm, subset_compl_comm.trans
-/
lemma subset_compl_singleton_iff : s subseteq {a}ᶜ ↔ a ∉ s := subset_compl_comm.trans singleton_subset_iff


/--
theorem `notMem_sdiff_of_mem` / 定理 `notMem_sdiff_of_mem`

English:
theorem notMem_sdiff_of_mem
  given: {s t : Set α} {x : α} (hx : x in t)
  statement: x ∉ s \ t
  proof: fun h => h.2 hx

@[deprecated (since := "2026-06-03")] alias notMem_diff_of_mem := notMem_sdiff_of_mem

中文:
定理 notMem_sdiff_of_mem
  条件: {s t : 集合 α} {x : α} (hx : x in t)
  结论: x ∉ s \ t
  证明: fun h => h.2 hx

@[deprecated (since := "2026-06-03")] alias notMem_diff_of_mem := notMem_sdiff_of_mem
-/
theorem notMem_sdiff_of_mem {s t : Set α} {x : α} (hx : x in t) : x ∉ s \ t := fun h => h.2 hx

@[deprecated (since := "2026-06-03")] alias notMem_diff_of_mem := notMem_sdiff_of_mem

/--
theorem `mem_of_mem_sdiff` / 定理 `mem_of_mem_sdiff`

English:
theorem mem_of_mem_sdiff
  given: {s t : Set α} {x : α} (h : x in s \ t)
  statement: x in s
  proof: h.left

@[deprecated (since := "2026-06-03")] alias mem_of_mem_diff := mem_of_mem_sdiff

中文:
定理 mem_of_mem_sdiff
  条件: {s t : 集合 α} {x : α} (h : x in s \ t)
  结论: x in s
  证明: h.left

@[deprecated (since := "2026-06-03")] alias mem_of_mem_diff := mem_of_mem_sdiff

Depends on / 依赖: h.left
-/
theorem mem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s \ t) : x in s :=
  h.left

@[deprecated (since := "2026-06-03")] alias mem_of_mem_diff := mem_of_mem_sdiff

/--
theorem `notMem_of_mem_sdiff` / 定理 `notMem_of_mem_sdiff`

English:
theorem notMem_of_mem_sdiff
  given: {s t : Set α} {x : α} (h : x in s \ t)
  statement: x ∉ t
  proof: h.right

@[deprecated (since := "2026-06-03")] alias notMem_of_mem_diff := notMem_of_mem_sdiff

中文:
定理 notMem_of_mem_sdiff
  条件: {s t : 集合 α} {x : α} (h : x in s \ t)
  结论: x ∉ t
  证明: h.right

@[deprecated (since := "2026-06-03")] alias notMem_of_mem_diff := notMem_of_mem_sdiff

Depends on / 依赖: h.right
-/
theorem notMem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s \ t) : x ∉ t :=
  h.right

@[deprecated (since := "2026-06-03")] alias notMem_of_mem_diff := notMem_of_mem_sdiff

/--
theorem `sdiff_eq_compl_inter` / 定理 `sdiff_eq_compl_inter`

English:
theorem sdiff_eq_compl_inter
  given: {s t : Set α}
  statement: s \ t = tᶜ inter s
  proof: by rw [sdiff_eq, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_eq_compl_inter := sdiff_eq_compl_inter

中文:
定理 sdiff_eq_compl_inter
  条件: {s t : 集合 α}
  结论: s \ t = tᶜ inter s
  证明: by rw [sdiff_eq, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_eq_compl_inter := sdiff_eq_compl_inter

Depends on / 依赖: inter_comm, sdiff_eq
-/
theorem sdiff_eq_compl_inter {s t : Set α} : s \ t = tᶜ inter s := by rw [sdiff_eq, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_eq_compl_inter := sdiff_eq_compl_inter

/--
theorem `sdiff_nonempty` / 定理 `sdiff_nonempty`

English:
theorem sdiff_nonempty
  given: {s t : Set α}
  statement: (s \ t).Nonempty ↔ ¬s subseteq t
  proof: inter_compl_nonempty_iff

@[deprecated (since := "2026-06-03")] alias diff_nonempty := sdiff_nonempty

中文:
定理 sdiff_nonempty
  条件: {s t : 集合 α}
  结论: (s \ t).非空 ↔ ¬s subseteq t
  证明: inter_compl_nonempty_iff

@[deprecated (since := "2026-06-03")] alias diff_nonempty := sdiff_nonempty

Depends on / 依赖: inter_compl_nonempty_iff
-/
theorem sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s subseteq t :=
  inter_compl_nonempty_iff

@[deprecated (since := "2026-06-03")] alias diff_nonempty := sdiff_nonempty

/--
theorem `sdiff_subset` / 定理 `sdiff_subset`

English:
theorem sdiff_subset
  given: {s t : Set α}
  statement: s \ t subseteq s
  proof: sdiff_le

@[deprecated (since := "2026-06-03")] alias diff_subset := sdiff_subset

中文:
定理 sdiff_subset
  条件: {s t : 集合 α}
  结论: s \ t subseteq s
  证明: sdiff_le

@[deprecated (since := "2026-06-03")] alias diff_subset := sdiff_subset

Depends on / 依赖: sdiff_le
-/
theorem sdiff_subset {s t : Set α} : s \ t subseteq s := sdiff_le

@[deprecated (since := "2026-06-03")] alias diff_subset := sdiff_subset

/--
theorem `sdiff_subset_compl` / 定理 `sdiff_subset_compl`

English:
theorem sdiff_subset_compl
  given: (s t : Set α)
  statement: s \ t subseteq tᶜ
  proof: sdiff_eq_compl_inter ▸ inter_subset_left

@[deprecated (since := "2026-06-03")] alias diff_subset_compl := sdiff_subset_compl

中文:
定理 sdiff_subset_compl
  条件: (s t : 集合 α)
  结论: s \ t subseteq tᶜ
  证明: sdiff_eq_compl_inter ▸ inter_subset_left

@[deprecated (since := "2026-06-03")] alias diff_subset_compl := sdiff_subset_compl

Depends on / 依赖: inter_subset_left, sdiff_eq_compl_inter
-/
theorem sdiff_subset_compl (s t : Set α) : s \ t subseteq tᶜ :=
  sdiff_eq_compl_inter ▸ inter_subset_left

@[deprecated (since := "2026-06-03")] alias diff_subset_compl := sdiff_subset_compl

/--
theorem `union_sdiff_cancel'` / 定理 `union_sdiff_cancel'`

English:
theorem union_sdiff_cancel'
  given: {s t u : Set α} (h₁ : s subseteq t) (h₂ : t subseteq u)
  statement: t union u \ s = u
  proof: sup_sdiff_cancel' h₁ h₂

@[deprecated (since := "2026-06-03")] alias union_diff_cancel' := union_sdiff_cancel'

中文:
定理 union_sdiff_cancel'
  条件: {s t u : 集合 α} (h₁ : s subseteq t) (h₂ : t subseteq u)
  结论: t union u \ s = u
  证明: sup_sdiff_cancel' h₁ h₂

@[deprecated (since := "2026-06-03")] alias union_diff_cancel' := union_sdiff_cancel'

Depends on / 依赖: sup_sdiff_cancel
-/
theorem union_sdiff_cancel' {s t u : Set α} (h₁ : s subseteq t) (h₂ : t subseteq u) : t union u \ s = u :=
  sup_sdiff_cancel' h₁ h₂

@[deprecated (since := "2026-06-03")] alias union_diff_cancel' := union_sdiff_cancel'

/--
theorem `union_sdiff_cancel` / 定理 `union_sdiff_cancel`

English:
theorem union_sdiff_cancel
  given: {s t : Set α} (h : s subseteq t)
  statement: s union t \ s = t
  proof: sup_sdiff_cancel_right h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel := union_sdiff_cancel

中文:
定理 union_sdiff_cancel
  条件: {s t : 集合 α} (h : s subseteq t)
  结论: s union t \ s = t
  证明: sup_sdiff_cancel_right h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel := union_sdiff_cancel

Depends on / 依赖: sup_sdiff_cancel_right
-/
theorem union_sdiff_cancel {s t : Set α} (h : s subseteq t) : s union t \ s = t :=
  sup_sdiff_cancel_right h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel := union_sdiff_cancel

/--
theorem `union_sdiff_cancel_left` / 定理 `union_sdiff_cancel_left`

English:
theorem union_sdiff_cancel_left
  given: {s t : Set α} (h : s inter t subseteq ∅)
  statement: (s union t) \ s = t
  proof: Disjoint.sup_sdiff_cancel_left disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_left := union_sdiff_cancel_left

中文:
定理 union_sdiff_cancel_left
  条件: {s t : 集合 α} (h : s inter t subseteq ∅)
  结论: (s union t) \ s = t
  证明: Disjoint.sup_sdiff_cancel_left disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_left := union_sdiff_cancel_left

Depends on / 依赖: Disjoint, Disjoint.sup_sdiff_cancel_left, disjoint_iff_inf_le, sup_sdiff_cancel_left
-/
theorem union_sdiff_cancel_left {s t : Set α} (h : s inter t subseteq ∅) : (s union t) \ s = t :=
Disjoint.sup_sdiff_cancel_left disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_left := union_sdiff_cancel_left

/--
theorem `union_sdiff_cancel_right` / 定理 `union_sdiff_cancel_right`

English:
theorem union_sdiff_cancel_right
  given: {s t : Set α} (h : s inter t subseteq ∅)
  statement: (s union t) \ t = s
  proof: Disjoint.sup_sdiff_cancel_right disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_right := union_sdiff_cancel_right

@[simp]

中文:
定理 union_sdiff_cancel_right
  条件: {s t : 集合 α} (h : s inter t subseteq ∅)
  结论: (s union t) \ t = s
  证明: Disjoint.sup_sdiff_cancel_right disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_right := union_sdiff_cancel_right

@[simp]

Depends on / 依赖: Disjoint, Disjoint.sup_sdiff_cancel_right, disjoint_iff_inf_le, sup_sdiff_cancel_right
-/
theorem union_sdiff_cancel_right {s t : Set α} (h : s inter t subseteq ∅) : (s union t) \ t = s :=
Disjoint.sup_sdiff_cancel_right disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_right := union_sdiff_cancel_right

@[simp]
/--
theorem `union_sdiff_left` / 定理 `union_sdiff_left`

English:
theorem union_sdiff_left
  given: {s t : Set α}
  statement: (s union t) \ s = t \ s
  proof: sup_sdiff_left_self

@[deprecated (since := "2026-06-03")] alias union_diff_left := union_sdiff_left

@[simp]

中文:
定理 union_sdiff_left
  条件: {s t : 集合 α}
  结论: (s union t) \ s = t \ s
  证明: sup_sdiff_left_self

@[deprecated (since := "2026-06-03")] alias union_diff_left := union_sdiff_left

@[simp]

Depends on / 依赖: sup_sdiff_left_self
-/
theorem union_sdiff_left {s t : Set α} : (s union t) \ s = t \ s :=
  sup_sdiff_left_self

@[deprecated (since := "2026-06-03")] alias union_diff_left := union_sdiff_left

@[simp]
/--
theorem `union_sdiff_right` / 定理 `union_sdiff_right`

English:
theorem union_sdiff_right
  given: {s t : Set α}
  statement: (s union t) \ t = s \ t
  proof: sup_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias union_diff_right := union_sdiff_right

中文:
定理 union_sdiff_right
  条件: {s t : 集合 α}
  结论: (s union t) \ t = s \ t
  证明: sup_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias union_diff_right := union_sdiff_right

Depends on / 依赖: sup_sdiff_right_self
-/
theorem union_sdiff_right {s t : Set α} : (s union t) \ t = s \ t :=
  sup_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias union_diff_right := union_sdiff_right

/--
theorem `union_sdiff_distrib` / 定理 `union_sdiff_distrib`

English:
theorem union_sdiff_distrib
  given: {s t u : Set α}
  statement: (s union t) \ u = s \ u union t \ u
  proof: sup_sdiff

@[deprecated (since := "2026-06-03")] alias union_diff_distrib := union_sdiff_distrib

@[simp]

中文:
定理 union_sdiff_distrib
  条件: {s t u : 集合 α}
  结论: (s union t) \ u = s \ u union t \ u
  证明: sup_sdiff

@[deprecated (since := "2026-06-03")] alias union_diff_distrib := union_sdiff_distrib

@[simp]

Depends on / 依赖: sup_sdiff
-/
theorem union_sdiff_distrib {s t u : Set α} : (s union t) \ u = s \ u union t \ u :=
  sup_sdiff

@[deprecated (since := "2026-06-03")] alias union_diff_distrib := union_sdiff_distrib

@[simp]
/--
theorem `inter_sdiff_self` / 定理 `inter_sdiff_self`

English:
theorem inter_sdiff_self
  given: (a b : Set α)
  statement: a inter (b \ a) = ∅
  proof: inf_sdiff_self_right

@[deprecated (since := "2026-06-03")] alias inter_diff_self := inter_sdiff_self

@[simp]

中文:
定理 inter_sdiff_self
  条件: (a b : 集合 α)
  结论: a inter (b \ a) = ∅
  证明: inf_sdiff_self_right

@[deprecated (since := "2026-06-03")] alias inter_diff_self := inter_sdiff_self

@[simp]

Depends on / 依赖: inf_sdiff_self_right
-/
theorem inter_sdiff_self (a b : Set α) : a inter (b \ a) = ∅ :=
  inf_sdiff_self_right

@[deprecated (since := "2026-06-03")] alias inter_diff_self := inter_sdiff_self

@[simp]
/--
theorem `inter_union_sdiff` / 定理 `inter_union_sdiff`

English:
theorem inter_union_sdiff
  given: (s t : Set α)
  statement: s inter t union s \ t = s
  proof: sup_inf_sdiff s t

@[deprecated (since := "2026-06-03")] alias inter_union_diff := inter_union_sdiff

@[simp]

中文:
定理 inter_union_sdiff
  条件: (s t : 集合 α)
  结论: s inter t union s \ t = s
  证明: sup_inf_sdiff s t

@[deprecated (since := "2026-06-03")] alias inter_union_diff := inter_union_sdiff

@[simp]

Depends on / 依赖: sup_inf_sdiff
-/
theorem inter_union_sdiff (s t : Set α) : s inter t union s \ t = s :=
  sup_inf_sdiff s t

@[deprecated (since := "2026-06-03")] alias inter_union_diff := inter_union_sdiff

@[simp]
/--
theorem `sdiff_union_inter` / 定理 `sdiff_union_inter`

English:
theorem sdiff_union_inter
  given: (s t : Set α)
  statement: s \ t union s inter t = s
  proof: by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[deprecated (since := "2026-06-03")] alias diff_union_inter := sdiff_union_inter

@[simp]

中文:
定理 sdiff_union_inter
  条件: (s t : 集合 α)
  结论: s \ t union s inter t = s
  证明: by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[deprecated (since := "2026-06-03")] alias diff_union_inter := sdiff_union_inter

@[simp]

Depends on / 依赖: sup_inf_sdiff, union_comm
-/
theorem sdiff_union_inter (s t : Set α) : s \ t union s inter t = s := by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[deprecated (since := "2026-06-03")] alias diff_union_inter := sdiff_union_inter

@[simp]
/--
theorem `inter_union_compl` / 定理 `inter_union_compl`

English:
theorem inter_union_compl
  given: (s t : Set α)
  statement: s inter t union s inter tᶜ = s
  proof: inter_union_sdiff _ _

中文:
定理 inter_union_compl
  条件: (s t : 集合 α)
  结论: s inter t union s inter tᶜ = s
  证明: inter_union_sdiff _ _

Depends on / 依赖: inter_union_sdiff
-/
theorem inter_union_compl (s t : Set α) : s inter t union s inter tᶜ = s :=
  inter_union_sdiff _ _

/--
theorem `subset_inter_union_compl_left` / 定理 `subset_inter_union_compl_left`

English:
theorem subset_inter_union_compl_left
  given: (s t : Set α)
  statement: t subseteq s inter t union sᶜ
  proof: by
  simp [inter_union_distrib_right]

中文:
定理 subset_inter_union_compl_left
  条件: (s t : 集合 α)
  结论: t subseteq s inter t union sᶜ
  证明: by
  simp [inter_union_distrib_right]

Depends on / 依赖: inter_union_distrib_right
-/
theorem subset_inter_union_compl_left (s t : Set α) : t subseteq s inter t union sᶜ := by
  simp [inter_union_distrib_right]

/--
theorem `subset_inter_union_compl_right` / 定理 `subset_inter_union_compl_right`

English:
theorem subset_inter_union_compl_right
  given: (s t : Set α)
  statement: s subseteq s inter t union tᶜ
  proof: by
  simp [inter_union_distrib_right]

中文:
定理 subset_inter_union_compl_right
  条件: (s t : 集合 α)
  结论: s subseteq s inter t union tᶜ
  证明: by
  simp [inter_union_distrib_right]

Depends on / 依赖: inter_union_distrib_right
-/
theorem subset_inter_union_compl_right (s t : Set α) : s subseteq s inter t union tᶜ := by
  simp [inter_union_distrib_right]

/--
theorem `union_inter_compl_left_subset` / 定理 `union_inter_compl_left_subset`

English:
theorem union_inter_compl_left_subset
  given: (s t : Set α)
  statement: (s union t) inter sᶜ subseteq t
  proof: by
  simp [union_inter_distrib_right]

中文:
定理 union_inter_compl_left_subset
  条件: (s t : 集合 α)
  结论: (s union t) inter sᶜ subseteq t
  证明: by
  simp [union_inter_distrib_right]

Depends on / 依赖: union_inter_distrib_right
-/
theorem union_inter_compl_left_subset (s t : Set α) : (s union t) inter sᶜ subseteq t := by
  simp [union_inter_distrib_right]

/--
theorem `union_inter_compl_right_subset` / 定理 `union_inter_compl_right_subset`

English:
theorem union_inter_compl_right_subset
  given: (s t : Set α)
  statement: (s union t) inter tᶜ subseteq s
  proof: by
  simp [union_inter_distrib_right]

中文:
定理 union_inter_compl_right_subset
  条件: (s t : 集合 α)
  结论: (s union t) inter tᶜ subseteq s
  证明: by
  simp [union_inter_distrib_right]

Depends on / 依赖: union_inter_distrib_right
-/
theorem union_inter_compl_right_subset (s t : Set α) : (s union t) inter tᶜ subseteq s := by
  simp [union_inter_distrib_right]

/--
theorem `sdiff_subset_sdiff` / 定理 `sdiff_subset_sdiff`

English:
theorem sdiff_subset_sdiff
  given: {s₁ s₂ t₁ t₂ : Set α}
  statement: s₁ subseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
  proof: sdiff_le_sdiff

@[deprecated (since := "2026-06-03")] alias diff_subset_diff := sdiff_subset_sdiff

中文:
定理 sdiff_subset_sdiff
  条件: {s₁ s₂ t₁ t₂ : 集合 α}
  结论: s₁ subseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
  证明: sdiff_le_sdiff

@[deprecated (since := "2026-06-03")] alias diff_subset_diff := sdiff_subset_sdiff

Depends on / 依赖: sdiff_le_sdiff
-/
theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ subseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂ :=
  sdiff_le_sdiff

@[deprecated (since := "2026-06-03")] alias diff_subset_diff := sdiff_subset_sdiff

/--
theorem `sdiff_subset_sdiff_left` / 定理 `sdiff_subset_sdiff_left`

English:
theorem sdiff_subset_sdiff_left
  given: {s₁ s₂ t : Set α} (h : s₁ subseteq s₂)
  statement: s₁ \ t subseteq s₂ \ t
  proof: by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_left := sdiff_subset_sdiff_left

中文:
定理 sdiff_subset_sdiff_left
  条件: {s₁ s₂ t : 集合 α} (h : s₁ subseteq s₂)
  结论: s₁ \ t subseteq s₂ \ t
  证明: by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_left := sdiff_subset_sdiff_left
-/
theorem sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t := by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_left := sdiff_subset_sdiff_left

/--
theorem `sdiff_subset_sdiff_right` / 定理 `sdiff_subset_sdiff_right`

English:
theorem sdiff_subset_sdiff_right
  given: {s t u : Set α} (h : t subseteq u)
  statement: s \ u subseteq s \ t
  proof: by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_right := sdiff_subset_sdiff_right

中文:
定理 sdiff_subset_sdiff_right
  条件: {s t u : 集合 α} (h : t subseteq u)
  结论: s \ u subseteq s \ t
  证明: by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_right := sdiff_subset_sdiff_right
-/
theorem sdiff_subset_sdiff_right {s t u : Set α} (h : t subseteq u) : s \ u subseteq s \ t := by
  gcongr

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_right := sdiff_subset_sdiff_right

/--
theorem `sdiff_subset_sdiff_iff_subset` / 定理 `sdiff_subset_sdiff_iff_subset`

English:
theorem sdiff_subset_sdiff_iff_subset
  given: {r : Set α} (hs : s subseteq r) (ht : t subseteq r)
  proof: sdiff_le_sdiff_iff_le hs ht

@[deprecated (since := "2026-06-03")]
alias diff_subset_diff_iff_subset := sdiff_subset_sdiff_iff_subset

中文:
定理 sdiff_subset_sdiff_iff_subset
  条件: {r : 集合 α} (hs : s subseteq r) (ht : t subseteq r)
  证明: sdiff_le_sdiff_iff_le hs ht

@[deprecated (since := "2026-06-03")]
alias diff_subset_diff_iff_subset := sdiff_subset_sdiff_iff_subset

Depends on / 依赖: sdiff_le_sdiff_iff_le
-/
theorem sdiff_subset_sdiff_iff_subset {r : Set α} (hs : s subseteq r) (ht : t subseteq r) :
    r \ s subseteq r \ t ↔ t subseteq s :=
  sdiff_le_sdiff_iff_le hs ht

@[deprecated (since := "2026-06-03")]
alias diff_subset_diff_iff_subset := sdiff_subset_sdiff_iff_subset

/--
theorem `compl_eq_univ_sdiff` / 定理 `compl_eq_univ_sdiff`

English:
theorem compl_eq_univ_sdiff
  given: (s : Set α)
  statement: sᶜ = univ \ s
  proof: top_sdiff.symm

@[deprecated (since := "2026-06-03")] alias compl_eq_univ_diff := compl_eq_univ_sdiff

@[simp]

中文:
定理 compl_eq_univ_sdiff
  条件: (s : 集合 α)
  结论: sᶜ = univ \ s
  证明: top_sdiff.symm

@[deprecated (since := "2026-06-03")] alias compl_eq_univ_diff := compl_eq_univ_sdiff

@[simp]

Depends on / 依赖: top_sdiff, top_sdiff.symm
-/
theorem compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm

@[deprecated (since := "2026-06-03")] alias compl_eq_univ_diff := compl_eq_univ_sdiff

@[simp]
/--
theorem `empty_sdiff` / 定理 `empty_sdiff`

English:
theorem empty_sdiff
  given: (s : Set α)
  statement: (∅ \ s : Set α) = ∅
  proof: bot_sdiff

@[deprecated (since := "2026-06-03")] alias empty_diff := empty_sdiff

中文:
定理 empty_sdiff
  条件: (s : 集合 α)
  结论: (∅ \ s : 集合 α) = ∅
  证明: bot_sdiff

@[deprecated (since := "2026-06-03")] alias empty_diff := empty_sdiff

Depends on / 依赖: bot_sdiff
-/
theorem empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff

@[deprecated (since := "2026-06-03")] alias empty_diff := empty_sdiff

/--
theorem `sdiff_eq_empty` / 定理 `sdiff_eq_empty`

English:
theorem sdiff_eq_empty
  given: {s t : Set α}
  statement: s \ t = ∅ ↔ s subseteq t
  proof: sdiff_eq_bot_iff

@[deprecated (since := "2026-06-03")] alias diff_eq_empty := sdiff_eq_empty

@[simp]

中文:
定理 sdiff_eq_empty
  条件: {s t : 集合 α}
  结论: s \ t = ∅ ↔ s subseteq t
  证明: sdiff_eq_bot_iff

@[deprecated (since := "2026-06-03")] alias diff_eq_empty := sdiff_eq_empty

@[simp]

Depends on / 依赖: sdiff_eq_bot_iff
-/
theorem sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subseteq t :=
  sdiff_eq_bot_iff

@[deprecated (since := "2026-06-03")] alias diff_eq_empty := sdiff_eq_empty

@[simp]
/--
theorem `sdiff_empty` / 定理 `sdiff_empty`

English:
theorem sdiff_empty
  given: {s : Set α}
  statement: s \ ∅ = s
  proof: sdiff_bot

@[deprecated (since := "2026-06-03")] alias diff_empty := sdiff_empty

@[simp]

中文:
定理 sdiff_empty
  条件: {s : 集合 α}
  结论: s \ ∅ = s
  证明: sdiff_bot

@[deprecated (since := "2026-06-03")] alias diff_empty := sdiff_empty

@[simp]

Depends on / 依赖: sdiff_bot
-/
theorem sdiff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot

@[deprecated (since := "2026-06-03")] alias diff_empty := sdiff_empty

@[simp]
/--
theorem `sdiff_univ` / 定理 `sdiff_univ`

English:
theorem sdiff_univ
  given: (s : Set α)
  statement: s \ univ = ∅
  proof: sdiff_eq_empty.2 (subset_univ s)

@[deprecated (since := "2026-06-03")] alias diff_univ := sdiff_univ

中文:
定理 sdiff_univ
  条件: (s : 集合 α)
  结论: s \ univ = ∅
  证明: sdiff_eq_empty.2 (subset_univ s)

@[deprecated (since := "2026-06-03")] alias diff_univ := sdiff_univ

Depends on / 依赖: sdiff_eq_empty, subset_univ
-/
theorem sdiff_univ (s : Set α) : s \ univ = ∅ :=
  sdiff_eq_empty.2 (subset_univ s)

@[deprecated (since := "2026-06-03")] alias diff_univ := sdiff_univ

/--
theorem `sdiff_sdiff` / 定理 `sdiff_sdiff`

English:
theorem sdiff_sdiff
  given: {u : Set α}
  statement: (s \ t) \ u = s \ (t union u)
  proof: sdiff_sdiff_left

@[deprecated (since := "2026-06-03")] alias diff_diff := sdiff_sdiff

中文:
定理 sdiff_sdiff
  条件: {u : 集合 α}
  结论: (s \ t) \ u = s \ (t union u)
  证明: sdiff_sdiff_left

@[deprecated (since := "2026-06-03")] alias diff_diff := sdiff_sdiff

Depends on / 依赖: sdiff_sdiff_left
-/
theorem sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u) :=
  sdiff_sdiff_left

@[deprecated (since := "2026-06-03")] alias diff_diff := sdiff_sdiff

-- the following statement contains parentheses to help the reader
/--
theorem `sdiff_sdiff_comm` / 定理 `sdiff_sdiff_comm`

English:
theorem sdiff_sdiff_comm
  given: {s t u : Set α}
  statement: (s \ t) \ u = (s \ u) \ t
  proof: _root_.sdiff_sdiff_comm

@[deprecated (since := "2026-06-03")] alias diff_diff_comm := sdiff_sdiff_comm

@[simp]

中文:
定理 sdiff_sdiff_comm
  条件: {s t u : 集合 α}
  结论: (s \ t) \ u = (s \ u) \ t
  证明: _root_.sdiff_sdiff_comm

@[deprecated (since := "2026-06-03")] alias diff_diff_comm := sdiff_sdiff_comm

@[simp]

Depends on / 依赖: _root_, _root_.sdiff_sdiff_comm, sdiff_sdiff_comm
-/
theorem sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  _root_.sdiff_sdiff_comm

@[deprecated (since := "2026-06-03")] alias diff_diff_comm := sdiff_sdiff_comm

@[simp]
/--
theorem `sdiff_subset_iff` / 定理 `sdiff_subset_iff`

English:
theorem sdiff_subset_iff
  given: {s t u : Set α}
  statement: s \ t subseteq u ↔ s subseteq t union u
  proof: sdiff_le_iff

@[deprecated (since := "2026-06-03")] alias diff_subset_iff := sdiff_subset_iff

中文:
定理 sdiff_subset_iff
  条件: {s t u : 集合 α}
  结论: s \ t subseteq u ↔ s subseteq t union u
  证明: sdiff_le_iff

@[deprecated (since := "2026-06-03")] alias diff_subset_iff := sdiff_subset_iff

Depends on / 依赖: sdiff_le_iff
-/
theorem sdiff_subset_iff {s t u : Set α} : s \ t subseteq u ↔ s subseteq t union u :=
  sdiff_le_iff

@[deprecated (since := "2026-06-03")] alias diff_subset_iff := sdiff_subset_iff

/--
theorem `subset_sdiff_union` / 定理 `subset_sdiff_union`

English:
theorem subset_sdiff_union
  given: (s t : Set α)
  statement: s subseteq s \ t union t
  proof: le_sdiff_sup

@[deprecated (since := "2026-06-03")] alias subset_diff_union := subset_sdiff_union

中文:
定理 subset_sdiff_union
  条件: (s t : 集合 α)
  结论: s subseteq s \ t union t
  证明: le_sdiff_sup

@[deprecated (since := "2026-06-03")] alias subset_diff_union := subset_sdiff_union

Depends on / 依赖: le_sdiff_sup
-/
theorem subset_sdiff_union (s t : Set α) : s subseteq s \ t union t :=
  le_sdiff_sup

@[deprecated (since := "2026-06-03")] alias subset_diff_union := subset_sdiff_union

/--
theorem `sdiff_union_of_subset` / 定理 `sdiff_union_of_subset`

English:
theorem sdiff_union_of_subset
  given: {s t : Set α} (h : t subseteq s)
  statement: s \ t union t = s
  proof: Subset.antisymm (union_subset sdiff_subset h) (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias diff_union_of_subset := sdiff_union_of_subset

中文:
定理 sdiff_union_of_subset
  条件: {s t : 集合 α} (h : t subseteq s)
  结论: s \ t union t = s
  证明: Subset.antisymm (union_subset sdiff_subset h) (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias diff_union_of_subset := sdiff_union_of_subset

Depends on / 依赖: Subset, Subset.antisymm, antisymm, sdiff_subset, subset_sdiff_union, union_subset
-/
theorem sdiff_union_of_subset {s t : Set α} (h : t subseteq s) : s \ t union t = s :=
  Subset.antisymm (union_subset sdiff_subset h) (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias diff_union_of_subset := sdiff_union_of_subset

/--
theorem `sdiff_subset_comm` / 定理 `sdiff_subset_comm`

English:
theorem sdiff_subset_comm
  given: {s t u : Set α}
  statement: s \ t subseteq u ↔ s \ u subseteq t
  proof: sdiff_le_comm

@[deprecated (since := "2026-06-03")] alias diff_subset_comm := sdiff_subset_comm

中文:
定理 sdiff_subset_comm
  条件: {s t u : 集合 α}
  结论: s \ t subseteq u ↔ s \ u subseteq t
  证明: sdiff_le_comm

@[deprecated (since := "2026-06-03")] alias diff_subset_comm := sdiff_subset_comm

Depends on / 依赖: sdiff_le_comm
-/
theorem sdiff_subset_comm {s t u : Set α} : s \ t subseteq u ↔ s \ u subseteq t :=
  sdiff_le_comm

@[deprecated (since := "2026-06-03")] alias diff_subset_comm := sdiff_subset_comm

/--
theorem `sdiff_inter` / 定理 `sdiff_inter`

English:
theorem sdiff_inter
  given: {s t u : Set α}
  statement: s \ (t inter u) = s \ t union s \ u
  proof: sdiff_inf

@[deprecated (since := "2026-06-03")] alias diff_inter := sdiff_inter

中文:
定理 sdiff_inter
  条件: {s t u : 集合 α}
  结论: s \ (t inter u) = s \ t union s \ u
  证明: sdiff_inf

@[deprecated (since := "2026-06-03")] alias diff_inter := sdiff_inter

Depends on / 依赖: sdiff_inf
-/
theorem sdiff_inter {s t u : Set α} : s \ (t inter u) = s \ t union s \ u :=
  sdiff_inf

@[deprecated (since := "2026-06-03")] alias diff_inter := sdiff_inter

/--
theorem `sdiff_inter_sdiff` / 定理 `sdiff_inter_sdiff`

English:
theorem sdiff_inter_sdiff
  statement: s \ t inter (s \ u) = s \ (t union u)
  proof: sdiff_sup.symm

@[deprecated (since := "2026-06-03")] alias diff_inter_diff := sdiff_inter_sdiff

中文:
定理 sdiff_inter_sdiff
  结论: s \ t inter (s \ u) = s \ (t union u)
  证明: sdiff_sup.symm

@[deprecated (since := "2026-06-03")] alias diff_inter_diff := sdiff_inter_sdiff

Depends on / 依赖: sdiff_sup, sdiff_sup.symm
-/
theorem sdiff_inter_sdiff : s \ t inter (s \ u) = s \ (t union u) :=
  sdiff_sup.symm

@[deprecated (since := "2026-06-03")] alias diff_inter_diff := sdiff_inter_sdiff

/--
theorem `sdiff_compl` / 定理 `sdiff_compl`

English:
theorem sdiff_compl
  statement: s \ tᶜ = s inter t
  proof: _root_.sdiff_compl

@[deprecated (since := "2026-06-03")] alias diff_compl := sdiff_compl

中文:
定理 sdiff_compl
  结论: s \ tᶜ = s inter t
  证明: _root_.sdiff_compl

@[deprecated (since := "2026-06-03")] alias diff_compl := sdiff_compl

Depends on / 依赖: _root_, _root_.sdiff_compl, sdiff_compl
-/
theorem sdiff_compl : s \ tᶜ = s inter t :=
  _root_.sdiff_compl

@[deprecated (since := "2026-06-03")] alias diff_compl := sdiff_compl

/--
theorem `compl_sdiff` / 定理 `compl_sdiff`

English:
theorem compl_sdiff
  statement: (t \ s)ᶜ = s union tᶜ
  proof: Eq.trans _root_.compl_sdiff himp_eq

@[deprecated (since := "2026-06-03")] alias compl_diff := compl_sdiff

中文:
定理 compl_sdiff
  结论: (t \ s)ᶜ = s union tᶜ
  证明: Eq.trans _root_.compl_sdiff himp_eq

@[deprecated (since := "2026-06-03")] alias compl_diff := compl_sdiff

Depends on / 依赖: Eq.trans, _root_, _root_.compl_sdiff, compl_sdiff, himp_eq
-/
theorem compl_sdiff : (t \ s)ᶜ = s union tᶜ :=
  Eq.trans _root_.compl_sdiff himp_eq

@[deprecated (since := "2026-06-03")] alias compl_diff := compl_sdiff

/--
theorem `sdiff_sdiff_right` / 定理 `sdiff_sdiff_right`

English:
theorem sdiff_sdiff_right
  given: {s t u : Set α}
  statement: s \ (t \ u) = s \ t union s inter u
  proof: sdiff_sdiff_right'

@[deprecated (since := "2026-06-03")] alias diff_diff_right := sdiff_sdiff_right

中文:
定理 sdiff_sdiff_right
  条件: {s t u : 集合 α}
  结论: s \ (t \ u) = s \ t union s inter u
  证明: sdiff_sdiff_right'

@[deprecated (since := "2026-06-03")] alias diff_diff_right := sdiff_sdiff_right

Depends on / 依赖: sdiff_sdiff_right
-/
theorem sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) = s \ t union s inter u :=
  sdiff_sdiff_right'

@[deprecated (since := "2026-06-03")] alias diff_diff_right := sdiff_sdiff_right

/--
theorem `inter_sdiff_right_comm` / 定理 `inter_sdiff_right_comm`

English:
theorem inter_sdiff_right_comm
  statement: (s inter t) \ u = s \ u inter t
  proof: by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_right_comm]

@[deprecated (since := "2026-06-03")] alias diff_inter_right_comm := inter_sdiff_right_comm

@[simp]

中文:
定理 inter_sdiff_right_comm
  结论: (s inter t) \ u = s \ u inter t
  证明: by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_right_comm]

@[deprecated (since := "2026-06-03")] alias diff_inter_right_comm := inter_sdiff_right_comm

@[simp]

Depends on / 依赖: inter_right_comm, sdiff_eq
-/
theorem inter_sdiff_right_comm : (s inter t) \ u = s \ u inter t := by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_right_comm]

@[deprecated (since := "2026-06-03")] alias diff_inter_right_comm := inter_sdiff_right_comm

@[simp]
/--
theorem `union_sdiff_self` / 定理 `union_sdiff_self`

English:
theorem union_sdiff_self
  given: {s t : Set α}
  statement: s union t \ s = s union t
  proof: sup_sdiff_self _ _

@[deprecated (since := "2026-06-03")] alias union_diff_self := union_sdiff_self

@[simp]

中文:
定理 union_sdiff_self
  条件: {s t : 集合 α}
  结论: s union t \ s = s union t
  证明: sup_sdiff_self _ _

@[deprecated (since := "2026-06-03")] alias union_diff_self := union_sdiff_self

@[simp]

Depends on / 依赖: sup_sdiff_self
-/
theorem union_sdiff_self {s t : Set α} : s union t \ s = s union t :=
  sup_sdiff_self _ _

@[deprecated (since := "2026-06-03")] alias union_diff_self := union_sdiff_self

@[simp]
/--
theorem `sdiff_union_self` / 定理 `sdiff_union_self`

English:
theorem sdiff_union_self
  given: {s t : Set α}
  statement: s \ t union t = s union t
  proof: sdiff_sup_self _ _

@[deprecated (since := "2026-06-03")] alias diff_union_self := sdiff_union_self

@[simp]

中文:
定理 sdiff_union_self
  条件: {s t : 集合 α}
  结论: s \ t union t = s union t
  证明: sdiff_sup_self _ _

@[deprecated (since := "2026-06-03")] alias diff_union_self := sdiff_union_self

@[simp]

Depends on / 依赖: sdiff_sup_self
-/
theorem sdiff_union_self {s t : Set α} : s \ t union t = s union t :=
  sdiff_sup_self _ _

@[deprecated (since := "2026-06-03")] alias diff_union_self := sdiff_union_self

@[simp]
/--
theorem `sdiff_inter_self` / 定理 `sdiff_inter_self`

English:
theorem sdiff_inter_self
  given: {a b : Set α}
  statement: b \ a inter a = ∅
  proof: inf_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias diff_inter_self := sdiff_inter_self

@[simp]

中文:
定理 sdiff_inter_self
  条件: {a b : 集合 α}
  结论: b \ a inter a = ∅
  证明: inf_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias diff_inter_self := sdiff_inter_self

@[simp]

Depends on / 依赖: inf_sdiff_self_left
-/
theorem sdiff_inter_self {a b : Set α} : b \ a inter a = ∅ :=
  inf_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias diff_inter_self := sdiff_inter_self

@[simp]
/--
theorem `sdiff_inter_self_eq_sdiff` / 定理 `sdiff_inter_self_eq_sdiff`

English:
theorem sdiff_inter_self_eq_sdiff
  given: {s t : Set α}
  statement: s \ (t inter s) = s \ t
  proof: sdiff_inf_self_right _ _

@[deprecated (since := "2026-06-03")] alias diff_inter_self_eq_diff := sdiff_inter_self_eq_sdiff

@[simp]

中文:
定理 sdiff_inter_self_eq_sdiff
  条件: {s t : 集合 α}
  结论: s \ (t inter s) = s \ t
  证明: sdiff_inf_self_right _ _

@[deprecated (since := "2026-06-03")] alias diff_inter_self_eq_diff := sdiff_inter_self_eq_sdiff

@[simp]

Depends on / 依赖: sdiff_inf_self_right
-/
theorem sdiff_inter_self_eq_sdiff {s t : Set α} : s \ (t inter s) = s \ t :=
  sdiff_inf_self_right _ _

@[deprecated (since := "2026-06-03")] alias diff_inter_self_eq_diff := sdiff_inter_self_eq_sdiff

@[simp]
/--
theorem `sdiff_self_inter` / 定理 `sdiff_self_inter`

English:
theorem sdiff_self_inter
  given: {s t : Set α}
  statement: s \ (s inter t) = s \ t
  proof: sdiff_inf_self_left _ _

@[deprecated (since := "2026-06-03")] alias diff_self_inter := sdiff_self_inter

中文:
定理 sdiff_self_inter
  条件: {s t : 集合 α}
  结论: s \ (s inter t) = s \ t
  证明: sdiff_inf_self_left _ _

@[deprecated (since := "2026-06-03")] alias diff_self_inter := sdiff_self_inter

Depends on / 依赖: sdiff_inf_self_left
-/
theorem sdiff_self_inter {s t : Set α} : s \ (s inter t) = s \ t :=
  sdiff_inf_self_left _ _

@[deprecated (since := "2026-06-03")] alias diff_self_inter := sdiff_self_inter

/--
theorem `sdiff_self` / 定理 `sdiff_self`

English:
theorem sdiff_self
  given: {s : Set α}
  statement: s \ s = ∅
  proof: _root_.sdiff_self

@[deprecated (since := "2026-06-03")] alias diff_self := sdiff_self

中文:
定理 sdiff_self
  条件: {s : 集合 α}
  结论: s \ s = ∅
  证明: _root_.sdiff_self

@[deprecated (since := "2026-06-03")] alias diff_self := sdiff_self

Depends on / 依赖: _root_, _root_.sdiff_self, sdiff_self
-/
theorem sdiff_self {s : Set α} : s \ s = ∅ :=
  _root_.sdiff_self

@[deprecated (since := "2026-06-03")] alias diff_self := sdiff_self

/--
theorem `sdiff_sdiff_right_self` / 定理 `sdiff_sdiff_right_self`

English:
theorem sdiff_sdiff_right_self
  given: (s t : Set α)
  statement: s \ (s \ t) = s inter t
  proof: _root_.sdiff_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias diff_diff_right_self := sdiff_sdiff_right_self

中文:
定理 sdiff_sdiff_right_self
  条件: (s t : 集合 α)
  结论: s \ (s \ t) = s inter t
  证明: _root_.sdiff_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias diff_diff_right_self := sdiff_sdiff_right_self

Depends on / 依赖: _root_, _root_.sdiff_sdiff_right_self, sdiff_sdiff_right_self
-/
theorem sdiff_sdiff_right_self (s t : Set α) : s \ (s \ t) = s inter t :=
  _root_.sdiff_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias diff_diff_right_self := sdiff_sdiff_right_self

/--
theorem `sdiff_sdiff_cancel_left` / 定理 `sdiff_sdiff_cancel_left`

English:
theorem sdiff_sdiff_cancel_left
  given: {s t : Set α} (h : s subseteq t)
  statement: t \ (t \ s) = s
  proof: sdiff_sdiff_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_diff_cancel_left := sdiff_sdiff_cancel_left

中文:
定理 sdiff_sdiff_cancel_left
  条件: {s t : 集合 α} (h : s subseteq t)
  结论: t \ (t \ s) = s
  证明: sdiff_sdiff_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_diff_cancel_left := sdiff_sdiff_cancel_left

Depends on / 依赖: sdiff_sdiff_eq_self
-/
theorem sdiff_sdiff_cancel_left {s t : Set α} (h : s subseteq t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_diff_cancel_left := sdiff_sdiff_cancel_left

/--
theorem `union_eq_sdiff_union_sdiff_union_inter` / 定理 `union_eq_sdiff_union_sdiff_union_inter`

English:
theorem union_eq_sdiff_union_sdiff_union_inter
  given: (s t : Set α)
  statement: s union t = s \ t union t \ s union s inter t
  proof: sup_eq_sdiff_sup_sdiff_sup_inf

@[deprecated (since := "2026-06-03")]
alias union_eq_diff_union_diff_union_inter := union_eq_sdiff_union_sdiff_union_inter

中文:
定理 union_eq_sdiff_union_sdiff_union_inter
  条件: (s t : 集合 α)
  结论: s union t = s \ t union t \ s union s inter t
  证明: sup_eq_sdiff_sup_sdiff_sup_inf

@[deprecated (since := "2026-06-03")]
alias union_eq_diff_union_diff_union_inter := union_eq_sdiff_union_sdiff_union_inter

Depends on / 依赖: sup_eq_sdiff_sup_sdiff_sup_inf
-/
theorem union_eq_sdiff_union_sdiff_union_inter (s t : Set α) : s union t = s \ t union t \ s union s inter t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

@[deprecated (since := "2026-06-03")]
alias union_eq_diff_union_diff_union_inter := union_eq_sdiff_union_sdiff_union_inter

/--
lemma `sdiff_sep_self` / 引理 `sdiff_sep_self`

English:
lemma sdiff_sep_self
  given: (s : Set α) (p : α -> Prop)
  statement: s \ {a in s | p a} = {a in s | ¬ p a}
  proof: sdiff_self_inter

中文:
引理 sdiff_sep_self
  条件: (s : 集合 α) (p : α -> 命题)
  结论: s \ {a in s | p a} = {a in s | ¬ p a}
  证明: sdiff_self_inter
-/
@[simp] lemma sdiff_sep_self (s : Set α) (p : α -> Prop) : s \ {a in s | p a} = {a in s | ¬ p a} :=
  sdiff_self_inter

/--
lemma `disjoint_sdiff_left` / 引理 `disjoint_sdiff_left`

English:
lemma disjoint_sdiff_left
  statement: Disjoint (t \ s) s
  proof: disjoint_sdiff_self_left

中文:
引理 disjoint_sdiff_left
  结论: Disjoint (t \ s) s
  证明: disjoint_sdiff_self_left

Depends on / 依赖: disjoint_sdiff_self_left
-/
lemma disjoint_sdiff_left : Disjoint (t \ s) s := disjoint_sdiff_self_left

/--
lemma `disjoint_sdiff_right` / 引理 `disjoint_sdiff_right`

English:
lemma disjoint_sdiff_right
  statement: Disjoint s (t \ s)
  proof: disjoint_sdiff_self_right

中文:
引理 disjoint_sdiff_right
  结论: Disjoint s (t \ s)
  证明: disjoint_sdiff_self_right

Depends on / 依赖: disjoint_sdiff_self_right
-/
lemma disjoint_sdiff_right : Disjoint s (t \ s) := disjoint_sdiff_self_right

-- TODO: prove this in terms of a Boolean algebra lemma
/--
lemma `disjoint_sdiff_inter` / 引理 `disjoint_sdiff_inter`

English:
lemma disjoint_sdiff_inter
  statement: Disjoint (s \ t) (s inter t)
  proof: disjoint_of_subset_right inter_subset_right disjoint_sdiff_left

中文:
引理 disjoint_sdiff_inter
  结论: Disjoint (s \ t) (s inter t)
  证明: disjoint_of_subset_right inter_subset_right disjoint_sdiff_left

Depends on / 依赖: disjoint_of_subset_right, disjoint_sdiff_left, inter_subset_right
-/
lemma disjoint_sdiff_inter : Disjoint (s \ t) (s inter t) :=
  disjoint_of_subset_right inter_subset_right disjoint_sdiff_left

/--
lemma `subset_sdiff` / 引理 `subset_sdiff`

English:
lemma subset_sdiff
  statement: s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
  proof: le_sdiff

@[deprecated (since := "2026-06-03")] alias subset_diff := subset_sdiff

中文:
引理 subset_sdiff
  结论: s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
  证明: le_sdiff

@[deprecated (since := "2026-06-03")] alias subset_diff := subset_sdiff

Depends on / 依赖: le_sdiff
-/
lemma subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u := le_sdiff

@[deprecated (since := "2026-06-03")] alias subset_diff := subset_sdiff

/--
lemma `disjoint_of_subset_iff_left_eq_empty` / 引理 `disjoint_of_subset_iff_left_eq_empty`

English:
lemma disjoint_of_subset_iff_left_eq_empty
  given: (h : s subseteq t)
  statement: Disjoint s t ↔ s = ∅
  proof: disjoint_of_le_iff_left_eq_bot h

@[simp]

中文:
引理 disjoint_of_subset_iff_left_eq_empty
  条件: (h : s subseteq t)
  结论: Disjoint s t ↔ s = ∅
  证明: disjoint_of_le_iff_left_eq_bot h

@[simp]

Depends on / 依赖: disjoint_of_le_iff_left_eq_bot
-/
lemma disjoint_of_subset_iff_left_eq_empty (h : s subseteq t) : Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

@[simp]
/--
lemma `sdiff_ssubset_left_iff` / 引理 `sdiff_ssubset_left_iff`

English:
lemma sdiff_ssubset_left_iff
  statement: s \ t ⊂ s ↔ (s inter t).Nonempty
  proof: sdiff_lt_left.trans by rw [not_disjoint_iff_nonempty_inter, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_ssubset_left_iff := sdiff_ssubset_left_iff

中文:
引理 sdiff_ssubset_left_iff
  结论: s \ t ⊂ s ↔ (s inter t).非空
  证明: sdiff_lt_left.trans by rw [not_disjoint_iff_nonempty_inter, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_ssubset_left_iff := sdiff_ssubset_left_iff

Depends on / 依赖: inter_comm, not_disjoint_iff_nonempty_inter, sdiff_lt_left, sdiff_lt_left.trans
-/
lemma sdiff_ssubset_left_iff : s \ t ⊂ s ↔ (s inter t).Nonempty :=
sdiff_lt_left.trans by rw [not_disjoint_iff_nonempty_inter, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_ssubset_left_iff := sdiff_ssubset_left_iff

/--
lemma `_root_.LE.le.sdiff_ssubset_of_nonempty` / 引理 `_root_.LE.le.sdiff_ssubset_of_nonempty`

English:
lemma _root_.LE.le.sdiff_ssubset_of_nonempty
  given: (hst : s subseteq t) (hs : s.Nonempty)
  proof: by
  simpa [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty := LE.le.sdiff_ssubset_of_nonempty

@[deprecated (since := "2026-06-03")]
alias _root_.HasSubset.Subset.diff_ssubset_of_nonempty :=
  _root_.LE.le.sdiff_ssubs

中文:
引理 _root_.LE.le.sdiff_ssubset_of_nonempty
  条件: (hst : s subseteq t) (hs : s.非空)
  证明: by
  simpa [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty := LE.le.sdiff_ssubset_of_nonempty

@[deprecated (since := "2026-06-03")]
alias _root_.HasSubset.Subset.diff_ssubset_of_nonempty :=
  _root_.LE.le.sdiff_ssubs

Depends on / 依赖: inter_eq_self_of_subset_right
-/
lemma _root_.LE.le.sdiff_ssubset_of_nonempty (hst : s subseteq t) (hs : s.Nonempty) :
    t \ s ⊂ t := by
  simpa [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty := LE.le.sdiff_ssubset_of_nonempty

@[deprecated (since := "2026-06-03")]
alias _root_.HasSubset.Subset.diff_ssubset_of_nonempty :=
  _root_.LE.le.sdiff_ssubset_of_nonempty

/--
lemma `ssubset_iff_sdiff_singleton` / 引理 `ssubset_iff_sdiff_singleton`

English:
lemma ssubset_iff_sdiff_singleton
  statement: s ⊂ t ↔ exists a in t, s subseteq t \ {a}
  proof: by
  grind

中文:
引理 ssubset_iff_sdiff_singleton
  结论: s ⊂ t ↔ 存在 a in t, s subseteq t \ {a}
  证明: by
  grind
-/
lemma ssubset_iff_sdiff_singleton : s ⊂ t ↔ exists a in t, s subseteq t \ {a} := by
  grind

/--
lemma `sdiff_singleton_subset_iff` / 引理 `sdiff_singleton_subset_iff`

English:
lemma sdiff_singleton_subset_iff
  statement: s \ {a} subseteq t ↔ s subseteq insert a t
  proof: by
  simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_subset_iff := sdiff_singleton_subset_iff

中文:
引理 sdiff_singleton_subset_iff
  结论: s \ {a} subseteq t ↔ s subseteq insert a t
  证明: by
  simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_subset_iff := sdiff_singleton_subset_iff
-/
lemma sdiff_singleton_subset_iff : s \ {a} subseteq t ↔ s subseteq insert a t := by
  simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_subset_iff := sdiff_singleton_subset_iff

/--
lemma `subset_sdiff_singleton` / 引理 `subset_sdiff_singleton`

English:
lemma subset_sdiff_singleton
  given: (h : s subseteq t) (ha : a ∉ s)
  statement: s subseteq t \ {a}
  proof: subset_inter h subset_compl_comm.1 singleton_subset_iff.2 ha

@[deprecated (since := "2026-06-03")] alias subset_diff_singleton := subset_sdiff_singleton

中文:
引理 subset_sdiff_singleton
  条件: (h : s subseteq t) (ha : a ∉ s)
  结论: s subseteq t \ {a}
  证明: subset_inter h subset_compl_comm.1 singleton_subset_iff.2 ha

@[deprecated (since := "2026-06-03")] alias subset_diff_singleton := subset_sdiff_singleton

Depends on / 依赖: singleton_subset_iff, subset_compl_comm, subset_inter
-/
lemma subset_sdiff_singleton (h : s subseteq t) (ha : a ∉ s) : s subseteq t \ {a} :=
subset_inter h subset_compl_comm.1 singleton_subset_iff.2 ha

@[deprecated (since := "2026-06-03")] alias subset_diff_singleton := subset_sdiff_singleton

/--
lemma `subset_insert_sdiff_singleton` / 引理 `subset_insert_sdiff_singleton`

English:
lemma subset_insert_sdiff_singleton
  given: (x : α) (s : Set α)
  statement: s subseteq insert x (s \ {x})
  proof: by
  rw [← sdiff_singleton_subset_iff]

@[deprecated (since := "2026-06-03")]
alias subset_insert_diff_singleton := subset_insert_sdiff_singleton

中文:
引理 subset_insert_sdiff_singleton
  条件: (x : α) (s : 集合 α)
  结论: s subseteq insert x (s \ {x})
  证明: by
  rw [← sdiff_singleton_subset_iff]

@[deprecated (since := "2026-06-03")]
alias subset_insert_diff_singleton := subset_insert_sdiff_singleton

Depends on / 依赖: sdiff_singleton_subset_iff
-/
lemma subset_insert_sdiff_singleton (x : α) (s : Set α) : s subseteq insert x (s \ {x}) := by
  rw [← sdiff_singleton_subset_iff]

@[deprecated (since := "2026-06-03")]
alias subset_insert_diff_singleton := subset_insert_sdiff_singleton

/--
lemma `sdiff_insert_of_notMem` / 引理 `sdiff_insert_of_notMem`

English:
lemma sdiff_insert_of_notMem
  given: (h : a ∉ s)
  statement: s \ insert a t = s \ t
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias diff_insert_of_notMem := sdiff_insert_of_notMem

@[simp]

中文:
引理 sdiff_insert_of_notMem
  条件: (h : a ∉ s)
  结论: s \ insert a t = s \ t
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias diff_insert_of_notMem := sdiff_insert_of_notMem

@[simp]
-/
lemma sdiff_insert_of_notMem (h : a ∉ s) : s \ insert a t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias diff_insert_of_notMem := sdiff_insert_of_notMem

@[simp]
/--
lemma `insert_sdiff_of_mem` / 引理 `insert_sdiff_of_mem`

English:
lemma insert_sdiff_of_mem
  given: (s) (h : a in t)
  statement: insert a s \ t = s \ t
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_mem := insert_sdiff_of_mem

中文:
引理 insert_sdiff_of_mem
  条件: (s) (h : a in t)
  结论: insert a s \ t = s \ t
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_mem := insert_sdiff_of_mem
-/
lemma insert_sdiff_of_mem (s) (h : a in t) : insert a s \ t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_mem := insert_sdiff_of_mem

/--
lemma `insert_sdiff_of_notMem` / 引理 `insert_sdiff_of_notMem`

English:
lemma insert_sdiff_of_notMem
  given: (s) (h : a ∉ t)
  statement: insert a s \ t = insert a (s \ t)
  proof: by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_notMem := insert_sdiff_of_notMem

中文:
引理 insert_sdiff_of_notMem
  条件: (s) (h : a ∉ t)
  结论: insert a s \ t = insert a (s \ t)
  证明: by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_notMem := insert_sdiff_of_notMem
-/
lemma insert_sdiff_of_notMem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_notMem := insert_sdiff_of_notMem

/--
lemma `insert_sdiff_self_of_notMem` / 引理 `insert_sdiff_self_of_notMem`

English:
lemma insert_sdiff_self_of_notMem
  given: (h : a ∉ s)
  statement: insert a s \ {a} = s
  proof: by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_self_of_notMem := insert_sdiff_self_of_notMem

中文:
引理 insert_sdiff_self_of_notMem
  条件: (h : a ∉ s)
  结论: insert a s \ {a} = s
  证明: by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_self_of_notMem := insert_sdiff_self_of_notMem

Depends on / 依赖: and_iff_left_of_imp, ne_of_mem_of_not_mem
-/
lemma insert_sdiff_self_of_notMem (h : a ∉ s) : insert a s \ {a} = s := by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_self_of_notMem := insert_sdiff_self_of_notMem

/--
lemma `insert_sdiff_self_of_mem` / 引理 `insert_sdiff_self_of_mem`

English:
lemma insert_sdiff_self_of_mem
  given: (ha : a in s)
  statement: insert a (s \ {a}) = s
  proof: by
  ext; simp +contextual [or_and_left, em, ha]

@[deprecated (since := "2026-06-03")] alias insert_diff_self_of_mem := insert_sdiff_self_of_mem

中文:
引理 insert_sdiff_self_of_mem
  条件: (ha : a in s)
  结论: insert a (s \ {a}) = s
  证明: by
  ext; simp +contextual [or_and_left, em, ha]

@[deprecated (since := "2026-06-03")] alias insert_diff_self_of_mem := insert_sdiff_self_of_mem
-/
@[simp] lemma insert_sdiff_self_of_mem (ha : a in s) : insert a (s \ {a}) = s := by
  ext; simp +contextual [or_and_left, em, ha]

@[deprecated (since := "2026-06-03")] alias insert_diff_self_of_mem := insert_sdiff_self_of_mem

/--
lemma `insert_sdiff_subset` / 引理 `insert_sdiff_subset`

English:
lemma insert_sdiff_subset
  statement: insert a s \ t subseteq insert a (s \ t)
  proof: by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

@[deprecated (since := "2026-06-03")] alias insert_diff_subset := insert_sdiff_subset

中文:
引理 insert_sdiff_subset
  结论: insert a s \ t subseteq insert a (s \ t)
  证明: by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

@[deprecated (since := "2026-06-03")] alias insert_diff_subset := insert_sdiff_subset
-/
lemma insert_sdiff_subset : insert a s \ t subseteq insert a (s \ t) := by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

@[deprecated (since := "2026-06-03")] alias insert_diff_subset := insert_sdiff_subset

/--
lemma `insert_erase_invOn` / 引理 `insert_erase_invOn`

English:
lemma insert_erase_invOn
  proof: ⟨fun _s ha => insert_sdiff_self_of_mem ha, fun _s => insert_sdiff_self_of_notMem⟩

@[simp]

中文:
引理 insert_erase_invOn
  证明: ⟨fun _s ha => insert_sdiff_self_of_mem ha, fun _s => insert_sdiff_self_of_notMem⟩

@[simp]

Depends on / 依赖: insert_sdiff_self_of_mem, insert_sdiff_self_of_notMem
-/
lemma insert_erase_invOn :
    InvOn (insert a) (fun s => s \ {a}) {s : Set α | a in s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha => insert_sdiff_self_of_mem ha, fun _s => insert_sdiff_self_of_notMem⟩

@[simp]
/--
lemma `sdiff_singleton_eq_self` / 引理 `sdiff_singleton_eq_self`

English:
lemma sdiff_singleton_eq_self
  given: (h : a ∉ s)
  statement: s \ {a} = s
  proof: sdiff_eq_self_iff_disjoint.2 by simp [h]

@[deprecated (since := "2026-06-03")] alias diff_singleton_eq_self := sdiff_singleton_eq_self

中文:
引理 sdiff_singleton_eq_self
  条件: (h : a ∉ s)
  结论: s \ {a} = s
  证明: sdiff_eq_self_iff_disjoint.2 by simp [h]

@[deprecated (since := "2026-06-03")] alias diff_singleton_eq_self := sdiff_singleton_eq_self

Depends on / 依赖: sdiff_eq_self_iff_disjoint
-/
lemma sdiff_singleton_eq_self (h : a ∉ s) : s \ {a} = s :=
sdiff_eq_self_iff_disjoint.2 by simp [h]

@[deprecated (since := "2026-06-03")] alias diff_singleton_eq_self := sdiff_singleton_eq_self

/--
lemma `sdiff_singleton_ssubset` / 引理 `sdiff_singleton_ssubset`

English:
lemma sdiff_singleton_ssubset
  statement: s \ {a} ⊂ s ↔ a in s
  proof: by simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_ssubset := sdiff_singleton_ssubset

@[simp]

中文:
引理 sdiff_singleton_ssubset
  结论: s \ {a} ⊂ s ↔ a in s
  证明: by simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_ssubset := sdiff_singleton_ssubset

@[simp]
-/
lemma sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a in s := by simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_ssubset := sdiff_singleton_ssubset

@[simp]
/--
lemma `insert_sdiff_singleton` / 引理 `insert_sdiff_singleton`

English:
lemma insert_sdiff_singleton
  statement: insert a (s \ {a}) = insert a s
  proof: by
  simp [insert_eq, union_sdiff_self, -union_singleton, -singleton_union]

@[deprecated (since := "2026-06-03")] alias insert_diff_singleton := insert_sdiff_singleton

中文:
引理 insert_sdiff_singleton
  结论: insert a (s \ {a}) = insert a s
  证明: by
  simp [insert_eq, union_sdiff_self, -union_singleton, -singleton_union]

@[deprecated (since := "2026-06-03")] alias insert_diff_singleton := insert_sdiff_singleton

Depends on / 依赖: insert_eq, singleton_union, union_sdiff_self, union_singleton
-/
lemma insert_sdiff_singleton : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_sdiff_self, -union_singleton, -singleton_union]

@[deprecated (since := "2026-06-03")] alias insert_diff_singleton := insert_sdiff_singleton

/--
lemma `insert_sdiff_singleton_comm` / 引理 `insert_sdiff_singleton_comm`

English:
lemma insert_sdiff_singleton_comm
  given: (hab : a != b) (s : Set α)
  proof: by
  simp_rw [← union_singleton, union_sdiff_distrib,
    sdiff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_singleton_comm := insert_sdiff_singleton_comm

@[simp]

中文:
引理 insert_sdiff_singleton_comm
  条件: (hab : a != b) (s : 集合 α)
  证明: by
  simp_rw [← union_singleton, union_sdiff_distrib,
    sdiff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_singleton_comm := insert_sdiff_singleton_comm

@[simp]

Depends on / 依赖: hab.symm, mem_singleton_iff, mem_singleton_iff.not, sdiff_singleton_eq_self, simp_rw, union_sdiff_distrib, union_singleton
-/
lemma insert_sdiff_singleton_comm (hab : a != b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_sdiff_distrib,
    sdiff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_singleton_comm := insert_sdiff_singleton_comm

@[simp]
/--
lemma `insert_sdiff_insert` / 引理 `insert_sdiff_insert`

English:
lemma insert_sdiff_insert
  statement: insert a (s \ insert a t) = insert a (s \ t)
  proof: by
  rw [← union_singleton (s := t)]; rw [← sdiff_sdiff]; rw [insert_sdiff_singleton]

@[deprecated (since := "2026-06-03")] alias insert_diff_insert := insert_sdiff_insert

中文:
引理 insert_sdiff_insert
  结论: insert a (s \ insert a t) = insert a (s \ t)
  证明: by
  rw [← union_singleton (s := t)]; rw [← sdiff_sdiff]; rw [insert_sdiff_singleton]

@[deprecated (since := "2026-06-03")] alias insert_diff_insert := insert_sdiff_insert

Depends on / 依赖: insert_sdiff_singleton, sdiff_sdiff, union_singleton
-/
lemma insert_sdiff_insert : insert a (s \ insert a t) = insert a (s \ t) := by
  rw [← union_singleton (s := t)]; rw [← sdiff_sdiff]; rw [insert_sdiff_singleton]

@[deprecated (since := "2026-06-03")] alias insert_diff_insert := insert_sdiff_insert

/--
lemma `mem_sdiff_singleton` / 引理 `mem_sdiff_singleton`

English:
lemma mem_sdiff_singleton
  statement: a in s \ {b} ↔ a in s ∧ a != b
  proof: .rfl

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton := mem_sdiff_singleton

中文:
引理 mem_sdiff_singleton
  结论: a in s \ {b} ↔ a in s ∧ a != b
  证明: .rfl

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton := mem_sdiff_singleton
-/
lemma mem_sdiff_singleton : a in s \ {b} ↔ a in s ∧ a != b := .rfl

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton := mem_sdiff_singleton

/--
lemma `mem_sdiff_singleton_empty` / 引理 `mem_sdiff_singleton_empty`

English:
lemma mem_sdiff_singleton_empty
  given: {t : Set (Set α)}
  statement: s in t \ {∅} ↔ s in t ∧ s.Nonempty
  proof: mem_sdiff_singleton.trans and_congr_right' nonempty_iff_ne_empty.symm

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton_empty := mem_sdiff_singleton_empty

中文:
引理 mem_sdiff_singleton_empty
  条件: {t : 集合 (集合 α)}
  结论: s in t \ {∅} ↔ s in t ∧ s.非空
  证明: mem_sdiff_singleton.trans and_congr_right' nonempty_iff_ne_empty.symm

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton_empty := mem_sdiff_singleton_empty

Depends on / 依赖: and_congr_right, mem_sdiff_singleton, mem_sdiff_singleton.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
lemma mem_sdiff_singleton_empty {t : Set (Set α)} : s in t \ {∅} ↔ s in t ∧ s.Nonempty :=
mem_sdiff_singleton.trans and_congr_right' nonempty_iff_ne_empty.symm

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton_empty := mem_sdiff_singleton_empty

/--
lemma `subset_insert_iff` / 引理 `subset_insert_iff`

English:
lemma subset_insert_iff
  statement: s subseteq insert a t ↔ s subseteq t ∨ (a in s ∧ s \ {a} subseteq t)
  proof: by
  grind

中文:
引理 subset_insert_iff
  结论: s subseteq insert a t ↔ s subseteq t ∨ (a in s ∧ s \ {a} subseteq t)
  证明: by
  grind
-/
lemma subset_insert_iff : s subseteq insert a t ↔ s subseteq t ∨ (a in s ∧ s \ {a} subseteq t) := by
  grind

/--
lemma `pair_sdiff_left` / 引理 `pair_sdiff_left`

English:
lemma pair_sdiff_left
  given: (hab : a != b)
  statement: ({a, b} : Set α) \ {a} = {b}
  proof: by
  rw [insert_sdiff_of_mem _ (mem_singleton a)]; rw [sdiff_singleton_eq_self (by simpa)]

@[deprecated (since := "2026-06-03")] alias pair_diff_left := pair_sdiff_left

中文:
引理 pair_sdiff_left
  条件: (hab : a != b)
  结论: ({a, b} : 集合 α) \ {a} = {b}
  证明: by
  rw [insert_sdiff_of_mem _ (mem_singleton a)]; rw [sdiff_singleton_eq_self (by simpa)]

@[deprecated (since := "2026-06-03")] alias pair_diff_left := pair_sdiff_left

Depends on / 依赖: insert_sdiff_of_mem, mem_singleton, sdiff_singleton_eq_self
-/
lemma pair_sdiff_left (hab : a != b) : ({a, b} : Set α) \ {a} = {b} := by
  rw [insert_sdiff_of_mem _ (mem_singleton a)]; rw [sdiff_singleton_eq_self (by simpa)]

@[deprecated (since := "2026-06-03")] alias pair_diff_left := pair_sdiff_left

/--
lemma `pair_sdiff_right` / 引理 `pair_sdiff_right`

English:
lemma pair_sdiff_right
  given: (hab : a != b)
  statement: ({a, b} : Set α) \ {b} = {a}
  proof: by
  rw [pair_comm]; rw [pair_sdiff_left hab.symm]

@[deprecated (since := "2026-06-03")] alias pair_diff_right := pair_sdiff_right

中文:
引理 pair_sdiff_right
  条件: (hab : a != b)
  结论: ({a, b} : 集合 α) \ {b} = {a}
  证明: by
  rw [pair_comm]; rw [pair_sdiff_left hab.symm]

@[deprecated (since := "2026-06-03")] alias pair_diff_right := pair_sdiff_right

Depends on / 依赖: hab.symm, pair_comm, pair_sdiff_left
-/
lemma pair_sdiff_right (hab : a != b) : ({a, b} : Set α) \ {b} = {a} := by
  rw [pair_comm]; rw [pair_sdiff_left hab.symm]

@[deprecated (since := "2026-06-03")] alias pair_diff_right := pair_sdiff_right

/-! ### If-then-else for sets -/

/--
Definition of `ite` / `ite` 的定义

English:
definition ite
  signature: (t s s' : Set α)
  body: s inter t union s' \ t

@[simp]

中文:
定义 ite
  签名: (t s s' : 集合 α)
  定义体: s inter t union s' \ t

@[simp]
-/
protected def ite (t s s' : Set α) : Set α :=
  s inter t union s' \ t

@[simp]
/--
theorem `ite_inter_self` / 定理 `ite_inter_self`

English:
theorem ite_inter_self
  given: (t s s' : Set α)
  statement: t.ite s s' inter t = s inter t
  proof: by
  rw [Set.ite]; rw [union_inter_distrib_right]; rw [sdiff_inter_self]; rw [inter_assoc]; rw [inter_self]; rw [union_empty]

@[simp]

中文:
定理 ite_inter_self
  条件: (t s s' : 集合 α)
  结论: t.ite s s' inter t = s inter t
  证明: by
  rw [Set.ite]; rw [union_inter_distrib_right]; rw [sdiff_inter_self]; rw [inter_assoc]; rw [inter_self]; rw [union_empty]

@[simp]

Depends on / 依赖: Set.ite, inter_assoc, inter_self, sdiff_inter_self, union_empty, union_inter_distrib_right
-/
theorem ite_inter_self (t s s' : Set α) : t.ite s s' inter t = s inter t := by
  rw [Set.ite]; rw [union_inter_distrib_right]; rw [sdiff_inter_self]; rw [inter_assoc]; rw [inter_self]; rw [union_empty]

@[simp]
/--
theorem `ite_compl` / 定理 `ite_compl`

English:
theorem ite_compl
  given: (t s s' : Set α)
  statement: tᶜ.ite s s' = t.ite s' s
  proof: by
  rw [Set.ite]; rw [Set.ite]; rw [sdiff_compl]; rw [union_comm]; rw [sdiff_eq]

@[simp]

中文:
定理 ite_compl
  条件: (t s s' : 集合 α)
  结论: tᶜ.ite s s' = t.ite s' s
  证明: by
  rw [Set.ite]; rw [Set.ite]; rw [sdiff_compl]; rw [union_comm]; rw [sdiff_eq]

@[simp]

Depends on / 依赖: Set.ite, sdiff_compl, sdiff_eq, union_comm
-/
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite]; rw [Set.ite]; rw [sdiff_compl]; rw [union_comm]; rw [sdiff_eq]

@[simp]
/--
theorem `ite_inter_compl_self` / 定理 `ite_inter_compl_self`

English:
theorem ite_inter_compl_self
  given: (t s s' : Set α)
  statement: t.ite s s' inter tᶜ = s' inter tᶜ
  proof: by
  rw [← ite_compl]; rw [ite_inter_self]

@[simp]

中文:
定理 ite_inter_compl_self
  条件: (t s s' : 集合 α)
  结论: t.ite s s' inter tᶜ = s' inter tᶜ
  证明: by
  rw [← ite_compl]; rw [ite_inter_self]

@[simp]

Depends on / 依赖: ite_compl, ite_inter_self
-/
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' inter tᶜ = s' inter tᶜ := by
  rw [← ite_compl]; rw [ite_inter_self]

@[simp]
/--
theorem `ite_sdiff_self` / 定理 `ite_sdiff_self`

English:
theorem ite_sdiff_self
  given: (t s s' : Set α)
  statement: t.ite s s' \ t = s' \ t
  proof: ite_inter_compl_self t s s'

@[deprecated (since := "2026-06-03")] alias ite_diff_self := ite_sdiff_self

@[simp]

中文:
定理 ite_sdiff_self
  条件: (t s s' : 集合 α)
  结论: t.ite s s' \ t = s' \ t
  证明: ite_inter_compl_self t s s'

@[deprecated (since := "2026-06-03")] alias ite_diff_self := ite_sdiff_self

@[simp]

Depends on / 依赖: ite_inter_compl_self
-/
theorem ite_sdiff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[deprecated (since := "2026-06-03")] alias ite_diff_self := ite_sdiff_self

@[simp]
/--
theorem `ite_same` / 定理 `ite_same`

English:
theorem ite_same
  given: (t s : Set α)
  statement: t.ite s s = s
  proof: inter_union_sdiff _ _

@[simp]

中文:
定理 ite_same
  条件: (t s : 集合 α)
  结论: t.ite s s = s
  证明: inter_union_sdiff _ _

@[simp]

Depends on / 依赖: inter_union_sdiff
-/
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_sdiff _ _

@[simp]
/--
theorem `ite_left` / 定理 `ite_left`

English:
theorem ite_left
  given: (s t : Set α)
  statement: s.ite s t = s union t
  proof: by simp [Set.ite]

@[simp]

中文:
定理 ite_left
  条件: (s t : 集合 α)
  结论: s.ite s t = s union t
  证明: by simp [Set.ite]

@[simp]

Depends on / 依赖: Set.ite
-/
theorem ite_left (s t : Set α) : s.ite s t = s union t := by simp [Set.ite]

@[simp]
/--
theorem `ite_right` / 定理 `ite_right`

English:
theorem ite_right
  given: (s t : Set α)
  statement: s.ite t s = t inter s
  proof: by simp [Set.ite]

@[simp]

中文:
定理 ite_right
  条件: (s t : 集合 α)
  结论: s.ite t s = t inter s
  证明: by simp [Set.ite]

@[simp]

Depends on / 依赖: Set.ite
-/
theorem ite_right (s t : Set α) : s.ite t s = t inter s := by simp [Set.ite]

@[simp]
/--
theorem `ite_empty` / 定理 `ite_empty`

English:
theorem ite_empty
  given: (s s' : Set α)
  statement: Set.ite ∅ s s' = s'
  proof: by simp [Set.ite]

@[simp]

中文:
定理 ite_empty
  条件: (s s' : 集合 α)
  结论: 集合.ite ∅ s s' = s'
  证明: by simp [Set.ite]

@[simp]

Depends on / 依赖: Set.ite
-/
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]

@[simp]
/--
theorem `ite_univ` / 定理 `ite_univ`

English:
theorem ite_univ
  given: (s s' : Set α)
  statement: Set.ite univ s s' = s
  proof: by simp [Set.ite]

@[simp]

中文:
定理 ite_univ
  条件: (s s' : 集合 α)
  结论: 集合.ite univ s s' = s
  证明: by simp [Set.ite]

@[simp]

Depends on / 依赖: Set.ite
-/
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]

@[simp]
/--
theorem `ite_empty_left` / 定理 `ite_empty_left`

English:
theorem ite_empty_left
  given: (t s : Set α)
  statement: t.ite ∅ s = s \ t
  proof: by simp [Set.ite]

@[simp]

中文:
定理 ite_empty_left
  条件: (t s : 集合 α)
  结论: t.ite ∅ s = s \ t
  证明: by simp [Set.ite]

@[simp]

Depends on / 依赖: Set.ite
-/
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]

@[simp]
/--
theorem `ite_empty_right` / 定理 `ite_empty_right`

English:
theorem ite_empty_right
  given: (t s : Set α)
  statement: t.ite s ∅ = s inter t
  proof: by simp [Set.ite]

中文:
定理 ite_empty_right
  条件: (t s : 集合 α)
  结论: t.ite s ∅ = s inter t
  证明: by simp [Set.ite]

Depends on / 依赖: Set.ite
-/
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s inter t := by simp [Set.ite]

/--
theorem `ite_mono` / 定理 `ite_mono`

English:
theorem ite_mono
  given: (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ subseteq s₂) (h' : s₁' subseteq s₂')
  proof: union_subset_union (inter_subset_inter_left _ h) (sdiff_subset_sdiff_left h')

中文:
定理 ite_mono
  条件: (t : 集合 α) {s₁ s₁' s₂ s₂' : 集合 α} (h : s₁ subseteq s₂) (h' : s₁' subseteq s₂')
  证明: union_subset_union (inter_subset_inter_left _ h) (sdiff_subset_sdiff_left h')

Depends on / 依赖: inter_subset_inter_left, sdiff_subset_sdiff_left, union_subset_union
-/
theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ subseteq s₂) (h' : s₁' subseteq s₂') :
    t.ite s₁ s₁' subseteq t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (sdiff_subset_sdiff_left h')

/--
theorem `ite_subset_union` / 定理 `ite_subset_union`

English:
theorem ite_subset_union
  given: (t s s' : Set α)
  statement: t.ite s s' subseteq s union s'
  proof: union_subset_union inter_subset_left sdiff_subset

中文:
定理 ite_subset_union
  条件: (t s s' : 集合 α)
  结论: t.ite s s' subseteq s union s'
  证明: union_subset_union inter_subset_left sdiff_subset

Depends on / 依赖: inter_subset_left, sdiff_subset, union_subset_union
-/
theorem ite_subset_union (t s s' : Set α) : t.ite s s' subseteq s union s' :=
  union_subset_union inter_subset_left sdiff_subset

/--
theorem `inter_subset_ite` / 定理 `inter_subset_ite`

English:
theorem inter_subset_ite
  given: (t s s' : Set α)
  statement: s inter s' subseteq t.ite s s'
  proof: ite_same t (s inter s') ▸ ite_mono _ inter_subset_left inter_subset_right

中文:
定理 inter_subset_ite
  条件: (t s s' : 集合 α)
  结论: s inter s' subseteq t.ite s s'
  证明: ite_same t (s inter s') ▸ ite_mono _ inter_subset_left inter_subset_right

Depends on / 依赖: inter_subset_left, inter_subset_right, ite_mono, ite_same
-/
theorem inter_subset_ite (t s s' : Set α) : s inter s' subseteq t.ite s s' :=
  ite_same t (s inter s') ▸ ite_mono _ inter_subset_left inter_subset_right

/--
theorem `ite_inter_inter` / 定理 `ite_inter_inter`

English:
theorem ite_inter_inter
  given: (t s₁ s₂ s₁' s₂' : Set α)
  proof: by
  ext x
  unfold Set.ite
  push _ in _
  tauto

中文:
定理 ite_inter_inter
  条件: (t s₁ s₂ s₁' s₂' : 集合 α)
  证明: by
  ext x
  unfold Set.ite
  push _ in _
  tauto

Depends on / 依赖: Set.ite
-/
theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ inter s₂) (s₁' inter s₂') = t.ite s₁ s₁' inter t.ite s₂ s₂' := by
  ext x
  unfold Set.ite
  push _ in _
  tauto

/--
theorem `ite_inter` / 定理 `ite_inter`

English:
theorem ite_inter
  given: (t s₁ s₂ s : Set α)
  statement: t.ite (s₁ inter s) (s₂ inter s) = t.ite s₁ s₂ inter s
  proof: by
  rw [ite_inter_inter]; rw [ite_same]

中文:
定理 ite_inter
  条件: (t s₁ s₂ s : 集合 α)
  结论: t.ite (s₁ inter s) (s₂ inter s) = t.ite s₁ s₂ inter s
  证明: by
  rw [ite_inter_inter]; rw [ite_same]

Depends on / 依赖: ite_inter_inter, ite_same
-/
theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ inter s) (s₂ inter s) = t.ite s₁ s₂ inter s := by
  rw [ite_inter_inter]; rw [ite_same]

/--
theorem `ite_inter_of_inter_eq` / 定理 `ite_inter_of_inter_eq`

English:
theorem ite_inter_of_inter_eq
  given: (t : Set α) {s₁ s₂ s : Set α} (h : s₁ inter s = s₂ inter s)
  proof: by rw [← ite_inter, ← h, ite_same]

中文:
定理 ite_inter_of_inter_eq
  条件: (t : 集合 α) {s₁ s₂ s : 集合 α} (h : s₁ inter s = s₂ inter s)
  证明: by rw [← ite_inter, ← h, ite_same]

Depends on / 依赖: ite_inter, ite_same
-/
theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ inter s = s₂ inter s) :
    t.ite s₁ s₂ inter s = s₁ inter s := by rw [← ite_inter, ← h, ite_same]

/--
theorem `subset_ite` / 定理 `subset_ite`

English:
theorem subset_ite
  given: {t s s' u : Set α}
  statement: u subseteq t.ite s s' ↔ u inter t subseteq s ∧ u \ t subseteq s'
  proof: by
  simp only [subset_def, ← forall_and]
  refine forall_congr' fun x => ?_
  by_cases hx : x in t <;> simp [*, Set.ite]

中文:
定理 subset_ite
  条件: {t s s' u : 集合 α}
  结论: u subseteq t.ite s s' ↔ u inter t subseteq s ∧ u \ t subseteq s'
  证明: by
  simp only [subset_def, ← forall_and]
  refine forall_congr' fun x => ?_
  by_cases hx : x in t <;> simp [*, Set.ite]

Depends on / 依赖: Set.ite, forall_and, forall_congr, subset_def
-/
theorem subset_ite {t s s' u : Set α} : u subseteq t.ite s s' ↔ u inter t subseteq s ∧ u \ t subseteq s' := by
  simp only [subset_def, ← forall_and]
  refine forall_congr' fun x => ?_
  by_cases hx : x in t <;> simp [*, Set.ite]

/--
theorem `ite_eq_of_subset_left` / 定理 `ite_eq_of_subset_left`

English:
theorem ite_eq_of_subset_left
  given: (t : Set α) {s₁ s₂ : Set α} (h : s₁ subseteq s₂)
  proof: by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_right_of_imp (@h x)]

中文:
定理 ite_eq_of_subset_left
  条件: (t : 集合 α) {s₁ s₂ : 集合 α} (h : s₁ subseteq s₂)
  证明: by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_right_of_imp (@h x)]

Depends on / 依赖: Set.ite, or_iff_right_of_imp
-/
theorem ite_eq_of_subset_left (t : Set α) {s₁ s₂ : Set α} (h : s₁ subseteq s₂) :
    t.ite s₁ s₂ = s₁ union (s₂ \ t) := by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_right_of_imp (@h x)]

/--
theorem `ite_eq_of_subset_right` / 定理 `ite_eq_of_subset_right`

English:
theorem ite_eq_of_subset_right
  given: (t : Set α) {s₁ s₂ : Set α} (h : s₂ subseteq s₁)
  proof: by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_left_of_imp (@h x)]

中文:
定理 ite_eq_of_subset_right
  条件: (t : 集合 α) {s₁ s₂ : 集合 α} (h : s₂ subseteq s₁)
  证明: by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_left_of_imp (@h x)]

Depends on / 依赖: Set.ite, or_iff_left_of_imp
-/
theorem ite_eq_of_subset_right (t : Set α) {s₁ s₂ : Set α} (h : s₂ subseteq s₁) :
    t.ite s₁ s₂ = (s₁ inter t) union s₂ := by
  ext x
  by_cases hx : x in t <;> simp [*, Set.ite, or_iff_left_of_imp (@h x)]

end Set
