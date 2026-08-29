/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Difference of finite sets

## Main declarations

* `Finset.instSDiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `Finset.instGeneralizedBooleanAlgebra`: Finsets almost have a Boolean algebra structure

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff (Finset α)
  body: ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le (Multiset.sub_le_self ..) s₁.2⟩⟩

@[simp]

中文:
实例 instSDiff
  签名: : SDiff (Finset α)
  定义体: ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le (Multiset.sub_le_self ..) s₁.2⟩⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.sub_le_self, nodup_of_le, sub_le_self
-/
instance instSDiff : SDiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le (Multiset.sub_le_self ..) s₁.2⟩⟩

@[simp]
/--
theorem `sdiff_val` / 定理 `sdiff_val`

English:
theorem sdiff_val
  given: (s₁ s₂ : Finset α)
  statement: (s₁ \ s₂).val = s₁.val - s₂.val
  proof: rfl

@[simp, grind =]

中文:
定理 sdiff_val
  条件: (s₁ s₂ : Finset α)
  结论: (s₁ \ s₂).val = s₁.val - s₂.val
  证明: rfl

@[simp, grind =]
-/
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl

@[simp, grind =]
/--
theorem `mem_sdiff` / 定理 `mem_sdiff`

English:
theorem mem_sdiff
  statement: a in s \ t ↔ a in s ∧ a ∉ t
  proof: mem_sub_of_nodup s.2

@[simp]

中文:
定理 mem_sdiff
  结论: a in s \ t ↔ a in s ∧ a ∉ t
  证明: mem_sub_of_nodup s.2

@[simp]

Depends on / 依赖: mem_sub_of_nodup
-/
theorem mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t :=
  mem_sub_of_nodup s.2

@[simp]
/--
theorem `inter_sdiff_self` / 定理 `inter_sdiff_self`

English:
theorem inter_sdiff_self
  given: (s₁ s₂ : Finset α)
  statement: s₁ inter (s₂ \ s₁) = ∅
  proof: by grind

中文:
定理 inter_sdiff_self
  条件: (s₁ s₂ : Finset α)
  结论: s₁ inter (s₂ \ s₁) = ∅
  证明: by grind
-/
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ inter (s₂ \ s₁) = ∅ := by grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GeneralizedBooleanAlgebra (Finset α)
  body: by grind
  inf_inf_sdiff := by grind

中文:
实例 :
  签名: Generalized布尔eanAlgebra (Finset α)
  定义体: by grind
  inf_inf_sdiff := by grind

Depends on / 依赖: inf_inf_sdiff
-/
instance : GeneralizedBooleanAlgebra (Finset α) where
  sup_inf_sdiff := by grind
  inf_inf_sdiff := by grind

/--
theorem `notMem_sdiff_of_mem_right` / 定理 `notMem_sdiff_of_mem_right`

English:
theorem notMem_sdiff_of_mem_right
  given: (h : a in t)
  statement: a ∉ s \ t
  proof: by grind

中文:
定理 notMem_sdiff_of_mem_right
  条件: (h : a in t)
  结论: a ∉ s \ t
  证明: by grind
-/
theorem notMem_sdiff_of_mem_right (h : a in t) : a ∉ s \ t := by grind

/--
theorem `notMem_sdiff_of_notMem_left` / 定理 `notMem_sdiff_of_notMem_left`

English:
theorem notMem_sdiff_of_notMem_left
  given: (h : a ∉ s)
  statement: a ∉ s \ t
  proof: by simp [h]

中文:
定理 notMem_sdiff_of_notMem_left
  条件: (h : a ∉ s)
  结论: a ∉ s \ t
  证明: by simp [h]
-/
theorem notMem_sdiff_of_notMem_left (h : a ∉ s) : a ∉ s \ t := by simp [h]

/--
theorem `union_sdiff_of_subset` / 定理 `union_sdiff_of_subset`

English:
theorem union_sdiff_of_subset
  given: (h : s subseteq t)
  statement: s union t \ s = t
  proof: by grind

中文:
定理 union_sdiff_of_subset
  条件: (h : s subseteq t)
  结论: s union t \ s = t
  证明: by grind
-/
theorem union_sdiff_of_subset (h : s subseteq t) : s union t \ s = t := by grind

/--
theorem `sdiff_union_of_subset` / 定理 `sdiff_union_of_subset`

English:
theorem sdiff_union_of_subset
  given: {s₁ s₂ : Finset α} (h : s₁ subseteq s₂)
  statement: s₂ \ s₁ union s₁ = s₂
  proof: by grind

中文:
定理 sdiff_union_of_subset
  条件: {s₁ s₂ : Finset α} (h : s₁ subseteq s₂)
  结论: s₂ \ s₁ union s₁ = s₂
  证明: by grind
-/
theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂ := by grind

/--
lemma `inter_sdiff_assoc` / 引理 `inter_sdiff_assoc`

English:
lemma inter_sdiff_assoc
  given: (s t u : Finset α)
  statement: (s inter t) \ u = s inter (t \ u)
  proof: inf_sdiff_assoc ..

中文:
引理 inter_sdiff_assoc
  条件: (s t u : Finset α)
  结论: (s inter t) \ u = s inter (t \ u)
  证明: inf_sdiff_assoc ..

Depends on / 依赖: inf_sdiff_assoc
-/
lemma inter_sdiff_assoc (s t u : Finset α) : (s inter t) \ u = s inter (t \ u) := inf_sdiff_assoc ..

/--
lemma `sdiff_inter_right_comm` / 引理 `sdiff_inter_right_comm`

English:
lemma sdiff_inter_right_comm
  given: (s t u : Finset α)
  statement: s \ t inter u = (s inter u) \ t
  proof: sdiff_inf_right_comm ..

中文:
引理 sdiff_inter_right_comm
  条件: (s t u : Finset α)
  结论: s \ t inter u = (s inter u) \ t
  证明: sdiff_inf_right_comm ..

Depends on / 依赖: sdiff_inf_right_comm
-/
lemma sdiff_inter_right_comm (s t u : Finset α) : s \ t inter u = (s inter u) \ t := sdiff_inf_right_comm ..

/--
lemma `inter_sdiff_left_comm` / 引理 `inter_sdiff_left_comm`

English:
lemma inter_sdiff_left_comm
  given: (s t u : Finset α)
  statement: s inter (t \ u) = t inter (s \ u)
  proof: inf_sdiff_left_comm ..

@[simp]

中文:
引理 inter_sdiff_left_comm
  条件: (s t u : Finset α)
  结论: s inter (t \ u) = t inter (s \ u)
  证明: inf_sdiff_left_comm ..

@[simp]

Depends on / 依赖: inf_sdiff_left_comm
-/
lemma inter_sdiff_left_comm (s t u : Finset α) : s inter (t \ u) = t inter (s \ u) := inf_sdiff_left_comm ..

@[simp]
/--
theorem `sdiff_inter_self` / 定理 `sdiff_inter_self`

English:
theorem sdiff_inter_self
  given: (s₁ s₂ : Finset α)
  statement: s₂ \ s₁ inter s₁ = ∅
  proof: inf_sdiff_self_left

中文:
定理 sdiff_inter_self
  条件: (s₁ s₂ : Finset α)
  结论: s₂ \ s₁ inter s₁ = ∅
  证明: inf_sdiff_self_left

Depends on / 依赖: inf_sdiff_self_left
-/
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ inter s₁ = ∅ :=
  inf_sdiff_self_left

/--
theorem `sdiff_self` / 定理 `sdiff_self`

English:
theorem sdiff_self
  given: (s₁ : Finset α)
  statement: s₁ \ s₁ = ∅
  proof: _root_.sdiff_self

中文:
定理 sdiff_self
  条件: (s₁ : Finset α)
  结论: s₁ \ s₁ = ∅
  证明: _root_.sdiff_self
-/
protected theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  _root_.sdiff_self

/--
theorem `sdiff_inter_distrib_right` / 定理 `sdiff_inter_distrib_right`

English:
theorem sdiff_inter_distrib_right
  given: (s t u : Finset α)
  statement: s \ (t inter u) = s \ t union s \ u
  proof: sdiff_inf

@[simp]

中文:
定理 sdiff_inter_distrib_right
  条件: (s t u : Finset α)
  结论: s \ (t inter u) = s \ t union s \ u
  证明: sdiff_inf

@[simp]

Depends on / 依赖: sdiff_inf
-/
theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t inter u) = s \ t union s \ u :=
  sdiff_inf

@[simp]
/--
theorem `sdiff_inter_self_left` / 定理 `sdiff_inter_self_left`

English:
theorem sdiff_inter_self_left
  given: (s t : Finset α)
  statement: s \ (s inter t) = s \ t
  proof: sdiff_inf_self_left _ _

@[simp]

中文:
定理 sdiff_inter_self_left
  条件: (s t : Finset α)
  结论: s \ (s inter t) = s \ t
  证明: sdiff_inf_self_left _ _

@[simp]

Depends on / 依赖: Nat.binaryRec, binaryRec, sdiff_inf_self_left
-/
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s inter t) = s \ t :=
  sdiff_inf_self_left _ _

@[simp]
/--
theorem `sdiff_inter_self_right` / 定理 `sdiff_inter_self_right`

English:
theorem sdiff_inter_self_right
  given: (s t : Finset α)
  statement: s \ (t inter s) = s \ t
  proof: sdiff_inf_self_right _ _

@[simp]

中文:
定理 sdiff_inter_self_right
  条件: (s t : Finset α)
  结论: s \ (t inter s) = s \ t
  证明: sdiff_inf_self_right _ _

@[simp]

Depends on / 依赖: sdiff_inf_self_right
-/
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t inter s) = s \ t :=
  sdiff_inf_self_right _ _

@[simp]
/--
theorem `sdiff_empty` / 定理 `sdiff_empty`

English:
theorem sdiff_empty
  statement: s \ ∅ = s
  proof: sdiff_bot

@[mono, gcongr]

中文:
定理 sdiff_empty
  结论: s \ ∅ = s
  证明: sdiff_bot

@[mono, gcongr]

Depends on / 依赖: sdiff_bot
-/
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot

@[mono, gcongr]
/--
theorem `sdiff_subset_sdiff` / 定理 `sdiff_subset_sdiff`

English:
theorem sdiff_subset_sdiff
  given: (hst : s subseteq t) (hvu : v subseteq u)
  statement: s \ u subseteq t \ v
  proof: by grind

中文:
定理 sdiff_subset_sdiff
  条件: (hst : s subseteq t) (hvu : v subseteq u)
  结论: s \ u subseteq t \ v
  证明: by grind
-/
theorem sdiff_subset_sdiff (hst : s subseteq t) (hvu : v subseteq u) : s \ u subseteq t \ v := by grind

variable (u) in
/--
lemma `sdiff_subset_sdiff_left` / 引理 `sdiff_subset_sdiff_left`

English:
lemma sdiff_subset_sdiff_left
  given: (h : s subseteq t)
  statement: s \ u subseteq t \ u
  proof: by gcongr

中文:
引理 sdiff_subset_sdiff_left
  条件: (h : s subseteq t)
  结论: s \ u subseteq t \ u
  证明: by gcongr
-/
lemma sdiff_subset_sdiff_left (h : s subseteq t) : s \ u subseteq t \ u := by gcongr

variable (u) in
/--
lemma `sdiff_subset_sdiff_right` / 引理 `sdiff_subset_sdiff_right`

English:
lemma sdiff_subset_sdiff_right
  given: (h : s subseteq t)
  statement: u \ t subseteq u \ s
  proof: by gcongr

中文:
引理 sdiff_subset_sdiff_right
  条件: (h : s subseteq t)
  结论: u \ t subseteq u \ s
  证明: by gcongr
-/
lemma sdiff_subset_sdiff_right (h : s subseteq t) : u \ t subseteq u \ s := by gcongr

/--
theorem `sdiff_subset_sdiff_iff_subset` / 定理 `sdiff_subset_sdiff_iff_subset`

English:
theorem sdiff_subset_sdiff_iff_subset
  given: {r : Finset α} (hs : s subseteq r) (ht : t subseteq r)
  proof: sdiff_le_sdiff_iff_le hs ht

@[simp, grind =, norm_cast]

中文:
定理 sdiff_subset_sdiff_iff_subset
  条件: {r : Finset α} (hs : s subseteq r) (ht : t subseteq r)
  证明: sdiff_le_sdiff_iff_le hs ht

@[simp, grind =, norm_cast]

Depends on / 依赖: sdiff_le_sdiff_iff_le
-/
theorem sdiff_subset_sdiff_iff_subset {r : Finset α} (hs : s subseteq r) (ht : t subseteq r) :
    r \ s subseteq r \ t ↔ t subseteq s :=
  sdiff_le_sdiff_iff_le hs ht

@[simp, grind =, norm_cast]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: (s₁ s₂ : Finset α)
  statement: ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α)
  proof: Set.ext fun _ => mem_sdiff

@[simp]

中文:
定理 coe_sdiff
  条件: (s₁ s₂ : Finset α)
  结论: ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α)
  证明: Set.ext fun _ => mem_sdiff

@[simp]

Depends on / 依赖: Set.ext, mem_sdiff
-/
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff

@[simp]
/--
theorem `union_sdiff_self_eq_union` / 定理 `union_sdiff_self_eq_union`

English:
theorem union_sdiff_self_eq_union
  statement: s union t \ s = s union t
  proof: sup_sdiff_self_right _ _

@[simp]

中文:
定理 union_sdiff_self_eq_union
  结论: s union t \ s = s union t
  证明: sup_sdiff_self_right _ _

@[simp]

Depends on / 依赖: sup_sdiff_self_right
-/
theorem union_sdiff_self_eq_union : s union t \ s = s union t :=
  sup_sdiff_self_right _ _

@[simp]
/--
theorem `sdiff_union_self_eq_union` / 定理 `sdiff_union_self_eq_union`

English:
theorem sdiff_union_self_eq_union
  statement: s \ t union t = s union t
  proof: sup_sdiff_self_left _ _

中文:
定理 sdiff_union_self_eq_union
  结论: s \ t union t = s union t
  证明: sup_sdiff_self_left _ _

Depends on / 依赖: sup_sdiff_self_left
-/
theorem sdiff_union_self_eq_union : s \ t union t = s union t :=
  sup_sdiff_self_left _ _

/--
theorem `union_sdiff_left` / 定理 `union_sdiff_left`

English:
theorem union_sdiff_left
  given: (s t : Finset α)
  statement: (s union t) \ s = t \ s
  proof: sup_sdiff_left_self

中文:
定理 union_sdiff_left
  条件: (s t : Finset α)
  结论: (s union t) \ s = t \ s
  证明: sup_sdiff_left_self

Depends on / 依赖: sup_sdiff_left_self
-/
theorem union_sdiff_left (s t : Finset α) : (s union t) \ s = t \ s :=
  sup_sdiff_left_self

/--
theorem `union_sdiff_right` / 定理 `union_sdiff_right`

English:
theorem union_sdiff_right
  given: (s t : Finset α)
  statement: (s union t) \ t = s \ t
  proof: sup_sdiff_right_self

中文:
定理 union_sdiff_right
  条件: (s t : Finset α)
  结论: (s union t) \ t = s \ t
  证明: sup_sdiff_right_self

Depends on / 依赖: sup_sdiff_right_self
-/
theorem union_sdiff_right (s t : Finset α) : (s union t) \ t = s \ t :=
  sup_sdiff_right_self

/--
theorem `union_sdiff_cancel_left` / 定理 `union_sdiff_cancel_left`

English:
theorem union_sdiff_cancel_left
  given: (h : Disjoint s t)
  statement: (s union t) \ s = t
  proof: h.sup_sdiff_cancel_left

中文:
定理 union_sdiff_cancel_left
  条件: (h : Disjoint s t)
  结论: (s union t) \ s = t
  证明: h.sup_sdiff_cancel_left

Depends on / 依赖: h.sup_sdiff_cancel_left, sup_sdiff_cancel_left
-/
theorem union_sdiff_cancel_left (h : Disjoint s t) : (s union t) \ s = t :=
  h.sup_sdiff_cancel_left

/--
theorem `union_sdiff_cancel_right` / 定理 `union_sdiff_cancel_right`

English:
theorem union_sdiff_cancel_right
  given: (h : Disjoint s t)
  statement: (s union t) \ t = s
  proof: h.sup_sdiff_cancel_right

中文:
定理 union_sdiff_cancel_right
  条件: (h : Disjoint s t)
  结论: (s union t) \ t = s
  证明: h.sup_sdiff_cancel_right

Depends on / 依赖: h.sup_sdiff_cancel_right, sup_sdiff_cancel_right
-/
theorem union_sdiff_cancel_right (h : Disjoint s t) : (s union t) \ t = s :=
  h.sup_sdiff_cancel_right

/--
lemma `disjoint_injOn_union_left` / 引理 `disjoint_injOn_union_left`

English:
lemma disjoint_injOn_union_left
  given: (s : Finset α)
  statement: {t | Disjoint s t}.InjOn (· union s)
  proof: by
  grind [Set.InjOn, union_sdiff_cancel_right]

中文:
引理 disjoint_injOn_union_left
  条件: (s : Finset α)
  结论: {t | Disjoint s t}.InjOn (· union s)
  证明: by
  grind [Set.InjOn, union_sdiff_cancel_right]

Depends on / 依赖: Set.InjOn, union_sdiff_cancel_right
-/
lemma disjoint_injOn_union_left (s : Finset α) : {t | Disjoint s t}.InjOn (· union s) := by
  grind [Set.InjOn, union_sdiff_cancel_right]

/--
lemma `superset_injOn_sdiff` / 引理 `superset_injOn_sdiff`

English:
lemma superset_injOn_sdiff
  given: (s : Finset α)
  statement: {t | s subseteq t}.InjOn (· \ s)
  proof: by
  grind [Set.InjOn, sdiff_union_of_subset]

中文:
引理 superset_injOn_sdiff
  条件: (s : Finset α)
  结论: {t | s subseteq t}.InjOn (· \ s)
  证明: by
  grind [Set.InjOn, sdiff_union_of_subset]

Depends on / 依赖: Set.InjOn, sdiff_union_of_subset
-/
lemma superset_injOn_sdiff (s : Finset α) : {t | s subseteq t}.InjOn (· \ s) := by
  grind [Set.InjOn, sdiff_union_of_subset]

/--
theorem `union_sdiff_symm` / 定理 `union_sdiff_symm`

English:
theorem union_sdiff_symm
  statement: s union t \ s = t union s \ t
  proof: by simp [union_comm]

中文:
定理 union_sdiff_symm
  结论: s union t \ s = t union s \ t
  证明: by simp [union_comm]

Depends on / 依赖: union_comm
-/
theorem union_sdiff_symm : s union t \ s = t union s \ t := by simp [union_comm]

/--
theorem `sdiff_union_inter` / 定理 `sdiff_union_inter`

English:
theorem sdiff_union_inter
  given: (s t : Finset α)
  statement: s \ t union s inter t = s
  proof: sup_sdiff_inf _ _

中文:
定理 sdiff_union_inter
  条件: (s t : Finset α)
  结论: s \ t union s inter t = s
  证明: sup_sdiff_inf _ _

Depends on / 依赖: sup_sdiff_inf
-/
theorem sdiff_union_inter (s t : Finset α) : s \ t union s inter t = s :=
  sup_sdiff_inf _ _

/--
theorem `sdiff_idem` / 定理 `sdiff_idem`

English:
theorem sdiff_idem
  given: (s t : Finset α)
  statement: (s \ t) \ t = s \ t
  proof: _root_.sdiff_idem

中文:
定理 sdiff_idem
  条件: (s t : Finset α)
  结论: (s \ t) \ t = s \ t
  证明: _root_.sdiff_idem

Depends on / 依赖: _root_, _root_.sdiff_idem, sdiff_idem
-/
theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  _root_.sdiff_idem

/--
theorem `subset_sdiff` / 定理 `subset_sdiff`

English:
theorem subset_sdiff
  statement: s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
  proof: le_sdiff

@[simp]

中文:
定理 subset_sdiff
  结论: s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u
  证明: le_sdiff

@[simp]

Depends on / 依赖: le_sdiff
-/
theorem subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjoint s u :=
  le_sdiff

@[simp]
/--
theorem `sdiff_eq_empty_iff_subset` / 定理 `sdiff_eq_empty_iff_subset`

English:
theorem sdiff_eq_empty_iff_subset
  statement: s \ t = ∅ ↔ s subseteq t
  proof: sdiff_eq_bot_iff

@[grind =]

中文:
定理 sdiff_eq_empty_iff_subset
  结论: s \ t = ∅ ↔ s subseteq t
  证明: sdiff_eq_bot_iff

@[grind =]

Depends on / 依赖: sdiff_eq_bot_iff
-/
theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s subseteq t :=
  sdiff_eq_bot_iff

@[grind =]
/--
theorem `sdiff_nonempty` / 定理 `sdiff_nonempty`

English:
theorem sdiff_nonempty
  statement: (s \ t).Nonempty ↔ ¬s subseteq t
  proof: nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp]

中文:
定理 sdiff_nonempty
  结论: (s \ t).Nonempty ↔ ¬s subseteq t
  证明: nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp]

Depends on / 依赖: nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans, sdiff_eq_empty_iff_subset, sdiff_eq_empty_iff_subset.not
-/
theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s subseteq t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp]
/--
theorem `empty_sdiff` / 定理 `empty_sdiff`

English:
theorem empty_sdiff
  given: (s : Finset α)
  statement: ∅ \ s = ∅
  proof: bot_sdiff

中文:
定理 empty_sdiff
  条件: (s : Finset α)
  结论: ∅ \ s = ∅
  证明: bot_sdiff

Depends on / 依赖: bot_sdiff
-/
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff

/--
theorem `insert_sdiff_of_notMem` / 定理 `insert_sdiff_of_notMem`

English:
theorem insert_sdiff_of_notMem
  given: (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t)
  proof: by grind

中文:
定理 insert_sdiff_of_notMem
  条件: (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t)
  证明: by grind
-/
theorem insert_sdiff_of_notMem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
    insert x s \ t = insert x (s \ t) := by grind

/--
theorem `insert_sdiff_of_mem` / 定理 `insert_sdiff_of_mem`

English:
theorem insert_sdiff_of_mem
  given: (s : Finset α) {x : α} (h : x in t)
  statement: insert x s \ t = s \ t
  proof: by grind

中文:
定理 insert_sdiff_of_mem
  条件: (s : Finset α) {x : α} (h : x in t)
  结论: insert x s \ t = s \ t
  证明: by grind
-/
theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x in t) : insert x s \ t = s \ t := by grind

/--
lemma `insert_sdiff_self_of_mem` / 引理 `insert_sdiff_self_of_mem`

English:
lemma insert_sdiff_self_of_mem
  given: (ha : a in s)
  statement: insert a (s \ {a}) = s
  proof: by grind

中文:
引理 insert_sdiff_self_of_mem
  条件: (ha : a in s)
  结论: insert a (s \ {a}) = s
  证明: by grind
-/
@[simp] lemma insert_sdiff_self_of_mem (ha : a in s) : insert a (s \ {a}) = s := by grind

/--
lemma `insert_sdiff_cancel` / 引理 `insert_sdiff_cancel`

English:
lemma insert_sdiff_cancel
  given: (ha : a ∉ s)
  statement: insert a s \ s = {a}
  proof: by grind

@[simp]

中文:
引理 insert_sdiff_cancel
  条件: (ha : a ∉ s)
  结论: insert a s \ s = {a}
  证明: by grind

@[simp]
-/
@[simp] lemma insert_sdiff_cancel (ha : a ∉ s) : insert a s \ s = {a} := by grind

@[simp]
/--
theorem `insert_sdiff_insert` / 定理 `insert_sdiff_insert`

English:
theorem insert_sdiff_insert
  given: (s t : Finset α) (x : α)
  statement: insert x s \ insert x t = s \ insert x t
  proof: insert_sdiff_of_mem _ (mem_insert_self _ _)

中文:
定理 insert_sdiff_insert
  条件: (s t : Finset α) (x : α)
  结论: insert x s \ insert x t = s \ insert x t
  证明: insert_sdiff_of_mem _ (mem_insert_self _ _)

Depends on / 依赖: insert_sdiff_of_mem, mem_insert_self
-/
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)

/--
lemma `insert_sdiff_insert'` / 引理 `insert_sdiff_insert'`

English:
lemma insert_sdiff_insert'
  given: (hab : a != b) (ha : a ∉ s)
  statement: insert a s \ insert b s = {a}
  proof: by
  ext; aesop

中文:
引理 insert_sdiff_insert'
  条件: (hab : a != b) (ha : a ∉ s)
  结论: insert a s \ insert b s = {a}
  证明: by
  ext; aesop
-/
lemma insert_sdiff_insert' (hab : a != b) (ha : a ∉ s) : insert a s \ insert b s = {a} := by
  ext; aesop

/--
lemma `cons_sdiff_cons` / 引理 `cons_sdiff_cons`

English:
lemma cons_sdiff_cons
  given: (hab : a != b) (ha hb)
  statement: s.cons a ha \ s.cons b hb = {a}
  proof: by grind

中文:
引理 cons_sdiff_cons
  条件: (hab : a != b) (ha hb)
  结论: s.cons a ha \ s.cons b hb = {a}
  证明: by grind
-/
lemma cons_sdiff_cons (hab : a != b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by grind

/--
theorem `sdiff_insert_of_notMem` / 定理 `sdiff_insert_of_notMem`

English:
theorem sdiff_insert_of_notMem
  given: {x : α} (h : x ∉ s) (t : Finset α)
  statement: s \ insert x t = s \ t
  proof: by
  grind

中文:
定理 sdiff_insert_of_notMem
  条件: {x : α} (h : x ∉ s) (t : Finset α)
  结论: s \ insert x t = s \ t
  证明: by
  grind
-/
theorem sdiff_insert_of_notMem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  grind

/--
theorem `sdiff_subset` / 定理 `sdiff_subset`

English:
theorem sdiff_subset
  given: {s t : Finset α}
  statement: s \ t subseteq s
  proof: by simp

中文:
定理 sdiff_subset
  条件: {s t : Finset α}
  结论: s \ t subseteq s
  证明: by simp
-/
theorem sdiff_subset {s t : Finset α} : s \ t subseteq s := by simp

/--
theorem `sdiff_ssubset` / 定理 `sdiff_ssubset`

English:
theorem sdiff_ssubset
  given: (h : t subseteq s) (ht : t.Nonempty)
  statement: s \ t ⊂ s
  proof: by grind

中文:
定理 sdiff_ssubset
  条件: (h : t subseteq s) (ht : t.Nonempty)
  结论: s \ t ⊂ s
  证明: by grind
-/
theorem sdiff_ssubset (h : t subseteq s) (ht : t.Nonempty) : s \ t ⊂ s := by grind

/--
theorem `union_sdiff_distrib` / 定理 `union_sdiff_distrib`

English:
theorem union_sdiff_distrib
  given: (s₁ s₂ t : Finset α)
  statement: (s₁ union s₂) \ t = s₁ \ t union s₂ \ t
  proof: sup_sdiff

中文:
定理 union_sdiff_distrib
  条件: (s₁ s₂ t : Finset α)
  结论: (s₁ union s₂) \ t = s₁ \ t union s₂ \ t
  证明: sup_sdiff

Depends on / 依赖: sup_sdiff
-/
theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ union s₂) \ t = s₁ \ t union s₂ \ t :=
  sup_sdiff

/--
theorem `sdiff_union_distrib` / 定理 `sdiff_union_distrib`

English:
theorem sdiff_union_distrib
  given: (s t₁ t₂ : Finset α)
  statement: s \ (t₁ union t₂) = s \ t₁ inter (s \ t₂)
  proof: sdiff_sup

中文:
定理 sdiff_union_distrib
  条件: (s t₁ t₂ : Finset α)
  结论: s \ (t₁ union t₂) = s \ t₁ inter (s \ t₂)
  证明: sdiff_sup

Depends on / 依赖: sdiff_sup
-/
theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ union t₂) = s \ t₁ inter (s \ t₂) :=
  sdiff_sup

/--
theorem `union_sdiff_self` / 定理 `union_sdiff_self`

English:
theorem union_sdiff_self
  given: (s t : Finset α)
  statement: (s union t) \ t = s \ t
  proof: sup_sdiff_right_self

中文:
定理 union_sdiff_self
  条件: (s t : Finset α)
  结论: (s union t) \ t = s \ t
  证明: sup_sdiff_right_self

Depends on / 依赖: sup_sdiff_right_self
-/
theorem union_sdiff_self (s t : Finset α) : (s union t) \ t = s \ t :=
  sup_sdiff_right_self

/--
theorem `Nontrivial.sdiff_singleton_nonempty` / 定理 `Nontrivial.sdiff_singleton_nonempty`

English:
theorem Nontrivial.sdiff_singleton_nonempty
  given: {c : α} {s : Finset α} (hS : s.Nontrivial)
  proof: by grind

中文:
定理 Nontrivial.sdiff_singleton_nonempty
  条件: {c : α} {s : Finset α} (hS : s.Nontrivial)
  证明: by grind
-/
theorem Nontrivial.sdiff_singleton_nonempty {c : α} {s : Finset α} (hS : s.Nontrivial) :
    (s \ {c}).Nonempty := by grind

/--
theorem `sdiff_sdiff_left'` / 定理 `sdiff_sdiff_left'`

English:
theorem sdiff_sdiff_left'
  given: (s t u : Finset α)
  statement: (s \ t) \ u = s \ t inter (s \ u)
  proof: _root_.sdiff_sdiff_left'

中文:
定理 sdiff_sdiff_left'
  条件: (s t u : Finset α)
  结论: (s \ t) \ u = s \ t inter (s \ u)
  证明: _root_.sdiff_sdiff_left'

Depends on / 依赖: _root_, _root_.sdiff_sdiff_left, sdiff_sdiff_left
-/
theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t inter (s \ u) :=
  _root_.sdiff_sdiff_left'

/--
theorem `sdiff_union_sdiff_cancel` / 定理 `sdiff_union_sdiff_cancel`

English:
theorem sdiff_union_sdiff_cancel
  given: (hts : t subseteq s) (hut : u subseteq t)
  statement: s \ t union t \ u = s \ u
  proof: sdiff_sup_sdiff_cancel hts hut

中文:
定理 sdiff_union_sdiff_cancel
  条件: (hts : t subseteq s) (hut : u subseteq t)
  结论: s \ t union t \ u = s \ u
  证明: sdiff_sup_sdiff_cancel hts hut

Depends on / 依赖: sdiff_sup_sdiff_cancel
-/
theorem sdiff_union_sdiff_cancel (hts : t subseteq s) (hut : u subseteq t) : s \ t union t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

/--
theorem `sdiff_sdiff_eq_sdiff_union` / 定理 `sdiff_sdiff_eq_sdiff_union`

English:
theorem sdiff_sdiff_eq_sdiff_union
  given: (h : u subseteq s)
  statement: s \ (t \ u) = s \ t union u
  proof: sdiff_sdiff_eq_sdiff_sup h

中文:
定理 sdiff_sdiff_eq_sdiff_union
  条件: (h : u subseteq s)
  结论: s \ (t \ u) = s \ t union u
  证明: sdiff_sdiff_eq_sdiff_sup h

Depends on / 依赖: sdiff_sdiff_eq_sdiff_sup
-/
theorem sdiff_sdiff_eq_sdiff_union (h : u subseteq s) : s \ (t \ u) = s \ t union u :=
  sdiff_sdiff_eq_sdiff_sup h

/--
theorem `sdiff_sdiff_self_left` / 定理 `sdiff_sdiff_self_left`

English:
theorem sdiff_sdiff_self_left
  given: (s t : Finset α)
  statement: s \ (s \ t) = s inter t
  proof: sdiff_sdiff_right_self

中文:
定理 sdiff_sdiff_self_left
  条件: (s t : Finset α)
  结论: s \ (s \ t) = s inter t
  证明: sdiff_sdiff_right_self

Depends on / 依赖: sdiff_sdiff_right_self
-/
theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s inter t :=
  sdiff_sdiff_right_self

/--
theorem `sdiff_sdiff_eq_self` / 定理 `sdiff_sdiff_eq_self`

English:
theorem sdiff_sdiff_eq_self
  given: (h : t subseteq s)
  statement: s \ (s \ t) = t
  proof: _root_.sdiff_sdiff_eq_self h

中文:
定理 sdiff_sdiff_eq_self
  条件: (h : t subseteq s)
  结论: s \ (s \ t) = t
  证明: _root_.sdiff_sdiff_eq_self h

Depends on / 依赖: _root_, _root_.sdiff_sdiff_eq_self, sdiff_sdiff_eq_self
-/
theorem sdiff_sdiff_eq_self (h : t subseteq s) : s \ (s \ t) = t :=
  _root_.sdiff_sdiff_eq_self h

/--
theorem `sdiff_eq_sdiff_iff_inter_eq_inter` / 定理 `sdiff_eq_sdiff_iff_inter_eq_inter`

English:
theorem sdiff_eq_sdiff_iff_inter_eq_inter
  given: {s t₁ t₂ : Finset α}
  proof: sdiff_eq_sdiff_iff_inf_eq_inf

中文:
定理 sdiff_eq_sdiff_iff_inter_eq_inter
  条件: {s t₁ t₂ : Finset α}
  证明: sdiff_eq_sdiff_iff_inf_eq_inf

Depends on / 依赖: sdiff_eq_sdiff_iff_inf_eq_inf
-/
theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} :
    s \ t₁ = s \ t₂ ↔ s inter t₁ = s inter t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf

/--
theorem `union_eq_sdiff_union_sdiff_union_inter` / 定理 `union_eq_sdiff_union_sdiff_union_inter`

English:
theorem union_eq_sdiff_union_sdiff_union_inter
  given: (s t : Finset α)
  statement: s union t = s \ t union t \ s union s inter t
  proof: sup_eq_sdiff_sup_sdiff_sup_inf

中文:
定理 union_eq_sdiff_union_sdiff_union_inter
  条件: (s t : Finset α)
  结论: s union t = s \ t union t \ s union s inter t
  证明: sup_eq_sdiff_sup_sdiff_sup_inf

Depends on / 依赖: sup_eq_sdiff_sup_sdiff_sup_inf
-/
theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s union t = s \ t union t \ s union s inter t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

/--
theorem `sdiff_eq_self_iff_disjoint` / 定理 `sdiff_eq_self_iff_disjoint`

English:
theorem sdiff_eq_self_iff_disjoint
  statement: s \ t = s ↔ Disjoint s t
  proof: sdiff_eq_left

中文:
定理 sdiff_eq_self_iff_disjoint
  结论: s \ t = s ↔ Disjoint s t
  证明: sdiff_eq_left

Depends on / 依赖: sdiff_eq_left
-/
theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_left

/--
theorem `sdiff_eq_self_of_disjoint` / 定理 `sdiff_eq_self_of_disjoint`

English:
theorem sdiff_eq_self_of_disjoint
  given: (h : Disjoint s t)
  statement: s \ t = s
  proof: sdiff_eq_self_iff_disjoint.2 h

中文:
定理 sdiff_eq_self_of_disjoint
  条件: (h : Disjoint s t)
  结论: s \ t = s
  证明: sdiff_eq_self_iff_disjoint.2 h

Depends on / 依赖: sdiff_eq_self_iff_disjoint
-/
theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h

end Sdiff

end Finset
