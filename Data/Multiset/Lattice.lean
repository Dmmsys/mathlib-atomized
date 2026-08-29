/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Multiset.Fold

/-!
# Lattice operations on multisets

This file defines `Multiset.sup` and derives the dual `Multiset.inf` and their basic lemmas
via `to_dual`.
-/

@[expose] public section


namespace Multiset

variable {α : Type*}

-- `sup` can be defined with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
-- `inf` can be defined with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
@[to_dual /-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/]
/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: (s : Multiset α)
  body: s.fold (· ⊔ ·) ⊥

@[to_dual (attr := simp)]

中文:
定义 sup
  签名: (s : Multiset α)
  定义体: s.fold (· ⊔ ·) ⊥

@[to_dual (attr := simp)]

Depends on / 依赖: s.fold
-/
def sup (s : Multiset α) : α :=
  s.fold (· ⊔ ·) ⊥

@[to_dual (attr := simp)]
/--
theorem `sup_coe` / 定理 `sup_coe`

English:
theorem sup_coe
  given: (l : List α)
  statement: sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 sup_coe
  条件: (l : List α)
  结论: sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_zero` / 定理 `sup_zero`

English:
theorem sup_zero
  statement: (0 : Multiset α).sup = ⊥
  proof: fold_zero _ _

@[to_dual (attr := simp)]

中文:
定理 sup_zero
  结论: (0 : Multiset α).sup = ⊥
  证明: fold_zero _ _

@[to_dual (attr := simp)]

Depends on / 依赖: fold_zero
-/
theorem sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _

@[to_dual (attr := simp)]
/--
theorem `sup_cons` / 定理 `sup_cons`

English:
theorem sup_cons
  given: (a : α) (s : Multiset α)
  statement: (a ::ₘ s).sup = a ⊔ s.sup
  proof: fold_cons_left _ _ _ _

@[to_dual (attr := simp)]

中文:
定理 sup_cons
  条件: (a : α) (s : Multiset α)
  结论: (a ::ₘ s).sup = a ⊔ s.sup
  证明: fold_cons_left _ _ _ _

@[to_dual (attr := simp)]

Depends on / 依赖: fold_cons_left
-/
theorem sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup :=
  fold_cons_left _ _ _ _

@[to_dual (attr := simp)]
/--
theorem `sup_singleton` / 定理 `sup_singleton`

English:
theorem sup_singleton
  given: {a : α}
  statement: ({a} : Multiset α).sup = a
  proof: sup_bot_eq _

@[to_dual (attr := simp)]

中文:
定理 sup_singleton
  条件: {a : α}
  结论: ({a} : Multiset α).sup = a
  证明: sup_bot_eq _

@[to_dual (attr := simp)]

Depends on / 依赖: sup_bot_eq
-/
theorem sup_singleton {a : α} : ({a} : Multiset α).sup = a := sup_bot_eq _

@[to_dual (attr := simp)]
/--
theorem `sup_add` / 定理 `sup_add`

English:
theorem sup_add
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup
  proof: Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

@[to_dual (attr := simp) le_inf]

中文:
定理 sup_add
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup
  证明: Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

@[to_dual (attr := simp) le_inf]

Depends on / 依赖: Eq.trans, fold_add
-/
theorem sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
  Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

@[to_dual (attr := simp) le_inf]
/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  given: {s : Multiset α} {a : α}
  statement: s.sup <= a ↔ forall b in s, b <= a
  proof: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and])

@[to_dual inf_le]

中文:
定理 sup_le
  条件: {s : Multiset α} {a : α}
  结论: s.sup <= a ↔ 对任意 b in s, b <= a
  证明: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and])

@[to_dual inf_le]

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, forall_and, induction_on, or_imp
-/
theorem sup_le {s : Multiset α} {a : α} : s.sup <= a ↔ forall b in s, b <= a :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and])

@[to_dual inf_le]
/--
theorem `le_sup` / 定理 `le_sup`

English:
theorem le_sup
  given: {s : Multiset α} {a : α} (h : a in s)
  statement: a <= s.sup
  proof: sup_le.1 le_rfl _ h

@[to_dual (attr := gcongr)]

中文:
定理 le_sup
  条件: {s : Multiset α} {a : α} (h : a in s)
  结论: a <= s.sup
  证明: sup_le.1 le_rfl _ h

@[to_dual (attr := gcongr)]

Depends on / 依赖: le_rfl, sup_le
-/
theorem le_sup {s : Multiset α} {a : α} (h : a in s) : a <= s.sup :=
  sup_le.1 le_rfl _ h

@[to_dual (attr := gcongr)]
/--
theorem `sup_mono` / 定理 `sup_mono`

English:
theorem sup_mono
  given: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  statement: s₁.sup <= s₂.sup
  proof: sup_le.2 fun _ hb => le_sup (h hb)

中文:
定理 sup_mono
  条件: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  结论: s₁.sup <= s₂.sup
  证明: sup_le.2 fun _ hb => le_sup (h hb)

Depends on / 依赖: le_sup, sup_le
-/
theorem sup_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₁.sup <= s₂.sup :=
  sup_le.2 fun _ hb => le_sup (h hb)

variable [DecidableEq α]

@[to_dual (attr := simp)]
/--
theorem `sup_dedup` / 定理 `sup_dedup`

English:
theorem sup_dedup
  given: (s : Multiset α)
  statement: (dedup s).sup = s.sup
  proof: fold_dedup_idem _ _ _

@[to_dual (attr := simp)]

中文:
定理 sup_dedup
  条件: (s : Multiset α)
  结论: (dedup s).sup = s.sup
  证明: fold_dedup_idem _ _ _

@[to_dual (attr := simp)]

Depends on / 依赖: fold_dedup_idem
-/
theorem sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _

@[to_dual (attr := simp)]
/--
theorem `sup_ndunion` / 定理 `sup_ndunion`

English:
theorem sup_ndunion
  given: (s₁ s₂ : Multiset α)
  statement: (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup
  proof: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]

中文:
定理 sup_ndunion
  条件: (s₁ s₂ : Multiset α)
  结论: (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup
  证明: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]

Depends on / 依赖: dedup_ext, sup_add, sup_dedup
-/
theorem sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]
/--
theorem `sup_union` / 定理 `sup_union`

English:
theorem sup_union
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ union s₂).sup = s₁.sup ⊔ s₂.sup
  proof: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]

中文:
定理 sup_union
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ union s₂).sup = s₁.sup ⊔ s₂.sup
  证明: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]

Depends on / 依赖: dedup_ext, sup_add, sup_dedup
-/
theorem sup_union (s₁ s₂ : Multiset α) : (s₁ union s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_add]; simp

@[to_dual (attr := simp)]
/--
theorem `sup_ndinsert` / 定理 `sup_ndinsert`

English:
theorem sup_ndinsert
  given: (a : α) (s : Multiset α)
  statement: (ndinsert a s).sup = a ⊔ s.sup
  proof: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_cons]; simp

中文:
定理 sup_ndinsert
  条件: (a : α) (s : Multiset α)
  结论: (ndinsert a s).sup = a ⊔ s.sup
  证明: by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_cons]; simp

Depends on / 依赖: dedup_ext, sup_cons, sup_dedup
-/
theorem sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup := by
  rw [← sup_dedup]; rw [dedup_ext.2]; rw [sup_dedup]; rw [sup_cons]; simp

/--
theorem `nodup_sup_iff` / 定理 `nodup_sup_iff`

English:
theorem nodup_sup_iff
  given: {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)}
  proof: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ h => simp [h]

中文:
定理 nodup_sup_iff
  条件: {α : 类型} [DecidableEq α] {m : Multiset (Multiset α)}
  证明: by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ h => simp [h]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem nodup_sup_iff {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ forall a : Multiset α, a in m -> a.Nodup := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ h => simp [h]

end Multiset
