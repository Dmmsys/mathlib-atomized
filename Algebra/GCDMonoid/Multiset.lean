/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Multiset.Fold

/-!
# GCD and LCM operations on multisets

## Main definitions

- `Multiset.gcd` - the greatest common denominator of a `Multiset` of elements of a `GCDMonoid`
- `Multiset.lcm` - the least common multiple of a `Multiset` of elements of a `GCDMonoid`

## Implementation notes

TODO: simplify with a tactic and `Data.Multiset.Lattice`

## Tags

multiset, gcd
-/

@[expose] public section

namespace Multiset

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### LCM -/


section lcm

/--
Definition of `lcm` / `lcm` 的定义

English:
definition lcm
  signature: (s : Multiset α)
  body: s.fold GCDMonoid.lcm 1

@[simp]

中文:
定义 lcm
  签名: (s : Multiset α)
  定义体: s.fold GCDMonoid.lcm 1

@[simp]

Depends on / 依赖: GCDMonoid, GCDMonoid.lcm, s.fold
-/
def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1

@[simp]
/--
theorem `lcm_zero` / 定理 `lcm_zero`

English:
theorem lcm_zero
  statement: (0 : Multiset α).lcm = 1
  proof: fold_zero _ _

@[simp]

中文:
定理 lcm_zero
  结论: (0 : Multiset α).lcm = 1
  证明: fold_zero _ _

@[simp]

Depends on / 依赖: fold_zero
-/
theorem lcm_zero : (0 : Multiset α).lcm = 1 :=
  fold_zero _ _

@[simp]
/--
theorem `lcm_cons` / 定理 `lcm_cons`

English:
theorem lcm_cons
  given: (a : α) (s : Multiset α)
  statement: (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm
  proof: fold_cons_left _ _ _ _

@[simp]

中文:
定理 lcm_cons
  条件: (a : α) (s : Multiset α)
  结论: (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm
  证明: fold_cons_left _ _ _ _

@[simp]

Depends on / 依赖: fold_cons_left
-/
theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm :=
  fold_cons_left _ _ _ _

@[simp]
/--
theorem `lcm_singleton` / 定理 `lcm_singleton`

English:
theorem lcm_singleton
  given: {a : α}
  statement: ({a} : Multiset α).lcm = normalize a
  proof: (fold_singleton _ _ _).trans lcm_one_right _

@[simp]

中文:
定理 lcm_singleton
  条件: {a : α}
  结论: ({a} : Multiset α).lcm = normalize a
  证明: (fold_singleton _ _ _).trans lcm_one_right _

@[simp]

Depends on / 依赖: fold_singleton, lcm_one_right
-/
theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a :=
(fold_singleton _ _ _).trans lcm_one_right _

@[simp]
/--
theorem `lcm_add` / 定理 `lcm_add`

English:
theorem lcm_add
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  proof: Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)

中文:
定理 lcm_add
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  证明: Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)

Depends on / 依赖: Eq.trans, fold_add
-/
theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)

/--
theorem `lcm_dvd` / 定理 `lcm_dvd`

English:
theorem lcm_dvd
  given: {s : Multiset α} {a : α}
  statement: s.lcm ∣ a ↔ forall b in s, b ∣ a
  proof: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, lcm_dvd_iff])

中文:
定理 lcm_dvd
  条件: {s : Multiset α} {a : α}
  结论: s.lcm ∣ a ↔ 对任意 b in s, b ∣ a
  证明: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, lcm_dvd_iff])

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, forall_and, induction_on, lcm_dvd_iff, or_imp
-/
theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall b in s, b ∣ a :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, lcm_dvd_iff])

/--
theorem `dvd_lcm` / 定理 `dvd_lcm`

English:
theorem dvd_lcm
  given: {s : Multiset α} {a : α} (h : a in s)
  statement: a ∣ s.lcm
  proof: lcm_dvd.1 dvd_rfl _ h

中文:
定理 dvd_lcm
  条件: {s : Multiset α} {a : α} (h : a in s)
  结论: a ∣ s.lcm
  证明: lcm_dvd.1 dvd_rfl _ h

Depends on / 依赖: dvd_rfl, lcm_dvd
-/
theorem dvd_lcm {s : Multiset α} {a : α} (h : a in s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h

/--
theorem `lcm_mono` / 定理 `lcm_mono`

English:
theorem lcm_mono
  given: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  statement: s₁.lcm ∣ s₂.lcm
  proof: lcm_dvd.2 fun _ hb => dvd_lcm (h hb)

@[simp]

中文:
定理 lcm_mono
  条件: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  结论: s₁.lcm ∣ s₂.lcm
  证明: lcm_dvd.2 fun _ hb => dvd_lcm (h hb)

@[simp]

Depends on / 依赖: dvd_lcm, lcm_dvd
-/
theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₁.lcm ∣ s₂.lcm :=
  lcm_dvd.2 fun _ hb => dvd_lcm (h hb)

@[simp]
/--
theorem `normalize_lcm` / 定理 `normalize_lcm`

English:
theorem normalize_lcm
  given: (s : Multiset α)
  statement: normalize s.lcm = s.lcm
  proof: Multiset.induction_on s (by simp) fun a s _ => by simp

@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ 0 in s := by
  induction s using Multiset.induction_on with
  | empty => simp only [lcm_zero, one_ne_zero, notMem_zero]
  | cons a s ihs => simp only [mem_cons

中文:
定理 normalize_lcm
  条件: (s : Multiset α)
  结论: normalize s.lcm = s.lcm
  证明: Multiset.induction_on s (by simp) fun a s _ => by simp

@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ 0 in s := by
  induction s using Multiset.induction_on with
  | empty => simp only [lcm_zero, one_ne_zero, notMem_zero]
  | cons a s ihs => simp only [mem_cons

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s _ => by simp

@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ 0 in s := by
  induction s using Multiset.induction_on with
  | empty => simp only [lcm_zero, one_ne_zero, notMem_zero]
  | cons a s ihs => simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a]

/--
theorem `lcm_ne_zero_iff` / 定理 `lcm_ne_zero_iff`

English:
theorem lcm_ne_zero_iff
  given: [Nontrivial α] (s : Multiset α)
  statement: s.lcm != 0 ↔ 0 ∉ s
  proof: not_congr (lcm_eq_zero_iff s)

中文:
定理 lcm_ne_zero_iff
  条件: [Nontrivial α] (s : Multiset α)
  结论: s.lcm != 0 ↔ 0 ∉ s
  证明: not_congr (lcm_eq_zero_iff s)

Depends on / 依赖: lcm_eq_zero_iff, not_congr
-/
theorem lcm_ne_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm != 0 ↔ 0 ∉ s :=
  not_congr (lcm_eq_zero_iff s)

variable [DecidableEq α]

@[simp]
/--
theorem `lcm_dedup` / 定理 `lcm_dedup`

English:
theorem lcm_dedup
  given: (s : Multiset α)
  statement: (dedup s).lcm = s.lcm
  proof: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, lcm_cons]
    unfold lcm
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← lcm_assoc]; rw [lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _

中文:
定理 lcm_dedup
  条件: (s : Multiset α)
  结论: (dedup s).lcm = s.lcm
  证明: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, lcm_cons]
    unfold lcm
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← lcm_assoc]; rw [lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _

Depends on / 依赖: Multiset, Multiset.induction_on, associated_normalize, cons_erase, dedup_cons_of_mem, fold_cons_left, induction_on, lcm_assoc, lcm_cons, lcm_eq_of_associated_left, lcm_same
-/
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, lcm_cons]
    unfold lcm
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← lcm_assoc]; rw [lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)

@[simp]
/--
theorem `lcm_ndunion` / 定理 `lcm_ndunion`

English:
theorem lcm_ndunion
  given: (s₁ s₂ : Multiset α)
  statement: (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  proof: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]

中文:
定理 lcm_ndunion
  条件: (s₁ s₂ : Multiset α)
  结论: (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  证明: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]

Depends on / 依赖: dedup_ext, lcm_add, lcm_dedup
-/
theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]
/--
theorem `lcm_union` / 定理 `lcm_union`

English:
theorem lcm_union
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ union s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  proof: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]

中文:
定理 lcm_union
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ union s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
  证明: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]

Depends on / 依赖: dedup_ext, lcm_add, lcm_dedup
-/
theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ union s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_add]
  simp

@[simp]
/--
theorem `lcm_ndinsert` / 定理 `lcm_ndinsert`

English:
theorem lcm_ndinsert
  given: (a : α) (s : Multiset α)
  statement: (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm
  proof: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_cons]
  simp

中文:
定理 lcm_ndinsert
  条件: (a : α) (s : Multiset α)
  结论: (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm
  证明: by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_cons]
  simp

Depends on / 依赖: dedup_ext, lcm_cons, lcm_dedup
-/
theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm := by
  rw [← lcm_dedup]; rw [dedup_ext.2]; rw [lcm_dedup]; rw [lcm_cons]
  simp

end lcm

/-! ### GCD -/


section gcd

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (s : Multiset α)
  body: s.fold GCDMonoid.gcd 0

@[simp]

中文:
定义 gcd
  签名: (s : Multiset α)
  定义体: s.fold GCDMonoid.gcd 0

@[simp]

Depends on / 依赖: GCDMonoid, GCDMonoid.gcd, s.fold
-/
def gcd (s : Multiset α) : α :=
  s.fold GCDMonoid.gcd 0

@[simp]
/--
theorem `gcd_zero` / 定理 `gcd_zero`

English:
theorem gcd_zero
  statement: (0 : Multiset α).gcd = 0
  proof: fold_zero _ _

@[simp]

中文:
定理 gcd_zero
  结论: (0 : Multiset α).gcd = 0
  证明: fold_zero _ _

@[simp]

Depends on / 依赖: fold_zero
-/
theorem gcd_zero : (0 : Multiset α).gcd = 0 :=
  fold_zero _ _

@[simp]
/--
theorem `gcd_cons` / 定理 `gcd_cons`

English:
theorem gcd_cons
  given: (a : α) (s : Multiset α)
  statement: (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd
  proof: fold_cons_left _ _ _ _

@[simp]

中文:
定理 gcd_cons
  条件: (a : α) (s : Multiset α)
  结论: (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd
  证明: fold_cons_left _ _ _ _

@[simp]

Depends on / 依赖: fold_cons_left
-/
theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd :=
  fold_cons_left _ _ _ _

@[simp]
/--
theorem `gcd_singleton` / 定理 `gcd_singleton`

English:
theorem gcd_singleton
  given: {a : α}
  statement: ({a} : Multiset α).gcd = normalize a
  proof: (fold_singleton _ _ _).trans gcd_zero_right _

@[simp]

中文:
定理 gcd_singleton
  条件: {a : α}
  结论: ({a} : Multiset α).gcd = normalize a
  证明: (fold_singleton _ _ _).trans gcd_zero_right _

@[simp]

Depends on / 依赖: fold_singleton, gcd_zero_right
-/
theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a :=
(fold_singleton _ _ _).trans gcd_zero_right _

@[simp]
/--
theorem `gcd_add` / 定理 `gcd_add`

English:
theorem gcd_add
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  proof: Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)

中文:
定理 gcd_add
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  证明: Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)

Depends on / 依赖: Eq.trans, fold_add
-/
theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)

/--
theorem `dvd_gcd` / 定理 `dvd_gcd`

English:
theorem dvd_gcd
  given: {s : Multiset α} {a : α}
  statement: a ∣ s.gcd ↔ forall b in s, a ∣ b
  proof: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

中文:
定理 dvd_gcd
  条件: {s : Multiset α} {a : α}
  结论: a ∣ s.gcd ↔ 对任意 b in s, a ∣ b
  证明: Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, dvd_gcd_iff, forall_and, induction_on, or_imp
-/
theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ forall b in s, a ∣ b :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

/--
theorem `gcd_dvd` / 定理 `gcd_dvd`

English:
theorem gcd_dvd
  given: {s : Multiset α} {a : α} (h : a in s)
  statement: s.gcd ∣ a
  proof: dvd_gcd.1 dvd_rfl _ h

中文:
定理 gcd_dvd
  条件: {s : Multiset α} {a : α} (h : a in s)
  结论: s.gcd ∣ a
  证明: dvd_gcd.1 dvd_rfl _ h

Depends on / 依赖: dvd_gcd, dvd_rfl
-/
theorem gcd_dvd {s : Multiset α} {a : α} (h : a in s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h

/--
theorem `gcd_mono` / 定理 `gcd_mono`

English:
theorem gcd_mono
  given: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  statement: s₂.gcd ∣ s₁.gcd
  proof: dvd_gcd.2 fun _ hb => gcd_dvd (h hb)

@[simp]

中文:
定理 gcd_mono
  条件: {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂)
  结论: s₂.gcd ∣ s₁.gcd
  证明: dvd_gcd.2 fun _ hb => gcd_dvd (h hb)

@[simp]

Depends on / 依赖: dvd_gcd, gcd_dvd
-/
theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun _ hb => gcd_dvd (h hb)

@[simp]
/--
theorem `normalize_gcd` / 定理 `normalize_gcd`

English:
theorem normalize_gcd
  given: (s : Multiset α)
  statement: normalize s.gcd = s.gcd
  proof: Multiset.induction_on s (by simp) fun a s _ => by simp

中文:
定理 normalize_gcd
  条件: (s : Multiset α)
  结论: normalize s.gcd = s.gcd
  证明: Multiset.induction_on s (by simp) fun a s _ => by simp

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s _ => by simp

/--
theorem `gcd_eq_zero_iff` / 定理 `gcd_eq_zero_iff`

English:
theorem gcd_eq_zero_iff
  given: (s : Multiset α)
  statement: s.gcd = 0 ↔ forall x in s, x = 0
  proof: by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx => h x (mem_cons_of_mem hx)]

中文:
定理 gcd_eq_zero_iff
  条件: (s : Multiset α)
  结论: s.gcd = 0 ↔ 对任意 x in s, x = 0
  证明: by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx => h x (mem_cons_of_mem hx)]

Depends on / 依赖: eq_zero_of_zero_dvd, gcd_dvd, induction_on, mem_cons_of_mem, mem_cons_self, s.induction_on
-/
theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ forall x in s, x = 0 := by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx => h x (mem_cons_of_mem hx)]

/--
theorem `gcd_ne_zero_iff` / 定理 `gcd_ne_zero_iff`

English:
theorem gcd_ne_zero_iff
  given: (s : Multiset α)
  statement: s.gcd != 0 ↔ exists x in s, x != 0
  proof: by
  simp [gcd_eq_zero_iff]

中文:
定理 gcd_ne_zero_iff
  条件: (s : Multiset α)
  结论: s.gcd != 0 ↔ 存在 x in s, x != 0
  证明: by
  simp [gcd_eq_zero_iff]

Depends on / 依赖: gcd_eq_zero_iff
-/
theorem gcd_ne_zero_iff (s : Multiset α) : s.gcd != 0 ↔ exists x in s, x != 0 := by
  simp [gcd_eq_zero_iff]

/--
theorem `gcd_map_mul` / 定理 `gcd_map_mul`

English:
theorem gcd_map_mul
  statement: {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
  proof: by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero]
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right

中文:
定理 gcd_map_mul
  结论: {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
  证明: by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero]
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right

Depends on / 依赖: gcd_cons, gcd_eq_right, gcd_mul_left, gcd_zero, induction_on, map_cons, map_zero, mul_right, mul_zero, normalize_associated, s.induction_on, simp_rw
-/
theorem gcd_map_mul {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    (a : α) (s : Multiset α) : (s.map (a * ·)).gcd = normalize a * s.gcd := by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero]
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right

/--
theorem `associated_gcd_map_mul` / 定理 `associated_gcd_map_mul`

English:
theorem associated_gcd_map_mul
  given: (a : α) (s : Multiset α)
  proof: by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero, Associated.of_eq]
  · simp_rw [map_cons, gcd_cons]
    exact .trans (.gcd .rfl ih) (gcd_mul_left' ..)

中文:
定理 associated_gcd_map_mul
  条件: (a : α) (s : Multiset α)
  证明: by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero, Associated.of_eq]
  · simp_rw [map_cons, gcd_cons]
    exact .trans (.gcd .rfl ih) (gcd_mul_left' ..)

Depends on / 依赖: Associated, Associated.of_eq, gcd_cons, gcd_mul_left, gcd_zero, induction_on, map_cons, map_zero, mul_zero, of_eq, s.induction_on, simp_rw
-/
theorem associated_gcd_map_mul (a : α) (s : Multiset α) :
    Associated (s.map (a * ·)).gcd (a * s.gcd) := by
  refine s.induction_on ?_ fun b s ih => ?_
  · simp_rw [map_zero, gcd_zero, mul_zero, Associated.of_eq]
  · simp_rw [map_cons, gcd_cons]
    exact .trans (.gcd .rfl ih) (gcd_mul_left' ..)

section

variable [DecidableEq α]

@[simp]
/--
theorem `gcd_dedup` / 定理 `gcd_dedup`

English:
theorem gcd_dedup
  given: (s : Multiset α)
  statement: (dedup s).gcd = s.gcd
  proof: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, gcd_cons]
    unfold gcd
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← gcd_assoc]; rw [gcd_same]
    apply (associated_normalize _).gcd_eq_left

@[simp]

中文:
定理 gcd_dedup
  条件: (s : Multiset α)
  结论: (dedup s).gcd = s.gcd
  证明: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, gcd_cons]
    unfold gcd
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← gcd_assoc]; rw [gcd_same]
    apply (associated_normalize _).gcd_eq_left

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, associated_normalize, cons_erase, dedup_cons_of_mem, fold_cons_left, gcd_assoc, gcd_cons, gcd_eq_left, gcd_same, induction_on
-/
theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, gcd_cons]
    unfold gcd
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← gcd_assoc]; rw [gcd_same]
    apply (associated_normalize _).gcd_eq_left

@[simp]
/--
theorem `gcd_ndunion` / 定理 `gcd_ndunion`

English:
theorem gcd_ndunion
  given: (s₁ s₂ : Multiset α)
  statement: (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  proof: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]

中文:
定理 gcd_ndunion
  条件: (s₁ s₂ : Multiset α)
  结论: (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  证明: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]

Depends on / 依赖: dedup_ext, gcd_add, gcd_dedup
-/
theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]
/--
theorem `gcd_union` / 定理 `gcd_union`

English:
theorem gcd_union
  given: (s₁ s₂ : Multiset α)
  statement: (s₁ union s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  proof: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]

中文:
定理 gcd_union
  条件: (s₁ s₂ : Multiset α)
  结论: (s₁ union s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
  证明: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]

Depends on / 依赖: dedup_ext, gcd_add, gcd_dedup
-/
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ union s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_add]
  simp

@[simp]
/--
theorem `gcd_ndinsert` / 定理 `gcd_ndinsert`

English:
theorem gcd_ndinsert
  given: (a : α) (s : Multiset α)
  statement: (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd
  proof: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_cons]
  simp

中文:
定理 gcd_ndinsert
  条件: (a : α) (s : Multiset α)
  结论: (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd
  证明: by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_cons]
  simp

Depends on / 依赖: dedup_ext, gcd_cons, gcd_dedup
-/
theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd := by
  rw [← gcd_dedup]; rw [dedup_ext.2]; rw [gcd_dedup]; rw [gcd_cons]
  simp

end

/--
theorem `extract_gcd'` / 定理 `extract_gcd'`

English:
theorem extract_gcd'
  statement: (s t : Multiset α) (hs : exists x, x in s ∧ x != (0 : α))
  proof: by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm ?_) .rfl (a := s.gcd) ?_
  · simpa using (Associated.of_eq <| congr(gcd $ht)).trans (associated_gcd_map_mul ..)
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

中文:
定理 extract_gcd'
  结论: (s t : Multiset α) (hs : 存在 x, x in s ∧ x != (0 : α))
  证明: by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm ?_) .rfl (a := s.gcd) ?_
  · simpa using (Associated.of_eq <| congr(gcd $ht)).trans (associated_gcd_map_mul ..)
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

Depends on / 依赖: Associated, Associated.of_eq, associated_gcd_map_mul, associated_one_iff_isUnit, contrapose, gcd_eq_zero_iff, normalize_eq_one, normalize_gcd, of_eq, of_mul_left, s.gcd, s.gcd_eq_zero_iff
-/
theorem extract_gcd' (s t : Multiset α) (hs : exists x, x in s ∧ x != (0 : α))
    (ht : s = t.map (s.gcd * ·)) : t.gcd = 1 := by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm ?_) .rfl (a := s.gcd) ?_
  · simpa using (Associated.of_eq <| congr(gcd $ht)).trans (associated_gcd_map_mul ..)
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

/--
theorem `extract_gcd` / 定理 `extract_gcd`

English:
theorem extract_gcd
  given: (s : Multiset α) (hs : s != 0)
  proof: by
  classical
    by_cases! h : forall x in s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate]; rw [eq_replicate]; rw [mul_one]; rw [s.gcd_eq_zero_iff.2 h]; rw [← nsmul_singleton]; rw [← gcd_dedup]; rw [dedup_nsmul (card_pos.2 hs).ne']; rw [dedup_singleton]; rw [gcd_singleton]
 

中文:
定理 extract_gcd
  条件: (s : Multiset α) (hs : s != 0)
  证明: by
  classical
    by_cases! h : forall x in s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate]; rw [eq_replicate]; rw [mul_one]; rw [s.gcd_eq_zero_iff.2 h]; rw [← nsmul_singleton]; rw [← gcd_dedup]; rw [dedup_nsmul (card_pos.2 hs).ne']; rw [dedup_singleton]; rw [gcd_singleton]
 

Depends on / 依赖: card_pos, classical, conv_lhs, dedup_nsmul, dedup_singleton, eq_replicate, extract_gcd, gcd_dedup, gcd_dvd, gcd_eq_zero_iff, gcd_singleton, map_id, map_pmap, map_replicate, mul_one, normalize_one, nsmul_singleton, pmap_eq_map, replicate, s.gcd_eq_zero_iff
-/
theorem extract_gcd (s : Multiset α) (hs : s != 0) :
    exists t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  classical
    by_cases! h : forall x in s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate]; rw [eq_replicate]; rw [mul_one]; rw [s.gcd_eq_zero_iff.2 h]; rw [← nsmul_singleton]; rw [← gcd_dedup]; rw [dedup_nsmul (card_pos.2 hs).ne']; rw [dedup_singleton]; rw [gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @gcd_dvd _ _ _ s
      refine ⟨s.pmap @f fun _ => id, ?_, extract_gcd' s _ h ?_⟩ <;>
      · rw [map_pmap]
        conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ => id]
        congr with (x hx)
        rw [id]; rw [← hf hx]

end gcd

end Multiset
