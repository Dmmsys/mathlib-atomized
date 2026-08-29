/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Dedup
public import Mathlib.Data.Multiset.Basic

/-!
# Deduplicating Multisets to make Finsets

This file concerns `Multiset.dedup` and `List.dedup` as a way to create `Finset`s.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

@[simp]
/--
theorem `dedup_eq_self` / 定理 `dedup_eq_self`

English:
theorem dedup_eq_self
  given: [DecidableEq α] (s : Finset α)
  statement: dedup s.1 = s.1
  proof: s.2.dedup

中文:
定理 dedup_eq_self
  条件: [DecidableEq α] (s : Finset α)
  结论: dedup s.1 = s.1
  证明: s.2.dedup
-/
theorem dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1 :=
  s.2.dedup

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (s : Multiset α)
  body: ⟨_, nodup_dedup s⟩

@[simp]

中文:
定义 toFinset
  签名: (s : Multiset α)
  定义体: ⟨_, nodup_dedup s⟩

@[simp]

Depends on / 依赖: nodup_dedup
-/
def toFinset (s : Multiset α) : Finset α :=
  ⟨_, nodup_dedup s⟩

@[simp]
/--
theorem `toFinset_val` / 定理 `toFinset_val`

English:
theorem toFinset_val
  given: (s : Multiset α)
  statement: s.toFinset.1 = s.dedup
  proof: rfl

中文:
定理 toFinset_val
  条件: (s : Multiset α)
  结论: s.toFinset.1 = s.dedup
  证明: rfl
-/
theorem toFinset_val (s : Multiset α) : s.toFinset.1 = s.dedup :=
  rfl

/--
theorem `toFinset_eq` / 定理 `toFinset_eq`

English:
theorem toFinset_eq
  given: {s : Multiset α} (n : Nodup s)
  statement: Finset.mk s n = s.toFinset
  proof: Finset.val_inj.1 n.dedup.symm

中文:
定理 toFinset_eq
  条件: {s : Multiset α} (n : Nodup s)
  结论: Finset.mk s n = s.toFinset
  证明: Finset.val_inj.1 n.dedup.symm

Depends on / 依赖: Finset, Finset.val_inj, n.dedup.symm, val_inj
-/
theorem toFinset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset :=
  Finset.val_inj.1 n.dedup.symm

/--
theorem `Nodup.toFinset_inj` / 定理 `Nodup.toFinset_inj`

English:
theorem Nodup.toFinset_inj
  statement: {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
  proof: by
  simpa [← toFinset_eq hl, ← toFinset_eq hl'] using h

@[simp, grind =]

中文:
定理 Nodup.toFinset_inj
  结论: {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
  证明: by
  simpa [← toFinset_eq hl, ← toFinset_eq hl'] using h

@[simp, grind =]

Depends on / 依赖: toFinset_eq
-/
theorem Nodup.toFinset_inj {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l = l' := by
  simpa [← toFinset_eq hl, ← toFinset_eq hl'] using h

@[simp, grind =]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  given: {a : α} {s : Multiset α}
  statement: a in s.toFinset ↔ a in s
  proof: mem_dedup

@[simp]

中文:
定理 mem_toFinset
  条件: {a : α} {s : Multiset α}
  结论: a in s.toFinset ↔ a in s
  证明: mem_dedup

@[simp]

Depends on / 依赖: mem_dedup
-/
theorem mem_toFinset {a : α} {s : Multiset α} : a in s.toFinset ↔ a in s :=
  mem_dedup

@[simp]
/--
theorem `toFinset_subset` / 定理 `toFinset_subset`

English:
theorem toFinset_subset
  statement: s.toFinset subseteq t.toFinset ↔ s subseteq t
  proof: by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]

@[simp]

中文:
定理 toFinset_subset
  结论: s.toFinset subseteq t.toFinset ↔ s subseteq t
  证明: by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]

@[simp]

Depends on / 依赖: Finset, Finset.subset_iff, Multiset, Multiset.mem_toFinset, Multiset.subset_iff, mem_toFinset, subset_iff
-/
theorem toFinset_subset : s.toFinset subseteq t.toFinset ↔ s subseteq t := by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]

@[simp]
/--
theorem `toFinset_ssubset` / 定理 `toFinset_ssubset`

English:
theorem toFinset_ssubset
  statement: s.toFinset ⊂ t.toFinset ↔ s ⊂ t
  proof: by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  rfl

@[simp]

中文:
定理 toFinset_ssubset
  结论: s.toFinset ⊂ t.toFinset ↔ s ⊂ t
  证明: by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  rfl

@[simp]

Depends on / 依赖: Finset, Finset.ssubset_def, simp_rw, ssubset_def, toFinset_subset
-/
theorem toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  rfl

@[simp]
/--
theorem `toFinset_dedup` / 定理 `toFinset_dedup`

English:
theorem toFinset_dedup
  given: (m : Multiset α)
  statement: m.dedup.toFinset = m.toFinset
  proof: by
  simp_rw [toFinset, dedup_idem]

中文:
定理 toFinset_dedup
  条件: (m : Multiset α)
  结论: m.dedup.toFinset = m.toFinset
  证明: by
  simp_rw [toFinset, dedup_idem]

Depends on / 依赖: dedup_idem, simp_rw, toFinset
-/
theorem toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset := by
  simp_rw [toFinset, dedup_idem]

/--
Instance `isWellFounded_ssubset` / 实例 `isWellFounded_ssubset`

English:
instance isWellFounded_ssubset
  signature: : IsWellFounded (Multiset β) (· ⊂ ·)
  body: by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2

中文:
实例 isWellFounded_ssubset
  签名: : IsWellFounded (Multiset β) (· ⊂ ·)
  定义体: by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2

Depends on / 依赖: InvImage, Subrelation, Subrelation.isWellFounded, classical, isWellFounded, shiftLeft, toFinset, toFinset_ssubset
-/
instance isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·) := by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2

end Multiset

namespace Finset

@[simp]
/--
theorem `val_toFinset` / 定理 `val_toFinset`

English:
theorem val_toFinset
  given: [DecidableEq α] (s : Finset α)
  statement: s.val.toFinset = s
  proof: by
  ext
  rw [Multiset.mem_toFinset]; rw [← mem_def]

中文:
定理 val_toFinset
  条件: [DecidableEq α] (s : Finset α)
  结论: s.val.toFinset = s
  证明: by
  ext
  rw [Multiset.mem_toFinset]; rw [← mem_def]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, mem_def, mem_toFinset
-/
theorem val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s := by
  ext
  rw [Multiset.mem_toFinset]; rw [← mem_def]

/--
theorem `val_le_iff_val_subset` / 定理 `val_le_iff_val_subset`

English:
theorem val_le_iff_val_subset
  given: {a : Finset α} {b : Multiset α}
  statement: a.val <= b ↔ a.val subseteq b
  proof: Multiset.le_iff_subset a.nodup

中文:
定理 val_le_iff_val_subset
  条件: {a : Finset α} {b : Multiset α}
  结论: a.val <= b ↔ a.val subseteq b
  证明: Multiset.le_iff_subset a.nodup

Depends on / 依赖: Multiset, Multiset.le_iff_subset, a.nodup, le_iff_subset
-/
theorem val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val <= b ↔ a.val subseteq b :=
  Multiset.le_iff_subset a.nodup

end Finset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α} {f : α -> β}
  {s : Finset α} {t : Set β} {t' : Finset β}

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (l : List α)
  body: Multiset.toFinset l

@[simp]

中文:
定义 toFinset
  签名: (l : List α)
  定义体: Multiset.toFinset l

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinset, toFinset
-/
def toFinset (l : List α) : Finset α :=
  Multiset.toFinset l

@[simp]
/--
theorem `toFinset_val` / 定理 `toFinset_val`

English:
theorem toFinset_val
  given: (l : List α)
  statement: l.toFinset.1 = (l.dedup : Multiset α)
  proof: rfl

@[simp]

中文:
定理 toFinset_val
  条件: (l : List α)
  结论: l.toFinset.1 = (l.dedup : Multiset α)
  证明: rfl

@[simp]
-/
theorem toFinset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α) :=
  rfl

@[simp]
/--
theorem `toFinset_coe` / 定理 `toFinset_coe`

English:
theorem toFinset_coe
  given: (l : List α)
  statement: (l : Multiset α).toFinset = l.toFinset
  proof: rfl

中文:
定理 toFinset_coe
  条件: (l : List α)
  结论: (l : Multiset α).toFinset = l.toFinset
  证明: rfl
-/
theorem toFinset_coe (l : List α) : (l : Multiset α).toFinset = l.toFinset :=
  rfl

/--
theorem `toFinset_eq` / 定理 `toFinset_eq`

English:
theorem toFinset_eq
  given: (n : Nodup l)
  statement: @Finset.mk α l n = l.toFinset
  proof: Multiset.toFinset_eq by rwa [Multiset.coe_nodup]

@[simp]

中文:
定理 toFinset_eq
  条件: (n : Nodup l)
  结论: @Finset.mk α l n = l.toFinset
  证明: Multiset.toFinset_eq by rwa [Multiset.coe_nodup]

@[simp]

Depends on / 依赖: Multiset, Multiset.coe_nodup, Multiset.toFinset_eq, coe_nodup, toFinset_eq
-/
theorem toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFinset :=
Multiset.toFinset_eq by rwa [Multiset.coe_nodup]

@[simp]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  statement: a in l.toFinset ↔ a in l
  proof: mem_dedup

@[simp, norm_cast]

中文:
定理 mem_toFinset
  结论: a in l.toFinset ↔ a in l
  证明: mem_dedup

@[simp, norm_cast]

Depends on / 依赖: mem_dedup
-/
theorem mem_toFinset : a in l.toFinset ↔ a in l :=
  mem_dedup

@[simp, norm_cast]
/--
theorem `coe_toFinset` / 定理 `coe_toFinset`

English:
theorem coe_toFinset
  given: (l : List α)
  statement: (l.toFinset : Set α) = { a | a in l }
  proof: Set.ext fun _ => List.mem_toFinset

中文:
定理 coe_toFinset
  条件: (l : List α)
  结论: (l.toFinset : Set α) = { a | a in l }
  证明: Set.ext fun _ => List.mem_toFinset

Depends on / 依赖: List.mem_toFinset, Set.ext, mem_toFinset
-/
theorem coe_toFinset (l : List α) : (l.toFinset : Set α) = { a | a in l } :=
  Set.ext fun _ => List.mem_toFinset

/--
theorem `toFinset_surj_on` / 定理 `toFinset_surj_on`

English:
theorem toFinset_surj_on
  statement: Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ
  proof: by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (toFinset_eq hl).symm⟩

中文:
定理 toFinset_surj_on
  结论: Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ
  证明: by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (toFinset_eq hl).symm⟩

Depends on / 依赖: toFinset_eq
-/
theorem toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ := by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (toFinset_eq hl).symm⟩

/--
theorem `toFinset_surjective` / 定理 `toFinset_surjective`

English:
theorem toFinset_surjective
  statement: Surjective (toFinset : List α -> Finset α)
  proof: fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩

中文:
定理 toFinset_surjective
  结论: Surjective (toFinset : List α -> Finset α)
  证明: fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩
-/
theorem toFinset_surjective : Surjective (toFinset : List α -> Finset α) := fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩

/--
theorem `toFinset_eq_iff_perm_dedup` / 定理 `toFinset_eq_iff_perm_dedup`

English:
theorem toFinset_eq_iff_perm_dedup
  statement: l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup
  proof: by
  simp [Finset.ext_iff, perm_ext_iff_of_nodup (nodup_dedup _) (nodup_dedup _)]

中文:
定理 toFinset_eq_iff_perm_dedup
  结论: l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup
  证明: by
  simp [Finset.ext_iff, perm_ext_iff_of_nodup (nodup_dedup _) (nodup_dedup _)]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff, nodup_dedup, perm_ext_iff_of_nodup
-/
theorem toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [Finset.ext_iff, perm_ext_iff_of_nodup (nodup_dedup _) (nodup_dedup _)]

/--
theorem `toFinset.ext_iff` / 定理 `toFinset.ext_iff`

English:
theorem toFinset.ext_iff
  given: {a b : List α}
  statement: a.toFinset = b.toFinset ↔ forall x, x in a ↔ x in b
  proof: by
  simp only [Finset.ext_iff, mem_toFinset]

中文:
定理 toFinset.ext_iff
  条件: {a b : List α}
  结论: a.toFinset = b.toFinset ↔ 对任意 x, x in a ↔ x in b
  证明: by
  simp only [Finset.ext_iff, mem_toFinset]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff, mem_toFinset
-/
theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ forall x, x in a ↔ x in b := by
  simp only [Finset.ext_iff, mem_toFinset]

/--
theorem `toFinset.ext` / 定理 `toFinset.ext`

English:
theorem toFinset.ext
  statement: (forall x, x in l ↔ x in l') -> l.toFinset = l'.toFinset
  proof: toFinset.ext_iff.mpr

中文:
定理 toFinset.ext
  结论: (对任意 x, x in l ↔ x in l') -> l.toFinset = l'.toFinset
  证明: toFinset.ext_iff.mpr

Depends on / 依赖: ext_iff, toFinset, toFinset.ext_iff.mpr
-/
theorem toFinset.ext : (forall x, x in l ↔ x in l') -> l.toFinset = l'.toFinset :=
  toFinset.ext_iff.mpr

/--
theorem `toFinset_eq_of_perm` / 定理 `toFinset_eq_of_perm`

English:
theorem toFinset_eq_of_perm
  given: (l l' : List α) (h : l ~ l')
  statement: l.toFinset = l'.toFinset
  proof: toFinset_eq_iff_perm_dedup.mpr h.dedup

中文:
定理 toFinset_eq_of_perm
  条件: (l l' : List α) (h : l ~ l')
  结论: l.toFinset = l'.toFinset
  证明: toFinset_eq_iff_perm_dedup.mpr h.dedup

Depends on / 依赖: h.dedup, toFinset_eq_iff_perm_dedup, toFinset_eq_iff_perm_dedup.mpr
-/
theorem toFinset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinset :=
  toFinset_eq_iff_perm_dedup.mpr h.dedup

/--
theorem `perm_of_nodup_nodup_toFinset_eq` / 定理 `perm_of_nodup_nodup_toFinset_eq`

English:
theorem perm_of_nodup_nodup_toFinset_eq
  statement: (hl : Nodup l) (hl' : Nodup l')
  proof: by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.toFinset_inj hl hl' h

@[simp]

中文:
定理 perm_of_nodup_nodup_toFinset_eq
  结论: (hl : Nodup l) (hl' : Nodup l')
  证明: by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.toFinset_inj hl hl' h

@[simp]

Depends on / 依赖: Multiset, Multiset.Nodup.toFinset_inj, Multiset.coe_eq_coe, coe_eq_coe, toFinset_inj
-/
theorem perm_of_nodup_nodup_toFinset_eq (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l ~ l' := by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.toFinset_inj hl hl' h

@[simp]
/--
theorem `toFinset_reverse` / 定理 `toFinset_reverse`

English:
theorem toFinset_reverse
  given: {l : List α}
  statement: toFinset l.reverse = l.toFinset
  proof: toFinset_eq_of_perm _ _ (reverse_perm l)

中文:
定理 toFinset_reverse
  条件: {l : List α}
  结论: toFinset l.reverse = l.toFinset
  证明: toFinset_eq_of_perm _ _ (reverse_perm l)

Depends on / 依赖: reverse_perm, toFinset_eq_of_perm
-/
theorem toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  toFinset_eq_of_perm _ _ (reverse_perm l)

end List

namespace Finset

section ToList

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (s : Finset α)
  body: s.1.toList

中文:
定义 toList
  签名: (s : Finset α)
  定义体: s.1.toList

Depends on / 依赖: toList
-/
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList

/--
theorem `nodup_toList` / 定理 `nodup_toList`

English:
theorem nodup_toList
  given: (s : Finset α)
  statement: s.toList.Nodup
  proof: by
  rw [toList]; rw [← Multiset.coe_nodup]; rw [Multiset.coe_toList]
  exact s.nodup

@[simp]

中文:
定理 nodup_toList
  条件: (s : Finset α)
  结论: s.toList.Nodup
  证明: by
  rw [toList]; rw [← Multiset.coe_nodup]; rw [Multiset.coe_toList]
  exact s.nodup

@[simp]

Depends on / 依赖: Multiset, Multiset.coe_nodup, Multiset.coe_toList, coe_nodup, coe_toList, s.nodup, toList
-/
theorem nodup_toList (s : Finset α) : s.toList.Nodup := by
  rw [toList]; rw [← Multiset.coe_nodup]; rw [Multiset.coe_toList]
  exact s.nodup

@[simp]
/--
theorem `mem_toList` / 定理 `mem_toList`

English:
theorem mem_toList
  given: {a : α} {s : Finset α}
  statement: a in s.toList ↔ a in s
  proof: Multiset.mem_toList

@[simp, norm_cast]

中文:
定理 mem_toList
  条件: {a : α} {s : Finset α}
  结论: a in s.toList ↔ a in s
  证明: Multiset.mem_toList

@[simp, norm_cast]

Depends on / 依赖: Multiset, Multiset.mem_toList, mem_toList
-/
theorem mem_toList {a : α} {s : Finset α} : a in s.toList ↔ a in s :=
  Multiset.mem_toList

@[simp, norm_cast]
/--
theorem `coe_toList` / 定理 `coe_toList`

English:
theorem coe_toList
  given: (s : Finset α)
  statement: (s.toList : Multiset α) = s.val
  proof: s.val.coe_toList

@[simp]

中文:
定理 coe_toList
  条件: (s : Finset α)
  结论: (s.toList : Multiset α) = s.val
  证明: s.val.coe_toList

@[simp]

Depends on / 依赖: coe_toList, s.val.coe_toList
-/
theorem coe_toList (s : Finset α) : (s.toList : Multiset α) = s.val :=
  s.val.coe_toList

@[simp]
/--
theorem `toList_toFinset` / 定理 `toList_toFinset`

English:
theorem toList_toFinset
  given: [DecidableEq α] (s : Finset α)
  statement: s.toList.toFinset = s
  proof: by
  ext
  simp

中文:
定理 toList_toFinset
  条件: [DecidableEq α] (s : Finset α)
  结论: s.toList.toFinset = s
  证明: by
  ext
  simp
-/
theorem toList_toFinset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s := by
  ext
  simp

/--
theorem `_root_.List.toFinset_toList` / 定理 `_root_.List.toFinset_toList`

English:
theorem _root_.List.toFinset_toList
  given: [DecidableEq α] {s : List α} (hs : s.Nodup)
  proof: by
  apply List.perm_of_nodup_nodup_toFinset_eq (nodup_toList _) hs
  rw [toList_toFinset]

中文:
定理 _root_.List.toFinset_toList
  条件: [DecidableEq α] {s : List α} (hs : s.Nodup)
  证明: by
  apply List.perm_of_nodup_nodup_toFinset_eq (nodup_toList _) hs
  rw [toList_toFinset]

Depends on / 依赖: List.perm_of_nodup_nodup_toFinset_eq, nodup_toList, perm_of_nodup_nodup_toFinset_eq, toList_toFinset
-/
theorem _root_.List.toFinset_toList [DecidableEq α] {s : List α} (hs : s.Nodup) :
    s.toFinset.toList.Perm s := by
  apply List.perm_of_nodup_nodup_toFinset_eq (nodup_toList _) hs
  rw [toList_toFinset]

/--
theorem `exists_list_nodup_eq` / 定理 `exists_list_nodup_eq`

English:
theorem exists_list_nodup_eq
  given: [DecidableEq α] (s : Finset α)
  proof: ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩

@[simp]

中文:
定理 exists_list_nodup_eq
  条件: [DecidableEq α] (s : Finset α)
  证明: ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩

@[simp]

Depends on / 依赖: nodup_toList, s.nodup_toList, s.toList, s.toList_toFinset, toList, toList_toFinset
-/
theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) :
    exists l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩

@[simp]
/--
theorem `perm_toList` / 定理 `perm_toList`

English:
theorem perm_toList
  given: {f₁ f₂ : Finset α}
  statement: f₁.toList.Perm f₂.toList ↔ f₁ = f₂ where
  proof: Finset.ext fun x => by simp [← Finset.mem_toList, h.mem_iff]
mpr h := .of_eq congrArg Finset.toList h

中文:
定理 perm_toList
  条件: {f₁ f₂ : Finset α}
  结论: f₁.toList.Perm f₂.toList ↔ f₁ = f₂ where
  证明: Finset.ext fun x => by simp [← Finset.mem_toList, h.mem_iff]
mpr h := .of_eq congrArg Finset.toList h
-/
protected theorem perm_toList {f₁ f₂ : Finset α} : f₁.toList.Perm f₂.toList ↔ f₁ = f₂ where
  mp h := Finset.ext fun x => by simp [← Finset.mem_toList, h.mem_iff]
mpr h := .of_eq congrArg Finset.toList h

end ToList

end Finset
