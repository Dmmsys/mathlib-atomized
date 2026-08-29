/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete
partial order, as opposed to a conditionally complete lattice.

-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {a b : α}

@[to_dual]
/--
theorem `Directed.isLUB_ciSup` / 定理 `Directed.isLUB_ciSup`

English:
theorem Directed.isLUB_ciSup
  statement: [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
  proof: hd.directedOn_range.isLUB_csSup (range_nonempty f) H

@[to_dual]

中文:
定理 Directed.isLUB_ciSup
  结论: [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
  证明: hd.directedOn_range.isLUB_csSup (range_nonempty f) H

@[to_dual]

Depends on / 依赖: directedOn_range, hd.directedOn_range.isLUB_csSup, isLUB_csSup, range_nonempty
-/
theorem Directed.isLUB_ciSup [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
    (H : BddAbove (range f)) : IsLUB (range f) (⨆ i, f i) :=
  hd.directedOn_range.isLUB_csSup (range_nonempty f) H

@[to_dual]
/--
theorem `DirectedOn.isLUB_ciSup_set` / 定理 `DirectedOn.isLUB_ciSup_set`

English:
theorem DirectedOn.isLUB_ciSup_set
  statement: {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
  proof: by
  rw [← sSup_image']
  exact hd.isLUB_csSup (Hne.image _) H

@[to_dual Directed.le_ciInf_iff]

中文:
定理 DirectedOn.isLUB_ciSup_set
  结论: {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
  证明: by
  rw [← sSup_image']
  exact hd.isLUB_csSup (Hne.image _) H

@[to_dual Directed.le_ciInf_iff]

Depends on / 依赖: Hne.image, hd.isLUB_csSup, isLUB_csSup, sSup_image
-/
theorem DirectedOn.isLUB_ciSup_set {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
    (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact hd.isLUB_csSup (Hne.image _) H

@[to_dual Directed.le_ciInf_iff]
/--
theorem `Directed.ciSup_le_iff` / 定理 `Directed.ciSup_le_iff`

English:
theorem Directed.ciSup_le_iff
  statement: [Nonempty ι] {f : ι -> α} {a : α}
  proof: (isLUB_le_iff <| hd.isLUB_ciSup hf).trans forall_mem_range

@[to_dual DirectedOn.le_ciInf_set_iff]

中文:
定理 Directed.ciSup_le_iff
  结论: [Nonempty ι] {f : ι -> α} {a : α}
  证明: (isLUB_le_iff <| hd.isLUB_ciSup hf).trans forall_mem_range

@[to_dual DirectedOn.le_ciInf_set_iff]

Depends on / 依赖: forall_mem_range, hd.isLUB_ciSup, isLUB_ciSup, isLUB_le_iff
-/
theorem Directed.ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α}
    (hd : Directed (· <= ·) f) (hf : BddAbove (range f)) :
    iSup f <= a ↔ forall i, f i <= a :=
  (isLUB_le_iff <| hd.isLUB_ciSup hf).trans forall_mem_range

@[to_dual DirectedOn.le_ciInf_set_iff]
/--
theorem `DirectedOn.ciSup_set_le_iff` / 定理 `DirectedOn.ciSup_set_le_iff`

English:
theorem DirectedOn.ciSup_set_le_iff
  statement: {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
  proof: (isLUB_le_iff <| hd.isLUB_ciSup_set hf hs).trans forall_mem_image

@[to_dual Directed.ciInf_le_of_le]

中文:
定理 DirectedOn.ciSup_set_le_iff
  结论: {ι : 类型} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
  证明: (isLUB_le_iff <| hd.isLUB_ciSup_set hf hs).trans forall_mem_image

@[to_dual Directed.ciInf_le_of_le]

Depends on / 依赖: forall_mem_image, hd.isLUB_ciSup_set, isLUB_ciSup_set, isLUB_le_iff
-/
theorem DirectedOn.ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
    (hd : DirectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s)) :
    ⨆ i : s, f i <= a ↔ forall i in s, f i <= a :=
  (isLUB_le_iff <| hd.isLUB_ciSup_set hf hs).trans forall_mem_image

@[to_dual Directed.ciInf_le_of_le]
/--
theorem `Directed.le_ciSup_of_le` / 定理 `Directed.le_ciSup_of_le`

English:
theorem Directed.le_ciSup_of_le
  statement: {f : ι -> α} (hd : Directed (· <= ·) f)
  proof: le_trans h (hd.le_ciSup H c)

中文:
定理 Directed.le_ciSup_of_le
  结论: {f : ι -> α} (hd : Directed (· <= ·) f)
  证明: le_trans h (hd.le_ciSup H c)

Depends on / 依赖: hd.le_ciSup, le_ciSup, le_trans
-/
theorem Directed.le_ciSup_of_le {f : ι -> α} (hd : Directed (· <= ·) f)
    (H : BddAbove (range f)) (c : ι) (h : a <= f c) : a <= iSup f :=
  le_trans h (hd.le_ciSup H c)

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[to_dual (attr := gcongr low)
/-- The indexed infimum of two functions are comparable if the functions are pointwise
comparable -/]
/--
theorem `Directed.ciSup_mono` / 定理 `Directed.ciSup_mono`

English:
theorem Directed.ciSup_mono
  statement: {f g : ι -> α} (hdf : Directed (· <= ·) f)
  proof: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact hdf.ciSup_le fun x => hdg.le_ciSup_of_le B x (H x)

@[to_dual DirectedOn.ciInf_set_le]

中文:
定理 Directed.ciSup_mono
  结论: {f g : ι -> α} (hdf : Directed (· <= ·) f)
  证明: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact hdf.ciSup_le fun x => hdg.le_ciSup_of_le B x (H x)

@[to_dual DirectedOn.ciInf_set_le]

Depends on / 依赖: ciSup_le, hdf.ciSup_le, hdg.le_ciSup_of_le, iSup_of_empty, isEmpty_or_nonempty, le_ciSup_of_le
-/
theorem Directed.ciSup_mono {f g : ι -> α} (hdf : Directed (· <= ·) f)
    (hdg : Directed (· <= ·) g) (B : BddAbove (range g)) (H : forall x, f x <= g x) :
    iSup f <= iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact hdf.ciSup_le fun x => hdg.le_ciSup_of_le B x (H x)

@[to_dual DirectedOn.ciInf_set_le]
/--
theorem `DirectedOn.le_ciSup_set` / 定理 `DirectedOn.le_ciSup_set`

English:
theorem DirectedOn.le_ciSup_set
  statement: {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
  proof: (hd.le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

@[to_dual (attr := simp)]

中文:
定理 DirectedOn.le_ciSup_set
  结论: {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
  证明: (hd.le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

@[to_dual (attr := simp)]

Depends on / 依赖: hd.le_csSup, le_csSup, mem_image_of_mem, sSup_image, trans_eq
-/
theorem DirectedOn.le_ciSup_set {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·) (f '' s))
    (H : BddAbove (f '' s)) {c : β} (hc : c in s) : f c <= ⨆ i : s, f i :=
  (hd.le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

@[to_dual (attr := simp)]
/--
theorem `ciSup_const` / 定理 `ciSup_const`

English:
theorem ciSup_const
  given: [hι : Nonempty ι] {a : α}
  statement: ⨆ _ : ι, a = a
  proof: by
  rw [iSup]; rw [range_const]; rw [csSup_singleton]

@[to_dual (attr := simp)]

中文:
定理 ciSup_const
  条件: [hι : Nonempty ι] {a : α}
  结论: ⨆ _ : ι, a = a
  证明: by
  rw [iSup]; rw [range_const]; rw [csSup_singleton]

@[to_dual (attr := simp)]

Depends on / 依赖: csSup_singleton, range_const
-/
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup]; rw [range_const]; rw [csSup_singleton]

@[to_dual (attr := simp)]
/--
theorem `ciSup_unique` / 定理 `ciSup_unique`

English:
theorem ciSup_unique
  given: [Unique ι] {s : ι -> α}
  statement: ⨆ i, s i = s default
  proof: by
  have : forall i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[to_dual]

中文:
定理 ciSup_unique
  条件: [Unique ι] {s : ι -> α}
  结论: ⨆ i, s i = s default
  证明: by
  have : forall i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[to_dual]

Depends on / 依赖: Unique, Unique.eq_default, ciSup_const, congr_arg, eq_default
-/
theorem ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s default := by
  have : forall i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[to_dual]
/--
theorem `ciSup_subsingleton` / 定理 `ciSup_subsingleton`

English:
theorem ciSup_subsingleton
  given: [Subsingleton ι] (i : ι) (s : ι -> α)
  statement: ⨆ i, s i = s i
  proof: @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[to_dual]

中文:
定理 ciSup_subsingleton
  条件: [Subsingleton ι] (i : ι) (s : ι -> α)
  结论: ⨆ i, s i = s i
  证明: @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[to_dual]

Depends on / 依赖: Subsingleton, Subsingleton.elim, ciSup_unique
-/
theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι -> α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[to_dual]
/--
theorem `ciSup_pos` / 定理 `ciSup_pos`

English:
theorem ciSup_pos
  given: {p : Prop} {f : p -> α} (hp : p)
  statement: ⨆ h : p, f h = f hp
  proof: by
  simp [hp]

@[to_dual]

中文:
定理 ciSup_pos
  条件: {p : 命题} {f : p -> α} (hp : p)
  结论: ⨆ h : p, f h = f hp
  证明: by
  simp [hp]

@[to_dual]
-/
theorem ciSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f hp := by
  simp [hp]

@[to_dual]
/--
lemma `ciSup_neg` / 引理 `ciSup_neg`

English:
lemma ciSup_neg
  given: {p : Prop} {f : p -> α} (hp : ¬ p)
  proof: by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

@[to_dual]

中文:
引理 ciSup_neg
  条件: {p : 命题} {f : p -> α} (hp : ¬ p)
  证明: by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

@[to_dual]

Depends on / 依赖: isEmpty_Prop, range_eq_empty_iff, repr_reindex_apply, smulTower, smulTower_repr
-/
lemma ciSup_neg {p : Prop} {f : p -> α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

@[to_dual]
/--
lemma `ciSup_eq_ite` / 引理 `ciSup_eq_ite`

English:
lemma ciSup_eq_ite
  given: {p : Prop} [Decidable p] {f : p -> α}
  proof: by
  by_cases H : p <;> simp [ciSup_neg, H]

@[to_dual]

中文:
引理 ciSup_eq_ite
  条件: {p : 命题} [Decidable p] {f : p -> α}
  证明: by
  by_cases H : p <;> simp [ciSup_neg, H]

@[to_dual]

Depends on / 依赖: _repr, b.smulTower, ciSup_neg, smulTower
-/
lemma ciSup_eq_ite {p : Prop} [Decidable p] {f : p -> α} :
    (⨆ h : p, f h) = if h : p then f h else sSup (∅ : Set α) := by
  by_cases H : p <;> simp [ciSup_neg, H]

@[to_dual]
/--
theorem `cbiSup_eq_of_forall` / 定理 `cbiSup_eq_of_forall`

English:
theorem cbiSup_eq_of_forall
  given: {p : ι -> Prop} {f : Subtype p -> α} (hp : forall i, p i)
  proof: by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

@[to_dual]

中文:
定理 cbiSup_eq_of_forall
  条件: {p : ι -> 命题} {f : Subtype p -> α} (hp : 对任意 i, p i)
  证明: by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

@[to_dual]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, ciSup_unique, reindex_apply, smulTower, smulTower_apply
-/
theorem cbiSup_eq_of_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : forall i, p i) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f := by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

@[to_dual]
/--
lemma `cbiSup_eq_of_forall_not` / 引理 `cbiSup_eq_of_forall_not`

English:
lemma cbiSup_eq_of_forall_not
  given: {p : ι -> Prop} {f : forall i, p i -> α} (hp : forall i, ¬p i)
  proof: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty']
  · have (i : ι) : IsEmpty (p i) := ⟨hp i⟩
    simp only [iSup_of_empty', ciSup_const]

@[to_dual]

中文:
引理 cbiSup_eq_of_forall_not
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α} (hp : 对任意 i, ¬p i)
  证明: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty']
  · have (i : ι) : IsEmpty (p i) := ⟨hp i⟩
    simp only [iSup_of_empty', ciSup_const]

@[to_dual]

Depends on / 依赖: IsEmpty, ciSup_const, iSup_of_empty, isEmpty_or_nonempty
-/
lemma cbiSup_eq_of_forall_not {p : ι -> Prop} {f : forall i, p i -> α} (hp : forall i, ¬p i) :
    ⨆ (i) (h : p i), f i h = sSup ∅ := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty']
  · have (i : ι) : IsEmpty (p i) := ⟨hp i⟩
    simp only [iSup_of_empty', ciSup_const]

@[to_dual]
/--
theorem `cbiSup_empty` / 定理 `cbiSup_empty`

English:
theorem cbiSup_empty
  given: {f : β -> α}
  statement: ⨆ i in (∅ : Set β), f i = sSup ∅
  proof: cbiSup_eq_of_forall_not Set.notMem_empty

中文:
定理 cbiSup_empty
  条件: {f : β -> α}
  结论: ⨆ i in (∅ : Set β), f i = sSup ∅
  证明: cbiSup_eq_of_forall_not Set.notMem_empty

Depends on / 依赖: Set.notMem_empty, cbiSup_eq_of_forall_not, notMem_empty
-/
theorem cbiSup_empty {f : β -> α} : ⨆ i in (∅ : Set β), f i = sSup ∅ :=
  cbiSup_eq_of_forall_not Set.notMem_empty

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual Directed.ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/]
/--
theorem `Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  statement: [Nonempty ι] {f : ι -> α}
  proof: hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f)
(forall_mem_range.mpr h₁) fun w hw => exists_range_iff.mpr h₂ w hw

中文:
定理 Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  结论: [Nonempty ι] {f : ι -> α}
  证明: hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f)
(forall_mem_range.mpr h₁) fun w hw => exists_range_iff.mpr h₂ w hw

Depends on / 依赖: csSup_eq_of_forall_le_of_forall_lt_exists_gt, directedOn_range, exists_range_iff, exists_range_iff.mpr, forall_mem_range, forall_mem_range.mpr, hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt, range_nonempty
-/
theorem Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι -> α}
    (hd : Directed (· <= ·) f) (h₁ : forall i, f i <= b) (h₂ : forall w, w < b -> exists i, w < f i) :
    ⨆ i : ι, f i = b :=
  hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f)
(forall_mem_range.mpr h₁) fun w hw => exists_range_iff.mpr h₂ w hw

/--
theorem `Monotone.ciSup_mem_iInter_Icc_of_antitone` / 定理 `Monotone.ciSup_mem_iInter_Icc_of_antitone`

English:
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone
  statement: [Preorder β] [IsDirectedOrder β]
  proof: by
  refine mem_iInter.2 fun n => ?_
  have : Nonempty β := ⟨n⟩
  have h₁ : forall m, f m <= g n := fun m => hf.forall_le_of_antitone hg h m n
  have h₂ : Directed (· <= ·) f := hf.directed_le
exact ⟨h₂.le_ciSup ⟨g n, forall_mem_range.2 h₁⟩ _, h₂.ciSup_le h₁⟩

中文:
定理 Monotone.ciSup_mem_iInter_Icc_of_antitone
  结论: [Preorder β] [IsDirectedOrder β]
  证明: by
  refine mem_iInter.2 fun n => ?_
  have : Nonempty β := ⟨n⟩
  have h₁ : forall m, f m <= g n := fun m => hf.forall_le_of_antitone hg h m n
  have h₂ : Directed (· <= ·) f := hf.directed_le
exact ⟨h₂.le_ciSup ⟨g n, forall_mem_range.2 h₁⟩ _, h₂.ciSup_le h₁⟩

Depends on / 依赖: Directed, Nonempty, ciSup_le, directed_le, forall_le_of_antitone, forall_mem_range, hf.directed_le, hf.forall_le_of_antitone, le_ciSup, mem_iInter
-/
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone [Preorder β] [IsDirectedOrder β]
    {f g : β -> α} (hf : Monotone f) (hg : Antitone g) (h : f <= g) :
    (⨆ n, f n) in ⋂ n, Icc (f n) (g n) := by
  refine mem_iInter.2 fun n => ?_
  have : Nonempty β := ⟨n⟩
  have h₁ : forall m, f m <= g n := fun m => hf.forall_le_of_antitone hg h m n
  have h₂ : Directed (· <= ·) f := hf.directed_le
exact ⟨h₂.le_ciSup ⟨g n, forall_mem_range.2 h₁⟩ _, h₂.ciSup_le h₁⟩

/--
theorem `ciSup_mem_iInter_Icc_of_antitone_Icc` / 定理 `ciSup_mem_iInter_Icc_of_antitone_Icc`

English:
theorem ciSup_mem_iInter_Icc_of_antitone_Icc
  statement: [Preorder β] [IsDirectedOrder β] {f g : β -> α}
  proof: Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

@[to_dual]

中文:
定理 ciSup_mem_iInter_Icc_of_antitone_Icc
  结论: [Preorder β] [IsDirectedOrder β] {f g : β -> α}
  证明: Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

@[to_dual]

Depends on / 依赖: Icc_subset_Icc_iff, Monotone, Monotone.ciSup_mem_iInter_Icc_of_antitone, ciSup_mem_iInter_Icc_of_antitone
-/
theorem ciSup_mem_iInter_Icc_of_antitone_Icc [Preorder β] [IsDirectedOrder β] {f g : β -> α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : forall n, f n <= g n) :
    (⨆ n, f n) in ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

@[to_dual]
/--
lemma `Directed.Ici_ciSup` / 引理 `Directed.Ici_ciSup`

English:
lemma Directed.Ici_ciSup
  statement: [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
  proof: by
  ext
  simpa using hd.ciSup_le_iff hf

@[to_dual]

中文:
引理 Directed.Ici_ciSup
  结论: [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
  证明: by
  ext
  simpa using hd.ciSup_le_iff hf

@[to_dual]

Depends on / 依赖: ciSup_le_iff, hd.ciSup_le_iff
-/
lemma Directed.Ici_ciSup [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f)
    (hf : BddAbove (range f)) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) := by
  ext
  simpa using hd.ciSup_le_iff hf

@[to_dual]
/--
theorem `ciSup_Iic` / 定理 `ciSup_Iic`

English:
theorem ciSup_Iic
  given: [Preorder β] {f : β -> α} (a : β) (hf : Monotone f)
  proof: by
  have hd : Directed (· <= ·) (fun x : Iic a => f x) := fun x y => ⟨⟨a, le_refl a⟩, ⟨hf x.2, hf y.2⟩⟩
  have H : BddAbove (range fun x : Iic a => f x) := ⟨f a, fun _ => by aesop⟩
  apply (hd.le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [hd.ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

中文:
定理 ciSup_Iic
  条件: [Preorder β] {f : β -> α} (a : β) (hf : Monotone f)
  证明: by
  have hd : Directed (· <= ·) (fun x : Iic a => f x) := fun x y => ⟨⟨a, le_refl a⟩, ⟨hf x.2, hf y.2⟩⟩
  have H : BddAbove (range fun x : Iic a => f x) := ⟨f a, fun _ => by aesop⟩
  apply (hd.le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [hd.ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

Depends on / 依赖: BddAbove, Directed, antisymm, ciSup_le_iff, hd.ciSup_le_iff, hd.le_ciSup, le_ciSup, le_refl
-/
theorem ciSup_Iic [Preorder β] {f : β -> α} (a : β) (hf : Monotone f) :
    ⨆ x : Iic a, f x = f a := by
  have hd : Directed (· <= ·) (fun x : Iic a => f x) := fun x y => ⟨⟨a, le_refl a⟩, ⟨hf x.2, hf y.2⟩⟩
  have H : BddAbove (range fun x : Iic a => f x) := ⟨f a, fun _ => by aesop⟩
  apply (hd.le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [hd.ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

end ConditionallyCompletePartialOrderSup

/--
lemma `Directed.ciInf_le_ciSup` / 引理 `Directed.ciInf_le_ciSup`

English:
lemma Directed.ciInf_le_ciSup
  statement: [ConditionallyCompletePartialOrder α] [Nonempty ι] {f : ι -> α}
  proof: (hd.ciInf_le hf (Classical.arbitrary _)).trans hd'.le_ciSup hf' (Classical.arbitrary _)

中文:
引理 Directed.ciInf_le_ciSup
  结论: [ConditionallyCompletePartialOrder α] [Nonempty ι] {f : ι -> α}
  证明: (hd.ciInf_le hf (Classical.arbitrary _)).trans hd'.le_ciSup hf' (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, ciInf_le, hd.ciInf_le, le_ciSup
-/
lemma Directed.ciInf_le_ciSup [ConditionallyCompletePartialOrder α] [Nonempty ι] {f : ι -> α}
    (hd : Directed (· >= ·) f) (hf : BddBelow (range f))
    (hd' : Directed (· <= ·) f) (hf' : BddAbove (range f)) :
    ⨅ i, f i <= ⨆ i, f i :=
(hd.ciInf_le hf (Classical.arbitrary _)).trans hd'.le_ciSup hf' (Classical.arbitrary _)

namespace GaloisConnection

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
    [Nonempty ι] {l : α -> β} {u : β -> α}

@[to_dual u_csInf_of_directedOn']
/--
theorem `l_csSup_of_directedOn'` / 定理 `l_csSup_of_directedOn'`

English:
theorem l_csSup_of_directedOn'
  statement: (gc : GaloisConnection l u) {s : Set α}
  proof: .unique gc.isLUB_l_image (hd.isLUB_csSup hne hbdd)
    (hd.mono_comp gc.monotone_l).isLUB_csSup (hne.image l) (gc.monotone_l.map_bddAbove hbdd)

@[to_dual u_csInf_of_directedOn]

中文:
定理 l_csSup_of_directedOn'
  结论: (gc : GaloisConnection l u) {s : Set α}
  证明: .unique gc.isLUB_l_image (hd.isLUB_csSup hne hbdd)
    (hd.mono_comp gc.monotone_l).isLUB_csSup (hne.image l) (gc.monotone_l.map_bddAbove hbdd)

@[to_dual u_csInf_of_directedOn]

Depends on / 依赖: gc.isLUB_l_image, gc.monotone_l, gc.monotone_l.map_bddAbove, hd.isLUB_csSup, hd.mono_comp, hne.image, isLUB_csSup, isLUB_l_image, map_bddAbove, mono_comp, monotone_l, unique
-/
theorem l_csSup_of_directedOn' (gc : GaloisConnection l u) {s : Set α}
    (hd : DirectedOn (· <= ·) s) (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) :=
.unique gc.isLUB_l_image (hd.isLUB_csSup hne hbdd)
    (hd.mono_comp gc.monotone_l).isLUB_csSup (hne.image l) (gc.monotone_l.map_bddAbove hbdd)

@[to_dual u_csInf_of_directedOn]
/--
theorem `l_csSup_of_directedOn` / 定理 `l_csSup_of_directedOn`

English:
theorem l_csSup_of_directedOn
  statement: (gc : GaloisConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s)
  proof: by
  simpa only [← comp_def, ← sSup_range, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq]
    using gc.l_csSup_of_directedOn' hd hne hbdd

@[to_dual u_ciInf_of_directed]

中文:
定理 l_csSup_of_directedOn
  结论: (gc : GaloisConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s)
  证明: by
  simpa only [← comp_def, ← sSup_range, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq]
    using gc.l_csSup_of_directedOn' hd hne hbdd

@[to_dual u_ciInf_of_directed]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, comp_def, gc.l_csSup_of_directedOn, l_csSup_of_directedOn, ofPred_mem_eq, range_coe_subtype, range_comp, sSup_range
-/
theorem l_csSup_of_directedOn (gc : GaloisConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x := by
  simpa only [← comp_def, ← sSup_range, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq]
    using gc.l_csSup_of_directedOn' hd hne hbdd

@[to_dual u_ciInf_of_directed]
/--
theorem `l_ciSup_of_directed` / 定理 `l_ciSup_of_directed`

English:
theorem l_ciSup_of_directed
  statement: (gc : GaloisConnection l u) {f : ι -> α} (hd : Directed (· <= ·) f)
  proof: by
  rw [iSup]; rw [gc.l_csSup_of_directedOn hd.directedOn_range (range_nonempty _) hf]; rw [iSup_range']

@[to_dual u_ciInf_set_of_directedOn]

中文:
定理 l_ciSup_of_directed
  结论: (gc : GaloisConnection l u) {f : ι -> α} (hd : Directed (· <= ·) f)
  证明: by
  rw [iSup]; rw [gc.l_csSup_of_directedOn hd.directedOn_range (range_nonempty _) hf]; rw [iSup_range']

@[to_dual u_ciInf_set_of_directedOn]

Depends on / 依赖: directedOn_range, gc.l_csSup_of_directedOn, hd.directedOn_range, iSup_range, l_csSup_of_directedOn, range_nonempty
-/
theorem l_ciSup_of_directed (gc : GaloisConnection l u) {f : ι -> α} (hd : Directed (· <= ·) f)
    (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i) := by
  rw [iSup]; rw [gc.l_csSup_of_directedOn hd.directedOn_range (range_nonempty _) hf]; rw [iSup_range']

@[to_dual u_ciInf_set_of_directedOn]
/--
theorem `l_ciSup_set_of_directedOn` / 定理 `l_ciSup_set_of_directedOn`

English:
theorem l_ciSup_set_of_directedOn
  statement: (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α}
  proof: by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  refine gc.l_ciSup_of_directed ?_ hf
  simpa [← directedOn_range, ← comp_def, range_comp]

中文:
定理 l_ciSup_set_of_directedOn
  结论: (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α}
  证明: by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  refine gc.l_ciSup_of_directed ?_ hf
  simpa [← directedOn_range, ← comp_def, range_comp]

Depends on / 依赖: comp_def, directedOn_range, gc.l_ciSup_of_directed, hne.to_subtype, image_eq_range, l_ciSup_of_directed, range_comp, to_subtype
-/
theorem l_ciSup_set_of_directedOn (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α}
    (hd : DirectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  refine gc.l_ciSup_of_directed ?_ hf
  simpa [← directedOn_range, ← comp_def, range_comp]

end Sup

end GaloisConnection

namespace OrderIso

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
  [Nonempty ι]

-- these need to have `directed` in their names.
@[to_dual]
/--
theorem `map_csSup_of_directedOn` / 定理 `map_csSup_of_directedOn`

English:
theorem map_csSup_of_directedOn
  statement: (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
  proof: e.to_galoisConnection.l_csSup_of_directedOn hd hne hbdd

@[to_dual]

中文:
定理 map_csSup_of_directedOn
  结论: (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
  证明: e.to_galoisConnection.l_csSup_of_directedOn hd hne hbdd

@[to_dual]

Depends on / 依赖: e.to_galoisConnection.l_csSup_of_directedOn, l_csSup_of_directedOn, to_galoisConnection
-/
theorem map_csSup_of_directedOn (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup_of_directedOn hd hne hbdd

@[to_dual]
/--
theorem `map_csSup_of_directedOn'` / 定理 `map_csSup_of_directedOn'`

English:
theorem map_csSup_of_directedOn'
  statement: (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
  proof: e.to_galoisConnection.l_csSup_of_directedOn' hd hne hbdd

@[to_dual]

中文:
定理 map_csSup_of_directedOn'
  结论: (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
  证明: e.to_galoisConnection.l_csSup_of_directedOn' hd hne hbdd

@[to_dual]

Depends on / 依赖: e.to_galoisConnection.l_csSup_of_directedOn, l_csSup_of_directedOn, to_galoisConnection
-/
theorem map_csSup_of_directedOn' (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup_of_directedOn' hd hne hbdd

@[to_dual]
/--
theorem `map_ciSup_of_directed` / 定理 `map_ciSup_of_directed`

English:
theorem map_ciSup_of_directed
  statement: (e : α ≃o β) {f : ι -> α} (hd : Directed (· <= ·) f)
  proof: e.to_galoisConnection.l_ciSup_of_directed hd hf

@[to_dual]

中文:
定理 map_ciSup_of_directed
  结论: (e : α ≃o β) {f : ι -> α} (hd : Directed (· <= ·) f)
  证明: e.to_galoisConnection.l_ciSup_of_directed hd hf

@[to_dual]

Depends on / 依赖: e.to_galoisConnection.l_ciSup_of_directed, l_ciSup_of_directed, to_galoisConnection
-/
theorem map_ciSup_of_directed (e : α ≃o β) {f : ι -> α} (hd : Directed (· <= ·) f)
    (hf : BddAbove (range f)) : e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup_of_directed hd hf

@[to_dual]
/--
theorem `map_ciSup_set_of_directedOn` / 定理 `map_ciSup_set_of_directedOn`

English:
theorem map_ciSup_set_of_directedOn
  statement: (e : α ≃o β) {s : Set γ} {f : γ -> α}
  proof: e.to_galoisConnection.l_ciSup_set_of_directedOn hd hf hne

中文:
定理 map_ciSup_set_of_directedOn
  结论: (e : α ≃o β) {s : Set γ} {f : γ -> α}
  证明: e.to_galoisConnection.l_ciSup_set_of_directedOn hd hf hne

Depends on / 依赖: e.to_galoisConnection.l_ciSup_set_of_directedOn, l_ciSup_set_of_directedOn, to_galoisConnection
-/
theorem map_ciSup_set_of_directedOn (e : α ≃o β) {s : Set γ} {f : γ -> α}
    (hd : DirectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s)) (hne : s.Nonempty) :
    e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set_of_directedOn hd hf hne

end Sup

end OrderIso
