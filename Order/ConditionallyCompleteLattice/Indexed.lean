/-
Copyright (c) 2018 Sébastian Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastian Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete,
rather than complete, lattice. We add a prefix `c` to distinguish them from the versions for
complete lattices, giving names `ciSup_xxx` or `ciInf_xxx`.
-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `iSup` and `iInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

@[simp]
/--
theorem `WithTop.iInf_empty` / 定理 `WithTop.iInf_empty`

English:
theorem WithTop.iInf_empty
  given: [IsEmpty ι] [InfSet α] (f : ι -> WithTop α)
  proof: by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]

中文:
定理 WithTop.iInf_empty
  条件: [是空 ι] [下确界集 α] (f : ι -> WithTop α)
  证明: by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]

Depends on / 依赖: WithTop, WithTop.sInf_empty, range_eq_empty, sInf_empty
-/
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι -> WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]
/--
theorem `WithTop.coe_iInf` / 定理 `WithTop.coe_iInf`

English:
theorem WithTop.coe_iInf
  given: [Nonempty ι] [InfSet α] {f : ι -> α} (hf : BddBelow (range f))
  proof: by
  rw [iInf]; rw [iInf]; rw [WithTop.coe_sInf' (range_nonempty f) hf]; rw [← range_comp]; rw [Function.comp_def]

@[norm_cast]

中文:
定理 WithTop.coe_iInf
  条件: [非空 ι] [下确界集 α] {f : ι -> α} (hf : BddBelow (range f))
  证明: by
  rw [iInf]; rw [iInf]; rw [WithTop.coe_sInf' (range_nonempty f) hf]; rw [← range_comp]; rw [Function.comp_def]

@[norm_cast]

Depends on / 依赖: Function, Function.comp_def, WithTop, WithTop.coe_sInf, coe_sInf, comp_def, range_comp, range_nonempty
-/
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι -> α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf]; rw [iInf]; rw [WithTop.coe_sInf' (range_nonempty f) hf]; rw [← range_comp]; rw [Function.comp_def]

@[norm_cast]
/--
theorem `WithTop.coe_iSup` / 定理 `WithTop.coe_iSup`

English:
theorem WithTop.coe_iSup
  given: [SupSet α] (f : ι -> α) (h : BddAbove (Set.range f))
  proof: by
  rw [iSup]; rw [iSup]; rw [WithTop.coe_sSup' h]; rw [← range_comp]; rw [Function.comp_def]

@[simp]

中文:
定理 WithTop.coe_iSup
  条件: [上确界集 α] (f : ι -> α) (h : BddAbove (集合.range f))
  证明: by
  rw [iSup]; rw [iSup]; rw [WithTop.coe_sSup' h]; rw [← range_comp]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, WithTop, WithTop.coe_sSup, coe_sSup, comp_def, range_comp
-/
theorem WithTop.coe_iSup [SupSet α] (f : ι -> α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup]; rw [iSup]; rw [WithTop.coe_sSup' h]; rw [← range_comp]; rw [Function.comp_def]

@[simp]
/--
theorem `WithBot.ciSup_empty` / 定理 `WithBot.ciSup_empty`

English:
theorem WithBot.ciSup_empty
  given: [IsEmpty ι] [SupSet α] (f : ι -> WithBot α)
  proof: WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]

中文:
定理 WithBot.ciSup_empty
  条件: [是空 ι] [上确界集 α] (f : ι -> WithBot α)
  证明: WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]

Depends on / 依赖: WithTop, WithTop.iInf_empty, iInf_empty
-/
theorem WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι -> WithBot α) :
    ⨆ i, f i = ⊥ :=
  WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]
/--
theorem `WithBot.coe_iSup` / 定理 `WithBot.coe_iSup`

English:
theorem WithBot.coe_iSup
  given: [Nonempty ι] [SupSet α] {f : ι -> α} (hf : BddAbove (range f))
  proof: WithTop.coe_iInf (α := αᵒᵈ) hf

中文:
定理 WithBot.coe_iSup
  条件: [非空 ι] [上确界集 α] {f : ι -> α} (hf : BddAbove (range f))
  证明: WithTop.coe_iInf (α := αᵒᵈ) hf

Depends on / 依赖: WithTop, WithTop.coe_iInf, coe_iInf
-/
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} (hf : BddAbove (range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithTop.coe_iInf (α := αᵒᵈ) hf

/--
theorem `WithBot.coe_biSup` / 定理 `WithBot.coe_biSup`

English:
theorem WithBot.coe_biSup
  statement: {ι : Type*} {s : Set ι} (hs : s.Nonempty)
  proof: by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i => ?_) <| iSup_le_iff.mpr <| fun _ => iSup_le_iff.mpr <|
      fun hi => WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i in

中文:
定理 WithBot.coe_biSup
  结论: {ι : 类型} {s : 集合 ι} (hs : s.非空)
  证明: by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i => ?_) <| iSup_le_iff.mpr <| fun _ => iSup_le_iff.mpr <|
      fun hi => WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i in

Depends on / 依赖: Nonempty, Nonempty.intro, OrderTop, OrderTop.bddAbove, WithBot, WithBot.coe_iSup, WithBot.coe_le_coe.mpr, bddAbove, coe_iSup, coe_le_coe, iSup_le_iff, iSup_le_iff.mpr, iSup_neg, iSup_pos, le_antisymm, le_biSup, le_trans, trans_le
-/
theorem WithBot.coe_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty)
    {α : Type*} [CompleteLattice α] (f : ι -> α) :
    ⨆ i in s, f i = ⨆ i in s, (f i : WithBot α) := by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i => ?_) <| iSup_le_iff.mpr <| fun _ => iSup_le_iff.mpr <|
      fun hi => WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i in s
  · simpa only [iSup_pos h] using by apply le_biSup _ h
  · simpa only [iSup_neg h] using le_trans (by simp) (le_biSup _ hj)

@[norm_cast]
/--
theorem `WithBot.coe_iInf` / 定理 `WithBot.coe_iInf`

English:
theorem WithBot.coe_iInf
  given: [InfSet α] (f : ι -> α) (h : BddBelow (Set.range f))
  proof: WithTop.coe_iSup (α := αᵒᵈ) _ h

中文:
定理 WithBot.coe_iInf
  条件: [下确界集 α] (f : ι -> α) (h : BddBelow (集合.range f))
  证明: WithTop.coe_iSup (α := αᵒᵈ) _ h

Depends on / 依赖: WithTop, WithTop.coe_iSup, coe_iSup
-/
theorem WithBot.coe_iInf [InfSet α] (f : ι -> α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  WithTop.coe_iSup (α := αᵒᵈ) _ h

/--
theorem `WithBot.coe_biInf` / 定理 `WithBot.coe_biInf`

English:
theorem WithBot.coe_biInf
  given: {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] (f : ι -> α)
  proof: by
refine le_antisymm (by simpa using fun _ => biInf_le _)
    (le_iInf_iff.mpr fun i => ?_).trans_eq (WithBot.coe_iInf _ (OrderBot.bddBelow _)).symm
  by_cases h : i in s
  · simpa only [iInf_pos h] using by apply biInf_le _ h
  · simp [iInf_neg h]

中文:
定理 WithBot.coe_biInf
  条件: {ι : 类型} {s : 集合 ι} {α : 类型} [完备格 α] (f : ι -> α)
  证明: by
refine le_antisymm (by simpa using fun _ => biInf_le _)
    (le_iInf_iff.mpr fun i => ?_).trans_eq (WithBot.coe_iInf _ (OrderBot.bddBelow _)).symm
  by_cases h : i in s
  · simpa only [iInf_pos h] using by apply biInf_le _ h
  · simp [iInf_neg h]

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WithBot, WithBot.coe_iInf, bddBelow, biInf_le, coe_iInf, iInf_neg, iInf_pos, le_antisymm, le_iInf_iff, le_iInf_iff.mpr, trans_eq
-/
theorem WithBot.coe_biInf {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] (f : ι -> α) :
    ⨅ i in s, f i = ⨅ i in s, (f i : WithBot α) := by
refine le_antisymm (by simpa using fun _ => biInf_le _)
    (le_iInf_iff.mpr fun i => ?_).trans_eq (WithBot.coe_iInf _ (OrderBot.bddBelow _)).symm
  by_cases h : i in s
  · simpa only [iInf_pos h] using by apply biInf_le _ h
  · simp [iInf_neg h]

end

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {a b : α}

/--
theorem `isLUB_ciSup` / 定理 `isLUB_ciSup`

English:
theorem isLUB_ciSup
  given: [Nonempty ι] {f : ι -> α} (H : BddAbove (range f))
  proof: isLUB_csSup (range_nonempty f) H

中文:
定理 isLUB_ciSup
  条件: [非空 ι] {f : ι -> α} (H : BddAbove (range f))
  证明: isLUB_csSup (range_nonempty f) H

Depends on / 依赖: isLUB_csSup, range_nonempty
-/
theorem isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H

/--
theorem `isLUB_ciSup_set` / 定理 `isLUB_ciSup_set`

English:
theorem isLUB_ciSup_set
  given: {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty)
  proof: by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

中文:
定理 isLUB_ciSup_set
  条件: {f : β -> α} {s : 集合 β} (H : BddAbove (f '' s)) (Hne : s.非空)
  证明: by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

Depends on / 依赖: Hne.image, Linear, isLUB_csSup, sSup_image
-/
theorem isLUB_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

/--
theorem `isGLB_ciInf` / 定理 `isGLB_ciInf`

English:
theorem isGLB_ciInf
  given: [Nonempty ι] {f : ι -> α} (H : BddBelow (range f))
  proof: isGLB_csInf (range_nonempty f) H

中文:
定理 isGLB_ciInf
  条件: [非空 ι] {f : ι -> α} (H : BddBelow (range f))
  证明: isGLB_csInf (range_nonempty f) H

Depends on / 依赖: isGLB_csInf, range_nonempty
-/
theorem isGLB_ciInf [Nonempty ι] {f : ι -> α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H

/--
theorem `isGLB_ciInf_set` / 定理 `isGLB_ciInf_set`

English:
theorem isGLB_ciInf_set
  given: {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty)
  proof: isLUB_ciSup_set (α := αᵒᵈ) H Hne

中文:
定理 isGLB_ciInf_set
  条件: {f : β -> α} {s : 集合 β} (H : BddBelow (f '' s)) (Hne : s.非空)
  证明: isLUB_ciSup_set (α := αᵒᵈ) H Hne

Depends on / 依赖: isLUB_ciSup_set
-/
theorem isGLB_ciInf_set {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  isLUB_ciSup_set (α := αᵒᵈ) H Hne

/--
theorem `ciSup_le_iff` / 定理 `ciSup_le_iff`

English:
theorem ciSup_le_iff
  given: [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAbove (range f))
  proof: (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

中文:
定理 ciSup_le_iff
  条件: [非空 ι] {f : ι -> α} {a : α} (hf : BddAbove (range f))
  证明: (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

Depends on / 依赖: forall_mem_range, isLUB_ciSup, isLUB_le_iff
-/
theorem ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAbove (range f)) :
    iSup f <= a ↔ forall i, f i <= a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

/--
theorem `le_ciInf_iff` / 定理 `le_ciInf_iff`

English:
theorem le_ciInf_iff
  given: [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBelow (range f))
  proof: (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

中文:
定理 le_ciInf_iff
  条件: [非空 ι] {f : ι -> α} {a : α} (hf : BddBelow (range f))
  证明: (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

Depends on / 依赖: forall_mem_range, isGLB_ciInf, le_isGLB_iff
-/
theorem le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBelow (range f)) :
    a <= iInf f ↔ forall i, a <= f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

/--
theorem `ciSup_set_le_iff` / 定理 `ciSup_set_le_iff`

English:
theorem ciSup_set_le_iff
  statement: {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
  proof: (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

中文:
定理 ciSup_set_le_iff
  结论: {ι : 类型} {s : 集合 ι} {f : ι -> α} {a : α} (hs : s.非空)
  证明: (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

Depends on / 依赖: forall_mem_image, isLUB_ciSup_set, isLUB_le_iff
-/
theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i <= a ↔ forall i in s, f i <= a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

/--
theorem `le_ciInf_set_iff` / 定理 `le_ciInf_set_iff`

English:
theorem le_ciInf_set_iff
  statement: {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
  proof: (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

中文:
定理 le_ciInf_set_iff
  结论: {ι : 类型} {s : 集合 ι} {f : ι -> α} {a : α} (hs : s.非空)
  证明: (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

Depends on / 依赖: forall_mem_image, isGLB_ciInf_set, le_isGLB_iff
-/
theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a <= ⨅ i : s, f i) ↔ forall i in s, a <= f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

/--
theorem `IsLUB.ciSup_eq` / 定理 `IsLUB.ciSup_eq`

English:
theorem IsLUB.ciSup_eq
  given: [Nonempty ι] {f : ι -> α} (H : IsLUB (range f) a)
  statement: ⨆ i, f i = a
  proof: H.csSup_eq (range_nonempty f)

中文:
定理 IsLUB.ciSup_eq
  条件: [非空 ι] {f : ι -> α} (H : IsLUB (range f) a)
  结论: ⨆ i, f i = a
  证明: H.csSup_eq (range_nonempty f)

Depends on / 依赖: H.csSup_eq, csSup_eq, range_nonempty
-/
theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι -> α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)

/--
theorem `IsLUB.ciSup_set_eq` / 定理 `IsLUB.ciSup_set_eq`

English:
theorem IsLUB.ciSup_set_eq
  given: {s : Set β} {f : β -> α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty)
  proof: IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

中文:
定理 IsLUB.ciSup_set_eq
  条件: {s : 集合 β} {f : β -> α} (H : IsLUB (f '' s) a) (Hne : s.非空)
  证明: IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

Depends on / 依赖: Hne.image, IsLUB.csSup_eq, csSup_eq, image_eq_range
-/
theorem IsLUB.ciSup_set_eq {s : Set β} {f : β -> α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/--
theorem `IsGLB.ciInf_eq` / 定理 `IsGLB.ciInf_eq`

English:
theorem IsGLB.ciInf_eq
  given: [Nonempty ι] {f : ι -> α} (H : IsGLB (range f) a)
  statement: ⨅ i, f i = a
  proof: H.csInf_eq (range_nonempty f)

中文:
定理 IsGLB.ciInf_eq
  条件: [非空 ι] {f : ι -> α} (H : IsGLB (range f) a)
  结论: ⨅ i, f i = a
  证明: H.csInf_eq (range_nonempty f)

Depends on / 依赖: H.csInf_eq, csInf_eq, range_nonempty
-/
theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι -> α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)

/--
theorem `IsGLB.ciInf_set_eq` / 定理 `IsGLB.ciInf_set_eq`

English:
theorem IsGLB.ciInf_set_eq
  given: {s : Set β} {f : β -> α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty)
  proof: IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

中文:
定理 IsGLB.ciInf_set_eq
  条件: {s : 集合 β} {f : β -> α} (H : IsGLB (f '' s) a) (Hne : s.非空)
  证明: IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

Depends on / 依赖: Hne.image, IsGLB.csInf_eq, csInf_eq, image_eq_range
-/
theorem IsGLB.ciInf_set_eq {s : Set β} {f : β -> α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/--
theorem `ciSup_le` / 定理 `ciSup_le`

English:
theorem ciSup_le
  given: [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x <= c)
  statement: iSup f <= c
  proof: csSup_le (range_nonempty f) (by rwa [forall_mem_range])

中文:
定理 ciSup_le
  条件: [非空 ι] {f : ι -> α} {c : α} (H : 对任意 x, f x <= c)
  结论: iSup f <= c
  证明: csSup_le (range_nonempty f) (by rwa [forall_mem_range])

Depends on / 依赖: csSup_le, forall_mem_range, range_nonempty
-/
theorem ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x <= c) : iSup f <= c :=
  csSup_le (range_nonempty f) (by rwa [forall_mem_range])

/--
theorem `le_ciSup` / 定理 `le_ciSup`

English:
theorem le_ciSup
  given: {f : ι -> α} (H : BddAbove (range f)) (c : ι)
  statement: f c <= iSup f
  proof: le_csSup H (mem_range_self _)

中文:
定理 le_ciSup
  条件: {f : ι -> α} (H : BddAbove (range f)) (c : ι)
  结论: f c <= iSup f
  证明: le_csSup H (mem_range_self _)

Depends on / 依赖: le_csSup, mem_range_self
-/
theorem le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <= iSup f :=
  le_csSup H (mem_range_self _)

/--
theorem `le_ciSup_of_le` / 定理 `le_ciSup_of_le`

English:
theorem le_ciSup_of_le
  given: {f : ι -> α} (H : BddAbove (range f)) (c : ι) (h : a <= f c)
  statement: a <= iSup f
  proof: le_trans h (le_ciSup H c)

中文:
定理 le_ciSup_of_le
  条件: {f : ι -> α} (H : BddAbove (range f)) (c : ι) (h : a <= f c)
  结论: a <= iSup f
  证明: le_trans h (le_ciSup H c)

Depends on / 依赖: le_ciSup, le_trans
-/
theorem le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c : ι) (h : a <= f c) : a <= iSup f :=
  le_trans h (le_ciSup H c)

/--
theorem `BddAbove.range_iSup_of_iUnion_range` / 定理 `BddAbove.range_iSup_of_iUnion_range`

English:
theorem BddAbove.range_iSup_of_iUnion_range
  statement: {κ : ι -> Sort*} {f : forall i, κ i -> α}
  proof: by
  have ⟨a, h⟩ := H
  refine ⟨a ⊔ (sSup ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iSup_of_empty' (f i) ▸ le_sup_right
exact ciSup_le fun j => le_sup_of_le_left h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

中文:
定理 BddAbove.range_iSup_of_iUnion_range
  结论: {κ : ι -> 类型层*} {f : 对任意 i, κ i -> α}
  证明: by
  have ⟨a, h⟩ := H
  refine ⟨a ⊔ (sSup ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iSup_of_empty' (f i) ▸ le_sup_right
exact ciSup_le fun j => le_sup_of_le_left h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

Depends on / 依赖: ciSup_le, iSup_of_empty, isEmpty_or_nonempty, le_sup_of_le_left, le_sup_right
-/
theorem BddAbove.range_iSup_of_iUnion_range {κ : ι -> Sort*} {f : forall i, κ i -> α}
(H : BddAbove <| ⋃ i, range (f i)) : BddAbove range fun i => ⨆ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊔ (sSup ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iSup_of_empty' (f i) ▸ le_sup_right
exact ciSup_le fun j => le_sup_of_le_left h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

/--
theorem `le_ciSup₂` / 定理 `le_ciSup₂`

English:
theorem le_ciSup₂
  statement: {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddAbove <| ⋃ i, range (f i)) (i : ι)
  proof: le_ciSup_of_le H.range_iSup_of_iUnion_range i
    le_ciSup (H.mono <| subset_iUnion (range <| f ·) i) j

中文:
定理 le_ciSup₂
  结论: {κ : ι -> 类型层*} {f : 对任意 i, κ i -> α} (H : BddAbove <| ⋃ i, range (f i)) (i : ι)
  证明: le_ciSup_of_le H.range_iSup_of_iUnion_range i
    le_ciSup (H.mono <| subset_iUnion (range <| f ·) i) j

Depends on / 依赖: H.mono, H.range_iSup_of_iUnion_range, le_ciSup, le_ciSup_of_le, range_iSup_of_iUnion_range, subset_iUnion
-/
theorem le_ciSup₂ {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddAbove <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : f i j <= ⨆ (i) (j), f i j :=
le_ciSup_of_le H.range_iSup_of_iUnion_range i
    le_ciSup (H.mono <| subset_iUnion (range <| f ·) i) j

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
/--
theorem `ciSup_mono` / 定理 `ciSup_mono`

English:
theorem ciSup_mono
  given: {f g : ι -> α} (B : BddAbove (range g)) (H : forall x, f x <= g x)
  proof: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

中文:
定理 ciSup_mono
  条件: {f g : ι -> α} (B : BddAbove (range g)) (H : 对任意 x, f x <= g x)
  证明: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

Depends on / 依赖: ciSup_le, iSup_of_empty, isEmpty_or_nonempty, le_ciSup_of_le
-/
theorem ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : forall x, f x <= g x) :
    iSup f <= iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

/--
theorem `ciSup_sup_eq` / 定理 `ciSup_sup_eq`

English:
theorem ciSup_sup_eq
  given: {f g : ι -> α} (Hf : BddAbove <| range f) (Hg : BddAbove <| range g)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [iSup_of_empty']
apply le_antisymm ciSup_le fun x => sup_le_sup (le_ciSup Hf x) (le_ciSup Hg x)
  have := bbdAbove_range_sup Hf Hg
  exact sup_le (ciSup_mono this fun _ => le_sup_left) (ciSup_mono this fun _ => le_sup_right)

中文:
定理 ciSup_sup_eq
  条件: {f g : ι -> α} (Hf : BddAbove <| range f) (Hg : BddAbove <| range g)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [iSup_of_empty']
apply le_antisymm ciSup_le fun x => sup_le_sup (le_ciSup Hf x) (le_ciSup Hg x)
  have := bbdAbove_range_sup Hf Hg
  exact sup_le (ciSup_mono this fun _ => le_sup_left) (ciSup_mono this fun _ => le_sup_right)

Depends on / 依赖: bbdAbove_range_sup, ciSup_le, ciSup_mono, iSup_of_empty, isEmpty_or_nonempty, le_antisymm, le_ciSup, le_sup_left, le_sup_right, sup_le, sup_le_sup
-/
theorem ciSup_sup_eq {f g : ι -> α} (Hf : BddAbove <| range f) (Hg : BddAbove <| range g) :
    ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x) := by
  cases isEmpty_or_nonempty ι
  · simp [iSup_of_empty']
apply le_antisymm ciSup_le fun x => sup_le_sup (le_ciSup Hf x) (le_ciSup Hg x)
  have := bbdAbove_range_sup Hf Hg
  exact sup_le (ciSup_mono this fun _ => le_sup_left) (ciSup_mono this fun _ => le_sup_right)

/--
theorem `le_ciSup_set` / 定理 `le_ciSup_set`

English:
theorem le_ciSup_set
  given: {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c in s)
  proof: (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

中文:
定理 le_ciSup_set
  条件: {f : β -> α} {s : 集合 β} (H : BddAbove (f '' s)) {c : β} (hc : c in s)
  证明: (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

Depends on / 依赖: IsScalarTower, le_csSup, mem_image_of_mem, sSup_image, trans_eq
-/
theorem le_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c in s) :
    f c <= ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
/--
theorem `ciInf_mono` / 定理 `ciInf_mono`

English:
theorem ciInf_mono
  given: {f g : ι -> α} (B : BddBelow (range f)) (H : forall x, f x <= g x)
  statement: iInf f <= iInf g
  proof: ciSup_mono (α := αᵒᵈ) B H

中文:
定理 ciInf_mono
  条件: {f g : ι -> α} (B : BddBelow (range f)) (H : 对任意 x, f x <= g x)
  结论: iInf f <= iInf g
  证明: ciSup_mono (α := αᵒᵈ) B H

Depends on / 依赖: SMulCommClass, ciSup_mono
-/
theorem ciInf_mono {f g : ι -> α} (B : BddBelow (range f)) (H : forall x, f x <= g x) : iInf f <= iInf g :=
  ciSup_mono (α := αᵒᵈ) B H

/--
theorem `ciInf_inf_eq` / 定理 `ciInf_inf_eq`

English:
theorem ciInf_inf_eq
  given: {f g : ι -> α} (Hf : BddBelow <| range f) (Hg : BddBelow <| range g)
  proof: ciSup_sup_eq (α := αᵒᵈ) Hf Hg

中文:
定理 ciInf_inf_eq
  条件: {f g : ι -> α} (Hf : BddBelow <| range f) (Hg : BddBelow <| range g)
  证明: ciSup_sup_eq (α := αᵒᵈ) Hf Hg

Depends on / 依赖: ciSup_sup_eq
-/
theorem ciInf_inf_eq {f g : ι -> α} (Hf : BddBelow <| range f) (Hg : BddBelow <| range g) :
    ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ (⨅ x, g x) :=
  ciSup_sup_eq (α := αᵒᵈ) Hf Hg

/--
theorem `le_ciInf` / 定理 `le_ciInf`

English:
theorem le_ciInf
  given: [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <= f x)
  statement: c <= iInf f
  proof: ciSup_le (α := αᵒᵈ) H

中文:
定理 le_ciInf
  条件: [非空 ι] {f : ι -> α} {c : α} (H : 对任意 x, c <= f x)
  结论: c <= iInf f
  证明: ciSup_le (α := αᵒᵈ) H

Depends on / 依赖: ciSup_le
-/
theorem le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <= f x) : c <= iInf f :=
  ciSup_le (α := αᵒᵈ) H

/--
theorem `ciInf_le` / 定理 `ciInf_le`

English:
theorem ciInf_le
  given: {f : ι -> α} (H : BddBelow (range f)) (c : ι)
  statement: iInf f <= f c
  proof: le_ciSup (α := αᵒᵈ) H c

中文:
定理 ciInf_le
  条件: {f : ι -> α} (H : BddBelow (range f)) (c : ι)
  结论: iInf f <= f c
  证明: le_ciSup (α := αᵒᵈ) H c

Depends on / 依赖: le_ciSup
-/
theorem ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf f <= f c :=
  le_ciSup (α := αᵒᵈ) H c

/--
theorem `ciInf_le_of_le` / 定理 `ciInf_le_of_le`

English:
theorem ciInf_le_of_le
  given: {f : ι -> α} (H : BddBelow (range f)) (c : ι) (h : f c <= a)
  statement: iInf f <= a
  proof: le_ciSup_of_le (α := αᵒᵈ) H c h

中文:
定理 ciInf_le_of_le
  条件: {f : ι -> α} (H : BddBelow (range f)) (c : ι) (h : f c <= a)
  结论: iInf f <= a
  证明: le_ciSup_of_le (α := αᵒᵈ) H c h

Depends on / 依赖: le_ciSup_of_le
-/
theorem ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) (h : f c <= a) : iInf f <= a :=
  le_ciSup_of_le (α := αᵒᵈ) H c h

/--
theorem `ciSup_mono_of_forall_exists` / 定理 `ciSup_mono_of_forall_exists`

English:
theorem ciSup_mono_of_forall_exists
  statement: {ι'} [Nonempty ι] {f : ι -> α} {g : ι' -> α}
  proof: .elim le_ciSup_of_le hg ciSup_le fun i => h i

中文:
定理 ciSup_mono_of_对任意_存在
  结论: {ι'} [非空 ι] {f : ι -> α} {g : ι' -> α}
  证明: .elim le_ciSup_of_le hg ciSup_le fun i => h i

Depends on / 依赖: ciSup_le, le_ciSup_of_le
-/
theorem ciSup_mono_of_forall_exists {ι'} [Nonempty ι] {f : ι -> α} {g : ι' -> α}
    (hg : BddAbove <| range g) (h : forall i, exists i', f i <= g i') : ⨆ i, f i <= ⨆ i', g i' :=
.elim le_ciSup_of_le hg ciSup_le fun i => h i

/--
theorem `ciInf_mono_of_forall_exists` / 定理 `ciInf_mono_of_forall_exists`

English:
theorem ciInf_mono_of_forall_exists
  statement: {ι'} [Nonempty ι'] {f : ι -> α} {g : ι' -> α}
  proof: ciSup_mono_of_forall_exists (α := αᵒᵈ) hf h

中文:
定理 ciInf_mono_of_对任意_存在
  结论: {ι'} [非空 ι'] {f : ι -> α} {g : ι' -> α}
  证明: ciSup_mono_of_forall_exists (α := αᵒᵈ) hf h

Depends on / 依赖: ciSup_mono_of_forall_exists
-/
theorem ciInf_mono_of_forall_exists {ι'} [Nonempty ι'] {f : ι -> α} {g : ι' -> α}
    (hf : BddBelow <| range f) (h : forall i', exists i, f i <= g i') : ⨅ i, f i <= ⨅ i', g i' :=
  ciSup_mono_of_forall_exists (α := αᵒᵈ) hf h

/--
theorem `BddBelow.range_iInf_of_iUnion_range` / 定理 `BddBelow.range_iInf_of_iUnion_range`

English:
theorem BddBelow.range_iInf_of_iUnion_range
  statement: {κ : ι -> Sort*} {f : forall i, κ i -> α}
  proof: by
  have ⟨a, h⟩ := H
  refine ⟨a ⊓ (sInf ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iInf_of_isEmpty (f i) ▸ inf_le_right
exact le_ciInf fun j => inf_le_of_left_le h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

中文:
定理 BddBelow.range_iInf_of_iUnion_range
  结论: {κ : ι -> 类型层*} {f : 对任意 i, κ i -> α}
  证明: by
  have ⟨a, h⟩ := H
  refine ⟨a ⊓ (sInf ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iInf_of_isEmpty (f i) ▸ inf_le_right
exact le_ciInf fun j => inf_le_of_left_le h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

Depends on / 依赖: iInf_of_isEmpty, inf_le_of_left_le, inf_le_right, isEmpty_or_nonempty, le_ciInf
-/
theorem BddBelow.range_iInf_of_iUnion_range {κ : ι -> Sort*} {f : forall i, κ i -> α}
(H : BddBelow <| ⋃ i, range (f i)) : BddBelow range fun i => ⨅ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊓ (sInf ∅), fun x ⟨i, hx⟩ => hx ▸ ?_⟩
cases isEmpty_or_nonempty κ i
  · exact iInf_of_isEmpty (f i) ▸ inf_le_right
exact le_ciInf fun j => inf_le_of_left_le h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

/--
theorem `ciInf₂_le` / 定理 `ciInf₂_le`

English:
theorem ciInf₂_le
  statement: {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddBelow <| ⋃ i, range (f i)) (i : ι)
  proof: ciInf_le_of_le H.range_iInf_of_iUnion_range i
    ciInf_le (H.mono <| subset_iUnion (range <| f ·) i) j

中文:
定理 ciInf₂_le
  结论: {κ : ι -> 类型层*} {f : 对任意 i, κ i -> α} (H : BddBelow <| ⋃ i, range (f i)) (i : ι)
  证明: ciInf_le_of_le H.range_iInf_of_iUnion_range i
    ciInf_le (H.mono <| subset_iUnion (range <| f ·) i) j

Depends on / 依赖: H.mono, H.range_iInf_of_iUnion_range, ciInf_le, ciInf_le_of_le, range_iInf_of_iUnion_range, subset_iUnion
-/
theorem ciInf₂_le {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddBelow <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : ⨅ (i) (j), f i j <= f i j :=
ciInf_le_of_le H.range_iInf_of_iUnion_range i
    ciInf_le (H.mono <| subset_iUnion (range <| f ·) i) j

/--
theorem `ciInf_set_le` / 定理 `ciInf_set_le`

English:
theorem ciInf_set_le
  given: {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c in s)
  proof: le_ciSup_set (α := αᵒᵈ) H hc

中文:
定理 ciInf_set_le
  条件: {f : β -> α} {s : 集合 β} (H : BddBelow (f '' s)) {c : β} (hc : c in s)
  证明: le_ciSup_set (α := αᵒᵈ) H hc

Depends on / 依赖: le_ciSup_set
-/
theorem ciInf_set_le {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c in s) :
    ⨅ i : s, f i <= f c :=
  le_ciSup_set (α := αᵒᵈ) H hc

/--
lemma `ciInf_le_ciSup` / 引理 `ciInf_le_ciSup`

English:
lemma ciInf_le_ciSup
  given: [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f)) (hf' : BddAbove (range f))
  proof: (ciInf_le hf (Classical.arbitrary _)).trans le_ciSup hf' (Classical.arbitrary _)

中文:
引理 ciInf_le_ciSup
  条件: [非空 ι] {f : ι -> α} (hf : BddBelow (range f)) (hf' : BddAbove (range f))
  证明: (ciInf_le hf (Classical.arbitrary _)).trans le_ciSup hf' (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, ciInf_le, le_ciSup
-/
lemma ciInf_le_ciSup [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f)) (hf' : BddAbove (range f)) :
    ⨅ i, f i <= ⨆ i, f i :=
(ciInf_le hf (Classical.arbitrary _)).trans le_ciSup hf' (Classical.arbitrary _)

/--
lemma `ciSup_prod` / 引理 `ciSup_prod`

English:
lemma ciSup_prod
  given: {f : β × γ -> α} (hf : BddAbove (Set.range f))
  proof: by
  rcases isEmpty_or_nonempty β
  · simp [iSup_of_empty']
  rcases isEmpty_or_nonempty γ
  · simp [iSup_of_empty']
  have h₁ : BddAbove (Set.range fun b => ⨆ c, f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := Set.mem_rang

中文:
引理 ciSup_prod
  条件: {f : β × γ -> α} (hf : BddAbove (集合.range f))
  证明: by
  rcases isEmpty_or_nonempty β
  · simp [iSup_of_empty']
  rcases isEmpty_or_nonempty γ
  · simp [iSup_of_empty']
  have h₁ : BddAbove (Set.range fun b => ⨆ c, f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := Set.mem_rang

Depends on / 依赖: BddAbove, Set.mem_range.mp, Set.range, bddAbove_def, ciSup_le, ciSup_le_iff, eq_of_forall_ge_iff, iSup_of_empty, isEmpty_or_nonempty, mem_range
-/
lemma ciSup_prod {f : β × γ -> α} (hf : BddAbove (Set.range f)) :
    ⨆ p, f p = ⨆ b, ⨆ c, f (b, c) := by
  rcases isEmpty_or_nonempty β
  · simp [iSup_of_empty']
  rcases isEmpty_or_nonempty γ
  · simp [iSup_of_empty']
  have h₁ : BddAbove (Set.range fun b => ⨆ c, f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
    exact ciSup_le fun c => by grind
  have h₂ b : BddAbove (Set.range fun c => f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    exact ⟨B, by grind⟩
  refine eq_of_forall_ge_iff fun c => ?_
  rw [ciSup_le_iff (bddAbove_iff_subset_Iic.mpr hf)]; rw [ciSup_le_iff h₁]
  conv_rhs => enter [b]; rw [ciSup_le_iff (h₂ b)]
  simp [Prod.forall]

/--
lemma `ciInf_prod` / 引理 `ciInf_prod`

English:
lemma ciInf_prod
  given: {f : β × γ -> α} (hf : BddBelow (Set.range f))
  proof: ciSup_prod (α := αᵒᵈ) hf

中文:
引理 ciInf_prod
  条件: {f : β × γ -> α} (hf : BddBelow (集合.range f))
  证明: ciSup_prod (α := αᵒᵈ) hf

Depends on / 依赖: ciSup_prod
-/
lemma ciInf_prod {f : β × γ -> α} (hf : BddBelow (Set.range f)) :
    ⨅ p, f p = ⨅ b, ⨅ c, f (b, c) :=
  ciSup_prod (α := αᵒᵈ) hf

/--
theorem `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  statement: [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b)
  proof: csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
fun w hw => exists_range_iff.mpr h₂ w hw

中文:
定理 ciSup_eq_of_对任意_le_of_对任意_lt_存在_gt
  结论: [非空 ι] {f : ι -> α} (h₁ : 对任意 i, f i <= b)
  证明: csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
fun w hw => exists_range_iff.mpr h₂ w hw

Depends on / 依赖: csSup_eq_of_forall_le_of_forall_lt_exists_gt, exists_range_iff, exists_range_iff.mpr, forall_mem_range, forall_mem_range.mpr, range_nonempty
-/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b)
    (h₂ : forall w, w < b -> exists i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
fun w hw => exists_range_iff.mpr h₂ w hw

/--
theorem `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` / 定理 `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt`

English:
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
  statement: [Nonempty ι] {f : ι -> α} (h₁ : forall i, b <= f i)
  proof: ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂

中文:
定理 ciInf_eq_of_对任意_ge_of_对任意_gt_存在_lt
  结论: [非空 ι] {f : ι -> α} (h₁ : 对任意 i, b <= f i)
  证明: ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂

Depends on / 依赖: ciSup_eq_of_forall_le_of_forall_lt_exists_gt
-/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι -> α} (h₁ : forall i, b <= f i)
    (h₂ : forall w, b < w -> exists i, f i < w) : ⨅ i : ι, f i = b :=
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂

/--
lemma `Set.Iic_ciInf` / 引理 `Set.Iic_ciInf`

English:
lemma Set.Iic_ciInf
  given: [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f))
  proof: by
  ext
  simpa using le_ciInf_iff hf

中文:
引理 集合.Iic_ciInf
  条件: [非空 ι] {f : ι -> α} (hf : BddBelow (range f))
  证明: by
  ext
  simpa using le_ciInf_iff hf

Depends on / 依赖: le_ciInf_iff
-/
lemma Set.Iic_ciInf [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f)) :
    Iic (⨅ i, f i) = ⋂ i, Iic (f i) := by
  ext
  simpa using le_ciInf_iff hf

/--
lemma `Set.Ici_ciSup` / 引理 `Set.Ici_ciSup`

English:
lemma Set.Ici_ciSup
  given: [Nonempty ι] {f : ι -> α} (hf : BddAbove (range f))
  proof: Iic_ciInf (α := αᵒᵈ) hf

中文:
引理 集合.Ici_ciSup
  条件: [非空 ι] {f : ι -> α} (hf : BddAbove (range f))
  证明: Iic_ciInf (α := αᵒᵈ) hf

Depends on / 依赖: Iic_ciInf
-/
lemma Set.Ici_ciSup [Nonempty ι] {f : ι -> α} (hf : BddAbove (range f)) :
    Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  Iic_ciInf (α := αᵒᵈ) hf

/--
theorem `ciSup_subtype` / 定理 `ciSup_subtype`

English:
theorem ciSup_subtype
  statement: {p : ι -> Prop} {f : Subtype p -> α}
  proof: by
  cases isEmpty_or_nonempty (Subtype p)
  · rw [iSup_of_empty', cbiSup_eq_of_forall_not fun i h => isEmptyElim (⟨i, h⟩ : Subtype p)]
  have : Nonempty ι := (nonempty_subtype.mp ‹_›).nonempty
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι => ⨆ (

中文:
定理 ciSup_subtype
  结论: {p : ι -> 命题} {f : 子类型 p -> α}
  证明: by
  cases isEmpty_or_nonempty (Subtype p)
  · rw [iSup_of_empty', cbiSup_eq_of_forall_not fun i h => isEmptyElim (⟨i, h⟩ : Subtype p)]
  have : Nonempty ι := (nonempty_subtype.mp ‹_›).nonempty
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι => ⨆ (

Depends on / 依赖: Nonempty, Subtype, bddAbove_singleton, cbiSup_eq_of_forall_not, ciSup_eq_ite, ciSup_le, classical, hf.union, iSup_of_empty, isEmptyElim, isEmpty_or_nonempty, le_antisymm, le_ciSup, nonempty, nonempty_subtype, nonempty_subtype.mp, simp_rw
-/
theorem ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α}
    (hf : BddAbove (Set.range f)) (hf' : sSup ∅ <= iSup f) :
    iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ := by
  cases isEmpty_or_nonempty (Subtype p)
  · rw [iSup_of_empty', cbiSup_eq_of_forall_not fun i h => isEmptyElim (⟨i, h⟩ : Subtype p)]
  have : Nonempty ι := (nonempty_subtype.mp ‹_›).nonempty
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι => ⨆ (h : p i), f ⟨i, h⟩) i := by simp [h]
    rw [this]
    refine le_ciSup (f := (fun i : ι => ⨆ (h : p i), f ⟨i, h⟩)) ?_ i
    simp_rw [ciSup_eq_ite]
    refine (hf.union (bddAbove_singleton (a := sSup ∅))).mono ?_
    grind
  · refine ciSup_le fun i => ?_
    simp_rw [ciSup_eq_ite]
    split_ifs
    · exact le_ciSup hf ?_
    · exact hf'

/--
theorem `ciInf_subtype` / 定理 `ciInf_subtype`

English:
theorem ciInf_subtype
  statement: {p : ι -> Prop} {f : Subtype p -> α}
  proof: ciSup_subtype (α := αᵒᵈ) hf hf'

中文:
定理 ciInf_subtype
  结论: {p : ι -> 命题} {f : 子类型 p -> α}
  证明: ciSup_subtype (α := αᵒᵈ) hf hf'

Depends on / 依赖: ciSup_subtype
-/
theorem ciInf_subtype {p : ι -> Prop} {f : Subtype p -> α}
    (hf : BddBelow (Set.range f)) (hf' : iInf f <= sInf ∅) :
    iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  ciSup_subtype (α := αᵒᵈ) hf hf'

/--
theorem `cbiSup_eq_ciSup_subtype` / 定理 `cbiSup_eq_ciSup_subtype`

English:
theorem cbiSup_eq_ciSup_subtype
  statement: {p : ι -> Prop} {f : forall i, p i -> α}
  proof: (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciSup_subtype' := cbiSup_eq_ciSup_subtype

中文:
定理 cbiSup_eq_ciSup_subtype
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α}
  证明: (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciSup_subtype' := cbiSup_eq_ciSup_subtype

Depends on / 依赖: ciSup_subtype, property, x.property, x.val
-/
theorem cbiSup_eq_ciSup_subtype {p : ι -> Prop} {f : forall i, p i -> α}
    (hf : BddAbove (Set.range (fun i : Subtype p => f i i.prop)))
    (hf' : sSup ∅ <= ⨆ (i : Subtype p), f i i.prop) :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciSup_subtype' := cbiSup_eq_ciSup_subtype

/--
theorem `cbiInf_eq_ciInf_subtype` / 定理 `cbiInf_eq_ciInf_subtype`

English:
theorem cbiInf_eq_ciInf_subtype
  statement: {p : ι -> Prop} {f : forall i, p i -> α}
  proof: (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciInf_subtype' := cbiInf_eq_ciInf_subtype

中文:
定理 cbiInf_eq_ciInf_subtype
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α}
  证明: (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciInf_subtype' := cbiInf_eq_ciInf_subtype

Depends on / 依赖: ciInf_subtype, property, x.property, x.val
-/
theorem cbiInf_eq_ciInf_subtype {p : ι -> Prop} {f : forall i, p i -> α}
    (hf : BddBelow (Set.range (fun i : Subtype p => f i i.prop)))
    (hf' : ⨅ (i : Subtype p), f i i.prop <= sInf ∅) :
    ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property :=
  (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciInf_subtype' := cbiInf_eq_ciInf_subtype

/--
theorem `ciSup_subtype_fun` / 定理 `ciSup_subtype_fun`

English:
theorem ciSup_subtype_fun
  statement: {ι} {s : Set ι} {f : ι -> α}
  proof: ciSup_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciSup_subtype'' := ciSup_subtype_fun

中文:
定理 ciSup_subtype_fun
  结论: {ι} {s : 集合 ι} {f : ι -> α}
  证明: ciSup_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciSup_subtype'' := ciSup_subtype_fun

Depends on / 依赖: ciSup_subtype
-/
theorem ciSup_subtype_fun {ι} {s : Set ι} {f : ι -> α}
    (hf : BddAbove (Set.range fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) :
    ⨆ i : s, f i = ⨆ (t : ι) (_ : t in s), f t :=
  ciSup_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciSup_subtype'' := ciSup_subtype_fun

/--
theorem `ciInf_subtype_fun` / 定理 `ciInf_subtype_fun`

English:
theorem ciInf_subtype_fun
  statement: {ι} {s : Set ι} {f : ι -> α}
  proof: ciInf_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciInf_subtype'' := ciInf_subtype_fun

中文:
定理 ciInf_subtype_fun
  结论: {ι} {s : 集合 ι} {f : ι -> α}
  证明: ciInf_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciInf_subtype'' := ciInf_subtype_fun

Depends on / 依赖: ciInf_subtype
-/
theorem ciInf_subtype_fun {ι} {s : Set ι} {f : ι -> α}
    (hf : BddBelow (Set.range fun i : s => f i)) (hf' : ⨅ i : s, f i <= sInf ∅) :
    ⨅ i : s, f i = ⨅ (t : ι) (_ : t in s), f t :=
  ciInf_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciInf_subtype'' := ciInf_subtype_fun

/--
theorem `csSup_image` / 定理 `csSup_image`

English:
theorem csSup_image
  statement: {s : Set β} {f : β -> α}
  proof: by
  rw [← ciSup_subtype_fun hf hf']; rw [iSup]; rw [Set.image_eq_range]

中文:
定理 csSup_image
  结论: {s : 集合 β} {f : β -> α}
  证明: by
  rw [← ciSup_subtype_fun hf hf']; rw [iSup]; rw [Set.image_eq_range]

Depends on / 依赖: Set.image_eq_range, ciSup_subtype_fun, image_eq_range
-/
theorem csSup_image {s : Set β} {f : β -> α}
    (hf : BddAbove (Set.range fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) :
    sSup (f '' s) = ⨆ a in s, f a := by
  rw [← ciSup_subtype_fun hf hf']; rw [iSup]; rw [Set.image_eq_range]

/--
theorem `csInf_image` / 定理 `csInf_image`

English:
theorem csInf_image
  statement: {s : Set β} {f : β -> α}
  proof: csSup_image (α := αᵒᵈ) hf hf'

中文:
定理 csInf_image
  结论: {s : 集合 β} {f : β -> α}
  证明: csSup_image (α := αᵒᵈ) hf hf'

Depends on / 依赖: csSup_image
-/
theorem csInf_image {s : Set β} {f : β -> α}
    (hf : BddBelow (Set.range fun i : s => f i)) (hf' : ⨅ i : s, f i <= sInf ∅) :
    sInf (f '' s) = ⨅ a in s, f a :=
  csSup_image (α := αᵒᵈ) hf hf'

/--
theorem `cbiSup_id` / 定理 `cbiSup_id`

English:
theorem cbiSup_id
  given: {s : Set α} (hs : BddAbove s) (h : sSup ∅ <= sSup s)
  statement: ⨆ i in s, i = sSup s
  proof: by
  rw [← csSup_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sSup_range]; rw [Subtype.range_coe]

中文:
定理 cbiSup_id
  条件: {s : 集合 α} (hs : BddAbove s) (h : sSup ∅ <= sSup s)
  结论: ⨆ i in s, i = sSup s
  证明: by
  rw [← csSup_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sSup_range]; rw [Subtype.range_coe]

Depends on / 依赖: Set.image_id, Subtype, Subtype.range_coe, convert, csSup_image, image_id, range_coe, sSup_range
-/
theorem cbiSup_id {s : Set α} (hs : BddAbove s) (h : sSup ∅ <= sSup s) : ⨆ i in s, i = sSup s := by
  rw [← csSup_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sSup_range]; rw [Subtype.range_coe]

/--
theorem `cbiInf_id` / 定理 `cbiInf_id`

English:
theorem cbiInf_id
  given: {s : Set α} (hs : BddBelow s) (h : sInf s <= sInf ∅)
  statement: ⨅ i in s, i = sInf s
  proof: by
  rw [← csInf_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sInf_range]; rw [Subtype.range_coe]

中文:
定理 cbiInf_id
  条件: {s : 集合 α} (hs : BddBelow s) (h : sInf s <= sInf ∅)
  结论: ⨅ i in s, i = sInf s
  证明: by
  rw [← csInf_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sInf_range]; rw [Subtype.range_coe]

Depends on / 依赖: Set.image_id, Subtype, Subtype.range_coe, convert, csInf_image, image_id, range_coe, sInf_range
-/
theorem cbiInf_id {s : Set α} (hs : BddBelow s) (h : sInf s <= sInf ∅) : ⨅ i in s, i = sInf s := by
  rw [← csInf_image (Subtype.range_coe ▸ hs)]; rw [Set.image_id']
  · convert! h
    rw [← sInf_range]; rw [Subtype.range_coe]

/--
lemma `ciSup_image` / 引理 `ciSup_image`

English:
lemma ciSup_image
  statement: {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α}
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [Set.image_empty, cbiSup_empty, cbiSup_empty]
  have hg : BddAbove (Set.range fun i : f '' s => g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ <= ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.N

中文:
引理 ciSup_image
  结论: {ι ι' : 类型} {s : 集合 ι} {f : ι -> ι'} {g : ι' -> α}
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [Set.image_empty, cbiSup_empty, cbiSup_empty]
  have hg : BddAbove (Set.range fun i : f '' s => g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ <= ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.N

Depends on / 依赖: BddAbove, Nonempty, Set.Nonempty.to_subtype, Set.image_empty, Set.mem_image_of_mem, Set.range, Subtype, Subtype.mk, bddAbove_def, cbiSup_empty, ciSup_le, eq_empty_or_nonempty, image_empty, mem_image_of_mem, s.eq_empty_or_nonempty, to_subtype
-/
lemma ciSup_image {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α}
    (hf : BddAbove (Set.range fun i : s => g (f i))) (hg' : sSup ∅ <= ⨆ i : s, g (f i)) :
    ⨆ i in (f '' s), g i = ⨆ x in s, g (f x) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [Set.image_empty, cbiSup_empty, cbiSup_empty]
  have hg : BddAbove (Set.range fun i : f '' s => g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ <= ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.Nonempty.to_subtype hs
    refine ciSup_le ?_
    intro ⟨i, h⟩
    obtain ⟨t, ht⟩ : exists t : f '' s, g t = g (f (Subtype.mk i h)) := by
      have : f i in f '' s := Set.mem_image_of_mem _ h
      exact ⟨⟨f i, this⟩, by simp⟩
    rw [← ht]
    refine le_ciSup_set ?_ t.prop
    simpa [bddAbove_def] using hf
  rw [← csSup_image hg hf']; rw [← csSup_image hf hg']; rw [← Set.image_comp]; rw [comp_def]

/--
lemma `ciInf_image` / 引理 `ciInf_image`

English:
lemma ciInf_image
  statement: {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α}
  proof: ciSup_image (α := αᵒᵈ) hf hg'

中文:
引理 ciInf_image
  结论: {ι ι' : 类型} {s : 集合 ι} {f : ι -> ι'} {g : ι' -> α}
  证明: ciSup_image (α := αᵒᵈ) hf hg'

Depends on / 依赖: ciSup_image
-/
lemma ciInf_image {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α}
    (hf : BddBelow (Set.range fun i : s => g (f i))) (hg' : ⨅ i : s, g (f i) <= sInf ∅) :
    ⨅ i in (f '' s), g i = ⨅ x in s, g (f x) :=
  ciSup_image (α := αᵒᵈ) hf hg'

/--
theorem `le_ciSup_ciSup_eq_left` / 定理 `le_ciSup_ciSup_eq_left`

English:
theorem le_ciSup_ciSup_eq_left
  given: {b : β} {f : forall x : β, x = b -> α}
  proof: by
  refine le_ciSup₂ (f := f) ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl

中文:
定理 le_ciSup_ciSup_eq_left
  条件: {b : β} {f : 对任意 x : β, x = b -> α}
  证明: by
  refine le_ciSup₂ (f := f) ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl
-/
theorem le_ciSup_ciSup_eq_left {b : β} {f : forall x : β, x = b -> α} :
    f b rfl <= ⨆ x, ⨆ h : x = b, f x h := by
  refine le_ciSup₂ (f := f) ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl

/--
theorem `ciInf_ciInf_eq_left_le` / 定理 `ciInf_ciInf_eq_left_le`

English:
theorem ciInf_ciInf_eq_left_le
  given: {b : β} {f : forall x : β, x = b -> α}
  proof: le_ciSup_ciSup_eq_left (α := αᵒᵈ)

中文:
定理 ciInf_ciInf_eq_left_le
  条件: {b : β} {f : 对任意 x : β, x = b -> α}
  证明: le_ciSup_ciSup_eq_left (α := αᵒᵈ)

Depends on / 依赖: le_ciSup_ciSup_eq_left
-/
theorem ciInf_ciInf_eq_left_le {b : β} {f : forall x : β, x = b -> α} :
    ⨅ x, ⨅ h : x = b, f x h <= f b rfl :=
  le_ciSup_ciSup_eq_left (α := αᵒᵈ)

/--
theorem `le_ciSup_ciSup_eq_right` / 定理 `le_ciSup_ciSup_eq_right`

English:
theorem le_ciSup_ciSup_eq_right
  given: {b : β} {f : forall x : β, b = x -> α}
  proof: by
  refine le_ciSup₂ ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl

中文:
定理 le_ciSup_ciSup_eq_right
  条件: {b : β} {f : 对任意 x : β, b = x -> α}
  证明: by
  refine le_ciSup₂ ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl
-/
theorem le_ciSup_ciSup_eq_right {b : β} {f : forall x : β, b = x -> α} :
    f b rfl <= ⨆ x, ⨆ h : b = x, f x h := by
  refine le_ciSup₂ ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl

/--
theorem `ciInf_ciInf_eq_right_le` / 定理 `ciInf_ciInf_eq_right_le`

English:
theorem ciInf_ciInf_eq_right_le
  given: {b : β} {f : forall x : β, b = x -> α}
  proof: le_ciSup_ciSup_eq_right (α := αᵒᵈ)

中文:
定理 ciInf_ciInf_eq_right_le
  条件: {b : β} {f : 对任意 x : β, b = x -> α}
  证明: le_ciSup_ciSup_eq_right (α := αᵒᵈ)

Depends on / 依赖: le_ciSup_ciSup_eq_right
-/
theorem ciInf_ciInf_eq_right_le {b : β} {f : forall x : β, b = x -> α} :
    ⨅ x, ⨅ h : b = x, f x h <= f b rfl :=
  le_ciSup_ciSup_eq_right (α := αᵒᵈ)

/--
theorem `ciSup_exists_le` / 定理 `ciSup_exists_le`

English:
theorem ciSup_exists_le
  given: {p : ι -> Prop} {f : Exists p -> α}
  statement: ⨆ ih, f ih <= ⨆ (i) (h), f ⟨i, h⟩
  proof: by
  by_cases! h : Exists p
· have : Nonempty Exists p := ⟨h⟩
    refine ciSup_le fun ⟨i, hi⟩ => le_ciSup₂ (f := fun _ _ => _) ⟨f ⟨i, hi⟩, ?_⟩ i hi
    rintro _ ⟨_, ⟨j, rfl⟩, ⟨hj, rfl⟩⟩
    rfl
  · cases isEmpty_or_nonempty ι <;>
      simp [h, iSup_of_empty', ciSup_const]

中文:
定理 ciSup_存在_le
  条件: {p : ι -> 命题} {f : 存在 p -> α}
  结论: ⨆ ih, f ih <= ⨆ (i) (h), f ⟨i, h⟩
  证明: by
  by_cases! h : Exists p
· have : Nonempty Exists p := ⟨h⟩
    refine ciSup_le fun ⟨i, hi⟩ => le_ciSup₂ (f := fun _ _ => _) ⟨f ⟨i, hi⟩, ?_⟩ i hi
    rintro _ ⟨_, ⟨j, rfl⟩, ⟨hj, rfl⟩⟩
    rfl
  · cases isEmpty_or_nonempty ι <;>
      simp [h, iSup_of_empty', ciSup_const]

Depends on / 依赖: Exists, Nonempty, ciSup_const, ciSup_le, iSup_of_empty, isEmpty_or_nonempty
-/
theorem ciSup_exists_le {p : ι -> Prop} {f : Exists p -> α} : ⨆ ih, f ih <= ⨆ (i) (h), f ⟨i, h⟩ := by
  by_cases! h : Exists p
· have : Nonempty Exists p := ⟨h⟩
    refine ciSup_le fun ⟨i, hi⟩ => le_ciSup₂ (f := fun _ _ => _) ⟨f ⟨i, hi⟩, ?_⟩ i hi
    rintro _ ⟨_, ⟨j, rfl⟩, ⟨hj, rfl⟩⟩
    rfl
  · cases isEmpty_or_nonempty ι <;>
      simp [h, iSup_of_empty', ciSup_const]

/--
theorem `le_ciInf_exists` / 定理 `le_ciInf_exists`

English:
theorem le_ciInf_exists
  given: {p : ι -> Prop} {f : Exists p -> α}
  statement: ⨅ (i) (h), f ⟨i, h⟩ <= ⨅ ih, f ih
  proof: ciSup_exists_le (α := αᵒᵈ)

中文:
定理 le_ciInf_存在
  条件: {p : ι -> 命题} {f : 存在 p -> α}
  结论: ⨅ (i) (h), f ⟨i, h⟩ <= ⨅ ih, f ih
  证明: ciSup_exists_le (α := αᵒᵈ)

Depends on / 依赖: ciSup_exists_le
-/
theorem le_ciInf_exists {p : ι -> Prop} {f : Exists p -> α} : ⨅ (i) (h), f ⟨i, h⟩ <= ⨅ ih, f ih :=
  ciSup_exists_le (α := αᵒᵈ)

/--
theorem `ciSup_and` / 定理 `ciSup_and`

English:
theorem ciSup_and
  given: {p q : Prop} {f : p ∧ q -> α}
  statement: ⨆ ih, f ih = ⨆ (h₁) (h₂), f ⟨h₁, h₂⟩
  proof: by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iSup_of_empty']

中文:
定理 ciSup_and
  条件: {p q : 命题} {f : p ∧ q -> α}
  结论: ⨆ ih, f ih = ⨆ (h₁) (h₂), f ⟨h₁, h₂⟩
  证明: by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iSup_of_empty']

Depends on / 依赖: iSup_of_empty
-/
theorem ciSup_and {p q : Prop} {f : p ∧ q -> α} : ⨆ ih, f ih = ⨆ (h₁) (h₂), f ⟨h₁, h₂⟩ := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iSup_of_empty']

/--
theorem `ciInf_and` / 定理 `ciInf_and`

English:
theorem ciInf_and
  given: {p q : Prop} {f : p ∧ q -> α}
  statement: ⨅ ih, f ih = ⨅ (h₁) (h₂), f ⟨h₁, h₂⟩
  proof: ciSup_and (α := αᵒᵈ)

中文:
定理 ciInf_and
  条件: {p q : 命题} {f : p ∧ q -> α}
  结论: ⨅ ih, f ih = ⨅ (h₁) (h₂), f ⟨h₁, h₂⟩
  证明: ciSup_and (α := αᵒᵈ)

Depends on / 依赖: ciSup_and
-/
theorem ciInf_and {p q : Prop} {f : p ∧ q -> α} : ⨅ ih, f ih = ⨅ (h₁) (h₂), f ⟨h₁, h₂⟩ :=
  ciSup_and (α := αᵒᵈ)

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {a b : α}

/--
theorem `ciSup_sup_le` / 定理 `ciSup_sup_le`

English:
theorem ciSup_sup_le
  given: {f g : ι -> α}
  statement: ⨆ x, f x ⊔ g x <= (⨆ x, f x) ⊔ (⨆ x, g x)
  proof: by
  by_cases! hf : ¬BddAbove (range f)
  · rw [ciSup_of_not_bddAbove hf, ciSup_of_not_bddAbove <| mt bbdAbove_range_left_of_sup hf]
    exact le_sup_left
  by_cases! hg : ¬BddAbove (range g)
  · rw [ciSup_of_not_bddAbove hg, ciSup_of_not_bddAbove <| mt bbdAbove_range_right_of_sup hg]
    exact le_s

中文:
定理 ciSup_sup_le
  条件: {f g : ι -> α}
  结论: ⨆ x, f x ⊔ g x <= (⨆ x, f x) ⊔ (⨆ x, g x)
  证明: by
  by_cases! hf : ¬BddAbove (range f)
  · rw [ciSup_of_not_bddAbove hf, ciSup_of_not_bddAbove <| mt bbdAbove_range_left_of_sup hf]
    exact le_sup_left
  by_cases! hg : ¬BddAbove (range g)
  · rw [ciSup_of_not_bddAbove hg, ciSup_of_not_bddAbove <| mt bbdAbove_range_right_of_sup hg]
    exact le_s

Depends on / 依赖: BddAbove, bbdAbove_range_left_of_sup, bbdAbove_range_right_of_sup, ciSup_of_not_bddAbove, ciSup_sup_eq, le_sup_left, le_sup_right
-/
theorem ciSup_sup_le {f g : ι -> α} : ⨆ x, f x ⊔ g x <= (⨆ x, f x) ⊔ (⨆ x, g x) := by
  by_cases! hf : ¬BddAbove (range f)
  · rw [ciSup_of_not_bddAbove hf, ciSup_of_not_bddAbove <| mt bbdAbove_range_left_of_sup hf]
    exact le_sup_left
  by_cases! hg : ¬BddAbove (range g)
  · rw [ciSup_of_not_bddAbove hg, ciSup_of_not_bddAbove <| mt bbdAbove_range_right_of_sup hg]
    exact le_sup_right
.le exact ciSup_sup_eq hf hg

/--
theorem `ciInf_inf_le` / 定理 `ciInf_inf_le`

English:
theorem ciInf_inf_le
  given: {f g : ι -> α}
  statement: (⨅ x, f x) ⊓ (⨅ x, g x) <= ⨅ x, f x ⊓ g x
  proof: ciSup_sup_le (α := αᵒᵈ)

中文:
定理 ciInf_inf_le
  条件: {f g : ι -> α}
  结论: (⨅ x, f x) ⊓ (⨅ x, g x) <= ⨅ x, f x ⊓ g x
  证明: ciSup_sup_le (α := αᵒᵈ)

Depends on / 依赖: ciSup_sup_le
-/
theorem ciInf_inf_le {f g : ι -> α} : (⨅ x, f x) ⊓ (⨅ x, g x) <= ⨅ x, f x ⊓ g x :=
  ciSup_sup_le (α := αᵒᵈ)

/--
theorem `exists_lt_of_lt_ciSup` / 定理 `exists_lt_of_lt_ciSup`

English:
theorem exists_lt_of_lt_ciSup
  given: [Nonempty ι] {f : ι -> α} (h : b < iSup f)
  statement: exists i, b < f i
  proof: let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

中文:
定理 存在_lt_of_lt_ciSup
  条件: [非空 ι] {f : ι -> α} (h : b < iSup f)
  结论: 存在 i, b < f i
  证明: let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

Depends on / 依赖: exists_lt_of_lt_csSup, range_nonempty
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (h : b < iSup f) : exists i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

/--
theorem `exists_lt_of_ciInf_lt` / 定理 `exists_lt_of_ciInf_lt`

English:
theorem exists_lt_of_ciInf_lt
  given: [Nonempty ι] {f : ι -> α} (h : iInf f < a)
  statement: exists i, f i < a
  proof: exists_lt_of_lt_ciSup (α := αᵒᵈ) h

中文:
定理 存在_lt_of_ciInf_lt
  条件: [非空 ι] {f : ι -> α} (h : iInf f < a)
  结论: 存在 i, f i < a
  证明: exists_lt_of_lt_ciSup (α := αᵒᵈ) h

Depends on / 依赖: exists_lt_of_lt_ciSup
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι -> α} (h : iInf f < a) : exists i, f i < a :=
  exists_lt_of_lt_ciSup (α := αᵒᵈ) h

/--
theorem `lt_ciSup_iff` / 定理 `lt_ciSup_iff`

English:
theorem lt_ciSup_iff
  given: [Nonempty ι] {f : ι -> α} (hb : BddAbove (range f))
  proof: by
  simpa only [mem_range, exists_exists_eq_and] using! lt_csSup_iff hb (range_nonempty _)

中文:
定理 lt_ciSup_iff
  条件: [非空 ι] {f : ι -> α} (hb : BddAbove (range f))
  证明: by
  simpa only [mem_range, exists_exists_eq_and] using! lt_csSup_iff hb (range_nonempty _)

Depends on / 依赖: exists_exists_eq_and, lt_csSup_iff, mem_range, range_nonempty
-/
theorem lt_ciSup_iff [Nonempty ι] {f : ι -> α} (hb : BddAbove (range f)) :
    a < iSup f ↔ exists i, a < f i := by
  simpa only [mem_range, exists_exists_eq_and] using! lt_csSup_iff hb (range_nonempty _)

/--
theorem `ciInf_lt_iff` / 定理 `ciInf_lt_iff`

English:
theorem ciInf_lt_iff
  given: [Nonempty ι] {f : ι -> α} (hb : BddBelow (range f))
  proof: by
  simpa only [mem_range, exists_exists_eq_and] using! csInf_lt_iff hb (range_nonempty _)

中文:
定理 ciInf_lt_iff
  条件: [非空 ι] {f : ι -> α} (hb : BddBelow (range f))
  证明: by
  simpa only [mem_range, exists_exists_eq_and] using! csInf_lt_iff hb (range_nonempty _)

Depends on / 依赖: csInf_lt_iff, exists_exists_eq_and, mem_range, range_nonempty
-/
theorem ciInf_lt_iff [Nonempty ι] {f : ι -> α} (hb : BddBelow (range f)) :
    iInf f < a ↔ exists i, f i < a := by
  simpa only [mem_range, exists_exists_eq_and] using! csInf_lt_iff hb (range_nonempty _)

/--
theorem `cbiSup_of_not_bddAbove` / 定理 `cbiSup_of_not_bddAbove`

English:
theorem cbiSup_of_not_bddAbove
  statement: {p : ι -> Prop} {f : forall i, p i -> α}
  proof: ciSup_of_not_bddAbove fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciSup_pos x.prop⟩⟩

中文:
定理 cbiSup_of_not_bddAbove
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α}
  证明: ciSup_of_not_bddAbove fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciSup_pos x.prop⟩⟩

Depends on / 依赖: ciSup_of_not_bddAbove, ciSup_pos, x.prop
-/
theorem cbiSup_of_not_bddAbove {p : ι -> Prop} {f : forall i, p i -> α}
    (h : ¬BddAbove (range fun i : Subtype p => f i i.prop)) :
    ⨆ (i : ι), ⨆ (h : p i), f i h = sSup ∅ :=
  ciSup_of_not_bddAbove fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciSup_pos x.prop⟩⟩

/--
theorem `cbiInf_of_not_bddBelow` / 定理 `cbiInf_of_not_bddBelow`

English:
theorem cbiInf_of_not_bddBelow
  statement: {p : ι -> Prop} {f : forall i, p i -> α}
  proof: ciInf_of_not_bddBelow fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciInf_pos x.prop⟩⟩

中文:
定理 cbiInf_of_not_bddBelow
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α}
  证明: ciInf_of_not_bddBelow fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciInf_pos x.prop⟩⟩

Depends on / 依赖: ciInf_of_not_bddBelow, ciInf_pos, x.prop
-/
theorem cbiInf_of_not_bddBelow {p : ι -> Prop} {f : forall i, p i -> α}
    (h : ¬BddBelow (range fun i : Subtype p => f i i.prop)) :
    ⨅ (i : ι), ⨅ (h : p i), f i h = sInf ∅ :=
  ciInf_of_not_bddBelow fun ⟨u, hu⟩ => h ⟨u, fun _ ⟨x, hx⟩ => hx ▸ hu ⟨x, ciInf_pos x.prop⟩⟩

/--
theorem `cbiSup_eq_of_not_forall` / 定理 `cbiSup_eq_of_not_forall`

English:
theorem cbiSup_eq_of_not_forall
  given: {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (forall i, p i))
  proof: by
  rcases le_or_gt (sSup ∅) (iSup f) with le | gt
  · rw [max_eq_left le]
    by_cases bdd : BddAbove (range f)
    · rw [← ciSup_subtype bdd le]
    · rw [ciSup_of_not_bddAbove bdd, cbiSup_of_not_bddAbove bdd]
  have ⟨i, hi⟩ := not_forall.mp hp
  have : Nonempty ι := ⟨i⟩
  have bdd : BddAbove (ra

中文:
定理 cbiSup_eq_of_not_对任意
  条件: {p : ι -> 命题} {f : 子类型 p -> α} (hp : ¬ (对任意 i, p i))
  证明: by
  rcases le_or_gt (sSup ∅) (iSup f) with le | gt
  · rw [max_eq_left le]
    by_cases bdd : BddAbove (range f)
    · rw [← ciSup_subtype bdd le]
    · rw [ciSup_of_not_bddAbove bdd, cbiSup_of_not_bddAbove bdd]
  have ⟨i, hi⟩ := not_forall.mp hp
  have : Nonempty ι := ⟨i⟩
  have bdd : BddAbove (ra

Depends on / 依赖: BddAbove, Nonempty, cbiSup_of_not_bddAbove, ciSup_eq_of_forall_le_of_forall_lt_exists_gt, ciSup_of_not_bddAbove, ciSup_pos, ciSup_subtype, gt.le, gt.ne, le_ciSup, le_or_gt, max_eq_left, max_eq_right, not_forall, not_forall.mp, not_not, not_not.mp, trans_le
-/
theorem cbiSup_eq_of_not_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (forall i, p i)) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅ := by
  rcases le_or_gt (sSup ∅) (iSup f) with le | gt
  · rw [max_eq_left le]
    by_cases bdd : BddAbove (range f)
    · rw [← ciSup_subtype bdd le]
    · rw [ciSup_of_not_bddAbove bdd, cbiSup_of_not_bddAbove bdd]
  have ⟨i, hi⟩ := not_forall.mp hp
  have : Nonempty ι := ⟨i⟩
  have bdd : BddAbove (range f) := not_not.mp fun h => gt.ne (ciSup_of_not_bddAbove h)
  rw [max_eq_right gt.le]
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) ?_
  · by_cases hj : p j
    · exact ((ciSup_pos hj).trans_le (le_ciSup bdd ⟨j, hj⟩)).trans gt.le
    · exact (ciSup_neg hj).le
  · exact fun w hw => ⟨i, hw.trans_eq (ciSup_neg hi).symm⟩

/--
theorem `cbiInf_eq_of_not_forall` / 定理 `cbiInf_eq_of_not_forall`

English:
theorem cbiInf_eq_of_not_forall
  given: {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (forall i, p i))
  proof: cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

中文:
定理 cbiInf_eq_of_not_对任意
  条件: {p : ι -> 命题} {f : 子类型 p -> α} (hp : ¬ (对任意 i, p i))
  证明: cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

Depends on / 依赖: cbiSup_eq_of_not_forall
-/
theorem cbiInf_eq_of_not_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (forall i, p i)) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅ :=
  cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

/--
theorem `ciInf_eq_bot_of_bot_mem` / 定理 `ciInf_eq_bot_of_bot_mem`

English:
theorem ciInf_eq_bot_of_bot_mem
  given: [OrderBot α] {f : ι -> α} (hs : ⊥ in range f)
  statement: iInf f = ⊥
  proof: csInf_eq_bot_of_bot_mem hs

中文:
定理 ciInf_eq_bot_of_bot_mem
  条件: [有底序 α] {f : ι -> α} (hs : ⊥ in range f)
  结论: iInf f = ⊥
  证明: csInf_eq_bot_of_bot_mem hs

Depends on / 依赖: csInf_eq_bot_of_bot_mem
-/
theorem ciInf_eq_bot_of_bot_mem [OrderBot α] {f : ι -> α} (hs : ⊥ in range f) : iInf f = ⊥ :=
  csInf_eq_bot_of_bot_mem hs

/--
theorem `ciSup_eq_top_of_top_mem` / 定理 `ciSup_eq_top_of_top_mem`

English:
theorem ciSup_eq_top_of_top_mem
  given: [OrderTop α] {f : ι -> α} (hs : ⊤ in range f)
  statement: iSup f = ⊤
  proof: csSup_eq_top_of_top_mem hs

@[deprecated (since := "2026-04-05")] alias ciInf_eq_top_of_top_mem := ciSup_eq_top_of_top_mem

中文:
定理 ciSup_eq_top_of_top_mem
  条件: [有顶序 α] {f : ι -> α} (hs : ⊤ in range f)
  结论: iSup f = ⊤
  证明: csSup_eq_top_of_top_mem hs

@[deprecated (since := "2026-04-05")] alias ciInf_eq_top_of_top_mem := ciSup_eq_top_of_top_mem

Depends on / 依赖: csSup_eq_top_of_top_mem
-/
theorem ciSup_eq_top_of_top_mem [OrderTop α] {f : ι -> α} (hs : ⊤ in range f) : iSup f = ⊤ :=
  csSup_eq_top_of_top_mem hs

@[deprecated (since := "2026-04-05")] alias ciInf_eq_top_of_top_mem := ciSup_eq_top_of_top_mem

variable [WellFoundedLT α]

/--
theorem `ciInf_mem` / 定理 `ciInf_mem`

English:
theorem ciInf_mem
  given: [Nonempty ι] (f : ι -> α)
  statement: iInf f in range f
  proof: csInf_mem (range_nonempty f)

中文:
定理 ciInf_mem
  条件: [非空 ι] (f : ι -> α)
  结论: iInf f in range f
  证明: csInf_mem (range_nonempty f)

Depends on / 依赖: csInf_mem, range_nonempty
-/
theorem ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f :=
  csInf_mem (range_nonempty f)

/--
lemma `ciInf_eq_iff` / 引理 `ciInf_eq_iff`

English:
lemma ciInf_eq_iff
  given: [Nonempty ι] (f : ι -> α) (n : α)
  proof: by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · rintro rfl
    exact ⟨ciInf_mem f, ciInf_le (OrderBot.bddBelow ..)⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (ciInf_le (OrderBot.bddBelow ..) _) (le_ciInf h)

中文:
引理 ciInf_eq_iff
  条件: [非空 ι] (f : ι -> α) (n : α)
  证明: by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · rintro rfl
    exact ⟨ciInf_mem f, ciInf_le (OrderBot.bddBelow ..)⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (ciInf_le (OrderBot.bddBelow ..) _) (le_ciInf h)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WellFoundedLT, WellFoundedLT.toOrderBot, bddBelow, ciInf_le, ciInf_mem, le_antisymm, le_ciInf, toOrderBot
-/
lemma ciInf_eq_iff [Nonempty ι] (f : ι -> α) (n : α) :
    ⨅ i, (f i) = n ↔ (exists i, f i = n) ∧ forall i, n <= f i := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · rintro rfl
    exact ⟨ciInf_mem f, ciInf_le (OrderBot.bddBelow ..)⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (ciInf_le (OrderBot.bddBelow ..) _) (le_ciInf h)

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] {f : ι -> α} {a : α}

@[simp]
/--
theorem `ciSup_of_empty` / 定理 `ciSup_of_empty`

English:
theorem ciSup_of_empty
  given: [IsEmpty ι] (f : ι -> α)
  statement: ⨆ i, f i = ⊥
  proof: by
  rw [iSup_of_empty']; rw [csSup_empty]

中文:
定理 ciSup_of_empty
  条件: [是空 ι] (f : ι -> α)
  结论: ⨆ i, f i = ⊥
  证明: by
  rw [iSup_of_empty']; rw [csSup_empty]

Depends on / 依赖: csSup_empty, iSup_of_empty
-/
theorem ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty']; rw [csSup_empty]

/--
theorem `ciSup_false` / 定理 `ciSup_false`

English:
theorem ciSup_false
  given: (f : False -> α)
  statement: ⨆ i, f i = ⊥
  proof: ciSup_of_empty f

中文:
定理 ciSup_false
  条件: (f : 假 -> α)
  结论: ⨆ i, f i = ⊥
  证明: ciSup_of_empty f

Depends on / 依赖: ciSup_of_empty
-/
theorem ciSup_false (f : False -> α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f

/--
theorem `le_ciSup_iff'` / 定理 `le_ciSup_iff'`

English:
theorem le_ciSup_iff'
  given: {s : ι -> α} {a : α} (h : BddAbove (range s))
  proof: by simp [iSup, h, le_csSup_iff', upperBounds]

中文:
定理 le_ciSup_iff'
  条件: {s : ι -> α} {a : α} (h : BddAbove (range s))
  证明: by simp [iSup, h, le_csSup_iff', upperBounds]

Depends on / 依赖: le_csSup_iff, upperBounds
-/
theorem le_ciSup_iff' {s : ι -> α} {a : α} (h : BddAbove (range s)) :
    a <= iSup s ↔ forall b, (forall i, s i <= b) -> a <= b := by simp [iSup, h, le_csSup_iff', upperBounds]

/--
theorem `le_ciInf_iff'` / 定理 `le_ciInf_iff'`

English:
theorem le_ciInf_iff'
  given: [Nonempty ι] {f : ι -> α} {a : α}
  statement: a <= iInf f ↔ forall i, a <= f i
  proof: le_ciInf_iff (OrderBot.bddBelow _)

中文:
定理 le_ciInf_iff'
  条件: [非空 ι] {f : ι -> α} {a : α}
  结论: a <= iInf f ↔ 对任意 i, a <= f i
  证明: le_ciInf_iff (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, le_ciInf_iff
-/
theorem le_ciInf_iff' [Nonempty ι] {f : ι -> α} {a : α} : a <= iInf f ↔ forall i, a <= f i :=
  le_ciInf_iff (OrderBot.bddBelow _)

/--
theorem `ciInf_le'` / 定理 `ciInf_le'`

English:
theorem ciInf_le'
  given: (f : ι -> α) (i : ι)
  statement: iInf f <= f i
  proof: ciInf_le (OrderBot.bddBelow _) _

中文:
定理 ciInf_le'
  条件: (f : ι -> α) (i : ι)
  结论: iInf f <= f i
  证明: ciInf_le (OrderBot.bddBelow _) _

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, ciInf_le
-/
theorem ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i := ciInf_le (OrderBot.bddBelow _) _

/--
lemma `ciInf_le_of_le'` / 引理 `ciInf_le_of_le'`

English:
lemma ciInf_le_of_le'
  given: (c : ι)
  statement: f c <= a -> iInf f <= a
  proof: ciInf_le_of_le (OrderBot.bddBelow _) _

中文:
引理 ciInf_le_of_le'
  条件: (c : ι)
  结论: f c <= a -> iInf f <= a
  证明: ciInf_le_of_le (OrderBot.bddBelow _) _

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, ciInf_le_of_le
-/
lemma ciInf_le_of_le' (c : ι) : f c <= a -> iInf f <= a := ciInf_le_of_le (OrderBot.bddBelow _) _

/--
theorem `ciSup_le_iff'` / 定理 `ciSup_le_iff'`

English:
theorem ciSup_le_iff'
  given: {f : ι -> α} (h : BddAbove (range f)) {a : α}
  proof: (csSup_le_iff' h).trans forall_mem_range

中文:
定理 ciSup_le_iff'
  条件: {f : ι -> α} (h : BddAbove (range f)) {a : α}
  证明: (csSup_le_iff' h).trans forall_mem_range

Depends on / 依赖: csSup_le_iff, forall_mem_range
-/
theorem ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i <= a ↔ forall i, f i <= a :=
  (csSup_le_iff' h).trans forall_mem_range

/--
theorem `ciSup_le'` / 定理 `ciSup_le'`

English:
theorem ciSup_le'
  given: {f : ι -> α} {a : α} (h : forall i, f i <= a)
  statement: ⨆ i, f i <= a
  proof: csSup_le' forall_mem_range.2 h

@[simp]

中文:
定理 ciSup_le'
  条件: {f : ι -> α} {a : α} (h : 对任意 i, f i <= a)
  结论: ⨆ i, f i <= a
  证明: csSup_le' forall_mem_range.2 h

@[simp]

Depends on / 依赖: csSup_le, forall_mem_range
-/
theorem ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i, f i <= a :=
csSup_le' forall_mem_range.2 h

@[simp]
/--
theorem `ciSup_bot` / 定理 `ciSup_bot`

English:
theorem ciSup_bot
  statement: ⨆ _ : ι, (⊥ : α) = ⊥
  proof: le_bot_iff.mp (ciSup_le' fun _ => bot_le)

中文:
定理 ciSup_bot
  结论: ⨆ _ : ι, (⊥ : α) = ⊥
  证明: le_bot_iff.mp (ciSup_le' fun _ => bot_le)

Depends on / 依赖: bot_le, ciSup_le, le_bot_iff, le_bot_iff.mp
-/
theorem ciSup_bot : ⨆ _ : ι, (⊥ : α) = ⊥ := le_bot_iff.mp (ciSup_le' fun _ => bot_le)

/--
theorem `lt_ciSup_iff'` / 定理 `lt_ciSup_iff'`

English:
theorem lt_ciSup_iff'
  given: {f : ι -> α} (h : BddAbove (range f))
  statement: a < iSup f ↔ exists i, a < f i
  proof: by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not

中文:
定理 lt_ciSup_iff'
  条件: {f : ι -> α} (h : BddAbove (range f))
  结论: a < iSup f ↔ 存在 i, a < f i
  证明: by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not

Depends on / 依赖: ciSup_le_iff, not_forall, not_le
-/
theorem lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a < iSup f ↔ exists i, a < f i := by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not

/--
theorem `exists_lt_of_lt_ciSup'` / 定理 `exists_lt_of_lt_ciSup'`

English:
theorem exists_lt_of_lt_ciSup'
  given: {f : ι -> α} {a : α} (h : a < ⨆ i, f i)
  statement: exists i, a < f i
  proof: by
  contrapose! h
  exact ciSup_le' h

中文:
定理 存在_lt_of_lt_ciSup'
  条件: {f : ι -> α} {a : α} (h : a < ⨆ i, f i)
  结论: 存在 i, a < f i
  证明: by
  contrapose! h
  exact ciSup_le' h

Depends on / 依赖: ciSup_le, contrapose
-/
theorem exists_lt_of_lt_ciSup' {f : ι -> α} {a : α} (h : a < ⨆ i, f i) : exists i, a < f i := by
  contrapose! h
  exact ciSup_le' h

/--
theorem `ciSup_mono_of_forall_exists'` / 定理 `ciSup_mono_of_forall_exists'`

English:
theorem ciSup_mono_of_forall_exists'
  statement: {ι'} {f : ι -> α} {g : ι' -> α} (hg : BddAbove <| range g)
  proof: .elim le_ciSup_of_le hg ciSup_le' fun i => h i

@[deprecated (since := "2026-05-03")] alias ciSup_mono' := ciSup_mono_of_forall_exists'

中文:
定理 ciSup_mono_of_对任意_存在'
  结论: {ι'} {f : ι -> α} {g : ι' -> α} (hg : BddAbove <| range g)
  证明: .elim le_ciSup_of_le hg ciSup_le' fun i => h i

@[deprecated (since := "2026-05-03")] alias ciSup_mono' := ciSup_mono_of_forall_exists'

Depends on / 依赖: ciSup_le, le_ciSup_of_le
-/
theorem ciSup_mono_of_forall_exists' {ι'} {f : ι -> α} {g : ι' -> α} (hg : BddAbove <| range g)
    (h : forall i, exists i', f i <= g i') : ⨆ i, f i <= ⨆ i', g i' :=
.elim le_ciSup_of_le hg ciSup_le' fun i => h i

@[deprecated (since := "2026-05-03")] alias ciSup_mono' := ciSup_mono_of_forall_exists'

/--
theorem `ciSup_exists` / 定理 `ciSup_exists`

English:
theorem ciSup_exists
  given: {p : ι -> Prop} {f : Exists p -> α}
  statement: ⨆ ih, f ih = ⨆ (i) (h), f ⟨i, h⟩
  proof: by
refine le_antisymm ciSup_exists_le ciSup_le' fun i => ciSup_le' fun hi => ?_
  simp [show Exists p from ⟨i, hi⟩]

@[simp]

中文:
定理 ciSup_存在
  条件: {p : ι -> 命题} {f : 存在 p -> α}
  结论: ⨆ ih, f ih = ⨆ (i) (h), f ⟨i, h⟩
  证明: by
refine le_antisymm ciSup_exists_le ciSup_le' fun i => ciSup_le' fun hi => ?_
  simp [show Exists p from ⟨i, hi⟩]

@[simp]

Depends on / 依赖: Exists, ciSup_exists_le, ciSup_le, le_antisymm
-/
theorem ciSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ ih, f ih = ⨆ (i) (h), f ⟨i, h⟩ := by
refine le_antisymm ciSup_exists_le ciSup_le' fun i => ciSup_le' fun hi => ?_
  simp [show Exists p from ⟨i, hi⟩]

@[simp]
/--
theorem `ciSup_ciSup_eq_left` / 定理 `ciSup_ciSup_eq_left`

English:
theorem ciSup_ciSup_eq_left
  given: {b : β} {f : forall x : β, x = b -> α}
  proof: le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_rfl)) le_ciSup_ciSup_eq_left

@[simp]

中文:
定理 ciSup_ciSup_eq_left
  条件: {b : β} {f : 对任意 x : β, x = b -> α}
  证明: le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_rfl)) le_ciSup_ciSup_eq_left

@[simp]

Depends on / 依赖: ciSup_le, le_antisymm, le_ciSup_ciSup_eq_left, le_rfl
-/
theorem ciSup_ciSup_eq_left {b : β} {f : forall x : β, x = b -> α} :
    ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_rfl)) le_ciSup_ciSup_eq_left

@[simp]
/--
theorem `ciSup_ciSup_eq_right` / 定理 `ciSup_ciSup_eq_right`

English:
theorem ciSup_ciSup_eq_right
  given: {b : β} {f : forall x : β, b = x -> α}
  proof: le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_refl (f b rfl))) le_ciSup_ciSup_eq_right

中文:
定理 ciSup_ciSup_eq_right
  条件: {b : β} {f : 对任意 x : β, b = x -> α}
  证明: le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_refl (f b rfl))) le_ciSup_ciSup_eq_right

Depends on / 依赖: ciSup_le, le_antisymm, le_ciSup_ciSup_eq_right, le_refl
-/
theorem ciSup_ciSup_eq_right {b : β} {f : forall x : β, b = x -> α} :
    ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  le_antisymm (ciSup_le' fun _ => ciSup_le' (· ▸ le_refl (f b rfl))) le_ciSup_ciSup_eq_right

/--
lemma `ciSup_or'` / 引理 `ciSup_or'`

English:
lemma ciSup_or'
  given: (p q : Prop) (f : p ∨ q -> α)
  proof: by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]

中文:
引理 ciSup_or'
  条件: (p q : 命题) (f : p ∨ q -> α)
  证明: by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]
-/
lemma ciSup_or' (p q : Prop) (f : p ∨ q -> α) :
    ⨆ (h : p ∨ q), f h = (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h) := by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]

end ConditionallyCompleteLinearOrderBot

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α -> β}
  {u : β -> α}

/--
theorem `l_csSup` / 定理 `l_csSup`

English:
theorem l_csSup
  given: (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s)
  proof: Eq.symm IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

中文:
定理 l_csSup
  条件: (gc : GaloisConnection l u) {s : 集合 α} (hne : s.非空) (hbdd : BddAbove s)
  证明: Eq.symm IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

Depends on / 依赖: Eq.symm, IsLUB.ciSup_set_eq, ciSup_set_eq, gc.isLUB_l_image, isLUB_csSup, isLUB_l_image
-/
theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
Eq.symm IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

/--
theorem `l_csSup'` / 定理 `l_csSup'`

English:
theorem l_csSup'
  given: (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s)
  proof: by rw [gc.l_csSup hne hbdd, sSup_image']

中文:
定理 l_csSup'
  条件: (gc : GaloisConnection l u) {s : 集合 α} (hne : s.非空) (hbdd : BddAbove s)
  证明: by rw [gc.l_csSup hne hbdd, sSup_image']

Depends on / 依赖: gc.l_csSup, l_csSup, sSup_image
-/
theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']

/--
theorem `l_ciSup` / 定理 `l_ciSup`

English:
theorem l_ciSup
  given: (gc : GaloisConnection l u) {f : ι -> α} (hf : BddAbove (range f))
  proof: by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

中文:
定理 l_ciSup
  条件: (gc : GaloisConnection l u) {f : ι -> α} (hf : BddAbove (range f))
  证明: by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

Depends on / 依赖: gc.l_csSup, iSup_range, l_csSup, range_nonempty
-/
theorem l_ciSup (gc : GaloisConnection l u) {f : ι -> α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

/--
theorem `l_ciSup_set` / 定理 `l_ciSup_set`

English:
theorem l_ciSup_set
  statement: (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α} (hf : BddAbove (f '' s))
  proof: by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

中文:
定理 l_ciSup_set
  结论: (gc : GaloisConnection l u) {s : 集合 γ} {f : γ -> α} (hf : BddAbove (f '' s))
  证明: by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

Depends on / 依赖: gc.l_ciSup, hne.to_subtype, image_eq_range, l_ciSup, to_subtype
-/
theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

/--
theorem `u_csInf` / 定理 `u_csInf`

English:
theorem u_csInf
  given: (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s)
  proof: gc.dual.l_csSup hne hbdd

中文:
定理 u_csInf
  条件: (gc : GaloisConnection l u) {s : 集合 β} (hne : s.非空) (hbdd : BddBelow s)
  证明: gc.dual.l_csSup hne hbdd

Depends on / 依赖: gc.dual.l_csSup, l_csSup
-/
theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd

/--
theorem `u_csInf'` / 定理 `u_csInf'`

English:
theorem u_csInf'
  given: (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s)
  proof: gc.dual.l_csSup' hne hbdd

中文:
定理 u_csInf'
  条件: (gc : GaloisConnection l u) {s : 集合 β} (hne : s.非空) (hbdd : BddBelow s)
  证明: gc.dual.l_csSup' hne hbdd

Depends on / 依赖: gc.dual.l_csSup, l_csSup
-/
theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd

/--
theorem `u_ciInf` / 定理 `u_ciInf`

English:
theorem u_ciInf
  given: (gc : GaloisConnection l u) {f : ι -> β} (hf : BddBelow (range f))
  proof: gc.dual.l_ciSup hf

中文:
定理 u_ciInf
  条件: (gc : GaloisConnection l u) {f : ι -> β} (hf : BddBelow (range f))
  证明: gc.dual.l_ciSup hf

Depends on / 依赖: gc.dual.l_ciSup, l_ciSup
-/
theorem u_ciInf (gc : GaloisConnection l u) {f : ι -> β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf

/--
theorem `u_ciInf_set` / 定理 `u_ciInf_set`

English:
theorem u_ciInf_set
  statement: (gc : GaloisConnection l u) {s : Set γ} {f : γ -> β} (hf : BddBelow (f '' s))
  proof: gc.dual.l_ciSup_set hf hne

中文:
定理 u_ciInf_set
  结论: (gc : GaloisConnection l u) {s : 集合 γ} {f : γ -> β} (hf : BddBelow (f '' s))
  证明: gc.dual.l_ciSup_set hf hne

Depends on / 依赖: gc.dual.l_ciSup_set, l_ciSup_set
-/
theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ -> β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne

end GaloisConnection

namespace OrderIso

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

/--
theorem `map_csSup` / 定理 `map_csSup`

English:
theorem map_csSup
  given: (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s)
  proof: e.to_galoisConnection.l_csSup hne hbdd

中文:
定理 map_csSup
  条件: (e : α ≃o β) {s : 集合 α} (hne : s.非空) (hbdd : BddAbove s)
  证明: e.to_galoisConnection.l_csSup hne hbdd

Depends on / 依赖: e.to_galoisConnection.l_csSup, l_csSup, to_galoisConnection
-/
theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd

/--
theorem `map_csSup'` / 定理 `map_csSup'`

English:
theorem map_csSup'
  given: (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s)
  proof: e.to_galoisConnection.l_csSup' hne hbdd

中文:
定理 map_csSup'
  条件: (e : α ≃o β) {s : 集合 α} (hne : s.非空) (hbdd : BddAbove s)
  证明: e.to_galoisConnection.l_csSup' hne hbdd

Depends on / 依赖: e.to_galoisConnection.l_csSup, l_csSup, to_galoisConnection
-/
theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd

/--
theorem `map_ciSup` / 定理 `map_ciSup`

English:
theorem map_ciSup
  given: (e : α ≃o β) {f : ι -> α} (hf : BddAbove (range f))
  proof: e.to_galoisConnection.l_ciSup hf

中文:
定理 map_ciSup
  条件: (e : α ≃o β) {f : ι -> α} (hf : BddAbove (range f))
  证明: e.to_galoisConnection.l_ciSup hf

Depends on / 依赖: e.to_galoisConnection.l_ciSup, l_ciSup, to_galoisConnection
-/
theorem map_ciSup (e : α ≃o β) {f : ι -> α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf

/--
theorem `map_ciSup_set` / 定理 `map_ciSup_set`

English:
theorem map_ciSup_set
  statement: (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddAbove (f '' s))
  proof: e.to_galoisConnection.l_ciSup_set hf hne

中文:
定理 map_ciSup_set
  结论: (e : α ≃o β) {s : 集合 γ} {f : γ -> α} (hf : BddAbove (f '' s))
  证明: e.to_galoisConnection.l_ciSup_set hf hne

Depends on / 依赖: e.to_galoisConnection.l_ciSup_set, l_ciSup_set, to_galoisConnection
-/
theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne

/--
theorem `map_csInf` / 定理 `map_csInf`

English:
theorem map_csInf
  given: (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s)
  proof: e.dual.map_csSup hne hbdd

中文:
定理 map_csInf
  条件: (e : α ≃o β) {s : 集合 α} (hne : s.非空) (hbdd : BddBelow s)
  证明: e.dual.map_csSup hne hbdd

Depends on / 依赖: e.dual.map_csSup, map_csSup
-/
theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd

/--
theorem `map_csInf'` / 定理 `map_csInf'`

English:
theorem map_csInf'
  given: (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s)
  proof: e.dual.map_csSup' hne hbdd

中文:
定理 map_csInf'
  条件: (e : α ≃o β) {s : 集合 α} (hne : s.非空) (hbdd : BddBelow s)
  证明: e.dual.map_csSup' hne hbdd

Depends on / 依赖: e.dual.map_csSup, map_csSup
-/
theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd

/--
theorem `map_ciInf` / 定理 `map_ciInf`

English:
theorem map_ciInf
  given: (e : α ≃o β) {f : ι -> α} (hf : BddBelow (range f))
  proof: e.dual.map_ciSup hf

中文:
定理 map_ciInf
  条件: (e : α ≃o β) {f : ι -> α} (hf : BddBelow (range f))
  证明: e.dual.map_ciSup hf

Depends on / 依赖: e.dual.map_ciSup, map_ciSup
-/
theorem map_ciInf (e : α ≃o β) {f : ι -> α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf

/--
theorem `map_ciInf_set` / 定理 `map_ciInf_set`

English:
theorem map_ciInf_set
  statement: (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddBelow (f '' s))
  proof: e.dual.map_ciSup_set hf hne

中文:
定理 map_ciInf_set
  结论: (e : α ≃o β) {s : 集合 γ} {f : γ -> α} (hf : BddBelow (f '' s))
  证明: e.dual.map_ciSup_set hf hne

Depends on / 依赖: e.dual.map_ciSup_set, map_ciSup_set
-/
theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrderBot β]

@[simp]
/--
lemma `map_ciSup'` / 引理 `map_ciSup'`

English:
lemma map_ciSup'
  given: (e : α ≃o β) (f : ι -> α)
  statement: e (⨆ i, f i) = ⨆ i, e (f i)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i => e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

中文:
引理 map_ciSup'
  条件: (e : α ≃o β) (f : ι -> α)
  结论: e (⨆ i, f i) = ⨆ i, e (f i)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i => e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

Depends on / 依赖: BddAbove, Nonempty, Set.Nonempty, e.map_ciSup, e.surjective.forall, isEmpty_or_nonempty, map_bot, map_ciSup, surjective, upperBounds
-/
lemma map_ciSup' (e : α ≃o β) (f : ι -> α) : e (⨆ i, f i) = ⨆ i, e (f i) := by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i => e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

end ConditionallyCompleteLinearOrderBot
end OrderIso

section WithTopBot

namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α] {f : ι -> α}

/--
lemma `iSup_coe_eq_top` / 引理 `iSup_coe_eq_top`

English:
lemma iSup_coe_eq_top
  statement: ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f)
  proof: by
  rw [iSup_eq_top]; rw [not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.n

中文:
引理 iSup_coe_eq_top
  结论: ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f)
  证明: by
  rw [iSup_eq_top]; rw [not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.n

Depends on / 依赖: WithTop, WithTop.coe_lt_coe.mp, WithTop.coe_lt_coe.mpr, WithTop.coe_lt_top, WithTop.coe_untop, a.untop, coe_lt_coe, coe_lt_top, coe_untop, ha.ne, iSup_eq_top, not_bddAbove_iff
-/
lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top]; rw [not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩

/--
lemma `iSup_coe_lt_top` / 引理 `iSup_coe_lt_top`

English:
lemma iSup_coe_lt_top
  statement: ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f)
  proof: lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

中文:
引理 iSup_coe_lt_top
  结论: ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f)
  证明: lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

Depends on / 依赖: iSup_coe_eq_top, iSup_coe_eq_top.not_left, lt_top_iff_ne_top, lt_top_iff_ne_top.trans, not_left
-/
lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

/--
lemma `iInf_coe_eq_top` / 引理 `iInf_coe_eq_top`

English:
lemma iInf_coe_eq_top
  statement: ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι
  proof: by simp [isEmpty_iff]

中文:
引理 iInf_coe_eq_top
  结论: ⨅ x, (f x : WithTop α) = ⊤ ↔ 是空 ι
  证明: by simp [isEmpty_iff]

Depends on / 依赖: isEmpty_iff
-/
lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]

/--
lemma `iInf_coe_lt_top` / 引理 `iInf_coe_lt_top`

English:
lemma iInf_coe_lt_top
  statement: ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι
  proof: by
  rw [lt_top_iff_ne_top]; rw [Ne]; rw [iInf_coe_eq_top]; rw [not_isEmpty_iff]

中文:
引理 iInf_coe_lt_top
  结论: ⨅ i, (f i : WithTop α) < ⊤ ↔ 非空 ι
  证明: by
  rw [lt_top_iff_ne_top]; rw [Ne]; rw [iInf_coe_eq_top]; rw [not_isEmpty_iff]

Depends on / 依赖: iInf_coe_eq_top, lt_top_iff_ne_top, not_isEmpty_iff
-/
lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top]; rw [Ne]; rw [iInf_coe_eq_top]; rw [not_isEmpty_iff]

end WithTop

end WithTopBot
