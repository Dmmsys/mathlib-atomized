/-
Copyright (c) 2024 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal-indexed approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal-indexed approximation of the least fixed point
  greater or equal than an initial value of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal-indexed approximation of the greatest fixed point
  less or equal than an initial value of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_mem_range_lfpApprox`: The ordinal-indexed approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_mem_range_gfpApprox`: The ordinal-indexed approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

@[expose] public section

namespace Cardinal

universe u
variable {α : Type u}
variable (g : Ordinal -> α)

open Cardinal Ordinal SuccOrder Function Set

/--
theorem `not_injective_limitation_set` / 定理 `not_injective_limitation_set`

English:
theorem not_injective_limitation_set
  statement: ¬ InjOn g (Iio (ord <| succ #α))
  proof: by
  intro h_inj
have h := lift_mk_le_lift_mk_of_injective injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_ofPred, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype]; rw

中文:
定理 not_injective_limitation_set
  结论: ¬ 单射限制 g (左无界右开区间 (ord <| succ #α))
  证明: by
  intro h_inj
have h := lift_mk_le_lift_mk_of_injective injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_ofPred, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype]; rw

Depends on / 依赖: Order.lt_succ, card_ord, card_typein, coe_ofPred, h_inj, injOn_iff_injective, lift_le, lift_lift, lift_mk_le_lift_mk_of_injective, lt_succ, mk_Iio_ordinal, mk_initialSeg_subtype, not_le_of_gt
-/
theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
have h := lift_mk_le_lift_mk_of_injective injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_ofPred, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype]; rw [lift_lift]; rw [lift_le] at h
  exact not_le_of_gt (Order.lt_succ #α) h

end Cardinal

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α ->o α) {x : α} {a b c : Ordinal.{u}}

open Function fixedPoints Cardinal Order OrderHom

variable (x) in
/--
Definition of `lfpApprox` / `lfpApprox` 的定义

English:
definition lfpApprox
  signature: (a : Ordinal.{u})
  body: x ⊔ ⨆ b < a, f (lfpApprox b)
termination_by a

中文:
定义 lfpApprox
  签名: (a : 序数.{u})
  定义体: x ⊔ ⨆ b < a, f (lfpApprox b)
termination_by a

Depends on / 依赖: lfpApprox, termination_by
-/
def lfpApprox (a : Ordinal.{u}) : α :=
  x ⊔ ⨆ b < a, f (lfpApprox b)
termination_by a

/--
theorem `lfpApprox_mono_right` / 定理 `lfpApprox_mono_right`

English:
theorem lfpApprox_mono_right
  statement: Monotone (lfpApprox f x)
  proof: by
  intro a b h
  rw [lfpApprox]; rw [lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind

@[deprecated (since := "2026-03-30")] alias lfpApprox_monotone := lfpApprox_mono_right

中文:
定理 lfpApprox_mono_right
  结论: 递增 (lfpApprox f x)
  证明: by
  intro a b h
  rw [lfpApprox]; rw [lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind

@[deprecated (since := "2026-03-30")] alias lfpApprox_monotone := lfpApprox_mono_right

Depends on / 依赖: lfpApprox, sup_le_sup_left
-/
theorem lfpApprox_mono_right : Monotone (lfpApprox f x) := by
  intro a b h
  rw [lfpApprox]; rw [lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind

@[deprecated (since := "2026-03-30")] alias lfpApprox_monotone := lfpApprox_mono_right

/--
theorem `lfpApprox_zero` / 定理 `lfpApprox_zero`

English:
theorem lfpApprox_zero
  statement: lfpApprox f x 0 = x
  proof: by
  rw [lfpApprox]
  simp

中文:
定理 lfpApprox_zero
  结论: lfpApprox f x 0 = x
  证明: by
  rw [lfpApprox]
  simp

Depends on / 依赖: lfpApprox
-/
theorem lfpApprox_zero : lfpApprox f x 0 = x := by
  rw [lfpApprox]
  simp

/--
theorem `le_lfpApprox` / 定理 `le_lfpApprox`

English:
theorem le_lfpApprox
  given: {a : Ordinal}
  statement: x <= lfpApprox f x a
  proof: by
  rw [lfpApprox]
  exact le_sup_left

中文:
定理 le_lfpApprox
  条件: {a : 序数}
  结论: x <= lfpApprox f x a
  证明: by
  rw [lfpApprox]
  exact le_sup_left

Depends on / 依赖: le_sup_left, lfpApprox
-/
theorem le_lfpApprox {a : Ordinal} : x <= lfpApprox f x a := by
  rw [lfpApprox]
  exact le_sup_left

/--
theorem `apply_lfpApprox_le_lfpApprox_of_lt` / 定理 `apply_lfpApprox_le_lfpApprox_of_lt`

English:
theorem apply_lfpApprox_le_lfpApprox_of_lt
  given: {a b : Ordinal} (h : a < b)
  proof: by
  nth_rw 2 [lfpApprox]
exact le_sup_of_le_right le_iSup₂_of_le a h le_rfl

中文:
定理 apply_lfpApprox_le_lfpApprox_of_lt
  条件: {a b : 序数} (h : a < b)
  证明: by
  nth_rw 2 [lfpApprox]
exact le_sup_of_le_right le_iSup₂_of_le a h le_rfl

Depends on / 依赖: le_rfl, le_sup_of_le_right, lfpApprox, nth_rw
-/
theorem apply_lfpApprox_le_lfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    f (lfpApprox f x a) <= lfpApprox f x b := by
  nth_rw 2 [lfpApprox]
exact le_sup_of_le_right le_iSup₂_of_le a h le_rfl

/--
theorem `lfpApprox_add_one` / 定理 `lfpApprox_add_one`

English:
theorem lfpApprox_add_one
  given: (hx : x <= f x) (a : Ordinal)
  proof: by
  apply (apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one a)).antisymm'
  rw [lfpApprox]
apply sup_le hx.trans (f.mono (le_lfpApprox f))
  simpa using fun i h => f.monotone.comp (lfpApprox_mono_right f) h

中文:
定理 lfpApprox_add_one
  条件: (hx : x <= f x) (a : 序数)
  证明: by
  apply (apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one a)).antisymm'
  rw [lfpApprox]
apply sup_le hx.trans (f.mono (le_lfpApprox f))
  simpa using fun i h => f.monotone.comp (lfpApprox_mono_right f) h

Depends on / 依赖: antisymm, apply_lfpApprox_le_lfpApprox_of_lt, f.mono, f.monotone.comp, hx.trans, le_lfpApprox, lfpApprox, lfpApprox_mono_right, lt_add_one, monotone, sup_le
-/
theorem lfpApprox_add_one (hx : x <= f x) (a : Ordinal) :
    lfpApprox f x (a + 1) = f (lfpApprox f x a) := by
  apply (apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one a)).antisymm'
  rw [lfpApprox]
apply sup_le hx.trans (f.mono (le_lfpApprox f))
  simpa using fun i h => f.monotone.comp (lfpApprox_mono_right f) h

/--
theorem `lfpApprox_of_isSuccLimit` / 定理 `lfpApprox_of_isSuccLimit`

English:
theorem lfpApprox_of_isSuccLimit
  given: {a : Ordinal} (ha : Order.IsSuccLimit a)
  proof: by
  apply (iSup_le fun b => lfpApprox_mono_right f b.2.le).antisymm'
  rw [lfpApprox]; rw [sup_le_iff]; rw [iSup_le_iff]
  constructor
  · refine le_iSup_of_le ⟨0, ha.bot_lt⟩ (by simp [lfpApprox_zero])
  · exact fun b => iSup_mono' fun hab => ⟨⟨b + 1, ha.succ_lt hab⟩, (by
    simpa using apply_lfpA

中文:
定理 lfpApprox_of_isSuccLimit
  条件: {a : 序数} (ha : Order.是SuccLimit a)
  证明: by
  apply (iSup_le fun b => lfpApprox_mono_right f b.2.le).antisymm'
  rw [lfpApprox]; rw [sup_le_iff]; rw [iSup_le_iff]
  constructor
  · refine le_iSup_of_le ⟨0, ha.bot_lt⟩ (by simp [lfpApprox_zero])
  · exact fun b => iSup_mono' fun hab => ⟨⟨b + 1, ha.succ_lt hab⟩, (by
    simpa using apply_lfpA

Depends on / 依赖: antisymm, apply_lfpApprox_le_lfpApprox_of_lt, bot_lt, ha.bot_lt, ha.succ_lt, iSup_le, iSup_le_iff, iSup_mono, le_iSup_of_le, lfpApprox, lfpApprox_mono_right, lfpApprox_zero, lt_add_one, succ_lt, sup_le_iff
-/
theorem lfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    lfpApprox f x a = ⨆ b : Set.Iio a, lfpApprox f x b := by
  apply (iSup_le fun b => lfpApprox_mono_right f b.2.le).antisymm'
  rw [lfpApprox]; rw [sup_le_iff]; rw [iSup_le_iff]
  constructor
  · refine le_iSup_of_le ⟨0, ha.bot_lt⟩ (by simp [lfpApprox_zero])
  · exact fun b => iSup_mono' fun hab => ⟨⟨b + 1, ha.succ_lt hab⟩, (by
    simpa using apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one b))⟩

/--
theorem `lfpApprox_mono_left` / 定理 `lfpApprox_mono_left`

English:
theorem lfpApprox_mono_left
  statement: Monotone (lfpApprox : (α ->o α) -> _)
  proof: by
  intro f g h x a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
  exact sup_le_sup_left (iSup₂_mono fun j hj => (f.mono (IH j hj)).trans (h _)) _

中文:
定理 lfpApprox_mono_left
  结论: 递增 (lfpApprox : (α ->o α) -> _)
  证明: by
  intro f g h x a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
  exact sup_le_sup_left (iSup₂_mono fun j hj => (f.mono (IH j hj)).trans (h _)) _

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, f.mono, lfpApprox, sup_le_sup_left
-/
theorem lfpApprox_mono_left : Monotone (lfpApprox : (α ->o α) -> _) := by
  intro f g h x a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
  exact sup_le_sup_left (iSup₂_mono fun j hj => (f.mono (IH j hj)).trans (h _)) _

/--
theorem `lfpApprox_mono_mid` / 定理 `lfpApprox_mono_mid`

English:
theorem lfpApprox_mono_mid
  statement: Monotone (lfpApprox f)
  proof: by
  intro x₁ x₂ h a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
exact sup_le_sup h iSup₂_mono fun j hj => f.mono (IH j hj)

中文:
定理 lfpApprox_mono_mid
  结论: 递增 (lfpApprox f)
  证明: by
  intro x₁ x₂ h a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
exact sup_le_sup h iSup₂_mono fun j hj => f.mono (IH j hj)

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, f.mono, lfpApprox, sup_le_sup
-/
theorem lfpApprox_mono_mid : Monotone (lfpApprox f) := by
  intro x₁ x₂ h a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]; rw [lfpApprox]
exact sup_le_sup h iSup₂_mono fun j hj => f.mono (IH j hj)

/--
theorem `lfpApprox_eq_of_mem_fixedPoints` / 定理 `lfpApprox_eq_of_mem_fixedPoints`

English:
theorem lfpApprox_eq_of_mem_fixedPoints
  statement: (hab : a <= b)
  proof: by
  rw [mem_fixedPoints_iff] at hf
  induction b using WellFoundedLT.induction with | ind b IH
  apply (lfpApprox_mono_right f hab).antisymm'
  rw [lfpApprox]
  apply sup_le (le_lfpApprox ..)
  rw [iSup₂_le_iff]
  intro i hi
  by_cases! hi' : i < a
  · exact apply_lfpApprox_le_lfpApprox_of_lt f hi'

中文:
定理 lfpApprox_eq_of_mem_fixedPoints
  结论: (hab : a <= b)
  证明: by
  rw [mem_fixedPoints_iff] at hf
  induction b using WellFoundedLT.induction with | ind b IH
  apply (lfpApprox_mono_right f hab).antisymm'
  rw [lfpApprox]
  apply sup_le (le_lfpApprox ..)
  rw [iSup₂_le_iff]
  intro i hi
  by_cases! hi' : i < a
  · exact apply_lfpApprox_le_lfpApprox_of_lt f hi'

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, antisymm, apply_lfpApprox_le_lfpApprox_of_lt, le_lfpApprox, lfpApprox, lfpApprox_mono_right, mem_fixedPoints_iff, sup_le
-/
theorem lfpApprox_eq_of_mem_fixedPoints (hab : a <= b)
    (hf : lfpApprox f x a in fixedPoints f) : lfpApprox f x b = lfpApprox f x a := by
  rw [mem_fixedPoints_iff] at hf
  induction b using WellFoundedLT.induction with | ind b IH
  apply (lfpApprox_mono_right f hab).antisymm'
  rw [lfpApprox]
  apply sup_le (le_lfpApprox ..)
  rw [iSup₂_le_iff]
  intro i hi
  by_cases! hi' : i < a
  · exact apply_lfpApprox_le_lfpApprox_of_lt f hi'
  · simp [IH i hi hi', hf]

/--
theorem `lfpApprox_eq_all_of_fixedPoint` / 定理 `lfpApprox_eq_all_of_fixedPoint`

English:
theorem lfpApprox_eq_all_of_fixedPoint
  given: (hx : x <= f x)
  proof: by
  refine ⟨fun h => ?_, fun h o => ?_⟩
  · specialize h 1
    rwa [← zero_add 1, lfpApprox_add_one f hx, lfpApprox_zero] at h
  · have : lfpApprox f x 0 in fixedPoints f := by
      rwa [mem_fixedPoints_iff, lfpApprox_zero]
    simpa [lfpApprox_zero] using
      lfpApprox_eq_of_mem_fixedPoints f z

中文:
定理 lfpApprox_eq_all_of_fixedPoint
  条件: (hx : x <= f x)
  证明: by
  refine ⟨fun h => ?_, fun h o => ?_⟩
  · specialize h 1
    rwa [← zero_add 1, lfpApprox_add_one f hx, lfpApprox_zero] at h
  · have : lfpApprox f x 0 in fixedPoints f := by
      rwa [mem_fixedPoints_iff, lfpApprox_zero]
    simpa [lfpApprox_zero] using
      lfpApprox_eq_of_mem_fixedPoints f z

Depends on / 依赖: fixedPoints, lfpApprox, lfpApprox_add_one, lfpApprox_eq_of_mem_fixedPoints, lfpApprox_zero, mem_fixedPoints_iff, specialize, zero_add, zero_le
-/
theorem lfpApprox_eq_all_of_fixedPoint (hx : x <= f x) :
    (forall o, lfpApprox f x o = x) ↔ f x = x := by
  refine ⟨fun h => ?_, fun h o => ?_⟩
  · specialize h 1
    rwa [← zero_add 1, lfpApprox_add_one f hx, lfpApprox_zero] at h
  · have : lfpApprox f x 0 in fixedPoints f := by
      rwa [mem_fixedPoints_iff, lfpApprox_zero]
    simpa [lfpApprox_zero] using
      lfpApprox_eq_of_mem_fixedPoints f zero_le this

/--
lemma `lfpApprox_mem_fixedPoints_of_eq` / 引理 `lfpApprox_mem_fixedPoints_of_eq`

English:
lemma lfpApprox_mem_fixedPoints_of_eq
  statement: (hx : x <= f x) (hab : a < b) (hac : a <= c)
  proof: by
  have H : lfpApprox f x a in fixedPoints f := by
    rw [mem_fixedPoints_iff]; rw [← lfpApprox_add_one f hx]
    exact (lfpApprox_mono_right f).eq_of_ge_of_le
      hf (lt_add_one a).le (add_one_le_of_lt hab)
  rwa [lfpApprox_eq_of_mem_fixedPoints f hac H]

中文:
引理 lfpApprox_mem_fixedPoints_of_eq
  结论: (hx : x <= f x) (hab : a < b) (hac : a <= c)
  证明: by
  have H : lfpApprox f x a in fixedPoints f := by
    rw [mem_fixedPoints_iff]; rw [← lfpApprox_add_one f hx]
    exact (lfpApprox_mono_right f).eq_of_ge_of_le
      hf (lt_add_one a).le (add_one_le_of_lt hab)
  rwa [lfpApprox_eq_of_mem_fixedPoints f hac H]

Depends on / 依赖: add_one_le_of_lt, eq_of_ge_of_le, fixedPoints, lfpApprox, lfpApprox_add_one, lfpApprox_eq_of_mem_fixedPoints, lfpApprox_mono_right, lt_add_one, mem_fixedPoints_iff
-/
lemma lfpApprox_mem_fixedPoints_of_eq (hx : x <= f x) (hab : a < b) (hac : a <= c)
    (hf : lfpApprox f x a = lfpApprox f x b) : lfpApprox f x c in fixedPoints f := by
  have H : lfpApprox f x a in fixedPoints f := by
    rw [mem_fixedPoints_iff]; rw [← lfpApprox_add_one f hx]
    exact (lfpApprox_mono_right f).eq_of_ge_of_le
      hf (lt_add_one a).le (add_one_le_of_lt hab)
  rwa [lfpApprox_eq_of_mem_fixedPoints f hac H]

/--
theorem `lfpApprox_eq_of_fixedPoint_or_zero` / 定理 `lfpApprox_eq_of_fixedPoint_or_zero`

English:
theorem lfpApprox_eq_of_fixedPoint_or_zero
  given: (hx : x <= f x) (o : Ordinal)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_ne o 0 with (rfl | ho)
    · exact Or.inr rfl
    · have hpos : (0 : Ordinal) < o :=
        zero_lt_one.trans_le (one_le_iff_ne_zero.mpr ho)
      have hmem : lfpApprox f x 0 in fixedPoints f :=
        lfpApprox_mem_fixedPoints_of_eq f hx hpo

中文:
定理 lfpApprox_eq_of_fixedPoint_or_zero
  条件: (hx : x <= f x) (o : 序数)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_ne o 0 with (rfl | ho)
    · exact Or.inr rfl
    · have hpos : (0 : Ordinal) < o :=
        zero_lt_one.trans_le (one_le_iff_ne_zero.mpr ho)
      have hmem : lfpApprox f x 0 in fixedPoints f :=
        lfpApprox_mem_fixedPoints_of_eq f hx hpo

Depends on / 依赖: Or.inl, Or.inr, Ordinal, eq_or_ne, fixedPoints, h.symm, le_refl, lfpApprox, lfpApprox_eq_all_of_fixedPoint, lfpApprox_mem_fixedPoints_of_eq, lfpApprox_zero, mem_fixedPoints_iff, mem_fixedPoints_iff.mp, one_le_iff_ne_zero, one_le_iff_ne_zero.mpr, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem lfpApprox_eq_of_fixedPoint_or_zero (hx : x <= f x) (o : Ordinal) :
    lfpApprox f x o = x ↔ f x = x ∨ o = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_ne o 0 with (rfl | ho)
    · exact Or.inr rfl
    · have hpos : (0 : Ordinal) < o :=
        zero_lt_one.trans_le (one_le_iff_ne_zero.mpr ho)
      have hmem : lfpApprox f x 0 in fixedPoints f :=
        lfpApprox_mem_fixedPoints_of_eq f hx hpos (le_refl _)
          ((lfpApprox_zero f).trans h.symm)
      have hfx : f x = x :=
        (mem_fixedPoints_iff.mp (by simpa [lfpApprox_zero] using hmem))
      exact Or.inl hfx
  · rcases h with (hf | rfl)
    · exact (lfpApprox_eq_all_of_fixedPoint f hx).mpr hf o
    · exact lfpApprox_zero f

variable (x) in
/--
theorem `exists_lfpApprox_eq_lfpApprox` / 定理 `exists_lfpApprox_eq_lfpApprox`

English:
theorem exists_lfpApprox_eq_lfpApprox
  statement: exists a < ord succ #α, exists b < ord succ #α,
  proof: by
have h_ninj := not_injective_limitation_set lfpApprox f x
  rw [Set.injOn_iff_injective]; rw [Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] a

中文:
定理 存在_lfpApprox_eq_lfpApprox
  结论: 存在 a < ord succ #α, 存在 b < ord succ #α,
  证明: by
have h_ninj := not_injective_limitation_set lfpApprox f x
  rw [Set.injOn_iff_injective]; rw [Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] a

Depends on / 依赖: And.intro, Function, Function.not_injective_iff, Set.injOn_iff_injective, Subtype, Subtype.coe_inj, a.prop, a.val, b.prop, b.val, coe_inj, h_eq, h_fab, h_nab, h_ninj, injOn_iff_injective, lfpApprox, not_injective_iff, not_injective_limitation_set
-/
theorem exists_lfpApprox_eq_lfpApprox : exists a < ord succ #α, exists b < ord succ #α,
    a != b ∧ lfpApprox f x a = lfpApprox f x b := by
have h_ninj := not_injective_limitation_set lfpApprox f x
  rw [Set.injOn_iff_injective]; rw [Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/--
theorem `lfpApprox_ord_mem_fixedPoint` / 定理 `lfpApprox_ord_mem_fixedPoint`

English:
theorem lfpApprox_ord_mem_fixedPoint
  given: (hx : x <= f x)
  proof: by
  let ⟨a, ha, b, hb, hne, hf⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl hab => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.lt_of_le hab) ha.le hf
  | inr hba => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.symm.lt_of_le hba) hb.le hf.symm

中文:
定理 lfpApprox_ord_mem_fixedPoint
  条件: (hx : x <= f x)
  证明: by
  let ⟨a, ha, b, hb, hne, hf⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl hab => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.lt_of_le hab) ha.le hf
  | inr hba => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.symm.lt_of_le hba) hb.le hf.symm

Depends on / 依赖: exists_lfpApprox_eq_lfpApprox, ha.le, hb.le, hf.symm, hne.lt_of_le, hne.symm.lt_of_le, le_total, lfpApprox_mem_fixedPoints_of_eq, lt_of_le
-/
theorem lfpApprox_ord_mem_fixedPoint (hx : x <= f x) :
    lfpApprox f x (ord <| succ #α) in fixedPoints f := by
  let ⟨a, ha, b, hb, hne, hf⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl hab => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.lt_of_le hab) ha.le hf
  | inr hba => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.symm.lt_of_le hba) hb.le hf.symm

/--
theorem `lfpApprox_le_of_mem_fixedPoints` / 定理 `lfpApprox_le_of_mem_fixedPoints`

English:
theorem lfpApprox_le_of_mem_fixedPoints
  statement: {a : α}
  proof: by
  induction i using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]
  apply sup_le hxa
  rw [iSup₂_le_iff]; rw [← ha.eq]
  exact fun y hy => f.mono (IH y hy)

中文:
定理 lfpApprox_le_of_mem_fixedPoints
  结论: {a : α}
  证明: by
  induction i using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]
  apply sup_le hxa
  rw [iSup₂_le_iff]; rw [← ha.eq]
  exact fun y hy => f.mono (IH y hy)

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, f.mono, ha.eq, lfpApprox, sup_le
-/
theorem lfpApprox_le_of_mem_fixedPoints {a : α}
    (ha : a in fixedPoints f) (hxa : x <= a) (i : Ordinal) : lfpApprox f x i <= a := by
  induction i using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]
  apply sup_le hxa
  rw [iSup₂_le_iff]; rw [← ha.eq]
  exact fun y hy => f.mono (IH y hy)

/--
theorem `lfpApprox_ord_eq_lfp` / 定理 `lfpApprox_ord_eq_lfp`

English:
theorem lfpApprox_ord_eq_lfp
  statement: lfpApprox f ⊥ (ord <| succ #α) = f.lfp
  proof: by
  apply le_antisymm
  · have h_lfp : exists y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f y.2 bot_le (ord <| succ #α)
  · have h_fix : exists y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      sim

中文:
定理 lfpApprox_ord_eq_lfp
  结论: lfpApprox f ⊥ (ord <| succ #α) = f.lfp
  证明: by
  apply le_antisymm
  · have h_lfp : exists y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f y.2 bot_le (ord <| succ #α)
  · have h_fix : exists y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      sim

Depends on / 依赖: Subtype, Subtype.exists, bot_le, exists_eq_right, exists_prop, f.lfp, fixedPoints, h_fix, h_lfp, le_antisymm, lfpApprox, lfpApprox_le_of_mem_fixedPoints, lfpApprox_ord_mem_fixedPoint, lfp_le_fixed, mem_fixedPoints, x.prop
-/
theorem lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord <| succ #α) = f.lfp := by
  apply le_antisymm
  · have h_lfp : exists y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f y.2 bot_le (ord <| succ #α)
  · have h_fix : exists y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_ord_mem_fixedPoint f bot_le
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop

/--
theorem `lfp_mem_range_lfpApprox` / 定理 `lfp_mem_range_lfpApprox`

English:
theorem lfp_mem_range_lfpApprox
  statement: f.lfp in Set.range (lfpApprox f ⊥)
  proof: by
use ord succ #α
  exact lfpApprox_ord_eq_lfp f

中文:
定理 lfp_mem_range_lfpApprox
  结论: f.lfp in 集合.range (lfpApprox f ⊥)
  证明: by
use ord succ #α
  exact lfpApprox_ord_eq_lfp f

Depends on / 依赖: lfpApprox_ord_eq_lfp
-/
theorem lfp_mem_range_lfpApprox : f.lfp in Set.range (lfpApprox f ⊥) := by
use ord succ #α
  exact lfpApprox_ord_eq_lfp f

/--
lemma `iSup_lfpApprox_eq_of_mem_fixedPoints` / 引理 `iSup_lfpApprox_eq_of_mem_fixedPoints`

English:
lemma iSup_lfpApprox_eq_of_mem_fixedPoints
  given: (hf : lfpApprox f x a in fixedPoints f)
  proof: by
  apply (le_iSup (lfpApprox f x) a).antisymm'
  refine ciSup_le fun i => ?_
  by_cases h : i <= a
  · exact lfpApprox_mono_right f h
  · exact (lfpApprox_eq_of_mem_fixedPoints f (le_of_not_ge h) hf).le

中文:
引理 iSup_lfpApprox_eq_of_mem_fixedPoints
  条件: (hf : lfpApprox f x a in fixedPoints f)
  证明: by
  apply (le_iSup (lfpApprox f x) a).antisymm'
  refine ciSup_le fun i => ?_
  by_cases h : i <= a
  · exact lfpApprox_mono_right f h
  · exact (lfpApprox_eq_of_mem_fixedPoints f (le_of_not_ge h) hf).le

Depends on / 依赖: antisymm, ciSup_le, le_iSup, le_of_not_ge, lfpApprox, lfpApprox_eq_of_mem_fixedPoints, lfpApprox_mono_right
-/
lemma iSup_lfpApprox_eq_of_mem_fixedPoints (hf : lfpApprox f x a in fixedPoints f) :
    ⨆ i : Ordinal, lfpApprox f x i = lfpApprox f x a := by
  apply (le_iSup (lfpApprox f x) a).antisymm'
  refine ciSup_le fun i => ?_
  by_cases h : i <= a
  · exact lfpApprox_mono_right f h
  · exact (lfpApprox_eq_of_mem_fixedPoints f (le_of_not_ge h) hf).le

/--
theorem `nextFixed_eq_iSup_lfpApprox` / 定理 `nextFixed_eq_iSup_lfpApprox`

English:
theorem nextFixed_eq_iSup_lfpApprox
  given: (hx : x <= f x)
  proof: by
  let o := (succ #α).ord
  have hfix : lfpApprox f x o in fixedPoints f :=
    lfpApprox_ord_mem_fixedPoint f hx
  rw [iSup_lfpApprox_eq_of_mem_fixedPoints f hfix]
  apply le_antisymm
  · exact f.nextFixed_le hx (y := ⟨lfpApprox f x o, hfix⟩) (le_lfpApprox f)
  · exact lfpApprox_le_of_mem_fixedPo

中文:
定理 nextFixed_eq_iSup_lfpApprox
  条件: (hx : x <= f x)
  证明: by
  let o := (succ #α).ord
  have hfix : lfpApprox f x o in fixedPoints f :=
    lfpApprox_ord_mem_fixedPoint f hx
  rw [iSup_lfpApprox_eq_of_mem_fixedPoints f hfix]
  apply le_antisymm
  · exact f.nextFixed_le hx (y := ⟨lfpApprox f x o, hfix⟩) (le_lfpApprox f)
  · exact lfpApprox_le_of_mem_fixedPo

Depends on / 依赖: f.le_nextFixed, f.nextFixed, f.nextFixed_le, fixedPoints, iSup_lfpApprox_eq_of_mem_fixedPoints, le_antisymm, le_lfpApprox, le_nextFixed, lfpApprox, lfpApprox_le_of_mem_fixedPoints, lfpApprox_ord_mem_fixedPoint, nextFixed, nextFixed_le
-/
theorem nextFixed_eq_iSup_lfpApprox (hx : x <= f x) :
    (f.nextFixed x hx).val = ⨆ a : Ordinal, lfpApprox f x a := by
  let o := (succ #α).ord
  have hfix : lfpApprox f x o in fixedPoints f :=
    lfpApprox_ord_mem_fixedPoint f hx
  rw [iSup_lfpApprox_eq_of_mem_fixedPoints f hfix]
  apply le_antisymm
  · exact f.nextFixed_le hx (y := ⟨lfpApprox f x o, hfix⟩) (le_lfpApprox f)
  · exact lfpApprox_le_of_mem_fixedPoints f (f.nextFixed x hx).2 (f.le_nextFixed hx) o

variable (x) in
/--
Definition of `gfpApprox` / `gfpApprox` 的定义

English:
definition gfpApprox
  signature: (a : Ordinal.{u})
  body: x ⊓ ⨅ b < a, f (gfpApprox b)
termination_by a

中文:
定义 gfpApprox
  签名: (a : 序数.{u})
  定义体: x ⊓ ⨅ b < a, f (gfpApprox b)
termination_by a

Depends on / 依赖: gfpApprox, termination_by
-/
def gfpApprox (a : Ordinal.{u}) : α :=
  x ⊓ ⨅ b < a, f (gfpApprox b)
termination_by a

-- By unsealing these recursive definitions we can relate them
-- by definitional equality
unseal gfpApprox lfpApprox

/--
theorem `gfpApprox_zero` / 定理 `gfpApprox_zero`

English:
theorem gfpApprox_zero
  statement: gfpApprox f x 0 = x
  proof: by
  exact lfpApprox_zero f.dual

中文:
定理 gfpApprox_zero
  结论: gfpApprox f x 0 = x
  证明: by
  exact lfpApprox_zero f.dual

Depends on / 依赖: f.dual, lfpApprox_zero
-/
theorem gfpApprox_zero : gfpApprox f x 0 = x := by
  exact lfpApprox_zero f.dual

/--
theorem `gfpApprox_anti_right` / 定理 `gfpApprox_anti_right`

English:
theorem gfpApprox_anti_right
  statement: Antitone (gfpApprox f x)
  proof: lfpApprox_mono_right f.dual

@[deprecated (since := "2026-03-30")] alias gfpApprox_antitone := gfpApprox_anti_right

中文:
定理 gfpApprox_anti_right
  结论: 递减 (gfpApprox f x)
  证明: lfpApprox_mono_right f.dual

@[deprecated (since := "2026-03-30")] alias gfpApprox_antitone := gfpApprox_anti_right

Depends on / 依赖: f.dual, lfpApprox_mono_right
-/
theorem gfpApprox_anti_right : Antitone (gfpApprox f x) :=
  lfpApprox_mono_right f.dual

@[deprecated (since := "2026-03-30")] alias gfpApprox_antitone := gfpApprox_anti_right

/--
theorem `gfpApprox_le` / 定理 `gfpApprox_le`

English:
theorem gfpApprox_le
  given: {a : Ordinal}
  statement: gfpApprox f x a <= x
  proof: le_lfpApprox f.dual

中文:
定理 gfpApprox_le
  条件: {a : 序数}
  结论: gfpApprox f x a <= x
  证明: le_lfpApprox f.dual

Depends on / 依赖: f.dual, le_lfpApprox
-/
theorem gfpApprox_le {a : Ordinal} : gfpApprox f x a <= x :=
  le_lfpApprox f.dual

/--
theorem `gfpApprox_add_one` / 定理 `gfpApprox_add_one`

English:
theorem gfpApprox_add_one
  given: (hx : f x <= x) (a : Ordinal)
  proof: lfpApprox_add_one f.dual hx a

中文:
定理 gfpApprox_add_one
  条件: (hx : f x <= x) (a : 序数)
  证明: lfpApprox_add_one f.dual hx a

Depends on / 依赖: f.dual, lfpApprox_add_one
-/
theorem gfpApprox_add_one (hx : f x <= x) (a : Ordinal) :
    gfpApprox f x (a + 1) = f (gfpApprox f x a) :=
  lfpApprox_add_one f.dual hx a

/--
theorem `gfpApprox_le_apply_gfpApprox_of_lt` / 定理 `gfpApprox_le_apply_gfpApprox_of_lt`

English:
theorem gfpApprox_le_apply_gfpApprox_of_lt
  given: {a b : Ordinal} (h : a < b)
  proof: apply_lfpApprox_le_lfpApprox_of_lt f.dual h

中文:
定理 gfpApprox_le_apply_gfpApprox_of_lt
  条件: {a b : 序数} (h : a < b)
  证明: apply_lfpApprox_le_lfpApprox_of_lt f.dual h

Depends on / 依赖: apply_lfpApprox_le_lfpApprox_of_lt, f.dual
-/
theorem gfpApprox_le_apply_gfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    gfpApprox f x b <= f (gfpApprox f x a) :=
  apply_lfpApprox_le_lfpApprox_of_lt f.dual h

/--
theorem `gfpApprox_of_isSuccLimit` / 定理 `gfpApprox_of_isSuccLimit`

English:
theorem gfpApprox_of_isSuccLimit
  given: {a : Ordinal} (ha : Order.IsSuccLimit a)
  proof: lfpApprox_of_isSuccLimit f.dual ha

中文:
定理 gfpApprox_of_isSuccLimit
  条件: {a : 序数} (ha : Order.是SuccLimit a)
  证明: lfpApprox_of_isSuccLimit f.dual ha

Depends on / 依赖: f.dual, lfpApprox_of_isSuccLimit
-/
theorem gfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    gfpApprox f x a = ⨅ b : Set.Iio a, gfpApprox f x b :=
  lfpApprox_of_isSuccLimit f.dual ha

/--
theorem `gfpApprox_mono_left` / 定理 `gfpApprox_mono_left`

English:
theorem gfpApprox_mono_left
  statement: Monotone (gfpApprox : (α ->o α) -> _)
  proof: by
  intro f g h
  have : g.dual <= f.dual := h
  exact lfpApprox_mono_left this

中文:
定理 gfpApprox_mono_left
  结论: 递增 (gfpApprox : (α ->o α) -> _)
  证明: by
  intro f g h
  have : g.dual <= f.dual := h
  exact lfpApprox_mono_left this

Depends on / 依赖: f.dual, g.dual, lfpApprox_mono_left
-/
theorem gfpApprox_mono_left : Monotone (gfpApprox : (α ->o α) -> _) := by
  intro f g h
  have : g.dual <= f.dual := h
  exact lfpApprox_mono_left this

/--
theorem `gfpApprox_mono_mid` / 定理 `gfpApprox_mono_mid`

English:
theorem gfpApprox_mono_mid
  statement: Monotone (gfpApprox f)
  proof: fun _ _ h => lfpApprox_mono_mid f.dual h

中文:
定理 gfpApprox_mono_mid
  结论: 递增 (gfpApprox f)
  证明: fun _ _ h => lfpApprox_mono_mid f.dual h

Depends on / 依赖: f.dual, lfpApprox_mono_mid
-/
theorem gfpApprox_mono_mid : Monotone (gfpApprox f) :=
  fun _ _ h => lfpApprox_mono_mid f.dual h

/--
theorem `gfpApprox_eq_of_mem_fixedPoints` / 定理 `gfpApprox_eq_of_mem_fixedPoints`

English:
theorem gfpApprox_eq_of_mem_fixedPoints
  statement: {a b : Ordinal} (h_ab : a <= b)
  proof: lfpApprox_eq_of_mem_fixedPoints f.dual h_ab h

中文:
定理 gfpApprox_eq_of_mem_fixedPoints
  结论: {a b : 序数} (h_ab : a <= b)
  证明: lfpApprox_eq_of_mem_fixedPoints f.dual h_ab h

Depends on / 依赖: f.dual, h_ab, lfpApprox_eq_of_mem_fixedPoints
-/
theorem gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_ab : a <= b)
    (h : gfpApprox f x a in fixedPoints f) : gfpApprox f x b = gfpApprox f x a :=
  lfpApprox_eq_of_mem_fixedPoints f.dual h_ab h

/--
theorem `gfpApprox_eq_all_of_fixedPoint` / 定理 `gfpApprox_eq_all_of_fixedPoint`

English:
theorem gfpApprox_eq_all_of_fixedPoint
  given: (hx : f x <= x)
  proof: lfpApprox_eq_all_of_fixedPoint f.dual hx

中文:
定理 gfpApprox_eq_all_of_fixedPoint
  条件: (hx : f x <= x)
  证明: lfpApprox_eq_all_of_fixedPoint f.dual hx

Depends on / 依赖: f.dual, lfpApprox_eq_all_of_fixedPoint
-/
theorem gfpApprox_eq_all_of_fixedPoint (hx : f x <= x) :
    (forall o, gfpApprox f x o = x) ↔ f x = x :=
  lfpApprox_eq_all_of_fixedPoint f.dual hx

/--
lemma `gfpApprox_mem_fixedPoints_of_eq` / 引理 `gfpApprox_mem_fixedPoints_of_eq`

English:
lemma gfpApprox_mem_fixedPoints_of_eq
  statement: (hx : f x <= x) (hab : a < b) (hac : a <= c)
  proof: lfpApprox_mem_fixedPoints_of_eq f.dual hx hab hac hf

中文:
引理 gfpApprox_mem_fixedPoints_of_eq
  结论: (hx : f x <= x) (hab : a < b) (hac : a <= c)
  证明: lfpApprox_mem_fixedPoints_of_eq f.dual hx hab hac hf

Depends on / 依赖: f.dual, lfpApprox_mem_fixedPoints_of_eq
-/
lemma gfpApprox_mem_fixedPoints_of_eq (hx : f x <= x) (hab : a < b) (hac : a <= c)
    (hf : gfpApprox f x a = gfpApprox f x b) : gfpApprox f x c in fixedPoints f :=
  lfpApprox_mem_fixedPoints_of_eq f.dual hx hab hac hf

/--
theorem `gfpApprox_eq_of_fixedPoint_or_zero` / 定理 `gfpApprox_eq_of_fixedPoint_or_zero`

English:
theorem gfpApprox_eq_of_fixedPoint_or_zero
  given: (hx : f x <= x) (o : Ordinal)
  proof: lfpApprox_eq_of_fixedPoint_or_zero f.dual hx o

中文:
定理 gfpApprox_eq_of_fixedPoint_or_zero
  条件: (hx : f x <= x) (o : 序数)
  证明: lfpApprox_eq_of_fixedPoint_or_zero f.dual hx o

Depends on / 依赖: f.dual, lfpApprox_eq_of_fixedPoint_or_zero
-/
theorem gfpApprox_eq_of_fixedPoint_or_zero (hx : f x <= x) (o : Ordinal) :
    gfpApprox f x o = x ↔ f x = x ∨ o = 0 :=
  lfpApprox_eq_of_fixedPoint_or_zero f.dual hx o

/--
theorem `exists_gfpApprox_eq_gfpApprox` / 定理 `exists_gfpApprox_eq_gfpApprox`

English:
theorem exists_gfpApprox_eq_gfpApprox
  statement: exists a < ord succ #α, exists b < ord succ #α,
  proof: exists_lfpApprox_eq_lfpApprox f.dual x

中文:
定理 存在_gfpApprox_eq_gfpApprox
  结论: 存在 a < ord succ #α, 存在 b < ord succ #α,
  证明: exists_lfpApprox_eq_lfpApprox f.dual x

Depends on / 依赖: exists_lfpApprox_eq_lfpApprox, f.dual
-/
theorem exists_gfpApprox_eq_gfpApprox : exists a < ord succ #α, exists b < ord succ #α,
    a != b ∧ gfpApprox f x a = gfpApprox f x b :=
  exists_lfpApprox_eq_lfpApprox f.dual x

/--
lemma `gfpApprox_ord_mem_fixedPoint` / 引理 `gfpApprox_ord_mem_fixedPoint`

English:
lemma gfpApprox_ord_mem_fixedPoint
  given: (hx : f x <= x)
  proof: lfpApprox_ord_mem_fixedPoint f.dual hx

中文:
引理 gfpApprox_ord_mem_fixedPoint
  条件: (hx : f x <= x)
  证明: lfpApprox_ord_mem_fixedPoint f.dual hx

Depends on / 依赖: f.dual, lfpApprox_ord_mem_fixedPoint
-/
lemma gfpApprox_ord_mem_fixedPoint (hx : f x <= x) :
    gfpApprox f x (ord <| succ #α) in fixedPoints f :=
  lfpApprox_ord_mem_fixedPoint f.dual hx

/--
lemma `le_gfpApprox_of_mem_fixedPoints` / 引理 `le_gfpApprox_of_mem_fixedPoints`

English:
lemma le_gfpApprox_of_mem_fixedPoints
  statement: {a : α}
  proof: lfpApprox_le_of_mem_fixedPoints f.dual ha hax i

中文:
引理 le_gfpApprox_of_mem_fixedPoints
  结论: {a : α}
  证明: lfpApprox_le_of_mem_fixedPoints f.dual ha hax i

Depends on / 依赖: f.dual, lfpApprox_le_of_mem_fixedPoints
-/
lemma le_gfpApprox_of_mem_fixedPoints {a : α}
    (ha : a in fixedPoints f) (hax : a <= x) (i : Ordinal) : a <= gfpApprox f x i :=
  lfpApprox_le_of_mem_fixedPoints f.dual ha hax i

/--
theorem `gfpApprox_ord_eq_gfp` / 定理 `gfpApprox_ord_eq_gfp`

English:
theorem gfpApprox_ord_eq_gfp
  statement: gfpApprox f ⊤ (ord <| succ #α) = f.gfp
  proof: lfpApprox_ord_eq_lfp f.dual

中文:
定理 gfpApprox_ord_eq_gfp
  结论: gfpApprox f ⊤ (ord <| succ #α) = f.gfp
  证明: lfpApprox_ord_eq_lfp f.dual

Depends on / 依赖: f.dual, lfpApprox_ord_eq_lfp
-/
theorem gfpApprox_ord_eq_gfp : gfpApprox f ⊤ (ord <| succ #α) = f.gfp :=
  lfpApprox_ord_eq_lfp f.dual

/--
theorem `gfp_mem_range_gfpApprox` / 定理 `gfp_mem_range_gfpApprox`

English:
theorem gfp_mem_range_gfpApprox
  statement: f.gfp in Set.range (gfpApprox f ⊤)
  proof: lfp_mem_range_lfpApprox f.dual

中文:
定理 gfp_mem_range_gfpApprox
  结论: f.gfp in 集合.range (gfpApprox f ⊤)
  证明: lfp_mem_range_lfpApprox f.dual

Depends on / 依赖: f.dual, lfp_mem_range_lfpApprox
-/
theorem gfp_mem_range_gfpApprox : f.gfp in Set.range (gfpApprox f ⊤) :=
  lfp_mem_range_lfpApprox f.dual

/--
lemma `iInf_gfpApprox_eq_of_mem_fixedPoints` / 引理 `iInf_gfpApprox_eq_of_mem_fixedPoints`

English:
lemma iInf_gfpApprox_eq_of_mem_fixedPoints
  given: (hf : gfpApprox f x a in fixedPoints f)
  proof: iSup_lfpApprox_eq_of_mem_fixedPoints f.dual hf

中文:
引理 iInf_gfpApprox_eq_of_mem_fixedPoints
  条件: (hf : gfpApprox f x a in fixedPoints f)
  证明: iSup_lfpApprox_eq_of_mem_fixedPoints f.dual hf

Depends on / 依赖: f.dual, iSup_lfpApprox_eq_of_mem_fixedPoints
-/
lemma iInf_gfpApprox_eq_of_mem_fixedPoints (hf : gfpApprox f x a in fixedPoints f) :
    ⨅ i : Ordinal, gfpApprox f x i = gfpApprox f x a :=
  iSup_lfpApprox_eq_of_mem_fixedPoints f.dual hf

/--
theorem `prevFixed_eq_iInf_gfpApprox` / 定理 `prevFixed_eq_iInf_gfpApprox`

English:
theorem prevFixed_eq_iInf_gfpApprox
  given: (hx : f x <= x)
  proof: nextFixed_eq_iSup_lfpApprox f.dual hx

中文:
定理 prevFixed_eq_iInf_gfpApprox
  条件: (hx : f x <= x)
  证明: nextFixed_eq_iSup_lfpApprox f.dual hx

Depends on / 依赖: f.dual, nextFixed_eq_iSup_lfpApprox
-/
theorem prevFixed_eq_iInf_gfpApprox (hx : f x <= x) :
    (f.prevFixed x hx).val = ⨅ a : Ordinal, gfpApprox f x a :=
  nextFixed_eq_iSup_lfpApprox f.dual hx

end OrdinalApprox
