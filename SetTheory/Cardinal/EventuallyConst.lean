/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Eventually constant monotone functions

This file proves variations of the following theorem: if `α` is a linear order and `β` is a partial
order with `#β < cof α`, then any monotone function `f : α → β` must be eventually constant. In
particular, this applies for functions from `Cardinal.{u}` or `Ordinal.{u}` into a `Small.{u}` type.
-/

public section

universe u v

variable {α : Type u} {β : Type v} [LinearOrder α] [PartialOrder β]

open Cardinal Filter Order Set

namespace Filter.EventuallyConst
variable {f : α -> β}

/--
theorem `of_not_isCofinal_rangeSplitting` / 定理 `of_not_isCofinal_rangeSplitting`

English:
theorem of_not_isCofinal_rangeSplitting
  statement: [Nonempty α] (hf : Monotone f)
  proof: by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
refine ⟨i, fun j hij => (hf hij).antisymm' (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]

中文:
定理 of_not_isCofinal_rangeSplitting
  结论: [Nonempty α] (hf : Monotone f)
  证明: by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
refine ⟨i, fun j hij => (hf hij).antisymm' (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]

Depends on / 依赖: antisymm, apply_rangeSplitting, eventuallyConst_atTop, not_isCofinal_iff
-/
theorem of_not_isCofinal_rangeSplitting [Nonempty α] (hf : Monotone f)
    (hf' : ¬ IsCofinal (range (rangeSplitting f))) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
refine ⟨i, fun j hij => (hf hij).antisymm' (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]

/--
theorem `of_monotone_of_lt_cof` / 定理 `of_monotone_of_lt_cof`

English:
theorem of_monotone_of_lt_cof
  given: (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof α))
  proof: by
  have : Nonempty α := by by_contra!; simp at hα
  refine .of_not_isCofinal_rangeSplitting hf ?_
  contrapose! hα
  classical let := hf.isChain_range.linearOrder
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα]; rw [lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)

中文:
定理 of_monotone_of_lt_cof
  条件: (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof α))
  证明: by
  have : Nonempty α := by by_contra!; simp at hα
  refine .of_not_isCofinal_rangeSplitting hf ?_
  contrapose! hα
  classical let := hf.isChain_range.linearOrder
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα]; rw [lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)

Depends on / 依赖: Nonempty, classical, cof_le_cardinalMk, contrapose, hf.isChain_range.linearOrder, isChain_range, lift_cof_congr_of_strictMono, lift_le, linearOrder, mk_set_le, of_not_isCofinal_rangeSplitting, rangeSplitting_strictMono
-/
theorem of_monotone_of_lt_cof (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f := by
  have : Nonempty α := by by_contra!; simp at hα
  refine .of_not_isCofinal_rangeSplitting hf ?_
  contrapose! hα
  classical let := hf.isChain_range.linearOrder
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα]; rw [lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)

/--
theorem `of_antitone_of_lt_cof` / 定理 `of_antitone_of_lt_cof`

English:
theorem of_antitone_of_lt_cof
  given: (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof α))
  proof: .of_monotone_of_lt_cof (β := βᵒᵈ) hf.dual_right hα

中文:
定理 of_antitone_of_lt_cof
  条件: (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof α))
  证明: .of_monotone_of_lt_cof (β := βᵒᵈ) hf.dual_right hα

Depends on / 依赖: dual_right, hf.dual_right, of_monotone_of_lt_cof
-/
theorem of_antitone_of_lt_cof (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f :=
  .of_monotone_of_lt_cof (β := βᵒᵈ) hf.dual_right hα

end Filter.EventuallyConst

namespace Cardinal
variable {f : Cardinal.{v} -> β} [Small.{v} β]

/--
theorem `eventuallyConst_of_monotone` / 定理 `eventuallyConst_of_monotone`

English:
theorem eventuallyConst_of_monotone
  given: (hf : Monotone f)
  statement: atTop.EventuallyConst f
  proof: by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

中文:
定理 eventuallyConst_of_monotone
  条件: (hf : Monotone f)
  结论: atTop.EventuallyConst f
  证明: by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

Depends on / 依赖: of_monotone_of_lt_cof, small_iff_lift_mk_lt_univ
-/
theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

/--
theorem `eventuallyConst_of_antitone` / 定理 `eventuallyConst_of_antitone`

English:
theorem eventuallyConst_of_antitone
  given: (hf : Antitone f)
  statement: atTop.EventuallyConst f
  proof: eventuallyConst_of_monotone (β := βᵒᵈ) hf

中文:
定理 eventuallyConst_of_antitone
  条件: (hf : Antitone f)
  结论: atTop.EventuallyConst f
  证明: eventuallyConst_of_monotone (β := βᵒᵈ) hf

Depends on / 依赖: eventuallyConst_of_monotone
-/
theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Cardinal

namespace Ordinal
variable {f : Ordinal.{v} -> β} [Small.{v} β]

/--
theorem `eventuallyConst_of_monotone` / 定理 `eventuallyConst_of_monotone`

English:
theorem eventuallyConst_of_monotone
  given: (hf : Monotone f)
  statement: atTop.EventuallyConst f
  proof: by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

中文:
定理 eventuallyConst_of_monotone
  条件: (hf : Monotone f)
  结论: atTop.EventuallyConst f
  证明: by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

Depends on / 依赖: of_monotone_of_lt_cof, small_iff_lift_mk_lt_univ
-/
theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

/--
theorem `eventuallyConst_of_antitone` / 定理 `eventuallyConst_of_antitone`

English:
theorem eventuallyConst_of_antitone
  given: (hf : Antitone f)
  statement: atTop.EventuallyConst f
  proof: eventuallyConst_of_monotone (β := βᵒᵈ) hf

中文:
定理 eventuallyConst_of_antitone
  条件: (hf : Antitone f)
  结论: atTop.EventuallyConst f
  证明: eventuallyConst_of_monotone (β := βᵒᵈ) hf

Depends on / 依赖: eventuallyConst_of_monotone
-/
theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Ordinal
