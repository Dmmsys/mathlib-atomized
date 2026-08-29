/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Order.Hom.Lex
public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!

# Lexicographical order on Hahn series

In this file, we define lexicographical ordered `Lex R⟦Γ⟧`, and show this is a `LinearOrder` when
`Γ` and `R` themselves are linearly ordered. Additionally, it is an ordered group or ring whenever
`R` is.

## Main definitions

* `HahnSeries.finiteArchimedeanClassOrderIsoLex`: `FiniteArchimedeanClass` of `Lex R⟦Γ⟧`
  can be decomposed by `Γ`.

-/

@[expose] public section

namespace HahnSeries

variable {Γ R : Type*} [LinearOrder Γ]

section PartialOrder
variable [Zero R] [PartialOrder R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Lex R⟦Γ⟧)
  body: PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y => by simp

中文:
实例 :
  签名: PartialOrder (Lex R⟦Γ⟧)
  定义体: PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y => by simp

Depends on / 依赖: PartialOrder, PartialOrder.lift
-/
instance : PartialOrder (Lex R⟦Γ⟧) :=
  PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y => by simp

/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  given: (a b : Lex R⟦Γ⟧)
  proof: by rfl

中文:
定理 lt_iff
  条件: (a b : Lex R⟦Γ⟧)
  证明: by rfl
-/
theorem lt_iff (a b : Lex R⟦Γ⟧) :
    a < b ↔ exists (i : Γ), (forall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j)
    ∧ (ofLex a).coeff i < (ofLex b).coeff i := by rfl

end PartialOrder

section LinearOrder
variable [Zero R] [LinearOrder R]

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (Lex R⟦Γ⟧)
  body: by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
· have hab := Function.ne_iff.mp HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i != 0} union {i : Γ | (ofLex b).coeff i != 0}
      let v := {i : Γ | (ofLex a).coeff i != (ofLex b).coeff i}
      have hvu : v 

中文:
实例 :
  签名: LinearOrder (Lex R⟦Γ⟧)
  定义体: by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
· have hab := Function.ne_iff.mp HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i != 0} union {i : Γ | (ofLex b).coeff i != 0}
      let v := {i : Γ | (ofLex a).coeff i != (ofLex b).coeff i}
      have hvu : v 

Depends on / 依赖: Function, Function.ne_iff.mp, HahnSeries, HahnSeries.ext_iff.ne.mp, Or.inl, Set.mem_ofPred_eq, Set.mem_union, Set.notMem_ofPred_iff, contrapose, eq_or_ne, ext_iff, hab.le, isPWO_support, isWF.union, mem_ofPred_eq, mem_union, ne_iff, notMem_ofPred_iff, not_not, subseteq
-/
instance : LinearOrder (Lex R⟦Γ⟧) where
  le_total a b := by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
· have hab := Function.ne_iff.mp HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i != 0} union {i : Γ | (ofLex b).coeff i != 0}
      let v := {i : Γ | (ofLex a).coeff i != (ofLex b).coeff i}
      have hvu : v subseteq u := by
        intro i h
        rw [Set.mem_union]; rw [Set.mem_ofPred_eq]; rw [Set.mem_ofPred_eq]
        contrapose! h
        rw [Set.notMem_ofPred_iff]; rw [not_not]; rw [h.1]; rw [h.2]
      have hv : v.IsWF :=
        ((ofLex a).isPWO_support'.isWF.union (ofLex b).isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i -> (ofLex a).coeff j = (ofLex b).coeff j :=
not_imp_not.mp fun h' => hv.not_lt_min hab h'
      have hne : (ofLex a).coeff i != (ofLex b).coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj => (hji j hj).symm, hi⟩)
  toDecidableLE := Classical.decRel _

@[simp]
/--
theorem `leadingCoeff_pos_iff` / 定理 `leadingCoeff_pos_iff`

English:
theorem leadingCoeff_pos_iff
  given: {x : Lex R⟦Γ⟧}
  statement: 0 < (ofLex x).leadingCoeff ↔ 0 < x
  proof: by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) != 0 := leadingCoeff_ne_zero.mp hpos.ne.symm
    have htop : (ofLex x).orderTop != ⊤ := orderTop_ne_top.2 hne
    refine ⟨(ofLex x).orderTop.untop htop, ?_, by simpa [coeff_untop_eq_leadingCoeff] using hpos⟩
    intro j hj
    si

中文:
定理 leadingCoeff_pos_iff
  条件: {x : Lex R⟦Γ⟧}
  结论: 0 < (ofLex x).leadingCoeff ↔ 0 < x
  证明: by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) != 0 := leadingCoeff_ne_zero.mp hpos.ne.symm
    have htop : (ofLex x).orderTop != ⊤ := orderTop_ne_top.2 hne
    refine ⟨(ofLex x).orderTop.untop htop, ?_, by simpa [coeff_untop_eq_leadingCoeff] using hpos⟩
    intro j hj
    si

Depends on / 依赖: WithTop, WithTop.lt_untop_iff, WithTop.some, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, contra, hi.ne.symm, horder, hpos.ne.symm, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mp, lt_iff, lt_untop_iff, orderTop, orderTop.untop, orderTop_eq_of_le, orderTop_ne_top
-/
theorem leadingCoeff_pos_iff {x : Lex R⟦Γ⟧} : 0 < (ofLex x).leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) != 0 := leadingCoeff_ne_zero.mp hpos.ne.symm
    have htop : (ofLex x).orderTop != ⊤ := orderTop_ne_top.2 hne
    refine ⟨(ofLex x).orderTop.untop htop, ?_, by simpa [coeff_untop_eq_leadingCoeff] using hpos⟩
    intro j hj
    simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
  · intro ⟨i, hj, hi⟩
    have horder : (ofLex x).orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : (ofLex x).orderTop != ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : ofLex x != 0 := orderTop_ne_top.1 htop
    have horder' : (ofLex x).orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [leadingCoeff_of_ne_zero hne]; rw [horder']
    simpa using hi

@[simp]
/--
theorem `leadingCoeff_nonneg_iff` / 定理 `leadingCoeff_nonneg_iff`

English:
theorem leadingCoeff_nonneg_iff
  given: {x : Lex R⟦Γ⟧}
  statement: 0 <= (ofLex x).leadingCoeff ↔ 0 <= x
  proof: by
  constructor <;> intro h
  · obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_zero.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

@[simp]

中文:
定理 leadingCoeff_nonneg_iff
  条件: {x : Lex R⟦Γ⟧}
  结论: 0 <= (ofLex x).leadingCoeff ↔ 0 <= x
  证明: by
  constructor <;> intro h
  · obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_zero.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

@[simp]

Depends on / 依赖: eq_or_lt, h.eq_or_lt, heq.symm, le_of_eq, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, leadingCoeff_pos_iff, leadingCoeff_pos_iff.mp, leadingCoeff_pos_iff.mpr
-/
theorem leadingCoeff_nonneg_iff {x : Lex R⟦Γ⟧} : 0 <= (ofLex x).leadingCoeff ↔ 0 <= x := by
  constructor <;> intro h
  · obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_zero.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

@[simp]
/--
theorem `leadingCoeff_neg_iff` / 定理 `leadingCoeff_neg_iff`

English:
theorem leadingCoeff_neg_iff
  given: {x : Lex R⟦Γ⟧}
  statement: (ofLex x).leadingCoeff < 0 ↔ x < 0
  proof: by
  simp [← not_le]

@[simp]

中文:
定理 leadingCoeff_neg_iff
  条件: {x : Lex R⟦Γ⟧}
  结论: (ofLex x).leadingCoeff < 0 ↔ x < 0
  证明: by
  simp [← not_le]

@[simp]

Depends on / 依赖: not_le
-/
theorem leadingCoeff_neg_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff < 0 ↔ x < 0 := by
  simp [← not_le]

@[simp]
/--
theorem `leadingCoeff_nonpos_iff` / 定理 `leadingCoeff_nonpos_iff`

English:
theorem leadingCoeff_nonpos_iff
  given: {x : Lex R⟦Γ⟧}
  statement: (ofLex x).leadingCoeff <= 0 ↔ x <= 0
  proof: by
  simp [← not_lt]

中文:
定理 leadingCoeff_nonpos_iff
  条件: {x : Lex R⟦Γ⟧}
  结论: (ofLex x).leadingCoeff <= 0 ↔ x <= 0
  证明: by
  simp [← not_lt]

Depends on / 依赖: not_lt
-/
theorem leadingCoeff_nonpos_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff <= 0 ↔ x <= 0 := by
  simp [← not_lt]

end LinearOrder

section OrderedMonoid
variable [PartialOrder R] [AddCommMonoid R] [AddLeftStrictMono R] [IsOrderedAddMonoid R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (Lex R⟦Γ⟧)
  body: by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, fun j hji => ?_, add_left_strictMono hi⟩
      simp [hj j hji]

中文:
实例 :
  签名: IsOrderedAddMonoid (Lex R⟦Γ⟧)
  定义体: by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, fun j hji => ?_, add_left_strictMono hi⟩
      simp [hj j hji]

Depends on / 依赖: add_left_strictMono, eq_or_lt, hab.eq_or_lt, le_of_lt, lt_iff
-/
instance : IsOrderedAddMonoid (Lex R⟦Γ⟧) where
  add_le_add_left a b hab c := by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, fun j hji => ?_, add_left_strictMono hi⟩
      simp [hj j hji]

end OrderedMonoid

section OrderedGroup
variable [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

@[simp]
/--
theorem `support_abs` / 定理 `support_abs`

English:
theorem support_abs
  given: (x : Lex R⟦Γ⟧)
  statement: (ofLex |x|).support = (ofLex x).support
  proof: by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

@[simp]

中文:
定理 support_abs
  条件: (x : Lex R⟦Γ⟧)
  结论: (ofLex |x|).support = (ofLex x).support
  证明: by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

@[simp]

Depends on / 依赖: abs_eq_neg_self, abs_eq_neg_self.mpr, abs_eq_self, abs_eq_self.mpr, le_total
-/
theorem support_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).support = (ofLex x).support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

@[simp]
/--
theorem `orderTop_abs` / 定理 `orderTop_abs`

English:
theorem orderTop_abs
  given: (x : Lex R⟦Γ⟧)
  statement: (ofLex |x|).orderTop = (ofLex x).orderTop
  proof: by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

中文:
定理 orderTop_abs
  条件: (x : Lex R⟦Γ⟧)
  结论: (ofLex |x|).orderTop = (ofLex x).orderTop
  证明: by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

Depends on / 依赖: abs_eq_neg_self, abs_eq_neg_self.mpr, abs_eq_self, abs_eq_self.mpr, le_total, ofLex_neg, orderTop_neg
-/
theorem orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).orderTop = (ofLex x).orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

/--
theorem `order_abs` / 定理 `order_abs`

English:
theorem order_abs
  given: [Zero Γ] (x : Lex R⟦Γ⟧)
  statement: (ofLex |x|).order = (ofLex x).order
  proof: by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x != 0 := hne
    have habs : ofLex |x| != 0 := by simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero habs]; rw [order_eq_orderTop_of_ne_zero hne']
    apply orderTop_abs

中文:
定理 order_abs
  条件: [Zero Γ] (x : Lex R⟦Γ⟧)
  结论: (ofLex |x|).order = (ofLex x).order
  证明: by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x != 0 := hne
    have habs : ofLex |x| != 0 := by simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero habs]; rw [order_eq_orderTop_of_ne_zero hne']
    apply orderTop_abs

Depends on / 依赖: WithTop, WithTop.coe_injective, coe_injective, eq_or_ne, orderTop_abs, order_eq_orderTop_of_ne_zero
-/
theorem order_abs [Zero Γ] (x : Lex R⟦Γ⟧) : (ofLex |x|).order = (ofLex x).order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x != 0 := hne
    have habs : ofLex |x| != 0 := by simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero habs]; rw [order_eq_orderTop_of_ne_zero hne']
    apply orderTop_abs

/--
theorem `leadingCoeff_abs` / 定理 `leadingCoeff_abs`

English:
theorem leadingCoeff_abs
  given: (x : Lex R⟦Γ⟧)
  proof: by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le]; rw [abs_eq_neg_self.mpr hlt'.le]; rw [ofLex_neg]; rw [leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le]; rw [

中文:
定理 leadingCoeff_abs
  条件: (x : Lex R⟦Γ⟧)
  证明: by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le]; rw [abs_eq_neg_self.mpr hlt'.le]; rw [ofLex_neg]; rw [leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le]; rw [

Depends on / 依赖: abs_eq_neg_self, abs_eq_neg_self.mpr, abs_eq_self, abs_eq_self.mpr, hgt.le, hlt.le, leadingCoeff_neg, leadingCoeff_neg_iff, leadingCoeff_neg_iff.mpr, leadingCoeff_pos_iff, leadingCoeff_pos_iff.mpr, lt_trichotomy, ofLex_neg
-/
theorem leadingCoeff_abs (x : Lex R⟦Γ⟧) :
    (ofLex |x|).leadingCoeff = |(ofLex x).leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le]; rw [abs_eq_neg_self.mpr hlt'.le]; rw [ofLex_neg]; rw [leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le]; rw [abs_eq_self.mpr hgt'.le]

/--
theorem `abs_lt_abs_of_orderTop_ofLex` / 定理 `abs_lt_abs_of_orderTop_ofLex`

English:
theorem abs_lt_abs_of_orderTop_ofLex
  statement: {x y : Lex R⟦Γ⟧}
  proof: by
  rw [← orderTop_abs x]; rw [← orderTop_abs y] at h
  refine (lt_iff _ _).mpr ⟨(ofLex |y|).orderTop.untop h.ne_top, ?_, ?_⟩
  · simp +contextual [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, h.trans']
  · simpa [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, h]
      us

中文:
定理 abs_lt_abs_of_orderTop_ofLex
  结论: {x y : Lex R⟦Γ⟧}
  证明: by
  rw [← orderTop_abs x]; rw [← orderTop_abs y] at h
  refine (lt_iff _ _).mpr ⟨(ofLex |y|).orderTop.untop h.ne_top, ?_, ?_⟩
  · simp +contextual [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, h.trans']
  · simpa [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, h]
      us

Depends on / 依赖: coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, contextual, h.ne_top, h.trans, lt_iff, ne_top, orderTop, orderTop.untop, orderTop_abs
-/
theorem abs_lt_abs_of_orderTop_ofLex {x y : Lex R⟦Γ⟧}
    (h : (ofLex y).orderTop < (ofLex x).orderTop) : |x| < |y| := by
  rw [← orderTop_abs x]; rw [← orderTop_abs y] at h
  refine (lt_iff _ _).mpr ⟨(ofLex |y|).orderTop.untop h.ne_top, ?_, ?_⟩
  · simp +contextual [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, h.trans']
  · simpa [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, h]
      using h.ne_top

set_option backward.isDefEq.respectTransparency false in
/--
theorem `archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex` / 定理 `archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex`

English:
theorem archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex
  statement: {x y : Lex R⟦Γ⟧}
  proof: by
  simp_rw [ArchimedeanClass.mk_le_mk]
  obtain rfl | hy := eq_or_ne y 0
  · -- special case: both `x` and `y` are zero
    simp_all
  -- general case: `x` and `y` are not zero
have hx : x != 0 := by simpa using orderTop_ne_top.1 h ▸ orderTop_ne_top.2 (by simpa using hy)
  have h' : (ofLex |x|).or

中文:
定理 archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex
  结论: {x y : Lex R⟦Γ⟧}
  证明: by
  simp_rw [ArchimedeanClass.mk_le_mk]
  obtain rfl | hy := eq_or_ne y 0
  · -- special case: both `x` and `y` are zero
    simp_all
  -- general case: `x` and `y` are not zero
have hx : x != 0 := by simpa using orderTop_ne_top.1 h ▸ orderTop_ne_top.2 (by simpa using hy)
  have h' : (ofLex |x|).or

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk_le_mk, eq_or_ne, mk_le_mk, simp_rw, special
-/
theorem archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex {x y : Lex R⟦Γ⟧}
    (h : (ofLex x).orderTop = (ofLex y).orderTop) :
    ArchimedeanClass.mk x <= .mk y ↔
      ArchimedeanClass.mk (ofLex x).leadingCoeff <= .mk (ofLex y).leadingCoeff := by
  simp_rw [ArchimedeanClass.mk_le_mk]
  obtain rfl | hy := eq_or_ne y 0
  · -- special case: both `x` and `y` are zero
    simp_all
  -- general case: `x` and `y` are not zero
have hx : x != 0 := by simpa using orderTop_ne_top.1 h ▸ orderTop_ne_top.2 (by simpa using hy)
  have h' : (ofLex |x|).orderTop = (ofLex |y|).orderTop := by simpa using h
  constructor
  · -- `mk x ≤ mk y → mk x.leadingCoeff ≤ mk y.leadingCoeff`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have hn' : |y| < (n + 1) • |x| :=
lt_of_le_of_lt hn nsmul_lt_nsmul_left (by simpa using hx) (by simp)
    obtain ⟨j, hj, hi⟩ := (lt_iff _ _).mp hn'
    simp_rw [ofLex_smul, coeff_smul] at hj hi
    simp_rw [← leadingCoeff_abs]
    rw [leadingCoeff_of_ne_zero (by simpa using hy)]; rw [leadingCoeff_of_ne_zero (by simpa using hx)]
    simp_rw [← h']
    obtain hjlt | hjeq | hjgt := lt_trichotomy (WithTop.some j) (ofLex |x|).orderTop
    · -- impossible case: `x` and `y` differ before their leading coefficients
      have hjlt' : j < (ofLex |y|).orderTop := h'.symm ▸ hjlt
      simp [coeff_eq_zero_of_lt_orderTop hjlt, coeff_eq_zero_of_lt_orderTop hjlt'] at hi
    · convert! hi.le <;> exact (WithTop.untop_eq_iff _).mpr hjeq.symm
    · exact (hj _ ((WithTop.untop_lt_iff _).mpr hjgt)).le
  · -- `mk x.leadingCoeff ≤ mk y.leadingCoeff → mk x ≤ mk y`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ((lt_iff _ _).mpr ?_).le⟩
    refine ⟨(ofLex x).orderTop.untop (by simpa using hx), ?_, ?_⟩
    · -- all coefficients before the leading coefficient are zero
      intro j hj
      trans 0
      · apply coeff_eq_zero_of_lt_orderTop
        simpa [← h] using hj
      · suffices (ofLex |x|).coeff j = 0 by simp [this]
        apply coeff_eq_zero_of_lt_orderTop
        simpa using hj
    -- the leading coefficient determines the relation
    rw [ofLex_smul]; rw [coeff_smul]
    suffices |(ofLex y).leadingCoeff| < (n + 1) • |(ofLex x).leadingCoeff| by
      simp_rw [← leadingCoeff_abs] at this
      rw [leadingCoeff_of_ne_zero (by simpa using hy)]; rw [leadingCoeff_of_ne_zero (by simpa using hx)]
        at this
      convert! this using 3 <;> simp [h]
refine lt_of_le_of_lt hn nsmul_lt_nsmul_left ?_ (by simp)
    rwa [abs_pos, leadingCoeff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `archimedeanClassMk_le_archimedeanClassMk_iff` / 定理 `archimedeanClassMk_le_archimedeanClassMk_iff`

English:
theorem archimedeanClassMk_le_archimedeanClassMk_iff
  given: {x y : Lex R⟦Γ⟧}
  proof: by
  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when `x`'s order is less than `y`'s, this reduces to abs_lt_abs_of_orderTop_ofLex
    simpa [ArchimedeanClass.mk_le_mk, hlt] using
      ⟨1, by simpa using (abs_lt_abs_of_orderTop_ofLex hlt).le⟩
  · -- when `x`

中文:
定理 archimedeanClassMk_le_archimedeanClassMk_iff
  条件: {x y : Lex R⟦Γ⟧}
  证明: by
  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when `x`'s order is less than `y`'s, this reduces to abs_lt_abs_of_orderTop_ofLex
    simpa [ArchimedeanClass.mk_le_mk, hlt] using
      ⟨1, by simpa using (abs_lt_abs_of_orderTop_ofLex hlt).le⟩
  · -- when `x`

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk_le_mk, abs_lt_abs_of_orderTop_ofLex, lt_trichotomy, mk_le_mk, orderTop, reduces
-/
theorem archimedeanClassMk_le_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} :
    ArchimedeanClass.mk x <= .mk y ↔
      (ofLex x).orderTop < (ofLex y).orderTop ∨
        (ofLex x).orderTop = (ofLex y).orderTop ∧
          ArchimedeanClass.mk (ofLex x).leadingCoeff <= .mk (ofLex y).leadingCoeff := by
  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when `x`'s order is less than `y`'s, this reduces to abs_lt_abs_of_orderTop_ofLex
    simpa [ArchimedeanClass.mk_le_mk, hlt] using
      ⟨1, by simpa using (abs_lt_abs_of_orderTop_ofLex hlt).le⟩
  · -- when `x` and `y` have the same order, this reduces to
    -- `archimedeanClass_le_iff_of_orderTop_eq`
    simpa [heq] using archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex heq
  -- when `x`'s order is greater than `y`'s, neither side is true
  simp_rw [ArchimedeanClass.mk_le_mk]
  refine ⟨?_, by simp [hgt.not_gt, hgt.ne']⟩
  intro ⟨n, hn⟩
  contrapose! hn
  rw [← abs_nsmul]
  have hgt' : (ofLex y).orderTop < (ofLex (n • x)).orderTop := by
    apply lt_of_lt_of_le hgt
    simpa using orderTop_smul_not_lt n (ofLex x)
  exact abs_lt_abs_of_orderTop_ofLex hgt'

/--
theorem `archimedeanClassMk_eq_archimedeanClassMk_iff` / 定理 `archimedeanClassMk_eq_archimedeanClassMk_iff`

English:
theorem archimedeanClassMk_eq_archimedeanClassMk_iff
  given: {x y : Lex R⟦Γ⟧}
  proof: by
  rw [le_antisymm_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
  constructor
  · simpa +contextual [or_imp, ne_of_gt, le_of_lt] using fun _ => le_antisymm
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.sym

中文:
定理 archimedeanClassMk_eq_archimedeanClassMk_iff
  条件: {x y : Lex R⟦Γ⟧}
  证明: by
  rw [le_antisymm_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
  constructor
  · simpa +contextual [or_imp, ne_of_gt, le_of_lt] using fun _ => le_antisymm
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.sym

Depends on / 依赖: archimedeanClassMk_le_archimedeanClassMk_iff, contextual, hcoeff, hcoeff.ge, hcoeff.le, horder, horder.symm, le_antisymm, le_antisymm_iff, le_of_lt, ne_of_gt, or_imp
-/
theorem archimedeanClassMk_eq_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} :
    ArchimedeanClass.mk x = ArchimedeanClass.mk y ↔
    (ofLex x).orderTop = (ofLex y).orderTop ∧
    ArchimedeanClass.mk (ofLex x).leadingCoeff = ArchimedeanClass.mk (ofLex y).leadingCoeff := by
  rw [le_antisymm_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
  constructor
  · simpa +contextual [or_imp, ne_of_gt, le_of_lt] using fun _ => le_antisymm
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.symm, hcoeff.ge⟩⟩

variable (Γ R) in
/--
Definition of `finiteArchimedeanClassOrderHomLex` / `finiteArchimedeanClassOrderHomLex` 的定义

English:
definition finiteArchimedeanClassOrderHomLex
  signature: :
  body: FiniteArchimedeanClass.liftOrderHom
    (fun ⟨x, hx⟩ => toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne_zero (show ofLex x != 0 by exact hx)]),
      FiniteArchimedeanClass.mk (ofLex x).leadingCoeff (leadingCoeff_ne_zero.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [Prod.Lex.le_

中文:
定义 finiteArchimedeanClassOrderHomLex
  签名: :
  定义体: FiniteArchimedeanClass.liftOrderHom
    (fun ⟨x, hx⟩ => toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne_zero (show ofLex x != 0 by exact hx)]),
      FiniteArchimedeanClass.mk (ofLex x).leadingCoeff (leadingCoeff_ne_zero.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [Prod.Lex.le_

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.liftOrderHom, FiniteArchimedeanClass.mk, FiniteArchimedeanClass.mk_le_mk, Prod.Lex.le_iff, WithTop, WithTop.untop_eq_iff, archimedeanClassMk_le_archimedeanClassMk_iff, archimedeanClassMk_le_archimedeanClassMk_iff.mp, le_iff, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, liftOrderHom, mk_le_mk, ofLex_toLex, orderTop, orderTop.untop, orderTop_of_ne_zero, untop_eq_iff
-/
noncomputable def finiteArchimedeanClassOrderHomLex :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) ->o Γ ×ₗ FiniteArchimedeanClass R :=
  FiniteArchimedeanClass.liftOrderHom
    (fun ⟨x, hx⟩ => toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne_zero (show ofLex x != 0 by exact hx)]),
      FiniteArchimedeanClass.mk (ofLex x).leadingCoeff (leadingCoeff_ne_zero.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [Prod.Lex.le_iff]
      simp only [ofLex_toLex]
      rw [FiniteArchimedeanClass.mk_le_mk] at ⊢ h
      rw [WithTop.untop_eq_iff]
      simpa using archimedeanClassMk_le_archimedeanClassMk_iff.mp h

variable (Γ R) in
/--
Definition of `finiteArchimedeanClassOrderHomInvLex` / `finiteArchimedeanClassOrderHomInvLex` 的定义

English:
definition finiteArchimedeanClassOrderHomInvLex
  signature: :
  body: (ofLex x).2.liftOrderHom
    (fun a => FiniteArchimedeanClass.mk (toLex (single (ofLex x).1 a.val)) (by
      simpa using! a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [FiniteArchimedeanClass.mk_le_mk]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
      simpa [ha, hb] using! h
  monotone' 

中文:
定义 finiteArchimedeanClassOrderHomInvLex
  签名: :
  定义体: (ofLex x).2.liftOrderHom
    (fun a => FiniteArchimedeanClass.mk (toLex (single (ofLex x).1 a.val)) (by
      simpa using! a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [FiniteArchimedeanClass.mk_le_mk]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
      simpa [ha, hb] using! h
  monotone' 

Depends on / 依赖: liftOrderHom
-/
noncomputable def finiteArchimedeanClassOrderHomInvLex :
    Γ ×ₗ FiniteArchimedeanClass R ->o FiniteArchimedeanClass (Lex R⟦Γ⟧) where
  toFun x := (ofLex x).2.liftOrderHom
    (fun a => FiniteArchimedeanClass.mk (toLex (single (ofLex x).1 a.val)) (by
      simpa using! a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
      rw [FiniteArchimedeanClass.mk_le_mk]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
      simpa [ha, hb] using! h
  monotone' a b := a.rec fun (ao, ac) => b.rec fun (bo, bc) h => by
    obtain h | ⟨rfl, hle⟩ := Prod.Lex.le_iff.mp h
    · induction ac using FiniteArchimedeanClass.ind with | mk a ha
      induction bc using FiniteArchimedeanClass.ind with | mk b hb
      simp only [ne_eq, ofLex_toLex, FiniteArchimedeanClass.liftOrderHom_mk]
      rw [FiniteArchimedeanClass.mk_le_mk]; rw [archimedeanClassMk_le_archimedeanClassMk_iff]
      exact .inl (by simpa [ha, hb] using! h)
    · exact OrderHom.monotone _ hle

set_option backward.isDefEq.respectTransparency.types false in
variable (Γ R) in
/--
Definition of `finiteArchimedeanClassOrderIsoLex` / `finiteArchimedeanClassOrderIsoLex` 的定义

English:
definition finiteArchimedeanClassOrderIsoLex
  signature: :
  body: by
  apply OrderIso.ofHomInv (finiteArchimedeanClassOrderHomLex Γ R)
    (finiteArchimedeanClassOrderHomInvLex Γ R)
  · ext x
    cases x with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteA

中文:
定义 finiteArchimedeanClassOrderIsoLex
  签名: :
  定义体: by
  apply OrderIso.ofHomInv (finiteArchimedeanClassOrderHomLex Γ R)
    (finiteArchimedeanClassOrderHomInvLex Γ R)
  · ext x
    cases x with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteA

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.ind, OrderIso, OrderIso.ofHomInv, archimedeanClassMk_eq_archimedeanClassMk_i, finiteArchimedeanClassOrderHomInvLex, finiteArchimedeanClassOrderHomLex, ofHomInv
-/
noncomputable def finiteArchimedeanClassOrderIsoLex :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ ×ₗ FiniteArchimedeanClass R := by
  apply OrderIso.ofHomInv (finiteArchimedeanClassOrderHomLex Γ R)
    (finiteArchimedeanClassOrderHomInvLex Γ R)
  · ext x
    cases x with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex, ha]
  · ext x
    induction x using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex,
      archimedeanClassMk_eq_archimedeanClassMk_iff, ha]

@[simp]
/--
theorem `finiteArchimedeanClassOrderIsoLex_apply_fst` / 定理 `finiteArchimedeanClassOrderIsoLex_apply_fst`

English:
theorem finiteArchimedeanClassOrderIsoLex_apply_fst
  given: {x : Lex R⟦Γ⟧} (h : x != 0)
  proof: by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

@[simp]

中文:
定理 finiteArchimedeanClassOrderIsoLex_apply_fst
  条件: {x : Lex R⟦Γ⟧} (h : x != 0)
  证明: by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

@[simp]

Depends on / 依赖: finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderIsoLex
-/
theorem finiteArchimedeanClassOrderIsoLex_apply_fst {x : Lex R⟦Γ⟧} (h : x != 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).1 =
    (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

@[simp]
/--
theorem `finiteArchimedeanClassOrderIsoLex_apply_snd` / 定理 `finiteArchimedeanClassOrderIsoLex_apply_snd`

English:
theorem finiteArchimedeanClassOrderIsoLex_apply_snd
  given: {x : Lex R⟦Γ⟧} (h : x != 0)
  proof: by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

中文:
定理 finiteArchimedeanClassOrderIsoLex_apply_snd
  条件: {x : Lex R⟦Γ⟧} (h : x != 0)
  证明: by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

Depends on / 依赖: finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderIsoLex
-/
theorem finiteArchimedeanClassOrderIsoLex_apply_snd {x : Lex R⟦Γ⟧} (h : x != 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).2.val =
    ArchimedeanClass.mk (ofLex x).leadingCoeff := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

section Archimedean
variable [Archimedean R] [Nontrivial R]

variable (Γ R) in
/--
Definition of `finiteArchimedeanClassOrderIso` / `finiteArchimedeanClassOrderIso` 的定义

English:
definition finiteArchimedeanClassOrderIso
  signature: :
  body: have : Unique (FiniteArchimedeanClass R) := (nonempty_unique _).some
  (finiteArchimedeanClassOrderIsoLex Γ R).trans (Prod.Lex.prodUnique _ _)

@[simp]

中文:
定义 finiteArchimedeanClassOrderIso
  签名: :
  定义体: have : Unique (FiniteArchimedeanClass R) := (nonempty_unique _).some
  (finiteArchimedeanClassOrderIsoLex Γ R).trans (Prod.Lex.prodUnique _ _)

@[simp]

Depends on / 依赖: FiniteArchimedeanClass, Prod.Lex.prodUnique, Unique, finiteArchimedeanClassOrderIsoLex, nonempty_unique, prodUnique
-/
noncomputable def finiteArchimedeanClassOrderIso :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ :=
  have : Unique (FiniteArchimedeanClass R) := (nonempty_unique _).some
  (finiteArchimedeanClassOrderIsoLex Γ R).trans (Prod.Lex.prodUnique _ _)

@[simp]
/--
theorem `finiteArchimedeanClassOrderIso_apply` / 定理 `finiteArchimedeanClassOrderIso_apply`

English:
theorem finiteArchimedeanClassOrderIso_apply
  given: {x : Lex R⟦Γ⟧} (h : x != 0)
  proof: by
  simp [finiteArchimedeanClassOrderIso]

中文:
定理 finiteArchimedeanClassOrderIso_apply
  条件: {x : Lex R⟦Γ⟧} (h : x != 0)
  证明: by
  simp [finiteArchimedeanClassOrderIso]

Depends on / 依赖: finiteArchimedeanClassOrderIso
-/
theorem finiteArchimedeanClassOrderIso_apply {x : Lex R⟦Γ⟧} (h : x != 0) :
    finiteArchimedeanClassOrderIso Γ R (FiniteArchimedeanClass.mk x h) = (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIso]

variable (Γ R) in
/--
Definition of `archimedeanClassOrderIsoWithTop` / `archimedeanClassOrderIsoWithTop` 的定义

English:
definition archimedeanClassOrderIsoWithTop
  signature: :
  body: (FiniteArchimedeanClass.withTopOrderIso _).symm.trans
  (finiteArchimedeanClassOrderIso _ _).withTopCongr

@[simp]

中文:
定义 archimedeanClassOrderIsoWithTop
  签名: :
  定义体: (FiniteArchimedeanClass.withTopOrderIso _).symm.trans
  (finiteArchimedeanClassOrderIso _ _).withTopCongr

@[simp]

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.withTopOrderIso, finiteArchimedeanClassOrderIso, symm.trans, withTopCongr, withTopOrderIso
-/
noncomputable def archimedeanClassOrderIsoWithTop :
    ArchimedeanClass (Lex R⟦Γ⟧) ≃o WithTop Γ :=
  (FiniteArchimedeanClass.withTopOrderIso _).symm.trans
  (finiteArchimedeanClassOrderIso _ _).withTopCongr

@[simp]
/--
theorem `archimedeanClassOrderIsoWithTop_apply` / 定理 `archimedeanClassOrderIsoWithTop_apply`

English:
theorem archimedeanClassOrderIsoWithTop_apply
  given: (x : Lex R⟦Γ⟧)
  proof: by
  unfold archimedeanClassOrderIsoWithTop
  obtain rfl | h := eq_or_ne x 0 <;>
    simp [FiniteArchimedeanClass.withTopOrderIso_symm_apply, *]

中文:
定理 archimedeanClassOrderIsoWithTop_apply
  条件: (x : Lex R⟦Γ⟧)
  证明: by
  unfold archimedeanClassOrderIsoWithTop
  obtain rfl | h := eq_or_ne x 0 <;>
    simp [FiniteArchimedeanClass.withTopOrderIso_symm_apply, *]

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.withTopOrderIso_symm_apply, archimedeanClassOrderIsoWithTop, eq_or_ne, from_lrat, withTopOrderIso_symm_apply
-/
theorem archimedeanClassOrderIsoWithTop_apply (x : Lex R⟦Γ⟧) :
    archimedeanClassOrderIsoWithTop Γ R (ArchimedeanClass.mk x) = (ofLex x).orderTop := by
  unfold archimedeanClassOrderIsoWithTop
  obtain rfl | h := eq_or_ne x 0 <;>
    simp [FiniteArchimedeanClass.withTopOrderIso_symm_apply, *]

end Archimedean

end OrderedGroup

section OrderedRing
variable [LinearOrder R] [Ring R] [AddCommMonoid Γ]
  [IsOrderedCancelAddMonoid Γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedRing
  signature: R] [NoZeroDivisors R] : IsOrderedRing (Lex R⟦Γ⟧) where
  body: by simp [← leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← mul_sub]; rw [← leadingCoeff_nonneg_iff]; rw [ofLex_mul]; rw [leadingCoeff_mul]
    apply mul_nonneg
    · simpa
    · rwa [leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_righ

中文:
实例 [IsOrderedRing
  签名: R] [NoZeroDivisors R] : IsOrderedRing (Lex R⟦Γ⟧) where
  定义体: by simp [← leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← mul_sub]; rw [← leadingCoeff_nonneg_iff]; rw [ofLex_mul]; rw [leadingCoeff_mul]
    apply mul_nonneg
    · simpa
    · rwa [leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_righ

Depends on / 依赖: leadingCoeff_mul, leadingCoeff_nonneg_iff, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_sub, ofLex_mul, sub_mul, sub_nonneg
-/
instance [IsOrderedRing R] [NoZeroDivisors R] : IsOrderedRing (Lex R⟦Γ⟧) where
  zero_le_one := by simp [← leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← mul_sub]; rw [← leadingCoeff_nonneg_iff]; rw [ofLex_mul]; rw [leadingCoeff_mul]
    apply mul_nonneg
    · simpa
    · rwa [leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← sub_mul]; rw [← leadingCoeff_nonneg_iff]; rw [ofLex_mul]; rw [leadingCoeff_mul]
    apply mul_nonneg
    · rwa [leadingCoeff_nonneg_iff]
    · simpa

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictOrderedRing
  signature: R] : IsStrictOrderedRing (Lex R⟦Γ⟧) where

中文:
实例 [IsStrictOrderedRing
  签名: R] : IsStrictOrderedRing (Lex R⟦Γ⟧) where
-/
instance [IsStrictOrderedRing R] : IsStrictOrderedRing (Lex R⟦Γ⟧) where

end OrderedRing

section EmbDomain
variable [PartialOrder R] {Γ' : Type*} [LinearOrder Γ'] (f : Γ ↪o Γ')

/-- `HahnSeries.embDomain` as an `OrderEmbedding`. -/
@[simps]
noncomputable
/--
Definition of `embDomainOrderEmbedding` / `embDomainOrderEmbedding` 的定义

English:
definition embDomainOrderEmbedding
  signature: [Zero R]
  body: toLex (embDomain f (ofLex a))
  inj' := toLex.injective.comp (embDomain_injective.comp (ofLex.injective))
  map_rel_iff' {a b} := by
    simp_rw [le_iff_lt_or_eq, lt_iff]
    simp only [Function.Embedding.coeFn_mk, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro (⟨i, hj, hi⟩

中文:
定义 embDomainOrderEmbedding
  签名: [Zero R]
  定义体: toLex (embDomain f (ofLex a))
  inj' := toLex.injective.comp (embDomain_injective.comp (ofLex.injective))
  map_rel_iff' {a b} := by
    simp_rw [le_iff_lt_or_eq, lt_iff]
    simp only [Function.Embedding.coeFn_mk, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro (⟨i, hj, hi⟩

Depends on / 依赖: embDomain
-/
def embDomainOrderEmbedding [Zero R] : Lex R⟦Γ⟧ ↪o Lex R⟦Γ'⟧ where
  toFun a := toLex (embDomain f (ofLex a))
  inj' := toLex.injective.comp (embDomain_injective.comp (ofLex.injective))
  map_rel_iff' {a b} := by
    simp_rw [le_iff_lt_or_eq, lt_iff]
    simp only [Function.Embedding.coeFn_mk, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro (⟨i, hj, hi⟩ | heq)
      · have himem : i in Set.range f := by
          contrapose hi
          simp [embDomain_of_notMem_range hi]
        obtain ⟨k, rfl⟩ := himem
        refine Or.inl ⟨k, fun j hjk => ?_, by simpa using hi⟩
        simpa using hj (f j) (f.lt_iff_lt.mpr hjk)
· exact Or.inr embDomain_injective.comp (ofLex.injective) heq
    · rintro (⟨i, hj, hi⟩ | rfl)
      · refine Or.inl ⟨f i, fun k hki => ?_, by simpa using hi⟩
        by_cases hkmem : k in Set.range f
        · obtain ⟨j', rfl⟩ := hkmem
simpa using hj _ f.lt_iff_lt.mp hki
        · simp_rw [embDomain_of_notMem_range hkmem]
      · simp

/-- `HahnSeries.embDomain` as an `OrderAddMonoidHom`. -/
@[simps]
noncomputable
/--
Definition of `embDomainOrderAddMonoidHom` / `embDomainOrderAddMonoidHom` 的定义

English:
definition embDomainOrderAddMonoidHom
  signature: [AddMonoid R]
  body: (embDomainOrderEmbedding f).toOrderHom
  map_zero' := by simp
  map_add' := by simp [embDomainOrderEmbedding, embDomain_add]

中文:
定义 embDomainOrderAddMonoidHom
  签名: [AddMonoid R]
  定义体: (embDomainOrderEmbedding f).toOrderHom
  map_zero' := by simp
  map_add' := by simp [embDomainOrderEmbedding, embDomain_add]

Depends on / 依赖: embDomainOrderEmbedding, toOrderHom
-/
def embDomainOrderAddMonoidHom [AddMonoid R] : Lex R⟦Γ⟧ ->+o Lex R⟦Γ'⟧ where
  __ := (embDomainOrderEmbedding f).toOrderHom
  map_zero' := by simp
  map_add' := by simp [embDomainOrderEmbedding, embDomain_add]

/--
theorem `embDomainOrderAddMonoidHom_injective` / 定理 `embDomainOrderAddMonoidHom_injective`

English:
theorem embDomainOrderAddMonoidHom_injective
  given: [AddMonoid R]
  proof: (embDomainOrderEmbedding f).injective

中文:
定理 embDomainOrderAddMonoidHom_injective
  条件: [AddMonoid R]
  证明: (embDomainOrderEmbedding f).injective
-/
theorem embDomainOrderAddMonoidHom_injective [AddMonoid R] :
    Function.Injective (embDomainOrderAddMonoidHom f (R := R)) :=
  (embDomainOrderEmbedding f).injective

end EmbDomain

end HahnSeries
