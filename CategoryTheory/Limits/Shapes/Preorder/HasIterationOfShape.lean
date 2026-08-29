/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.Interval.Set.InitialSeg

/-!
# An assumption for constructions by transfinite induction

In this file, we introduce the typeclass `HasIterationOfShape J C` which is
an assumption in order to do constructions by transfinite induction indexed by
a well-ordered type `J` in a category `C` (see `CategoryTheory.SmallObject`).

-/

public section

universe w v v' u u'

namespace CategoryTheory.Limits

variable (J : Type w) [LinearOrder J] (C : Type u) [Category.{v} C]
  (K : Type u') [Category.{v'} K]

/--
Definition of `HasIterationOfShape` / `HasIterationOfShape` 的定义

English:
class HasIterationOfShape
  parameters: : Prop where
  axioms and operations (2):
    - hasColimitsOfShape_of_isSuccLimit((j : J) (hj : Order.IsSuccLimit j)) : HasColimitsOfShape (Set.Iio j) C  [default: by infer_instance]
    - hasColimitsOfShape : HasColimitsOfShape J C  [default: by infer_instance]

中文:
类 有IterationOfShape
  参数: : 命题 where
  公理与运算 (2 个):
    - hasColimitsOfShape_of_isSuccLimit((j : J) (hj : Order.是SuccLimit j)) : 有形状余极限 (集合.左无界右开区间 j) C  [默认: by infer_instance]
    - hasColimitsOfShape : 有形状余极限 J C  [默认: by infer_instance]

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape, infer_instance
-/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfSize.{w,
  signature: w} C] : HasIterationOfShape J C where

中文:
实例 [有余limitsOfSize.{w,
  签名: w} C] : 有IterationOfShape J C where
-/
instance [HasColimitsOfSize.{w, w} C] : HasIterationOfShape J C where

variable [HasIterationOfShape J C]

variable {J} in
/--
lemma `hasColimitsOfShape_of_isSuccLimit` / 引理 `hasColimitsOfShape_of_isSuccLimit`

English:
lemma hasColimitsOfShape_of_isSuccLimit
  statement: (j : J)
  proof: HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

中文:
引理 hasColimitsOfShape_of_isSuccLimit
  结论: (j : J)
  证明: HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

Depends on / 依赖: HasIterationOfShape, HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit, hasColimitsOfShape_of_isSuccLimit
-/
lemma hasColimitsOfShape_of_isSuccLimit (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

variable {J} in
/--
lemma `hasColimitsOfShape_of_isSuccLimit'` / 引理 `hasColimitsOfShape_of_isSuccLimit'`

English:
lemma hasColimitsOfShape_of_isSuccLimit'
  proof: by
  have := hasColimitsOfShape_of_isSuccLimit C h.top hα
  exact hasColimitsOfShape_of_equivalence h.orderIsoIio.equivalence.symm

中文:
引理 hasColimitsOfShape_of_isSuccLimit'
  证明: by
  have := hasColimitsOfShape_of_isSuccLimit C h.top hα
  exact hasColimitsOfShape_of_equivalence h.orderIsoIio.equivalence.symm

Depends on / 依赖: equivalence, h.orderIsoIio.equivalence.symm, h.top, hasColimitsOfShape_of_equivalence, hasColimitsOfShape_of_isSuccLimit, orderIsoIio
-/
lemma hasColimitsOfShape_of_isSuccLimit'
    {α : Type*} [PartialOrder α] (h : α <i J) (hα : Order.IsSuccLimit h.top) :
    HasColimitsOfShape α C := by
  have := hasColimitsOfShape_of_isSuccLimit C h.top hα
  exact hasColimitsOfShape_of_equivalence h.orderIsoIio.equivalence.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasIterationOfShape J (Arrow C)
  body: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

中文:
实例 :
  签名: 有IterationOfShape J (箭头 C)
  定义体: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit, infer_instance
-/
instance : HasIterationOfShape J (Arrow C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasIterationOfShape J (K ⥤ C)
  body: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

中文:
实例 :
  签名: 有IterationOfShape J (K ⥤ C)
  定义体: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit, infer_instance
-/
instance : HasIterationOfShape J (K ⥤ C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

variable {J} [SuccOrder J] [WellFoundedLT J]

/--
lemma `hasColimitsOfShape_of_initialSeg` / 引理 `hasColimitsOfShape_of_initialSeg`

English:
lemma hasColimitsOfShape_of_initialSeg
  proof: by
  by_cases hf : Function.Surjective f
  · exact hasColimitsOfShape_of_equivalence
      (OrderIso.ofRelIsoLT (RelIso.ofSurjective f.toRelEmbedding hf)).equivalence.symm
  · let s := f.toPrincipalSeg hf
    obtain ⟨i, hi₀⟩ : exists i, i = s.top := ⟨_, rfl⟩
    induction i using SuccOrder.limitRecO

中文:
引理 hasColimitsOfShape_of_initialSeg
  证明: by
  by_cases hf : Function.Surjective f
  · exact hasColimitsOfShape_of_equivalence
      (OrderIso.ofRelIsoLT (RelIso.ofSurjective f.toRelEmbedding hf)).equivalence.symm
  · let s := f.toPrincipalSeg hf
    obtain ⟨i, hi₀⟩ : exists i, i = s.top := ⟨_, rfl⟩
    induction i using SuccOrder.limitRecO

Depends on / 依赖: Classical, Classical.arbitrary, Function, Function.Surjective, Order.lt_succ_of_not_isMax, OrderIso, OrderIso.ofRelIsoLT, RelIso, RelIso.ofSurjective, SuccOrder, SuccOrder.limitRecOn, Surjective, arbitrary, equivalence, equivalence.symm, f.toPrincipalSeg, f.toRelEmbedding, hasColimitsOfShape_of_equivalence, hi.not_lt, limitRecOn
-/
lemma hasColimitsOfShape_of_initialSeg
    {α : Type*} [PartialOrder α] (f : α <=i J) [Nonempty α] :
    HasColimitsOfShape α C := by
  by_cases hf : Function.Surjective f
  · exact hasColimitsOfShape_of_equivalence
      (OrderIso.ofRelIsoLT (RelIso.ofSurjective f.toRelEmbedding hf)).equivalence.symm
  · let s := f.toPrincipalSeg hf
    obtain ⟨i, hi₀⟩ : exists i, i = s.top := ⟨_, rfl⟩
    induction i using SuccOrder.limitRecOn with
    | isMin i hi =>
      subst hi₀
      exact (hi.not_lt (s.lt_top (Classical.arbitrary _))).elim
    | succ i hi _ =>
      obtain ⟨a, rfl⟩ := (s.mem_range_iff_rel (b := i)).2 (by
        simpa only [← hi₀] using Order.lt_succ_of_not_isMax hi)
      have : OrderTop α :=
        { top := a
          le_top b := by
            rw [← s.le_iff_le]
            exact Order.le_of_lt_succ (by simpa only [hi₀] using s.lt_top b) }
      infer_instance
    | isSuccLimit i hi =>
      subst hi₀
      exact hasColimitsOfShape_of_isSuccLimit' C s hi

/--
lemma `hasIterationOfShape_of_initialSeg` / 引理 `hasIterationOfShape_of_initialSeg`

English:
lemma hasIterationOfShape_of_initialSeg
  statement: {α : Type*} [LinearOrder α]
  proof: hasColimitsOfShape_of_initialSeg C h
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    exact hasColimitsOfShape_of_initialSeg _
      (InitialSeg.trans (Set.principalSegIio j) h)

中文:
引理 hasIterationOfShape_of_initialSeg
  结论: {α : 类型} [线性序 α]
  证明: hasColimitsOfShape_of_initialSeg C h
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    exact hasColimitsOfShape_of_initialSeg _
      (InitialSeg.trans (Set.principalSegIio j) h)

Depends on / 依赖: hasColimitsOfShape_of_initialSeg
-/
lemma hasIterationOfShape_of_initialSeg {α : Type*} [LinearOrder α]
    (h : α <=i J) [Nonempty α] :
    HasIterationOfShape α C where
  hasColimitsOfShape := hasColimitsOfShape_of_initialSeg C h
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    exact hasColimitsOfShape_of_initialSeg _
      (InitialSeg.trans (Set.principalSegIio j) h)

instance (j : J) : HasIterationOfShape (Set.Iic j) C :=
  hasIterationOfShape_of_initialSeg C (Set.initialSegIic j)

end CategoryTheory.Limits
