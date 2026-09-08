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

/-- A category `C` has iterations of shape a linearly ordered type `J`
when certain specific shapes of colimits exists: colimits indexed by `J`,
and by `Set.Iio j` for `j : J`. -/
/-
**CategoryTheory.Limits.HasIterationOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasIterationOfShape : Prop where hasColimitsOfShape_of_isSuccLimit (j : J)
 (hj : Order.IsSuccLimit j) : HasColimitsOfShape (Set.Iio j) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` has iterations of shape a linearly ordered type `J`
when certain specific shapes of colimits exists: colimits indexed by `J`,
and by `Set.Iio j` for `j : J`.
-/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfSize.{w, w} C] : HasIterationOfShape J C where

variable [HasIterationOfShape J C]

variable {J} in
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_isSuccLimit** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) : Has
ColimitsOfShape (Set.Iio j) C
参数：j : J；hj : Order.IsSuccLimit j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasIterationOfShape.hasColimitsOfShape_of_isSuccLi
mit`：∀ {J : Type w} {inst : LinearOrder J} {C : Type u} {inst_1 : CategoryTheory
.Category.{v, u} C}   [self : CategoryTheory.Limits.HasIterationO…
-/
lemma hasColimitsOfShape_of_isSuccLimit (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

variable {J} in
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_isSuccLimit'** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_isSuccLimit' {α : Type*} [PartialOrder α] (h : α <i 
J) (hα : Order.IsSuccLimit h.top) : HasColimitsOfShape α C
参数：h : α <i J；hα : Order.IsSuccLimit h.top。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasColimitsOfShape_of_isSuccLimit`：hasColimitsOfSh
ape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) : HasColimitsOfShape (Set.
Iio j) C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
lemma hasColimitsOfShape_of_isSuccLimit'
    {α : Type*} [PartialOrder α] (h : α <i J) (hα : Order.IsSuccLimit h.top) :
    HasColimitsOfShape α C := by
  have := hasColimitsOfShape_of_isSuccLimit C h.top hα
  exact hasColimitsOfShape_of_equivalence h.orderIsoIio.equivalence.symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasIterationOfShape J (Arrow C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasIterationOfShape J (K ⥤ C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

variable {J} [SuccOrder J] [WellFoundedLT J]
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_initialSeg** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_initialSeg {α : Type*} [PartialOrder α] (f : α <=i J
) [Nonempty α] : HasColimitsOfShape α C
参数：f : α <=i J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.HasIterationOfShape.hasColimitsOfShape`：∀ {J : Typ
e w} {inst : LinearOrder J} {C : Type u} {inst_1 : CategoryTheory.Category.{v, u
} C}   [self : CategoryTheory.Limits.HasIterationO…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrincipalSeg.mem_range_iff_rel`：mem_range_iff_rel (f : r ≺i s) : forall 
{b : β}, b in Set.range f ↔ s b f.top
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `PrincipalSeg.le_iff_le`：le_iff_le [PartialOrder α] (f : α <i β) : f a <=
 f a' ↔ a <= a'
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用定理 `Preorder.instHasColimitsOfShape`：∀ (C : Type u) [inst : CategoryTheory.C
ategory.{v, u} C] (J : Type w) [inst_1 : Preorder J] [OrderTop J],   CategoryThe
ory.Limits.HasColimit…
· 使用引理 `CategoryTheory.Limits.hasColimitsOfShape_of_isSuccLimit'`：hasColimitsOfS
hape_of_isSuccLimit' {α : Type*} [PartialOrder α] (h : α <i J) (hα : Order.IsSuc
cLimit h.top) : HasColimitsOfShape α C
-/
lemma hasColimitsOfShape_of_initialSeg
    {α : Type*} [PartialOrder α] (f : α ≤i J) [Nonempty α] :
    HasColimitsOfShape α C := by
  by_cases hf : Function.Surjective f
  · exact hasColimitsOfShape_of_equivalence
      (OrderIso.ofRelIsoLT (RelIso.ofSurjective f.toRelEmbedding hf)).equivalence.symm
  · let s := f.toPrincipalSeg hf
    obtain ⟨i, hi₀⟩ : ∃ i, i = s.top := ⟨_, rfl⟩
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
/-
**CategoryTheory.Limits.hasIterationOfShape_of_initialSeg** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasIterationOfShape_of_initialSeg {α : Type*} [LinearOrder α] (h : α <=i J
) [Nonempty α] : HasIterationOfShape α C where hasColimitsOfShape
参数：h : α <=i J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Order.IsSuccLimit.nonempty_Iio`：∀ {α : Type u_1} {a : α} [inst : Preorde
r α], Order.IsSuccLimit a → (Set.Iio a).Nonempty
· 使用引理 `CategoryTheory.Limits.hasColimitsOfShape_of_initialSeg`：hasColimitsOfSha
pe_of_initialSeg {α : Type*} [PartialOrder α] (f : α <=i J) [Nonempty α] : HasCo
limitsOfShape α C
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
lemma hasIterationOfShape_of_initialSeg {α : Type*} [LinearOrder α]
    (h : α ≤i J) [Nonempty α] :
    HasIterationOfShape α C where
  hasColimitsOfShape := hasColimitsOfShape_of_initialSeg C h
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    exact hasColimitsOfShape_of_initialSeg _
      (InitialSeg.trans (Set.principalSegIio j) h)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : J) : HasIterationOfShape (Set.Iic j) C :=
  hasIterationOfShape_of_initialSeg C (Set.initialSegIic j)

end CategoryTheory.Limits

