/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Yoneda

/-!
# Filtered categories and limits

In this file, we show that `C` is filtered if and only if for every functor `F : J ⥤ C` from a
finite category there is some `X : C` such that `lim Hom(F·, X)` is nonempty.

Furthermore, we define the type classes `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize`.
-/

public section


universe w' w w₂' w₂ v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section NonemptyLimit

open CategoryTheory.Limits Opposite

/-- `C` is filtered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(F·, X)` is nonempty.

    Lemma 3.1.2 of [Kashiwara2006] -/
/-
**CategoryTheory.IsFiltered.iff_nonempty_limit** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.IsFiltered`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   CategoryTheory
.IsFiltered C ↔     ∀ {J : Type v} [inst_1 : CategoryTheory.SmallCategory J] [Ca
tegoryTheory.FinCategory J]       (F : CategoryTheory.Functor J C),       ∃ X, N
onempty (CategoryTheory.Limits.limit (F.op.comp (CategoryTheory.yoneda.obj X)))
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.limit (F.op.comp (Catego
ryTheory.yoneda.obj X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsFiltered.iff_cocone_nonempty`：iff_cocone_nonempty : IsF
iltered C ↔ forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), N
onempty (Cocone F)

--- 原说明 ---
`C` is filtered if and only if for every functor `F : J ⥤ C` from a finite categ
ory there is
    some `X : C` such that `lim Hom(F·, X)` is nonempty.

    Lemma 3.1.2 of [Kashiwara2006]
-/
theorem IsFiltered.iff_nonempty_limit : IsFiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F.op ⋙ yoneda.obj X)) := by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompYonedaIsoCocone F c.pt).inv c.ι⟩⟩
  · obtain ⟨pt, ⟨ι⟩⟩ := h F
    exact ⟨⟨pt, (limitCompYonedaIsoCocone F pt).hom ι⟩⟩

/-- `C` is cofiltered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(X, F·)` is nonempty. -/
/-
**CategoryTheory.IsCofiltered.iff_nonempty_limit** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsCofiltered`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   CategoryTheory
.IsCofiltered C ↔     ∀ {J : Type v} [inst_1 : CategoryTheory.SmallCategory J] [
CategoryTheory.FinCategory J]       (F : CategoryTheory.Functor J C),       ∃ X,
 Nonempty (CategoryTheory.Limits.limit (F.comp (CategoryTheory.coyoneda.obj (Opp
osite.op X))))
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.limit (F.comp (CategoryT
heory.coyoneda.obj (Opposite.op X)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsCofiltered.iff_cone_nonempty`：iff_cone_nonempty : IsCof
iltered C ↔ forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), N
onempty (Cone F)

--- 原说明 ---
`C` is cofiltered if and only if for every functor `F : J ⥤ C` from a finite cat
egory there is
    some `X : C` such that `lim Hom(X, F·)` is nonempty.
-/
theorem IsCofiltered.iff_nonempty_limit : IsCofiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F ⋙ coyoneda.obj (op X))) := by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompCoyonedaIsoCone F c.pt).inv c.π⟩⟩
  · obtain ⟨pt, ⟨π⟩⟩ := h F
    exact ⟨⟨pt, (limitCompCoyonedaIsoCone F pt).hom π⟩⟩

end NonemptyLimit

namespace Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize` would default to universe
-- output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.HasCofilteredLimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class HasCofilteredLimitsOfSize : Prop where
  /-- For all filtered types of size `w`, we have limits -/
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C

/-- Class for having all filtered colimits of a given size. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.HasFilteredColimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class for having all filtered colimits of a given size.
-/
class HasFilteredColimitsOfSize : Prop where
  /-- For all filtered types of a size `w`, we have colimits -/
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

/-- Class for having cofiltered limits. -/
/-
**CategoryTheory.Limits.HasCofilteredLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：HasCofilteredLimits
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class for having cofiltered limits.
-/
abbrev HasCofilteredLimits := HasCofilteredLimitsOfSize.{v, v} C

/-- Class for having filtered colimits. -/
/-
**CategoryTheory.Limits.HasFilteredColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：HasFilteredColimits
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class for having filtered colimits.
-/
abbrev HasFilteredColimits := HasFilteredColimitsOfSize.{v, v} C

end

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFilteredColimitsOfSize_of_hasColimitsOfSize
    [HasColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape _ _ _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCofilteredLimitsOfSize_of_hasLimitsOfSize
    [HasLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape _ _ _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.HasLimitsOfShape _
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _
/-
**CategoryTheory.Limits.hasCofilteredLimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasCofilteredLimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [H
asCofilteredLimitsOfSize.{w₂', w₂} C] : HasCofilteredLimitsOfSize.{w', w} C wher
e HasLimitsOfShape J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
-/
lemma hasCofilteredLimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasCofilteredLimitsOfSize.{w₂', w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape J :=
    haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasLimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm
/-
**CategoryTheory.Limits.hasCofilteredLimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasCofilteredLimitsOfSize_shrink [HasCofilteredLimitsOfSize.{max w' w₂', m
ax w w₂} C] : HasCofilteredLimitsOfSize.{w', w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCofilteredLimitsOfSize_of_univLE`：hasCofiltered
LimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [HasCofilteredLimitsO
fSize.{w₂', w₂} C] : HasCofilteredLimitsOfSize.…
-/
lemma hasCofilteredLimitsOfSize_shrink [HasCofilteredLimitsOfSize.{max w' w₂', max w w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C :=
  hasCofilteredLimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}
/-
**CategoryTheory.Limits.hasFilteredColimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFilteredColimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [H
asFilteredColimitsOfSize.{w₂', w₂} C] : HasFilteredColimitsOfSize.{w', w} C wher
e HasColimitsOfShape J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
-/
lemma hasFilteredColimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasFilteredColimitsOfSize.{w₂', w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape J :=
    haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasColimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm
/-
**CategoryTheory.Limits.hasFilteredColimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasFilteredColimitsOfSize_shrink [HasFilteredColimitsOfSize.{max w' w₂', m
ax w w₂} C] : HasFilteredColimitsOfSize.{w', w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_univLE`：hasFilteredCo
limitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}] [HasFilteredColimitsO
fSize.{w₂', w₂} C] : HasFilteredColimitsOfSize.…
-/
lemma hasFilteredColimitsOfSize_shrink [HasFilteredColimitsOfSize.{max w' w₂', max w w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C :=
  hasFilteredColimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

end Limits

end CategoryTheory

