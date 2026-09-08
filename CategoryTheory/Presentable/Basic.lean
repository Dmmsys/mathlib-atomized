/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsCardinalAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).
We also introduce another typeclass `Functor.IsAccessible` saying that there exists
a regular cardinal `κ` such that `Functor.IsCardinalAccessible`.

An object `X` of a category is `κ`-presentable (`IsCardinalPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.
Similarly as for accessible functors, we define a type class `IsAccessible`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe t w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

section

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor `F : C ⥤ D` is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category.
In the mathematical literature, some assumptions are often made on the
categories `C` or `D` (e.g. the existence of `κ`-filtered colimits,
see `HasCardinalFilteredColimits` below), but here we do not
make such assumptions. -/
/-
**CategoryTheory.Functor.IsCardinalAccessible** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Functor`。
形式化陈述：IsCardinalAccessible : Prop where preservesColimitOfShape (J : Type w) [Sm
allCategory J] [IsCardinalFiltered J κ] : PreservesColimitsOfShape J F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category.
In the mathematical literature, some assumptions are often made on the
categories `C` or `D` (e.g. the existence of `κ`-filtered colimits,
see `HasCardinalFilteredColimits` below), but here we do not
make such assumptions.
-/
class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by intros; infer_instance
/-
**CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ
] (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] : PreservesColimitsOfS
hape J F
参数：J : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCardinalAccessible.preservesColimitOfShape`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 :
 CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsCardinalAccessible.preservesColimitOfShape κ _
/-
**CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_ess
entiallySmall** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall [F.Is
CardinalAccessible κ] (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [
IsCardinalFiltered J κ] : PreservesColimitsOfShape J F
参数：J : Type u₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsCardinalFiltered.of_equivalence`：of_equivalence {J' : T
ype u'} [Category.{v'} J'] (e : J ≌ J') : IsCardinalFiltered J' κ where nonempty
_cocone F hA
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
-/
lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    [F.IsCardinalAccessible κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in
/-
**CategoryTheory.Functor.isCardinalAccessible_of_le** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：isCardinalAccessible_of_le [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} 
[Fact κ'.IsRegular] (h : κ <= κ') : F.IsCardinalAccessible κ' where preservesCol
imitOfShape {J _ _}
参数：h : κ <= κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsCardinalFiltered.of_le`：of_le {κ' : Cardinal.{w}} [Fact
 κ'.IsRegular] (h : κ' <= κ) : IsCardinalFiltered J κ' where nonempty_cocone F h
A
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
-/
lemma isCardinalAccessible_of_le
    [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsCardinalAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in
variable {F G} in
/-
**CategoryTheory.Functor.isCardinalAccessible_of_natIso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAc
cessible κ where preservesColimitOfShape J _ hκ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_natIso`：preservesColim
itsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] : 
PreservesColimitsOfShape J G where preservesCo…
-/
lemma isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalAccessible (𝟭 C) κ where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] :
    (F ⋙ G).IsCardinalAccessible κ := by
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ
  have := G.preservesColimitsOfShape_of_isCardinalAccessible κ
  exact { }
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesColimitsOfSize.{w, w} F] : F.IsCardinalAccessible κ where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) : IsCardinalAccessible ((Functor.const C).obj A) κ where
  preservesColimitOfShape J _ _ :=
    { preservesColimit {F} :=
        { preserves {c} hc := ⟨by
            have h := isFiltered_of_isCardinalFiltered J κ
            have (j : J) : IsIso ((((const C).obj A).mapCocone c).ι.app j) := by
              dsimp
              infer_instance
            exact Functor.IsEventuallyConstantFrom.isColimitOfIsIso
              (i₀ := h.nonempty.some) (fun _ _ ↦ by dsimp; infer_instance) _⟩ } }

end

section

variable (F : C ⥤ D)

/-- A functor is accessible relative to a universe `w` if
it is `κ`-accessible for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
/-
**CategoryTheory.Functor.IsAccessible** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is accessible relative to a universe `w` if
it is `κ`-accessible for some regular `κ : Cardinal.{w}`.
-/
class IsAccessible : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessible F κ
/-
**CategoryTheory.Functor.isAccessible_of_isCardinalAccessible** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isAccessible_of_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
 [IsCardinalAccessible F κ] : IsAccessible.{w} F where exists_cardinal
参数：κ : Cardinal.{w}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isAccessible_of_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessible F κ] : IsAccessible.{w} F where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) [IsAccessible.{w} F]
    [IsAccessible.{w} G] : IsAccessible.{w} (F ⋙ G) := by
  obtain ⟨κF, _, _⟩ := IsAccessible.exists_cardinal (F := F)
  obtain ⟨κG, _, _⟩ := IsAccessible.exists_cardinal (F := G)
  have : Fact (κF ⊔ κG).IsRegular := ⟨iteInduction (fun _ ↦ Fact.out) (fun _ ↦ Fact.out)⟩
  have := isCardinalAccessible_of_le F (by simp : κF ≤ κF ⊔ κG)
  have := isCardinalAccessible_of_le G (by simp : κG ≤ κF ⊔ κG)
  exact isAccessible_of_isCardinalAccessible (F ⋙ G) (κF ⊔ κG)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) : IsAccessible.{w} ((Functor.const C).obj A) := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

end

end Functor

section

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
/-
**CategoryTheory.IsCardinalPresentable** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：IsCardinalPresentable : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories.
-/
abbrev IsCardinalPresentable : Prop := (coyoneda.obj (op X)).IsCardinalAccessible κ

variable (C) in
/-- The property of objects that are `κ`-presentable. -/
/-
**CategoryTheory.isCardinalPresentable** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：isCardinalPresentable : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects that are `κ`-presentable.
-/
def isCardinalPresentable : ObjectProperty C := fun X ↦ IsCardinalPresentable X κ
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable X.obj κ :=
  X.property
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable ((isCardinalPresentable C κ).ι.obj X) κ := by
  dsimp
  infer_instance
/-
**CategoryTheory.isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj : IsCardinalPr
esentable X κ ↔ (coyoneda.obj (op X)).IsCardinalAccessible κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj :
    IsCardinalPresentable X κ ↔ (coyoneda.obj (op X)).IsCardinalAccessible κ := Iff.rfl
/-
**CategoryTheory.isCardinalPresentable_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isCardinalPresentable_iff (X : C) : isCardinalPresentable C κ X ↔ IsCardin
alPresentable X κ
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCardinalPresentable_iff (X : C) :
    isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ := Iff.rfl
/-
**CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：preservesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X
 κ] (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] : PreservesColim
itsOfShape J (coyoneda.obj (op X))
参数：J : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
-/
lemma preservesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ]
    (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J
/-
**CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable_of_essentiall
ySmall** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall [IsC
ardinalPresentable X κ] (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J]
 [IsCardinalFiltered J κ] : PreservesColimitsOfShape J (coyoneda.obj (op X))
参数：J : Type u₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible_
of_essentiallySmall`：preservesColimitsOfShape_of_isCardinalAccessible_of_essenti
allySmall [F.IsCardinalAccessible κ] (J : Type u₃) [Category.{v₃} J] [Essentiall
y…
-/
lemma preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
    [IsCardinalPresentable X κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

variable {κ} in
/-
**CategoryTheory.isCardinalPresentable_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：isCardinalPresentable_of_le [IsCardinalPresentable X κ] {κ' : Cardinal.{w}
} [Fact κ'.IsRegular] (h : κ <= κ') : IsCardinalPresentable X κ'
参数：h : κ <= κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isCardinalAccessible_of_le`：isCardinalAccessible_
of_le [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ 
<= κ') : F.IsCardinalAccessible κ' wher…
-/
lemma isCardinalPresentable_of_le [IsCardinalPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsCardinalPresentable X κ' :=
  (coyoneda.obj (op X)).isCardinalAccessible_of_le h

variable (C) {κ} in
/-
**CategoryTheory.isCardinalPresentable_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isCardinalPresentable_monotone {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h 
: κ <= κ') : isCardinalPresentable C κ <= isCardinalPresentable C κ'
参数：h : κ <= κ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalPresentable_iff`：isCardinalPresentable_iff (X :
 C) : isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ
· 使用引理 `CategoryTheory.isCardinalPresentable_of_le`：isCardinalPresentable_of_le 
[IsCardinalPresentable X κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ'
) : IsCardinalPresentable X κ'
-/
lemma isCardinalPresentable_monotone {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    isCardinalPresentable C κ ≤ isCardinalPresentable C κ' := by
  intro X hX
  rw [isCardinalPresentable_iff] at hX ⊢
  exact isCardinalPresentable_of_le _ h

include e in
variable {X Y} in
/-
**CategoryTheory.isCardinalPresentable_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPrese
ntable Y κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isCardinalAccessible_of_natIso`：isCardinalAccessi
ble_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where preser
vesColimitOfShape J _ hκ
-/
lemma isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ :=
  Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isCardinalPresentable C κ).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact isCardinalPresentable_of_iso e _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isCardinalPresentable_of_equivalence** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：isCardinalPresentable_of_equivalence {C' : Type u₃} [Category.{v₃} C'] [Is
CardinalPresentable X κ] (e : C ≌ C') : IsCardinalPresentable (e.functor.obj X) 
κ
参数：e : C ≌ C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable`：preser
vesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ] (J : Typ
e w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] : …
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesColimitsOfSizeUliftFunctor`：Cat
egoryTheory.Limits.PreservesColimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1
) (v + 1)}   CategoryTheory.uliftFunctor.{v, u}
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
lemma isCardinalPresentable_of_equivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (e : C ≌ C') :
    IsCardinalPresentable (e.functor.obj X) κ := by
  refine ⟨fun J _ _ ↦ ⟨fun {Y} ↦ ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc ↦ ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) hc)⟩⟩
  have iso : coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁} ≅
    e.inverse ⋙ coyoneda.obj (op X) ⋙ uliftFunctor.{v₃} :=
    NatIso.ofComponents (fun Z ↦
      (Equiv.ulift.trans ((e.toAdjunction.homEquiv X Z).trans Equiv.ulift.symm)).toIso) (by
        intro _ _ f
        ext ⟨g⟩
        simp [Adjunction.homEquiv_unit])
  exact preservesColimit_of_natIso Y iso.symm
/-
**CategoryTheory.isCardinalPresentable_of_isEquivalence** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory`。
形式化陈述：isCardinalPresentable_of_isEquivalence {C' : Type u₃} [Category.{v₃} C'] [
IsCardinalPresentable X κ] (F : C ⥤ C') [F.IsEquivalence] : IsCardinalPresentabl
e (F.obj X) κ
参数：F : C ⥤ C'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCardinalPresentable_of_equivalence`：isCardinalPresentab
le_of_equivalence {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] 
(e : C ≌ C') : IsCardinalPresentable (e.f…
-/
instance isCardinalPresentable_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ :=
  isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]
/-
**CategoryTheory.isCardinalPresentable_iff_of_isEquivalence** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory`。
形式化陈述：isCardinalPresentable_iff_of_isEquivalence {C' : Type u₃} [Category.{v₃} C
'] (F : C ⥤ C') [F.IsEquivalence] : IsCardinalPresentable (F.obj X) κ ↔ IsCardin
alPresentable X κ
参数：F : C ⥤ C'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCardinalPresentable_of_iso`：isCardinalPresentable_of_is
o [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ
-/
lemma isCardinalPresentable_iff_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ ↔ IsCardinalPresentable X κ := by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

section

variable {J : Type*} [Category* J] {D : J ⥤ C}

/-
**CategoryTheory.Limits.exists_hom_of_preservesColimit_coyoneda** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} {c : CategoryTheory.Limits.Cocone D}   (hc : CategoryTheory.Limits.IsColimit
 c) {X : C}   [CategoryTheory.Limits.PreservesColimit D (CategoryTheory.coyoneda
.obj (Opposite.op X))] (f : X ⟶ c.pt),   ∃ j p, CategoryTheory.CategoryStruct.co
mp p (c.ι.app j) = f
参数：hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.coyoneda.obj (Opposite.
op X)；f : X ⟶ c.pt；c.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
-/
lemma Limits.exists_hom_of_preservesColimit_coyoneda {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f
/-
**CategoryTheory.Limits.exists_eq_of_preservesColimit_coyoneda** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} [CategoryTheory.IsFiltered J]   {c : CategoryTheory.Limits.Cocone D} (hc : C
ategoryTheory.Limits.IsColimit c) {X : C}   [CategoryTheory.Limits.PreservesColi
mit D (CategoryTheory.coyoneda.obj (Opposite.op X))] {i j : J} (f : X ⟶ D.obj i)
   (g : X ⟶ D.obj j),   CategoryTheory.CategoryStruct.comp f (c.ι.app i) = Categ
oryTheory.CategoryStruct.comp g (c.ι.app j) →     ∃ k u v, CategoryTheory.Catego
ryStruct.comp f (D.map u) = CategoryTheory.CategoryStruct.comp g (D.map v)
参数：hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.coyoneda.obj (Opposite.
op X)；f : X ⟶ D.obj i；g : X ⟶ D.obj j；c.ι.app i；c.ι.app j；D.map u；D.map v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
-/
lemma Limits.exists_eq_of_preservesColimit_coyoneda [IsFiltered J] {c : Cocone D}
    (hc : IsColimit c) {X : C} [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h
/-
**CategoryTheory.Limits.exists_eq_of_preservesColimit_coyoneda_self** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} [CategoryTheory.IsFiltered J]   {c : CategoryTheory.Limits.Cocone D} (hc : C
ategoryTheory.Limits.IsColimit c) {X : C}   [CategoryTheory.Limits.PreservesColi
mit D (CategoryTheory.coyoneda.obj (Opposite.op X))] {i : J} (f g : X ⟶ D.obj i)
,   CategoryTheory.CategoryStruct.comp f (c.ι.app i) = CategoryTheory.CategorySt
ruct.comp g (c.ι.app i) →     ∃ j a, CategoryTheory.CategoryStruct.comp f (D.map
 a) = CategoryTheory.CategoryStruct.comp g (D.map a)
参数：hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.coyoneda.obj (Opposite.
op X)；f g : X ⟶ D.obj i；c.ι.app i；c.ι.app i；D.map a；D.map a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
-/
lemma Limits.exists_eq_of_preservesColimit_coyoneda_self [IsFiltered J] {c : Cocone D}
    (hc : IsColimit c) {X : C} [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f g).mp h
/-
**CategoryTheory.Limits.exists_hom_of_preservesColimit_yoneda** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} {c : CategoryTheory.Limits.Cone D}   (hc : CategoryTheory.Limits.IsLimit c) 
{X : C}   [CategoryTheory.Limits.PreservesColimit D.op (CategoryTheory.yoneda.ob
j X)] (f : c.pt ⟶ X),   ∃ j p, CategoryTheory.CategoryStruct.comp (c.π.app j) p 
= f
参数：hc : CategoryTheory.Limits.IsLimit c；CategoryTheory.yoneda.obj X；f : c.pt ⟶ X
；c.π.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
-/
lemma Limits.exists_hom_of_preservesColimit_yoneda {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)] (f : c.pt ⟶ X) :
    ∃ (j : J) (p : D.obj j ⟶ X), c.π.app j ≫ p = f := by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  exact ⟨j.unop, p, hp⟩
/-
**CategoryTheory.Limits.exists_eq_of_preservesColimit_yoneda** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} [CategoryTheory.IsCofiltered J]   {c : CategoryTheory.Limits.Cone D} (hc : C
ategoryTheory.Limits.IsLimit c) {X : C}   [CategoryTheory.Limits.PreservesColimi
t D.op (CategoryTheory.yoneda.obj X)] {i j : J} (f : D.obj i ⟶ X)   (g : D.obj j
 ⟶ X),   CategoryTheory.CategoryStruct.comp (c.π.app i) f = CategoryTheory.Categ
oryStruct.comp (c.π.app j) g →     ∃ k u v, CategoryTheory.CategoryStruct.comp (
D.map u) f = CategoryTheory.CategoryStruct.comp (D.map v) g
参数：hc : CategoryTheory.Limits.IsLimit c；CategoryTheory.yoneda.obj X；f : D.obj i 
⟶ X；g : D.obj j ⟶ X；c.π.app i；c.π.app j；D.map u；D.map v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
-/
lemma Limits.exists_eq_of_preservesColimit_yoneda [IsCofiltered J] {c : Cone D} (hc : IsLimit c)
    {X : C} [PreservesColimit D.op (yoneda.obj X)]
    {i j : J} (f : D.obj i ⟶ X) (g : D.obj j ⟶ X) (h : c.π.app i ≫ f = c.π.app j ≫ g) :
    ∃ (k : J) (u : k ⟶ i) (v : k ⟶ j), D.map u ≫ f = D.map v ≫ g := by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  exact ⟨k.unop, u.unop, v.unop, huv⟩
/-
**CategoryTheory.Limits.exists_eq_of_preservesColimit_yoneda_self** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTheory.Functor J
 C} [CategoryTheory.IsCofiltered J]   {c : CategoryTheory.Limits.Cone D} (hc : C
ategoryTheory.Limits.IsLimit c) {X : C}   [CategoryTheory.Limits.PreservesColimi
t D.op (CategoryTheory.yoneda.obj X)] {i : J} (f g : D.obj i ⟶ X),   CategoryThe
ory.CategoryStruct.comp (c.π.app i) f = CategoryTheory.CategoryStruct.comp (c.π.
app i) g →     ∃ j a, CategoryTheory.CategoryStruct.comp (D.map a) f = CategoryT
heory.CategoryStruct.comp (D.map a) g
参数：hc : CategoryTheory.Limits.IsLimit c；CategoryTheory.yoneda.obj X；f g : D.obj 
i ⟶ X；c.π.app i；c.π.app i；D.map a；D.map a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
-/
lemma Limits.exists_eq_of_preservesColimit_yoneda_self [IsCofiltered J] {c : Cone D}
    (hc : IsLimit c) {X : C} [PreservesColimit D.op (yoneda.obj X)]
    {i : J} (f g : D.obj i ⟶ X) (h : c.π.app i ≫ f = c.π.app i ≫ g) :
    ∃ (j : J) (a : j ⟶ i), D.map a ≫ f = D.map a ≫ g := by
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (yoneda.obj X) hc.op) f g).mp h
  exact ⟨j.unop, a.unop, ha⟩

variable {X} in
/-
**CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.IsCardinalPresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : C
ardinal.{w}) [inst_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 : CategoryTheo
ry.Category.{v_1, u_1} J] [CategoryTheory.IsCardinalPresentable X κ]   [Category
Theory.EssentiallySmall.{w, v_1, u_1} J] [CategoryTheory.IsCardinalFiltered J κ]
   {F : CategoryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone F} (hc : C
ategoryTheory.Limits.IsColimit c)   (f : X ⟶ c.pt), ∃ j f', CategoryTheory.Categ
oryStruct.comp f' (c.ι.app j) = f
参数：κ : Cardinal.{w}；hc : CategoryTheory.Limits.IsColimit c；f : X ⟶ c.pt；c.ι.app 
j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable_of_esse
ntiallySmall`：preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySm
all [IsCardinalPresentable X κ] (J : Type u₃) [Category.{v₃} J] [Essential…
· 使用定理 `CategoryTheory.Limits.exists_hom_of_preservesColimit_coyoneda`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}   [inst_1 : Ca
tegoryTheory.Category.{v_1, u_1} J] {D : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma IsCardinalPresentable.exists_hom_of_isColimit [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (f : X ⟶ c.pt) :
    ∃ (j : J) (f' : X ⟶ F.obj j), f' ≫ c.ι.app j = f := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  exact exists_hom_of_preservesColimit_coyoneda hc f

variable {X} in
/-
**CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.IsCardinalPresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : C
ardinal.{w}) [inst_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 : CategoryTheo
ry.Category.{v_1, u_1} J] [CategoryTheory.IsCardinalPresentable X κ]   [Category
Theory.EssentiallySmall.{w, v_1, u_1} J] [CategoryTheory.IsCardinalFiltered J κ]
   {F : CategoryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone F} (hc : C
ategoryTheory.Limits.IsColimit c)   {i₁ i₂ : J} (f₁ : X ⟶ F.obj i₁) (f₂ : X ⟶ F.
obj i₂),   CategoryTheory.CategoryStruct.comp f₁ (c.ι.app i₁) = CategoryTheory.C
ategoryStruct.comp f₂ (c.ι.app i₂) →     ∃ j u v, CategoryTheory.CategoryStruct.
comp f₁ (F.map u) = CategoryTheory.CategoryStruct.comp f₂ (F.map v)
参数：κ : Cardinal.{w}；hc : CategoryTheory.Limits.IsColimit c；f₁ : X ⟶ F.obj i₁；f₂ 
: X ⟶ F.obj i₂；c.ι.app i₁；c.ι.app i₂；F.map u；F.map v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable_of_esse
ntiallySmall`：preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySm
all [IsCardinalPresentable X κ] (J : Type u₃) [Category.{v₃} J] [Essential…
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.Limits.exists_eq_of_preservesColimit_coyoneda`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}   [inst_1 : Cat
egoryTheory.Category.{v_1, u_1} J] {D : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma IsCardinalPresentable.exists_eq_of_isColimit [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i₁ i₂ : J} (f₁ : X ⟶ F.obj i₁)
    (f₂ : X ⟶ F.obj i₂) (hf : f₁ ≫ c.ι.app i₁ = f₂ ≫ c.ι.app i₂) :
    ∃ (j : J) (u : i₁ ⟶ j) (v : i₂ ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map v := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda hc f₁ f₂ hf

variable {X} in
/-
**CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit'** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.IsCardinalPresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : C
ardinal.{w}) [inst_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 : CategoryTheo
ry.Category.{v_1, u_1} J] [CategoryTheory.IsCardinalPresentable X κ]   [Category
Theory.EssentiallySmall.{w, v_1, u_1} J] [CategoryTheory.IsCardinalFiltered J κ]
   {F : CategoryTheory.Functor J C} {c : CategoryTheory.Limits.Cocone F} (hc : C
ategoryTheory.Limits.IsColimit c) {i : J}   (f₁ f₂ : X ⟶ F.obj i),   CategoryThe
ory.CategoryStruct.comp f₁ (c.ι.app i) = CategoryTheory.CategoryStruct.comp f₂ (
c.ι.app i) →     ∃ j u, CategoryTheory.CategoryStruct.comp f₁ (F.map u) = Catego
ryTheory.CategoryStruct.comp f₂ (F.map u)
参数：κ : Cardinal.{w}；hc : CategoryTheory.Limits.IsColimit c；f₁ f₂ : X ⟶ F.obj i；c
.ι.app i；c.ι.app i；F.map u；F.map u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable_of_esse
ntiallySmall`：preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySm
all [IsCardinalPresentable X κ] (J : Type u₃) [Category.{v₃} J] [Essential…
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.Limits.exists_eq_of_preservesColimit_coyoneda_self`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u_1}   [inst_1 
: CategoryTheory.Category.{v_1, u_1} J] {D : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma IsCardinalPresentable.exists_eq_of_isColimit' [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i : J} (f₁ f₂ : X ⟶ F.obj i)
    (hf : f₁ ≫ c.ι.app i = f₂ ≫ c.ι.app i) :
    ∃ (j : J) (u : i ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map u := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda_self hc f₁ f₂ hf

end

/-
**CategoryTheory.isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_ob
j** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj : IsCardi
nalPresentable X κ ↔ (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleComp`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (κ : Cardinal.{w})…
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleOfPreservesColimitsOfSize
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesColimitsOfSizeUliftFunctor`：Cat
egoryTheory.Limits.PreservesColimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1
) (v + 1)}   CategoryTheory.uliftFunctor.{v, u}
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves`
：preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (
F ⋙ G)] [ReflectsColimitsOfShape J G] : PreservesColimitsOfSh…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
lemma isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj :
    IsCardinalPresentable X κ ↔ (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ := by
  change _ ↔ (coyoneda.obj (op X) ⋙ uliftFunctor.{t}).IsCardinalAccessible κ
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun J _ _ ↦ ?_⟩⟩
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (coyoneda.obj (op X) ⋙ uliftFunctor.{t}) κ J
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{t, v₁}
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCardinalPresentable X κ] :
    (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ :=
  (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{t} X κ).1 inferInstance

end

section

variable (X : C)

/-- An object of a category is presentable relative to a universe `w`
if it is `κ`-presentable for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
/-
**CategoryTheory.IsPresentable** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsPresentable (X : C) : Prop
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object of a category is presentable relative to a universe `w`
if it is `κ`-presentable for some regular `κ : Cardinal.{w}`.
-/
abbrev IsPresentable (X : C) : Prop :=
  Functor.IsAccessible.{w} (coyoneda.obj (op X))
/-
**CategoryTheory.isPresentable_of_isCardinalPresentable** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：isPresentable_of_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegula
r] [IsCardinalPresentable X κ] : IsPresentable.{w} X where exists_cardinal
参数：κ : Cardinal.{w}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isPresentable_of_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] : IsPresentable.{w} X where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end

section

/-- A category has `κ`-filtered colimits if it has colimits of shape `J`
for any `κ`-filtered category `J`. -/
/-
**CategoryTheory.HasCardinalFilteredColimits** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory`。
形式化陈述：HasCardinalFilteredColimits (C : Type u₁) [Category.{v₁} C] (κ : Cardinal.
{w}) [Fact κ.IsRegular] : Prop where hasColimitsOfShape (C) (J : Type w) [SmallC
ategory J] [IsCardinalFiltered J κ] : HasColimitsOfShape J C
参数：C : Type u₁；κ : Cardinal.{w}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has `κ`-filtered colimits if it has colimits of shape `J`
for any `κ`-filtered category `J`.
-/
class HasCardinalFilteredColimits (C : Type u₁) [Category.{v₁} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  hasColimitsOfShape (C) (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasColimitsOfSize.{w, w} C] :
    HasCardinalFilteredColimits.{w} C κ where

end

end CategoryTheory

