/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

@[expose] public section

assert_not_exists AddCommMonoid

open Opposite CategoryTheory Limits ConcreteCategory

universe t w w' v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type u} [Category.{v} C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
@[simps]
/-
**CategoryTheory.Coyoneda.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Coyoneda`。
形式化陈述：colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where pt
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app _ := ↾fun _ ↦ by cat_disch }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
/-
**CategoryTheory.Coyoneda.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Coyoneda`。
形式化陈述：colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where desc 
s
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc s := ↾fun _ ↦ s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    simpa using congr_hom (s.w f).symm (𝟙 (unop X))
  uniq s m w := by
    ext ⟨⟩
    simp [← w]
/-
**CategoryTheory.Coyoneda.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Coyoneda`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

/-- The colimit of `coyoneda.obj X` is isomorphic to `PUnit`.
-/
/-
**CategoryTheory.Coyoneda.colimitCoyonedaIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Coyoneda`。
形式化陈述：colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Coyoneda.instHasColimitObjOppositeFunctorTypeCoyoneda`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheo
ry.Limits.HasColimit (CategoryTheory.coyoneda.obj X)

--- 原说明 ---
The colimit of `coyoneda.obj X` is isomorphic to `PUnit`.
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit := by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

section

variable {J : Type w} [Category.{t} J]

set_option backward.defeqAttrib.useBackward true in
/-- The cone of `F` corresponding to an element in `(F ⋙ yoneda.obj X).sections`. -/
@[simps]
/-
**CategoryTheory.Limits.coneOfSectionCompYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} →       [inst_1 : CategoryTheory.Category.{t, w} J] →         (F : CategoryT
heory.Functor J Cᵒᵖ) →           (X : C) → ↑(F.comp (CategoryTheory.yoneda.obj X
)).sections → CategoryTheory.Limits.Cone F
参数：F : CategoryTheory.Functor J Cᵒᵖ；X : C；F.comp (CategoryTheory.yoneda.obj X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone of `F` corresponding to an element in `(F ⋙ yoneda.obj X).sections`.
-/
def Limits.coneOfSectionCompYoneda (F : J ⥤ Cᵒᵖ) (X : C)
    (s : (F ⋙ yoneda.obj X).sections) : Cone F where
  pt := Opposite.op X
  π := {
    app := fun j => (s.val j).op
    naturality _ _ f := by simp [(s.property f).symm] }
/-
**CategoryTheory.yoneda_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：yoneda_preservesLimit (F : J ⥤ Cᵒᵖ) (X : C) : PreservesLimit F (yoneda.obj
 X) where preserves {c} hc
参数：F : J ⥤ Cᵒᵖ；X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isLimit_iff`：isLimit_iff (c : Cone F) : None
mpty (IsLimit c) ↔ forall s in F.sections, exists! x : c.pt, forall j, c.π.app j
 x = s j
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
instance yoneda_preservesLimit (F : J ⥤ Cᵒᵖ) (X : C) :
    PreservesLimit F (yoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) _
          (fun j => Quiver.Hom.unop_inj (hm j)))⟩

variable (J) in
/-
**CategoryTheory.yoneda_preservesLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Type w) [ins
t_1 : CategoryTheory.Category.{t, w} J]   (X : C), CategoryTheory.Limits.Preserv
esLimitsOfShape J (CategoryTheory.yoneda.obj X)
参数：J : Type w；X : C；CategoryTheory.yoneda.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance yoneda_preservesLimitsOfShape (X : C) :
    PreservesLimitsOfShape J (yoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embeddings jointly reflect limits. -/
/-
**CategoryTheory.yonedaJointlyReflectsLimits** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F) (hc : forall X : C,
 IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where lift s
参数：F : J ⥤ Cᵒᵖ；c : Cone F；hc : forall X : C, IsLimit ((yoneda.obj X).mapCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda embeddings jointly reflect limits.
-/
def yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F)
    (hc : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where
  lift s := ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt)))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).injective
    ext j
    have eq := congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt))
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    simp_all [← hm])

/-- A cocone is colimit iff it becomes limit after the
application of `yoneda.obj X` for all `X : C`. -/
/-
**CategoryTheory.Limits.Cocone.isColimitYonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} →       [inst_1 : CategoryTheory.Category.{t, w} J] →         {F : CategoryT
heory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →           
  CategoryTheory.Limits.IsColimit c ≃               ((X : C) → CategoryTheory.Li
mits.IsLimit ((CategoryTheory.yoneda.obj X).mapCone c.op))
参数：c : CategoryTheory.Limits.Cocone F；(X : C) → CategoryTheory.Limits.IsLimit ((
CategoryTheory.yoneda.obj X).mapCone c.op)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone is colimit iff it becomes limit after the
application of `yoneda.obj X` for all `X : C`.
-/
noncomputable def Limits.Cocone.isColimitYonedaEquiv {F : J ⥤ C} (c : Cocone F) :
    IsColimit c ≃ ∀ (X : C), IsLimit ((yoneda.obj X).mapCone c.op) where
  toFun h _ := isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

set_option backward.defeqAttrib.useBackward true in
/-- The cone of `F` corresponding to an element in `(F ⋙ coyoneda.obj X).sections`. -/
@[simps]
/-
**CategoryTheory.Limits.coneOfSectionCompCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} →       [inst_1 : CategoryTheory.Category.{t, w} J] →         (F : CategoryT
heory.Functor J C) →           (X : Cᵒᵖ) → ↑(F.comp (CategoryTheory.coyoneda.obj
 X)).sections → CategoryTheory.Limits.Cone F
参数：F : CategoryTheory.Functor J C；X : Cᵒᵖ；F.comp (CategoryTheory.coyoneda.obj X)
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone of `F` corresponding to an element in `(F ⋙ coyoneda.obj X).sections`.
-/
def Limits.coneOfSectionCompCoyoneda (F : J ⥤ C) (X : Cᵒᵖ)
    (s : (F ⋙ coyoneda.obj X).sections) : Cone F where
  pt := X.unop
  π := {
    app := fun j => s.val j
    naturality _ _ f := by simp [(s.property f).symm] }
/-
**CategoryTheory.coyoneda_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：coyoneda_preservesLimit (F : J ⥤ C) (X : Cᵒᵖ) : PreservesLimit F (coyoneda
.obj X) where preserves {c} hc
参数：F : J ⥤ C；X : Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isLimit_iff`：isLimit_iff (c : Cone F) : None
mpty (IsLimit c) ↔ forall s in F.sections, exists! x : c.pt, forall j, c.π.app j
 x = s j
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
-/
instance coyoneda_preservesLimit (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

variable (J) in
/-
**CategoryTheory.coyonedaPreservesLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Type w) [ins
t_1 : CategoryTheory.Category.{t, w} J]   (X : Cᵒᵖ), CategoryTheory.Limits.Prese
rvesLimitsOfShape J (CategoryTheory.coyoneda.obj X)
参数：J : Type w；X : Cᵒᵖ；CategoryTheory.coyoneda.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance coyonedaPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (coyoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/-- The coyoneda embeddings jointly reflect limits. -/
/-
**CategoryTheory.coyonedaJointlyReflectsLimits** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F) (hc : forall X : Cᵒ
ᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where lift s
参数：F : J ⥤ C；c : Cone F；hc : forall X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c
)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coyoneda embeddings jointly reflect limits.
-/
def coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F)
    (hc : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where
  lift s := (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_hom ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    have eq := congr_hom ((hc (op s.pt)).fac ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
    cat_disch

/-- A cone is limit iff it is so after the application of `coyoneda.obj X` for all `X : Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.Cone.isLimitCoyonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Cone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} →       [inst_1 : CategoryTheory.Category.{t, w} J] →         {F : CategoryT
heory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →             
CategoryTheory.Limits.IsLimit c ≃               ((X : Cᵒᵖ) → CategoryTheory.Limi
ts.IsLimit ((CategoryTheory.coyoneda.obj X).mapCone c))
参数：c : CategoryTheory.Limits.Cone F；(X : Cᵒᵖ) → CategoryTheory.Limits.IsLimit ((
CategoryTheory.coyoneda.obj X).mapCone c)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone is limit iff it is so after the application of `coyoneda.obj X` for all `
X : Cᵒᵖ`.
-/
noncomputable def Limits.Cone.isLimitCoyonedaEquiv {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit ((coyoneda.obj X).mapCone c) where
  toFun h _ := isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

end

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
/-
**CategoryTheory.yoneda_preservesLimits** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X : C),   Catego
ryTheory.Limits.PreservesLimitsOfSize.{t, w, v, v, u, v + 1} (CategoryTheory.yon
eda.obj X)
参数：X : C；CategoryTheory.yoneda.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.yoneda_preservesLimitsOfShape`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] (J : Type w) [inst_1 : CategoryTheory.Category.{t
, w} J]   (X : C), CategoryTheory.…

--- 原说明 ---
The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits.
-/
instance yoneda_preservesLimits (X : C) :
    PreservesLimitsOfSize.{t, w} (yoneda.obj X) where

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
/-
**CategoryTheory.coyoneda_preservesLimits** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X : Cᵒᵖ),   Cate
goryTheory.Limits.PreservesLimitsOfSize.{t, w, v, v, u, v + 1} (CategoryTheory.c
oyoneda.obj X)
参数：X : Cᵒᵖ；CategoryTheory.coyoneda.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.coyonedaPreservesLimitsOfShape`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (J : Type w) [inst_1 : CategoryTheory.Category.{
t, w} J]   (X : Cᵒᵖ), CategoryTheor…

--- 原说明 ---
The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves lim
its.
-/
instance coyoneda_preservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{t, w} (coyoneda.obj X) where
/-
**CategoryTheory.yonedaFunctor_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory`。
形式化陈述：yonedaFunctor_preservesLimits : PreservesLimitsOfSize.{t, w} (@yoneda C _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_evaluation`：preservesLimits_of_
evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙
 (evaluation K C).obj k)) : PreservesLimi…
· 使用定理 `CategoryTheory.coyoneda_preservesLimits`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesLimitsOfSi
ze.{t, w, v, v, u, v + 1} (Ca…
-/
instance yonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@yoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance
/-
**CategoryTheory.coyonedaFunctor_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory`。
形式化陈述：coyonedaFunctor_preservesLimits : PreservesLimitsOfSize.{t, w} (@coyoneda 
C _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_evaluation`：preservesLimits_of_
evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙
 (evaluation K C).obj k)) : PreservesLimi…
· 使用定理 `CategoryTheory.yoneda_preservesLimits`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (X : C),   CategoryTheory.Limits.PreservesLimitsOfSize.{
t, w, v, v, u, v + 1} (Cate…
-/
noncomputable instance coyonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@coyoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance
/-
**CategoryTheory.yonedaFunctor_reflectsLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory`。
形式化陈述：yonedaFunctor_reflectsLimits : ReflectsLimitsOfSize.{t, w} (@yoneda C _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance yonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@yoneda C _) := inferInstance
/-
**CategoryTheory.coyonedaFunctor_reflectsLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：coyonedaFunctor_reflectsLimits : ReflectsLimitsOfSize.{t, w} (@coyoneda C 
_)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance coyonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@coyoneda C _) := inferInstance
/-
**CategoryTheory.uliftYonedaFunctor_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory`。
形式化陈述：uliftYonedaFunctor_preservesLimits : PreservesLimitsOfSize.{t, w} (uliftYo
neda.{w'} : C ⥤ _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_evaluation`：preservesLimits_of_
evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙
 (evaluation K C).obj k)) : PreservesLimi…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.coyoneda_preservesLimits`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesLimitsOfSi
ze.{t, w, v, v, u, v + 1} (Ca…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesLimitsOfSizeUliftFunctor`：Categ
oryTheory.Limits.PreservesLimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1) (v
 + 1)}   CategoryTheory.uliftFunctor.{v, u}
-/
instance uliftYonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (uliftYoneda.{w'} : C ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (coyoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj _ ⋙ uliftFunctor.{w'})
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w'} C] :
    PreservesLimitsOfSize.{t, w} (shrinkYoneda.{w'} (C := C)) :=
  preservesLimits_of_evaluation _ (fun K ↦ ⟨fun {J _} ↦ by
    have := preservesLimitsOfShape_of_natIso (J := J) (Functor.associator _ _ _ ≪≫
      shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor.{w'} K).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}⟩)

namespace Functor

section Representable

variable (F : Cᵒᵖ ⥤ Type w') [F.IsRepresentable]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfSize.{t, w} F := by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso.symm]
  exact inferInstanceAs <| PreservesLimitsOfSize (yoneda.obj _ ⋙ uliftFunctor)

end Representable

section Corepresentable

variable (F : C ⥤ Type*) [F.IsCorepresentable]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfSize.{t, w} F := by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftCoyonedaCoreprXIso.symm]
  exact inferInstanceAs <| PreservesLimitsOfSize (coyoneda.obj _ ⋙ uliftFunctor)

end Corepresentable

end Functor

end CategoryTheory

