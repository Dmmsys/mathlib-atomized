/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weighted limits

In this file, we define weighted limits (in the non enriched case).
Given a weight `W : J ⥤ Type w` and a functor `F : J ⥤ C`,
the `W`-weighted limit of `J` is the limit of the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`.

## References
* https://ncatlab.org/nlab/show/weighted+limit

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]

/-- Given `W : J ⥤ Type w` and `F : J ⥤ C`, this is the type of cones for
the functor `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`. -/
/-
**CategoryTheory.Limits.WeightedCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：WeightedCone (W : J ⥤ Type w) (F : J ⥤ C)
参数：W : J ⥤ Type w；F : J ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : J ⥤ Type w` and `F : J ⥤ C`, this is the type of cones for
the functor `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`.
-/
abbrev WeightedCone (W : J ⥤ Type w) (F : J ⥤ C) :=
  Cone (CategoryOfElements.π W ⋙ F)

/-- Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, we say that
the `W`-weighted limit of `F` exists if the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C` has a limit. -/
/-
**CategoryTheory.Limits.HasWeightedLimit** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasWeightedLimit (W : J ⥤ Type w) (F : J ⥤ C) : Prop
参数：W : J ⥤ Type w；F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, we say that
the `W`-weighted limit of `F` exists if the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C` has a limit.
-/
abbrev HasWeightedLimit (W : J ⥤ Type w) (F : J ⥤ C) : Prop :=
  HasLimit (CategoryOfElements.π W ⋙ F)

namespace WeightedCone

variable {W : J ⥤ Type w} {F : J ⥤ C}

/-- The projection `c.pt ⟶ F.obj j` for `c : WeightedCone W F`
and `x : W.obj j`. -/
/-
**CategoryTheory.Limits.WeightedCone.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits.WeightedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `c.pt ⟶ F.obj j` for `c : WeightedCone W F`
and `x : W.obj j`.
-/
protected abbrev π (c : WeightedCone W F) {j : J} (x : W.obj j) :
    c.pt ⟶ F.obj j :=
  (Cone.π c).app (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WeightedCone.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.WeightedCone`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {W : CategoryTheory.Functor J (Type
 w)} {F : CategoryTheory.Functor J C} (c : CategoryTheory.Limits.WeightedCone W 
F)   {i j : J} (x : W.obj i) (f : i ⟶ j),   CategoryTheory.CategoryStruct.comp (
c.π x) (F.map f) = c.π ((CategoryTheory.ConcreteCategory.hom (W.map f)) x)
参数：Type w；c : CategoryTheory.Limits.WeightedCone W F；x : W.obj i；f : i ⟶ j；c.π x
；F.map f；(CategoryTheory.ConcreteCategory.hom (W.map f)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
-/
protected lemma w (c : WeightedCone W F) {i j : J} (x : W.obj i) (f : i ⟶ j) :
    c.π x ≫ F.map f = c.π (W.map f x) :=
  Cone.w c (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
    (Functor.elementsMk _ _ (W.map f x)) f rfl)

variable (pt : C) (π : ∀ ⦃j : J⦄ (_ : W.obj j), pt ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for weighted cones. -/
@[simps pt]
/-
**CategoryTheory.Limits.WeightedCone.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.WeightedCone`。
形式化陈述：mk : WeightedCone W F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for weighted cones.
-/
def mk : WeightedCone W F where
  pt := pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]
/-
**CategoryTheory.Limits.WeightedCone.mk_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Limits.WeightedCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_π {j : J} (x : W.obj j) :
    (mk pt π hπ).π x = π x := rfl

/-- A weighted cone `c : WeightedCone W F` is a limit if it is so
as a cone of `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`. -/
/-
**CategoryTheory.Limits.WeightedCone.IsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.WeightedCone`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         {W : Catego
ryTheory.Functor J (Type w)} →           {F : CategoryTheory.Functor J C} → Cate
goryTheory.Limits.WeightedCone W F → Type (max (max (max u w) u') v')
参数：Type w；max (max (max u w) u') v'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weighted cone `c : WeightedCone W F` is a limit if it is so
as a cone of `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`.
-/
protected abbrev IsLimit (c : WeightedCone W F) := Limits.IsLimit c

namespace IsLimit

variable {c : WeightedCone W F} (hc : c.IsLimit) {Z : C}

include hc in
/-
**CategoryTheory.Limits.WeightedCone.IsLimit.hasWeightedLimit** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits.WeightedCone.IsLimit`。
形式化陈述：hasWeightedLimit : HasWeightedLimit W F
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasWeightedLimit : HasWeightedLimit W F := ⟨_, hc⟩

section

variable
  (π : ∀ ⦃j : J⦄ (_ : W.obj j), Z ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

/-- Constructor for morphisms from the point of a limit weighted cone. -/
/-
**CategoryTheory.Limits.WeightedCone.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.WeightedCone.IsLimit`。
形式化陈述：lift : Z ⟶ c.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from the point of a limit weighted cone.
-/
def lift : Z ⟶ c.pt :=
  Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WeightedCone.IsLimit.fac** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits.WeightedCone.IsLimit`。
形式化陈述：fac {j : J} (x : W.obj j) : hc.lift π hπ ≫ c.π x = π x
参数：x : W.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma fac {j : J} (x : W.obj j) :
    hc.lift π hπ ≫ c.π x = π x :=
  Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

end

include hc in
/-
**CategoryTheory.Limits.WeightedCone.IsLimit.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.WeightedCone.IsLimit`。
形式化陈述：hom_ext {f g : Z ⟶ c.pt} (h : forall {j : J} (x : W.obj j), f ≫ c.π x = g 
≫ c.π x) : f = g
参数：h : forall {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
lemma hom_ext {f g : Z ⟶ c.pt} (h : ∀ {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x) :
    f = g :=
  Limits.IsLimit.hom_ext hc (fun _ ↦ h _)

end IsLimit

open Opposite in
set_option backward.defeqAttrib.useBackward true in
/-- If the weight is `coyoneda.obj (op j) : J ⥤ Type _`, this is the limit
weighted cone for `F : J ⥤ C` with point `F.obj j`. -/
@[simps]
/-
**CategoryTheory.Limits.WeightedCone.coyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.WeightedCone`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         (F : Catego
ryTheory.Functor J C) →           (j : J) → CategoryTheory.Limits.WeightedCone (
CategoryTheory.coyoneda.obj (Opposite.op j)) F
参数：F : CategoryTheory.Functor J C；j : J；CategoryTheory.coyoneda.obj (Opposite.op
 j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the weight is `coyoneda.obj (op j) : J ⥤ Type _`, this is the limit
weighted cone for `F : J ⥤ C` with point `F.obj j`.
-/
protected abbrev coyoneda (F : J ⥤ C) (j : J) :
    WeightedCone (coyoneda.obj (op j)) F where
  pt := F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by simp [← Functor.map_comp, Category.id_comp, f.prop.symm]

set_option backward.defeqAttrib.useBackward true in
/-- The weighted limit of `F` for the weight `coyoneda.obj (op j)` is `F.obj j`. -/
/-
**CategoryTheory.Limits.WeightedCone.isLimitCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.WeightedCone`。
形式化陈述：isLimitCoyoneda (F : J ⥤ C) (j : J) : (WeightedCone.coyoneda F j).IsLimit 
where lift s
参数：F : J ⥤ C；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted limit of `F` for the weight `coyoneda.obj (op j)` is `F.obj j`.
-/
def isLimitCoyoneda (F : J ⥤ C) (j : J) : (WeightedCone.coyoneda F j).IsLimit where
  lift s := WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (CategoryOfElements.homMk (Functor.elementsMk _ j (𝟙 j)) x x.snd (by simp))
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

end WeightedCone

end Limits

namespace Functor

section

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (W W' W'' : J ⥤ Type w) (g : W ⟶ W') (g' : W' ⟶ W'') (F : J ⥤ C)
  [HasWeightedLimit W F] [HasWeightedLimit W' F] [HasWeightedLimit W'' F]

/-- Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, this is the `W`-weighted
limit of `F`. -/
/-
**CategoryTheory.Functor.weightedLimObjObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：weightedLimObjObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, this is the `W`-weighted
limit of `F`.
-/
noncomputable def weightedLimObjObj : C :=
  limit (CategoryOfElements.π W ⋙ F)

/-- The projections from the weighted limit. -/
@[no_expose]
/-
**CategoryTheory.Functor.weightedLimObjObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：weightedLimObjObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projections from the weighted limit.
-/
noncomputable def weightedLimObjObjπ ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjObj F ⟶ F.obj j :=
  limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.weightedLimObjObj_w** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：weightedLimObjObj_w ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂) : W.weightedL
imObjObjπ F x ≫ F.map f = W.weightedLimObjObjπ F (W.map f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
-/
lemma weightedLimObjObj_w ⦃j₁ j₂ : J⦄ (x : W.obj j₁)
    (f : j₁ ⟶ j₂) :
    W.weightedLimObjObjπ F x ≫ F.map f =
      W.weightedLimObjObjπ F (W.map f x) :=
  limit.w (CategoryOfElements.π W ⋙ F)
    (CategoryOfElements.homMk (Functor.elementsMk _ _ x) (Functor.elementsMk _ _
      (W.map f x)) f rfl)

/-- A choice of limit weighted cone. -/
/-
**CategoryTheory.Functor.weightedLimCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：weightedLimCone : WeightedCone W F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of limit weighted cone.
-/
noncomputable abbrev weightedLimCone :
    WeightedCone W F :=
  WeightedCone.mk (W.weightedLimObjObj F)
    (fun j x ↦ W.weightedLimObjObjπ F x)
    (fun j₁ j₂ x f ↦ by simp)

/-- The weighted cone `W.weightedLimCone F` is a limit. -/
@[no_expose]
/-
**CategoryTheory.Functor.isLimitWeightedLimCone** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：isLimitWeightedLimCone : (W.weightedLimCone F).IsLimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted cone `W.weightedLimCone F` is a limit.
-/
noncomputable def isLimitWeightedLimCone :
    (W.weightedLimCone F).IsLimit :=
  limit.isLimit _

@[reassoc, simp] -- `simp` can prove the `reassoc` version
/-
**CategoryTheory.Functor.isLimitWeightedLimCone_fac** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：isLimitWeightedLimCone_fac {Z} (π) (hπ) ⦃j : J⦄ (x : W.obj j) : (W.isLimit
WeightedLimCone F).lift (Z
参数：π；hπ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.WeightedCone.IsLimit.fac`：fac {j : J} (x : W.obj j
) : hc.lift π hπ ≫ c.π x = π x
-/
lemma isLimitWeightedLimCone_fac {Z} (π) (hπ) ⦃j : J⦄ (x : W.obj j) :
    (W.isLimitWeightedLimCone F).lift (Z := Z) π hπ ≫ W.weightedLimObjObjπ F x = π x :=
  (W.isLimitWeightedLimCone F).fac ..

variable {W F} in
@[ext]
/-
**CategoryTheory.Functor.weightedLimObjObj.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.weightedLimObjObj`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {W : CategoryTheory.Functor J (Type
 w)} {F : CategoryTheory.Functor J C}   [inst_2 : CategoryTheory.Limits.HasWeigh
tedLimit W F] {Z : C} {f g : Z ⟶ W.weightedLimObjObj F},   (∀ {j : J} (x : W.obj
 j),       CategoryTheory.CategoryStruct.comp f (W.weightedLimObjObjπ F x) =    
     CategoryTheory.CategoryStruct.comp g (W.weightedLimObjObjπ F x)) →     f = 
g
参数：Type w；∀ {j : J} (x : W.obj j),       CategoryTheory.CategoryStruct.comp f (W
.weightedLimObjObjπ F x) =         CategoryTheory.CategoryStruct.comp g (W.weigh
tedLimObjObjπ F x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.WeightedCone.IsLimit.hom_ext`：hom_ext {f g : Z ⟶ c
.pt} (h : forall {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x) : f = g
-/
lemma weightedLimObjObj.hom_ext {Z : C} {f g : Z ⟶ W.weightedLimObjObj F}
    (h : ∀ {j : J} (x : W.obj j),
      f ≫ W.weightedLimObjObjπ F x = g ≫ W.weightedLimObjObjπ F x) :
    f = g :=
  (W.isLimitWeightedLimCone F).hom_ext h

/-- Functoriality of the weighted limits with fixed weight `W : J ⥤ Type w`
with respect to the functor in `J ⥤ C`. -/
@[no_expose]
/-
**CategoryTheory.Functor.weightedLimObjMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：weightedLimObjMap {F₁ F₂ : J ⥤ C} [HasWeightedLimit W F₁] [HasWeightedLimi
t W F₂] (f : F₁ ⟶ F₂) : W.weightedLimObjObj F₁ ⟶ W.weightedLimObjObj F₂
参数：f : F₁ ⟶ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of the weighted limits with fixed weight `W : J ⥤ Type w`
with respect to the functor in `J ⥤ C`.
-/
noncomputable def weightedLimObjMap {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) :
    W.weightedLimObjObj F₁ ⟶ W.weightedLimObjObj F₂ :=
  limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.weightedLimObjMap_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightedLimObjMap_π {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂)
    ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjMap f ≫ W.weightedLimObjObjπ F₂ x =
      W.weightedLimObjObjπ F₁ x ≫ f.app j :=
  limit.lift_π ..

@[simp]
/-
**CategoryTheory.Functor.weightedLimObjMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：weightedLimObjMap_id (F : J ⥤ C) [HasWeightedLimit W F] : W.weightedLimObj
Map (𝟙 F) = 𝟙 _
参数：F : J ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.weightedLimObjObj.hom_ext`：∀ {J : Type u} [inst :
 CategoryTheory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Catego
ry.{v', u'} C]   {W : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.weightedLimObjMap_π`：weightedLimObjMap_π {F₁ F₂ :
 J ⥤ C} [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) ⦃j : J⦄ (x
 : W.obj j) : W.weightedLimObjMa…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedLimObjMap_id (F : J ⥤ C) [HasWeightedLimit W F] :
    W.weightedLimObjMap (𝟙 F) = 𝟙 _ := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.Functor.weightedLimObjMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：weightedLimObjMap_comp {F₁ F₂ F₃ : J ⥤ C} [HasWeightedLimit W F₁] [HasWeig
htedLimit W F₂] [HasWeightedLimit W F₃] (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : W.weighted
LimObjMap (f ≫ g) = W.weightedLimObjMap f ≫ W.weightedLimObjMap g
参数：f : F₁ ⟶ F₂；g : F₂ ⟶ F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.weightedLimObjObj.hom_ext`：∀ {J : Type u} [inst :
 CategoryTheory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Catego
ry.{v', u'} C]   {W : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.weightedLimObjMap_π`：weightedLimObjMap_π {F₁ F₂ :
 J ⥤ C} [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) ⦃j : J⦄ (x
 : W.obj j) : W.weightedLimObjMa…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.weightedLimObjMap_π_assoc`：∀ {J : Type u} [inst :
 CategoryTheory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Catego
ry.{v', u'} C]   (W : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedLimObjMap_comp {F₁ F₂ F₃ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] [HasWeightedLimit W F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    W.weightedLimObjMap (f ≫ g) = W.weightedLimObjMap f ≫ W.weightedLimObjMap g := by
  cat_disch

section

variable {W W' W''}

/-- The (contravariant) functoriality of weighted limits with respect to the weight. -/
/-
**CategoryTheory.Functor.weightedLimFlipObjMap** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：weightedLimFlipObjMap : W'.weightedLimObjObj F ⟶ W.weightedLimObjObj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (contravariant) functoriality of weighted limits with respect to the weight.
-/
noncomputable def weightedLimFlipObjMap :
    W'.weightedLimObjObj F ⟶ W.weightedLimObjObj F :=
  (W.isLimitWeightedLimCone F).lift
    (fun j x ↦ W'.weightedLimObjObjπ F (g.app j x)) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.weightedLimObjObjMap_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightedLimObjObjMap_π ⦃j : J⦄ (x : W.obj j) :
    weightedLimFlipObjMap g F ≫ W.weightedLimObjObjπ F x =
      W'.weightedLimObjObjπ F (g.app j x) :=
  (W.isLimitWeightedLimCone F).fac ..

@[simp]
/-
**CategoryTheory.Functor.weightedLimFlipObjMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：weightedLimFlipObjMap_id : weightedLimFlipObjMap (𝟙 W) F = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.weightedLimObjObj.hom_ext`：∀ {J : Type u} [inst :
 CategoryTheory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Catego
ry.{v', u'} C]   {W : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.weightedLimObjObjMap_π`：weightedLimObjObjMap_π ⦃j
 : J⦄ (x : W.obj j) : weightedLimFlipObjMap g F ≫ W.weightedLimObjObjπ F x = W'.
weightedLimObjObjπ F (g.app j x)
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedLimFlipObjMap_id :
    weightedLimFlipObjMap (𝟙 W) F = 𝟙 _ := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.Functor.weightedLimFlipObjMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：weightedLimFlipObjMap_comp : weightedLimFlipObjMap g' F ≫ weightedLimFlipO
bjMap g F = weightedLimFlipObjMap (g ≫ g') F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.weightedLimObjObj.hom_ext`：∀ {J : Type u} [inst :
 CategoryTheory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Catego
ry.{v', u'} C]   {W : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.weightedLimObjObjMap_π`：weightedLimObjObjMap_π ⦃j
 : J⦄ (x : W.obj j) : weightedLimFlipObjMap g F ≫ W.weightedLimObjObjπ F x = W'.
weightedLimObjObjπ F (g.app j x)
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedLimFlipObjMap_comp :
    weightedLimFlipObjMap g' F ≫ weightedLimFlipObjMap g F =
    weightedLimFlipObjMap (g ≫ g') F := by
  cat_disch

end

end

end Functor

end CategoryTheory

