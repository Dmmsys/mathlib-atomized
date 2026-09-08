/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preservation of (co)limits in the functor category

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
  for `F : C ⥤ D` preserves colimits.

  The idea of the proof is simply that products and colimits in the functor category are computed
  pointwise, so pointwise preservation implies general preservation.
* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

## References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

@[expose] public section


universe w w' v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

section

variable {C : Type u} [Category.{v₁} C]
variable {D : Type u₂} [Category.{u} D]
variable {E : Type u} [Category.{v₂} E]

/-- If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a special case.
That is, even with a formalised proof of the general statement, there would still need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅
  prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
/-
**CategoryTheory.FunctorCategory.prod_preservesColimits** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.FunctorCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v₁, u} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{u, u₂} D]   [inst_2 : CategoryTheory.Limits.Has
BinaryProducts D] [CategoryTheory.Limits.HasColimits D]   [∀ (X : D), CategoryTh
eory.Limits.PreservesColimits (CategoryTheory.Limits.prod.functor.obj X)]   (F :
 CategoryTheory.Functor C D), CategoryTheory.Limits.PreservesColimits (CategoryT
heory.Limits.prod.functor.obj F)
参数：X : D；CategoryTheory.Limits.prod.functor.obj X；F : CategoryTheory.Functor C D
；CategoryTheory.Limits.prod.functor.obj F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasBinaryProductObjOfPreservesLimitDiscreteWal
kingPairPair`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : T
ype u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instIsIsoProdComparison`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.prodComparison_natural`：prodComparison_natural (f 
: A ⟶ A') (g : B ⟶ B') : F.map (prod.map f g) ≫ prodComparison F A' B' = prodCom
parison F A B ≫ prod.map (F.map f)…

--- 原说明 ---
If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `
F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a
 special case.
That is, even with a formalised proof of the general statement, there would stil
l need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅
  prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
lemma FunctorCategory.prod_preservesColimits [HasBinaryProducts D] [HasColimits D]
    [∀ X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F) where
  preservesColimitsOfShape {J : Type u} [Category.{u, u} J] :=
    {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let :=
              isColimitOfPreserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply IsColimit.mapCoconeEquiv _ this
            apply (NatIso.ofComponents _ _).symm
            · intro G
              apply asIso (prodComparison ((evaluation C D).obj k) F G)
            · intro G G'
              apply prodComparison_natural ((evaluation C D).obj k) (𝟙 F)⟩ }) }

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-
**CategoryTheory.whiskeringLeft_preservesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory`。
形式化陈述：whiskeringLeft_preservesLimitsOfShape (J : Type u) [Category.{v} J] [HasLi
mitsOfShape J D] (F : C ⥤ E) : PreservesLimitsOfShape J ((whiskeringLeft C E D).
obj F)
参数：J : Type u；F : C ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance whiskeringLeft_preservesLimitsOfShape (J : Type u) [Category.{v} J]
    [HasLimitsOfShape J D] (F : C ⥤ E) :
    PreservesLimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro Y
      change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩
/-
**CategoryTheory.whiskeringLeft_preservesColimitsOfShape** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory`。
形式化陈述：whiskeringLeft_preservesColimitsOfShape (J : Type u) [Category.{v} J] [Has
ColimitsOfShape J D] (F : C ⥤ E) : PreservesColimitsOfShape J ((whiskeringLeft C
 E D).obj F)
参数：J : Type u；F : C ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance whiskeringLeft_preservesColimitsOfShape (J : Type u) [Category.{v} J]
    [HasColimitsOfShape J D] (F : C ⥤ E) :
    PreservesColimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro Y
      change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩
/-
**CategoryTheory.whiskeringLeft_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：whiskeringLeft_preservesLimits [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E) : P
reservesLimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F)
参数：F : C ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance whiskeringLeft_preservesLimits [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesLimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesLimitsOfShape J F⟩
/-
**CategoryTheory.whiskeringLeft_preservesColimit** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory`。
形式化陈述：whiskeringLeft_preservesColimit [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E) 
: PreservesColimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F)
参数：F : C ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance whiskeringLeft_preservesColimit [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesColimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesColimitsOfShape J F⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [HasFiniteLimits E] :
    PreservesFiniteLimits ((Functor.whiskeringLeft C D E).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [HasFiniteColimits E] :
    PreservesFiniteColimits ((Functor.whiskeringLeft C D E).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance
/-
**CategoryTheory.whiskeringRight_preservesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory`。
形式化陈述：whiskeringRight_preservesLimitsOfShape {C : Type*} [Category* C] {D : Type
*} [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J] [HasLimitsO
fShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J 
((whiskeringRight C D E).obj F)
参数：F : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance whiskeringRight_preservesLimitsOfShape {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [F.ReflectsIsomorphisms] [PreservesLimitsOfShape J F] :
    ReflectsLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J E] (F : D ⥤ E) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨by
    apply evaluationJointlyReflectsLimits _ (fun k ↦ ?_)
    apply isLimitOfReflects F
    exact isLimitOfPreserves ((evaluation C E).obj k) hc⟩⟩⟩

/-- Whiskering right and then taking a limit is the same as taking the limit and applying the
functor. -/
/-
**CategoryTheory.limitCompWhiskeringRightIsoLimitComp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory`。
形式化陈述：limitCompWhiskeringRightIsoLimitComp {C : Type*} [Category* C] {D : Type*}
 [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J] [HasLimitsOfS
hape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) : limit (G ⋙ 
(whiskeringRight _ _ _).obj F) ≅ limit G ⋙ F
参数：F : D ⥤ E；G : J ⥤ C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering right and then taking a limit is the same as taking the limit and app
lying the
functor.
-/
def limitCompWhiskeringRightIsoLimitComp {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    limit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ limit G ⋙ F :=
  (preservesLimitIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.limitCompWhiskeringRightIsoLimitComp_inv_** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitCompWhiskeringRightIsoLimitComp_inv_π {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).inv ≫
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j = whiskerRight (limit.π G j) F := by
  simp [limitCompWhiskeringRightIsoLimitComp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).hom ≫ whiskerRight (limit.π G j) F =
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [← Iso.eq_inv_comp]
/-
**CategoryTheory.whiskeringRight_preservesColimitsOfShape** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory`。
形式化陈述：whiskeringRight_preservesColimitsOfShape {C : Type*} [Category* C] {D : Ty
pe*} [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J] [HasColim
itsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] : PreservesColimitsOf
Shape J ((whiskeringRight C D E).obj F)
参数：F : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance whiskeringRight_preservesColimitsOfShape {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun k => ?_)
      change IsColimit (((evaluation _ _).obj k ⋙ F).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

/-- Whiskering right and then taking a colimit is the same as taking the colimit and applying the
functor. -/
/-
**CategoryTheory.colimitCompWhiskeringRightIsoColimitComp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory`。
形式化陈述：colimitCompWhiskeringRightIsoColimitComp {C : Type*} [Category* C] {D : Ty
pe*} [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J] [HasColim
itsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) : col
imit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ colimit G ⋙ F
参数：F : D ⥤ E；G : J ⥤ C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering right and then taking a colimit is the same as taking the colimit and
 applying the
functor.
-/
def colimitCompWhiskeringRightIsoColimitComp {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    colimit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ colimit G ⋙ F :=
  (preservesColimitIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitCompWhiskeringRightIsoColimitComp_hom {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j ≫
      (colimitCompWhiskeringRightIsoColimitComp F G).hom = whiskerRight (colimit.ι G j) F := by
  simp [colimitCompWhiskeringRightIsoColimitComp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.whiskerRight_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv {C : Type*} [Category* C]
    {D : Type*} [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    whiskerRight (colimit.ι G j) F ≫ (colimitCompWhiskeringRightIsoColimitComp F G).inv =
      colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [Iso.comp_inv_eq]
/-
**CategoryTheory.whiskeringRightPreservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：whiskeringRightPreservesLimits {C : Type*} [Category* C] {D : Type*} [Cate
gory* D] {E : Type*} [Category* E] (F : D ⥤ E) [HasLimitsOfSize.{w, w'} D] [Pres
ervesLimitsOfSize.{w, w'} F] : PreservesLimitsOfSize.{w, w'} ((whiskeringRight C
 D E).obj F)
参数：F : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance whiskeringRightPreservesLimits {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : D ⥤ E) [HasLimitsOfSize.{w, w'} D]
    [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩
/-
**CategoryTheory.whiskeringRightPreservesColimits** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory`。
形式化陈述：whiskeringRightPreservesColimits {C : Type*} [Category* C] {D : Type*} [Ca
tegory* D] {E : Type*} [Category* E] (F : D ⥤ E) [HasColimitsOfSize.{w, w'} D] [
PreservesColimitsOfSize.{w, w'} F] : PreservesColimitsOfSize.{w, w'} ((whiskerin
gRight C D E).obj F)
参数：F : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance whiskeringRightPreservesColimits {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : D ⥤ E) [HasColimitsOfSize.{w, w'} D]
    [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩

/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
/-
**CategoryTheory.preservesLimit_of_lan_preservesLimit** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：preservesLimit_of_lan_preservesLimit {C D : Type u} [SmallCategory C] [Sma
llCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J] [PreservesLimitsOfShape
 J (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F
参数：F : C ⥤ D；J : Type u；F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `CategoryTheory.ULiftYoneda.instFullFunctorOppositeTypeUliftYoneda`：∀ (C 
: Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C], CategoryTheory.uliftYone
da.{w, v₁, u₁}.Full
· 使用定理 `CategoryTheory.ULiftYoneda.instFaithfulFunctorOppositeTypeUliftYoneda`：∀
 (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C], CategoryTheory.ulift
Yoneda.{w, v₁, u₁}.Faithful

--- 原说明 ---
If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so 
will `F`.
-/
lemma preservesLimit_of_lan_preservesLimit {C D : Type u} [SmallCategory C]
    [SmallCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J]
    [PreservesLimitsOfShape J (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F :=
  letI := preservesLimitsOfShape_of_natIso (J := J)
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm
  preservesLimitsOfShape_of_reflects_of_preserves F uliftYoneda.{u}

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
/-
**CategoryTheory.preservesFiniteLimits_of_evaluation** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：preservesFiniteLimits_of_evaluation {D : Type*} [Category* D] {E : Type*} 
[Category* E] (F : C ⥤ D ⥤ E) (h : forall d : D, PreservesFiniteLimits (F ⋙ (eva
luation D E).obj d)) : PreservesFiniteLimits F
参数：F : C ⥤ D ⥤ E；h : forall d : D, PreservesFiniteLimits (F ⋙ (evaluation D E).o
bj d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_evaluation`：preservesLim
itsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J] (_ : forall k
 : K, PreservesLimitsOfShape J (F ⋙ (evaluation …
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`.
-/
lemma preservesFiniteLimits_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteLimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteLimits F :=
  ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteLimits _⟩

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
/-
**CategoryTheory.preservesFiniteColimits_of_evaluation** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
形式化陈述：preservesFiniteColimits_of_evaluation {D : Type*} [Category* D] {E : Type*
} [Category* E] (F : C ⥤ D ⥤ E) (h : forall d : D, PreservesFiniteColimits (F ⋙ 
(evaluation D E).obj d)) : PreservesFiniteColimits F
参数：F : C ⥤ D ⥤ E；h : forall d : D, PreservesFiniteColimits (F ⋙ (evaluation D E)
.obj d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_evaluation`：preservesC
olimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J] (_ : fora
ll k : K, PreservesColimitsOfShape J (F ⋙ (evaluat…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`.
-/
lemma preservesFiniteColimits_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteColimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteColimits F :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteColimits _⟩

end

section

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable {D : Type u₃} [Category.{v₃} D]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimitsOfShape J (colim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesLimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (colim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        colimit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (colimitObjIsoColimitCompEvaluation _ _) ≪≫
          (by exact HasColimit.isoOfNatIso (Iso.refl _)) ≪≫
          (colimitObjIsoColimitCompEvaluation _ _).symm)
        (fun {F G} η => colimit_obj_ext (fun j => by simp [← NatTrans.comp_app_assoc]))
    preservesLimitsOfShape_of_natIso (i ≪≫ colimitFlipIsoCompColim _).symm)

end

section

variable [HasColimitsOfShape J C] [HasLimitsOfShape K C]
variable [PreservesColimitsOfShape J (lim : (K ⥤ C) ⥤ _)]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimitsOfShape J (lim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesColimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (lim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        limit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (limitObjIsoLimitCompEvaluation _ _) ≪≫
          (by exact HasLimit.isoOfNatIso (Iso.refl _)) ≪≫
          (limitObjIsoLimitCompEvaluation _ _).symm)
        (fun {F G} η => limit_obj_ext (fun j => by simp [← NatTrans.comp_app]))
    preservesColimitsOfShape_of_natIso (i ≪≫ limitFlipIsoCompLim _).symm)

end

end

end CategoryTheory

