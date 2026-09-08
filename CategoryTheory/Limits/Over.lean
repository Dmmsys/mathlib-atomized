/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : Over X ⥤ C` creates colimits, and hence `Over X` has
any colimits that `C` has (as well as the dual that `forget X : Under X ⟶ C` creates limits).

Note that the folder `CategoryTheory.Limits.Shapes.Constructions.Over` further shows that
`forget X : Over X ⥤ C` creates connected limits (so `Over X` has connected limits), and that
`Over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.
-/

@[expose] public section


noncomputable section

-- morphism levels before object levels. See note [category_theory universes].
universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

/-
**CategoryTheory.Over.hasColimit_of_hasColimit_comp_forget** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Over`。
形式化陈述：hasColimit_of_hasColimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙
 forget X)] : HasColimit F
参数：F : J ⥤ Over X；F ⋙ forget X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance hasColimit_of_hasColimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)] :
    HasColimit F :=
  CostructuredArrow.hasColimit (i₁ := i)
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Over X) where
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] : HasFiniteColimits (Over X) where
  out _ _ _ := inferInstance
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : HasColimits (Over X) :=
  ⟨inferInstance⟩
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteCoproducts C] : HasFiniteCoproducts (Over X) where
  out := inferInstance
/-
**CategoryTheory.Over.createsColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：createsColimitsOfSize : CreatesColimitsOfSize.{w, w'} (forget X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance createsColimitsOfSize : CreatesColimitsOfSize.{w, w'} (forget X) :=
  CostructuredArrow.createsColimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasColimits C] : PreservesColimits (forget X) :=
  inferInstance
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ReflectsColimits (forget X) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Over.epi_left_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h
.left
参数：h : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h.left :=
  CostructuredArrow.epi_left_of_epi _
/-
**CategoryTheory.Over.epi_iff_epi_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Over`。
形式化陈述：epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi 
h.left
参数：h : f ⟶ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.epi_iff_epi_left`：epi_iff_epi_left [Has
Pushouts A] [PreservesColimitsOfShape WalkingSpan G] {Y Z : CostructuredArrow G 
X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi h.left :=
  CostructuredArrow.epi_iff_epi_left _
/-
**CategoryTheory.Over.createsColimitsOfSizeMapCompForget** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Over`。
形式化陈述：createsColimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) : CreatesColimitsOf
Size.{w, w'} (map f ⋙ forget Y)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance createsColimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesColimitsOfSize.{w, w'} (map f ⋙ forget Y) :=
  show CreatesColimitsOfSize.{w, w'} (forget X) from inferInstance
/-
**CategoryTheory.Over.preservesColimitsOfSize_map** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：preservesColimitsOfSize_map [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶
 Y) : PreservesColimitsOfSize.{w, w'} (map f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_reflects_of_preserves`：preser
vesColimits_of_reflects_of_preserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)] [
ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsO…
· 使用定理 `CategoryTheory.preservesColimits_of_createsColimits_and_hasColimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsColimitsOfCreatesColimits`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance preservesColimitsOfSize_map [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{w, w'} (map f) :=
  preservesColimits_of_reflects_of_preserves (map f) (forget Y)

/-- If `c` is a colimit cocone, then so is the cocone `c.toOver` with cocone point `𝟙 c.pt`. -/
/-
**CategoryTheory.Over.isColimitToOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：isColimitToOver {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsColimit 
c.toOver
参数：hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a colimit cocone, then so is the cocone `c.toOver` with cocone point `
𝟙 c.pt`.
-/
def isColimitToOver {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsColimit c.toOver :=
  isColimitOfReflects (forget c.pt) <| IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

/-- If `F` has a colimit, then the cocone `colimit.toOver F` with cocone point `𝟙 (colimit F)` is
    also a colimit cocone. -/
/-
**CategoryTheory.Over._root_.CategoryTheory.Limits.colimit.isColimitToOver** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a colimit, then the cocone `colimit.toOver F` with cocone point `𝟙 (c
olimit F)` is
    also a colimit cocone.
-/
def _root_.CategoryTheory.Limits.colimit.isColimitToOver (F : J ⥤ C) [HasColimit F] :
    IsColimit (colimit.toOver F) :=
  Over.isColimitToOver (colimit.isColimit F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given an arrow `c.pt ⟶ X`, the diagram `J ⥤ C` can be lifted to `Over X ⥤ C`, and
the cocone `c` also lifts to the diagram on `Over`. -/
/-
**CategoryTheory.Over.liftCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     {C : Typ
e u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Category
Theory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →          
   {X : C} →               (f : c.pt ⟶ X) →                 CategoryTheory.Limit
s.Cocone                   (CategoryTheory.Over.lift F                     (Cate
goryTheory.CategoryStruct.comp c.ι ((CategoryTheory.Functor.const J).map f)))
参数：c : CategoryTheory.Limits.Cocone F；f : c.pt ⟶ X；CategoryTheory.Over.lift F   
                  (CategoryTheory.CategoryStruct.comp c.ι ((CategoryTheory.Funct
or.const J).map f))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an arrow `c.pt ⟶ X`, the diagram `J ⥤ C` can be lifted to `Over X ⥤ C`, an
d
the cocone `c` also lifts to the diagram on `Over`.
-/
@[simps] def liftCocone {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X) :
    Cocone (Over.lift F (c.ι ≫ (Functor.const J).map f)) where
  pt := Over.mk f
  ι.app j := Over.homMk (c.ι.app j)

/-- `Over.liftCocone` is limiting if the original cocone is. -/
/-
**CategoryTheory.Over.isColimitLiftCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：isColimitLiftCocone {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X) (hc 
: IsColimit c) : IsColimit (liftCocone c f)
参数：c : Cocone F；f : c.pt ⟶ X；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Over.liftCocone` is limiting if the original cocone is.
-/
noncomputable def isColimitLiftCocone {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
    (hc : IsColimit c) : IsColimit (liftCocone c f) :=
  isColimitOfReflects (Over.forget _) hc

end CategoryTheory.Over

namespace CategoryTheory.Under

/-
**CategoryTheory.Under.hasLimit_of_hasLimit_comp_forget** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Under`。
形式化陈述：hasLimit_of_hasLimit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forg
et X)] : HasLimit F
参数：F : J ⥤ Under X；F ⋙ forget X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance hasLimit_of_hasLimit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)] :
    HasLimit F :=
  StructuredArrow.hasLimit (i₁ := i)
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Under X) where
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] : HasLimits (Under X) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Under.mono_right_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Under`。
形式化陈述：mono_right_of_mono [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h] :
 Mono h.right
参数：h : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem mono_right_of_mono [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h] : Mono h.right :=
  StructuredArrow.mono_right_of_mono _
/-
**CategoryTheory.Under.mono_iff_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：mono_iff_mono_right [HasPullbacks C] {f g : Under X} (h : f ⟶ g) : Mono h 
↔ Mono h.right
参数：h : f ⟶ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.mono_iff_mono_right`：mono_iff_mono_right 
[HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G] {Y Z : StructuredArrow
 X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.righ…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem mono_iff_mono_right [HasPullbacks C] {f g : Under X} (h : f ⟶ g) : Mono h ↔ Mono h.right :=
  StructuredArrow.mono_iff_mono_right _
/-
**CategoryTheory.Under.createsLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：createsLimitsOfSize : CreatesLimitsOfSize.{w, w'} (forget X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance createsLimitsOfSize : CreatesLimitsOfSize.{w, w'} (forget X) :=
  StructuredArrow.createsLimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects limits.
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasLimits C] : PreservesLimits (forget X) :=
  inferInstance
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ReflectsLimits (forget X) :=
  inferInstance
/-
**CategoryTheory.Under.createLimitsOfSizeMapCompForget** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Under`。
形式化陈述：createLimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) : CreatesLimitsOfSize.
{w, w'} (map f ⋙ forget X)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance createLimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesLimitsOfSize.{w, w'} (map f ⋙ forget X) :=
  show CreatesLimitsOfSize.{w, w'} (forget Y) from inferInstance
/-
**CategoryTheory.Under.preservesLimitsOfSize_map** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Under`。
形式化陈述：preservesLimitsOfSize_map [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) 
: PreservesLimitsOfSize.{w, w'} (map f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves`：preserve
sLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)] [Reflec
tsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w…
· 使用定理 `CategoryTheory.preservesLimits_of_createsLimits_and_hasLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsLimitsOfCreatesLimits`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance preservesLimitsOfSize_map [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesLimitsOfSize.{w, w'} (map f) :=
  preservesLimits_of_reflects_of_preserves (map f) (forget X)

/-- If `c` is a limit cone, then so is the cone `c.toUnder` with cone point `𝟙 c.pt`. -/
/-
**CategoryTheory.Under.isLimitToUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Under`。
形式化陈述：isLimitToUnder {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) : IsLimit c.toUnd
er
参数：hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a limit cone, then so is the cone `c.toUnder` with cone point `𝟙 c.pt`
.
-/
def isLimitToUnder {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) : IsLimit c.toUnder :=
  isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

/-- If `F` has a limit, then the cone `limit.toUnder F` with cone point `𝟙 (limit F)` is
    also a limit cone. -/
/-
**CategoryTheory.Under._root_.CategoryTheory.Limits.limit.isLimitToOver** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a limit, then the cone `limit.toUnder F` with cone point `𝟙 (limit F)
` is
    also a limit cone.
-/
def _root_.CategoryTheory.Limits.limit.isLimitToOver (F : J ⥤ C) [HasLimit F] :
    IsLimit (limit.toUnder F) :=
  Under.isLimitToUnder (limit.isLimit F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given an arrow `X ⟶ c.pt`, the diagram `J ⥤ C` can be lifted to `Under X ⥤ C`, and
the cone `c` also lifts to the diagram on `Under`. -/
/-
**CategoryTheory.Under.liftCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`
。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     {C : Typ
e u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Category
Theory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →            
 {X : C} →               (f : X ⟶ c.pt) →                 CategoryTheory.Limits.
Cone                   (CategoryTheory.Under.lift F                     (Categor
yTheory.CategoryStruct.comp ((CategoryTheory.Functor.const J).map f) c.π))
参数：c : CategoryTheory.Limits.Cone F；f : X ⟶ c.pt；CategoryTheory.Under.lift F    
                 (CategoryTheory.CategoryStruct.comp ((CategoryTheory.Functor.co
nst J).map f) c.π)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an arrow `X ⟶ c.pt`, the diagram `J ⥤ C` can be lifted to `Under X ⥤ C`, a
nd
the cone `c` also lifts to the diagram on `Under`.
-/
@[simps] def liftCone {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    Cone (Under.lift F ((Functor.const J).map f ≫ c.π)) where
  pt := Under.mk f
  π.app j := Under.homMk (c.π.app j)

/-- `Under.liftCone` is limiting if the original cone is. -/
/-
**CategoryTheory.Under.isLimitLiftCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Under`。
形式化陈述：isLimitLiftCone {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt) (hc : IsLi
mit c) : IsLimit (liftCone c f)
参数：c : Cone F；f : X ⟶ c.pt；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Under.liftCone` is limiting if the original cone is.
-/
noncomputable def isLimitLiftCone {F : J ⥤ C} (c : Cone F) {X : C}
    (f : X ⟶ c.pt) (hc : IsLimit c) : IsLimit (liftCone c f) :=
  isLimitOfReflects (Under.forget _) hc

end CategoryTheory.Under

