/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck

/-!
# Colimits on Grothendieck constructions preserving limits

We characterize the condition in which colimits on Grothendieck constructions preserve limits: By
preserving limits on the Grothendieck construction's base category as well as on each of its fibers.
-/

@[expose] public section


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor

namespace Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {H : Type u₂} [Category.{v₂} H]
variable {J : Type u₃} [Category.{v₃} J]
variable {F : C ⥤ Cat.{v₄, u₄}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `colim` on each fiber `F.obj c` of a functor `F : C ⥤ Cat` preserves limits of shape `J`,
then the fiberwise colimit of the limit of a functor `K : J ⥤ Grothendieck F ⥤ H` is naturally
isomorphic to taking the limit of the composition `K ⋙ fiberwiseColim F H`. -/
@[simps!]
/-
**CategoryTheory.Limits.fiberwiseColimitLimitIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：fiberwiseColimitLimitIso (K : J ⥤ Grothendieck F ⥤ H) [forall (c : C), Has
ColimitsOfShape (↑(F.obj c)) H] [HasLimitsOfShape J H] [forall c, PreservesLimit
sOfShape J (colim (J
参数：K : J ⥤ Grothendieck F ⥤ H；c : C；↑(F.obj c)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `colim` on each fiber `F.obj c` of a functor `F : C ⥤ Cat` preserves limits o
f shape `J`,
then the fiberwise colimit of the limit of a functor `K : J ⥤ Grothendieck F ⥤ H
` is naturally
isomorphic to taking the limit of the composition `K ⋙ fiberwiseColim F H`.
-/
def fiberwiseColimitLimitIso (K : J ⥤ Grothendieck F ⥤ H)
    [∀ (c : C), HasColimitsOfShape (↑(F.obj c)) H] [HasLimitsOfShape J H]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    fiberwiseColimit (limit K) ≅ limit (K ⋙ fiberwiseColim F H) :=
  NatIso.ofComponents
    (fun c => HasColimit.isoOfNatIso
       (limitCompWhiskeringLeftIsoCompLimit K (Grothendieck.ι F c)).symm ≪≫
      preservesLimitIso colim _ ≪≫
      HasLimit.isoOfNatIso
        (associator _ _ _ ≪≫
        isoWhiskerLeft _ (fiberwiseColimCompEvaluationIso _).symm ≪≫
        (associator _ _ _).symm) ≪≫
      (limitObjIsoLimitCompEvaluation _ c).symm)
    fun {c₁ c₂} f => by
      simp only [fiberwiseColimit_obj, fiberwiseColimit_map, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, limitObjIsoLimitCompEvaluation_inv_limit_map]
      apply colimit.hom_ext
      intro d
      simp only [← Category.assoc]
      congr 1
      apply limit.hom_ext
      intro e
      simp [← NatTrans.comp_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C) (F) in
/-- If `colim` on a category `C` preserves limits of shape `J` and if it does so for `colim` on
every `F.obj c` for a functor `F : C ⥤ Cat`, then `colim` on `Grothendieck F` also preserves limits
of shape `J`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_colim_grothendieck** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_colim_grothendieck [HasColimitsOfShape C H] [HasLim
itsOfShape J H] [forall c, HasColimitsOfShape (↑(F.obj c)) H] [PreservesLimitsOf
Shape J (colim (J
参数：↑(F.obj c)。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_grothendieck`：hasColimitsOfShap
e_grothendieck [forall X, HasColimitsOfShape (F.obj X) H] [HasColimitsOfShape C 
H] : HasColimitsOfShape (Grothendieck F) H …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用引理 `CategoryTheory.Limits.hasColimit_of_hasColimit_fiberwiseColimit_of_hasCo
limit`：hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit : HasColimit G wh
ere exists_colimit
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.post_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {D : Type u'} [inst_2…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.preservesLimitIso_hom_π_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用引理 `CategoryTheory.Limits.hasColimit_ι_comp`：hasColimit_ι_comp : forall X, H
asColimit (Grothendieck.ι F X ⋙ G)
· 使用定理 `CategoryTheory.Limits.ι_colimitFiberwiseColimitIso_inv_assoc`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C 
CategoryTheory.Cat}   {H : Type u₂} [inst_1 : Cate…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_π_app_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π_assoc`：∀ {J : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Limits.ι_colimitFiberwiseColimitIso_hom`：ι_colimitFiberwi
seColimitIso_hom (X : C) (d : F.obj X) : colimit.ι (Grothendieck.ι F X ⋙ G) d ≫ 
colimit.ι (fiberwiseColimit G) X ≫ (colimitF…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `colim` on a category `C` preserves limits of shape `J` and if it does so for
 `colim` on
every `F.obj c` for a functor `F : C ⥤ Cat`, then `colim` on `Grothendieck F` al
so preserves limits
of shape `J`.
-/
instance preservesLimitsOfShape_colim_grothendieck [HasColimitsOfShape C H] [HasLimitsOfShape J H]
    [∀ c, HasColimitsOfShape (↑(F.obj c)) H] [PreservesLimitsOfShape J (colim (J := C) (C := H))]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    PreservesLimitsOfShape J (colim (J := Grothendieck F) (C := H)) := by
  constructor
  intro K
  let i₂ := calc colimit (limit K)
    _ ≅ colimit (fiberwiseColimit (limit K)) := (colimitFiberwiseColimitIso _).symm
    _ ≅ colimit (limit (K ⋙ fiberwiseColim _ _)) :=
          HasColimit.isoOfNatIso (fiberwiseColimitLimitIso _)
    _ ≅ limit ((K ⋙ fiberwiseColim _ _) ⋙ colim) :=
          preservesLimitIso colim (K ⋙ fiberwiseColim _ _)
    _ ≅ limit (K ⋙ colim) :=
      HasLimit.isoOfNatIso
       (associator _ _ _ ≪≫ isoWhiskerLeft _ fiberwiseColimCompColimIso)
  have : IsIso (limit.post K colim) := by
    convert! Iso.isIso_hom i₂
    ext
    simp only [colim_obj, Functor.comp_obj, limit.post_π, colim_map, Iso.trans_def,
      Iso.trans_assoc, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      fiberwiseColim_obj, isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
      whiskerLeft_app, fiberwiseColimCompColimIso_hom_app, Category.id_comp,
      preservesLimitIso_hom_π_assoc, i₂]
    ext
    simp only [ι_colimMap, Trans.trans, Iso.symm_hom, ι_colimitFiberwiseColimitIso_inv_assoc,
      HasColimit.isoOfNatIso_ι_hom_assoc, fiberwiseColimit_obj, fiberwiseColimitLimitIso_hom_app,
      ι_colimMap_assoc, Category.assoc, limitObjIsoLimitCompEvaluation_inv_π_app_assoc,
      Functor.comp_obj, fiberwiseColim_obj, HasLimit.isoOfNatIso_hom_π_assoc,
      whiskeringLeft_obj_obj, colim_obj, evaluation_obj_obj, Iso.trans_hom, isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      fiberwiseColimCompEvaluationIso_inv_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, preservesLimitIso_hom_π_assoc, colim_map, Grothendieck.ι_obj,
      ι_colimitFiberwiseColimitIso_hom]
    simp [← Category.assoc, ← NatTrans.comp_app]
  apply preservesLimit_of_isIso_post

end

end Limits

end CategoryTheory

