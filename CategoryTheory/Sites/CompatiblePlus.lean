/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Plus

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `CategoryTheory/Sites/CompatibleSheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits Opposite CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type*} [Category* D]
variable {E : Type*} [Category* E]
variable (F : D ⥤ E)
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`. -/
/-
**CategoryTheory.GrothendieckTopology.diagramCompIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`.
-/
def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.diagramCompIso_hom_** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramCompIso_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) :
    (J.diagramCompIso F P X).hom.app W ≫ Multiequalizer.ι ((unop W).index (P ⋙ F)) i =
    F.map (Multiequalizer.ι _ _) := by
  delta diagramCompIso
  simp

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`. -/
/-
**CategoryTheory.GrothendieckTopology.plusCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`.
-/
def plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F) :=
  NatIso.ofComponents
    (fun X => by
      refine ?_ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      refine
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
      apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
      intro W
      dsimp [plusObj, plusMap]
      simp only [Functor.map_comp, Category.assoc]
      slice_rhs 1 2 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).fac]
      slice_lhs 1 3 =>
        simp only [← F.map_comp]
        dsimp [colimMap, IsColimit.map, colimit.pre]
        simp only [colimit.ι_desc_assoc, colimit.ι_desc]
        dsimp [Cocone.precompose]
        simp only [Category.assoc, colimit.ι_desc]
        dsimp [Cocone.whisker]
        rw [F.map_comp]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P Y.unop))).fac]
      dsimp
      simp only [HasColimit.isoOfNatIso_ι_hom_assoc, GrothendieckTopology.diagramPullback_app,
        colimit.ι_pre, HasColimit.isoOfNatIso_ι_hom, ι_colimMap_assoc]
      simp only [← Category.assoc]
      dsimp
      congr 1
      ext
      dsimp
      simp only [Category.assoc]
      rw [Multiequalizer.lift_ι, diagramCompIso_hom_ι, diagramCompIso_hom_ι, ← F.map_comp,
        Multiequalizer.lift_ι])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_plusCompIso_hom (X) (W) :
    F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X =
      (J.diagramCompIso F P X.unop).hom.app W ≫ colimit.ι _ W := by
  delta diagramCompIso plusCompIso
  simp only [Iso.trans_hom, NatIso.ofComponents_hom_app, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.plusCompIso_whiskerLeft** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusCompIso_whiskerLeft {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D) [forall X 
: C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F] [forall (X : C) (W : J.Cover X) (
P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] [forall X : C, Preserves
ColimitsOfShape (J.Cover X)ᵒᵖ G] [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), 
PreservesLimit (W.index P).multicospan G] : whiskerLeft _ η ≫ (J.plusCompIso G P
).hom = (J.plusCompIso F P).hom ≫ J.plusMap (whiskerLeft _ η)
参数：η : F ⟶ G；P : Cᵒᵖ ⥤ D；J.Cover X；X : C；W : J.Cover X；P : Cᵒᵖ ⥤ D；W.index P；J.C
over X；X : C；W : J.Cover X；P : Cᵒᵖ ⥤ D；W.index P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom`：ι_plusCompIso_hom
 (X) (W) : F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X = (J.diagramCom
pIso F P X.unop).hom.app W ≫ colimit.ι _ W
· 使用定理 `CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTo
pology C) {D : Type u_1}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι`：diagramCompIso
_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) : (J.diagramCompIso F P X)
.hom.app W ≫ Multiequalizer.ι ((unop W).index …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendiec
kTopology C) {D : Type u_1}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusCompIso_whiskerLeft {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ G]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan G] :
    whiskerLeft _ η ≫ (J.plusCompIso G P).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerLeft _ η) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc]
  congr 1
  cat_disch

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.GrothendieckTopology.plusFunctorWhiskerLeftIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D) [forall (F : D ⥤ E) (X : C), Prese
rvesColimitsOfShape (J.Cover X)ᵒᵖ F] [forall (F : D ⥤ E) (X : C) (W : J.Cover X)
 (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] : (whiskeringLeft _ _ 
E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E
参数：P : Cᵒᵖ ⥤ D；F : D ⥤ E；X : C；J.Cover X；F : D ⥤ E；X : C；W : J.Cover X；P : Cᵒᵖ ⥤
 D；W.index P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`.
-/
def plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.plusCompIso_whiskerRight** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusCompIso_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : whiskerRight (J.plu
sMap η) F ≫ (J.plusCompIso F Q).hom = (J.plusCompIso F P).hom ≫ J.plusMap (whisk
erRight η F)
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTo
pology C) {D : Type u_1}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom`：ι_plusCompIso_hom
 (X) (W) : F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X = (J.diagramCom
pIso F P X.unop).hom.app W ≫ colimit.ι _ W
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι`：diagramCompIso
_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) : (J.diagramCompIso F P X)
.hom.app W ≫ Multiequalizer.ι ((unop W).index …
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendiec
kTopology C) {D : Type u_1}   [inst_1 : CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusCompIso_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    whiskerRight (J.plusMap η) F ≫ (J.plusCompIso F Q).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerRight η F) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  dsimp [colimMap, IsColimit.map]
  simp only [colimit.ι_desc]
  dsimp [Cocone.precompose]
  simp only [Functor.map_comp, Category.assoc, ι_plusCompIso_hom]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  dsimp
  simp only [diagramCompIso_hom_ι_assoc, Multiequalizer.lift_ι, diagramCompIso_hom_ι,
    Category.assoc]
  simp only [← F.map_comp, Multiequalizer.lift_ι]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.GrothendieckTopology.plusFunctorWhiskerRightIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusFunctorWhiskerRightIso : J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj
 F ≅ (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plusCompIso_whiskerRight`：plusCompIs
o_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : whiskerRight (J.plusMap η) F ≫ (J.p
lusCompIso F Q).hom = (J.plusCompIso F P).hom ≫ J.…

--- 原说明 ---
The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`.
-/
def plusFunctorWhiskerRightIso :
    J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.whiskerRight_toPlus_comp_plusCompIso_hom**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：whiskerRight_toPlus_comp_plusCompIso_hom : whiskerRight (J.toPlus _) _ ≫ (
J.plusCompIso F P).hom = J.toPlus _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom`：ι_plusCompIso_hom
 (X) (W) : F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X = (J.diagramCom
pIso F P X.unop).hom.app W ≫ colimit.ι _ W
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι`：diagramCompIso
_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) : (J.diagramCompIso F P X)
.hom.app W ≫ Multiequalizer.ι ((unop W).index …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_toPlus_comp_plusCompIso_hom :
    whiskerRight (J.toPlus _) _ ≫ (J.plusCompIso F P).hom = J.toPlus _ := by
  ext
  dsimp [toPlus]
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  rw [Category.assoc, diagramCompIso_hom_ι, ← F.map_comp]
  simp only [unop_op, limit.lift_π, Multifork.ofι_π_app, Functor.comp_obj, Functor.comp_map]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.toPlus_comp_plusCompIso_inv** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toPlus_comp_plusCompIso_inv : J.toPlus _ ≫ (J.plusCompIso F P).inv = whisk
erRight (J.toPlus _) _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.whiskerRight_toPlus_comp_plusCompIso
_hom`：whiskerRight_toPlus_comp_plusCompIso_hom : whiskerRight (J.toPlus _) _ ≫ (
J.plusCompIso F P).hom = J.toPlus _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPlus_comp_plusCompIso_inv :
    J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.toPlus _) _ := by simp [Iso.comp_inv_eq]
/-
**CategoryTheory.GrothendieckTopology.plusCompIso_inv_eq_plusLift** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusCompIso_inv_eq_plusLift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) : 
(J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP
参数：hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.plusLift_unique`：plusLift_unique {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q) (hγ :
 J.toPlus P ≫ γ = η) : γ = J.plusLift η h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_comp_plusCompIso_inv`：toPlus_
comp_plusCompIso_inv : J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.to
Plus _) _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusCompIso_inv_eq_plusLift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) :
    (J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP := by
  apply J.plusLift_unique
  simp

end CategoryTheory.GrothendieckTopology

