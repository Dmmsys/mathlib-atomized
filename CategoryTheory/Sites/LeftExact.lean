/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Left exactness of sheafification

In this file we show that sheafification commutes with finite limits.
-/

@[expose] public section


open CategoryTheory Limits Opposite

universe s t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {D : Type w} [Category.{t} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.coneCompEvaluationOfConeCompDiagramFunctor
CompEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type
 s} [SmallCategory K] {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.Cover X} (i : W.Arrow) (E : Cone 
(F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj (op W))) : Cone (F 
⋙ (evaluation _ _).obj (op i.Y)) where pt
参数：i : W.Arrow；E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D)
.obj (op W))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits.
-/
def coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type s}
    [SmallCategory K] {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.Cover X} (i : W.Arrow)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj (op W))) :
    Cone (F ⋙ (evaluation _ _).obj (op i.Y)) where
  pt := E.pt
  π :=
    { app := fun k => E.π.app k ≫ Multiequalizer.ι (W.index (F.obj k)) i
      naturality := by
        intro a b f
        dsimp
        rw [Category.id_comp, Category.assoc, ← E.w f]
        dsimp [diagramNatTrans]
        simp only [Multiequalizer.lift_ι, Category.assoc] }

/-- Auxiliary definition for `liftToDiagramLimitObj`. -/
/-
**CategoryTheory.GrothendieckTopology.liftToDiagramLimitObjAux** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：liftToDiagramLimitObjAux {X : C} {K : Type s} [SmallCategory K] [HasLimits
OfShape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D) (E : Cone (F ⋙ J.diagramFunct
or D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) (i : (unop W).Arrow) : E.pt ⟶ (lim
it F).obj (op i.Y)
参数：J.Cover X；F : K ⥤ Cᵒᵖ ⥤ D；E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J
.Cover X)ᵒᵖ D).obj W)；i : (unop W).Arrow。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `liftToDiagramLimitObj`.
-/
def liftToDiagramLimitObjAux {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) :
    E.pt ⟶ (limit F).obj (op i.Y) :=
  (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.liftToDiagramLimitObjAux_fac** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：liftToDiagramLimitObjAux_fac {X : C} {K : Type s} [SmallCategory K] [HasLi
mitsOfShape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D) (E : Cone (F ⋙ J.diagramF
unctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) (i : (unop W).Arrow) (k : K) :
 liftToDiagramLimitObjAux F E i ≫ (limit.π F k).app (op i.Y) = E.π.app k ≫ Multi
equalizer.ι ((unop W).index (F.obj k)) i
参数：J.Cover X；F : K ⥤ Cᵒᵖ ⥤ D；E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J
.Cover X)ᵒᵖ D).obj W)；i : (unop W).Arrow；k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma liftToDiagramLimitObjAux_fac {X : C} {K : Type s} [SmallCategory K]
    [HasLimitsOfShape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) (k : K) :
    liftToDiagramLimitObjAux F E i ≫ (limit.π F k).app (op i.Y) = E.π.app k ≫
      Multiequalizer.ι ((unop W).index (F.obj k)) i :=
  IsLimit.fac _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
/-
**CategoryTheory.GrothendieckTopology.liftToDiagramLimitObj** 是 Mathlib 中的一个缩写定义
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：liftToDiagramLimitObj {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfS
hape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D) (E : Cone (F ⋙ J.diagramFunctor 
D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) : E.pt ⟶ (J.diagram (limit F) X).obj 
W
参数：J.Cover X；F : K ⥤ Cᵒᵖ ⥤ D；E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J
.Cover X)ᵒᵖ D).obj W)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits.
-/
abbrev liftToDiagramLimitObj {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) :
    E.pt ⟶ (J.diagram (limit F) X).obj W :=
  Multiequalizer.lift ((unop W).index (limit F)) E.pt (liftToDiagramLimitObjAux F E)
    (by
      intro i
      dsimp
      ext k
      simp only [Category.assoc, NatTrans.naturality, liftToDiagramLimitObjAux_fac_assoc]
      erw [Multiequalizer.condition]
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.preservesLimit_diagramFunctor** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimit_diagramFunctor (X : C) (K : Type s) [SmallCategory K] [HasL
imitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) : PreservesLimit F (J.diagramFunctor D X)
参数：X : C；K : Type s；F : K ⥤ Cᵒᵖ ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_evaluation`：preservesLimit_of_ev
aluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k : K, PreservesLimit G (F ⋙ (e
valuation K C).obj k : D ⥤ C)) : Preserv…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}
   (I : CategoryTheory.Limits.Multicosp…
· 使用引理 `CategoryTheory.GrothendieckTopology.liftToDiagramLimitObjAux_fac`：liftTo
DiagramLimitObjAux_fac {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape 
K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D) (E : Cone (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.limit_obj_ext`：limit_obj_ext {H : J ⥤ K ⥤ C} [HasL
imitsOfShape J C] {k : K} {W : C} {f g : W ⟶ (limit H).obj k} (w : forall j, f ≫
 (Limits.limit.π H j).app…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
instance preservesLimit_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimit_of_evaluation _ _ fun W =>
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{_, t, w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine Multiequalizer.hom_ext _ _ _ (fun a => ?_)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc,
            liftToDiagramLimitObjAux_fac]
        uniq := by
          intro E m hm
          refine Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => ?_))
          dsimp [liftToDiagramLimitObj]
          rw [Multiequalizer.lift_ι, Category.assoc, liftToDiagramLimitObjAux_fac, ← hm,
            Category.assoc]
          dsimp
          rw [limit.lift_π]
          dsimp }
/-
**CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_diagramFunctor** 是 
Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimitsOfShape_diagramFunctor (X : C) (K : Type s) [SmallCategory 
K] [HasLimitsOfShape K D] : PreservesLimitsOfShape K (J.diagramFunctor D X)
参数：X : C；K : Type s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesLimitsOfShape_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨by apply preservesLimit_diagramFunctor.{s, t, w, v, u}⟩
/-
**CategoryTheory.GrothendieckTopology.preservesLimits_diagramFunctor** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimits_diagramFunctor (X : C) [HasLimitsOfSize.{max t u v, max t 
u v} D] : PreservesLimits (J.diagramFunctor D X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance preservesLimits_diagramFunctor (X : C) [HasLimitsOfSize.{max t u v, max t u v} D] :
    PreservesLimits (J.diagramFunctor D X) := by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{max t u v}

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ]

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof that `J.plusFunctor D` commutes
with finite limits. -/
/-
**CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：liftToPlusObjLimitObj {K : Type s} [SmallCategory K] [FinCategory K] [HasL
imitsOfShape K D] [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K
 (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C) (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluat
ion Cᵒᵖ D).obj (op X))) : S.pt ⟶ (J.plusObj (limit F)).obj (op X)
参数：forget D；forget D；F : K ⥤ Cᵒᵖ ⥤ D；X : C；S : Cone (F ⋙ J.plusFunctor D ⋙ (eval
uation Cᵒᵖ D).obj (op X))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition to be used in the proof that `J.plusFunctor D` commutes
with finite limits.
-/
def liftToPlusObjLimitObj {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.pt ⟶ (J.plusObj (limit F)).obj (op X) :=
  let F' := F ⋙ J.diagramFunctor D X
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plusFunctor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
/-
**CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj_fac** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：liftToPlusObjLimitObj_fac {K : Type s} [SmallCategory K] [FinCategory K] [
HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfSha
pe K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C) (S : Cone (F ⋙ J.plusFunctor D ⋙ (eva
luation Cᵒᵖ D).obj (op X))) (k) : liftToPlusObjLimitObj F X S ≫ (J.plusMap (limi
t.π F k)).app (op X) = S.π.app k
参数：forget D；forget D；F : K ⥤ Cᵒᵖ ⥤ D；X : C；S : Cone (F ⋙ J.plusFunctor D ⋙ (eval
uation Cᵒᵖ D).obj (op X))；k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.ι_colimitLimitIso_limit_π_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.C
ategory.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem liftToPlusObjLimitObj_fac {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc, Category.assoc, ← Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π, Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_plusFunctor** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimitsOfShape_plusFunctor (K : Type t) [SmallCategory K] [FinCate
gory K] [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)] [ReflectsLi
mitsOfShape K (forget D)] : PreservesLimitsOfShape K (J.plusFunctor D)
参数：K : Type t；forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_evaluation`：preservesLimit_of_ev
aluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k : K, PreservesLimit G (F ⋙ (e
valuation K C).obj k : D ⥤ C)) : Preserv…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj_fac`：liftToPlu
sObjLimitObj_fac {K : Type s} [SmallCategory K] [FinCategory K] [HasLimitsOfShap
e K D] [PreservesLimitsOfShape K (forget D)] [Refle…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.colimit.ι_map`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimitLimitIso_limit_π_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.C
ategory.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_app_hom`：coli
mitObjIsoColimitCompEvaluation_ι_app_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C
) (j : J) (k : K) : (colimit.ι F j).app k ≫ (colimitObjI…
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
-/
instance preservesLimitsOfShape_plusFunctor
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc, ← NatTrans.comp_app, limit.lift_π]
    rfl
/-
**CategoryTheory.GrothendieckTopology.preserveFiniteLimits_plusFunctor** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preserveFiniteLimits_plusFunctor [HasFiniteLimits D] [PreservesFiniteLimit
s (forget D)] [(forget D).ReflectsIsomorphisms] : PreservesFiniteLimits (J.plusF
unctor D)
参数：forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance preserveFiniteLimits_plusFunctor
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply preservesLimitsOfShape_plusFunctor
/-
**CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_sheafification** 是 
Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimitsOfShape_sheafification (K : Type t) [SmallCategory K] [FinC
ategory K] [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)] [Reflect
sLimitsOfShape K (forget D)] : PreservesLimitsOfShape K (J.sheafification D)
参数：K : Type t；forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance preservesLimitsOfShape_sheafification
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.comp_preservesLimitsOfShape _ _
/-
**CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification** 是 M
athlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesFiniteLimits_sheafification [HasFiniteLimits D] [PreservesFiniteL
imits (forget D)] [(forget D).ReflectsIsomorphisms] : PreservesFiniteLimits (J.s
heafification D)
参数：forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
-/
instance preservesFiniteLimits_sheafification
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.comp_preservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

section

variable {D : Type w} [Category.{t} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable {FD : D → D → Type*} {CD : D → Type t}
variable [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [(forget D).ReflectsIsomorphisms]
variable [∀ {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable (K : Type w')
variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

/-
**CategoryTheory.preservesLimitsOfShape_presheafToSheaf** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory`。
形式化陈述：preservesLimitsOfShape_presheafToSheaf [PreservesLimits (forget D)] [foral
l X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] : PreservesLimitsOfShape K (plusPlusS
heaf J D)
参数：forget D；J.Cover X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance preservesLimitsOfShape_presheafToSheaf
    [PreservesLimits (forget D)] [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    PreservesLimitsOfShape K (plusPlusSheaf J D) := by
  let e := (FinCategory.equivAsType K).symm.trans (AsSmall.equiv.{0, 0, t})
  have : HasLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) D :=
    Limits.hasLimitsOfShape_of_equivalence e
  have : FinCategory (AsSmall.{t} (FinCategory.AsType K)) := by
    constructor
    · change Fintype (ULift _)
      infer_instance
    · intro j j'
      change Fintype (ULift _)
      infer_instance
  refine @preservesLimitsOfShape_of_equiv _ _ _ _ _ _ _ _ e.symm _ (show _ from ?_)
  constructor; intro F; constructor; intro S hS; constructor
  apply isLimitOfReflects (sheafToPresheaf J D)
  have : ReflectsLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) (forget D) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS
/-
**CategoryTheory.preservesFiniteLimits_presheafToSheaf** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory`。
形式化陈述：preservesFiniteLimits_presheafToSheaf [PreservesLimits (forget D)] [forall
 X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] [HasFiniteLimits D] : PreservesFiniteL
imits (plusPlusSheaf J D)
参数：forget D；J.Cover X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance preservesFiniteLimits_presheafToSheaf [PreservesLimits (forget D)]
    [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] [HasFiniteLimits D] :
    PreservesFiniteLimits (plusPlusSheaf J D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intros
  infer_instance

variable (J D)

/-- `plusPlusSheaf` is isomorphic to an arbitrary choice of left adjoint. -/
/-
**CategoryTheory.plusPlusSheafIsoPresheafToSheaf** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：plusPlusSheafIsoPresheafToSheaf : plusPlusSheaf J D ≅ presheafToSheaf J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`plusPlusSheaf` is isomorphic to an arbitrary choice of left adjoint.
-/
def plusPlusSheafIsoPresheafToSheaf : plusPlusSheaf J D ≅ presheafToSheaf J D :=
  (plusPlusAdjunction J D).leftAdjointUniq (sheafificationAdjunction J D)

/-- `plusPlusFunctor` is isomorphic to `sheafification`. -/
/-
**CategoryTheory.plusPlusFunctorIsoSheafification** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：plusPlusFunctorIsoSheafification : J.sheafification D ≅ sheafification J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`plusPlusFunctor` is isomorphic to `sheafification`.
-/
def plusPlusFunctorIsoSheafification : J.sheafification D ≅ sheafification J D :=
  Functor.isoWhiskerRight (plusPlusSheafIsoPresheafToSheaf J D) (sheafToPresheaf J D)

/-- `plusPlus` is isomorphic to `sheafify`. -/
/-
**CategoryTheory.plusPlusIsoSheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：plusPlusIsoSheafify (P : Cᵒᵖ ⥤ D) : J.sheafify P ≅ sheafify J P
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`plusPlus` is isomorphic to `sheafify`.
-/
def plusPlusIsoSheafify (P : Cᵒᵖ ⥤ D) : J.sheafify P ≅ sheafify J P :=
  (sheafToPresheaf J D).mapIso ((plusPlusSheafIsoPresheafToSheaf J D).app P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.toSheafify_plusPlusIsoSheafify_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：toSheafify_plusPlusIsoSheafify_hom (P : Cᵒᵖ ⥤ D) : J.toSheafify P ≫ (plusP
lusIsoSheafify J D P).hom = toSheafify J P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`：unit_leftAdjoint
Uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
 adj1.unit.app x ≫ G.map ((leftAdjointUniq a…
-/
lemma toSheafify_plusPlusIsoSheafify_hom (P : Cᵒᵖ ⥤ D) :
    J.toSheafify P ≫ (plusPlusIsoSheafify J D P).hom = toSheafify J P := by
  convert!
    Adjunction.unit_leftAdjointUniq_hom_app (plusPlusAdjunction J D) (sheafificationAdjunction J D)
      P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimits (forget D)] [HasFiniteLimits D]
    [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    HasSheafify J D :=
  HasSheafify.mk' J D (plusPlusAdjunction J D)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSheafify J (Type (max u v)) := by
  infer_instance

end

variable {D : Type w} [Category.{w'} D]

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FinitaryExtensive D] [HasPullbacks D] [HasSheafify J D] :
    FinitaryExtensive (Sheaf J D) :=
  finitaryExtensive_of_reflective (sheafificationAdjunction _ _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Adhesive D] [HasPullbacks D] [HasPushouts D] [HasSheafify J D] :
    Adhesive (Sheaf J D) :=
  adhesive_of_reflective (sheafificationAdjunction _ _)
/-
**CategoryTheory.SheafOfTypes.finitary_extensive** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.SheafOfTypes`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   [CategoryTheory.HasSheafify J (Type w)], CategoryTh
eory.FinitaryExtensive (CategoryTheory.Sheaf J (Type w))
参数：Type w；CategoryTheory.Sheaf J (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instFinitaryExtensiveSheafOfHasPullbacksOfHasSheafify`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Groth
endieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.types.finitaryExtensive`：CategoryTheory.FinitaryExtensive
 (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
-/
instance SheafOfTypes.finitary_extensive [HasSheafify J (Type w)] :
    FinitaryExtensive (Sheaf J (Type w)) :=
  inferInstance
/-
**CategoryTheory.SheafOfTypes.adhesive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.SheafOfTypes`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   [CategoryTheory.HasSheafify J (Type w)], CategoryTh
eory.Adhesive (CategoryTheory.Sheaf J (Type w))
参数：Type w；CategoryTheory.Sheaf J (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instAdhesiveSheafOfHasPullbacksOfHasPushoutsOfHasSheafify
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.G
rothendieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Type.adhesive`：CategoryTheory.Adhesive (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
-/
instance SheafOfTypes.adhesive [HasSheafify J (Type w)] :
    Adhesive (Sheaf J (Type w)) :=
  inferInstance
/-
**CategoryTheory.SheafOfTypes.balanced** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.SheafOfTypes`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   [CategoryTheory.HasSheafify J (Type w)], CategoryTh
eory.Balanced (CategoryTheory.Sheaf J (Type w))
参数：Type w；CategoryTheory.Sheaf J (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.Adhesive.toRegularMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.Adhesive C],   CategoryTheory.Is
RegularMonoCategory C
· 使用定理 `CategoryTheory.SheafOfTypes.adhesive`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
-/
instance SheafOfTypes.balanced [HasSheafify J (Type w)] :
    Balanced (Sheaf J (Type w)) :=
  inferInstance

end CategoryTheory

