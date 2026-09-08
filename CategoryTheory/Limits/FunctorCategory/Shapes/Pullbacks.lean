/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks in functor categories

We prove the isomorphism `(pullback f g).obj d ≅ pullback (f.app d) (g.app d)`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

section Pullback

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F G H` and natural transformations `f : F ⟶ H` and `g : g : G ⟶ H`, together
with a collection of limiting pullback cones for each cospan `F X ⟶ H X, G X ⟶ H X`, we can stitch
them together to give a pullback cone for the cospan formed by `f` and `g`.
`combinePullbackConesIsLimit` shows that this pullback cone is limiting. -/
@[simps!]
/-
**CategoryTheory.Limits.PullbackCone.combine** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.PullbackCone`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G H :
 CategoryTheory.Functor D C} →           (f : F ⟶ H) →             (g : G ⟶ H) →
               (c : (X : D) → CategoryTheory.Limits.PullbackCone (f.app X) (g.ap
p X)) →                 ((X : D) → CategoryTheory.Limits.IsLimit (c X)) → Catego
ryTheory.Limits.PullbackCone f g
参数：f : F ⟶ H；g : G ⟶ H；c : (X : D) → CategoryTheory.Limits.PullbackCone (f.app X
) (g.app X)；(X : D) → CategoryTheory.Limits.IsLimit (c X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functors `F G H` and natural transformations `f : F ⟶ H` and `g : g : G ⟶ 
H`, together
with a collection of limiting pullback cones for each cospan `F X ⟶ H X, G X ⟶ H
 X`, we can stitch
them together to give a pullback cone for the cospan formed by `f` and `g`.
`combinePullbackConesIsLimit` shows that this pullback cone is limiting.
-/
def PullbackCone.combine (f : F ⟶ H) (g : G ⟶ H) (c : ∀ X, PullbackCone (f.app X) (g.app X))
    (hc : ∀ X, IsLimit (c X)) : PullbackCone f g :=
  PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
    map_id _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp
    map_comp _ _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The pullback cone `combinePullbackCones` is limiting.
-/
/-
**CategoryTheory.Limits.PullbackCone.combineIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PullbackCone`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G H :
 CategoryTheory.Functor D C} →           (f : F ⟶ H) →             (g : G ⟶ H) →
               (c : (X : D) → CategoryTheory.Limits.PullbackCone (f.app X) (g.ap
p X)) →                 (hc : (X : D) → CategoryTheory.Limits.IsLimit (c X)) →  
                 CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.PullbackCo
ne.combine f g c hc)
参数：f : F ⟶ H；g : G ⟶ H；c : (X : D) → CategoryTheory.Limits.PullbackCone (f.app X
) (g.app X)；hc : (X : D) → CategoryTheory.Limits.IsLimit (c X)；CategoryTheory.Li
mits.PullbackCone.combine f g c hc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone `combinePullbackCones` is limiting.
-/
def PullbackCone.combineIsLimit (f : F ⟶ H) (g : G ⟶ H)
    (c : ∀ X, PullbackCone (f.app X) (g.app X)) (hc : ∀ X, IsLimit (c X)) :
    IsLimit (combine f g c hc) :=
  evaluationJointlyReflectsLimits _ fun k ↦ by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

variable [HasPullbacks C]

/-- Evaluating a pullback amounts to taking the pullback of the evaluations. -/
/-
**CategoryTheory.Limits.pullbackObjIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：pullbackObjIso (f : F ⟶ H) (g : G ⟶ H) (d : D) : (pullback f g).obj d ≅ pu
llback (f.app d) (g.app d)
参数：f : F ⟶ H；g : G ⟶ H；d : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluating a pullback amounts to taking the pullback of the evaluations.
-/
noncomputable def pullbackObjIso (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullback f g).obj d ≅ pullback (f.app d) (g.app d) :=
  limitObjIsoLimitCompEvaluation (cospan f g) d ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackObjIso_hom_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackObjIso_hom_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) : (pullbackObj
Iso f g d).hom ≫ pullback.fst (f.app d) (g.app d) = (pullback.fst f g).app d
参数：f : F ⟶ H；g : G ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.diagramIsoCospan_hom_app`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor CategoryTheory.Li
mits.WalkingCospan C) (X : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_π`：limitObjIsoL
imitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) 
: (limitObjIsoLimitCompEvaluation F k).hom ≫ lim…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackObjIso_hom_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.fst (f.app d) (g.app d) = (pullback.fst f g).app d := by
  simp [pullbackObjIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackObjIso_hom_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackObjIso_hom_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) : (pullbackObj
Iso f g d).hom ≫ pullback.snd (f.app d) (g.app d) = (pullback.snd f g).app d
参数：f : F ⟶ H；g : G ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.diagramIsoCospan_hom_app`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor CategoryTheory.Li
mits.WalkingCospan C) (X : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_π`：limitObjIsoL
imitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) 
: (limitObjIsoLimitCompEvaluation F k).hom ≫ lim…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackObjIso_hom_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.snd (f.app d) (g.app d) = (pullback.snd f g).app d := by
  simp [pullbackObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackObjIso_inv_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackObjIso_inv_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) : (pullbackObj
Iso f g d).inv ≫ (pullback.fst f g).app d = pullback.fst (f.app d) (g.app d)
参数：f : F ⟶ H；g : G ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_π_app`：limitObj
IsoLimitCompEvaluation_inv_π_app [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) 
(k : K) : (limitObjIsoLimitCompEvaluation F k).inv ≫…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_inv_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackObjIso_inv_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.fst f g).app d = pullback.fst (f.app d) (g.app d) := by
  simp [pullbackObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackObjIso_inv_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackObjIso_inv_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) : (pullbackObj
Iso f g d).inv ≫ (pullback.snd f g).app d = pullback.snd (f.app d) (g.app d)
参数：f : F ⟶ H；g : G ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_π_app`：limitObj
IsoLimitCompEvaluation_inv_π_app [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) 
(k : K) : (limitObjIsoLimitCompEvaluation F k).inv ≫…
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_inv_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackObjIso_inv_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.snd f g).app d = pullback.snd (f.app d) (g.app d) := by
  simp [pullbackObjIso]

end Pullback

section Pushout

variable [HasPushouts C]

/-- Evaluating a pushout amounts to taking the pushout of the evaluations. -/
/-
**CategoryTheory.Limits.pushoutObjIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：pushoutObjIso (f : F ⟶ G) (g : F ⟶ H) (d : D) : (pushout f g).obj d ≅ push
out (f.app d) (g.app d)
参数：f : F ⟶ G；g : F ⟶ H；d : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluating a pushout amounts to taking the pushout of the evaluations.
-/
noncomputable def pushoutObjIso (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout f g).obj d ≅ pushout (f.app d) (g.app d) :=
  colimitObjIsoColimitCompEvaluation (span f g) d ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_comp_pushoutObjIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inl_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) : (pushout.inl 
f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inl (f.app d) (g.app d)
参数：f : F ⟶ G；g : F ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1
 : CategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.diagramIsoSpan_hom_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor CategoryTheory.Limi
ts.WalkingSpan C) (X : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inl f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inl (f.app d) (g.app d) := by
  simp [pushoutObjIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_comp_pushoutObjIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inr_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) : (pushout.inr 
f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inr (f.app d) (g.app d)
参数：f : F ⟶ G；g : F ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1
 : CategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.diagramIsoSpan_hom_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor CategoryTheory.Limi
ts.WalkingSpan C) (X : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inr f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inr (f.app d) (g.app d) := by
  simp [pushoutObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_comp_pushoutObjIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inl_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) : pushout.inl (
f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inl f g).app d
参数：f : F ⟶ G；g : F ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv`：colimitO
bjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J
) (k : K) : colimit.ι (F ⋙ (evaluation K C).obj k) j…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inl (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inl f g).app d := by
  simp [pushoutObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_comp_pushoutObjIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inr_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) : pushout.inr (
f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inr f g).app d
参数：f : F ⟶ G；g : F ⟶ H；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv`：colimitO
bjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J
) (k : K) : colimit.ι (F ⋙ (evaluation K C).obj k) j…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inr (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inr f g).app d := by
  simp [pushoutObjIso]

end Pushout

end CategoryTheory.Limits

