/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `TopCat` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheafed spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/

@[expose] public section


noncomputable section

universe v' u' v u

open CategoryTheory Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  TopCat TopCat.Presheaf TopologicalSpace

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eqToHom_map

-- We could enable the following attribute:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.map_id_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.PresheafedSpace`。
形式化陈述：map_id_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U) : (F.map (𝟙 j))
.c.app U = (Pushforward.id (F.obj j).presheaf).inv.app U ≫ (pushforwardEq (by si
mp) (F.obj j).presheaf).hom.app U
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；j；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `AlgebraicGeometry.PresheafedSpace.id_c_app`：id_c_app (X : PresheafedSpac
e C) (U) : (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U)
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `TopCat.Presheaf.pushforwardEq_hom_app`：pushforwardEq_hom_app {X Y : TopC
at.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) : (pushforwardEq h ℱ).h
om.app U = ℱ.map (eqToHom (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U) :
    (F.map (𝟙 j)).c.app U =
      (Pushforward.id (F.obj j).presheaf).inv.app U ≫
        (pushforwardEq (by simp) (F.obj j).presheaf).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_id j)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.map_comp_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.PresheafedSpace`。
形式化陈述：map_comp_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃} (f : j₁ ⟶ 
j₂) (g : j₂ ⟶ j₃) (U) : (F.map (f ≫ g)).c.app U = (F.map g).c.app U ≫ ((pushforw
ard C (F.map g).base).map (F.map f).c).app U ≫ (pushforwardEq (congr_arg Hom.bas
e (F.map_comp f g).symm) _).hom.app U
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；f : j₁ ⟶ j₂；g : j₂ ⟶ j₃；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.pushforwardEq_hom_app`：pushforwardEq_hom_app {X Y : TopC
at.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) : (pushforwardEq h ℱ).h
om.app U = ℱ.map (eqToHom (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app U =
      (F.map g).c.app U ≫
        ((pushforward C (F.map g).base).map (F.map f).c).app U ≫
          (pushforwardEq (congr_arg Hom.base (F.map_comp f g).symm) _).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_comp f g)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.componentwiseDiagram** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：componentwiseDiagram (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F] 
(U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C where obj j
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；U : Opens (Limits.colimit F).carrier。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the 
sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the unde
rlying spaces.
-/
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C where
  obj j := (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
  map_comp {i j k} f g := by
    simp only [assoc, CategoryTheory.NatTrans.naturality_assoc]
    simp

variable [HasColimitsOfShape J TopCat.{v}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(Presheaf C X)ᵒᵖ`.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : J ⥤ (P
resheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where obj j
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topo
logical spaces,
obtaining a diagram in `(Presheaf C X)ᵒᵖ`.
-/
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where
  obj j := op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).presheaf)
  map {j j'} f :=
    ((pushforward C (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).map (F.map f).c ≫
      (Pushforward.comp ((F ⋙ PresheafedSpace.forget C).map f)
        (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.obj j).presheaf).inv ≫
      (pushforwardEq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).presheaf).hom).op
  map_id j := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    induction U with
    | op U =>
      simp [opEquiv]
      rfl
  map_comp {j₁ j₂ j₃} f g := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    dsimp [opEquiv]
    have :
      op ((Opens.map (F.map g).base).obj
          ((Opens.map (colimit.ι (F ⋙ forget C) j₃)).obj U.unop)) =
        op ((Opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U)) := by
      apply unop_injective
      rw [← Opens.map_comp_obj]
      congr
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g
    simp only [map_comp_c_app, pushforward_obj_obj, pushforward_map_app, comp_base,
      pushforwardEq_hom_app, op_obj, Opens.map_comp_obj, id_comp, assoc, eqToHom_map_comp,
      NatTrans.naturality_assoc, pushforward_obj_map, eqToHom_unop]
    simp [NatTrans.congr (α := (F.map f).c) this]

variable [∀ X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
/-
**AlgebraicGeometry.PresheafedSpace.colimit** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.PresheafedSpace`。
形式化陈述：colimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : PresheafedSpace C where ca
rrier
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : PresheafedSpace C where
  carrier := Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.colimit_carrier** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.PresheafedSpace`。
形式化陈述：colimit_carrier (F : J ⥤ PresheafedSpace.{_, _, v} C) : (colimit F).carrie
r = Limits.colimit (F ⋙ PresheafedSpace.forget C)
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.colimit_presheaf** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.PresheafedSpace`。
形式化陈述：colimit_presheaf (F : J ⥤ PresheafedSpace.{_, _, v} C) : (colimit F).presh
eaf = limit (pushforwardDiagramToColimit F).leftOp
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.PresheafedSpace`。
形式化陈述：colimitCocone (F : J ⥤ PresheafedSpace.{_, _, v} C) : Cocone F where pt
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimitCocone (F : J ⥤ PresheafedSpace.{_, _, v} C) : Cocone F where
  pt := colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
        · ext ⟨⟩
          simp [← congr_arg NatTrans.app (limit.w (pushforwardDiagramToColimit F).leftOp f.op)] }

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
/-
**AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descCApp** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit`。
形式化陈述：descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens 
s.pt.carrier)ᵒᵖ) : s.pt.presheaf.obj U ⟶ (colimit.desc (F ⋙ PresheafedSpace.forg
et C) ((PresheafedSpace.forget C).mapCocone s) _* limit (pushforwardDiagramToCol
imit F).leftOp).obj U
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；s : Cocone F；U : (Opens s.pt.carrier)ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColim
it`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ) :
    s.pt.presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U := by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eqToHom ?_)
    dsimp
    rw [← Opens.map_comp_obj]
    simp
  · dsimp
    rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    have w :=
      Functor.congr_obj
        (congr_arg Opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [Opens.map_comp_obj_unop] at w
    replace w := congr_arg op w
    have w' := NatTrans.congr (F.map f.unop).c w
    rw [w']
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturality** 是
 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit
`。
形式化陈述：desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) {U 
V : (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) : s.pt.presheaf.map i ≫ descCApp F s V =
 descCApp F s U ≫ (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (coli
mitCocone F).pt.presheaf).map i
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；s : Cocone F；Opens s.pt.carrier；i : U ⟶ V
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.limit_obj_ext`：limit_obj_ext {H : J ⥤ K ⥤ C} [HasL
imitsOfShape J C] {k : K} {W : C} {f g : W ⟶ (limit H).obj k} (w : forall j, f ≫
 (Limits.limit.π H j).app…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_π_app_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
    {U V : (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) :
    s.pt.presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫
        (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimitCocone F).pt.presheaf).map
          i := by
  dsimp [descCApp]
  refine limit_obj_ext (fun j => ?_)
  have w := Functor.congr_hom (congr_arg Opens.map
    (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j))) i.unop
  simp only [Opens.map_comp_map] at w
  simp [congr_arg Quiver.Hom.op w]

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
/-
**AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit`。
形式化陈述：desc (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) : colimit F ⟶ s.
pt where base
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；s : Cocone F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturali
ty`：desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) {U V 
: (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) : s.pt.presheaf.map i ≫ de…

--- 原说明 ---
Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColim
it`.
-/
def desc (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) : colimit F ⟶ s.pt where
  base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_fac** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit`。
形式化陈述：desc_fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) : (c
olimitCocone F).ι.app j ≫ desc F s = s.ι.app j
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；s : Cocone F；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ext`：ext {X Y : PresheafedSpace C} (α 
β : X ⟶ Y) (w : α.base = β.base) (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _
 = β.c) : α = β
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturali
ty`：desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) {U V 
: (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) : s.pt.presheaf.map i ≫ de…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_π_app_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem desc_fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the original proof is just
  -- `ext <;> dsimp [desc, descCApp] <;> simpa`,
  -- but this has to be expanded a bit
  ext U
  · simp [desc]
  · simp only [op_obj, desc, descCApp, Presheaf.comp_app, comp_c_app, colimitCocone_ι_app_c, assoc]
    rw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc]
    simp

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
/-
**AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : IsColimit (
colimitCocone F) where desc s
参数：F : J ⥤ PresheafedSpace.{_, _, v} C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_fac`：desc_
fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) : (colimitCocon
e F).ι.app j ≫ desc F s = s.ι.app j

--- 原说明 ---
Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    IsColimit (colimitCocone F) where
  desc s := desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      dsimp
      -- `colimit.hom_ext` used to be automatically applied by `ext` before https://github.com/leanprover-community/mathlib4/pull/21302
      apply colimit.hom_ext fun j => ?_
      ext
      rw [colimit.ι_desc, mapCocone_ι_app, ← w j]
      simp
    ext : 1
    · exact t
    · refine NatTrans.ext (funext fun U => limit_obj_ext fun j => ?_)
      simp [desc, descCApp,
        PresheafedSpace.congr_app (w (unop j)).symm U,
        NatTrans.congr (limit.π (pushforwardDiagramToColimit F).leftOp j)
        (congr_arg op (Functor.congr_obj (congr_arg Opens.map t) (unop U)))]
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimitsOfShape J (PresheafedSpace.{_, _, v} C) where
  has_colimit F := ⟨colimitCocone F, colimitCoconeIsColimit F⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfShape J (PresheafedSpace.forget.{v, u, v} C) :=
  ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F) <| by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    fapply Cocone.ext
    · rfl
    · simp⟩

/-- When `C` has limits, the category of presheafed spaces with values in `C` itself has colimits.
-/
/-
**AlgebraicGeometry.PresheafedSpace.instHasColimits** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.PresheafedSpace`。
形式化陈述：instHasColimits [HasLimits C] : HasColimits (PresheafedSpace.{_, _, v} C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
When `C` has limits, the category of presheafed spaces with values in `C` itself
 has colimits.
-/
instance instHasColimits [HasLimits C] : HasColimits (PresheafedSpace.{_, _, v} C) :=
  ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

/-- The underlying topological space of a colimit of presheafed spaces is
the colimit of the underlying topological spaces.
-/
/-
**AlgebraicGeometry.PresheafedSpace.forget_preservesColimits** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：forget_preservesColimits [HasLimits C] : PreservesColimits (PresheafedSpac
e.forget.{_, _, v} C) where preservesColimitsOfShape {J 𝒥}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`：∀ {J : Type u'
} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instPreservesColimitsOfShapeTopCatForg
et`：∀ {J : Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [in
st_1 : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limit…

--- 原说明 ---
The underlying topological space of a colimit of presheafed spaces is
the colimit of the underlying topological spaces.
-/
instance forget_preservesColimits [HasLimits C] :
    PreservesColimits (PresheafedSpace.forget.{_, _, v} C) where
  preservesColimitsOfShape {J 𝒥} :=
    { preservesColimit := fun {F} => preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit F)
          (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _))) }

set_option backward.isDefEq.respectTransparency false in
/-- The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
/-
**AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit** 是 
Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{_, _, v}
 C) [HasColimit F] (U : Opens (Limits.colimit F).carrier) : (Limits.colimit F).p
resheaf.obj (op U) ≅ limit (componentwiseDiagram F U)
参数：F : J ⥤ PresheafedSpace.{_, _, v} C；U : Opens (Limits.colimit F).carrier。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) :
    (Limits.colimit F).presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) := by
  refine
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      ?_
  refine (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso ?_)
  fapply NatIso.ofComponents
  · intro X
    refine (F.obj (unop X)).presheaf.mapIso (eqToIso ?_)
    simp only [Functor.op_obj, op_inj_iff, Opens.map_coe, SetLike.ext'_iff,
      Set.preimage_preimage]
    refine congr_arg (Set.preimage · U.1) (funext fun x => ?_)
    simp only [colimitCocone, colimit, ← TopCat.comp_app]
    congr
    exact ι_preservesColimitIso_inv (forget C) F (unop X)
  · intro X Y f
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).presheaf.map _ = _ ≫ _
    rw [TopCat.Presheaf.Pushforward.comp_inv_app]
    erw [Category.id_comp]
    rw [Category.assoc]
    erw [← (F.obj (unop Y)).presheaf.map_comp, (F.map f.unop).c.naturality_assoc,
      ← (F.obj (unop Y)).presheaf.map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_inv_
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) =
      limit.π _ (op j) := by
  delta colimitPresheafObjIsoComponentwiseLimit
  rw [Iso.trans_inv, Iso.trans_inv, Iso.app_inv, sheafIsoOfIso_inv, pushforwardToOfIso_app,
    congr_app (Iso.symm_inv _)]
  dsimp
  rw [map_id, comp_id, assoc, assoc, assoc, NatTrans.naturality,
      ← comp_c_app_assoc, congr_app (colimit.isoColimitCocone_ι_hom _ _), assoc,
      colimitCocone_ι_app_c, limitObjIsoLimitCompEvaluation_inv_π_app_assoc, limMap_π_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).hom ≫ limit.π _ (op j) =
      (colimit.ι F j).c.app (op U) := by
  rw [← Iso.eq_inv_comp, colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]

end PresheafedSpace

end AlgebraicGeometry

