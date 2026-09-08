/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.CompatiblePlus
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

@[expose] public section


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type*} [Category* D]
variable {E : Type*} [Category* E]
variable (F : D ⥤ E)

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphism to a state that can be handled using the universal property
of sheafification. -/
/-
**CategoryTheory.GrothendieckTopology.sheafifyCompIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_
lift` to reduce
the components of this isomorphism to a state that can be handled using the univ
ersal property
of sheafification.
-/
noncomputable def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D) [forall (F : D ⥤ E) (X : C), Pr
eservesColimitsOfShape (J.Cover X)ᵒᵖ F] [forall (F : D ⥤ E) (X : C) (W : J.Cover
 X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] : (whiskeringLeft _
 _ E).obj (J.sheafify P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E
参数：P : Cᵒᵖ ⥤ D；F : D ⥤ E；X : C；J.Cover X；F : D ⥤ E；X : C；W : J.Cover X；P : Cᵒᵖ ⥤
 D；W.index P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`.
-/
noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_hom_app** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E) [forall (F 
: D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F] [forall (F : D ⥤ E) 
(X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
 : (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom
参数：P : Cᵒᵖ ⥤ D；F : D ⥤ E；F : D ⥤ E；X : C；J.Cover X；F : D ⥤ E；X : C；W : J.Cover X
；P : Cᵒᵖ ⥤ D；W.index P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E) [forall (F 
: D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F] [forall (F : D ⥤ E) 
(X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
 : (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv
参数：P : Cᵒᵖ ⥤ D；F : D ⥤ E；F : D ⥤ E；X : C；J.Cover X；F : D ⥤ E；X : C；W : J.Cover X
；P : Cᵒᵖ ⥤ D；W.index P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp]

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerRightIso : J.sheafification D ⋙ (whiskeringRight _ _ 
_).obj F ≅ (whiskeringRight _ _ _).obj F ⋙ J.sheafification E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`.
-/
noncomputable def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.sheafification E := by
  refine associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ ?_
  refine ?_ ≪≫ associator _ _ _
  refine (associator _ _ _).symm ≪≫ ?_
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_hom_app** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerRightIso_hom_app : (J.sheafificationWhiskerRightIso F
).hom.app P = (J.sheafifyCompIso F P).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).hom.app P = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_inv_app** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafificationWhiskerRightIso_inv_app : (J.sheafificationWhiskerRightIso F
).inv.app P = (J.sheafifyCompIso F P).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_ho
m** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：whiskerRight_toSheafify_sheafifyCompIso_hom : whiskerRight (J.toSheafify _
) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrothendieckTopology.plusCompIso_whiskerRight`：plusCompIs
o_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : whiskerRight (J.plusMap η) F ≫ (J.p
lusCompIso F Q).hom = (J.plusCompIso F P).hom ≫ J.…
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_comp`：plusMap_comp {P Q R : 
Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ
· 使用定理 `CategoryTheory.GrothendieckTopology.whiskerRight_toPlus_comp_plusCompIso
_hom`：whiskerRight_toPlus_comp_plusCompIso_hom : whiskerRight (J.toPlus _) _ ≫ (
J.plusCompIso F P).hom = J.toPlus _
-/
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _ := by
  dsimp [sheafifyCompIso]
  simp only [toSheafify, sheafify, whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc, ← J.plusMap_comp, whiskerRight_toPlus_comp_plusCompIso_hom, ←
    Category.assoc, whiskerRight_toPlus_comp_plusCompIso_hom]

@[simp, reassoc]
/-
**CategoryTheory.GrothendieckTopology.toSheafify_comp_sheafifyCompIso_inv** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toSheafify_comp_sheafifyCompIso_inv : J.toSheafify _ ≫ (J.sheafifyCompIso 
F P).inv = whiskerRight (J.toSheafify _) _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyComp
Iso_hom`：whiskerRight_toSheafify_sheafifyCompIso_hom : whiskerRight (J.toSheafif
y _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [Iso.comp_inv_eq]; simp

section

-- We will sheafify `D`-valued presheaves in this section.
variable {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory D FD] [PreservesLimitsOfSize.{max v u, max v u} (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafifyCompIso_inv_eq_sheafifyLift** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyCompIso_inv_eq_sheafifyLift : (J.sheafifyCompIso F P).inv = J.shea
fifyLift (whiskerRight (J.toSheafify P) F) (HasSheafCompose.isSheaf _ ((J.sheafi
fy_isSheaf _)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafifyLift_unique`：sheafifyLift_un
ique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.sheafify P ⟶
 Q) : J.toSheafify P ≫ γ = η -> γ = sheafifyL…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {A : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} A}   {B : Type u₃} {ins…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafify_isSheaf`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology 
C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyComp
Iso_hom`：whiskerRight_toSheafify_sheafifyCompIso_hom : whiskerRight (J.toSheafif
y _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.sheafifyLift (whiskerRight (J.toSheafify P) F)
        (HasSheafCompose.isSheaf _ ((J.sheafify_isSheaf _))) := by
  apply J.sheafifyLift_unique
  rw [Iso.comp_inv_eq]
  simp

end

end CategoryTheory.GrothendieckTopology

