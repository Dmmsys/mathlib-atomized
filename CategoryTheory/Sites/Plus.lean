/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a Grothendieck topology `J`.

See <https://stacks.math.columbia.edu/tag/00W1> for details.

-/

@[expose] public section


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w' w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w} [Category.{w'} D]

noncomputable section

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable (P : Cᵒᵖ ⥤ D)

set_option backward.isDefEq.respectTransparency false in
/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.diagram** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：diagram (X : C) : (J.Cover X)ᵒᵖ ⥤ D where obj S
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram whose colimit defines the values of `plus`.
-/
def diagram (X : C) : (J.Cover X)ᵒᵖ ⥤ D where
  obj S := multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop))
      (fun I => Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' (I.r.map f.unop)))

set_option backward.isDefEq.respectTransparency false in
/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.diagramPullback** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op 
⋙ J.diagram P X where app S
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper definition used to define the morphisms for `plus`.
-/
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X where
  app S :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' I.r.base)
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I => by simp; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.diagramNatTrans** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.di
agram Q X where app W
参数：η : P ⟶ Q；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`.
-/
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X where
  app W :=
    Multiequalizer.lift _ _ (fun _ => Multiequalizer.ι _ _ ≫ η.app _) (fun i => by
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.diagramNatTrans_id** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) : J.diagramNatTrans (𝟙 P) X = 𝟙 (
J.diagram P X)
参数：X : C；P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift.congr_simp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanSha
pe}   (I : CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.diagramNatTrans_zero** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) : J.diagramNa
tTrans (0 : P ⟶ Q) X = 0
参数：X : C；P Q : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_app`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift.congr_simp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanSha
pe}   (I : CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (0 : P ⟶ Q) X = 0 := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.diagramNatTrans_comp** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) : J
.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X
参数：η : P ⟶ Q；γ : Q ⟶ R；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_app`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

variable (D) in
/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.diagramFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.Cover X)ᵒᵖ ⥤ D where obj P
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`J.diagram P`, as a functor in `P`.
-/
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.Cover X)ᵒᵖ ⥤ D where
  obj P := J.diagram P X
  map η := J.diagramNatTrans η X

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The plus construction, associating a presheaf to any presheaf.
See `plusFunctor` below for a functorial version. -/
/-
**CategoryTheory.GrothendieckTopology.plusObj** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：plusObj : Cᵒᵖ ⥤ D where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The plus construction, associating a presheaf to any presheaf.
See `plusFunctor` below for a functorial version.
-/
def plusObj : Cᵒᵖ ⥤ D where
  obj X := colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    let e := S.unop.pullbackId
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op, ← Category.assoc]
    convert! Category.id_comp (colimit.ι (diagram J P (unop X)) S)
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.id_comp, Category.assoc]
    dsimp [Cover.Arrow.map, Cover.Arrow.base]
    cases I
    congr
    simp
  map_comp := by
    intro X Y Z f g
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colimMap_assoc,
      Category.assoc]
    let e := S.unop.pullbackComp g.unop f.unop
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op, ← Category.assoc, ← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.assoc]
    cases I
    dsimp only [Cover.Arrow.base, Cover.Arrow.map]
    congr 2
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition used in `plus` below. -/
/-
**CategoryTheory.GrothendieckTopology.plusMap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where app 
X
参数：η : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition used in `plus` below.
-/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where
  app X := colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    ext
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    congr 1
    exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

@[simp]
/-
**CategoryTheory.GrothendieckTopology.plusMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_id`：diagramNatTrans_
id (X : C) (P : Cᵒᵖ ⥤ D) : J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X)
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ := by
  ext : 2
  dsimp only [plusMap, plusObj]
  rw [J.diagramNatTrans_id, NatTrans.id_app]
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.plusMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0
参数：P Q : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_zero`：diagramNatTran
s_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) : J.diagramNatTrans (0 : P ⟶ Q) X
 = 0
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0 := by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**CategoryTheory.GrothendieckTopology.plusMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plusMap (η ≫ γ)
 = J.plusMap η ≫ J.plusMap γ
参数：η : P ⟶ Q；γ : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_comp`：diagramNatTran
s_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) : J.diagramNatTrans (η 
≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatT…
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_app`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ := by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap, J.diagramNatTrans_comp]

variable (D) in
/-- The plus construction, a functor sending `P` to `J.plusObj P`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.plusFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where obj P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The plus construction, a functor sending `P` to `J.plusObj P`.
-/
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  obj P := J.plusObj P
  map η := J.plusMap η

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from `P` to `J.plusObj P`.
See `toPlusNatTrans` for a functorial version. -/
/-
**CategoryTheory.GrothendieckTopology.toPlus** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.GrothendieckTopology`。
形式化陈述：toPlus : P ⟶ J.plusObj P where app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P` to `J.plusObj P`.
See `toPlusNatTrans` for a functorial version.
-/
def toPlus : P ⟶ J.plusObj P where
  app X := Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    delta Cover.toMultiequalizer
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    dsimp only [Functor.op, unop_op]
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := homOfLE (OrderTop.le_top _)
    rw [← colimit.w _ e.op, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    simp only [Category.assoc]
    dsimp [Cover.Arrow.base]
    simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.toPlus_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus 
_ ≫ J.plusMap η
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_app`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η := by
  ext
  dsimp [toPlus, plusMap]
  delta Cover.toMultiequalizer
  simp only [ι_colimMap, Category.assoc]
  simp_rw [← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

set_option backward.defeqAttrib.useBackward true in
variable (D) in
/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.toPlusNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where app P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from the identity functor to `plus`.
-/
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  app P := J.toPlus P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
/-
**CategoryTheory.GrothendieckTopology.plusMap_toPlus** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramPullback_app`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.condition`：condition (b) : Multiequ
alizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι I (J.snd b) ≫ I.snd b

--- 原说明 ---
`(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺`
-/
theorem plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) := by
  ext X : 2
  refine colimit.hom_ext (fun S => ?_)
  dsimp only [plusMap, toPlus]
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [ι_colimMap, ← colimit.w _ e.op, ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
  erw [Multiequalizer.lift_ι]
  simp only [unop_op, op_unop, diagram_map, Category.assoc, limit.lift_π,
    Multifork.ofι_π_app]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  erw [← colimit.w _ ee.op, ι_colimMap_assoc, colimit.ι_pre, diagramPullback_app,
    ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun II => ?_)
  convert!
    Multiequalizer.condition (S.unop.index P)
      { fst := I, snd := II.base, r.Z := II.Y, r.g₁ := II.f, r.g₂ := 𝟙 II.Y } using 1
  all_goals simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P)
参数：hP : Presheaf.IsSheaf J P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multiequalizer`：isSheaf_iff_multiequ
alizer [forall (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] : IsSheaf
 J P ↔ forall (X : C) (S : J.Cover X), I…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.diagram_map`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D
 : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.map_f`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.Grothendieck
Topology C}   {S T : J.Cover X} (I : S.Arro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.of_isIso_fac_left`：of_isIso_fac_left {X Y Z : C} {f
 : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f] [hh : IsIso h] (w : f ≫ g = h) : IsI
so g
· 使用定理 `CategoryTheory.Limits.isIso_ι_of_isInitial`：isIso_ι_of_isInitial {j : J}
 (I : IsInitial j) (F : J ⥤ C) [HasColimit F] [forall (i j : J) (f : i ⟶ j), IsI
so (F.map f)] : IsIso (colimit.ι…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
theorem isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  suffices ∀ X, IsIso ((J.toPlus P).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine IsIso.comp_isIso' inferInstance ?_
  suffices ∀ (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f) from
    isIso_ι_of_isInitial (initialOpOfTerminal isTerminalTop) _
  intro S T e
  have : S.unop.toMultiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.toMultiequalizer P :=
    Multiequalizer.hom_ext _ _ _ (fun II => by simp)
  exact IsIso.of_isIso_fac_left this

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
/-
**CategoryTheory.GrothendieckTopology.isoToPlus** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GrothendieckTopology`。
形式化陈述：isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P
参数：hP : Presheaf.IsSheaf J P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf`：isIso_toPlu
s_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P)

--- 原说明 ---
The natural isomorphism between `P` and `P⁺` when `P` is a sheaf.
-/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)

@[simp]
/-
**CategoryTheory.GrothendieckTopology.isoToPlus_hom** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.GrothendieckTopology`。
形式化陈述：isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).hom = J.toP
lus P
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).hom = J.toPlus P :=
  rfl

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
/-
**CategoryTheory.GrothendieckTopology.plusLift** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusO
bj P ⟶ Q
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf.
-/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.toPlus_plusLift** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : 
J.toPlus P ≫ J.plusLift η hQ = η
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality`：toPlus_naturality
 {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η
-/
theorem toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η := by
  dsimp [plusLift]
  rw [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp only [isoToPlus, asIso]
  rw [toPlus_naturality]
/-
**CategoryTheory.GrothendieckTopology.plusLift_unique** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ
 : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q；γ : J.plusObj P ⟶ Q；hγ : J.toPlus P ≫ γ =
 η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_comp`：plusMap_comp {P Q R : 
Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality`：toPlus_naturality
 {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ := by
  dsimp only [plusLift]
  rw [Iso.eq_comp_inv, ← hγ, plusMap_comp]
  simp
/-
**CategoryTheory.GrothendieckTopology.plus_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsShea
f J Q) (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ
参数：η γ : J.plusObj P ⟶ Q；hQ : Presheaf.IsSheaf J Q；h : J.toPlus P ≫ η = J.toPlus
 P ≫ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plusLift_unique`：plusLift_unique {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q) (hγ :
 J.toPlus P ≫ γ = η) : γ = J.plusLift η h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ := by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  apply plusLift_unique
  exact h

@[simp]
/-
**CategoryTheory.GrothendieckTopology.isoToPlus_inv** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.GrothendieckTopology`。
形式化陈述：isoToPlus_inv (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).inv = J.plu
sLift (𝟙 _) hP
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plusLift_unique`：plusLift_unique {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q) (hγ :
 J.toPlus P ≫ γ = η) : γ = J.plusLift η h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem isoToPlus_inv (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP := by
  apply J.plusLift_unique
  rw [Iso.comp_inv_eq, Category.id_comp]
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.plusMap_plusLift** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.
IsSheaf J R) : J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR
参数：η : P ⟶ Q；γ : Q ⟶ R；hR : Presheaf.IsSheaf J R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plusLift_unique`：plusLift_unique {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q) (hγ :
 J.toPlus P ≫ γ = η) : γ = J.plusLift η h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality`：toPlus_naturality
 {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_plusLift`：toPlus_plusLift {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.toPlus P ≫ J.plusLift η
 hQ = η
-/
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plusLift_unique
  rw [← Category.assoc, ← J.toPlus_naturality, Category.assoc, J.toPlus_plusLift]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.plusFunctor_preservesZeroMorphisms** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：plusFunctor_preservesZeroMorphisms [Preadditive D] : (plusFunctor J D).Pre
servesZeroMorphisms where map_zero F G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_zero`：plusMap_zero [Preaddit
ive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0
· 使用定理 `CategoryTheory.NatTrans.app_zero`：app_zero (X : C) : (0 : F ⟶ G).app X =
 0
-/
instance plusFunctor_preservesZeroMorphisms [Preadditive D] :
    (plusFunctor J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext
    dsimp
    rw [J.plusMap_zero, NatTrans.app_zero]

end

end CategoryTheory.GrothendieckTopology

