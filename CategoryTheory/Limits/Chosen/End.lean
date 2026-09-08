/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Chosen ends and coends

This file defines typeclasses `ChosenCoendsOfShape` and `ChosenEndsOfShape` which contain the data
of a chosen coend and end in `C` for each functor `Jᵒᵖ ⥤ J ⥤ C` of a fixed shape `J`. It also
provides `ChosenCoends` and `ChosenEnds` abbreviations for chosen coends and ends of all shapes.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory.Limits

/-- The data of chosen coends of shape `J` in `C`. -/
/-
**CategoryTheory.Limits.ChosenCoendsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(J : Type u_1) →   [CategoryTheory.Category.{v_1, u_1} J] →     (C : Type 
u_2) → [CategoryTheory.Category.{v_2, u_2} C] → Type (max (max (max u_1 u_2) v_1
) v_2)
参数：max (max u_1 u_2) v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of chosen coends of shape `J` in `C`.
-/
class ChosenCoendsOfShape (J : Type*) [Category* J] (C : Type*) [Category* C] where
  /-- The chosen cowedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  cowedge (F : Jᵒᵖ ⥤ J ⥤ C) : Cowedge F
  /-- The chosen cowedge is colimiting. -/
  isCoend (F : Jᵒᵖ ⥤ J ⥤ C) : IsColimit (cowedge F)

set_option linter.checkUnivs false in
/-- The data of chosen coends in `C`. -/
@[pp_with_univ]
/-
**CategoryTheory.Limits.ChosenCoends** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：ChosenCoends (C : Type*) [Category* C]
参数：C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of chosen coends in `C`.
-/
abbrev ChosenCoends (C : Type*) [Category* C] :=
  ∀ {J : Type u} [Category.{v} J], ChosenCoendsOfShape J C

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenCoendsOfShape J C]

/-- The chosen coend of a functor `Jᵒᵖ ⥤ J ⥤ C`. -/
/-
**CategoryTheory.Limits.chosenCoend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：chosenCoend : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen coend of a functor `Jᵒᵖ ⥤ J ⥤ C`.
-/
def chosenCoend : C := (ChosenCoendsOfShape.cowedge F).pt

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ chosenCoend F`
for any `j : J`. -/
/-
**CategoryTheory.Limits.chosenCoend.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ chosenCoe
nd F`
for any `j : J`.
-/
def chosenCoend.ι (j : J) : (F.obj (op j)).obj j ⟶ chosenCoend F :=
  (ChosenCoendsOfShape.cowedge F).π j

@[reassoc]
/-
**CategoryTheory.Limits.chosenCoend.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_1} J] (F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C))   [inst_2 : CategoryTheory.Limits.ChosenCoen
dsOfShape J C] {i j : J} (f : i ⟶ j),   CategoryTheory.CategoryStruct.comp ((F.m
ap f.op).app i) (CategoryTheory.Limits.chosenCoend.ι F i) =     CategoryTheory.C
ategoryStruct.comp ((F.obj (Opposite.op j)).map f) (CategoryTheory.Limits.chosen
Coend.ι F j)
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)；f : i ⟶ j；(F.map 
f.op).app i；CategoryTheory.Limits.chosenCoend.ι F i；(F.obj (Opposite.op j)).map 
f；CategoryTheory.Limits.chosenCoend.ι F j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Cowedge.condition`：condition (c : Cowedge F) {i j 
: J} (f : i ⟶ j) : (F.map f.op).app i ≫ c.π i = (F.obj (op j)).map f ≫ c.π j
-/
lemma chosenCoend.condition {i j : J} (f : i ⟶ j) :
    (F.map f.op).app _ ≫ chosenCoend.ι F i = (F.obj _).map f ≫ chosenCoend.ι F j :=
  (ChosenCoendsOfShape.cowedge F).condition f

variable {F}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Morphisms out of the chosen coend are determined by their composites with `chosenCoend.ι`. -/
@[ext]
/-
**CategoryTheory.Limits.chosenCoend.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_1} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenCoen
dsOfShape J C] {X : C} {f g : CategoryTheory.Limits.chosenCoend F ⟶ X},   (∀ (j 
: J),       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.chosenCoen
d.ι F j) f =         CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.c
hosenCoend.ι F j) g) →     f = g
参数：CategoryTheory.Functor J C；∀ (j : J),       CategoryTheory.CategoryStruct.com
p (CategoryTheory.Limits.chosenCoend.ι F j) f =         CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.chosenCoend.ι F j) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Multicofork.fst_app_right`：fst_app_right (a) : K.ι
.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…

--- 原说明 ---
Morphisms out of the chosen coend are determined by their composites with `chose
nCoend.ι`.
-/
lemma chosenCoend.hom_ext {X : C} {f g : chosenCoend F ⟶ X}
    (h : ∀ j, chosenCoend.ι F j ≫ f = chosenCoend.ι F j ≫ g) : f = g := by
  apply (ChosenCoendsOfShape.isCoend F).hom_ext
  rintro (a | a)
  · simpa using! _ ≫= h _
  · exact h _

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/-- Constructor for morphisms out of the chosen coend of a functor. -/
/-
**CategoryTheory.Limits.chosenCoend.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.chosenCoend`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_1} J] →         {F
 : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 
: CategoryTheory.Limits.ChosenCoendsOfShape J C] →             {X : C} →        
       (f : (j : J) → (F.obj (Opposite.op j)).obj j ⟶ X) →                 (∀ ⦃i
 j : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp ((F.
map g.op).app i) (f i) =                       CategoryTheory.CategoryStruct.com
p ((F.obj (Opposite.op j)).map g) (f j)) →                   (CategoryTheory.Lim
its.chosenCoend F ⟶ X)
参数：CategoryTheory.Functor J C；f : (j : J) → (F.obj (Opposite.op j)).obj j ⟶ X；∀ 
⦃i j : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp ((
F.map g.op).app i) (f i) =                       CategoryTheory.CategoryStruct.c
omp ((F.obj (Opposite.op j)).map g) (f j)；CategoryTheory.Limits.chosenCoend F ⟶ 
X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms out of the chosen coend of a functor.
-/
def chosenCoend.desc : chosenCoend F ⟶ X :=
  Cowedge.IsColimit.desc (ChosenCoendsOfShape.isCoend F) f hf

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenCoend.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenCoend.ι_desc (j : J) : chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j := by
  apply IsColimit.fac

/-- A natural transformation of bifunctors induces a map on chosen coends. -/
/-
**CategoryTheory.Limits.chosenCoend.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.chosenCoend`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_1} J] →         {F
 : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 
: CategoryTheory.Limits.ChosenCoendsOfShape J C] →             {G : CategoryTheo
ry.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →               (F ⟶ G) → (Category
Theory.Limits.chosenCoend F ⟶ CategoryTheory.Limits.chosenCoend G)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；F ⟶ G；CategoryTheory.Li
mits.chosenCoend F ⟶ CategoryTheory.Limits.chosenCoend G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation of bifunctors induces a map on chosen coends.
-/
def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x ↦ (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ ↦ by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenCoend.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenCoend.ι_map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenCoend.ι F j ≫ chosenCoend.map f = (f.app _).app _ ≫ chosenCoend.ι G j := by
  simp [chosenCoend.map]

@[simp]
/-
**CategoryTheory.Limits.chosenCoend.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_1} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenCoen
dsOfShape J C],   CategoryTheory.Limits.chosenCoend.map (CategoryTheory.Category
Struct.id F) =     CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.chose
nCoend F)
参数：CategoryTheory.Functor J C；CategoryTheory.CategoryStruct.id F；CategoryTheory.
Limits.chosenCoend F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.chosenCoend.hom_ext`：∀ {J : Type u_1} {C : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_1} J] {F : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.chosenCoend.ι_map`：∀ {J : Type u_1} {C : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_1} J] {F : Categor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenCoend.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_1} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenCoen
dsOfShape J C]   {G H : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)}
 (f : F ⟶ G) (g : G ⟶ H),   CategoryTheory.CategoryStruct.comp (CategoryTheory.L
imits.chosenCoend.map f)       (CategoryTheory.Limits.chosenCoend.map g) =     C
ategoryTheory.Limits.chosenCoend.map (CategoryTheory.CategoryStruct.comp f g)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；f : F ⟶ G；g : G ⟶ H；Cat
egoryTheory.Limits.chosenCoend.map f；CategoryTheory.Limits.chosenCoend.map g；Cat
egoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.chosenCoend.hom_ext`：∀ {J : Type u_1} {C : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_1} J] {F : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.chosenCoend.ι_map_assoc`：∀ {J : Type u_1} {C : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_1} J] {F : Categor…
· 使用定理 `CategoryTheory.Limits.chosenCoend.ι_map`：∀ {J : Type u_1} {C : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_2} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_1} J] {F : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

/-- The chosen coend construction as a functor out of the bifunctor category. -/
@[simps]
/-
**CategoryTheory.Limits.chosenCoendFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：chosenCoendFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen coend construction as a functor out of the bifunctor category.
-/
def chosenCoendFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := chosenCoend F
  map f := chosenCoend.map f

/-- The data of chosen ends of shape `J` in `C`. -/
/-
**CategoryTheory.Limits.ChosenEndsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：(J : Type u_3) →   [CategoryTheory.Category.{v_3, u_3} J] →     (C : Type 
u_4) → [CategoryTheory.Category.{v_4, u_4} C] → Type (max (max (max u_3 u_4) v_3
) v_4)
参数：max (max u_3 u_4) v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of chosen ends of shape `J` in `C`.
-/
class ChosenEndsOfShape (J : Type*) [Category* J] (C : Type*) [Category* C] where
  /-- The chosen wedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  wedge (F : Jᵒᵖ ⥤ J ⥤ C) : Wedge F
  /-- The chosen wedge is limiting. -/
  isEnd (F : Jᵒᵖ ⥤ J ⥤ C) : IsLimit (wedge F)

set_option linter.checkUnivs false in
/-- The data of chosen ends in `C`. -/
@[pp_with_univ]
/-
**CategoryTheory.Limits.ChosenEnds** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：ChosenEnds (C : Type*) [Category* C]
参数：C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of chosen ends in `C`.
-/
abbrev ChosenEnds (C : Type*) [Category* C] :=
  ∀ {J : Type u} [Category.{v} J], ChosenEndsOfShape J C

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenEndsOfShape J C]

/-- The chosen end of a functor `Jᵒᵖ ⥤ J ⥤ C`. -/
/-
**CategoryTheory.Limits.chosenEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：chosenEnd : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen end of a functor `Jᵒᵖ ⥤ J ⥤ C`.
-/
def chosenEnd : C := (ChosenEndsOfShape.wedge F).pt

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `chosenEnd F ⟶ (F.obj (op j)).obj j`
for any `j : J`. -/
/-
**CategoryTheory.Limits.chosenEnd.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `chosenEnd F ⟶ (F.obj (op j)).ob
j j`
for any `j : J`.
-/
def chosenEnd.π (j : J) : chosenEnd F ⟶ (F.obj (op j)).obj j :=
  (ChosenEndsOfShape.wedge F).ι j

@[reassoc]
/-
**CategoryTheory.Limits.chosenEnd.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u_3} {C : Type u_4} [inst : CategoryTheory.Category.{v_3, u_4}
 C]   [inst_1 : CategoryTheory.Category.{v_4, u_3} J] (F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C))   [inst_2 : CategoryTheory.Limits.ChosenEnds
OfShape J C] {i j : J} (f : i ⟶ j),   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.chosenEnd.π F i) ((F.obj (Opposite.op i)).map f) =     CategoryT
heory.CategoryStruct.comp (CategoryTheory.Limits.chosenEnd.π F j) ((F.map f.op).
app j)
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)；f : i ⟶ j；Categor
yTheory.Limits.chosenEnd.π F i；(F.obj (Opposite.op i)).map f；CategoryTheory.Limi
ts.chosenEnd.π F j；(F.map f.op).app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Wedge.condition`：condition (c : Wedge F) {i j : J}
 (f : i ⟶ j) : c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j
-/
lemma chosenEnd.condition {i j : J} (f : i ⟶ j) :
    chosenEnd.π F i ≫ (F.obj (op i)).map f = chosenEnd.π F j ≫ (F.map f.op).app j :=
  (ChosenEndsOfShape.wedge F).condition f

variable {F}

/-- Morphisms into the chosen end are determined by their composites with `chosenEnd.π`. -/
@[ext]
/-
**CategoryTheory.Limits.chosenEnd.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u_3} {C : Type u_4} [inst : CategoryTheory.Category.{v_3, u_4}
 C]   [inst_1 : CategoryTheory.Category.{v_4, u_3} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenEnds
OfShape J C] {X : C} {f g : X ⟶ CategoryTheory.Limits.chosenEnd F},   (∀ (j : J)
,       CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.chosenEnd.π 
F j) =         CategoryTheory.CategoryStruct.comp g (CategoryTheory.Limits.chose
nEnd.π F j)) →     f = g
参数：CategoryTheory.Functor J C；∀ (j : J),       CategoryTheory.CategoryStruct.com
p f (CategoryTheory.Limits.chosenEnd.π F j) =         CategoryTheory.CategoryStr
uct.comp g (CategoryTheory.Limits.chosenEnd.π F j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Wedge.IsLimit.hom_ext`：hom_ext (hc : IsLimit c) {X
 : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j = g ≫ c.ι j) : f = g

--- 原说明 ---
Morphisms into the chosen end are determined by their composites with `chosenEnd
.π`.
-/
lemma chosenEnd.hom_ext {X : C} {f g : X ⟶ chosenEnd F}
    (h : ∀ j, f ≫ chosenEnd.π F j = g ≫ chosenEnd.π F j) : f = g :=
  Wedge.IsLimit.hom_ext (ChosenEndsOfShape.isEnd F) h

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- Constructor for morphisms into the chosen end of a functor. -/
/-
**CategoryTheory.Limits.chosenEnd.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.chosenEnd`。
形式化陈述：{J : Type u_3} →   {C : Type u_4} →     [inst : CategoryTheory.Category.{v
_3, u_4} C] →       [inst_1 : CategoryTheory.Category.{v_4, u_3} J] →         {F
 : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 
: CategoryTheory.Limits.ChosenEndsOfShape J C] →             {X : C} →          
     (f : (j : J) → X ⟶ (F.obj (Opposite.op j)).obj j) →                 (∀ ⦃i j
 : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp (f i) 
((F.obj (Opposite.op i)).map g) =                       CategoryTheory.CategoryS
truct.comp (f j) ((F.map g.op).app j)) →                   (X ⟶ CategoryTheory.L
imits.chosenEnd F)
参数：CategoryTheory.Functor J C；f : (j : J) → X ⟶ (F.obj (Opposite.op j)).obj j；∀ 
⦃i j : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp (f
 i) ((F.obj (Opposite.op i)).map g) =                       CategoryTheory.Categ
oryStruct.comp (f j) ((F.map g.op).app j)；X ⟶ CategoryTheory.Limits.chosenEnd F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms into the chosen end of a functor.
-/
def chosenEnd.lift : X ⟶ chosenEnd F :=
  Wedge.IsLimit.lift (ChosenEndsOfShape.isEnd F) f hf

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenEnd.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenEnd.lift_π (j : J) : chosenEnd.lift f hf ≫ chosenEnd.π F j = f j := by
  apply IsLimit.fac

/-- A natural transformation of bifunctors induces a map on chosen ends. -/
/-
**CategoryTheory.Limits.chosenEnd.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.chosenEnd`。
形式化陈述：{J : Type u_3} →   {C : Type u_4} →     [inst : CategoryTheory.Category.{v
_3, u_4} C] →       [inst_1 : CategoryTheory.Category.{v_4, u_3} J] →         {F
 : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 
: CategoryTheory.Limits.ChosenEndsOfShape J C] →             {G : CategoryTheory
.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →               (F ⟶ G) → (CategoryTh
eory.Limits.chosenEnd F ⟶ CategoryTheory.Limits.chosenEnd G)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；F ⟶ G；CategoryTheory.Li
mits.chosenEnd F ⟶ CategoryTheory.Limits.chosenEnd G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation of bifunctors induces a map on chosen ends.
-/
def chosenEnd.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenEnd F ⟶ chosenEnd G :=
  chosenEnd.lift (fun x ↦ chosenEnd.π F x ≫ (f.app (op x)).app x) (fun j j' φ ↦ by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e, reassoc_of% chosenEnd.condition F φ]
    simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenEnd.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenEnd.map_π {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenEnd.map f ≫ chosenEnd.π G j = chosenEnd.π F j ≫ (f.app (op j)).app j := by
  simp [chosenEnd.map]

@[simp]
/-
**CategoryTheory.Limits.chosenEnd.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u_3} {C : Type u_4} [inst : CategoryTheory.Category.{v_3, u_4}
 C]   [inst_1 : CategoryTheory.Category.{v_4, u_3} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenEnds
OfShape J C],   CategoryTheory.Limits.chosenEnd.map (CategoryTheory.CategoryStru
ct.id F) =     CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.chosenEnd
 F)
参数：CategoryTheory.Functor J C；CategoryTheory.CategoryStruct.id F；CategoryTheory.
Limits.chosenEnd F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.chosenEnd.hom_ext`：∀ {J : Type u_3} {C : Type u_4}
 [inst : CategoryTheory.Category.{v_3, u_4} C]   [inst_1 : CategoryTheory.Catego
ry.{v_4, u_3} J] {F : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.chosenEnd.map_π`：∀ {J : Type u_3} {C : Type u_4} [
inst : CategoryTheory.Category.{v_3, u_4} C]   [inst_1 : CategoryTheory.Category
.{v_4, u_3} J] {F : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chosenEnd.map_id : chosenEnd.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.chosenEnd.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u_3} {C : Type u_4} [inst : CategoryTheory.Category.{v_3, u_4}
 C]   [inst_1 : CategoryTheory.Category.{v_4, u_3} J] {F : CategoryTheory.Functo
r Jᵒᵖ (CategoryTheory.Functor J C)}   [inst_2 : CategoryTheory.Limits.ChosenEnds
OfShape J C] {G H : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)}   (
f : F ⟶ G) (g : G ⟶ H),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Lim
its.chosenEnd.map f) (CategoryTheory.Limits.chosenEnd.map g) =     CategoryTheor
y.Limits.chosenEnd.map (CategoryTheory.CategoryStruct.comp f g)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；f : F ⟶ G；g : G ⟶ H；Cat
egoryTheory.Limits.chosenEnd.map f；CategoryTheory.Limits.chosenEnd.map g；Categor
yTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.chosenEnd.hom_ext`：∀ {J : Type u_3} {C : Type u_4}
 [inst : CategoryTheory.Category.{v_3, u_4} C]   [inst_1 : CategoryTheory.Catego
ry.{v_4, u_3} J] {F : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.chosenEnd.map_π`：∀ {J : Type u_3} {C : Type u_4} [
inst : CategoryTheory.Category.{v_3, u_4} C]   [inst_1 : CategoryTheory.Category
.{v_4, u_3} J] {F : Categor…
· 使用定理 `CategoryTheory.Limits.chosenEnd.map_π_assoc`：∀ {J : Type u_3} {C : Type 
u_4} [inst : CategoryTheory.Category.{v_3, u_4} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_4, u_3} J] {F : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chosenEnd.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenEnd.map f ≫ chosenEnd.map g = chosenEnd.map (f ≫ g) := by
  cat_disch

/-- The chosen end construction as a functor out of the bifunctor category. -/
@[simps]
/-
**CategoryTheory.Limits.chosenEndFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：chosenEndFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen end construction as a functor out of the bifunctor category.
-/
def chosenEndFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := chosenEnd F
  map f := chosenEnd.map f

end CategoryTheory.Limits

