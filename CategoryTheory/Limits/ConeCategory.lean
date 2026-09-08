/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Limits and the category of (co)cones

This file contains results that stem from the limit API. For the definition and the category
instance of `Cone`, please refer to `Mathlib/CategoryTheory/Limits/Cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `CostructuredArrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/

@[expose] public section


namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- Given a cone `c` over `F`, we can interpret the legs of `c` as structured arrows
    `c.pt ⟶ F.obj -`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.Cone.toStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) → Catego
ryTheory.Functor J (CategoryTheory.StructuredArrow c.pt F)
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.StructuredArrow c.pt F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone `c` over `F`, we can interpret the legs of `c` as structured arrows
    `c.pt ⟶ F.obj -`.
-/
def Cone.toStructuredArrow {F : J ⥤ C} (c : Cone F) : J ⥤ StructuredArrow c.pt F where
  obj j := StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

/-- If `F` has a limit, then the limit projections can be interpreted as structured arrows
    `limit F ⟶ F.obj -`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.limit.toStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F]
 →             CategoryTheory.Functor J (CategoryTheory.StructuredArrow (Categor
yTheory.Limits.limit F) F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.StructuredArrow (CategoryTheory
.Limits.limit F) F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a limit, then the limit projections can be interpreted as structured 
arrows
    `limit F ⟶ F.obj -`.
-/
noncomputable def limit.toStructuredArrow (F : J ⥤ C) [HasLimit F] :
    J ⥤ StructuredArrow (limit F) F where
  obj j := StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

/-- `Cone.toStructuredArrow` can be expressed in terms of `Functor.toStructuredArrow`. -/
/-
**CategoryTheory.Limits.Cone.toStructuredArrowIsoToStructuredArrow** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →       
      c.toStructuredArrow ≅ (CategoryTheory.Functor.id J).toStructuredArrow c.pt
 F c.π.app ⋯
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.Functor.id J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cone.toStructuredArrow` can be expressed in terms of `Functor.toStructuredArrow
`.
-/
def Cone.toStructuredArrowIsoToStructuredArrow {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ≅ (𝟭 J).toStructuredArrow c.pt F c.π.app (by simp) :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- `Functor.toStructuredArrow` can be expressed in terms of `Cone.toStructuredArrow`. -/
/-
**CategoryTheory.Limits._root_.CategoryTheory.Functor.toStructuredArrowIsoToStru
cturedArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.toStructuredArrow` can be expressed in terms of `Cone.toStructuredArrow
`.
-/
def _root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow (G : J ⥤ K) (X : C)
    (F : K ⥤ C) (f : (Y : J) → X ⟶ F.obj (G.obj Y))
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ≅
      (Cone.mk X ⟨f, by simp [h]⟩).toStructuredArrow ⋙ StructuredArrow.pre _ _ _ :=
  Iso.refl _

/-- Interpreting the legs of a cone as a structured arrow and then forgetting the arrow again does
    nothing. -/
@[simps!]
/-
**CategoryTheory.Limits.Cone.toStructuredArrowCompProj** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →       
      c.toStructuredArrow.comp (CategoryTheory.StructuredArrow.proj c.pt F) ≅ Ca
tegoryTheory.Functor.id J
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.StructuredArrow.proj c.pt F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpreting the legs of a cone as a structured arrow and then forgetting the ar
row again does
    nothing.
-/
def Cone.toStructuredArrowCompProj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
/-
**CategoryTheory.Limits.Cone.toStructuredArrow_comp_proj** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.Cone`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 (c : CategoryTheory.Limits.Cone F),   c.toStructuredArrow.comp (CategoryTheory.
StructuredArrow.proj c.pt F) = CategoryTheory.Functor.id J
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.StructuredArrow.proj c.pt F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cone.toStructuredArrow_comp_proj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ = 𝟭 J :=
  rfl

/-- Interpreting the legs of a cone as a structured arrow, interpreting this arrow as an arrow over
    the cone point, and finally forgetting the arrow is the same as just applying the functor the
    cone was over. -/
@[simps!]
/-
**CategoryTheory.Limits.Cone.toStructuredArrowCompToUnderCompForget** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →       
      c.toStructuredArrow.comp                 ((CategoryTheory.StructuredArrow.
toUnder c.pt F).comp (CategoryTheory.Under.forget c.pt)) ≅               F
参数：c : CategoryTheory.Limits.Cone F；(CategoryTheory.StructuredArrow.toUnder c.pt
 F).comp (CategoryTheory.Under.forget c.pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpreting the legs of a cone as a structured arrow, interpreting this arrow a
s an arrow over
    the cone point, and finally forgetting the arrow is the same as just applyin
g the functor the
    cone was over.
-/
def Cone.toStructuredArrowCompToUnderCompForget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
/-
**CategoryTheory.Limits.Cone.toStructuredArrow_comp_toUnder_comp_forget** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Cone`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 (c : CategoryTheory.Limits.Cone F),   c.toStructuredArrow.comp ((CategoryTheory
.StructuredArrow.toUnder c.pt F).comp (CategoryTheory.Under.forget c.pt)) = F
参数：c : CategoryTheory.Limits.Cone F；(CategoryTheory.StructuredArrow.toUnder c.pt
 F).comp (CategoryTheory.Under.forget c.pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cone.toStructuredArrow_comp_toUnder_comp_forget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ = F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A cone `c` on `F : J ⥤ C` lifts to a cone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) →       
      CategoryTheory.Limits.Cone (c.toStructuredArrow.comp (CategoryTheory.Struc
turedArrow.toUnder c.pt F))
参数：c : CategoryTheory.Limits.Cone F；c.toStructuredArrow.comp (CategoryTheory.Str
ucturedArrow.toUnder c.pt F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone `c` on `F : J ⥤ C` lifts to a cone in `Over c.pt` with cone point `𝟙 c.pt
`.
-/
def Cone.toUnder {F : J ⥤ C} (c : Cone F) :
    Cone (c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 c.pt)
  π := { app := fun j => Under.homMk (c.π.app j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The limit cone for `F : J ⥤ C` lifts to a cocone in `Under (limit F)` with cone point
    `𝟙 (limit F)`. This is automatically also a limit cone. -/
/-
**CategoryTheory.Limits.limit.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F]
 →             CategoryTheory.Limits.Cone               ((CategoryTheory.Limits.
limit.toStructuredArrow F).comp                 (CategoryTheory.StructuredArrow.
toUnder (CategoryTheory.Limits.limit F) F))
参数：F : CategoryTheory.Functor J C；(CategoryTheory.Limits.limit.toStructuredArrow
 F).comp                 (CategoryTheory.StructuredArrow.toUnder (CategoryTheory
.Limits.limit F) F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for `F : J ⥤ C` lifts to a cocone in `Under (limit F)` with cone 
point
    `𝟙 (limit F)`. This is automatically also a limit cone.
-/
noncomputable def limit.toUnder (F : J ⥤ C) [HasLimit F] :
    Cone (limit.toStructuredArrow F ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 (limit F))
  π := { app := fun j => Under.homMk (limit.π F j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
/-- `c.toUnder` is a lift of `c` under the forgetful functor. -/
@[simps!]
/-
**CategoryTheory.Limits.Cone.mapConeToUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) → (Categ
oryTheory.Under.forget c.pt).mapCone c.toUnder ≅ c
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.Under.forget c.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c.toUnder` is a lift of `c` under the forgetful functor.
-/
def Cone.mapConeToUnder {F : J ⥤ C} (c : Cone F) : (Under.forget c.pt).mapCone c.toUnder ≅ c :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- Given a diagram of `StructuredArrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.Cone.fromStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {D : Typ
e u₄} →           [inst_2 : CategoryTheory.Category.{v₄, u₄} D] →             (F
 : CategoryTheory.Functor C D) →               {X : D} →                 (G : Ca
tegoryTheory.Functor J (CategoryTheory.StructuredArrow X F)) →                  
 CategoryTheory.Limits.Cone (G.comp ((CategoryTheory.StructuredArrow.proj X F).c
omp F))
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor J (CategoryTheory.S
tructuredArrow X F)；G.comp ((CategoryTheory.StructuredArrow.proj X F).comp F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a diagram of `StructuredArrow X F`s, we may obtain a cone with cone point 
`X`.
-/
def Cone.fromStructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ StructuredArrow X F) :
    Cone (G ⋙ StructuredArrow.proj X F ⋙ F) where
  pt := X
  π := { app := fun j => (G.obj j).hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a cone `c : Cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
/-
**CategoryTheory.Limits.Cone.toStructuredArrowCone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {D : Typ
e u₄} →           [inst_2 : CategoryTheory.Category.{v₄, u₄} D] →             {K
 : CategoryTheory.Functor J C} →               (c : CategoryTheory.Limits.Cone K
) →                 (F : CategoryTheory.Functor C D) →                   {X : D}
 →                     (f : X ⟶ F.obj c.pt) →                       CategoryTheo
ry.Limits.Cone                         ((F.mapCone c).toStructuredArrow.comp    
                       ((CategoryTheory.StructuredArrow.map f).comp (CategoryThe
ory.StructuredArrow.pre X K F)))
参数：c : CategoryTheory.Limits.Cone K；F : CategoryTheory.Functor C D；f : X ⟶ F.obj
 c.pt；(F.mapCone c).toStructuredArrow.comp                           ((CategoryT
heory.StructuredArrow.map f).comp (CategoryTheory.StructuredArrow.pre X K F))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone `c : Cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone
 of structured
arrows over `X` with `f` as the cone point.
-/
def Cone.toStructuredArrowCone {K : J ⥤ C} (c : Cone K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt) :
    Cone ((F.mapCone c).toStructuredArrow ⋙ StructuredArrow.map f ⋙ StructuredArrow.pre _ K F) where
  pt := StructuredArrow.mk f
  π := { app := fun j => StructuredArrow.homMk (c.π.app j) rfl }

set_option backward.defeqAttrib.useBackward true in
/-- Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.toCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Functor (CategoryTheory.Limi
ts.Cone F)             (CategoryTheory.CostructuredArrow (CategoryTheory.Functor
.const J) F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.Cone F；CategoryTheory.Co
structuredArrow (CategoryTheory.Functor.const J) F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part o
f an
    equivalence, see `Cone.equivCostructuredArrow`.
-/
def Cone.toCostructuredArrow (F : J ⥤ C) : Cone F ⥤ CostructuredArrow (const J) F where
  obj c := CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

set_option backward.defeqAttrib.useBackward true in
/-- Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.fromCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Functor (CategoryTheory.Cost
ructuredArrow (CategoryTheory.Functor.const J) F)             (CategoryTheory.Li
mits.Cone F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.CostructuredArrow (CategoryTheo
ry.Functor.const J) F；CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part o
f an
    equivalence, see `Cone.equivCostructuredArrow`.
-/
def Cone.fromCostructuredArrow (F : J ⥤ C) : CostructuredArrow (const J) F ⥤ Cone F where
  obj c := ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j => by
        convert! congr_fun (congr_arg NatTrans.app f.w) j
        simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is the constant
    functor. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.equivCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Limits.Cone F ≌ CategoryTheo
ry.CostructuredArrow (CategoryTheory.Functor.const J) F
参数：F : CategoryTheory.Functor J C；CategoryTheory.Functor.const J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is 
the constant
    functor.
-/
def Cone.equivCostructuredArrow (F : J ⥤ C) : Cone F ≌ CostructuredArrow (const J) F where
  functor := Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cone.eta
  counitIso := NatIso.ofComponents fun _ => (CostructuredArrow.eta _).symm

/-- A cone is a limit cone iff it is terminal. -/
/-
**CategoryTheory.Limits.Cone.isLimitEquivIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cone F) → Catego
ryTheory.Limits.IsLimit c ≃ CategoryTheory.Limits.IsTerminal c
参数：c : CategoryTheory.Limits.Cone F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A cone is a limit cone iff it is terminal.
-/
def Cone.isLimitEquivIsTerminal {F : J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c :=
  IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ => IsTerminal.ofUnique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
/-
**CategoryTheory.Limits.hasLimit_iff_hasTerminal_cone** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone
 F)
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F) :=
  ⟨fun _ => (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h =>
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩
/-
**CategoryTheory.Limits.hasLimitsOfShape_iff_isLeftAdjoint_const** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_iff_isLeftAdjoint_const : HasLimitsOfShape J C ↔ IsLeftAd
joint (const J : C ⥤ _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimitsOfShape.has_limit`：∀ {J : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} J} {C : Type u} {inst_1 : CategoryTheory.Cate
gory.{v, u} C}   [self : CategoryTheor…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_hasTerminal_cone`：hasLimit_iff_hasTer
minal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F)
· 使用定理 `CategoryTheory.Equivalence.hasTerminal_iff`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (e : C ≌ D), Categ…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.isLeftAdjoint_iff_hasTerminal_costructuredArrow`：isLeftAd
joint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} : F.IsLeftAdjoint ↔ forall A
, HasTerminal (CostructuredArrow F A)
-/
theorem hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ IsLeftAdjoint (const J : C ⥤ _) :=
  calc
    HasLimitsOfShape J C ↔ ∀ F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.has_limit, fun h => HasLimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ ∀ F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (forall_congr' fun F => (Cone.equivCostructuredArrow F).hasTerminal_iff)
    _ ↔ (IsLeftAdjoint (const J : C ⥤ _)) :=
      isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm
/-
**CategoryTheory.Limits.IsLimit.liftConeMorphism_eq_isTerminal_from** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.IsLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c : CategoryTheory.Limits.Cone F} (hc : CategoryTheory.Limits.IsLimit c)   (s 
: CategoryTheory.Limits.Cone F), hc.liftConeMorphism s = (c.isLimitEquivIsTermin
al hc).from s
参数：hc : CategoryTheory.Limits.IsLimit c；s : CategoryTheory.Limits.Cone F；c.isLim
itEquivIsTerminal hc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLimit.liftConeMorphism_eq_isTerminal_from {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (s : Cone F) : hc.liftConeMorphism s = IsTerminal.from (Cone.isLimitEquivIsTerminal _ hc) _ :=
  rfl
/-
**CategoryTheory.Limits.IsTerminal.from_eq_liftConeMorphism** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.IsTerminal`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c : CategoryTheory.Limits.Cone F} (hc : CategoryTheory.Limits.IsTerminal c)   
(s : CategoryTheory.Limits.Cone F), hc.from s = (c.isLimitEquivIsTerminal.symm h
c).liftConeMorphism s
参数：hc : CategoryTheory.Limits.IsTerminal c；s : CategoryTheory.Limits.Cone F；c.is
LimitEquivIsTerminal.symm hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.IsLimit.liftConeMorphism_eq_isTerminal_from`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem IsTerminal.from_eq_liftConeMorphism {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
    (s : Cone F) :
    IsTerminal.from hc s = ((Cone.isLimitEquivIsTerminal _).symm hc).liftConeMorphism s :=
  (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

/-- If `G : Cone F ⥤ Cone F'` preserves terminal objects, it preserves limit cones. -/
/-
**CategoryTheory.Limits.IsLimit.ofPreservesConeTerminal** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.IsLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             {D
 : Type u₄} →               [inst_3 : CategoryTheory.Category.{v₄, u₄} D] →     
            {F : CategoryTheory.Functor J C} →                   {F' : CategoryT
heory.Functor K D} →                     (G : CategoryTheory.Functor (CategoryTh
eory.Limits.Cone F) (CategoryTheory.Limits.Cone F')) →                       [Ca
tegoryTheory.Limits.PreservesLimit                             (CategoryTheory.F
unctor.empty (CategoryTheory.Limits.Cone F)) G] →                         {c : C
ategoryTheory.Limits.Cone F} →                           CategoryTheory.Limits.I
sLimit c → CategoryTheory.Limits.IsLimit (G.obj c)
参数：G : CategoryTheory.Functor (CategoryTheory.Limits.Cone F) (CategoryTheory.Lim
its.Cone F')；CategoryTheory.Functor.empty (CategoryTheory.Limits.Cone F)；G.obj c
。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `G : Cone F ⥤ Cone F'` preserves terminal objects, it preserves limit cones.
-/
noncomputable def IsLimit.ofPreservesConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [PreservesLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit c) : IsLimit (G.obj c) :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

/-- If `G : Cone F ⥤ Cone F'` reflects terminal objects, it reflects limit cones. -/
/-
**CategoryTheory.Limits.IsLimit.ofReflectsConeTerminal** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.IsLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             {D
 : Type u₄} →               [inst_3 : CategoryTheory.Category.{v₄, u₄} D] →     
            {F : CategoryTheory.Functor J C} →                   {F' : CategoryT
heory.Functor K D} →                     (G : CategoryTheory.Functor (CategoryTh
eory.Limits.Cone F) (CategoryTheory.Limits.Cone F')) →                       [Ca
tegoryTheory.Limits.ReflectsLimit (CategoryTheory.Functor.empty (CategoryTheory.
Limits.Cone F))                             G] →                         {c : Ca
tegoryTheory.Limits.Cone F} →                           CategoryTheory.Limits.Is
Limit (G.obj c) → CategoryTheory.Limits.IsLimit c
参数：G : CategoryTheory.Functor (CategoryTheory.Limits.Cone F) (CategoryTheory.Lim
its.Cone F')；CategoryTheory.Functor.empty (CategoryTheory.Limits.Cone F)；G.obj c
。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `G : Cone F ⥤ Cone F'` reflects terminal objects, it reflects limit cones.
-/
noncomputable def IsLimit.ofReflectsConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [ReflectsLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit (G.obj c)) : IsLimit c :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

/-- Given a cocone `c` over `F`, we can interpret the legs of `c` as costructured arrows
    `F.obj - ⟶ c.pt`. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) → Cate
goryTheory.Functor J (CategoryTheory.CostructuredArrow F c.pt)
参数：c : CategoryTheory.Limits.Cocone F；CategoryTheory.CostructuredArrow F c.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone `c` over `F`, we can interpret the legs of `c` as costructured ar
rows
    `F.obj - ⟶ c.pt`.
-/
def Cocone.toCostructuredArrow {F : J ⥤ C} (c : Cocone F) : J ⥤ CostructuredArrow F c.pt where
  obj j := CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

/-- If `F` has a colimit, then the colimit inclusions can be interpreted as costructured arrows
    `F.obj - ⟶ colimit F`. -/
@[simps]
/-
**CategoryTheory.Limits.colimit.toCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasColimit 
F] →             CategoryTheory.Functor J (CategoryTheory.CostructuredArrow F (C
ategoryTheory.Limits.colimit F))
参数：F : CategoryTheory.Functor J C；CategoryTheory.CostructuredArrow F (CategoryTh
eory.Limits.colimit F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a colimit, then the colimit inclusions can be interpreted as costruct
ured arrows
    `F.obj - ⟶ colimit F`.
-/
noncomputable def colimit.toCostructuredArrow (F : J ⥤ C) [HasColimit F] :
    J ⥤ CostructuredArrow F (colimit F) where
  obj j := CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

set_option backward.isDefEq.respectTransparency.types false in
/-- `Cocone.toCostructuredArrow` can be expressed in terms of `Functor.toCostructuredArrow`. -/
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrowIsoToCostructuredArrow** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →     
        c.toCostructuredArrow ≅ (CategoryTheory.Functor.id J).toCostructuredArro
w F c.pt c.ι.app ⋯
参数：c : CategoryTheory.Limits.Cocone F；CategoryTheory.Functor.id J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cocone.toCostructuredArrow` can be expressed in terms of `Functor.toCostructure
dArrow`.
-/
def Cocone.toCostructuredArrowIsoToCostructuredArrow {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ≅ (𝟭 J).toCostructuredArrow F c.pt c.ι.app (by simp) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Functor.toCostructuredArrow` can be expressed in terms of `Cocone.toCostructuredArrow`. -/
/-
**CategoryTheory.Limits._root_.CategoryTheory.Functor.toCostructuredArrowIsoToCo
structuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.toCostructuredArrow` can be expressed in terms of `Cocone.toCostructure
dArrow`.
-/
def _root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow (G : J ⥤ K)
    (F : K ⥤ C) (X : C) (f : (Y : J) → F.obj (G.obj Y) ⟶ X)
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ≅
      (Cocone.mk X ⟨f, by simp [h]⟩).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _ :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Interpreting the legs of a cocone as a costructured arrow and then forgetting the arrow again
    does nothing. -/
@[simps!]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrowCompProj** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →     
        c.toCostructuredArrow.comp (CategoryTheory.CostructuredArrow.proj F c.pt
) ≅ CategoryTheory.Functor.id J
参数：c : CategoryTheory.Limits.Cocone F；CategoryTheory.CostructuredArrow.proj F c.
pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpreting the legs of a cocone as a costructured arrow and then forgetting th
e arrow again
    does nothing.
-/
def Cocone.toCostructuredArrowCompProj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrow_comp_proj** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 (c : CategoryTheory.Limits.Cocone F),   c.toCostructuredArrow.comp (CategoryThe
ory.CostructuredArrow.proj F c.pt) = CategoryTheory.Functor.id J
参数：c : CategoryTheory.Limits.Cocone F；CategoryTheory.CostructuredArrow.proj F c.
pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cocone.toCostructuredArrow_comp_proj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ = 𝟭 J :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Interpreting the legs of a cocone as a costructured arrow, interpreting this arrow as an arrow
    over the cocone point, and finally forgetting the arrow is the same as just applying the
    functor the cocone was over. -/
@[simps!]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrowCompToOverCompForget** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →     
        c.toCostructuredArrow.comp                 ((CategoryTheory.Costructured
Arrow.toOver F c.pt).comp (CategoryTheory.Over.forget c.pt)) ≅               F
参数：c : CategoryTheory.Limits.Cocone F；(CategoryTheory.CostructuredArrow.toOver F
 c.pt).comp (CategoryTheory.Over.forget c.pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpreting the legs of a cocone as a costructured arrow, interpreting this arr
ow as an arrow
    over the cocone point, and finally forgetting the arrow is the same as just 
applying the
    functor the cocone was over.
-/
def Cocone.toCostructuredArrowCompToOverCompForget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ ≅ F :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrow_comp_toOver_comp_forget** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 (c : CategoryTheory.Limits.Cocone F),   c.toCostructuredArrow.comp ((CategoryTh
eory.CostructuredArrow.toOver F c.pt).comp (CategoryTheory.Over.forget c.pt)) = 
    F
参数：c : CategoryTheory.Limits.Cocone F；(CategoryTheory.CostructuredArrow.toOver F
 c.pt).comp (CategoryTheory.Over.forget c.pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cocone.toCostructuredArrow_comp_toOver_comp_forget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ = F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A cocone `c` on `F : J ⥤ C` lifts to a cocone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.toOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) →     
        CategoryTheory.Limits.Cocone (c.toCostructuredArrow.comp (CategoryTheory
.CostructuredArrow.toOver F c.pt))
参数：c : CategoryTheory.Limits.Cocone F；c.toCostructuredArrow.comp (CategoryTheory
.CostructuredArrow.toOver F c.pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone `c` on `F : J ⥤ C` lifts to a cocone in `Over c.pt` with cone point `𝟙 
c.pt`.
-/
def Cocone.toOver {F : J ⥤ C} (c : Cocone F) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 c.pt)
  ι := { app := fun j => Over.homMk (c.ι.app j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The colimit cocone for `F : J ⥤ C` lifts to a cocone in `Over (colimit F)` with cone point
    `𝟙 (colimit F)`. This is automatically also a colimit cocone. -/
@[simps]
/-
**CategoryTheory.Limits.colimit.toOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasColimit 
F] →             CategoryTheory.Limits.Cocone               ((CategoryTheory.Lim
its.colimit.toCostructuredArrow F).comp                 (CategoryTheory.Costruct
uredArrow.toOver F (CategoryTheory.Limits.colimit F)))
参数：F : CategoryTheory.Functor J C；(CategoryTheory.Limits.colimit.toCostructuredA
rrow F).comp                 (CategoryTheory.CostructuredArrow.toOver F (Categor
yTheory.Limits.colimit F))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for `F : J ⥤ C` lifts to a cocone in `Over (colimit F)` with 
cone point
    `𝟙 (colimit F)`. This is automatically also a colimit cocone.
-/
noncomputable def colimit.toOver (F : J ⥤ C) [HasColimit F] :
    Cocone (colimit.toCostructuredArrow F ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 (colimit F))
  ι := { app := fun j => Over.homMk (colimit.ι F j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
/-- `c.toOver` is a lift of `c` under the forgetful functor. -/
@[simps!]
/-
**CategoryTheory.Limits.Cocone.mapCoconeToOver** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) → (Cat
egoryTheory.Over.forget c.pt).mapCocone c.toOver ≅ c
参数：c : CategoryTheory.Limits.Cocone F；CategoryTheory.Over.forget c.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c.toOver` is a lift of `c` under the forgetful functor.
-/
def Cocone.mapCoconeToOver {F : J ⥤ C} (c : Cocone F) : (Over.forget c.pt).mapCocone c.toOver ≅ c :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a diagram `CostructuredArrow F X`s, we may obtain a cocone with cone point `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.Cocone.fromCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {D : Typ
e u₄} →           [inst_2 : CategoryTheory.Category.{v₄, u₄} D] →             (F
 : CategoryTheory.Functor C D) →               {X : D} →                 (G : Ca
tegoryTheory.Functor J (CategoryTheory.CostructuredArrow F X)) →                
   CategoryTheory.Limits.Cocone (G.comp ((CategoryTheory.CostructuredArrow.proj 
F X).comp F))
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor J (CategoryTheory.C
ostructuredArrow F X)；G.comp ((CategoryTheory.CostructuredArrow.proj F X).comp F
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a diagram `CostructuredArrow F X`s, we may obtain a cocone with cone point
 `X`.
-/
def Cocone.fromCostructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X) :
    Cocone (G ⋙ CostructuredArrow.proj F X ⋙ F) where
  pt := X
  ι := { app := fun j => (G.obj j).hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a cocone `c : Cocone K` and a map `f : F.obj c.X ⟶ X`, we can construct a cocone of
    costructured arrows over `X` with `f` as the cone point. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.toCostructuredArrowCocone** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {D : Typ
e u₄} →           [inst_2 : CategoryTheory.Category.{v₄, u₄} D] →             {K
 : CategoryTheory.Functor J C} →               (c : CategoryTheory.Limits.Cocone
 K) →                 (F : CategoryTheory.Functor C D) →                   {X : 
D} →                     (f : F.obj c.pt ⟶ X) →                       CategoryTh
eory.Limits.Cocone                         ((F.mapCocone c).toCostructuredArrow.
comp                           ((CategoryTheory.CostructuredArrow.map f).comp (C
ategoryTheory.CostructuredArrow.pre K F X)))
参数：c : CategoryTheory.Limits.Cocone K；F : CategoryTheory.Functor C D；f : F.obj c
.pt ⟶ X；(F.mapCocone c).toCostructuredArrow.comp                           ((Cat
egoryTheory.CostructuredArrow.map f).comp (CategoryTheory.CostructuredArrow.pre 
K F X))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone `c : Cocone K` and a map `f : F.obj c.X ⟶ X`, we can construct a 
cocone of
    costructured arrows over `X` with `f` as the cone point.
-/
def Cocone.toCostructuredArrowCocone {K : J ⥤ C} (c : Cocone K) (F : C ⥤ D) {X : D}
    (f : F.obj c.pt ⟶ X) : Cocone ((F.mapCocone c).toCostructuredArrow ⋙
      CostructuredArrow.map f ⋙ CostructuredArrow.pre _ _ _) where
  pt := CostructuredArrow.mk f
  ι := { app := fun j => CostructuredArrow.homMk (c.ι.app j) rfl }

set_option backward.defeqAttrib.useBackward true in
/-- Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.toStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Functor (CategoryTheory.Limi
ts.Cocone F)             (CategoryTheory.StructuredArrow F (CategoryTheory.Funct
or.const J))
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.Cocone F；CategoryTheory.
StructuredArrow F (CategoryTheory.Functor.const J)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part
 of an
    equivalence, see `Cocone.equivStructuredArrow`.
-/
def Cocone.toStructuredArrow (F : J ⥤ C) : Cocone F ⥤ StructuredArrow F (const J) where
  obj c := StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

set_option backward.defeqAttrib.useBackward true in
/-- Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.fromStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Functor (CategoryTheory.Stru
cturedArrow F (CategoryTheory.Functor.const J))             (CategoryTheory.Limi
ts.Cocone F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.StructuredArrow F (CategoryTheo
ry.Functor.const J)；CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part
 of an
    equivalence, see `Cocone.equivStructuredArrow`.
-/
def Cocone.fromStructuredArrow (F : J ⥤ C) : StructuredArrow F (const J) ⥤ Cocone F where
  obj c := ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w j := by simp [dsimp% congr_app f.w j] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` is the constant
    functor. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.equivStructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         (F : Cat
egoryTheory.Functor J C) →           CategoryTheory.Limits.Cocone F ≌ CategoryTh
eory.StructuredArrow F (CategoryTheory.Functor.const J)
参数：F : CategoryTheory.Functor J C；CategoryTheory.Functor.const J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` i
s the constant
    functor.
-/
def Cocone.equivStructuredArrow (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (const J) where
  functor := Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocone.eta
  counitIso := NatIso.ofComponents fun _ => (StructuredArrow.eta _).symm

/-- A cocone is a colimit cocone iff it is initial. -/
/-
**CategoryTheory.Limits.Cocone.isColimitEquivIsInitial** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Cocone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           (c : CategoryTheory.Limits.Cocone F) → Cate
goryTheory.Limits.IsColimit c ≃ CategoryTheory.Limits.IsInitial c
参数：c : CategoryTheory.Limits.Cocone F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A cocone is a colimit cocone iff it is initial.
-/
def Cocone.isColimitEquivIsInitial {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c :=
  IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ => IsInitial.ofUnique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
/-
**CategoryTheory.Limits.hasColimit_iff_hasInitial_cocone** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (
Cocone F)
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F) :=
  ⟨fun _ => (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h =>
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩
/-
**CategoryTheory.Limits.hasColimitsOfShape_iff_isRightAdjoint_const** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_iff_isRightAdjoint_const : HasColimitsOfShape J C ↔ IsR
ightAdjoint (const J : C ⥤ _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimitsOfShape.has_colimit`：∀ {J : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} J} {C : Type u} {inst_1 : CategoryTheory.
Category.{v, u} C}   [self : CategoryTheor…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_hasInitial_cocone`：hasColimit_iff_h
asInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F)
· 使用定理 `CategoryTheory.Equivalence.hasInitial_iff`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (e : C ≌ D), Categ…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.isRightAdjoint_iff_hasInitial_structuredArrow`：isRightAdj
oint_iff_hasInitial_structuredArrow {G : D ⥤ C} : G.IsRightAdjoint ↔ forall A, H
asInitial (StructuredArrow A G)
-/
theorem hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ IsRightAdjoint (const J : C ⥤ _) :=
  calc
    HasColimitsOfShape J C ↔ ∀ F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.has_colimit, fun h => HasColimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ ∀ F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
      (forall_congr' fun F => (Cocone.equivStructuredArrow F).hasInitial_iff)
    _ ↔ (IsRightAdjoint (const J : C ⥤ _)) :=
      isRightAdjoint_iff_hasInitial_structuredArrow.symm
/-
**CategoryTheory.Limits.IsColimit.descCoconeMorphism_eq_isInitial_to** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Limits.IsColimit c)  
 (s : CategoryTheory.Limits.Cocone F), hc.descCoconeMorphism s = (c.isColimitEqu
ivIsInitial hc).to s
参数：hc : CategoryTheory.Limits.IsColimit c；s : CategoryTheory.Limits.Cocone F；c.i
sColimitEquivIsInitial hc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsColimit.descCoconeMorphism_eq_isInitial_to {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    hc.descCoconeMorphism s = IsInitial.to (Cocone.isColimitEquivIsInitial _ hc) _ :=
  rfl
/-
**CategoryTheory.Limits.IsInitial.to_eq_descCoconeMorphism** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Limits.IsInitial c)  
 (s : CategoryTheory.Limits.Cocone F), hc.to s = (c.isColimitEquivIsInitial.symm
 hc).descCoconeMorphism s
参数：hc : CategoryTheory.Limits.IsInitial c；s : CategoryTheory.Limits.Cocone F；c.i
sColimitEquivIsInitial.symm hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.IsColimit.descCoconeMorphism_eq_isInitial_to`：∀ {J
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : 
CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem IsInitial.to_eq_descCoconeMorphism {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
    (s : Cocone F) :
    IsInitial.to hc s = ((Cocone.isColimitEquivIsInitial _).symm hc).descCoconeMorphism s :=
  (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

/-- If `G : Cocone F ⥤ Cocone F'` preserves initial objects, it preserves colimit cocones. -/
/-
**CategoryTheory.Limits.IsColimit.ofPreservesCoconeInitial** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             {D
 : Type u₄} →               [inst_3 : CategoryTheory.Category.{v₄, u₄} D] →     
            {F : CategoryTheory.Functor J C} →                   {F' : CategoryT
heory.Functor K D} →                     (G : CategoryTheory.Functor (CategoryTh
eory.Limits.Cocone F) (CategoryTheory.Limits.Cocone F')) →                      
 [CategoryTheory.Limits.PreservesColimit                             (CategoryTh
eory.Functor.empty (CategoryTheory.Limits.Cocone F)) G] →                       
  {c : CategoryTheory.Limits.Cocone F} →                           CategoryTheor
y.Limits.IsColimit c → CategoryTheory.Limits.IsColimit (G.obj c)
参数：G : CategoryTheory.Functor (CategoryTheory.Limits.Cocone F) (CategoryTheory.L
imits.Cocone F')；CategoryTheory.Functor.empty (CategoryTheory.Limits.Cocone F)；G
.obj c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `G : Cocone F ⥤ Cocone F'` preserves initial objects, it preserves colimit co
cones.
-/
noncomputable def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
  (Cocone.isColimitEquivIsInitial _).symm <| (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

/-- If `G : Cocone F ⥤ Cocone F'` reflects initial objects, it reflects colimit cocones. -/
/-
**CategoryTheory.Limits.IsColimit.ofReflectsCoconeInitial** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             {D
 : Type u₄} →               [inst_3 : CategoryTheory.Category.{v₄, u₄} D] →     
            {F : CategoryTheory.Functor J C} →                   {F' : CategoryT
heory.Functor K D} →                     (G : CategoryTheory.Functor (CategoryTh
eory.Limits.Cocone F) (CategoryTheory.Limits.Cocone F')) →                      
 [CategoryTheory.Limits.ReflectsColimit                             (CategoryThe
ory.Functor.empty (CategoryTheory.Limits.Cocone F)) G] →                        
 {c : CategoryTheory.Limits.Cocone F} →                           CategoryTheory
.Limits.IsColimit (G.obj c) → CategoryTheory.Limits.IsColimit c
参数：G : CategoryTheory.Functor (CategoryTheory.Limits.Cocone F) (CategoryTheory.L
imits.Cocone F')；CategoryTheory.Functor.empty (CategoryTheory.Limits.Cocone F)；G
.obj c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `G : Cocone F ⥤ Cocone F'` reflects initial objects, it reflects colimit coco
nes.
-/
noncomputable def IsColimit.ofReflectsCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [ReflectsColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit (G.obj c)) :
    IsColimit c :=
  (Cocone.isColimitEquivIsInitial _).symm <|
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

end CategoryTheory.Limits

