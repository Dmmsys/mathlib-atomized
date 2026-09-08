/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Chosen pullbacks along a morphism

## Main declarations

- `ChosenPullbacksAlong` : For a morphism `f : Y ⟶ X` in `C`, the type class
  `ChosenPullbacksAlong f` provides the data of a pullback functor `Over X ⥤ Over Y`
  as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullbacksAlong` has good closure properties: isos have chosen pullbacks,
  and composition of morphisms with chosen pullbacks have chosen pullbacks.

- We prove that chosen pullbacks yield usual pullbacks: `ChosenPullbacksAlong.isPullback`
  proves that for morphisms `f` and `g` with the same codomain, the object
  `ChosenPullbacksAlong.pullbackObj f g` together with morphisms
  `ChosenPullbacksAlong.fst f g` and `ChosenPullbacksAlong.snd f g` form a pullback square
  over `f` and `g`.

- We prove that in cartesian monoidal categories, morphisms to the terminal tensor unit and
  the product projections have chosen pullbacks.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory Over

variable {C : Type u₁} [Category.{v₁} C]

/-- A functorial choice of pullbacks along a morphism `f : Y ⟶ X` in `C` given by a functor
`Over X ⥤ Over Y` which is a right adjoint to the functor `Over.map f`. -/
/-
**CategoryTheory.ChosenPullbacksAlong** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {Y X : C} → 
(Y ⟶ X) → Type (max u₁ v₁)
参数：Y ⟶ X；max u₁ v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functorial choice of pullbacks along a morphism `f : Y ⟶ X` in `C` given by a 
functor
`Over X ⥤ Over Y` which is a right adjoint to the functor `Over.map f`.
-/
class ChosenPullbacksAlong {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

variable (C) in
/-- A category has chosen pullbacks if every morphism has a chosen pullback. -/
/-
**CategoryTheory.ChosenPullbacks** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ChosenPullbacks
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has chosen pullbacks if every morphism has a chosen pullback.
-/
abbrev ChosenPullbacks := Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

namespace ChosenPullbacksAlong

/-- Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPullbacksAlong`. -/
@[simps, instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.ofHasPullbacksAlong** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] : ChosenPu
llbacksAlong f where pullback
参数：f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPull
backsAlong`.
-/
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] :
    ChosenPullbacksAlong f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- The identity morphism has a functorial choice of pullbacks. -/
@[instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ChosenPullbacksAlong`。
形式化陈述：id (X : C) : ChosenPullbacksAlong (𝟙 X) where pullback
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism has a functorial choice of pullbacks.
-/
def id (X : C) : ChosenPullbacksAlong (𝟙 X) where
  pullback := 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

/-- Any chosen pullback functor of the identity morphism is naturally isomorphic to the identity
functor. -/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackId (X : C) [ChosenPullbacksAlong (𝟙 X)] : pullback (𝟙 X) ≅ 𝟭 (Over
 X)
参数：X : C；𝟙 X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any chosen pullback functor of the identity morphism is naturally isomorphic to 
the identity
functor.
-/
def pullbackId (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    pullback (𝟙 X) ≅ 𝟭 (Over X) :=
  (mapPullbackAdj (𝟙 X)).rightAdjointUniq (id X).mapPullbackAdj

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.unit_pullbackId_hom_app** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：unit_pullbackId_hom_app (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X) 
: (mapPullbackAdj (𝟙 X)).unit.app Y ≫ (pullbackId X).hom.app ((Over.map (𝟙 X)).o
bj Y) = (id X).mapPullbackAdj.unit.app Y
参数：X : C；𝟙 X；Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackId.eq_1`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] (X : C)   [inst_1 : CategoryTheory.Chos
enPullbacksAlong (CategoryTheory.Category…
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`：unit_rightAdjoi
ntUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : C)
 : adj1.unit.app x ≫ (rightAdjointUniq adj1 a…
-/
theorem unit_pullbackId_hom_app (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X) :
    (mapPullbackAdj (𝟙 X)).unit.app Y ≫ (pullbackId X).hom.app ((Over.map (𝟙 X)).obj Y) =
      (id X).mapPullbackAdj.unit.app Y := by
  rw [pullbackId, Adjunction.unit_rightAdjointUniq_hom_app]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.unit_pullbackId_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：unit_pullbackId_hom (X : C) [ChosenPullbacksAlong (𝟙 X)] : (mapPullbackAdj
 (𝟙 X)).unit ≫ (Over.map (𝟙 X)).whiskerLeft (pullbackId X).hom = (id X).mapPullb
ackAdj.unit
参数：X : C；𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackId.eq_1`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] (X : C)   [inst_1 : CategoryTheory.Chos
enPullbacksAlong (CategoryTheory.Category…
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom`：unit_rightAdjointUn
iq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : adj1.unit ≫ w
hiskerLeft F (rightAdjointUniq adj1 adj2)…
-/
theorem unit_pullbackId_hom (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    (mapPullbackAdj (𝟙 X)).unit ≫ (Over.map (𝟙 X)).whiskerLeft (pullbackId X).hom =
      (id X).mapPullbackAdj.unit := by
  rw [pullbackId, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackId_hom_counit** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackId_hom_counit (X : C) [ChosenPullbacksAlong (𝟙 X)] : Functor.whisk
erRight (pullbackId X).hom (Over.map (𝟙 X)) ≫ (id X).mapPullbackAdj.counit = (ma
pPullbackAdj (𝟙 X)).counit
参数：X : C；𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_counit`：rightAdjointUniq_
hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : whiskerRi
ght (rightAdjointUniq adj1 adj2).hom F ≫ ad…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackId.eq_1`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] (X : C)   [inst_1 : CategoryTheory.Chos
enPullbacksAlong (CategoryTheory.Category…
-/
theorem pullbackId_hom_counit (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    Functor.whiskerRight (pullbackId X).hom (Over.map (𝟙 X)) ≫ (id X).mapPullbackAdj.counit =
      (mapPullbackAdj (𝟙 X)).counit := by
  have := Adjunction.rightAdjointUniq_hom_counit (mapPullbackAdj (𝟙 X)) (id X).mapPullbackAdj
  rw [pullbackId, Adjunction.rightAdjointUniq_hom_counit]

set_option backward.defeqAttrib.useBackward true in
/-- Every isomorphism has a functorial choice of pullbacks. -/
@[simps, instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ChosenPullbacksAlong`。
形式化陈述：iso {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.hom where pullback.obj 
Z
参数：f : Y ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every isomorphism has a functorial choice of pullbacks.
-/
def iso {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.hom where
  pullback.obj Z := Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

/-- The inverse of an isomorphism has a functorial choice of pullbacks. -/
@[simps!, instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.isoInv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ChosenPullbacksAlong`。
形式化陈述：isoInv {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.inv
参数：f : Y ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an isomorphism has a functorial choice of pullbacks.
-/
def isoInv {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.inv := iso f.symm

/-- The composition of morphisms with chosen pullbacks has a chosen pullback. -/
@[instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ChosenPullbacksAlong`。
形式化陈述：comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [ChosenPullbacksAlong f] [ChosenP
ullbacksAlong g] : ChosenPullbacksAlong (f ≫ g) where pullback
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms with chosen pullbacks has a chosen pullback.
-/
def comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] : ChosenPullbacksAlong (f ≫ g) where
  pullback := pullback g ⋙ pullback f
  mapPullbackAdj := ((mapPullbackAdj f).comp (mapPullbackAdj g)).ofNatIsoLeft
    (Over.mapComp f g).symm

/-- Any chosen pullback of a composite of morphisms is naturally isomorphic to the composition of
chosen pullback functors. -/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [ChosenPullbacksAlong f] 
[ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] : pullback (f ≫ g) ≅ pul
lback g ⋙ pullback f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any chosen pullback of a composite of morphisms is naturally isomorphic to the c
omposition of
chosen pullback functors.
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj (f ≫ g)) ((comp f g).mapPullbackAdj)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.unit_pullbackComp_hom** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：unit_pullbackComp_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [ChosenPullbacks
Along f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] : (mapPullbackA
dj (f ≫ g)).unit ≫ (Over.map (f ≫ g)).whiskerLeft (pullbackComp f g).hom = (comp
 f g).mapPullbackAdj.unit
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackComp.eq_1`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)  
 [inst_1 : CategoryTheory.ChosenPullbacksAl…
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom`：unit_rightAdjointUn
iq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : adj1.unit ≫ w
hiskerLeft F (rightAdjointUniq adj1 adj2)…
-/
theorem unit_pullbackComp_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    (mapPullbackAdj (f ≫ g)).unit ≫ (Over.map (f ≫ g)).whiskerLeft (pullbackComp f g).hom =
      (comp f g).mapPullbackAdj.unit := by
  rw [pullbackComp, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackComp_hom_counit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackComp_hom_counit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [ChosenPullbac
ksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] : Functor.whi
skerRight (pullbackComp f g).hom (Over.map (f ≫ g)) ≫ (comp f g).mapPullbackAdj.
counit = (mapPullbackAdj (f ≫ g)).counit
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackComp.eq_1`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)  
 [inst_1 : CategoryTheory.ChosenPullbacksAl…
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_counit`：rightAdjointUniq_
hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : whiskerRi
ght (rightAdjointUniq adj1 adj2).hom F ≫ ad…
-/
theorem pullbackComp_hom_counit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    Functor.whiskerRight (pullbackComp f g).hom (Over.map (f ≫ g)) ≫
      (comp f g).mapPullbackAdj.counit =
      (mapPullbackAdj (f ≫ g)).counit := by
  rw [pullbackComp, Adjunction.rightAdjointUniq_hom_counit]

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, any morphism to the terminal tensor unit has a functorial
choice of pullbacks. -/
@[instance_reducible, simps]
/-
**CategoryTheory.ChosenPullbacksAlong.cartesianMonoidalCategoryToUnit** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：cartesianMonoidalCategoryToUnit [CartesianMonoidalCategory C] {X : C} (f :
 X ⟶ 𝟙_ C) : ChosenPullbacksAlong f where pullback.obj Y
参数：f : X ⟶ 𝟙_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In cartesian monoidal categories, any morphism to the terminal tensor unit has a
 functorial
choice of pullbacks.
-/
def cartesianMonoidalCategoryToUnit [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullbacksAlong f where
  pullback.obj Y := Over.mk (snd Y.left X)
  pullback.map {Y Z} g := Over.homMk (g.left ▷ X)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, the first product projections `fst` have a functorial choice
of pullbacks. -/
@[simps, instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.cartesianMonoidalCategoryFst** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：cartesianMonoidalCategoryFst [CartesianMonoidalCategory C] (X Y : C) : Cho
senPullbacksAlong (fst X Y : X otimes Y ⟶ X) where pullback.obj Z
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In cartesian monoidal categories, the first product projections `fst` have a fun
ctorial choice
of pullbacks.
-/
def cartesianMonoidalCategoryFst [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (fst X Y : X ⊗ Y ⟶ X) where
  pullback.obj Z := Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, the second product projections `snd` have a functorial choice
of pullbacks. -/
@[simps, instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.cartesianMonoidalCategorySnd** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] (X Y : C) : Cho
senPullbacksAlong (snd X Y : X otimes Y ⟶ Y) where pullback.obj Z
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In cartesian monoidal categories, the second product projections `snd` have a fu
nctorial choice
of pullbacks.
-/
def cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (snd X Y : X ⊗ Y ⟶ Y) where
  pullback.obj Z := Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

section PullbackFromChosenPullbacksAlongs

variable {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullbacksAlong g]

/-- The underlying object of the chosen pullback along `g` of `f`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of the chosen pullback along `g` of `f`.
-/
abbrev pullbackObj : C := ((pullback g).obj (Over.mk f)).left

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk f`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.fst'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.ChosenPullbacksAlong`。
形式化陈述：fst' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk f`.
-/
abbrev fst' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f :=
  (mapPullbackAdj g).counit.app <| Over.mk f

/-- The first projection from the chosen pullback along `g` of `f` to the domain of `f`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ChosenPullbacksAlong`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {Y Z X
 : C} →       (f : Y ⟶ X) →         (g : Z ⟶ X) →           [inst_1 : CategoryTh
eory.ChosenPullbacksAlong g] → CategoryTheory.ChosenPullbacksAlong.pullbackObj f
 g ⟶ Y
参数：f : Y ⟶ X；g : Z ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the chosen pullback along `g` of `f` to the domain of 
`f`.
-/
abbrev fst : pullbackObj f g ⟶ Y := fst' f g |>.left
/-
**CategoryTheory.ChosenPullbacksAlong.fst'_left** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ChosenPullbacksAlong`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} (f
 : Y ⟶ X) (g : Z ⟶ X)   [inst_1 : CategoryTheory.ChosenPullbacksAlong g],   Cate
goryTheory.Over.Hom.left (CategoryTheory.ChosenPullbacksAlong.fst' f g) =     Ca
tegoryTheory.ChosenPullbacksAlong.fst f g
参数：f : Y ⟶ X；g : Z ⟶ X；CategoryTheory.ChosenPullbacksAlong.fst' f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst'_left : (fst' f g).left = fst f g := rfl

/-- The second projection from the chosen pullback along `g` of `f` to the domain of `g`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ChosenPullbacksAlong`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {Y Z X
 : C} →       (f : Y ⟶ X) →         (g : Z ⟶ X) →           [inst_1 : CategoryTh
eory.ChosenPullbacksAlong g] → CategoryTheory.ChosenPullbacksAlong.pullbackObj f
 g ⟶ Z
参数：f : Y ⟶ X；g : Z ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the chosen pullback along `g` of `f` to the domain of
 `g`.
-/
abbrev snd : pullbackObj f g ⟶ Z := (pullback g).obj (Over.mk f) |>.hom

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk g`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.snd'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.ChosenPullbacksAlong`。
形式化陈述：snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk g`.
-/
abbrev snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g) :=
  Over.homMk (snd f g)
/-
**CategoryTheory.ChosenPullbacksAlong.snd'_left** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ChosenPullbacksAlong`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} (f
 : Y ⟶ X) (g : Z ⟶ X)   [inst_1 : CategoryTheory.ChosenPullbacksAlong g],   Cate
goryTheory.Over.Hom.left (CategoryTheory.ChosenPullbacksAlong.snd' f g) =     Ca
tegoryTheory.ChosenPullbacksAlong.snd f g
参数：f : Y ⟶ X；g : Z ⟶ X；CategoryTheory.ChosenPullbacksAlong.snd' f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd'_left : (snd' f g).left = snd f g := rfl

variable {f g}

@[reassoc]
/-
**CategoryTheory.ChosenPullbacksAlong.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ChosenPullbacksAlong`。
形式化陈述：condition : fst f g ≫ f = snd f g ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem condition : fst f g ≫ f = snd f g ≫ g :=
  Over.w (fst' f g)

variable (f g) in
@[ext]
/-
**CategoryTheory.ChosenPullbacksAlong.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ChosenPullbacksAlong`。
形式化陈述：hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fs
t _ _) (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) : φ₁ = φ₂
参数：h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _；h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Over.forget_faithful`：∀ {T : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Over.forget X).Faithful
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
    (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) :
    φ₁ = φ₂ := by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using! h₂.symm)
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    apply (Over.forget X).map_injective
    simpa using! h₁
  exact congr_arg CommaMorphism.left this

section Lift

variable {W : C} (a : W ⟶ Y) (b : W ⟶ Z) (h : a ≫ f = b ≫ g := by cat_disch)

set_option backward.privateInPublic true in
/-- Given morphisms `a : W ⟶ Y` and `b : W ⟶ Z` satisfying `a ≫ f = b ≫ g`,
constructs the unique morphism `W ⟶ pullbackObj f g` which lifts `a` and `b`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ChosenPullbacksAlong`。
形式化陈述：lift : W ⟶ pullbackObj f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given morphisms `a : W ⟶ Y` and `b : W ⟶ Z` satisfying `a ≫ f = b ≫ g`,
constructs the unique morphism `W ⟶ pullbackObj f g` which lifts `a` and `b`.
-/
def lift : W ⟶ pullbackObj f g :=
  (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ChosenPullbacksAlong`。
形式化陈述：lift_fst : lift a b h ≫ fst f g = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem lift_fst : lift a b h ≫ fst f g = a := by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  have : (Over.map g).map (adj.homEquiv (.mk b) (.mk f) (Over.homMk a)) ≫ fst' f g = a' := by
    simp only [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, adj, a']
  exact congr_arg CommaMorphism.left this

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ChosenPullbacksAlong`。
形式化陈述：lift_snd : lift a b h ≫ snd f g = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_snd : lift a b h ≫ snd f g = b := by
  simp [lift]

end Lift

section PullbackMap

variable (f g)

/-- The functoriality of `pullbackObj f g` in both arguments: Given a map from the pullback cospans
of `f' : Y' ⟶ X'` and `g' : Z' ⟶ X'` to the pullback cospan of `f : Y ⟶ X` and `g : Z ⟶ X`
as in the diagram below
```
Y' ⟶ Y
  ↘   ↘
  X' ⟶ X
  ↗   ↗
Z' ⟶ Z
```
if the morphisms `g'` and `g` both have chosen pullbacks, then we get an induced morphism
`pullbackMap f g f' g' comm₁ comm₂` from the chosen pullback of
`f' : Y' ⟶ X'` along `g'` to the chosen pullback of `f : Y ⟶ X` along `g`.
Here `comm₁` and `comm₂` are the commutativity conditions of the squares in the diagram above.
-/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackMap {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksA
long g'] (γ₁ : Y' ⟶ Y) (γ₂ : Z' ⟶ Z) (γ₃ : X' ⟶ X) (comm₁ : f' ≫ γ₃ = γ₁ ≫ f
参数：f' : Y' ⟶ X'；g' : Z' ⟶ X'；γ₁ : Y' ⟶ Y；γ₂ : Z' ⟶ Z；γ₃ : X' ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `pullbackObj f g` in both arguments: Given a map from the p
ullback cospans
of `f' : Y' ⟶ X'` and `g' : Z' ⟶ X'` to the pullback cospan of `f : Y ⟶ X` and `
g : Z ⟶ X`
as in the diagram below
```
Y' ⟶ Y
  ↘   ↘
  X' ⟶ X
  ↗   ↗
Z' ⟶ Z
```
if the morphisms `g'` and `g` both have chosen pullbacks, then we get an induced
 morphism
`pullbackMap f g f' g' comm₁ comm₂` from the chosen pullback of
`f' : Y' ⟶ X'` along `g'` to the chosen pullback of `f : Y ⟶ X` along `g`.
Here `comm₁` and `comm₂` are the commutativity conditions of the squares in the 
diagram above.
-/
def pullbackMap {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksAlong g']
    (γ₁ : Y' ⟶ Y) (γ₂ : Z' ⟶ Z) (γ₃ : X' ⟶ X)
    (comm₁ : f' ≫ γ₃ = γ₁ ≫ f := by cat_disch) (comm₂ : g' ≫ γ₃ = γ₂ ≫ g := by cat_disch) :
    pullbackObj f' g' ⟶ pullbackObj f g :=
  lift (fst f' g' ≫ γ₁) (snd f' g' ≫ γ₂)
    (by rw [assoc, ← comm₁, ← assoc, condition, assoc, comm₂, assoc])

variable {f g}

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackMap_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackMap_fst {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullba
cksAlong g'] {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.lift_fst`：lift_fst : lift a b h ≫ fs
t f g = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackMap_fst {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ fst f g = fst f' g' ≫ γ₁ := by
  simp only [pullbackMap, lift_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackMap_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackMap_snd {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullba
cksAlong g'] {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.lift_snd`：lift_snd : lift a b h ≫ sn
d f g = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackMap_snd {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ snd f g = snd f' g' ≫ γ₂ := by
  simp only [pullbackMap, lift_snd]

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackMap_id** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackMap_id : pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.hom_ext`：hom_ext {W : C} {φ₁ φ₂ : W 
⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _) (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ 
snd _ _) : φ₁ = φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_fst`：pullbackMap_fst {Y'
 Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g'] {γ₁ : Y' ⟶ Y
} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_snd`：pullbackMap_snd {Y'
 Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g'] {γ₁ : Y' ⟶ Y
} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm…
-/
theorem pullbackMap_id : pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackMap_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackMap_comp {Y' Z' X' Y'' Z'' X'' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} 
{f'' : Y'' ⟶ X''} {g'' : Z'' ⟶ X''} [ChosenPullbacksAlong g'] [ChosenPullbacksAl
ong g''] {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} {δ₁ : Y'' ⟶ Y'} {δ₂ : Z'' ⟶ Z
'} {δ₃ : X'' ⟶ X'} (comm₁ comm₂ comm₁' comm₂'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.hom_ext`：hom_ext {W : C} {φ₁ φ₂ : W 
⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _) (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ 
snd _ _) : φ₁ = φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_fst`：pullbackMap_fst {Y'
 Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g'] {γ₁ : Y' ⟶ Y
} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm…
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_fst_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} {f : Y ⟶ X} {g : Z ⟶ 
X}   [inst_1 : CategoryTheory.ChosenPullbacksAl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_snd`：pullbackMap_snd {Y'
 Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g'] {γ₁ : Y' ⟶ Y
} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm…
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.pullbackMap_snd_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} {f : Y ⟶ X} {g : Z ⟶ 
X}   [inst_1 : CategoryTheory.ChosenPullbacksAl…
-/
theorem pullbackMap_comp {Y' Z' X' Y'' Z'' X'' : C}
    {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} {f'' : Y'' ⟶ X''} {g'' : Z'' ⟶ X''}
    [ChosenPullbacksAlong g'] [ChosenPullbacksAlong g'']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X}
    {δ₁ : Y'' ⟶ Y'} {δ₂ : Z'' ⟶ Z'} {δ₃ : X'' ⟶ X'}
    (comm₁ comm₂ comm₁' comm₂' := by cat_disch) :
    pullbackMap f' g' f'' g'' δ₁ δ₂ δ₃ comm₁' comm₂' ≫
      pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ =
    pullbackMap f g f'' g'' (δ₁ ≫ γ₁) (δ₂ ≫ γ₂) (δ₃ ≫ γ₃)
      (by rw [reassoc_of% comm₁', comm₁, assoc]) (by rw [reassoc_of% comm₂', comm₂, assoc]) := by
  cat_disch

end PullbackMap

variable (f g)

/-- The canonical pullback cone from the data of a chosen pullback of `f` along `g`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackCone : PullbackCone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical pullback cone from the data of a chosen pullback of `f` along `g`.
-/
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (fst f g) (snd f g) (by rw [condition])
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackCone_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} (f
 : Y ⟶ X) (g : Z ⟶ X)   [inst_1 : CategoryTheory.ChosenPullbacksAlong g],   (Cat
egoryTheory.ChosenPullbacksAlong.pullbackCone f g).fst = CategoryTheory.ChosenPu
llbacksAlong.fst f g
参数：f : Y ⟶ X；g : Z ⟶ X；CategoryTheory.ChosenPullbacksAlong.pullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pullbackCone_fst : (pullbackCone f g).fst = fst f g := rfl
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackCone_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} (f
 : Y ⟶ X) (g : Z ⟶ X)   [inst_1 : CategoryTheory.ChosenPullbacksAlong g],   (Cat
egoryTheory.ChosenPullbacksAlong.pullbackCone f g).snd = CategoryTheory.ChosenPu
llbacksAlong.snd f g
参数：f : Y ⟶ X；g : Z ⟶ X；CategoryTheory.ChosenPullbacksAlong.pullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pullbackCone_snd : (pullbackCone f g).snd = snd f g := rfl

/-- The canonical pullback cone is a limit cone.
Note: this limit cone is computable as lifts are constructed from the data contained in the
`ChosenPullbackAlong` instance, contrary to `IsPullback.isLimit`, which constructs lifting data from
`CategoryTheory.Square.IsPullback` (a `Prop`). -/
/-
**CategoryTheory.ChosenPullbacksAlong.isLimitPullbackCone** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：isLimitPullbackCone : IsLimit (pullbackCone f g)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.condition`：condition : fst f g ≫ f =
 snd f g ≫ g
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
The canonical pullback cone is a limit cone.
Note: this limit cone is computable as lifts are constructed from the data conta
ined in the
`ChosenPullbackAlong` instance, contrary to `IsPullback.isLimit`, which construc
ts lifting data from
`CategoryTheory.Square.IsPullback` (a `Prop`).
-/
def isLimitPullbackCone :
    IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk condition (fun s ↦ lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)
/-
**CategoryTheory.ChosenPullbacksAlong.isPullback** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ChosenPullbacksAlong`。
形式化陈述：isPullback : IsPullback (fst f g) (snd f g) f g where w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.condition`：condition : fst f g ≫ f =
 snd f g ≫ g
-/
theorem isPullback : IsPullback (fst f g) (snd f g) f g where
  w := condition
  isLimit' := ⟨isLimitPullbackCone f g⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] condition in
/-- If `g` has a chosen pullback, then `Over.ChosenPullbacksAlong.fst f g` has a chosen pullback. -/
@[instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.chosenPullbacksAlongFst** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：chosenPullbacksAlongFst : ChosenPullbacksAlong (fst f g) where pullback.ob
j W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` has a chosen pullback, then `Over.ChosenPullbacksAlong.fst f g` has a cho
sen pullback.
-/
def chosenPullbacksAlongFst : ChosenPullbacksAlong (fst f g) where
  pullback.obj W := Over.mk (pullbackMap _ _ _ _ W.hom (𝟙 _) (𝟙 _))
  pullback.map {W' W} k := Over.homMk (lift (fst _ g ≫ k.left) (snd _ g)) _
  mapPullbackAdj.unit.app Q := Over.homMk (lift (𝟙 _) (Q.hom ≫ snd _ _))
  mapPullbackAdj.counit.app W := Over.homMk (fst _ g)
/-
**CategoryTheory.ChosenPullbacksAlong.hasPullbackAlong** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：hasPullbackAlong : HasPullbacksAlong g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.isPullback`：isPullback : IsPullback 
(fst f g) (snd f g) f g where w
-/
instance hasPullbackAlong : HasPullbacksAlong g := fun f => (isPullback f g).hasPullback
/-
**CategoryTheory.ChosenPullbacksAlong.hasPullbacks** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ChosenPullbacksAlong`。
形式化陈述：hasPullbacks [ChosenPullbacks C] : HasPullbacks C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan`：hasPullbacks_of_h
asLimit_cospan [forall {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g
)] : HasPullbacks C
-/
instance hasPullbacks [ChosenPullbacks C] : HasPullbacks C :=
  hasPullbacks_of_hasLimit_cospan _

/-- The computable `ChosenPullbacksAlong.pullback g` is naturally isomorphic to the noncomputable
`Over.pullback g`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackIsoOverPullback** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackIsoOverPullback : ChosenPullbacksAlong.pullback g ≅ Over.pullback 
g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The computable `ChosenPullbacksAlong.pullback g` is naturally isomorphic to the 
noncomputable
`Over.pullback g`.
-/
noncomputable def pullbackIsoOverPullback : ChosenPullbacksAlong.pullback g ≅ Over.pullback g :=
  (ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq (Over.mapPullbackAdj g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackIsoOverPullback_hom_app_comp_fst**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackIsoOverPullback_hom_app_comp_fst (T : Over X) : ((pullbackIsoOverP
ullback g).hom.app T).left ≫ pullback.fst _ _ = fst _ _
参数：T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Over.mapPullbackAdj_counit_app`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasPullbacksAlong f] (Y_1 :…
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`：rightAdjointU
niq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x 
: D) : F.map ((rightAdjointUniq adj1 adj2).hom.…
-/
theorem pullbackIsoOverPullback_hom_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.fst _ _ = fst _ _ := by
  simpa using! (Over.forget _).congr_map
    ((ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq_hom_app_counit
      (Over.mapPullbackAdj g) T)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackIsoOverPullback_hom_app_comp_snd**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackIsoOverPullback_hom_app_comp_snd (T : Over X) : ((pullbackIsoOverP
ullback g).hom.app T).left ≫ pullback.snd _ _ = snd _ _
参数：T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem pullbackIsoOverPullback_hom_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.snd _ _ = snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).hom.app T)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackIsoOverPullback_inv_app_comp_fst**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackIsoOverPullback_inv_app_comp_fst (T : Over X) : ((pullbackIsoOverP
ullback g).inv.app T).left ≫ fst _ _ = pullback.fst _ _
参数：T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoOverPullback_inv_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ fst _ _ = pullback.fst _ _ := by
  simp [← pullbackIsoOverPullback_hom_app_comp_fst, ← Over.comp_left_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.pullbackIsoOverPullback_inv_app_comp_snd**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：pullbackIsoOverPullback_inv_app_comp_snd (T : Over X) : ((pullbackIsoOverP
ullback g).inv.app T).left ≫ snd _ _ = pullback.snd _ _
参数：T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem pullbackIsoOverPullback_inv_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ snd _ _ = pullback.snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).inv.app T)

end PullbackFromChosenPullbacksAlongs

end ChosenPullbacksAlong

end CategoryTheory

