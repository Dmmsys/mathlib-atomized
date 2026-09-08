/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Pseudofunctors from locally discrete bicategories

This file provides various ways of constructing pseudofunctors from locally discrete
bicategories.

Firstly, we define the constructors `pseudofunctorOfIsLocallyDiscrete` and
`oplaxFunctorOfIsLocallyDiscrete` for defining pseudofunctors and oplax functors
from a locally discrete bicategory. In this situation, we do not need to care about
the field `map₂`, because all the `2`-morphisms in `B` are identities.

We also define a specialized constructor `LocallyDiscrete.mkPseudofunctor` when
the source bicategory is of the form `B := LocallyDiscrete B₀` for a category `B₀`.

We also prove that a functor `F : I ⥤ B` with `B` a strict bicategory can be promoted
to a pseudofunctor (or oplax functor) (`Functor.toPseudofunctor`) with domain
`LocallyDiscrete I`.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory

/-- Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors. -/
@[simps obj map mapId mapComp]
/-
**CategoryTheory.pseudofunctorOfIsLocallyDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：pseudofunctorOfIsLocallyDiscrete {B C : Type*} [Bicategory B] [IsLocallyDi
screte B] [Bicategory C] (obj : B -> C) (map : forall {b b' : B}, (b ⟶ b') -> (o
bj b ⟶ obj b')) (mapId : forall (b : B), map (𝟙 b) ≅ 𝟙 _) (mapComp : forall {b₀ 
b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g) (map₂_assoc
iator : forall {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃), (map
Comp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).h
om ≫ map f ◁ (mapComp g h)
参数：obj : B -> C；map : forall {b b' : B}, (b ⟶ b') -> (obj b ⟶ obj b')；mapId : fo
rall (b : B), map (𝟙 b) ≅ 𝟙 _；mapComp : forall {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g :
 b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors.
-/
def pseudofunctorOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (obj : B → C)
    (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ (b : B), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by cat_disch)
    (map₂_left_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    B ⥤ᵖ C where
  obj := obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  map₂_whisker_left _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η _ := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

/-- Constructor for oplax functors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of oplax functors. -/
@[simps obj map mapId mapComp]
/-
**CategoryTheory.oplaxFunctorOfIsLocallyDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：oplaxFunctorOfIsLocallyDiscrete {B C : Type*} [Bicategory B] [IsLocallyDis
crete B] [Bicategory C] (obj : B -> C) (map : forall {b b' : B}, (b ⟶ b') -> (ob
j b ⟶ obj b')) (mapId : forall (b : B), map (𝟙 b) ⟶ 𝟙 _) (mapComp : forall {b₀ b
₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ⟶ map f ≫ map g) (map₂_associ
ator : forall {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃), eqToH
om (by simp) ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h = mapComp (f ≫ g) h ≫ map
Comp f g ▷ map h ≫ (α_ (ma
参数：obj : B -> C；map : forall {b b' : B}, (b ⟶ b') -> (obj b ⟶ obj b')；mapId : fo
rall (b : B), map (𝟙 b) ⟶ 𝟙 _；mapComp : forall {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g :
 b₁ ⟶ b₂), map (f ≫ g) ⟶ map f ≫ map g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for oplax functors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of oplax functors.
-/
def oplaxFunctorOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (obj : B → C)
    (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ (b : B), map (𝟙 b) ⟶ 𝟙 _)
    (mapComp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ⟶ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      eqToHom (by simp) ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
        mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
          cat_disch)
    (map₂_left_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      mapComp (𝟙 b₀) f ≫ mapId b₀ ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      mapComp f (𝟙 b₁) ≫ map f ◁ mapId b₁ ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    B ⥤ᵒᵖᴸ C where
  obj := obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  mapComp_naturality_left η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  mapComp_naturality_right _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/--
A functor between two categories `C` and `D` can be lifted to a pseudofunctor between the
corresponding locally discrete bicategories.
-/
@[simps! obj map mapId mapComp]
/-
**CategoryTheory.Functor.toPseudofunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           CategoryTheory.Pseudofunctor (CategoryTheor
y.LocallyDiscrete C) (CategoryTheory.LocallyDiscrete D)
参数：CategoryTheory.LocallyDiscrete C；CategoryTheory.LocallyDiscrete D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instIsLocallyDiscreteLocallyDiscrete`：∀ (C : T
ype u_1) [inst : CategoryTheory.Category.{v_1, u_1} C],   CategoryTheory.Bicateg
ory.IsLocallyDiscrete (CategoryTheory.LocallyDiscret…

--- 原说明 ---
A functor between two categories `C` and `D` can be lifted to a pseudofunctor be
tween the
corresponding locally discrete bicategories.
-/
def Functor.toPseudofunctor : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete D) :=
  pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ ↦ .mk <| F.obj X) (fun ⟨f⟩ ↦ (F.map f).toLoc)
    (fun ⟨X⟩ ↦ eqToIso (by simp [CategoryStruct.id]))
    (fun ⟨f⟩ ⟨g⟩ ↦ eqToIso (by simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor := Functor.toPseudofunctor

/--
A functor between two categories `C` and `D` can be lifted to an oplax functor between the
corresponding locally discrete bicategories.

This is just an abbreviation of `Functor.toPseudofunctor.toOplax`.
-/
@[simps! map]
/-
**CategoryTheory.Functor.toOplaxFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           CategoryTheory.OplaxFunctor (CategoryTheory
.LocallyDiscrete C) (CategoryTheory.LocallyDiscrete D)
参数：CategoryTheory.LocallyDiscrete C；CategoryTheory.LocallyDiscrete D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between two categories `C` and `D` can be lifted to an oplax functor b
etween the
corresponding locally discrete bicategories.

This is just an abbreviation of `Functor.toPseudofunctor.toOplax`.
-/
abbrev Functor.toOplaxFunctor : LocallyDiscrete C ⥤ᵒᵖᴸ (LocallyDiscrete D) :=
  F.toPseudofunctor.toOplax

end

section

variable {I B : Type*} [Category* I] [Bicategory B] [Strict B] (F : I ⥤ B)

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to a pseudofunctor from `LocallyDiscrete I` to `B`.
-/
@[simps! obj map mapId mapComp]
/-
**CategoryTheory.Functor.toPseudofunctor'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{I : Type u_1} →   {B : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} I] →       [inst_1 : CategoryTheory.Bicategory B] →         [inst_2 : C
ategoryTheory.Bicategory.Strict B] →           CategoryTheory.Functor I B → Cate
goryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete I) B
参数：CategoryTheory.LocallyDiscrete I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instIsLocallyDiscreteLocallyDiscrete`：∀ (C : T
ype u_1) [inst : CategoryTheory.Category.{v_1, u_1} C],   CategoryTheory.Bicateg
ory.IsLocallyDiscrete (CategoryTheory.LocallyDiscret…

--- 原说明 ---
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categ
ories) `I ⥤ B` can
be promoted to a pseudofunctor from `LocallyDiscrete I` to `B`.
-/
def Functor.toPseudofunctor' : LocallyDiscrete I ⥤ᵖ B :=
  pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ ↦ F.obj X) (fun ⟨f⟩ ↦ F.map f)
    (fun ⟨X⟩ ↦ eqToIso (by simp [CategoryStruct.id]))
    (fun f g ↦ eqToIso (by obtain ⟨f⟩ := f; obtain ⟨g⟩ := g; simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor' := Functor.toPseudofunctor'

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
@[simps! map]
/-
**CategoryTheory.Functor.toOplaxFunctor'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{I : Type u_1} →   {B : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} I] →       [inst_1 : CategoryTheory.Bicategory B] →         [inst_2 : C
ategoryTheory.Bicategory.Strict B] →           CategoryTheory.Functor I B → Cate
goryTheory.OplaxFunctor (CategoryTheory.LocallyDiscrete I) B
参数：CategoryTheory.LocallyDiscrete I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categ
ories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
abbrev Functor.toOplaxFunctor' : LocallyDiscrete I ⥤ᵒᵖᴸ B :=
  F.toPseudofunctor'.toOplax

end

namespace LocallyDiscrete

/-- Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors. -/
@[simps! obj map mapId mapComp]
/-
**CategoryTheory.LocallyDiscrete.mkPseudofunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.LocallyDiscrete`。
形式化陈述：mkPseudofunctor {B₀ C : Type*} [Category* B₀] [Bicategory C] (obj : B₀ -> 
C) (map : forall {b b' : B₀}, (b ⟶ b') -> (obj b ⟶ obj b')) (mapId : forall (b :
 B₀), map (𝟙 b) ≅ 𝟙 _) (mapComp : forall {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶
 b₂), map (f ≫ g) ≅ map f ≫ map g) (map₂_associator : forall {b₀ b₁ b₂ b₃ : B₀} 
(f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃), (mapComp (f ≫ g) h).hom ≫ (mapComp f 
g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫ 
(mapComp f (g ≫ h)).inv = 
参数：obj : B₀ -> C；map : forall {b b' : B₀}, (b ⟶ b') -> (obj b ⟶ obj b')；mapId : 
forall (b : B₀), map (𝟙 b) ≅ 𝟙 _；mapComp : forall {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) 
(g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instIsLocallyDiscreteLocallyDiscrete`：∀ (C : T
ype u_1) [inst : CategoryTheory.Category.{v_1, u_1} C],   CategoryTheory.Bicateg
ory.IsLocallyDiscrete (CategoryTheory.LocallyDiscret…

--- 原说明 ---
Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors.
-/
def mkPseudofunctor {B₀ C : Type*} [Category* B₀] [Bicategory C]
    (obj : B₀ → C)
    (map : ∀ {b b' : B₀}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ (b : B₀), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : ∀ {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by cat_disch)
    (map₂_left_unitor : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    LocallyDiscrete B₀ ⥤ᵖ C :=
  pseudofunctorOfIsLocallyDiscrete (fun b ↦ obj b.as) (fun f ↦ map f.as)
    (fun _ ↦ mapId _) (fun _ _ ↦ mapComp _ _) (fun _ _ _ ↦ map₂_associator _ _ _)
    (fun _ ↦ map₂_left_unitor _) (fun _ ↦ map₂_right_unitor _)

end LocallyDiscrete

end CategoryTheory

