/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!

# `WithInitial` and `WithTerminal`

Given a category `C`, this file constructs two objects:
1. `WithTerminal C`, the category built from `C` by formally adjoining a terminal object.
2. `WithInitial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `WithTerminal.star` resp. `WithInitial.star`, and
the proofs that these are terminal resp. initial are in `WithTerminal.star_terminal`
and `WithInitial.star_initial`.

The inclusion from `C` into `WithTerminal C` resp. `WithInitial C` is denoted
`WithTerminal.incl` resp. `WithInitial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `WithTerminal C` resp. `WithInitial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `inclLift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `liftUnique` provides the uniqueness property of `lift`.

In addition to this, we provide `WithTerminal.map` and `WithInitial.map` providing the
functoriality of these constructions with respect to functors on the base categories.

We define corresponding pseudofunctors `WithTerminal.pseudofunctor` and `WithInitial.pseudofunctor`
from `Cat` to `Cat`.

-/

@[expose] public section


namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
/-
**CategoryTheory.WithTerminal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：WithTerminal : Type u | of : C -> WithTerminal | star : WithTerminal deriv
ing Inhabited  attribute [local aesop safe cases (rule_sets
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formally adjoin a terminal object to a category.
-/
inductive WithTerminal : Type u
  | of : C → WithTerminal
  | star : WithTerminal
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal

/-- Formally adjoin an initial object to a category. -/
/-
**CategoryTheory.WithInitial** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：WithInitial : Type u | of : C -> WithInitial | star : WithInitial deriving
 Inhabited  attribute [local aesop safe cases (rule_sets
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formally adjoin an initial object to a category.
-/
inductive WithInitial : Type u
  | of : C → WithInitial
  | star : WithInitial
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}

/-- Morphisms for `WithTerminal C`. -/
@[simp]
/-
**CategoryTheory.WithTerminal.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Terminal`。
形式化陈述：{C : Type u} →   [CategoryTheory.Category.{v, u} C] → CategoryTheory.WithT
erminal C → CategoryTheory.WithTerminal C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms for `WithTerminal C`.
-/
def Hom : WithTerminal C → WithTerminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of _ => PEmpty
  | _, star => PUnit
attribute [nolint simpNF] Hom.eq_3

/-- Identity morphisms for `WithTerminal C`. -/
@[simp]
/-
**CategoryTheory.WithTerminal.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.WithT
erminal`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (X : CategoryTh
eory.WithTerminal C) → X.Hom X
参数：X : CategoryTheory.WithTerminal C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity morphisms for `WithTerminal C`.
-/
def id : ∀ X : WithTerminal C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `WithTerminal C`. -/
@[simp]
/-
**CategoryTheory.WithTerminal.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hTerminal`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y Z : Cate
goryTheory.WithTerminal C} → X.Hom Y → Y.Hom Z → X.Hom Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms for `WithTerminal C`.
-/
def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | of _X, _, star => fun _f _g => PUnit.unit
  | star, of _X, _ => fun f _g => PEmpty.elim f
  | _, star, of _Y => fun _f g => PEmpty.elim g
  | star, star, star => fun _ _ => PUnit.unit
#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] comp.eq_2 comp.eq_4

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.WithTerminal.false_of_from_star'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.WithTerminal`。
形式化陈述：false_of_from_star' {X : C} (f : Hom star (of X)) : False
参数：f : Hom star (of X)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated.
-/
lemma false_of_from_star' {X : C} (f : Hom star (of X)) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{v} (WithTerminal C) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp

set_option backward.isDefEq.respectTransparency.types false in
/-- Helper function for typechecking. -/
/-
**CategoryTheory.WithTerminal.down** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hTerminal`。
形式化陈述：down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y
参数：f : of X ⟶ of Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for typechecking.
-/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.down_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
WithTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C},   Catego
ryTheory.WithTerminal.down (CategoryTheory.CategoryStruct.id (CategoryTheory.Wit
hTerminal.of X)) =     CategoryTheory.CategoryStruct.id X
参数：CategoryTheory.CategoryStruct.id (CategoryTheory.WithTerminal.of X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.down_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.WithTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C}   (f 
: CategoryTheory.WithTerminal.of X ⟶ CategoryTheory.WithTerminal.of Y)   (g : Ca
tegoryTheory.WithTerminal.of Y ⟶ CategoryTheory.WithTerminal.of Z),   CategoryTh
eory.WithTerminal.down (CategoryTheory.CategoryStruct.comp f g) =     CategoryTh
eory.CategoryStruct.comp (CategoryTheory.WithTerminal.down f) (CategoryTheory.Wi
thTerminal.down g)
参数：f : CategoryTheory.WithTerminal.of X ⟶ CategoryTheory.WithTerminal.of Y；g : C
ategoryTheory.WithTerminal.of Y ⟶ CategoryTheory.WithTerminal.of Z；CategoryTheor
y.CategoryStruct.comp f g；CategoryTheory.WithTerminal.down f；CategoryTheory.With
Terminal.down g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[aesop safe destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.WithTerminal.false_of_from_star** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.WithTerminal`。
形式化陈述：false_of_from_star {X : C} (f : star ⟶ of X) : False
参数：f : star ⟶ of X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma false_of_from_star {X : C} (f : star ⟶ of X) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion from `C` into `WithTerminal C`. -/
/-
**CategoryTheory.WithTerminal.incl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hTerminal`。
形式化陈述：incl : C ⥤ WithTerminal C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from `C` into `WithTerminal C`.
-/
def incl : C ⥤ WithTerminal C where
  obj := of
  map f := f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (incl : C ⥤ _).Faithful where

set_option backward.isDefEq.respectTransparency.types false in
/-- Map `WithTerminal` with respect to a functor `F : C ⥤ D`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Terminal`。
形式化陈述：map {D : Type*} [Category* D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal 
D where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `WithTerminal` with respect to a functor `F : C ⥤ D`.
-/
def map {D : Type*} [Category* D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of _, star, _ => PUnit.unit
    | star, star, _ => PUnit.unit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithTerminal C)`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wi
thTerminal`。
形式化陈述：mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C)
参数：C : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithTerminal C)`.
-/
def mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WithTerminal`。
形式化陈述：mapComp {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) 
: map (F ⋙ G) ≅ map F ⋙ map G
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `.
-/
def mapComp {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/-- From a natural transformation of functors `C ⥤ D`, the induced natural transformation
of functors `WithTerminal C ⥤ WithTerminal D`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Terminal`。
形式化陈述：map {D : Type*} [Category* D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal 
D where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a natural transformation of functors `C ⥤ D`, the induced natural transform
ation
of functors `WithTerminal C ⥤ WithTerminal D`.
-/
def map₂ {D : Type*} [Category* D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | of x, star, _ => rfl
    | star, star, _ => rfl

-- Note: ...
set_option backward.isDefEq.respectTransparency.types false in
/-- The prelax functor from `Cat` to `Cat` defined with `WithTerminal`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.prelaxfunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithTerminal`。
形式化陈述：prelaxfunctor : PrelaxFunctor Cat Cat where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prelax functor from `Cat` to `Cat` defined with `WithTerminal`.
-/
def prelaxfunctor : PrelaxFunctor Cat Cat where
  obj C := Cat.of (WithTerminal C)
  map F := (map F.toFunctor).toCatHom
  map₂ f := (map₂ f.toNatTrans).toCatHom₂
  map₂_id := by
    intros
    ext X
    cases X <;> rfl
  map₂_comp := by
    intros
    ext X
    cases X <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pseudofunctor from `Cat` to `Cat` defined with `WithTerminal`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.pseudofunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithTerminal`。
形式化陈述：pseudofunctor : Pseudofunctor Cat Cat where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudofunctor from `Cat` to `Cat` defined with `WithTerminal`.
-/
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
  mapId C := Cat.Hom.isoMk (mapId C)
  mapComp _ _ := Cat.Hom.isoMk <| mapComp _ _
  map₂_whisker_left := by
    intros
    ext X
    cases X
    · simp
    · rfl
  map₂_whisker_right := by
    intros
    ext X
    cases X
    · simp
      rfl
    · rfl
  map₂_associator := by
    intros
    dsimp
    ext X
    cases X
    · simp
    · rfl
  map₂_left_unitor := by
    intros
    ext X
    cases X
    · simp
    · rfl
  map₂_right_unitor := by
    intros
    ext X
    cases X
    · simpa using! (refl _)
    · rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : WithTerminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of _ => PUnit.unit
    | star => PUnit.unit
  uniq := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- `WithTerminal.star` is terminal. -/
/-
**CategoryTheory.WithTerminal.starTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithTerminal`。
形式化陈述：starTerminal : Limits.IsTerminal (star : WithTerminal C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithTerminal.star` is terminal.
-/
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasTerminal (WithTerminal C) := Limits.hasTerminal_of_unique star

/-- The isomorphism between star and an abstract terminal object of `WithTerminal C` -/
@[simps!]
/-
**CategoryTheory.WithTerminal.starIsoTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.WithTerminal`。
形式化陈述：starIsoTerminal : star ≅ ⊤_ (WithTerminal C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.WithTerminal.instHasTerminal`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C],   CategoryTheory.Limits.HasTerminal (CategoryTheo
ry.WithTerminal C)

--- 原说明 ---
The isomorphism between star and an abstract terminal object of `WithTerminal C`
-/
noncomputable def starIsoTerminal : star ≅ ⊤_ (WithTerminal C) :=
  starTerminal.uniqueUpToIso (Limits.terminalIsTerminal)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a functor `F : C ⥤ D` to `WithTerminal C ⥤ D`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hTerminal`。
形式化陈述：lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.ob
j x ⟶ Z) (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal
 C ⥤ D where obj X
参数：F : C ⥤ D；M : forall x : C, F.obj x ⟶ Z；hM : forall (x y : C) (f : x ⟶ y), F.
map f ≫ M y = M x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a functor `F : C ⥤ D` to `WithTerminal C ⥤ D`.
-/
def lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of x, star, _ => M x
    | star, star, _ => 𝟙 Z

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.inclLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.WithTerminal`。
形式化陈述：inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, 
F.obj x ⟶ Z) (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ l
ift F M hM ≅ F where hom
参数：F : C ⥤ D；M : forall x : C, F.obj x ⟶ Z；hM : forall (x y : C) (f : x ⟶ y), F.
map f ≫ M y = M x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `incl ⋙ lift F _ _` with `F`.
-/
def inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(lift F _ _).obj WithTerminal.star` with `Z`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.liftStar** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.WithTerminal`。
形式化陈述：liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, 
F.obj x ⟶ Z) (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F 
M hM).obj star ≅ Z
参数：F : C ⥤ D；M : forall x : C, F.obj x ⟶ Z；hM : forall (x y : C) (f : x ⟶ y), F.
map f ≫ M y = M x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `(lift F _ _).obj WithTerminal.star` with `Z`.
-/
def liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.WithTerminal.lift_map_liftStar** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.WithTerminal`。
形式化陈述：lift_map_liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : foral
l x : C, F.obj x ⟶ Z) (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (
x : C) : (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).
hom = (inclLift F M hM).hom.app x ≫ M x
参数：F : C ⥤ D；M : forall x : C, F.obj x ⟶ Z；hM : forall (x y : C) (f : x ⟶ y), F.
map f ≫ M y = M x；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem lift_map_liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).hom =
      (inclLift F M hM).hom.app x ≫ M x := by
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The uniqueness of `lift`. -/
@[simp]
/-
**CategoryTheory.WithTerminal.liftUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.WithTerminal`。
形式化陈述：liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C
, F.obj x ⟶ Z) (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (G : Wit
hTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) (hh : forall x : C, G.
map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) : G ≅ lift F 
M hM
参数：F : C ⥤ D；M : forall x : C, F.obj x ⟶ Z；hM : forall (x y : C) (f : x ⟶ y), F.
map f ≫ M y = M x；G : WithTerminal C ⥤ D；h : incl ⋙ G ≅ F；hG : G.obj star ≅ Z；hh
 : forall x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫
 M x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniqueness of `lift`.
-/
def liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
        exact hh _
      · cases f
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift` with `Z` a terminal object. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.liftToTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.WithTerminal`。
形式化陈述：liftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.
IsTerminal Z) : WithTerminal C ⥤ D
参数：F : C ⥤ D；hZ : Limits.IsTerminal Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `lift` with `Z` a terminal object.
-/
def liftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    WithTerminal C ⥤ D :=
  lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.inclLiftToTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.WithTerminal`。
形式化陈述：inclLiftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Lim
its.IsTerminal Z) : incl ⋙ liftToTerminal F hZ ≅ F
参数：F : C ⥤ D；hZ : Limits.IsTerminal Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `incl_lift` with `Z` a terminal object.
-/
def inclLiftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.liftToTerminalUnique** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.WithTerminal`。
形式化陈述：liftToTerminalUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : L
imits.IsTerminal Z) (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star
 ≅ Z) : G ≅ liftToTerminal F hZ
参数：F : C ⥤ D；hZ : Limits.IsTerminal Z；G : WithTerminal C ⥤ D；h : incl ⋙ G ≅ F；hG
 : G.obj star ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `lift_unique` with `Z` a terminal object.
-/
def liftToTerminalUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
/-
**CategoryTheory.WithTerminal.homFrom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WithTerminal`。
形式化陈述：homFrom (X : C) : incl.obj X ⟶ star
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a morphism to `star` from `of X`.
-/
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithTerminal.isIso_of_from_star** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.WithTerminal`。
形式化陈述：isIso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f
参数：f : star ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩

section

variable {D : Type*} [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor `WithTerminal C ⥤ D` can be seen as an element of the comma category
`Comma (𝟭 (C ⥤ D)) (const C)`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.mkCommaObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithTerminal`。
形式化陈述：mkCommaObject (F : WithTerminal C ⥤ D) : Comma (𝟭 (C ⥤ D)) (Functor.const 
C) where right
参数：F : WithTerminal C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `WithTerminal C ⥤ D` can be seen as an element of the comma category
`Comma (𝟭 (C ⥤ D)) (const C)`.
-/
def mkCommaObject (F : WithTerminal C ⥤ D) : Comma (𝟭 (C ⥤ D)) (Functor.const C) where
  right := F.obj .star
  left := (incl ⋙ F)
  hom :=
    { app x := F.map (starTerminal.from (.of x))
      naturality x y f := by
        dsimp
        rw [Category.comp_id, ← F.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism of functors `WithTerminal C ⥤ D` gives a morphism between the associated comma
objects. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.mkCommaMorphism** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.WithTerminal`。
形式化陈述：mkCommaMorphism {F G : WithTerminal C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶
 mkCommaObject G where right
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of functors `WithTerminal C ⥤ D` gives a morphism between the associa
ted comma
objects.
-/
def mkCommaMorphism {F G : WithTerminal C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶ mkCommaObject G where
  right := η.app .star
  left := Functor.whiskerLeft incl η

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An element of the comma category `Comma (𝟭 (C ⥤ D)) (Functor.const C)` can be seen as a
functor `WithTerminal C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.ofCommaObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithTerminal`。
形式化陈述：ofCommaObject (c : Comma (𝟭 (C ⥤ D)) (Functor.const C)) : WithTerminal C ⥤
 D
参数：c : Comma (𝟭 (C ⥤ D)) (Functor.const C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the comma category `Comma (𝟭 (C ⥤ D)) (Functor.const C)` can be se
en as a
functor `WithTerminal C ⥤ D`.
-/
def ofCommaObject (c : Comma (𝟭 (C ⥤ D)) (Functor.const C)) : WithTerminal C ⥤ D :=
  lift (Z := c.right) c.left (fun x ↦ c.hom.app x) (fun x y f ↦ by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `Comma (𝟭 (C ⥤ D)) (Functor.const C)` gives a morphism between the associated
functors `WithTerminal C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.ofCommaMorphism** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.WithTerminal`。
形式化陈述：ofCommaMorphism {c c' : Comma (𝟭 (C ⥤ D)) (Functor.const C)} (φ : c ⟶ c') 
: ofCommaObject c ⟶ ofCommaObject c' where app x
参数：𝟭 (C ⥤ D)；Functor.const C；φ : c ⟶ c'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Comma (𝟭 (C ⥤ D)) (Functor.const C)` gives a morphism between the
 associated
functors `WithTerminal C ⥤ D`.
-/
def ofCommaMorphism {c c' : Comma (𝟭 (C ⥤ D)) (Functor.const C)} (φ : c ⟶ c') :
    ofCommaObject c ⟶ ofCommaObject c' where
  app x :=
    match x with
    | of x => φ.left.app x
    | star => φ.right
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | of a, star, _ => by simp; simpa [-CommaMorphism.w] using (congrArg (fun f ↦ f.app a) φ.w).symm
    | star, star, _ => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The category of functors `WithTerminal C ⥤ D` is equivalent to the category
`Comma (𝟭 (C ⥤ D)) (const C) `. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.equivComma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.WithTerminal`。
形式化陈述：equivComma : (WithTerminal C ⥤ D) ≌ Comma (𝟭 (C ⥤ D)) (Functor.const C) wh
ere functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of functors `WithTerminal C ⥤ D` is equivalent to the category
`Comma (𝟭 (C ⥤ D)) (const C) `.
-/
def equivComma : (WithTerminal C ⥤ D) ≌ Comma (𝟭 (C ⥤ D)) (Functor.const C) where
  functor :=
    { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F ↦ liftUnique
        (incl ⋙ F)
        (fun x ↦ F.map (starTerminal.from (of x)))
        (fun x y f ↦ by
          simp only [Functor.comp_obj, Functor.comp_map]
          rw [← F.map_comp]
          congr 1)
        F (Iso.refl _) (Iso.refl _)
        (fun x ↦ by
          simp only [Iso.refl_hom, Category.id_comp, Functor.comp_obj,
            NatTrans.id_app, Category.comp_id]; rfl))
      (fun {x y} f ↦ by ext t; cases t <;> simp [incl])
  counitIso := NatIso.ofComponents (fun F ↦ Iso.refl _)
  functor_unitIso_comp x := by
    simp only [Functor.id_obj, Functor.comp_obj, liftUnique, lift_obj, NatIso.ofComponents_hom_app,
      Iso.refl_hom, Category.comp_id]
    ext <;> rfl

end

open CategoryTheory.Limits CategoryTheory.Limits.WidePullbackShape

/-
**CategoryTheory.WithTerminal.subsingleton_hom** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.WithTerminal`。
形式化陈述：subsingleton_hom {J : Type*} : Quiver.IsThin (WithTerminal (Discrete J))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance subsingleton_hom {J : Type*} : Quiver.IsThin (WithTerminal (Discrete J)) := fun _ _ => by
  constructor
  intro a b
  casesm* WithTerminal _, (_ : WithTerminal _) ⟶ (_ : WithTerminal _)
  · exact congr_arg (ULift.up ∘ PLift.up) rfl
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- Implementation detail for `widePullbackShapeEquiv`. -/
@[simps apply]
/-
**CategoryTheory.WithTerminal.widePullbackShapeEquivObj** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail for `widePullbackShapeEquiv`.
-/
private def widePullbackShapeEquivObj {J : Type*} :
    WidePullbackShape J ≃ WithTerminal (Discrete J) where
  toFun
  | .some x => .of <| .mk x
  | .none => .star
  invFun
  | .of x => .some <| Discrete.as x
  | .star => .none
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

set_option backward.privateInPublic true in
/-- Implementation detail for `widePullbackShapeEquiv`. -/
/-
**CategoryTheory.WithTerminal.widePullbackShapeEquivMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail for `widePullbackShapeEquiv`.
-/
private def widePullbackShapeEquivMap {J : Type*} (x y : WidePullbackShape J) :
    (x ⟶ y) ≃ (widePullbackShapeEquivObj x ⟶ widePullbackShapeEquivObj y) where
  toFun
  | .term _ => PUnit.unit
  | .id _ => 𝟙 _
  invFun f := match x, y with
  | some x, some y =>
    cast (by
        have eq : x = y := PLift.down (ULift.down (down f))
        rw [eq]
        rfl) (Hom.id (some y))
  | none, some y => by cases f
  | some x, none => .term x
  | none, none => .id none
  left_inv f := by apply Subsingleton.allEq
  right_inv f := match x, y with
  | some x, some y => Subsingleton.allEq _ _
  | none, some y => by cases f
  | some x, none
  | none, none => rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- In the case of a discrete category, `WithTerminal` is the same category as `WidePullbackShape`

TODO: Should we simply replace `WidePullbackShape J` with `WithTerminal (Discrete J)` everywhere? -/
@[simps! functor_obj inverse_obj]
/-
**CategoryTheory.WithTerminal.widePullbackShapeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.WithTerminal`。
形式化陈述：widePullbackShapeEquiv {J : Type*} : WidePullbackShape J ≌ WithTerminal (D
iscrete J) where functor.obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
In the case of a discrete category, `WithTerminal` is the same category as `Wide
PullbackShape`

TODO: Should we simply replace `WidePullbackShape J` with `WithTerminal (Discret
e J)` everywhere?
-/
def widePullbackShapeEquiv {J : Type*} : WidePullbackShape J ≌ WithTerminal (Discrete J) where
  functor.obj := widePullbackShapeEquivObj
  functor.map := widePullbackShapeEquivMap _ _
  inverse.obj := widePullbackShapeEquivObj.symm
  inverse.map f := (widePullbackShapeEquivMap _ _).symm (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  unitIso := NatIso.ofComponents fun x ↦ eqToIso (by aesop)
  counitIso := NatIso.ofComponents fun x ↦ eqToIso (by aesop)

end WithTerminal

namespace WithInitial

variable {C}

/-- Morphisms for `WithInitial C`. -/
@[simp]
/-
**CategoryTheory.WithInitial.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.WithI
nitial`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → CategoryTheory.WithIni
tial C → CategoryTheory.WithInitial C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms for `WithInitial C`.
-/
def Hom : WithInitial C → WithInitial C → Type v
  | of X, of Y => X ⟶ Y
  | of _, _ => PEmpty
  | star, _ => PUnit
attribute [nolint simpNF] Hom.eq_2

/-- Identity morphisms for `WithInitial C`. -/
@[simp]
/-
**CategoryTheory.WithInitial.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.WithIn
itial`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (X : CategoryTh
eory.WithInitial C) → X.Hom X
参数：X : CategoryTheory.WithInitial C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity morphisms for `WithInitial C`.
-/
def id : ∀ X : WithInitial C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `WithInitial C`. -/
@[simp]
/-
**CategoryTheory.WithInitial.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Initial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y Z : Cate
goryTheory.WithInitial C} → X.Hom Y → Y.Hom Z → X.Hom Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms for `WithInitial C`.
-/
def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | star, _, of _X => fun _f _g => PUnit.unit
  | _, of _X, star => fun _f g => PEmpty.elim g
  | of _Y, star, _ => fun f _g => PEmpty.elim f
  | star, star, star => fun _ _ => PUnit.unit
attribute [nolint simpNF] comp.eq_3

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.WithInitial.false_of_to_star'** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.WithInitial`。
形式化陈述：false_of_to_star' {X : C} (f : Hom (of X) star) : False
参数：f : Hom (of X) star。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma false_of_to_star' {X : C} (f : Hom (of X) star) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{v} (WithInitial C) where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Helper function for typechecking. -/
/-
**CategoryTheory.WithInitial.down** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Initial`。
形式化陈述：down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y
参数：f : of X ⟶ of Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for typechecking.
-/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.down_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.W
ithInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C},   Catego
ryTheory.WithInitial.down (CategoryTheory.CategoryStruct.id (CategoryTheory.With
Initial.of X)) =     CategoryTheory.CategoryStruct.id X
参数：CategoryTheory.CategoryStruct.id (CategoryTheory.WithInitial.of X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.down_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.WithInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C}   (f 
: CategoryTheory.WithInitial.of X ⟶ CategoryTheory.WithInitial.of Y)   (g : Cate
goryTheory.WithInitial.of Y ⟶ CategoryTheory.WithInitial.of Z),   CategoryTheory
.WithInitial.down (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.
CategoryStruct.comp (CategoryTheory.WithInitial.down f) (CategoryTheory.WithInit
ial.down g)
参数：f : CategoryTheory.WithInitial.of X ⟶ CategoryTheory.WithInitial.of Y；g : Cat
egoryTheory.WithInitial.of Y ⟶ CategoryTheory.WithInitial.of Z；CategoryTheory.Ca
tegoryStruct.comp f g；CategoryTheory.WithInitial.down f；CategoryTheory.WithIniti
al.down g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[aesop safe destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.WithInitial.false_of_to_star** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.WithInitial`。
形式化陈述：false_of_to_star {X : C} (f : of X ⟶ star) : False
参数：f : of X ⟶ star。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma false_of_to_star {X : C} (f : of X ⟶ star) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion of `C` into `WithInitial C`. -/
/-
**CategoryTheory.WithInitial.incl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Initial`。
形式化陈述：incl : C ⥤ WithInitial C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `C` into `WithInitial C`.
-/
def incl : C ⥤ WithInitial C where
  obj := of
  map f := f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (incl : C ⥤ _).Faithful where

set_option backward.isDefEq.respectTransparency.types false in
/-- Map `WithInitial` with respect to a functor `F : C ⥤ D`. -/
@[simps]
/-
**CategoryTheory.WithInitial.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.WithI
nitial`。
形式化陈述：map {D : Type*} [Category* D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D 
where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `WithInitial` with respect to a functor `F : C ⥤ D`.
-/
def map {D : Type*} [Category* D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => PUnit.unit
    | star, star, _ => PUnit.unit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithInitial C)`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hInitial`。
形式化陈述：mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithInitial C)
参数：C : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithInitial C)`.
-/
def mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithInitial C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
/-
**CategoryTheory.WithInitial.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.W
ithInitial`。
形式化陈述：mapComp {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) 
: map (F ⋙ G) ≅ map F ⋙ map G
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `.
-/
def mapComp {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/-- From a natural transformation of functors `C ⥤ D`, the induced natural transformation
of functors `WithInitial C ⥤ WithInitial D`. -/
@[simps]
/-
**CategoryTheory.WithInitial.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.WithI
nitial`。
形式化陈述：map {D : Type*} [Category* D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D 
where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a natural transformation of functors `C ⥤ D`, the induced natural transform
ation
of functors `WithInitial C ⥤ WithInitial D`.
-/
def map₂ {D : Type*} [Category* D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | star, of x, _ => rfl
    | star, star, _ => rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The prelax functor from `Cat` to `Cat` defined with `WithInitial`. -/
@[simps]
/-
**CategoryTheory.WithInitial.prelaxfunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：prelaxfunctor : PrelaxFunctor Cat Cat where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prelax functor from `Cat` to `Cat` defined with `WithInitial`.
-/
def prelaxfunctor : PrelaxFunctor Cat Cat where
  obj C := Cat.of (WithInitial C)
  map F := (map F.toFunctor).toCatHom
  map₂ f := (map₂ f.toNatTrans).toCatHom₂
  map₂_id := by
    intros
    ext X
    cases X <;> rfl
  map₂_comp := by
    intros
    ext X
    cases X <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pseudofunctor from `Cat` to `Cat` defined with `WithInitial`. -/
@[simps]
/-
**CategoryTheory.WithInitial.pseudofunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：pseudofunctor : Pseudofunctor Cat Cat where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudofunctor from `Cat` to `Cat` defined with `WithInitial`.
-/
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
  mapId C := Cat.Hom.isoMk <| mapId C
  mapComp _ _ := Cat.Hom.isoMk <| mapComp _ _
  map₂_whisker_left := by
    intros
    ext X
    cases X
    · simp
    · rfl
  map₂_whisker_right := by
    intros
    ext X
    cases X
    · simp
      rfl
    · rfl
  map₂_associator := by
    intros
    ext X
    cases X
    · simp
    · rfl
  map₂_left_unitor := by
    intros
    ext X
    cases X
    · simp
    · rfl
  map₂_right_unitor := by
    intros
    ext X
    cases X
    · simpa using! (refl _)
    · rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : WithInitial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of _x => PUnit.unit
    | star => PUnit.unit
  uniq := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- `WithInitial.star` is initial. -/
/-
**CategoryTheory.WithInitial.starInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.WithInitial`。
形式化陈述：starInitial : Limits.IsInitial (star : WithInitial C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithInitial.star` is initial.
-/
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasInitial (WithInitial C) := Limits.hasInitial_of_unique star

/-- The isomorphism between star and an abstract initial object of `WithInitial C` -/
@[simps!]
/-
**CategoryTheory.WithInitial.starIsoInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithInitial`。
形式化陈述：starIsoInitial : star ≅ ⊥_ (WithInitial C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.WithInitial.instHasInitial`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C],   CategoryTheory.Limits.HasInitial (CategoryTheory.
WithInitial C)

--- 原说明 ---
The isomorphism between star and an abstract initial object of `WithInitial C`
-/
noncomputable def starIsoInitial : star ≅ ⊥_ (WithInitial C) :=
  starInitial.uniqueUpToIso (Limits.initialIsInitial)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a functor `F : C ⥤ D` to `WithInitial C ⥤ D`. -/
@[simps]
/-
**CategoryTheory.WithInitial.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.With
Initial`。
形式化陈述：lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ 
F.obj x) (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial 
C ⥤ D where obj X
参数：F : C ⥤ D；M : forall x : C, Z ⟶ F.obj x；hM : forall (x y : C) (f : x ⟶ y), M 
x ≫ F.map f = M y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a functor `F : C ⥤ D` to `WithInitial C ⥤ D`.
-/
def lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => M _
    | star, star, _ => 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.inclLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WithInitial`。
形式化陈述：inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, 
Z ⟶ F.obj x) (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ l
ift F M hM ≅ F where hom
参数：F : C ⥤ D；M : forall x : C, Z ⟶ F.obj x；hM : forall (x y : C) (f : x ⟶ y), M 
x ≫ F.map f = M y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `incl ⋙ lift F _ _` with `F`.
-/
def inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(lift F _ _).obj WithInitial.star` with `Z`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.liftStar** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WithInitial`。
形式化陈述：liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, 
Z ⟶ F.obj x) (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F 
M hM).obj star ≅ Z
参数：F : C ⥤ D；M : forall x : C, Z ⟶ F.obj x；hM : forall (x y : C) (f : x ⟶ y), M 
x ≫ F.map f = M y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `(lift F _ _).obj WithInitial.star` with `Z`.
-/
def liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.WithInitial.liftStar_lift_map** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.WithInitial`。
形式化陈述：liftStar_lift_map {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : foral
l x : C, Z ⟶ F.obj x) (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (
x : C) : (liftStar F M hM).hom ≫ (lift F M hM).map (starInitial.to (incl.obj x))
 = M x ≫ (inclLift F M hM).hom.app x
参数：F : C ⥤ D；M : forall x : C, Z ⟶ F.obj x；hM : forall (x y : C) (f : x ⟶ y), M 
x ≫ F.map f = M y；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
theorem liftStar_lift_map {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) =
      M x ≫ (inclLift F M hM).hom.app x := by
  simp [incl]

set_option backward.isDefEq.respectTransparency.types false in
/-- The uniqueness of `lift`. -/
@[simp]
/-
**CategoryTheory.WithInitial.liftUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.WithInitial`。
形式化陈述：liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C
, Z ⟶ F.obj x) (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (G : Wit
hInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) (hh : forall x : C, hG.
symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) : G ≅ l
ift F M hM
参数：F : C ⥤ D；M : forall x : C, Z ⟶ F.obj x；hM : forall (x y : C) (f : x ⟶ y), M 
x ≫ F.map f = M y；G : WithInitial C ⥤ D；h : incl ⋙ G ≅ F；hG : G.obj star ≅ Z；hh 
: forall x : C, hG.symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm
.hom.app x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniqueness of `lift`.
-/
def liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
      · cases f
        change G.map _ ≫ h.hom.app _ = hG.hom ≫ _
        symm
        erw [← Iso.eq_inv_comp, ← Category.assoc, hh]
        simp
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift` with `Z` an initial object. -/
@[simps!]
/-
**CategoryTheory.WithInitial.liftToInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：liftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.I
sInitial Z) : WithInitial C ⥤ D
参数：F : C ⥤ D；hZ : Limits.IsInitial Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `lift` with `Z` an initial object.
-/
def liftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    WithInitial C ⥤ D :=
  lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps!]
/-
**CategoryTheory.WithInitial.inclLiftToInitial** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.WithInitial`。
形式化陈述：inclLiftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limi
ts.IsInitial Z) : incl ⋙ liftToInitial F hZ ≅ F
参数：F : C ⥤ D；hZ : Limits.IsInitial Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `incl_lift` with `Z` an initial object.
-/
def inclLiftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps!]
/-
**CategoryTheory.WithInitial.liftToInitialUnique** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.WithInitial`。
形式化陈述：liftToInitialUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Li
mits.IsInitial Z) (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ 
Z) : G ≅ liftToInitial F hZ
参数：F : C ⥤ D；hZ : Limits.IsInitial Z；G : WithInitial C ⥤ D；h : incl ⋙ G ≅ F；hG :
 G.obj star ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `lift_unique` with `Z` an initial object.
-/
def liftToInitialUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
/-
**CategoryTheory.WithInitial.homTo** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wit
hInitial`。
形式化陈述：homTo (X : C) : star ⟶ incl.obj X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a morphism from `star` to `of X`.
-/
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.WithInitial.isIso_of_to_star** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.WithInitial`。
形式化陈述：isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f
参数：f : X ⟶ star。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f :=
  match X with
  | of _ => f.elim
  | star => ⟨f, rfl, rfl⟩

section

variable {D : Type*} [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor `WithInitial C ⥤ D` can be seen as an element of the comma category
`Comma (const C) (𝟭 (C ⥤ D))`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.mkCommaObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：mkCommaObject (F : WithInitial C ⥤ D) : Comma (Functor.const C) (𝟭 (C ⥤ D)
) where left
参数：F : WithInitial C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `WithInitial C ⥤ D` can be seen as an element of the comma category
`Comma (const C) (𝟭 (C ⥤ D))`.
-/
def mkCommaObject (F : WithInitial C ⥤ D) : Comma (Functor.const C) (𝟭 (C ⥤ D)) where
  left := F.obj .star
  right := (incl ⋙ F)
  hom :=
    { app x := F.map (starInitial.to (.of x))
      naturality x y f := by
        dsimp
        rw [Category.id_comp, ← F.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism of functors `WithInitial C ⥤ D` gives a morphism between the associated comma
objects. -/
@[simps!]
/-
**CategoryTheory.WithInitial.mkCommaMorphism** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.WithInitial`。
形式化陈述：mkCommaMorphism {F G : WithInitial C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶ 
mkCommaObject G where left
参数：η : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of functors `WithInitial C ⥤ D` gives a morphism between the associat
ed comma
objects.
-/
def mkCommaMorphism {F G : WithInitial C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶ mkCommaObject G where
  left := η.app .star
  right := Functor.whiskerLeft incl η

set_option backward.defeqAttrib.useBackward true in
/-- An element of the comma category `Comma (Functor.const C) (𝟭 (C ⥤ D))` can be seen as a
functor `WithInitial C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.ofCommaObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：ofCommaObject (c : Comma (Functor.const C) (𝟭 (C ⥤ D))) : WithInitial C ⥤ 
D
参数：c : Comma (Functor.const C) (𝟭 (C ⥤ D))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the comma category `Comma (Functor.const C) (𝟭 (C ⥤ D))` can be se
en as a
functor `WithInitial C ⥤ D`.
-/
def ofCommaObject (c : Comma (Functor.const C) (𝟭 (C ⥤ D))) : WithInitial C ⥤ D :=
  lift (Z := c.left) c.right (fun x ↦ c.hom.app x)
    (fun x y f ↦ by simpa using (c.hom.naturality f).symm)

set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `Comma (Functor.const C) (𝟭 (C ⥤ D))` gives a morphism between the associated
functors `WithInitial C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.ofCommaMorphism** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.WithInitial`。
形式化陈述：ofCommaMorphism {c c' : Comma (Functor.const C) (𝟭 (C ⥤ D))} (φ : c ⟶ c') 
: ofCommaObject c ⟶ ofCommaObject c' where app x
参数：Functor.const C；𝟭 (C ⥤ D)；φ : c ⟶ c'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Comma (Functor.const C) (𝟭 (C ⥤ D))` gives a morphism between the
 associated
functors `WithInitial C ⥤ D`.
-/
def ofCommaMorphism {c c' : Comma (Functor.const C) (𝟭 (C ⥤ D))} (φ : c ⟶ c') :
    ofCommaObject c ⟶ ofCommaObject c' where
  app x :=
    match x with
    | of x => φ.right.app x
    | star => φ.left
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | star, of a, _ => by simpa [-CommaMorphism.w] using (congrArg (fun f ↦ f.app a) φ.w).symm
    | star, star, _ => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The category of functors `WithInitial C ⥤ D` is equivalent to the category
`Comma (const C) (𝟭 (C ⥤ D))`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.equivComma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.WithInitial`。
形式化陈述：equivComma : (WithInitial C ⥤ D) ≌ Comma (Functor.const C) (𝟭 (C ⥤ D)) whe
re functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of functors `WithInitial C ⥤ D` is equivalent to the category
`Comma (const C) (𝟭 (C ⥤ D))`.
-/
def equivComma : (WithInitial C ⥤ D) ≌ Comma (Functor.const C) (𝟭 (C ⥤ D)) where
  functor :=
    { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F ↦ liftUnique
        (incl ⋙ F)
        (fun x ↦ F.map (starInitial.to (of x)))
        (fun x y f ↦ by
          simp only [Functor.comp_obj, Functor.comp_map]
          rw [← F.map_comp]
          congr 1)
        F (Iso.refl _) (Iso.refl _)
        (fun x ↦ by
          simp only [Iso.refl_symm, Iso.refl_hom, Category.id_comp, Functor.comp_obj,
            NatTrans.id_app, Category.comp_id]; rfl))
      (fun {x y} f ↦ by ext t; cases t <;> simp [incl])
  counitIso := NatIso.ofComponents (fun F ↦ Iso.refl _)
  functor_unitIso_comp x := by
    simp only [Functor.id_obj, Functor.comp_obj, liftUnique, lift_obj, NatIso.ofComponents_hom_app,
      Iso.refl_hom, Category.comp_id]
    ext <;> rfl

end

end WithInitial

set_option backward.defeqAttrib.useBackward true in
open Opposite in
/-- The opposite category of `WithTerminal C` is equivalent to `WithInitial Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WithTerminal`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] → (CategoryTheo
ry.WithTerminal C)ᵒᵖ ≌ CategoryTheory.WithInitial Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite category of `WithTerminal C` is equivalent to `WithInitial Cᵒᵖ`.
-/
def WithTerminal.opEquiv : (WithTerminal C)ᵒᵖ ≌ WithInitial Cᵒᵖ where
  functor :=
    { obj := fun ⟨x⟩ ↦ match x with
      | of x => .of <| op x
      | star => .star
      map := fun {x y} ⟨f⟩ ↦
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op star, op (of _), _ => WithInitial.starInitial.to _
        | op star, op star, _ => 𝟙 _
      map_id := fun ⟨x⟩ ↦ by cases x <;> rfl
      map_comp := fun {x y z} ⟨f⟩ ⟨g⟩ ↦
        match x, y, z, f, g with
        | op (of x), op (of y), op (of z), f, g => rfl
        | _, op (of y), op star, f, g => (g : PEmpty).elim
        | op (of x), op star, _, f, _ => (f : PEmpty).elim
        | op star, _, _, f, g => rfl }
  inverse :=
    { obj := fun x ↦
      match x with
        | .of x => op <| .of <| x.unop
        | .star => op .star
      map := fun {x y} f ↦
        match x, y, f with
        | .of (op x), .of (op y), f => WithInitial.down f
        | .star, .of (op _), _ => op <| WithTerminal.starTerminal.from _
        | .star, .star, _ => 𝟙 _
      map_id := fun x ↦ by cases x <;> rfl
      map_comp := fun {x y z} f g ↦
        match x, y, z, f, g with
        | .of (op x), .of (op y), .of (op z), f, g => rfl
        | _, .of (op y), .star, f, g => (g : PEmpty).elim
        | .of (op x), .star, _, f, _ => (f : PEmpty).elim
        | .star, _, _, f, g => by subsingleton }
  unitIso :=
    NatIso.ofComponents
      (fun ⟨x⟩ ↦ match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
      (fun {x y} ⟨f⟩ ↦ match x, y, f with
        | op (of x), op (of y), f => by
            simp only [Functor.id_obj, Functor.comp_obj,
              Functor.id_map, Iso.refl_hom, Category.comp_id, Functor.comp_map, Category.id_comp]
            rfl
        | op star, op (of _), _ => rfl
        | op star, op star, _ => rfl)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦ match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
  functor_unitIso_comp := fun ⟨x⟩ ↦
    match x with
    | .of x => by
        simp only [op_unop, Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
          Iso.refl_hom, Category.comp_id]
        rfl
    | .star => rfl

set_option backward.defeqAttrib.useBackward true in
open Opposite in
/-- The opposite category of `WithInitial C` is equivalent to `WithTerminal Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.W
ithInitial`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] → (CategoryTheo
ry.WithInitial C)ᵒᵖ ≌ CategoryTheory.WithTerminal Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite category of `WithInitial C` is equivalent to `WithTerminal Cᵒᵖ`.
-/
def WithInitial.opEquiv : (WithInitial C)ᵒᵖ ≌ WithTerminal Cᵒᵖ where
  functor :=
    { obj := fun ⟨x⟩ ↦
        match x with
        | of x => .of <| op x
        | star => .star
      map := fun {x y} ⟨f⟩ ↦
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op (of _), op star, _ => WithTerminal.starTerminal.from _
        | op star, op star, _ => 𝟙 _
      map_id := fun ⟨x⟩ ↦ by cases x <;> rfl
      map_comp := fun {x y z} ⟨f⟩ ⟨g⟩ ↦
        match x, y, z, f, g with
        | op (of x), op (of y), op (of z), f, g => rfl
        | _, op star, op (of y), f, g => (g : PEmpty).elim
        | op star, op (of x), _, f, _ => (f : PEmpty).elim
        | _, _, op star, f, g => by subsingleton }
  inverse :=
    { obj := fun x ↦
        match x with
        | .of x => op <| .of <| x.unop
        | .star => op .star
      map := fun {x y} f ↦
        match x, y, f with
        | .of (op x), .of (op y), f => WithInitial.down f
        | .of (op _), .star, _ => op <| WithInitial.starInitial.to _
        | .star, .star, _ => 𝟙 _
      map_id := fun x ↦ by cases x <;> rfl
      map_comp := fun {x y z} f g ↦
        match x, y, z, f, g with
        | .of (op x), .of (op y), .of (op z), f, g => rfl
        | _, .star, .of (op y), f, g => (g : PEmpty).elim
        | .star, .of (op x), _, f, _ => (f : PEmpty).elim
        | _, _, .star, f, g => by rfl }
  unitIso :=
    NatIso.ofComponents
      (fun ⟨x⟩ ↦ match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
      (fun {x y} f ↦ match x, y, f with
        | op (of x), op (of y), f => by
            simp only [Functor.id_obj, Functor.comp_obj,
              Functor.id_map, Iso.refl_hom, Category.comp_id, Functor.comp_map, Category.id_comp]
            rfl
        | op (of _), op star, _ => rfl
        | _, op star, _ => rfl)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦ match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
  functor_unitIso_comp := fun ⟨x⟩ ↦
    match x with
    | .of x => by
        simp only [op_unop, Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
          Iso.refl_hom, Category.comp_id]
        rfl
    | .star => rfl

end CategoryTheory

