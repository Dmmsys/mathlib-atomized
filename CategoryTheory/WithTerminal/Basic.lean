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

/--
Inductive type `WithTerminal` / 归纳类型 `WithTerminal`

English:
inductive WithTerminal
  parameters: : Type u
  constructors (2):
    - of: C -> WithTerminal
    - star: WithTerminal

中文:
归纳类型 WithTerminal
  参数: : 类型u
  构造子 (2 个):
    - of: C -> WithTerminal
    - star: WithTerminal

Depends on / 依赖: CategoryTheory, WithTerminal
-/
inductive WithTerminal : Type u
  | of : C -> WithTerminal
  | star : WithTerminal
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal

/--
Inductive type `WithInitial` / 归纳类型 `WithInitial`

English:
inductive WithInitial
  parameters: : Type u
  constructors (2):
    - of: C -> WithInitial
    - star: WithInitial

中文:
归纳类型 WithInitial
  参数: : 类型u
  构造子 (2 个):
    - of: C -> WithInitial
    - star: WithInitial

Depends on / 依赖: CategoryTheory, WithInitial
-/
inductive WithInitial : Type u
  | of : C -> WithInitial
  | star : WithInitial
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}

/-- Morphisms for `WithTerminal C`. -/
@[simp]
/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: : WithTerminal C -> WithTerminal C -> Type v

中文:
定义 态射
  签名: : WithTerminal C -> WithTerminal C -> 类型v
-/
def Hom : WithTerminal C -> WithTerminal C -> Type v
  | of X, of Y => X ⟶ Y
  | star, of _ => PEmpty
  | _, star => PUnit
attribute [nolint simpNF] Hom.eq_3

/-- Identity morphisms for `WithTerminal C`. -/
@[simp]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : forall X : WithTerminal C, Hom X X

中文:
定义 id
  签名: : 对任意 X : WithTerminal C, 态射 X X
-/
def id : forall X : WithTerminal C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `WithTerminal C`. -/
@[simp]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : forall {X Y Z : WithTerminal C}, Hom X Y -> Hom Y Z -> Hom X Z

中文:
定义 comp
  签名: : 对任意 {X Y Z : WithTerminal C}, 态射 X Y -> 态射 Y Z -> 态射 X Z
-/
def comp : forall {X Y Z : WithTerminal C}, Hom X Y -> Hom Y Z -> Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | of _X, _, star => fun _f _g => PUnit.unit
  | star, of _X, _ => fun f _g => PEmpty.elim f
  | _, star, of _Y => fun _f g => PEmpty.elim g
  | star, star, star => fun _ _ => PUnit.unit
#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] comp.eq_2 comp.eq_4

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/--
lemma `false_of_from_star'` / 引理 `false_of_from_star'`

English:
lemma false_of_from_star'
  given: {X : C} (f : Hom star (of X))
  statement: False
  proof: (f : PEmpty).elim

中文:
引理 false_of_from_star'
  条件: {X : C} (f : 态射 star (of X))
  结论: 假
  证明: (f : PEmpty).elim

Depends on / 依赖: PEmpty
-/
lemma false_of_from_star' {X : C} (f : Hom star (of X)) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{v} (WithTerminal C)
  body: Hom X Y
  id _ := id _
  comp := comp

中文:
实例 :
  签名: 范畴.{v} (WithTerminal C)
  定义体: Hom X Y
  id _ := id _
  comp := comp
-/
instance : Category.{v} (WithTerminal C) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: {X Y : C} (f : of X ⟶ of Y)
  body: f

中文:
定义 down
  签名: {X Y : C} (f : of X ⟶ of Y)
  定义体: f
-/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `down_id` / 引理 `down_id`

English:
lemma down_id
  given: {X : C}
  statement: down (𝟙 (of X)) = 𝟙 X
  proof: rfl

中文:
引理 down_id
  条件: {X : C}
  结论: down (𝟙 (of X)) = 𝟙 X
  证明: rfl
-/
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `down_comp` / 引理 `down_comp`

English:
lemma down_comp
  given: {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z)
  proof: rfl

中文:
引理 down_comp
  条件: {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z)
  证明: rfl
-/
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[aesop safe destruct (rule_sets := [CategoryTheory])]
/--
lemma `false_of_from_star` / 引理 `false_of_from_star`

English:
lemma false_of_from_star
  given: {X : C} (f : star ⟶ of X)
  statement: False
  proof: (f : PEmpty).elim

中文:
引理 false_of_from_star
  条件: {X : C} (f : star ⟶ of X)
  结论: 假
  证明: (f : PEmpty).elim

Depends on / 依赖: PEmpty
-/
lemma false_of_from_star {X : C} (f : star ⟶ of X) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : C ⥤ WithTerminal C where
  body: of
  map f := f

中文:
定义 incl
  签名: : C ⥤ WithTerminal C where
  定义体: of
  map f := f
-/
def incl : C ⥤ WithTerminal C where
  obj := of
  map f := f

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl : C ⥤ _).Full
  body: ⟨f, rfl⟩

中文:
实例 :
  签名: (incl : C ⥤ _).满
  定义体: ⟨f, rfl⟩
-/
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl : C ⥤ _).Faithful

中文:
实例 :
  签名: (incl : C ⥤ _).忠实
-/
instance : (incl : C ⥤ _).Faithful where

set_option backward.isDefEq.respectTransparency.types false in
/-- Map `WithTerminal` with respect to a functor `F : C ⥤ D`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {D : Type*} [Category* D] (F : C ⥤ D)
  body: match X with
| of x => of F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of _, star, _ => PUnit.unit
    | star, star, _ => PUnit.unit

中文:
定义 map
  签名: {D : 类型} [范畴* D] (F : C ⥤ D)
  定义体: match X with
| of x => of F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of _, star, _ => PUnit.unit
    | star, star, _ => PUnit.unit

Depends on / 依赖: F.map, F.obj, PUnit.unit
-/
def map {D : Type*} [Category* D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D where
  obj X :=
    match X with
| of x => of F.obj x
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
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: (C : Type*) [Category* C]
  body: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

中文:
定义 mapId
  签名: (C : 类型) [范畴* C]
  定义体: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)
  body: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

中文:
定义 mapComp
  签名: {D E : 类型} [范畴* D] [范畴* E] (F : C ⥤ D) (G : D ⥤ E)
  定义体: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
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
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: {D : Type*} [Category* D] {F G : C ⥤ D} (η : F ⟶ G)
  body: fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | of x, star, _ => rfl
    | star, star, _ => rfl

中文:
定义 map₂
  签名: {D : 类型} [范畴* D] {F G : C ⥤ D} (η : F ⟶ G)
  定义体: fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | of x, star, _ => rfl
    | star, star, _ => rfl
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
/--
Definition of `prelaxfunctor` / `prelaxfunctor` 的定义

English:
definition prelaxfunctor
  signature: : PrelaxFunctor Cat Cat where
  body: Cat.of (WithTerminal C)
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

中文:
定义 prelaxfunctor
  签名: : 预松弛函子 Cat Cat where
  定义体: Cat.of (WithTerminal C)
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

Depends on / 依赖: Cat.of, WithTerminal
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
/--
Definition of `pseudofunctor` / `pseudofunctor` 的定义

English:
definition pseudofunctor
  signature: : Pseudofunctor Cat Cat where
  body: prelaxfunctor
  mapId C := Cat.Hom.isoMk (mapId C)
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
  

中文:
定义 pseudofunctor
  签名: : Pseudofunctor Cat Cat where
  定义体: prelaxfunctor
  mapId C := Cat.Hom.isoMk (mapId C)
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
  

Depends on / 依赖: prelaxfunctor
-/
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
  mapId C := Cat.Hom.isoMk (mapId C)
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
instance {X : WithTerminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of _ => PUnit.unit
    | star => PUnit.unit
  uniq := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `starTerminal` / `starTerminal` 的定义

English:
definition starTerminal
  signature: : Limits.IsTerminal (star : WithTerminal C)
  body: Limits.IsTerminal.ofUnique _

中文:
定义 starTerminal
  签名: : Limits.是终止 (star : WithTerminal C)
  定义体: Limits.IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.ofUnique, ofUnique
-/
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasTerminal (WithTerminal C)
  body: Limits.hasTerminal_of_unique star

中文:
实例 :
  签名: Limits.有终止 (WithTerminal C)
  定义体: Limits.hasTerminal_of_unique star

Depends on / 依赖: Limits, Limits.hasTerminal_of_unique, hasTerminal_of_unique
-/
instance : Limits.HasTerminal (WithTerminal C) := Limits.hasTerminal_of_unique star

/-- The isomorphism between star and an abstract terminal object of `WithTerminal C` -/
@[simps!]
/--
Definition of `starIsoTerminal` / `starIsoTerminal` 的定义

English:
definition starIsoTerminal
  signature: : star ≅ ⊤_ (WithTerminal C)
  body: starTerminal.uniqueUpToIso (Limits.terminalIsTerminal)

中文:
定义 starIsoTerminal
  签名: : star ≅ ⊤_ (WithTerminal C)
  定义体: starTerminal.uniqueUpToIso (Limits.terminalIsTerminal)

Depends on / 依赖: Limits, Limits.terminalIsTerminal, starTerminal, starTerminal.uniqueUpToIso, terminalIsTerminal, uniqueUpToIso
-/
noncomputable def starIsoTerminal : star ≅ ⊤_ (WithTerminal C) :=
  starTerminal.uniqueUpToIso (Limits.terminalIsTerminal)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a functor `F : C ⥤ D` to `WithTerminal C ⥤ D`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
  body: match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of x, star, _ => M x
    | star, star, _ => 𝟙 Z

中文:
定义 lift
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, F.obj x ⟶ Z)
  定义体: match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of x, star, _ => M x
    | star, star, _ => 𝟙 Z

Depends on / 依赖: F.map, F.obj
-/
def lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
    (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D where
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
/--
Definition of `inclLift` / `inclLift` 的定义

English:
definition inclLift
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 inclLift
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, F.obj x ⟶ Z)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
    (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(lift F _ _).obj WithTerminal.star` with `Z`. -/
@[simps!]
/--
Definition of `liftStar` / `liftStar` 的定义

English:
definition liftStar
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
  body: eqToIso rfl

中文:
定义 liftStar
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, F.obj x ⟶ Z)
  定义体: eqToIso rfl

Depends on / 依赖: eqToIso
-/
def liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
    (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_map_liftStar` / 定理 `lift_map_liftStar`

English:
theorem lift_map_liftStar
  statement: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
  proof: by
  simp
  rfl

中文:
定理 lift_map_liftStar
  结论: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, F.obj x ⟶ Z)
  证明: by
  simp
  rfl
-/
theorem lift_map_liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
    (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).hom =
      (inclLift F M hM).hom.app x ≫ M x := by
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The uniqueness of `lift`. -/
@[simp]
/--
Definition of `liftUnique` / `liftUnique` 的定义

English:
definition liftUnique
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
  body: NatIso.ofComponents
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

中文:
定义 liftUnique
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, F.obj x ⟶ Z)
  定义体: NatIso.ofComponents
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

Depends on / 依赖: G.map, NatIso, NatIso.ofComponents, h.app, h.hom.naturality, hG.hom, naturality, ofComponents
-/
def liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, F.obj x ⟶ Z)
    (hM : forall (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : forall x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) :
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
/--
Definition of `liftToTerminal` / `liftToTerminal` 的定义

English:
definition liftToTerminal
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
  body: lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _

中文:
定义 liftToTerminal
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.是终止 Z)
  定义体: lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _

Depends on / 依赖: hZ.from, hZ.hom_ext, hom_ext
-/
def liftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    WithTerminal C ⥤ D :=
  lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps!]
/--
Definition of `inclLiftToTerminal` / `inclLiftToTerminal` 的定义

English:
definition inclLiftToTerminal
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
  body: inclLift _ _ _

中文:
定义 inclLiftToTerminal
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.是终止 Z)
  定义体: inclLift _ _ _

Depends on / 依赖: inclLift
-/
def inclLiftToTerminal {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps!]
/--
Definition of `liftToTerminalUnique` / `liftToTerminalUnique` 的定义

English:
definition liftToTerminalUnique
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
  body: liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _

中文:
定义 liftToTerminalUnique
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.是终止 Z)
  定义体: liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _

Depends on / 依赖: hZ.from, hZ.hom_ext, hom_ext, liftUnique
-/
def liftToTerminalUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
/--
Definition of `homFrom` / `homFrom` 的定义

English:
definition homFrom
  signature: (X : C)
  body: starTerminal.from _

中文:
定义 homFrom
  签名: (X : C)
  定义体: starTerminal.from _

Depends on / 依赖: starTerminal, starTerminal.from
-/
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_of_from_star` / 实例 `isIso_of_from_star`

English:
instance isIso_of_from_star
  signature: {X : WithTerminal C} (f : star ⟶ X)
  body: match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩

中文:
实例 isIso_of_from_star
  签名: {X : WithTerminal C} (f : star ⟶ X)
  定义体: match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩

Depends on / 依赖: f.elim
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
/--
Definition of `mkCommaObject` / `mkCommaObject` 的定义

English:
definition mkCommaObject
  signature: (F : WithTerminal C ⥤ D)
  body: F.obj .star
  left := (incl ⋙ F)
  hom :=
    { app x := F.map (starTerminal.from (.of x))
      naturality x y f := by
        dsimp
        rw [Category.comp_id]; rw [← F.map_comp]
        congr 1 }

中文:
定义 mkCommaObject
  签名: (F : WithTerminal C ⥤ D)
  定义体: F.obj .star
  left := (incl ⋙ F)
  hom :=
    { app x := F.map (starTerminal.from (.of x))
      naturality x y f := by
        dsimp
        rw [Category.comp_id]; rw [← F.map_comp]
        congr 1 }

Depends on / 依赖: F.obj
-/
def mkCommaObject (F : WithTerminal C ⥤ D) : Comma (𝟭 (C ⥤ D)) (Functor.const C) where
  right := F.obj .star
  left := (incl ⋙ F)
  hom :=
    { app x := F.map (starTerminal.from (.of x))
      naturality x y f := by
        dsimp
        rw [Category.comp_id]; rw [← F.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism of functors `WithTerminal C ⥤ D` gives a morphism between the associated comma
objects. -/
@[simps!]
/--
Definition of `mkCommaMorphism` / `mkCommaMorphism` 的定义

English:
definition mkCommaMorphism
  signature: {F G : WithTerminal C ⥤ D} (η : F ⟶ G)
  body: η.app .star
  left := Functor.whiskerLeft incl η

中文:
定义 mkCommaMorphism
  签名: {F G : WithTerminal C ⥤ D} (η : F ⟶ G)
  定义体: η.app .star
  left := Functor.whiskerLeft incl η
-/
def mkCommaMorphism {F G : WithTerminal C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶ mkCommaObject G where
  right := η.app .star
  left := Functor.whiskerLeft incl η

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An element of the comma category `Comma (𝟭 (C ⥤ D)) (Functor.const C)` can be seen as a
functor `WithTerminal C ⥤ D`. -/
@[simps!]
/--
Definition of `ofCommaObject` / `ofCommaObject` 的定义

English:
definition ofCommaObject
  signature: (c : Comma (𝟭 (C ⥤ D)) (Functor.const C))
  body: lift (Z := c.right) c.left (fun x => c.hom.app x) (fun x y f => by simp)

中文:
定义 ofCommaObject
  签名: (c : 交换a (𝟭 (C ⥤ D)) (函子.const C))
  定义体: lift (Z := c.right) c.left (fun x => c.hom.app x) (fun x y f => by simp)

Depends on / 依赖: c.hom.app, c.left, c.right
-/
def ofCommaObject (c : Comma (𝟭 (C ⥤ D)) (Functor.const C)) : WithTerminal C ⥤ D :=
  lift (Z := c.right) c.left (fun x => c.hom.app x) (fun x y f => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `Comma (𝟭 (C ⥤ D)) (Functor.const C)` gives a morphism between the associated
functors `WithTerminal C ⥤ D`. -/
@[simps!]
/--
Definition of `ofCommaMorphism` / `ofCommaMorphism` 的定义

English:
definition ofCommaMorphism
  signature: {c c' : Comma (𝟭 (C ⥤ D)) (Functor.const C)} (φ : c ⟶ c')
  body: match x with
    | of x => φ.left.app x
    | star => φ.right
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | of a, star, _ => by simp; simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

中文:
定义 ofCommaMorphism
  签名: {c c' : 交换a (𝟭 (C ⥤ D)) (函子.const C)} (φ : c ⟶ c')
  定义体: match x with
    | of x => φ.left.app x
    | star => φ.right
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | of a, star, _ => by simp; simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

Depends on / 依赖: CommaMorphism, CommaMorphism.w, f.app, left.app, naturality
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
    | of a, star, _ => by simp; simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The category of functors `WithTerminal C ⥤ D` is equivalent to the category
`Comma (𝟭 (C ⥤ D)) (const C) `. -/
@[simps!]
/--
Definition of `equivComma` / `equivComma` 的定义

English:
definition equivComma
  signature: : (WithTerminal C ⥤ D) ≌ Comma (𝟭 (C ⥤ D)) (Functor.const C) where
  body: { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starTerminal.from (of x)))
        (fun x y f => by
          simp 

中文:
定义 equivComma
  签名: : (WithTerminal C ⥤ D) ≌ 交换a (𝟭 (C ⥤ D)) (函子.const C) where
  定义体: { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starTerminal.from (of x)))
        (fun x y f => by
          simp 

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, F.map, F.map_comp, Functor, Functor.comp_map, Functor.comp_obj, Iso.refl, Iso.refl_hom, NatIso, NatIso.ofComponents, NatTrans, NatTrans.id_app, comp_id, comp_map, comp_obj, id_app, id_comp, inverse
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
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starTerminal.from (of x)))
        (fun x y f => by
          simp only [Functor.comp_obj, Functor.comp_map]
          rw [← F.map_comp]
          congr 1)
        F (Iso.refl _) (Iso.refl _)
        (fun x => by
          simp only [Iso.refl_hom, Category.id_comp, Functor.comp_obj,
            NatTrans.id_app, Category.comp_id]; rfl))
      (fun {x y} f => by ext t; cases t <;> simp [incl])
  counitIso := NatIso.ofComponents (fun F => Iso.refl _)
  functor_unitIso_comp x := by
    simp only [Functor.id_obj, Functor.comp_obj, liftUnique, lift_obj, NatIso.ofComponents_hom_app,
      Iso.refl_hom, Category.comp_id]
    ext <;> rfl

end

open CategoryTheory.Limits CategoryTheory.Limits.WidePullbackShape

/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: {J : Type*}
  body: fun _ _ => by
  constructor
  intro a b
  casesm* WithTerminal _, (_ : WithTerminal _) ⟶ (_ : WithTerminal _)
  · exact congr_arg (ULift.up ∘ PLift.up) rfl
  · rfl
  · rfl

中文:
实例 subsingleton_hom
  签名: {J : 类型}
  定义体: fun _ _ => by
  constructor
  intro a b
  casesm* WithTerminal _, (_ : WithTerminal _) ⟶ (_ : WithTerminal _)
  · exact congr_arg (ULift.up ∘ PLift.up) rfl
  · rfl
  · rfl

Depends on / 依赖: PLift.up, ULift.up, WithTerminal, casesm, congr_arg
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
/--
Definition of `widePullbackShapeEquivObj` / `widePullbackShapeEquivObj` 的定义

English:
definition widePullbackShapeEquivObj
  signature: {J : Type*}
  body: by cases x <;> simp
  right_inv x := by cases x <;> simp

中文:
定义 widePullbackShapeEquivObj
  签名: {J : 类型}
  定义体: by cases x <;> simp
  right_inv x := by cases x <;> simp
-/
private def widePullbackShapeEquivObj {J : Type*} :
    WidePullbackShape J ≃ WithTerminal (Discrete J) where
  toFun
| .some x => .of .mk x
  | .none => .star
  invFun
| .of x => .some Discrete.as x
  | .star => .none
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

set_option backward.privateInPublic true in
/--
Definition of `widePullbackShapeEquivMap` / `widePullbackShapeEquivMap` 的定义

English:
definition widePullbackShapeEquivMap
  signature: {J : Type*} (x y : WidePullbackShape J)
  body: match x, y with
  | some x, some y =>
    cast (by
        have eq : x = y := PLift.down (ULift.down (down f))
        rw [eq]
        rfl) (Hom.id (some y))
  | none, some y => by cases f
  | some x, none => .term x
  | none, none => .id none
  left_inv f := by apply Subsingleton.allEq
  right_inv 

中文:
定义 widePullbackShapeEquivMap
  签名: {J : 类型} (x y : WidePullbackShape J)
  定义体: match x, y with
  | some x, some y =>
    cast (by
        have eq : x = y := PLift.down (ULift.down (down f))
        rw [eq]
        rfl) (Hom.id (some y))
  | none, some y => by cases f
  | some x, none => .term x
  | none, none => .id none
  left_inv f := by apply Subsingleton.allEq
  right_inv 
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
/--
Definition of `widePullbackShapeEquiv` / `widePullbackShapeEquiv` 的定义

English:
definition widePullbackShapeEquiv
  signature: {J : Type*}
  body: widePullbackShapeEquivObj
  functor.map := widePullbackShapeEquivMap _ _
  inverse.obj := widePullbackShapeEquivObj.symm
  inverse.map f := (widePullbackShapeEquivMap _ _).symm (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  unitIso := NatIso.ofComponents fun x => eqToIso (by aesop)
  counitIso := Nat

中文:
定义 widePullbackShapeEquiv
  签名: {J : 类型}
  定义体: widePullbackShapeEquivObj
  functor.map := widePullbackShapeEquivMap _ _
  inverse.obj := widePullbackShapeEquivObj.symm
  inverse.map f := (widePullbackShapeEquivMap _ _).symm (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  unitIso := NatIso.ofComponents fun x => eqToIso (by aesop)
  counitIso := Nat

Depends on / 依赖: widePullbackShapeEquivObj
-/
def widePullbackShapeEquiv {J : Type*} : WidePullbackShape J ≌ WithTerminal (Discrete J) where
  functor.obj := widePullbackShapeEquivObj
  functor.map := widePullbackShapeEquivMap _ _
  inverse.obj := widePullbackShapeEquivObj.symm
  inverse.map f := (widePullbackShapeEquivMap _ _).symm (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  unitIso := NatIso.ofComponents fun x => eqToIso (by aesop)
  counitIso := NatIso.ofComponents fun x => eqToIso (by aesop)

end WithTerminal

namespace WithInitial

variable {C}

/-- Morphisms for `WithInitial C`. -/
@[simp]
/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: : WithInitial C -> WithInitial C -> Type v

中文:
定义 态射
  签名: : WithInitial C -> WithInitial C -> 类型v
-/
def Hom : WithInitial C -> WithInitial C -> Type v
  | of X, of Y => X ⟶ Y
  | of _, _ => PEmpty
  | star, _ => PUnit
attribute [nolint simpNF] Hom.eq_2

/-- Identity morphisms for `WithInitial C`. -/
@[simp]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : forall X : WithInitial C, Hom X X

中文:
定义 id
  签名: : 对任意 X : WithInitial C, 态射 X X
-/
def id : forall X : WithInitial C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `WithInitial C`. -/
@[simp]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : forall {X Y Z : WithInitial C}, Hom X Y -> Hom Y Z -> Hom X Z

中文:
定义 comp
  签名: : 对任意 {X Y Z : WithInitial C}, 态射 X Y -> 态射 Y Z -> 态射 X Z
-/
def comp : forall {X Y Z : WithInitial C}, Hom X Y -> Hom Y Z -> Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | star, _, of _X => fun _f _g => PUnit.unit
  | _, of _X, star => fun _f g => PEmpty.elim g
  | of _Y, star, _ => fun f _g => PEmpty.elim f
  | star, star, star => fun _ _ => PUnit.unit
attribute [nolint simpNF] comp.eq_3

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/--
lemma `false_of_to_star'` / 引理 `false_of_to_star'`

English:
lemma false_of_to_star'
  given: {X : C} (f : Hom (of X) star)
  statement: False
  proof: (f : PEmpty).elim

中文:
引理 false_of_to_star'
  条件: {X : C} (f : 态射 (of X) star)
  结论: 假
  证明: (f : PEmpty).elim

Depends on / 依赖: PEmpty
-/
lemma false_of_to_star' {X : C} (f : Hom (of X) star) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{v} (WithInitial C)
  body: Hom X Y
  id X := id X
  comp f g := comp f g

中文:
实例 :
  签名: 范畴.{v} (WithInitial C)
  定义体: Hom X Y
  id X := id X
  comp f g := comp f g
-/
instance : Category.{v} (WithInitial C) where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: {X Y : C} (f : of X ⟶ of Y)
  body: f

中文:
定义 down
  签名: {X Y : C} (f : of X ⟶ of Y)
  定义体: f
-/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `down_id` / 引理 `down_id`

English:
lemma down_id
  given: {X : C}
  statement: down (𝟙 (of X)) = 𝟙 X
  proof: rfl

中文:
引理 down_id
  条件: {X : C}
  结论: down (𝟙 (of X)) = 𝟙 X
  证明: rfl
-/
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `down_comp` / 引理 `down_comp`

English:
lemma down_comp
  given: {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z)
  proof: rfl

中文:
引理 down_comp
  条件: {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z)
  证明: rfl
-/
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[aesop safe destruct (rule_sets := [CategoryTheory])]
/--
lemma `false_of_to_star` / 引理 `false_of_to_star`

English:
lemma false_of_to_star
  given: {X : C} (f : of X ⟶ star)
  statement: False
  proof: (f : PEmpty).elim

中文:
引理 false_of_to_star
  条件: {X : C} (f : of X ⟶ star)
  结论: 假
  证明: (f : PEmpty).elim

Depends on / 依赖: PEmpty
-/
lemma false_of_to_star {X : C} (f : of X ⟶ star) : False := (f : PEmpty).elim

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : C ⥤ WithInitial C where
  body: of
  map f := f

中文:
定义 incl
  签名: : C ⥤ WithInitial C where
  定义体: of
  map f := f
-/
def incl : C ⥤ WithInitial C where
  obj := of
  map f := f

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl : C ⥤ _).Full
  body: ⟨f, rfl⟩

中文:
实例 :
  签名: (incl : C ⥤ _).满
  定义体: ⟨f, rfl⟩
-/
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl : C ⥤ _).Faithful

中文:
实例 :
  签名: (incl : C ⥤ _).忠实
-/
instance : (incl : C ⥤ _).Faithful where

set_option backward.isDefEq.respectTransparency.types false in
/-- Map `WithInitial` with respect to a functor `F : C ⥤ D`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {D : Type*} [Category* D] (F : C ⥤ D)
  body: match X with
| of x => of F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => PUnit.unit
    | star, star, _ => PUnit.unit

中文:
定义 map
  签名: {D : 类型} [范畴* D] (F : C ⥤ D)
  定义体: match X with
| of x => of F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => PUnit.unit
    | star, star, _ => PUnit.unit

Depends on / 依赖: F.map, F.obj, PUnit.unit
-/
def map {D : Type*} [Category* D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D where
  obj X :=
    match X with
| of x => of F.obj x
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
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: (C : Type*) [Category* C]
  body: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

中文:
定义 mapId
  签名: (C : 类型) [范畴* C]
  定义体: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def mapId (C : Type*) [Category* C] : map (𝟭 C) ≅ 𝟭 (WithInitial C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)
  body: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

中文:
定义 mapComp
  签名: {D E : 类型} [范畴* D] [范畴* E] (F : C ⥤ D) (G : D ⥤ E)
  定义体: NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
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
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: {D : Type*} [Category* D] {F G : C ⥤ D} (η : F ⟶ G)
  body: fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | star, of x, _ => rfl
    | star, star, _ => rfl

中文:
定义 map₂
  签名: {D : 类型} [范畴* D] {F G : C ⥤ D} (η : F ⟶ G)
  定义体: fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | star, of x, _ => rfl
    | star, star, _ => rfl
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
/--
Definition of `prelaxfunctor` / `prelaxfunctor` 的定义

English:
definition prelaxfunctor
  signature: : PrelaxFunctor Cat Cat where
  body: Cat.of (WithInitial C)
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

中文:
定义 prelaxfunctor
  签名: : 预松弛函子 Cat Cat where
  定义体: Cat.of (WithInitial C)
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

Depends on / 依赖: Cat.of, WithInitial
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
/--
Definition of `pseudofunctor` / `pseudofunctor` 的定义

English:
definition pseudofunctor
  signature: : Pseudofunctor Cat Cat where
  body: prelaxfunctor
mapId C := Cat.Hom.isoMk mapId C
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
    ex

中文:
定义 pseudofunctor
  签名: : Pseudofunctor Cat Cat where
  定义体: prelaxfunctor
mapId C := Cat.Hom.isoMk mapId C
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
    ex

Depends on / 依赖: prelaxfunctor
-/
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
mapId C := Cat.Hom.isoMk mapId C
mapComp _ _ := Cat.Hom.isoMk mapComp _ _
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
instance {X : WithInitial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of _x => PUnit.unit
    | star => PUnit.unit
  uniq := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `starInitial` / `starInitial` 的定义

English:
definition starInitial
  signature: : Limits.IsInitial (star : WithInitial C)
  body: Limits.IsInitial.ofUnique _

中文:
定义 starInitial
  签名: : Limits.IsInitial (star : WithInitial C)
  定义体: Limits.IsInitial.ofUnique _

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofUnique, ofUnique
-/
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasInitial (WithInitial C)
  body: Limits.hasInitial_of_unique star

中文:
实例 :
  签名: Limits.HasInitial (WithInitial C)
  定义体: Limits.hasInitial_of_unique star

Depends on / 依赖: Limits, Limits.hasInitial_of_unique, hasInitial_of_unique
-/
instance : Limits.HasInitial (WithInitial C) := Limits.hasInitial_of_unique star

/-- The isomorphism between star and an abstract initial object of `WithInitial C` -/
@[simps!]
/--
Definition of `starIsoInitial` / `starIsoInitial` 的定义

English:
definition starIsoInitial
  signature: : star ≅ ⊥_ (WithInitial C)
  body: starInitial.uniqueUpToIso (Limits.initialIsInitial)

中文:
定义 starIsoInitial
  签名: : star ≅ ⊥_ (WithInitial C)
  定义体: starInitial.uniqueUpToIso (Limits.initialIsInitial)

Depends on / 依赖: Limits, Limits.initialIsInitial, initialIsInitial, starInitial, starInitial.uniqueUpToIso, uniqueUpToIso
-/
noncomputable def starIsoInitial : star ≅ ⊥_ (WithInitial C) :=
  starInitial.uniqueUpToIso (Limits.initialIsInitial)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a functor `F : C ⥤ D` to `WithInitial C ⥤ D`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
  body: match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => M _
    | star, star, _ => 𝟙 _

中文:
定义 lift
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, Z ⟶ F.obj x)
  定义体: match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => M _
    | star, star, _ => 𝟙 _

Depends on / 依赖: F.map, F.obj
-/
def lift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
    (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D where
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
/--
Definition of `inclLift` / `inclLift` 的定义

English:
definition inclLift
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 inclLift
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, Z ⟶ F.obj x)
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def inclLift {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
    (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(lift F _ _).obj WithInitial.star` with `Z`. -/
@[simps!]
/--
Definition of `liftStar` / `liftStar` 的定义

English:
definition liftStar
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
  body: eqToIso rfl

中文:
定义 liftStar
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, Z ⟶ F.obj x)
  定义体: eqToIso rfl

Depends on / 依赖: eqToIso
-/
def liftStar {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
    (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `liftStar_lift_map` / 定理 `liftStar_lift_map`

English:
theorem liftStar_lift_map
  statement: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
  proof: by
  simp [incl]

中文:
定理 liftStar_lift_map
  结论: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, Z ⟶ F.obj x)
  证明: by
  simp [incl]
-/
theorem liftStar_lift_map {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
    (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) =
      M x ≫ (inclLift F M hM).hom.app x := by
  simp [incl]

set_option backward.isDefEq.respectTransparency.types false in
/-- The uniqueness of `lift`. -/
@[simp]
/--
Definition of `liftUnique` / `liftUnique` 的定义

English:
definition liftUnique
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
  body: NatIso.ofComponents
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
        erw [← Iso.eq_inv_comp, ← Cate

中文:
定义 liftUnique
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (M : 对任意 x : C, Z ⟶ F.obj x)
  定义体: NatIso.ofComponents
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
        erw [← Iso.eq_inv_comp, ← Cate

Depends on / 依赖: Category, Category.assoc, G.map, Iso.eq_inv_comp, NatIso, NatIso.ofComponents, eq_inv_comp, h.app, h.hom.app, h.hom.naturality, hG.hom, naturality, ofComponents
-/
def liftUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (M : forall x : C, Z ⟶ F.obj x)
    (hM : forall (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : forall x : C, hG.symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) :
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
/--
Definition of `liftToInitial` / `liftToInitial` 的定义

English:
definition liftToInitial
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  body: lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _

中文:
定义 liftToInitial
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  定义体: lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _

Depends on / 依赖: hZ.hom_ext, hZ.to, hom_ext
-/
def liftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    WithInitial C ⥤ D :=
  lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps!]
/--
Definition of `inclLiftToInitial` / `inclLiftToInitial` 的定义

English:
definition inclLiftToInitial
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  body: inclLift _ _ _

中文:
定义 inclLiftToInitial
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  定义体: inclLift _ _ _

Depends on / 依赖: inclLift
-/
def inclLiftToInitial {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps!]
/--
Definition of `liftToInitialUnique` / `liftToInitialUnique` 的定义

English:
definition liftToInitialUnique
  signature: {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  body: liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _

中文:
定义 liftToInitialUnique
  签名: {D : 类型} [范畴* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
  定义体: liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _

Depends on / 依赖: hZ.hom_ext, hZ.to, hom_ext, liftUnique
-/
def liftToInitialUnique {D : Type*} [Category* D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
/--
Definition of `homTo` / `homTo` 的定义

English:
definition homTo
  signature: (X : C)
  body: starInitial.to _

中文:
定义 homTo
  签名: (X : C)
  定义体: starInitial.to _

Depends on / 依赖: starInitial, starInitial.to
-/
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_of_to_star` / 实例 `isIso_of_to_star`

English:
instance isIso_of_to_star
  signature: {X : WithInitial C} (f : X ⟶ star)
  body: match X with
  | of _ => f.elim
  | star => ⟨f, rfl, rfl⟩

中文:
实例 isIso_of_to_star
  签名: {X : WithInitial C} (f : X ⟶ star)
  定义体: match X with
  | of _ => f.elim
  | star => ⟨f, rfl, rfl⟩

Depends on / 依赖: f.elim
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
/--
Definition of `mkCommaObject` / `mkCommaObject` 的定义

English:
definition mkCommaObject
  signature: (F : WithInitial C ⥤ D)
  body: F.obj .star
  right := (incl ⋙ F)
  hom :=
    { app x := F.map (starInitial.to (.of x))
      naturality x y f := by
        dsimp
        rw [Category.id_comp]; rw [← F.map_comp]
        congr 1 }

中文:
定义 mkCommaObject
  签名: (F : WithInitial C ⥤ D)
  定义体: F.obj .star
  right := (incl ⋙ F)
  hom :=
    { app x := F.map (starInitial.to (.of x))
      naturality x y f := by
        dsimp
        rw [Category.id_comp]; rw [← F.map_comp]
        congr 1 }

Depends on / 依赖: F.obj
-/
def mkCommaObject (F : WithInitial C ⥤ D) : Comma (Functor.const C) (𝟭 (C ⥤ D)) where
  left := F.obj .star
  right := (incl ⋙ F)
  hom :=
    { app x := F.map (starInitial.to (.of x))
      naturality x y f := by
        dsimp
        rw [Category.id_comp]; rw [← F.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism of functors `WithInitial C ⥤ D` gives a morphism between the associated comma
objects. -/
@[simps!]
/--
Definition of `mkCommaMorphism` / `mkCommaMorphism` 的定义

English:
definition mkCommaMorphism
  signature: {F G : WithInitial C ⥤ D} (η : F ⟶ G)
  body: η.app .star
  right := Functor.whiskerLeft incl η

中文:
定义 mkCommaMorphism
  签名: {F G : WithInitial C ⥤ D} (η : F ⟶ G)
  定义体: η.app .star
  right := Functor.whiskerLeft incl η
-/
def mkCommaMorphism {F G : WithInitial C ⥤ D} (η : F ⟶ G) : mkCommaObject F ⟶ mkCommaObject G where
  left := η.app .star
  right := Functor.whiskerLeft incl η

set_option backward.defeqAttrib.useBackward true in
/-- An element of the comma category `Comma (Functor.const C) (𝟭 (C ⥤ D))` can be seen as a
functor `WithInitial C ⥤ D`. -/
@[simps!]
/--
Definition of `ofCommaObject` / `ofCommaObject` 的定义

English:
definition ofCommaObject
  signature: (c : Comma (Functor.const C) (𝟭 (C ⥤ D)))
  body: lift (Z := c.left) c.right (fun x => c.hom.app x)
    (fun x y f => by simpa using (c.hom.naturality f).symm)

中文:
定义 ofCommaObject
  签名: (c : 交换a (函子.const C) (𝟭 (C ⥤ D)))
  定义体: lift (Z := c.left) c.right (fun x => c.hom.app x)
    (fun x y f => by simpa using (c.hom.naturality f).symm)

Depends on / 依赖: c.hom.app, c.hom.naturality, c.left, c.right, naturality
-/
def ofCommaObject (c : Comma (Functor.const C) (𝟭 (C ⥤ D))) : WithInitial C ⥤ D :=
  lift (Z := c.left) c.right (fun x => c.hom.app x)
    (fun x y f => by simpa using (c.hom.naturality f).symm)

set_option backward.defeqAttrib.useBackward true in
/-- A morphism in `Comma (Functor.const C) (𝟭 (C ⥤ D))` gives a morphism between the associated
functors `WithInitial C ⥤ D`. -/
@[simps!]
/--
Definition of `ofCommaMorphism` / `ofCommaMorphism` 的定义

English:
definition ofCommaMorphism
  signature: {c c' : Comma (Functor.const C) (𝟭 (C ⥤ D))} (φ : c ⟶ c')
  body: match x with
    | of x => φ.right.app x
    | star => φ.left
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | star, of a, _ => by simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

中文:
定义 ofCommaMorphism
  签名: {c c' : 交换a (函子.const C) (𝟭 (C ⥤ D))} (φ : c ⟶ c')
  定义体: match x with
    | of x => φ.right.app x
    | star => φ.left
  naturality x y f :=
    match x, y, f with
    | of _, of _, f => by simp
    | star, of a, _ => by simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

Depends on / 依赖: CommaMorphism, CommaMorphism.w, f.app, naturality, right.app
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
    | star, of a, _ => by simpa [-CommaMorphism.w] using (congrArg (fun f => f.app a) φ.w).symm
    | star, star, _ => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The category of functors `WithInitial C ⥤ D` is equivalent to the category
`Comma (const C) (𝟭 (C ⥤ D))`. -/
@[simps!]
/--
Definition of `equivComma` / `equivComma` 的定义

English:
definition equivComma
  signature: : (WithInitial C ⥤ D) ≌ Comma (Functor.const C) (𝟭 (C ⥤ D)) where
  body: { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starInitial.to (of x)))
        (fun x y f => by
          simp onl

中文:
定义 equivComma
  签名: : (WithInitial C ⥤ D) ≌ 交换a (函子.const C) (𝟭 (C ⥤ D)) where
  定义体: { obj := mkCommaObject
      map := mkCommaMorphism }
  inverse :=
    { obj := ofCommaObject
      map := ofCommaMorphism }
  unitIso :=
    NatIso.ofComponents
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starInitial.to (of x)))
        (fun x y f => by
          simp onl

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, F.map, F.map_comp, Functor, Functor.comp_map, Functor.comp_obj, Iso.refl, Iso.refl_hom, Iso.refl_symm, NatIso, NatIso.ofComponents, NatTrans, NatTrans.id_app, comp_id, comp_map, comp_obj, id_app, id_comp
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
      (fun F => liftUnique
        (incl ⋙ F)
        (fun x => F.map (starInitial.to (of x)))
        (fun x y f => by
          simp only [Functor.comp_obj, Functor.comp_map]
          rw [← F.map_comp]
          congr 1)
        F (Iso.refl _) (Iso.refl _)
        (fun x => by
          simp only [Iso.refl_symm, Iso.refl_hom, Category.id_comp, Functor.comp_obj,
            NatTrans.id_app, Category.comp_id]; rfl))
      (fun {x y} f => by ext t; cases t <;> simp [incl])
  counitIso := NatIso.ofComponents (fun F => Iso.refl _)
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
/--
Definition of `WithTerminal.opEquiv` / `WithTerminal.opEquiv` 的定义

English:
definition WithTerminal.opEquiv
  signature: : (WithTerminal C)ᵒᵖ ≌ WithInitial Cᵒᵖ where
  body: { obj := fun ⟨x⟩ => match x with
| of x => .of op x
      | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op star, op (of _), _ => WithInitial.starInitial.to _
        | op star, op star, _ => 𝟙 _
      

中文:
定义 WithTerminal.opEquiv
  签名: : (WithTerminal C)ᵒᵖ ≌ WithInitial Cᵒᵖ where
  定义体: { obj := fun ⟨x⟩ => match x with
| of x => .of op x
      | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op star, op (of _), _ => WithInitial.starInitial.to _
        | op star, op star, _ => 𝟙 _
      

Depends on / 依赖: PEmpty, WithInitial, WithInitial.starInitial.to, WithTerminal, WithTerminal.down, map_comp, map_id, starInitial
-/
def WithTerminal.opEquiv : (WithTerminal C)ᵒᵖ ≌ WithInitial Cᵒᵖ where
  functor :=
    { obj := fun ⟨x⟩ => match x with
| of x => .of op x
      | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op star, op (of _), _ => WithInitial.starInitial.to _
        | op star, op star, _ => 𝟙 _
      map_id := fun ⟨x⟩ => by cases x <;> rfl
      map_comp := fun {x y z} ⟨f⟩ ⟨g⟩ =>
        match x, y, z, f, g with
        | op (of x), op (of y), op (of z), f, g => rfl
        | _, op (of y), op star, f, g => (g : PEmpty).elim
        | op (of x), op star, _, f, _ => (f : PEmpty).elim
        | op star, _, _, f, g => rfl }
  inverse :=
    { obj := fun x =>
      match x with
| .of x => op .of x.unop
        | .star => op .star
      map := fun {x y} f =>
        match x, y, f with
        | .of (op x), .of (op y), f => WithInitial.down f
| .star, .of (op _), _ => op WithTerminal.starTerminal.from _
        | .star, .star, _ => 𝟙 _
      map_id := fun x => by cases x <;> rfl
      map_comp := fun {x y z} f g =>
        match x, y, z, f, g with
        | .of (op x), .of (op y), .of (op z), f, g => rfl
        | _, .of (op y), .star, f, g => (g : PEmpty).elim
        | .of (op x), .star, _, f, _ => (f : PEmpty).elim
        | .star, _, _, f, g => by subsingleton }
  unitIso :=
    NatIso.ofComponents
      (fun ⟨x⟩ => match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
      (fun {x y} ⟨f⟩ => match x, y, f with
        | op (of x), op (of y), f => by
            simp only [Functor.id_obj, Functor.comp_obj,
              Functor.id_map, Iso.refl_hom, Category.comp_id, Functor.comp_map, Category.id_comp]
            rfl
        | op star, op (of _), _ => rfl
        | op star, op star, _ => rfl)
  counitIso :=
    NatIso.ofComponents
      (fun x => match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
  functor_unitIso_comp := fun ⟨x⟩ =>
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
/--
Definition of `WithInitial.opEquiv` / `WithInitial.opEquiv` 的定义

English:
definition WithInitial.opEquiv
  signature: : (WithInitial C)ᵒᵖ ≌ WithTerminal Cᵒᵖ where
  body: { obj := fun ⟨x⟩ =>
        match x with
| of x => .of op x
        | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op (of _), op star, _ => WithTerminal.starTerminal.from _
        | op star, op star, _

中文:
定义 WithInitial.opEquiv
  签名: : (WithInitial C)ᵒᵖ ≌ WithTerminal Cᵒᵖ where
  定义体: { obj := fun ⟨x⟩ =>
        match x with
| of x => .of op x
        | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op (of _), op star, _ => WithTerminal.starTerminal.from _
        | op star, op star, _

Depends on / 依赖: PEmpty, WithTerminal, WithTerminal.down, WithTerminal.starTerminal.from, map_comp, map_id, starTerminal
-/
def WithInitial.opEquiv : (WithInitial C)ᵒᵖ ≌ WithTerminal Cᵒᵖ where
  functor :=
    { obj := fun ⟨x⟩ =>
        match x with
| of x => .of op x
        | star => .star
      map := fun {x y} ⟨f⟩ =>
        match x, y, f with
        | op (of x), op (of y), f => (WithTerminal.down f).op
        | op (of _), op star, _ => WithTerminal.starTerminal.from _
        | op star, op star, _ => 𝟙 _
      map_id := fun ⟨x⟩ => by cases x <;> rfl
      map_comp := fun {x y z} ⟨f⟩ ⟨g⟩ =>
        match x, y, z, f, g with
        | op (of x), op (of y), op (of z), f, g => rfl
        | _, op star, op (of y), f, g => (g : PEmpty).elim
        | op star, op (of x), _, f, _ => (f : PEmpty).elim
        | _, _, op star, f, g => by subsingleton }
  inverse :=
    { obj := fun x =>
        match x with
| .of x => op .of x.unop
        | .star => op .star
      map := fun {x y} f =>
        match x, y, f with
        | .of (op x), .of (op y), f => WithInitial.down f
| .of (op _), .star, _ => op WithInitial.starInitial.to _
        | .star, .star, _ => 𝟙 _
      map_id := fun x => by cases x <;> rfl
      map_comp := fun {x y z} f g =>
        match x, y, z, f, g with
        | .of (op x), .of (op y), .of (op z), f, g => rfl
        | _, .star, .of (op y), f, g => (g : PEmpty).elim
        | .star, .of (op x), _, f, _ => (f : PEmpty).elim
        | _, _, .star, f, g => by rfl }
  unitIso :=
    NatIso.ofComponents
      (fun ⟨x⟩ => match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
      (fun {x y} f => match x, y, f with
        | op (of x), op (of y), f => by
            simp only [Functor.id_obj, Functor.comp_obj,
              Functor.id_map, Iso.refl_hom, Category.comp_id, Functor.comp_map, Category.id_comp]
            rfl
        | op (of _), op star, _ => rfl
        | _, op star, _ => rfl)
  counitIso :=
    NatIso.ofComponents
      (fun x => match x with
        | .of x => Iso.refl _
        | .star => Iso.refl _)
  functor_unitIso_comp := fun ⟨x⟩ =>
    match x with
    | .of x => by
        simp only [op_unop, Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
          Iso.refl_hom, Category.comp_id]
        rfl
    | .star => rfl

end CategoryTheory
