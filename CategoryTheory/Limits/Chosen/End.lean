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

/--
Definition of `ChosenCoendsOfShape` / `ChosenCoendsOfShape` 的定义

English:
class ChosenCoendsOfShape
  parameters: (J : Type*) [Category* J] (C : Type*) [Category* C]
  axioms and operations (2):
    - cowedge((F : Jᵒᵖ ⥤ J ⥤ C)) : Cowedge F
    - isCoend((F : Jᵒᵖ ⥤ J ⥤ C)) : IsColimit (cowedge F)

中文:
类 ChosenCoendsOfShape
  参数: (J : 类型) [Category* J] (C : 类型) [Category* C]
  公理与运算 (2 个):
    - cowedge((F : Jᵒᵖ ⥤ J ⥤ C)) : Cowedge F
    - isCoend((F : Jᵒᵖ ⥤ J ⥤ C)) : IsColimit (cowedge F)
-/
class ChosenCoendsOfShape (J : Type*) [Category* J] (C : Type*) [Category* C] where
  /-- The chosen cowedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  cowedge (F : Jᵒᵖ ⥤ J ⥤ C) : Cowedge F
  /-- The chosen cowedge is colimiting. -/
  isCoend (F : Jᵒᵖ ⥤ J ⥤ C) : IsColimit (cowedge F)

set_option linter.checkUnivs false in
/-- The data of chosen coends in `C`. -/
@[pp_with_univ]
/--
Definition of `ChosenCoends` / `ChosenCoends` 的定义

English:
abbreviation ChosenCoends
  signature: (C : Type*) [Category* C]
  body: forall {J : Type u} [Category.{v} J], ChosenCoendsOfShape J C

中文:
缩写 ChosenCoends
  签名: (C : 类型) [Category* C]
  定义体: forall {J : Type u} [Category.{v} J], ChosenCoendsOfShape J C

Depends on / 依赖: Category, ChosenCoendsOfShape
-/
abbrev ChosenCoends (C : Type*) [Category* C] :=
  forall {J : Type u} [Category.{v} J], ChosenCoendsOfShape J C

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenCoendsOfShape J C]

/--
Definition of `chosenCoend` / `chosenCoend` 的定义

English:
definition chosenCoend
  signature: : C
  body: (ChosenCoendsOfShape.cowedge F).pt

中文:
定义 chosenCoend
  签名: : C
  定义体: (ChosenCoendsOfShape.cowedge F).pt

Depends on / 依赖: ChosenCoendsOfShape, ChosenCoendsOfShape.cowedge, cowedge
-/
def chosenCoend : C := (ChosenCoendsOfShape.cowedge F).pt

/--
Definition of `chosenCoend.ι` / `chosenCoend.ι` 的定义

English:
definition chosenCoend.ι
  signature: (j : J)
  body: (ChosenCoendsOfShape.cowedge F).π j

@[reassoc]

中文:
定义 chosenCoend.ι
  签名: (j : J)
  定义体: (ChosenCoendsOfShape.cowedge F).π j

@[reassoc]

Depends on / 依赖: ChosenCoendsOfShape, ChosenCoendsOfShape.cowedge, cowedge
-/
def chosenCoend.ι (j : J) : (F.obj (op j)).obj j ⟶ chosenCoend F :=
  (ChosenCoendsOfShape.cowedge F).π j

@[reassoc]
/--
lemma `chosenCoend.condition` / 引理 `chosenCoend.condition`

English:
lemma chosenCoend.condition
  given: {i j : J} (f : i ⟶ j)
  proof: (ChosenCoendsOfShape.cowedge F).condition f

中文:
引理 chosenCoend.condition
  条件: {i j : J} (f : i ⟶ j)
  证明: (ChosenCoendsOfShape.cowedge F).condition f

Depends on / 依赖: ChosenCoendsOfShape, ChosenCoendsOfShape.cowedge, condition, cowedge
-/
lemma chosenCoend.condition {i j : J} (f : i ⟶ j) :
    (F.map f.op).app _ ≫ chosenCoend.ι F i = (F.obj _).map f ≫ chosenCoend.ι F j :=
  (ChosenCoendsOfShape.cowedge F).condition f

variable {F}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Morphisms out of the chosen coend are determined by their composites with `chosenCoend.ι`. -/
@[ext]
/--
lemma `chosenCoend.hom_ext` / 引理 `chosenCoend.hom_ext`

English:
lemma chosenCoend.hom_ext
  statement: {X : C} {f g : chosenCoend F ⟶ X}
  proof: by
  apply (ChosenCoendsOfShape.isCoend F).hom_ext
  rintro (a | a)
  · simpa using! _ ≫= h _
  · exact h _

中文:
引理 chosenCoend.hom_ext
  结论: {X : C} {f g : chosenCoend F ⟶ X}
  证明: by
  apply (ChosenCoendsOfShape.isCoend F).hom_ext
  rintro (a | a)
  · simpa using! _ ≫= h _
  · exact h _

Depends on / 依赖: ChosenCoendsOfShape, ChosenCoendsOfShape.isCoend, hom_ext, isCoend
-/
lemma chosenCoend.hom_ext {X : C} {f g : chosenCoend F ⟶ X}
    (h : forall j, chosenCoend.ι F j ≫ f = chosenCoend.ι F j ≫ g) : f = g := by
  apply (ChosenCoendsOfShape.isCoend F).hom_ext
  rintro (a | a)
  · simpa using! _ ≫= h _
  · exact h _

variable {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
  (hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/--
Definition of `chosenCoend.desc` / `chosenCoend.desc` 的定义

English:
definition chosenCoend.desc
  signature: : chosenCoend F ⟶ X
  body: Cowedge.IsColimit.desc (ChosenCoendsOfShape.isCoend F) f hf

@[reassoc (attr := simp)]

中文:
定义 chosenCoend.desc
  签名: : chosenCoend F ⟶ X
  定义体: Cowedge.IsColimit.desc (ChosenCoendsOfShape.isCoend F) f hf

@[reassoc (attr := simp)]

Depends on / 依赖: ChosenCoendsOfShape, ChosenCoendsOfShape.isCoend, Cowedge, Cowedge.IsColimit.desc, IsColimit, isCoend
-/
def chosenCoend.desc : chosenCoend F ⟶ X :=
  Cowedge.IsColimit.desc (ChosenCoendsOfShape.isCoend F) f hf

@[reassoc (attr := simp)]
/--
lemma `chosenCoend.ι_desc` / 引理 `chosenCoend.ι_desc`

English:
lemma chosenCoend.ι_desc
  given: (j : J)
  statement: chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j
  proof: by
  apply IsColimit.fac

中文:
引理 chosenCoend.ι_desc
  条件: (j : J)
  结论: chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j
  证明: by
  apply IsColimit.fac

Depends on / 依赖: IsColimit, IsColimit.fac, coequalizer_ext, hom_ext, ht.hom_ext
-/
lemma chosenCoend.ι_desc (j : J) : chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j := by
  apply IsColimit.fac

/--
Definition of `chosenCoend.map` / `chosenCoend.map` 的定义

English:
definition chosenCoend.map
  signature: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G)
  body: chosenCoend.desc (fun x => (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ => by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]

中文:
定义 chosenCoend.map
  签名: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G)
  定义体: chosenCoend.desc (fun x => (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ => by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: PushoutCocone, PushoutCocone.mk, chosenCoend, chosenCoend.condition, chosenCoend.desc, condition, f.app, ht.desc
-/
def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x => (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ => by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]
/--
lemma `chosenCoend.ι_map` / 引理 `chosenCoend.ι_map`

English:
lemma chosenCoend.ι_map
  given: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J)
  proof: by
  simp [chosenCoend.map]

@[simp]

中文:
引理 chosenCoend.ι_map
  条件: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J)
  证明: by
  simp [chosenCoend.map]

@[simp]

Depends on / 依赖: chosenCoend, chosenCoend.map
-/
lemma chosenCoend.ι_map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenCoend.ι F j ≫ chosenCoend.map f = (f.app _).app _ ≫ chosenCoend.ι G j := by
  simp [chosenCoend.map]

@[simp]
/--
lemma `chosenCoend.map_id` / 引理 `chosenCoend.map_id`

English:
lemma chosenCoend.map_id
  statement: chosenCoend.map (𝟙 F) = 𝟙 _
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
引理 chosenCoend.map_id
  结论: chosenCoend.map (𝟙 F) = 𝟙 _
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `chosenCoend.map_comp` / 引理 `chosenCoend.map_comp`

English:
lemma chosenCoend.map_comp
  given: {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H)
  proof: by
  cat_disch

中文:
引理 chosenCoend.map_comp
  条件: {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

/-- The chosen coend construction as a functor out of the bifunctor category. -/
@[simps]
/--
Definition of `chosenCoendFunctor` / `chosenCoendFunctor` 的定义

English:
definition chosenCoendFunctor
  signature: : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  body: chosenCoend F
  map f := chosenCoend.map f

中文:
定义 chosenCoendFunctor
  签名: : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  定义体: chosenCoend F
  map f := chosenCoend.map f

Depends on / 依赖: WalkingCospan, WalkingCospan.left, WalkingCospan.right, chosenCoend, fac_left, fac_right, isColimitAux
-/
def chosenCoendFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := chosenCoend F
  map f := chosenCoend.map f

/--
Definition of `ChosenEndsOfShape` / `ChosenEndsOfShape` 的定义

English:
class ChosenEndsOfShape
  parameters: (J : Type*) [Category* J] (C : Type*) [Category* C]
  axioms and operations (2):
    - wedge((F : Jᵒᵖ ⥤ J ⥤ C)) : Wedge F
    - isEnd((F : Jᵒᵖ ⥤ J ⥤ C)) : IsLimit (wedge F)

中文:
类 ChosenEndsOfShape
  参数: (J : 类型) [Category* J] (C : 类型) [Category* C]
  公理与运算 (2 个):
    - wedge((F : Jᵒᵖ ⥤ J ⥤ C)) : Wedge F
    - isEnd((F : Jᵒᵖ ⥤ J ⥤ C)) : IsLimit (wedge F)
-/
class ChosenEndsOfShape (J : Type*) [Category* J] (C : Type*) [Category* C] where
  /-- The chosen wedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  wedge (F : Jᵒᵖ ⥤ J ⥤ C) : Wedge F
  /-- The chosen wedge is limiting. -/
  isEnd (F : Jᵒᵖ ⥤ J ⥤ C) : IsLimit (wedge F)

set_option linter.checkUnivs false in
/-- The data of chosen ends in `C`. -/
@[pp_with_univ]
/--
Definition of `ChosenEnds` / `ChosenEnds` 的定义

English:
abbreviation ChosenEnds
  signature: (C : Type*) [Category* C]
  body: forall {J : Type u} [Category.{v} J], ChosenEndsOfShape J C

中文:
缩写 ChosenEnds
  签名: (C : 类型) [Category* C]
  定义体: forall {J : Type u} [Category.{v} J], ChosenEndsOfShape J C

Depends on / 依赖: Category, ChosenEndsOfShape
-/
abbrev ChosenEnds (C : Type*) [Category* C] :=
  forall {J : Type u} [Category.{v} J], ChosenEndsOfShape J C

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenEndsOfShape J C]

/--
Definition of `chosenEnd` / `chosenEnd` 的定义

English:
definition chosenEnd
  signature: : C
  body: (ChosenEndsOfShape.wedge F).pt

中文:
定义 chosenEnd
  签名: : C
  定义体: (ChosenEndsOfShape.wedge F).pt

Depends on / 依赖: ChosenEndsOfShape, ChosenEndsOfShape.wedge
-/
def chosenEnd : C := (ChosenEndsOfShape.wedge F).pt

/--
Definition of `chosenEnd.π` / `chosenEnd.π` 的定义

English:
definition chosenEnd.π
  signature: (j : J)
  body: (ChosenEndsOfShape.wedge F).ι j

@[reassoc]

中文:
定义 chosenEnd.π
  签名: (j : J)
  定义体: (ChosenEndsOfShape.wedge F).ι j

@[reassoc]

Depends on / 依赖: ChosenEndsOfShape, ChosenEndsOfShape.wedge
-/
def chosenEnd.π (j : J) : chosenEnd F ⟶ (F.obj (op j)).obj j :=
  (ChosenEndsOfShape.wedge F).ι j

@[reassoc]
/--
lemma `chosenEnd.condition` / 引理 `chosenEnd.condition`

English:
lemma chosenEnd.condition
  given: {i j : J} (f : i ⟶ j)
  proof: (ChosenEndsOfShape.wedge F).condition f

中文:
引理 chosenEnd.condition
  条件: {i j : J} (f : i ⟶ j)
  证明: (ChosenEndsOfShape.wedge F).condition f

Depends on / 依赖: ChosenEndsOfShape, ChosenEndsOfShape.wedge, condition
-/
lemma chosenEnd.condition {i j : J} (f : i ⟶ j) :
    chosenEnd.π F i ≫ (F.obj (op i)).map f = chosenEnd.π F j ≫ (F.map f.op).app j :=
  (ChosenEndsOfShape.wedge F).condition f

variable {F}

/-- Morphisms into the chosen end are determined by their composites with `chosenEnd.π`. -/
@[ext]
/--
lemma `chosenEnd.hom_ext` / 引理 `chosenEnd.hom_ext`

English:
lemma chosenEnd.hom_ext
  statement: {X : C} {f g : X ⟶ chosenEnd F}
  proof: Wedge.IsLimit.hom_ext (ChosenEndsOfShape.isEnd F) h

中文:
引理 chosenEnd.hom_ext
  结论: {X : C} {f g : X ⟶ chosenEnd F}
  证明: Wedge.IsLimit.hom_ext (ChosenEndsOfShape.isEnd F) h

Depends on / 依赖: ChosenEndsOfShape, ChosenEndsOfShape.isEnd, IsLimit, Wedge.IsLimit.hom_ext, hom_ext
-/
lemma chosenEnd.hom_ext {X : C} {f g : X ⟶ chosenEnd F}
    (h : forall j, f ≫ chosenEnd.π F j = g ≫ chosenEnd.π F j) : f = g :=
  Wedge.IsLimit.hom_ext (ChosenEndsOfShape.isEnd F) h

variable {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
  (hf : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/--
Definition of `chosenEnd.lift` / `chosenEnd.lift` 的定义

English:
definition chosenEnd.lift
  signature: : X ⟶ chosenEnd F
  body: Wedge.IsLimit.lift (ChosenEndsOfShape.isEnd F) f hf

@[reassoc (attr := simp)]

中文:
定义 chosenEnd.lift
  签名: : X ⟶ chosenEnd F
  定义体: Wedge.IsLimit.lift (ChosenEndsOfShape.isEnd F) f hf

@[reassoc (attr := simp)]

Depends on / 依赖: ChosenEndsOfShape, ChosenEndsOfShape.isEnd, IsLimit, Wedge.IsLimit.lift
-/
def chosenEnd.lift : X ⟶ chosenEnd F :=
  Wedge.IsLimit.lift (ChosenEndsOfShape.isEnd F) f hf

@[reassoc (attr := simp)]
/--
lemma `chosenEnd.lift_π` / 引理 `chosenEnd.lift_π`

English:
lemma chosenEnd.lift_π
  given: (j : J)
  statement: chosenEnd.lift f hf ≫ chosenEnd.π F j = f j
  proof: by
  apply IsLimit.fac

中文:
引理 chosenEnd.lift_π
  条件: (j : J)
  结论: chosenEnd.lift f hf ≫ chosenEnd.π F j = f j
  证明: by
  apply IsLimit.fac

Depends on / 依赖: IsLimit, IsLimit.fac
-/
lemma chosenEnd.lift_π (j : J) : chosenEnd.lift f hf ≫ chosenEnd.π F j = f j := by
  apply IsLimit.fac

/--
Definition of `chosenEnd.map` / `chosenEnd.map` 的定义

English:
definition chosenEnd.map
  signature: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G)
  body: chosenEnd.lift (fun x => chosenEnd.π F x ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% chosenEnd.condition F φ]
    simp)

@[reassoc (attr := simp)]

中文:
定义 chosenEnd.map
  签名: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G)
  定义体: chosenEnd.lift (fun x => chosenEnd.π F x ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% chosenEnd.condition F φ]
    simp)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, chosenEnd, chosenEnd.condition, chosenEnd.lift, condition, f.app, naturality, reassoc_of
-/
def chosenEnd.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenEnd F ⟶ chosenEnd G :=
  chosenEnd.lift (fun x => chosenEnd.π F x ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% chosenEnd.condition F φ]
    simp)

@[reassoc (attr := simp)]
/--
lemma `chosenEnd.map_π` / 引理 `chosenEnd.map_π`

English:
lemma chosenEnd.map_π
  given: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J)
  proof: by
  simp [chosenEnd.map]

@[simp]

中文:
引理 chosenEnd.map_π
  条件: {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J)
  证明: by
  simp [chosenEnd.map]

@[simp]

Depends on / 依赖: chosenEnd, chosenEnd.map
-/
lemma chosenEnd.map_π {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenEnd.map f ≫ chosenEnd.π G j = chosenEnd.π F j ≫ (f.app (op j)).app j := by
  simp [chosenEnd.map]

@[simp]
/--
lemma `chosenEnd.map_id` / 引理 `chosenEnd.map_id`

English:
lemma chosenEnd.map_id
  statement: chosenEnd.map (𝟙 F) = 𝟙 _
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
引理 chosenEnd.map_id
  结论: chosenEnd.map (𝟙 F) = 𝟙 _
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma chosenEnd.map_id : chosenEnd.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `chosenEnd.map_comp` / 引理 `chosenEnd.map_comp`

English:
lemma chosenEnd.map_comp
  given: {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H)
  proof: by
  cat_disch

中文:
引理 chosenEnd.map_comp
  条件: {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma chosenEnd.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenEnd.map f ≫ chosenEnd.map g = chosenEnd.map (f ≫ g) := by
  cat_disch

/-- The chosen end construction as a functor out of the bifunctor category. -/
@[simps]
/--
Definition of `chosenEndFunctor` / `chosenEndFunctor` 的定义

English:
definition chosenEndFunctor
  signature: : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  body: chosenEnd F
  map f := chosenEnd.map f

中文:
定义 chosenEndFunctor
  签名: : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  定义体: chosenEnd F
  map f := chosenEnd.map f

Depends on / 依赖: chosenEnd
-/
def chosenEndFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := chosenEnd F
  map f := chosenEnd.map f

end CategoryTheory.Limits
