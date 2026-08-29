/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
/-!

# Constructing monoidal functors from natural transformations between multifunctors

This file provides alternative constructors for (op/lax) monoidal functors, given tensorators
`μ : F - ⊗ F - ⟶ F (- ⊗ -)` / `δ : F (- ⊗ -) ⟶ F - ⊗ F -` as natural transformations between
bifunctors. The associativity conditions are phrased as equalities of natural transformations
between trifunctors `(F - ⊗ F -) ⊗ F - ⟶ F (- ⊗ (- ⊗ -))` / `F ((- ⊗ -) ⊗ -) ⟶ F - ⊗ (F - ⊗ F -)`,
and the unitality conditions are phrased as equalities of natural transformation between functors.

Once we have more API for quadrifunctors, we can add constructors for monoidal category structures
by phrasing the pentagon axiom as an equality of natural transformations between quadrifunctors.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]

namespace MonoidalCategory

open CategoryTheory.Functor

/--
Definition of `curriedTensorInsertFunctor₁` / `curriedTensorInsertFunctor₁` 的定义

English:
abbreviation curriedTensorInsertFunctor₁
  signature: (F : C ⥤ D)
  body: (((whiskeringLeft₂ _).obj F).obj (𝟭 D)).obj (curriedTensor D)

中文:
缩写 curriedTensorInsertFunctor₁
  签名: (F : C ⥤ D)
  定义体: (((whiskeringLeft₂ _).obj F).obj (𝟭 D)).obj (curriedTensor D)

Depends on / 依赖: curriedTensor
-/
abbrev curriedTensorInsertFunctor₁ (F : C ⥤ D) : C ⥤ D ⥤ D :=
  (((whiskeringLeft₂ _).obj F).obj (𝟭 D)).obj (curriedTensor D)

/--
Definition of `curriedTensorInsertFunctor₂` / `curriedTensorInsertFunctor₂` 的定义

English:
abbreviation curriedTensorInsertFunctor₂
  signature: (F : C ⥤ D)
  body: (((whiskeringLeft₂ _).obj (𝟭 D)).obj F).obj (curriedTensor D)

中文:
缩写 curriedTensorInsertFunctor₂
  签名: (F : C ⥤ D)
  定义体: (((whiskeringLeft₂ _).obj (𝟭 D)).obj F).obj (curriedTensor D)

Depends on / 依赖: curriedTensor
-/
abbrev curriedTensorInsertFunctor₂ (F : C ⥤ D) : D ⥤ C ⥤ D :=
  (((whiskeringLeft₂ _).obj (𝟭 D)).obj F).obj (curriedTensor D)

/--
Definition of `curriedTensorPre` / `curriedTensorPre` 的定义

English:
abbreviation curriedTensorPre
  signature: (F : C ⥤ D)
  body: .obj (curriedTensor D) .obj F (whiskeringLeft₂ _).obj F

中文:
缩写 curriedTensorPre
  签名: (F : C ⥤ D)
  定义体: .obj (curriedTensor D) .obj F (whiskeringLeft₂ _).obj F

Depends on / 依赖: curriedTensor
-/
abbrev curriedTensorPre (F : C ⥤ D) : C ⥤ C ⥤ D :=
.obj (curriedTensor D) .obj F (whiskeringLeft₂ _).obj F

/--
Definition of `curriedTensorPost` / `curriedTensorPost` 的定义

English:
abbreviation curriedTensorPost
  signature: (F : C ⥤ D)
  body: (Functor.postcompose₂.obj F).obj (curriedTensor C)

中文:
缩写 curriedTensorPost
  签名: (F : C ⥤ D)
  定义体: (Functor.postcompose₂.obj F).obj (curriedTensor C)

Depends on / 依赖: Functor, Functor.postcompose, curriedTensor
-/
abbrev curriedTensorPost (F : C ⥤ D) : C ⥤ C ⥤ D :=
  (Functor.postcompose₂.obj F).obj (curriedTensor C)

/--
Definition of `curriedTensorPrePre` / `curriedTensorPrePre` 的定义

English:
abbreviation curriedTensorPrePre
  signature: (F : C ⥤ D)
  body: bifunctorComp₁₂ (curriedTensorPre F) (curriedTensorInsertFunctor₂ F)

中文:
缩写 curriedTensorPrePre
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₁₂ (curriedTensorPre F) (curriedTensorInsertFunctor₂ F)

Depends on / 依赖: curriedTensorPre
-/
abbrev curriedTensorPrePre (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensorPre F) (curriedTensorInsertFunctor₂ F)

/--
Definition of `curriedTensorPrePre'` / `curriedTensorPrePre'` 的定义

English:
abbreviation curriedTensorPrePre'
  signature: (F : C ⥤ D)
  body: bifunctorComp₂₃ (curriedTensorInsertFunctor₁ F) (curriedTensorPre F)

中文:
缩写 curriedTensorPrePre'
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₂₃ (curriedTensorInsertFunctor₁ F) (curriedTensorPre F)

Depends on / 依赖: curriedTensorPre
-/
abbrev curriedTensorPrePre' (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorInsertFunctor₁ F) (curriedTensorPre F)

/--
Definition of `curriedTensorPostPre` / `curriedTensorPostPre` 的定义

English:
abbreviation curriedTensorPostPre
  signature: (F : C ⥤ D)
  body: bifunctorComp₁₂ (curriedTensor C) (curriedTensorPre F)

中文:
缩写 curriedTensorPostPre
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₁₂ (curriedTensor C) (curriedTensorPre F)

Depends on / 依赖: curriedTensor, curriedTensorPre
-/
abbrev curriedTensorPostPre (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensor C) (curriedTensorPre F)

/--
Definition of `curriedTensorPrePost` / `curriedTensorPrePost` 的定义

English:
abbreviation curriedTensorPrePost
  signature: (F : C ⥤ D)
  body: bifunctorComp₂₃ (curriedTensorPre F) (curriedTensor C)

中文:
缩写 curriedTensorPrePost
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₂₃ (curriedTensorPre F) (curriedTensor C)

Depends on / 依赖: curriedTensor, curriedTensorPre
-/
abbrev curriedTensorPrePost (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorPre F) (curriedTensor C)

/--
Definition of `curriedTensorPostPost` / `curriedTensorPostPost` 的定义

English:
abbreviation curriedTensorPostPost
  signature: (F : C ⥤ D)
  body: bifunctorComp₁₂ (curriedTensor C) (curriedTensorPost F)

中文:
缩写 curriedTensorPostPost
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₁₂ (curriedTensor C) (curriedTensorPost F)

Depends on / 依赖: curriedTensor, curriedTensorPost
-/
abbrev curriedTensorPostPost (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensor C) (curriedTensorPost F)

/--
Definition of `curriedTensorPostPost'` / `curriedTensorPostPost'` 的定义

English:
abbreviation curriedTensorPostPost'
  signature: (F : C ⥤ D)
  body: bifunctorComp₂₃ (curriedTensorPost F) (curriedTensor C)

中文:
缩写 curriedTensorPostPost'
  签名: (F : C ⥤ D)
  定义体: bifunctorComp₂₃ (curriedTensorPost F) (curriedTensor C)

Depends on / 依赖: curriedTensor, curriedTensorPost
-/
abbrev curriedTensorPostPost' (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorPost F) (curriedTensor C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism of bifunctors `F - ⊗ F - ≅ F (- ⊗ -)`, given a monoidal functor `F`. -/
@[simps!]
/--
Definition of `Functor.curriedTensorPreIsoPost` / `Functor.curriedTensorPreIsoPost` 的定义

English:
definition Functor.curriedTensorPreIsoPost
  signature: (F : C ⥤ D) [F.Monoidal]
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Monoidal.μIso F _ _))

中文:
定义 函子.curriedTensorPreIsoPost
  签名: (F : C ⥤ D) [F.幺半群]
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Monoidal.μIso F _ _))

Depends on / 依赖: Monoidal, NatIso, NatIso.ofComponents, ofComponents
-/
def Functor.curriedTensorPreIsoPost (F : C ⥤ D) [F.Monoidal] :
    curriedTensorPre F ≅ curriedTensorPost F :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Monoidal.μIso F _ _))

set_option backward.defeqAttrib.useBackward true in
/-- The functor which associates to a functor `F` the bifunctor `F - ⊗ F -`. -/
@[simps]
/--
Definition of `curriedTensorPreFunctor` / `curriedTensorPreFunctor` 的定义

English:
definition curriedTensorPreFunctor
  signature: : (C ⥤ D) ⥤ C ⥤ C ⥤ D where
  body: curriedTensorPre F
  map {F₁ F₂} f :=
    { app X₁ :=
        { app X₂ := f.app _ otimesₘ f.app _
          naturality := by simp [← id_tensorHom] }
      naturality _ _ _ := by
        ext
        simp [← tensorHom_id] }

中文:
定义 curriedTensorPreFunctor
  签名: : (C ⥤ D) ⥤ C ⥤ C ⥤ D where
  定义体: curriedTensorPre F
  map {F₁ F₂} f :=
    { app X₁ :=
        { app X₂ := f.app _ otimesₘ f.app _
          naturality := by simp [← id_tensorHom] }
      naturality _ _ _ := by
        ext
        simp [← tensorHom_id] }

Depends on / 依赖: curriedTensorPre
-/
def curriedTensorPreFunctor : (C ⥤ D) ⥤ C ⥤ C ⥤ D where
  obj F := curriedTensorPre F
  map {F₁ F₂} f :=
    { app X₁ :=
        { app X₂ := f.app _ otimesₘ f.app _
          naturality := by simp [← id_tensorHom] }
      naturality _ _ _ := by
        ext
        simp [← tensorHom_id] }

/--
Definition of `curriedTensorPostFunctor` / `curriedTensorPostFunctor` 的定义

English:
abbreviation curriedTensorPostFunctor
  signature: : (C ⥤ D) ⥤ C ⥤ C ⥤ D
  body: Functor.postcompose₂.flip.obj (curriedTensor C)

中文:
缩写 curriedTensorPostFunctor
  签名: : (C ⥤ D) ⥤ C ⥤ C ⥤ D
  定义体: Functor.postcompose₂.flip.obj (curriedTensor C)

Depends on / 依赖: Functor, Functor.postcompose, curriedTensor, flip.obj
-/
abbrev curriedTensorPostFunctor : (C ⥤ D) ⥤ C ⥤ C ⥤ D :=
  Functor.postcompose₂.flip.obj (curriedTensor C)

end MonoidalCategory

open MonoidalCategory

namespace Functor.LaxMonoidal

/-!

## Lax monoidal functors

Given a unit morphism `ε : 𝟙_ D ⟶ F.obj (𝟙_ C))` and a tensorator `μ : F - ⊗ F - ⟶ F (- ⊗ -)`
such that the diagrams below commute, we define
`CategoryTheory.Functor.LaxMonoidal.ofBifunctor : F.LaxMonoidal`.

### Associativity hexagon

```
      (F - ⊗ F -) ⊗ F -
        / \
       v v
F (- ⊗ -) ⊗ F - F - ⊗ (F - ⊗ F -)
       | |
       v v
F ((- ⊗ -) ⊗ -) F - ⊗ F (- ⊗ -)
        \ /
         v v
       F (- ⊗ (- ⊗ -))
```

### Left unitality square

```
𝟙 ⊗ F - ⟶ F 𝟙 ⊗ F -
  | |
  v v
  F ← F (𝟙 ⊗ -)
```

### Right unitality square

```
F - ⊗ 𝟙 ⟶ F - ⊗ F 𝟙
  | |
  v v
  F ← F (- ⊗ 𝟙)
```
-/

namespace ofBifunctor

/--
The top left map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₁` / `firstMap₁` 的定义

English:
definition firstMap₁
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: (bifunctorComp₁₂Functor.map μ).app (curriedTensorInsertFunctor₂ F)

中文:
定义 firstMap₁
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: (bifunctorComp₁₂Functor.map μ).app (curriedTensorInsertFunctor₂ F)

Depends on / 依赖: Functor.map
-/
def firstMap₁ {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    curriedTensorPrePre F ⟶ curriedTensorPostPre F :=
  (bifunctorComp₁₂Functor.map μ).app (curriedTensorInsertFunctor₂ F)

/--
The middle left map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₂` / `firstMap₂` 的定义

English:
definition firstMap₂
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: (bifunctorComp₁₂Functor.obj _).map μ

中文:
定义 firstMap₂
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: (bifunctorComp₁₂Functor.obj _).map μ

Depends on / 依赖: Functor.obj
-/
def firstMap₂ {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    (curriedTensorPostPre F) ⟶ curriedTensorPostPost F :=
  (bifunctorComp₁₂Functor.obj _).map μ

/--
The bottom left map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₃` / `firstMap₃` 的定义

English:
definition firstMap₃
  signature: (F : C ⥤ D)
  body: (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

#adaptation_note

中文:
定义 firstMap₃
  签名: (F : C ⥤ D)
  定义体: (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

#adaptation_note

Depends on / 依赖: curriedAssociatorNatIso
-/
def firstMap₃ (F : C ⥤ D) : curriedTensorPostPost F ⟶ curriedTensorPostPost' F :=
  (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
The composition of the left maps in the associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: firstMap₁ μ ≫ firstMap₂ μ ≫ firstMap₃ F

中文:
定义 firstMap
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: firstMap₁ μ ≫ firstMap₂ μ ≫ firstMap₃ F
-/
def firstMap {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    curriedTensorPrePre F ⟶ curriedTensorPostPost' F :=
  firstMap₁ μ ≫ firstMap₂ μ ≫ firstMap₃ F

/--
The top right map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₁` / `secondMap₁` 的定义

English:
definition secondMap₁
  signature: (F : C ⥤ D)
  body: ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

中文:
定义 secondMap₁
  签名: (F : C ⥤ D)
  定义体: ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

Depends on / 依赖: curriedAssociatorNatIso
-/
def secondMap₁ (F : C ⥤ D) : curriedTensorPrePre F ⟶ curriedTensorPrePre' F :=
  ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

/--
The middle right map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₂` / `secondMap₂` 的定义

English:
definition secondMap₂
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: (bifunctorComp₂₃Functor.obj _).map μ

中文:
定义 secondMap₂
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: (bifunctorComp₂₃Functor.obj _).map μ

Depends on / 依赖: Functor.obj
-/
def secondMap₂ {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    curriedTensorPrePre' F ⟶ curriedTensorPrePost F :=
  (bifunctorComp₂₃Functor.obj _).map μ

/--
The bottom right map in the associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₃` / `secondMap₃` 的定义

English:
definition secondMap₃
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: (bifunctorComp₂₃Functor.map μ).app _

#adaptation_note

中文:
定义 secondMap₃
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: (bifunctorComp₂₃Functor.map μ).app _

#adaptation_note

Depends on / 依赖: Functor.map
-/
def secondMap₃ {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    curriedTensorPrePost F ⟶ curriedTensorPostPost' F :=
  (bifunctorComp₂₃Functor.map μ).app _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
The composition of the right maps in the associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  body: secondMap₁ F ≫ secondMap₂ μ ≫ secondMap₃ μ

中文:
定义 secondMap
  签名: {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F)
  定义体: secondMap₁ F ≫ secondMap₂ μ ≫ secondMap₃ μ
-/
def secondMap {F : C ⥤ D} (μ : curriedTensorPre F ⟶ curriedTensorPost F) :
    curriedTensorPrePre F ⟶ curriedTensorPostPost' F :=
  secondMap₁ F ≫ secondMap₂ μ ≫ secondMap₃ μ

/--
The left map in the left unitality square.
-/
@[simps!]
/--
Definition of `leftMapₗ` / `leftMapₗ` 的定义

English:
definition leftMapₗ
  signature: (F : C ⥤ D)
  body: whiskerLeft F (leftUnitorNatIso D).hom

中文:
定义 leftMapₗ
  签名: (F : C ⥤ D)
  定义体: whiskerLeft F (leftUnitorNatIso D).hom

Depends on / 依赖: leftUnitorNatIso, whiskerLeft
-/
def leftMapₗ (F : C ⥤ D) : F ⋙ tensorUnitLeft D ⟶ F :=
  whiskerLeft F (leftUnitorNatIso D).hom

/--
The top map in the left unitality square.
-/
@[simps!]
/--
Definition of `topMapₗ` / `topMapₗ` 的定义

English:
definition topMapₗ
  signature: {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: whiskerLeft F ((curriedTensor _).map ε)

中文:
定义 topMapₗ
  签名: {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: whiskerLeft F ((curriedTensor _).map ε)

Depends on / 依赖: curriedTensor, whiskerLeft
-/
def topMapₗ {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C)) :
    F ⋙ tensorUnitLeft D ⟶ (curriedTensorPre F).obj (𝟙_ C) :=
  whiskerLeft F ((curriedTensor _).map ε)

/--
The bottom map in the left unitality square.
-/
@[simps!]
/--
Definition of `bottomMapₗ` / `bottomMapₗ` 的定义

English:
definition bottomMapₗ
  signature: (F : C ⥤ D)
  body: whiskerRight (leftUnitorNatIso C).hom F

中文:
定义 bottomMapₗ
  签名: (F : C ⥤ D)
  定义体: whiskerRight (leftUnitorNatIso C).hom F

Depends on / 依赖: leftUnitorNatIso, whiskerRight
-/
def bottomMapₗ (F : C ⥤ D) : (curriedTensor C).obj (𝟙_ C) ⋙ F ⟶ F :=
  whiskerRight (leftUnitorNatIso C).hom F

/--
The left map in the right unitality square.
-/
@[simps!]
/--
Definition of `leftMapᵣ` / `leftMapᵣ` 的定义

English:
definition leftMapᵣ
  signature: (F : C ⥤ D)
  body: whiskerLeft F (rightUnitorNatIso D).hom

中文:
定义 leftMapᵣ
  签名: (F : C ⥤ D)
  定义体: whiskerLeft F (rightUnitorNatIso D).hom

Depends on / 依赖: rightUnitorNatIso, whiskerLeft
-/
def leftMapᵣ (F : C ⥤ D) : F ⋙ tensorUnitRight D ⟶ F :=
  whiskerLeft F (rightUnitorNatIso D).hom

/--
The top map in the right unitality square.
-/
@[simps!]
/--
Definition of `topMapᵣ` / `topMapᵣ` 的定义

English:
definition topMapᵣ
  signature: {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: whiskerLeft F ((curriedTensor _).flip.map ε)

中文:
定义 topMapᵣ
  签名: {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: whiskerLeft F ((curriedTensor _).flip.map ε)

Depends on / 依赖: curriedTensor, flip.map, whiskerLeft
-/
def topMapᵣ {F : C ⥤ D} (ε : 𝟙_ D ⟶ F.obj (𝟙_ C)) :
    F ⋙ tensorUnitRight D ⟶ (curriedTensorPre F).flip.obj (𝟙_ C) :=
  whiskerLeft F ((curriedTensor _).flip.map ε)

/--
The bottom map in the right unitality square.
-/
@[simps!]
/--
Definition of `bottomMapᵣ` / `bottomMapᵣ` 的定义

English:
definition bottomMapᵣ
  signature: (F : C ⥤ D)
  body: whiskerRight (rightUnitorNatIso C).hom F

中文:
定义 bottomMapᵣ
  签名: (F : C ⥤ D)
  定义体: whiskerRight (rightUnitorNatIso C).hom F

Depends on / 依赖: rightUnitorNatIso, whiskerRight
-/
def bottomMapᵣ (F : C ⥤ D) : (curriedTensor C).flip.obj (𝟙_ C) ⋙ F ⟶ F :=
  whiskerRight (rightUnitorNatIso C).hom F

end ofBifunctor

open ofBifunctor

variable {F : C ⥤ D}
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator as a morphism of bifunctors -/
    (μ : curriedTensorPre F ⟶ curriedTensorPost F)
    /- the associativity hexagon commutes -/
    (associativity : firstMap μ = secondMap μ)
    /- the left unitality square commutes -/
    (left_unitality : leftMapₗ F = topMapₗ ε ≫ μ.app (𝟙_ C) ≫ bottomMapₗ F)
    /- the right unitality square commutes -/
    (right_unitality : leftMapᵣ F =
      topMapᵣ ε ≫ ((flipFunctor _ _ _).map μ).app (𝟙_ C) ≫ bottomMapᵣ F)

/--
`F` is lax monoidal given a unit morphism `ε : 𝟙_ D ⟶ F.obj (𝟙_ C))` and a tensorator
`μ : F - ⊗ F - ⟶ F (- ⊗ -)` as a natural transformation between bifunctors, satisfying the
relevant compatibilities.
-/
@[instance_reducible]
/--
Definition of `ofBifunctor` / `ofBifunctor` 的定义

English:
definition ofBifunctor
  signature: : F.LaxMonoidal where
  body: ε
  μ X Y := (μ.app X).app Y
  μ_natural_left f X := NatTrans.congr_app (μ.naturality f) X
  μ_natural_right X f := (μ.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatTrans.congr_app left_unita

中文:
定义 ofBifunctor
  签名: : F.松弛幺半群 where
  定义体: ε
  μ X Y := (μ.app X).app Y
  μ_natural_left f X := NatTrans.congr_app (μ.naturality f) X
  μ_natural_right X f := (μ.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatTrans.congr_app left_unita
-/
def ofBifunctor : F.LaxMonoidal where
  ε := ε
  μ X Y := (μ.app X).app Y
  μ_natural_left f X := NatTrans.congr_app (μ.naturality f) X
  μ_natural_right X f := (μ.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatTrans.congr_app left_unitality X
  right_unitality X := NatTrans.congr_app right_unitality X

end LaxMonoidal

namespace OplaxMonoidal

/-!

## Oplax monoidal functors

Given a counit morphism `η : F.obj (𝟙_ C)) ⟶ 𝟙_ D` and a tensorator `δ : F (- ⊗ -) ⟶ F - ⊗ F -`
such that the diagrams below commute, we define
`CategoryTheory.Functor.OplaxMonoidal.ofBifunctor : F.OplaxMonoidal`.

### Oplax associativity hexagon

```
      F ((- ⊗ -) ⊗ -)
        / \
       v v
F (- ⊗ -) ⊗ F - F (- ⊗ (- ⊗ -))
       | |
       v v
(F - ⊗ F -) ⊗ F - F - ⊗ F (- ⊗ -)
        \ /
         v v
       F - ⊗ (F - ⊗ F -)
```

### Oplax left unitality square

```
  F ⟶ F (𝟙 ⊗ -)
  | |
  v v
𝟙 ⊗ F - ← F 𝟙 ⊗ F -
```

### Oplax right unitality square

```
  F ⟶ F (- ⊗ 𝟙)
  | |
  v v
F - ⊗ 𝟙 ← F - ⊗ F 𝟙
```
-/

namespace ofBifunctor

/--
The top left map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₁` / `firstMap₁` 的定义

English:
definition firstMap₁
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: (bifunctorComp₁₂Functor.obj (curriedTensor C)).map δ

中文:
定义 firstMap₁
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: (bifunctorComp₁₂Functor.obj (curriedTensor C)).map δ

Depends on / 依赖: Functor.obj, curriedTensor
-/
def firstMap₁ {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    curriedTensorPostPost F ⟶ curriedTensorPostPre F :=
  (bifunctorComp₁₂Functor.obj (curriedTensor C)).map δ

/--
The middle left map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₂` / `firstMap₂` 的定义

English:
definition firstMap₂
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: (bifunctorComp₁₂Functor.map δ).app (curriedTensorInsertFunctor₂ F)

中文:
定义 firstMap₂
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: (bifunctorComp₁₂Functor.map δ).app (curriedTensorInsertFunctor₂ F)

Depends on / 依赖: Functor.map
-/
def firstMap₂ {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    (curriedTensorPostPre F) ⟶ curriedTensorPrePre F :=
  (bifunctorComp₁₂Functor.map δ).app (curriedTensorInsertFunctor₂ F)

/--
The bottom left map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap₃` / `firstMap₃` 的定义

English:
definition firstMap₃
  signature: (F : C ⥤ D)
  body: ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

#adaptation_note

中文:
定义 firstMap₃
  签名: (F : C ⥤ D)
  定义体: ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

#adaptation_note

Depends on / 依赖: curriedAssociatorNatIso
-/
def firstMap₃ (F : C ⥤ D) : curriedTensorPrePre F ⟶ curriedTensorPrePre' F :=
  ((((whiskeringLeft₃ D).obj F).obj F).obj F).map (curriedAssociatorNatIso D).hom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
The composition of the three left maps in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: firstMap₁ δ ≫ firstMap₂ δ ≫ firstMap₃ F

中文:
定义 firstMap
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: firstMap₁ δ ≫ firstMap₂ δ ≫ firstMap₃ F
-/
def firstMap {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    curriedTensorPostPost F ⟶ curriedTensorPrePre' F :=
  firstMap₁ δ ≫ firstMap₂ δ ≫ firstMap₃ F

/--
The top right map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₁` / `secondMap₁` 的定义

English:
definition secondMap₁
  signature: (F : C ⥤ D)
  body: (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

中文:
定义 secondMap₁
  签名: (F : C ⥤ D)
  定义体: (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

Depends on / 依赖: curriedAssociatorNatIso
-/
def secondMap₁ (F : C ⥤ D) : curriedTensorPostPost F ⟶ curriedTensorPostPost' F :=
  (postcompose₃.obj _).map (curriedAssociatorNatIso _).hom

/--
The middle right map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₂` / `secondMap₂` 的定义

English:
definition secondMap₂
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: (bifunctorComp₂₃Functor.map δ).app _

中文:
定义 secondMap₂
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: (bifunctorComp₂₃Functor.map δ).app _

Depends on / 依赖: Functor.map
-/
def secondMap₂ {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    curriedTensorPostPost' F ⟶ curriedTensorPrePost F :=
  (bifunctorComp₂₃Functor.map δ).app _

/--
The bottom right map in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap₃` / `secondMap₃` 的定义

English:
definition secondMap₃
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: (bifunctorComp₂₃Functor.obj (curriedTensorInsertFunctor₁ F)).map δ

#adaptation_note

中文:
定义 secondMap₃
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: (bifunctorComp₂₃Functor.obj (curriedTensorInsertFunctor₁ F)).map δ

#adaptation_note

Depends on / 依赖: Functor.obj
-/
def secondMap₃ {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    curriedTensorPrePost F ⟶ curriedTensorPrePre' F :=
  (bifunctorComp₂₃Functor.obj (curriedTensorInsertFunctor₁ F)).map δ

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
The composition of the three right maps in the oplax associativity hexagon.
-/
@[simps!]
/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  body: secondMap₁ F ≫ secondMap₂ δ ≫ secondMap₃ δ

中文:
定义 secondMap
  签名: {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F)
  定义体: secondMap₁ F ≫ secondMap₂ δ ≫ secondMap₃ δ
-/
def secondMap {F : C ⥤ D} (δ : curriedTensorPost F ⟶ curriedTensorPre F) :
    curriedTensorPostPost F ⟶ curriedTensorPrePre' F :=
  secondMap₁ F ≫ secondMap₂ δ ≫ secondMap₃ δ

/--
The left map in the oplax left unitality square.
-/
@[simps!]
/--
Definition of `leftMapₗ` / `leftMapₗ` 的定义

English:
definition leftMapₗ
  signature: (F : C ⥤ D)
  body: whiskerLeft F (leftUnitorNatIso D).inv

中文:
定义 leftMapₗ
  签名: (F : C ⥤ D)
  定义体: whiskerLeft F (leftUnitorNatIso D).inv

Depends on / 依赖: leftUnitorNatIso, whiskerLeft
-/
def leftMapₗ (F : C ⥤ D) : F ⟶ F ⋙ tensorUnitLeft D :=
  whiskerLeft F (leftUnitorNatIso D).inv

/--
The top map in the oplax left unitality square.
-/
@[simps!]
/--
Definition of `topMapₗ` / `topMapₗ` 的定义

English:
definition topMapₗ
  signature: (F : C ⥤ D)
  body: whiskerRight (leftUnitorNatIso C).inv F

中文:
定义 topMapₗ
  签名: (F : C ⥤ D)
  定义体: whiskerRight (leftUnitorNatIso C).inv F

Depends on / 依赖: leftUnitorNatIso, whiskerRight
-/
def topMapₗ (F : C ⥤ D) : F ⟶ (curriedTensor C).obj (𝟙_ C) ⋙ F :=
  whiskerRight (leftUnitorNatIso C).inv F

/--
The bottom map in the oplax left unitality square.
-/
@[simps!]
/--
Definition of `bottomMapₗ` / `bottomMapₗ` 的定义

English:
definition bottomMapₗ
  signature: {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  body: whiskerLeft F ((curriedTensor _).map η)

中文:
定义 bottomMapₗ
  签名: {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  定义体: whiskerLeft F ((curriedTensor _).map η)

Depends on / 依赖: curriedTensor, whiskerLeft
-/
def bottomMapₗ {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D) :
    (curriedTensorPre F).obj (𝟙_ C) ⟶ F ⋙ tensorUnitLeft D :=
  whiskerLeft F ((curriedTensor _).map η)

/--
The left map in the oplax right unitality square.
-/
@[simps!]
/--
Definition of `leftMapᵣ` / `leftMapᵣ` 的定义

English:
definition leftMapᵣ
  signature: (F : C ⥤ D)
  body: whiskerLeft F (rightUnitorNatIso D).inv

中文:
定义 leftMapᵣ
  签名: (F : C ⥤ D)
  定义体: whiskerLeft F (rightUnitorNatIso D).inv

Depends on / 依赖: rightUnitorNatIso, whiskerLeft
-/
def leftMapᵣ (F : C ⥤ D) : F ⟶ F ⋙ tensorUnitRight D :=
  whiskerLeft F (rightUnitorNatIso D).inv

/--
The top map in the oplax right unitality square.
-/
@[simps!]
/--
Definition of `topMapᵣ` / `topMapᵣ` 的定义

English:
definition topMapᵣ
  signature: (F : C ⥤ D)
  body: whiskerRight (rightUnitorNatIso C).inv F

中文:
定义 topMapᵣ
  签名: (F : C ⥤ D)
  定义体: whiskerRight (rightUnitorNatIso C).inv F

Depends on / 依赖: rightUnitorNatIso, whiskerRight
-/
def topMapᵣ (F : C ⥤ D) : F ⟶ (curriedTensor C).flip.obj (𝟙_ C) ⋙ F :=
  whiskerRight (rightUnitorNatIso C).inv F

/--
The bottom map in the oplax right unitality square.
-/
@[simps!]
/--
Definition of `bottomMapᵣ` / `bottomMapᵣ` 的定义

English:
definition bottomMapᵣ
  signature: {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  body: whiskerLeft F ((curriedTensor _).flip.map η)

中文:
定义 bottomMapᵣ
  签名: {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  定义体: whiskerLeft F ((curriedTensor _).flip.map η)

Depends on / 依赖: curriedTensor, flip.map, whiskerLeft
-/
def bottomMapᵣ {F : C ⥤ D} (η : F.obj (𝟙_ C) ⟶ 𝟙_ D) :
    (curriedTensorPre F).flip.obj (𝟙_ C) ⟶ F ⋙ tensorUnitRight D :=
  whiskerLeft F ((curriedTensor _).flip.map η)

end ofBifunctor

open ofBifunctor

variable {F : C ⥤ D}
    /- counit morphism -/
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    /- tensorator as a morphism of bifunctors -/
    (δ : curriedTensorPost F ⟶ curriedTensorPre F)
    /- the oplax associativity hexagon commutes -/
    (oplax_associativity : firstMap δ = secondMap δ)
    /- the oplax left unitality square commutes -/
    (oplax_left_unitality : leftMapₗ F = topMapₗ F ≫ δ.app (𝟙_ C) ≫ bottomMapₗ η)
    /- the oplax right unitality square commutes -/
    (oplax_right_unitality : leftMapᵣ F =
      topMapᵣ F ≫ ((flipFunctor _ _ _).map δ).app (𝟙_ C) ≫ bottomMapᵣ η)

/--
`F` is oplax monoidal given a counit morphism `η : F.obj (𝟙_ C) ⟶ 𝟙_ D` and a tensorator
`δ : F (- ⊗ -) ⟶ F - ⊗ F -` as a natural transformation between bifunctors, satisfying the
relevant compatibilities.
-/
@[instance_reducible]
/--
Definition of `ofBifunctor` / `ofBifunctor` 的定义

English:
definition ofBifunctor
  signature: : F.OplaxMonoidal where
  body: η
  δ X Y := (δ.app X).app Y
  δ_natural_left f X := (NatTrans.congr_app (δ.naturality f) X).symm
  δ_natural_right X f := ((δ.app X).naturality f).symm
  oplax_associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app oplax_associativity X) Y) Z
  oplax_left_unitality X 

中文:
定义 ofBifunctor
  签名: : F.反松弛幺半群 where
  定义体: η
  δ X Y := (δ.app X).app Y
  δ_natural_left f X := (NatTrans.congr_app (δ.naturality f) X).symm
  δ_natural_right X f := ((δ.app X).naturality f).symm
  oplax_associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app oplax_associativity X) Y) Z
  oplax_left_unitality X 
-/
def ofBifunctor : F.OplaxMonoidal where
  η := η
  δ X Y := (δ.app X).app Y
  δ_natural_left f X := (NatTrans.congr_app (δ.naturality f) X).symm
  δ_natural_right X f := ((δ.app X).naturality f).symm
  oplax_associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app oplax_associativity X) Y) Z
  oplax_left_unitality X := NatTrans.congr_app oplax_left_unitality X
  oplax_right_unitality X := NatTrans.congr_app oplax_right_unitality X

end OplaxMonoidal

open LaxMonoidal.ofBifunctor OplaxMonoidal.ofBifunctor

namespace Monoidal

variable {F : C ⥤ D}
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- lax tensorator as a morphism of bifunctors -/
    (μ : curriedTensorPre F ⟶ curriedTensorPost F)
    /- the lax associativity hexagon commutes -/
    (associativity : firstMap μ = secondMap μ)
    /- the lax left unitality square commutes -/
    (left_unitality : LaxMonoidal.ofBifunctor.leftMapₗ F = topMapₗ ε ≫ μ.app (𝟙_ C) ≫ bottomMapₗ F)
    /- the lax right unitality square commutes -/
    (right_unitality : LaxMonoidal.ofBifunctor.leftMapᵣ F =
      topMapᵣ ε ≫ ((flipFunctor _ _ _).map μ).app (𝟙_ C) ≫ bottomMapᵣ F)
    /- counit morphism -/
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    /- oplax tensorator as a morphism of bifunctors -/
    (δ : curriedTensorPost F ⟶ curriedTensorPre F)
    /- the oplax associativity hexagon commutes -/
    (oplax_associativity : firstMap δ = secondMap δ)
    /- the left unitality square commutes -/
    (oplax_left_unitality : OplaxMonoidal.ofBifunctor.leftMapₗ F =
      topMapₗ F ≫ δ.app (𝟙_ C) ≫ bottomMapₗ η)
    /- the right unitality square commutes -/
    (oplax_right_unitality : OplaxMonoidal.ofBifunctor.leftMapᵣ F =
      topMapᵣ F ≫ ((flipFunctor _ _ _).map δ).app (𝟙_ C) ≫ bottomMapᵣ η)

/--
`F` is monoidal given a co/unit morphisms `ε/η : 𝟙_ D ↔ F.obj (𝟙_ C)` and tensorators
`μ / δ : F - ⊗ F - ↔ F (- ⊗ -)` as natural transformations between bifunctors, satisfying the
relevant compatibilities.
-/
@[instance_reducible]
/--
Definition of `ofBifunctor` / `ofBifunctor` 的定义

English:
definition ofBifunctor
  signature: (ε_η : ε ≫ η = 𝟙 _) (η_ε : η ≫ ε = 𝟙 _) (μ_δ : μ ≫ δ = 𝟙 _)
  body: .ofBifunctor ε μ associativity left_unitality right_unitality
  toOplaxMonoidal := .ofBifunctor η δ oplax_associativity oplax_left_unitality oplax_right_unitality
  ε_η := ε_η
  η_ε := η_ε
  μ_δ X Y := NatTrans.congr_app ((NatTrans.congr_app μ_δ) X) Y
  δ_μ X Y := NatTrans.congr_app ((NatTrans.congr

中文:
定义 ofBifunctor
  签名: (ε_η : ε ≫ η = 𝟙 _) (η_ε : η ≫ ε = 𝟙 _) (μ_δ : μ ≫ δ = 𝟙 _)
  定义体: .ofBifunctor ε μ associativity left_unitality right_unitality
  toOplaxMonoidal := .ofBifunctor η δ oplax_associativity oplax_left_unitality oplax_right_unitality
  ε_η := ε_η
  η_ε := η_ε
  μ_δ X Y := NatTrans.congr_app ((NatTrans.congr_app μ_δ) X) Y
  δ_μ X Y := NatTrans.congr_app ((NatTrans.congr

Depends on / 依赖: associativity, left_unitality, ofBifunctor, right_unitality
-/
def ofBifunctor (ε_η : ε ≫ η = 𝟙 _) (η_ε : η ≫ ε = 𝟙 _) (μ_δ : μ ≫ δ = 𝟙 _)
    (δ_μ : δ ≫ μ = 𝟙 _) : F.Monoidal where
  toLaxMonoidal := .ofBifunctor ε μ associativity left_unitality right_unitality
  toOplaxMonoidal := .ofBifunctor η δ oplax_associativity oplax_left_unitality oplax_right_unitality
  ε_η := ε_η
  η_ε := η_ε
  μ_δ X Y := NatTrans.congr_app ((NatTrans.congr_app μ_δ) X) Y
  δ_μ X Y := NatTrans.congr_app ((NatTrans.congr_app δ_μ) X) Y

end Monoidal

namespace CoreMonoidal

variable {F : C ⥤ D}
    /- unit isomorphism -/
    (ε : 𝟙_ D ≅ F.obj (𝟙_ C))
    /- tensorator as an isomorphism of bifunctors -/
    (μ : curriedTensorPre F ≅ curriedTensorPost F)
    /- the associativity hexagon commutes -/
    (associativity : firstMap μ.hom = secondMap μ.hom)
    /- the left unitality square commutes -/
    (left_unitality : LaxMonoidal.ofBifunctor.leftMapₗ F =
      topMapₗ ε.hom ≫ μ.hom.app (𝟙_ C) ≫ bottomMapₗ F)
    /- the right unitality square commutes -/
    (right_unitality : LaxMonoidal.ofBifunctor.leftMapᵣ F =
      topMapᵣ ε.hom ≫ ((flipFunctor _ _ _).map μ.hom).app (𝟙_ C) ≫ bottomMapᵣ F)

/--
Definition of `ofBifunctor` / `ofBifunctor` 的定义

English:
definition ofBifunctor
  signature: : F.CoreMonoidal where
  body: ε
  μIso X Y := (μ.app X).app Y
  μIso_hom_natural_left f X := NatTrans.congr_app (μ.hom.naturality f) X
  μIso_hom_natural_right X f := (μ.hom.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatT

中文:
定义 ofBifunctor
  签名: : F.余reMonoidal where
  定义体: ε
  μIso X Y := (μ.app X).app Y
  μIso_hom_natural_left f X := NatTrans.congr_app (μ.hom.naturality f) X
  μIso_hom_natural_right X f := (μ.hom.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatT
-/
def ofBifunctor : F.CoreMonoidal where
  εIso := ε
  μIso X Y := (μ.app X).app Y
  μIso_hom_natural_left f X := NatTrans.congr_app (μ.hom.naturality f) X
  μIso_hom_natural_right X f := (μ.hom.app X).naturality f
  associativity X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app associativity X) Y) Z
  left_unitality X := NatTrans.congr_app left_unitality X
  right_unitality X := NatTrans.congr_app right_unitality X

end CategoryTheory.Functor.CoreMonoidal
