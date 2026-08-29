/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The section functor as a right adjoint to the toOver functor

We show that in a cartesian monoidal category `C`, for any exponentiable object `I`, the functor
`toOver I : C ⥤ Over I` mapping an object `X` to the projection `snd : X ⊗ I ⟶ I` in `Over I`
has a right adjoint `sections I : Over I ⥤ C` whose object part is the object of sections
of `X` over `I`.

In particular, if `C` is cartesian closed, then for all objects `I` in `C`, `toOver I : C ⥤ Over I`
has a right adjoint.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Closed I]

/--
Definition of `curryRightUnitorHom` / `curryRightUnitorHom` 的定义

English:
abbreviation curryRightUnitorHom
  signature: : 𝟙_ C ⟶ (I ⟶[C] I)
  body: curry (ρ_ _).hom

中文:
缩写 curryRightUnitorHom
  签名: : 𝟙_ C ⟶ (I ⟶[C] I)
  定义体: curry (ρ_ _).hom
-/
abbrev curryRightUnitorHom : 𝟙_ C ⟶ (I ⟶[C] I) :=
curry (ρ_ _).hom

variable {I}

/--
theorem `toUnit_comp_curryRightUnitorHom` / 定理 `toUnit_comp_curryRightUnitorHom`

English:
theorem toUnit_comp_curryRightUnitorHom
  given: {A : C}
  proof: by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

中文:
定理 toUnit_comp_curryRightUnitorHom
  条件: {A : C}
  证明: by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

Depends on / 依赖: curryRightUnitorHom, fst_def, toUnit, uncurry_injective, uncurry_natural_left
-/
theorem toUnit_comp_curryRightUnitorHom {A : C} :
    toUnit A ≫ curryRightUnitorHom I = curry (fst I A) := by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

namespace Over

open ChosenPullbacksAlong

variable (I) [ChosenPullbacksAlong (curryRightUnitorHom I)]

/-- The functor mapping an object `X : Over I` to the object of sections of `X` over `I`, defined
by the following pullback diagram. The functor's mapping of morphisms is induced by `pullbackMap`,
that is by the universal property of chosen pullbacks.

```
 sections X --> I ⟹ X
   | |
   | |
   v v
  𝟙_ C -----> I ⟹ I
```
-/
@[simps]
/--
Definition of `sections` / `sections` 的定义

English:
definition sections
  signature: : Over I ⥤ C where
  body: pullbackObj (ihom I |>.map X.hom) (curryRightUnitorHom I)
  map u := pullbackMap _ _ _ _ (ihom I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp]) (by cat_disch)

中文:
定义 sections
  签名: : Over I ⥤ C where
  定义体: pullbackObj (ihom I |>.map X.hom) (curryRightUnitorHom I)
  map u := pullbackMap _ _ _ _ (ihom I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp]) (by cat_disch)

Depends on / 依赖: X.hom, curryRightUnitorHom, pullbackObj
-/
def sections : Over I ⥤ C where
  obj X := pullbackObj (ihom I |>.map X.hom) (curryRightUnitorHom I)
  map u := pullbackMap _ _ _ _ (ihom I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp]) (by cat_disch)

variable {I}

open ChosenPullbacksAlong

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sectionsCurry` / `sectionsCurry` 的定义

English:
definition sectionsCurry
  signature: {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X)
  body: ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [w]; rw [← curry_natural_right]; rw [toUnit_comp_curryRightUnitorHom]
    congr
    simp [braiding_hom_snd])

中文:
定义 sectionsCurry
  签名: {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X)
  定义体: ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [w]; rw [← curry_natural_right]; rw [toUnit_comp_curryRightUnitorHom]
    congr
    simp [braiding_hom_snd])

Depends on / 依赖: Category, Category.assoc, ChosenPullbacksAlong, ChosenPullbacksAlong.lift, Functor, Functor.map_comp, braiding_hom_snd, curry_natural_right, map_comp, toUnit, toUnit_comp_curryRightUnitorHom, u.left
-/
def sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) :
    A ⟶ (sections I).obj X :=
  ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [w]; rw [← curry_natural_right]; rw [toUnit_comp_curryRightUnitorHom]
    congr
    simp [braiding_hom_snd])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sectionsUncurry` / `sectionsUncurry` 的定义

English:
definition sectionsUncurry
  signature: {X : Over I} {A : C} (v : A ⟶ (sections I).obj X)
  body: letI v₂ : A ⟶ (I ⟶[C] X.left) := v ≫ fst (ihom I |>.map X.hom) (curryRightUnitorHom I)
  Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    have comm : toUnit A ≫ (curryRightUnitorHom I) = v₂ ≫ (ihom I).map X.hom := by
      rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A) (v ≫ snd ..)]
      simp

中文:
定义 sectionsUncurry
  签名: {X : Over I} {A : C} (v : A ⟶ (sections I).obj X)
  定义体: letI v₂ : A ⟶ (I ⟶[C] X.left) := v ≫ fst (ihom I |>.map X.hom) (curryRightUnitorHom I)
  Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    have comm : toUnit A ≫ (curryRightUnitorHom I) = v₂ ≫ (ihom I).map X.hom := by
      rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A) (v ≫ snd ..)]
      simp

Depends on / 依赖: Equiv.symm_apply_apply, IsTerminal, IsTerminal.hom_ext, Over.homMk, X.hom, X.left, adjunction, condition, curriedTensor_obj_map, curriedTensor_obj_obj, curryRightUnitorHom, homEquiv_naturality_right_square, hom_ext, ihom.adjunction, isTerminalTensorUnit, symm_apply_apply, toUnit, uncurry
-/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (toOver I).obj A ⟶ X :=
  letI v₂ : A ⟶ (I ⟶[C] X.left) := v ≫ fst (ihom I |>.map X.hom) (curryRightUnitorHom I)
  Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    have comm : toUnit A ≫ (curryRightUnitorHom I) = v₂ ≫ (ihom I).map X.hom := by
      rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A) (v ≫ snd ..)]
      simp [v₂, condition]
    dsimp [curryRightUnitorHom] at comm
    have w' := (ihom.adjunction I).homEquiv_naturality_right_square _ _ _ _ comm
    simp only [curriedTensor_obj_obj, curriedTensor_obj_map, curry,
      Equiv.symm_apply_apply] at w'
    dsimp [uncurry] at *
    rw [Category.assoc]; rw [← w']; rw [whiskerLeft_toUnit_comp_rightUnitor_hom]; rw [braiding_hom_fst])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sectionsCurry_sectionUncurry` / 定理 `sectionsCurry_sectionUncurry`

English:
theorem sectionsCurry_sectionUncurry
  given: {X : Over I} {A : C} {v : A ⟶ (sections I).obj X}
  proof: by
  dsimp [sectionsCurry, sectionsUncurry]
  cat_disch

中文:
定理 sectionsCurry_sectionUncurry
  条件: {X : Over I} {A : C} {v : A ⟶ (sections I).obj X}
  证明: by
  dsimp [sectionsCurry, sectionsUncurry]
  cat_disch
-/
theorem sectionsCurry_sectionUncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sectionsUncurry_sectionsCurry` / 定理 `sectionsUncurry_sectionsCurry`

English:
theorem sectionsUncurry_sectionsCurry
  given: {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X}
  proof: by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

中文:
定理 sectionsUncurry_sectionsCurry
  条件: {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X}
  证明: by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp
-/
theorem sectionsUncurry_sectionsCurry {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

open Adjunction

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See `starSectionsAdjunction`. -/
@[simps homEquiv]
/--
Definition of `coreHomEquivToOverSections` / `coreHomEquivToOverSections` 的定义

English:
definition coreHomEquivToOverSections
  signature: : CoreHomEquiv (toOver I) (sections I) where
  body: { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only 

中文:
定义 coreHomEquivToOverSections
  签名: : 核态射等价 (toOver I) (sections I) where
  定义体: { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only 

Depends on / 依赖: ChosenPullbacksAlong, ChosenPullbacksAlong.hom_ext, Over.homMk_comp, curryRightUnitorHom, curry_, homEquiv_naturality_left_symm, homEquiv_naturality_right, homMk_comp, hom_ext, invFun, left_inv, right_inv, sectionsCurry, sectionsCurry_sectionUncurry, sectionsUncurry, sectionsUncurry_sectionsCurry, toOver_map, uncurry_natural_left
-/
def coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where
  homEquiv A X :=
    { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only [toOver_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    apply ChosenPullbacksAlong.hom_ext
    · simp [← curry_natural_right]
    · simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction between the toOver functor and the sections functor. -/
@[simps! unit_app counit_app]
/--
Definition of `toOverSectionsAdj` / `toOverSectionsAdj` 的定义

English:
definition toOverSectionsAdj
  signature: : toOver I ⊣ sections I
  body: .mkOfHomEquiv (coreHomEquivToOverSections I)

中文:
定义 toOverSectionsAdj
  签名: : toOver I ⊣ sections I
  定义体: .mkOfHomEquiv (coreHomEquivToOverSections I)

Depends on / 依赖: coreHomEquivToOverSections, mkOfHomEquiv
-/
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv (coreHomEquivToOverSections I)

end Over

end Sections

end CategoryTheory
