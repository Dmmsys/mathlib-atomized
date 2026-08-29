/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Tactic.ApplyFun

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : Arrow C`:
1. `f.cechNerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmentedCechNerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `SimplicialObject.cechNerve` and `SimplicialObject.augmentedCechNerve` are
  functorial versions of 1 resp. 2.

We end the file with a description of the Čech nerve of an arrow `X ⟶ ⊤_ C` to a terminal
object, when `C` has finite products. We call this `cechNerveTerminalFrom`. When `C` is
`G`-Set this gives us `EG` (the universal cover of the classifying space of `G`) as a simplicial
`G`-set, which is useful for group cohomology.

-/

@[expose] public section


open CategoryTheory Limits

open scoped Simplicial

noncomputable section

universe v u w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Arrow

variable (f : Arrow C)
variable [forall n : Nat, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The Čech nerve associated to an arrow. -/
@[simps, implicit_reducible]
/--
Definition of `cechNerve` / `cechNerve` 的定义

English:
definition cechNerve
  signature: : SimplicialObject C where
  body: widePullback.{0} f.right (fun _ : Fin (n.unop.len + 1) => f.left) fun _ => f.hom
  map g := WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (g.unop.toOrderHom i)) (by simp)

中文:
定义 cechNerve
  签名: : SimplicialObject C where
  定义体: widePullback.{0} f.right (fun _ : Fin (n.unop.len + 1) => f.left) fun _ => f.hom
  map g := WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (g.unop.toOrderHom i)) (by simp)

Depends on / 依赖: f.hom, f.left, f.right, n.unop.len, widePullback
-/
def cechNerve : SimplicialObject C where
  obj n := widePullback.{0} f.right (fun _ : Fin (n.unop.len + 1) => f.left) fun _ => f.hom
  map g := WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (g.unop.toOrderHom i)) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism between Čech nerves associated to a morphism of arrows. -/
@[simps]
/--
Definition of `mapCechNerve` / `mapCechNerve` 的定义

English:
definition mapCechNerve
  signature: {f g : Arrow C}
  body: WidePullback.lift (WidePullback.base _ ≫ F.right) (fun i => WidePullback.π _ i ≫ F.left)
      fun j => by simp

中文:
定义 mapCechNerve
  签名: {f g : 箭头 C}
  定义体: WidePullback.lift (WidePullback.base _ ≫ F.right) (fun i => WidePullback.π _ i ≫ F.left)
      fun j => by simp

Depends on / 依赖: F.left, F.right, WidePullback, WidePullback.base, WidePullback.lift
-/
def mapCechNerve {f g : Arrow C}
    [forall n : Nat, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [forall n : Nat, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.cechNerve ⟶ g.cechNerve where
  app n :=
    WidePullback.lift (WidePullback.base _ ≫ F.right) (fun i => WidePullback.π _ i ≫ F.left)
      fun j => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
/--
Definition of `augmentedCechNerve` / `augmentedCechNerve` 的定义

English:
definition augmentedCechNerve
  signature: : SimplicialObject.Augmented C where
  body: f.cechNerve
  right := f.right
  hom := { app := fun _ => WidePullback.base _ }

中文:
定义 augmentedCechNerve
  签名: : SimplicialObject.Augmented C where
  定义体: f.cechNerve
  right := f.right
  hom := { app := fun _ => WidePullback.base _ }

Depends on / 依赖: cechNerve, f.cechNerve
-/
def augmentedCechNerve : SimplicialObject.Augmented C where
  left := f.cechNerve
  right := f.right
  hom := { app := fun _ => WidePullback.base _ }

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between augmented Čech nerve associated to a morphism of arrows. -/
@[simps]
/--
Definition of `mapAugmentedCechNerve` / `mapAugmentedCechNerve` 的定义

English:
definition mapAugmentedCechNerve
  signature: {f g : Arrow C}
  body: mapCechNerve F
  right := F.right

中文:
定义 mapAugmentedCechNerve
  签名: {f g : 箭头 C}
  定义体: mapCechNerve F
  right := F.right

Depends on / 依赖: mapCechNerve
-/
def mapAugmentedCechNerve {f g : Arrow C}
    [forall n : Nat, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [forall n : Nat, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechNerve ⟶ g.augmentedCechNerve where
  left := mapCechNerve F
  right := F.right

end CategoryTheory.Arrow

namespace CategoryTheory

namespace SimplicialObject

variable
  [forall (n : Nat) (f : Arrow C), HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Čech nerve construction, as a functor from `Arrow C`. -/
@[simps]
/--
Definition of `cechNerve` / `cechNerve` 的定义

English:
definition cechNerve
  signature: : Arrow C ⥤ SimplicialObject C where
  body: f.cechNerve
  map F := Arrow.mapCechNerve F

中文:
定义 cechNerve
  签名: : 箭头 C ⥤ SimplicialObject C where
  定义体: f.cechNerve
  map F := Arrow.mapCechNerve F

Depends on / 依赖: cechNerve, f.cechNerve
-/
def cechNerve : Arrow C ⥤ SimplicialObject C where
  obj f := f.cechNerve
  map F := Arrow.mapCechNerve F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve construction, as a functor from `Arrow C`. -/
@[simps!]
/--
Definition of `augmentedCechNerve` / `augmentedCechNerve` 的定义

English:
definition augmentedCechNerve
  signature: : Arrow C ⥤ SimplicialObject.Augmented C where
  body: f.augmentedCechNerve
  map F := Arrow.mapAugmentedCechNerve F

中文:
定义 augmentedCechNerve
  签名: : 箭头 C ⥤ SimplicialObject.Augmented C where
  定义体: f.augmentedCechNerve
  map F := Arrow.mapAugmentedCechNerve F

Depends on / 依赖: augmentedCechNerve, f.augmentedCechNerve
-/
def augmentedCechNerve : Arrow C ⥤ SimplicialObject.Augmented C where
  obj f := f.augmentedCechNerve
  map F := Arrow.mapAugmentedCechNerve F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/--
Definition of `equivalenceRightToLeft` / `equivalenceRightToLeft` 的定义

English:
definition equivalenceRightToLeft
  signature: (X : SimplicialObject.Augmented C) (F : Arrow C)
  body: G.left.app _ ≫ WidePullback.π _ 0
  right := G.right
  w := by
    have := G.w
    apply_fun fun e => e.app (Opposite.op ⦋0⦌) at this
    simpa using this

中文:
定义 equivalenceRightToLeft
  签名: (X : SimplicialObject.Augmented C) (F : 箭头 C)
  定义体: G.left.app _ ≫ WidePullback.π _ 0
  right := G.right
  w := by
    have := G.w
    apply_fun fun e => e.app (Opposite.op ⦋0⦌) at this
    simpa using this

Depends on / 依赖: G.left.app, WidePullback
-/
def equivalenceRightToLeft (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : X ⟶ F.augmentedCechNerve) : Augmented.toArrow.obj X ⟶ F where
  left := G.left.app _ ≫ WidePullback.π _ 0
  right := G.right
  w := by
    have := G.w
    apply_fun fun e => e.app (Opposite.op ⦋0⦌) at this
    simpa using this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/--
Definition of `equivalenceLeftToRight` / `equivalenceLeftToRight` 的定义

English:
definition equivalenceLeftToRight
  signature: (X : SimplicialObject.Augmented C) (F : Arrow C)
  body: { app := fun x =>
        Limits.WidePullback.lift (X.hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const _ x.unop i).op ≫ G.left) fun i => by simp
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePullback.lift_π, Category.assoc, ← 

中文:
定义 equivalenceLeftToRight
  签名: (X : SimplicialObject.Augmented C) (F : 箭头 C)
  定义体: { app := fun x =>
        Limits.WidePullback.lift (X.hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const _ x.unop i).op ≫ G.left) fun i => by simp
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePullback.lift_π, Category.assoc, ← 

Depends on / 依赖: Category, Category.assoc, G.left, G.right, Limits, Limits.WidePullback.lift, SimplexCategory, SimplexCategory.const, WidePullback, WidePullback.lift_, X.hom.app, X.left.map, X.left.map_comp_assoc, map_comp_assoc, naturality, x.unop
-/
def equivalenceLeftToRight (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : Augmented.toArrow.obj X ⟶ F) : X ⟶ F.augmentedCechNerve where
  left :=
    { app := fun x =>
        Limits.WidePullback.lift (X.hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const _ x.unop i).op ≫ G.left) fun i => by simp
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePullback.lift_π, Category.assoc, ← X.left.map_comp_assoc]
          rfl
        · simp }
  right := G.right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/--
Definition of `cechNerveEquiv` / `cechNerveEquiv` 的定义

English:
definition cechNerveEquiv
  signature: (X : SimplicialObject.Augmented C) (F : Arrow C)
  body: equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv A := by ext <;> simp
  right_inv := by
    intro A
    ext x : 2
    · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
      · simp
      · simpa using congr_app A.w.symm x
    · simp

中文:
定义 cechNerveEquiv
  签名: (X : SimplicialObject.Augmented C) (F : 箭头 C)
  定义体: equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv A := by ext <;> simp
  right_inv := by
    intro A
    ext x : 2
    · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
      · simp
      · simpa using congr_app A.w.symm x
    · simp

Depends on / 依赖: equivalenceLeftToRight
-/
def cechNerveEquiv (X : SimplicialObject.Augmented C) (F : Arrow C) :
    (Augmented.toArrow.obj X ⟶ F) ≃ (X ⟶ F.augmentedCechNerve) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv A := by ext <;> simp
  right_inv := by
    intro A
    ext x : 2
    · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
      · simp
      · simpa using congr_app A.w.symm x
    · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cechNerveAdjunction` / `cechNerveAdjunction` 的定义

English:
abbreviation cechNerveAdjunction
  signature: : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNerve
  body: Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv]; cat_disch
      homEquiv_naturality_right := by
        dsimp [cechNerveEquiv]
        -- The next three lines were not needed before https://github.com/leanprover/lean4/pull/26

中文:
缩写 cechNerveAdjunction
  签名: : (Augmented.toArrow : _ ⥤ 箭头 C) ⊣ augmentedCechNerve
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv]; cat_disch
      homEquiv_naturality_right := by
        dsimp [cechNerveEquiv]
        -- The next three lines were not needed before https://github.com/leanprover/lean4/pull/26

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, cat_disch, cechNerveEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv
-/
abbrev cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNerve :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv]; cat_disch
      homEquiv_naturality_right := by
        dsimp [cechNerveEquiv]
        -- The next three lines were not needed before https://github.com/leanprover/lean4/pull/2644
        intro X Y Y' f g
        change equivalenceLeftToRight X Y' (f ≫ g) =
          equivalenceLeftToRight X Y f ≫ augmentedCechNerve.map g
        cat_disch
    }

end SimplicialObject

end CategoryTheory

namespace CategoryTheory.Arrow

variable (f : Arrow C)
variable [forall n : Nat, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The Čech conerve associated to an arrow. -/
@[simps]
/--
Definition of `cechConerve` / `cechConerve` 的定义

English:
definition cechConerve
  signature: : CosimplicialObject C where
  body: widePushout f.left (fun _ : Fin (n.len + 1) => f.right) fun _ => f.hom
  map {x y} g := by
    refine WidePushout.desc (WidePushout.head _)
      (fun i => (@WidePushout.ι _ _ _ _ _ (fun _ => f.hom) (_) (g.toOrderHom i))) (fun j => ?_)
    rw [← WidePushout.arrow_ι]

中文:
定义 cechConerve
  签名: : CosimplicialObject C where
  定义体: widePushout f.left (fun _ : Fin (n.len + 1) => f.right) fun _ => f.hom
  map {x y} g := by
    refine WidePushout.desc (WidePushout.head _)
      (fun i => (@WidePushout.ι _ _ _ _ _ (fun _ => f.hom) (_) (g.toOrderHom i))) (fun j => ?_)
    rw [← WidePushout.arrow_ι]

Depends on / 依赖: f.hom, f.left, f.right, n.len, widePushout
-/
def cechConerve : CosimplicialObject C where
  obj n := widePushout f.left (fun _ : Fin (n.len + 1) => f.right) fun _ => f.hom
  map {x y} g := by
    refine WidePushout.desc (WidePushout.head _)
      (fun i => (@WidePushout.ι _ _ _ _ _ (fun _ => f.hom) (_) (g.toOrderHom i))) (fun j => ?_)
    rw [← WidePushout.arrow_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
/--
Definition of `mapCechConerve` / `mapCechConerve` 的定义

English:
definition mapCechConerve
  signature: {f g : Arrow C}
  body: WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))

中文:
定义 mapCechConerve
  签名: {f g : 箭头 C}
  定义体: WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))

Depends on / 依赖: F.left, WidePushout, WidePushout.desc, WidePushout.head
-/
def mapCechConerve {f g : Arrow C}
    [forall n : Nat, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [forall n : Nat, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.cechConerve ⟶ g.cechConerve where
  app n := WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
/--
Definition of `augmentedCechConerve` / `augmentedCechConerve` 的定义

English:
definition augmentedCechConerve
  signature: : CosimplicialObject.Augmented C where
  body: f.left
  right := f.cechConerve
  hom :=
    { app := fun _ => (WidePushout.head _ : f.left ⟶ _) }

中文:
定义 augmentedCechConerve
  签名: : CosimplicialObject.Augmented C where
  定义体: f.left
  right := f.cechConerve
  hom :=
    { app := fun _ => (WidePushout.head _ : f.left ⟶ _) }

Depends on / 依赖: f.left
-/
def augmentedCechConerve : CosimplicialObject.Augmented C where
  left := f.left
  right := f.cechConerve
  hom :=
    { app := fun _ => (WidePushout.head _ : f.left ⟶ _) }

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between augmented Čech conerves associated to a morphism of arrows. -/
@[simps]
/--
Definition of `mapAugmentedCechConerve` / `mapAugmentedCechConerve` 的定义

English:
definition mapAugmentedCechConerve
  signature: {f g : Arrow C}
  body: F.left
  right := mapCechConerve F

中文:
定义 mapAugmentedCechConerve
  签名: {f g : 箭头 C}
  定义体: F.left
  right := mapCechConerve F

Depends on / 依赖: F.left
-/
def mapAugmentedCechConerve {f g : Arrow C}
    [forall n : Nat, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [forall n : Nat, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechConerve ⟶ g.augmentedCechConerve where
  left := F.left
  right := mapCechConerve F

end CategoryTheory.Arrow

namespace CategoryTheory

namespace CosimplicialObject

variable
  [forall (n : Nat) (f : Arrow C), HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
/--
Definition of `cechConerve` / `cechConerve` 的定义

English:
definition cechConerve
  signature: : Arrow C ⥤ CosimplicialObject C where
  body: f.cechConerve
  map F := Arrow.mapCechConerve F

中文:
定义 cechConerve
  签名: : 箭头 C ⥤ CosimplicialObject C where
  定义体: f.cechConerve
  map F := Arrow.mapCechConerve F

Depends on / 依赖: cechConerve, f.cechConerve
-/
def cechConerve : Arrow C ⥤ CosimplicialObject C where
  obj f := f.cechConerve
  map F := Arrow.mapCechConerve F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
/--
Definition of `augmentedCechConerve` / `augmentedCechConerve` 的定义

English:
definition augmentedCechConerve
  signature: : Arrow C ⥤ CosimplicialObject.Augmented C where
  body: f.augmentedCechConerve
  map F := Arrow.mapAugmentedCechConerve F

中文:
定义 augmentedCechConerve
  签名: : 箭头 C ⥤ CosimplicialObject.Augmented C where
  定义体: f.augmentedCechConerve
  map F := Arrow.mapAugmentedCechConerve F

Depends on / 依赖: augmentedCechConerve, f.augmentedCechConerve
-/
def augmentedCechConerve : Arrow C ⥤ CosimplicialObject.Augmented C where
  obj f := f.augmentedCechConerve
  map F := Arrow.mapAugmentedCechConerve F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps!]
/--
Definition of `equivalenceLeftToRight` / `equivalenceLeftToRight` 的定义

English:
definition equivalenceLeftToRight
  signature: (F : Arrow C) (X : CosimplicialObject.Augmented C)
  body: Arrow.homMk G.left (WidePushout.ι _ 0 ≫ G.right.app ⦋0⦌ :) (by
    dsimp
    rw [WidePushout.arrow_ι_assoc (fun (_ : Fin 1) => F.hom)]
    exact congr_app G.w ⦋0⦌)

中文:
定义 equivalenceLeftToRight
  签名: (F : 箭头 C) (X : CosimplicialObject.Augmented C)
  定义体: Arrow.homMk G.left (WidePushout.ι _ 0 ≫ G.right.app ⦋0⦌ :) (by
    dsimp
    rw [WidePushout.arrow_ι_assoc (fun (_ : Fin 1) => F.hom)]
    exact congr_app G.w ⦋0⦌)

Depends on / 依赖: Arrow.homMk, F.hom, G.left, G.right.app, WidePushout, WidePushout.arrow_, congr_app
-/
def equivalenceLeftToRight (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F.augmentedCechConerve ⟶ X) : F ⟶ Augmented.toArrow.obj X :=
  Arrow.homMk G.left (WidePushout.ι _ 0 ≫ G.right.app ⦋0⦌ :) (by
    dsimp
    rw [WidePushout.arrow_ι_assoc (fun (_ : Fin 1) => F.hom)]
    exact congr_app G.w ⦋0⦌)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps!]
/--
Definition of `equivalenceRightToLeft` / `equivalenceRightToLeft` 的定义

English:
definition equivalenceRightToLeft
  signature: (F : Arrow C) (X : CosimplicialObject.Augmented C)
  body: G.left
  right :=
    { app := fun x =>
        Limits.WidePushout.desc (G.left ≫ X.hom.app _)
          (fun i => G.right ≫ X.right.map (SimplexCategory.const _ x i))
          (by
            rintro j
            rw [← Arrow.w_assoc G]
            have t := X.hom.naturality (SimplexCategory.const 

中文:
定义 equivalenceRightToLeft
  签名: (F : 箭头 C) (X : CosimplicialObject.Augmented C)
  定义体: G.left
  right :=
    { app := fun x =>
        Limits.WidePushout.desc (G.left ≫ X.hom.app _)
          (fun i => G.right ≫ X.right.map (SimplexCategory.const _ x i))
          (by
            rintro j
            rw [← Arrow.w_assoc G]
            have t := X.hom.naturality (SimplexCategory.const 

Depends on / 依赖: G.left
-/
def equivalenceRightToLeft (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F ⟶ Augmented.toArrow.obj X) : F.augmentedCechConerve ⟶ X where
  left := G.left
  right :=
    { app := fun x =>
        Limits.WidePushout.desc (G.left ≫ X.hom.app _)
          (fun i => G.right ≫ X.right.map (SimplexCategory.const _ x i))
          (by
            rintro j
            rw [← Arrow.w_assoc G]
            have t := X.hom.naturality (SimplexCategory.const ⦋0⦌ x j)
            dsimp at t ⊢
            simp only [Category.id_comp] at t
            rw [← t])
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePushout.ι_desc_assoc, WidePushout.ι_desc]
          rw [Category.assoc]; rw [← X.right.map_comp]
          rfl
        · simp [← NatTrans.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
/--
Definition of `cechConerveEquiv` / `cechConerveEquiv` 的定义

English:
definition cechConerveEquiv
  signature: (F : Arrow C) (X : CosimplicialObject.Augmented C)
  body: equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    ext x : 2
    · rfl
    · refine WidePushout.hom_ext _ _ _ (fun j => ?_) ?_
      · dsimp
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          S

中文:
定义 cechConerveEquiv
  签名: (F : 箭头 C) (X : CosimplicialObject.Augmented C)
  定义体: equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    ext x : 2
    · rfl
    · refine WidePushout.hom_ext _ _ _ (fun j => ?_) ?_
      · dsimp
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          S

Depends on / 依赖: equivalenceLeftToRight
-/
def cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) :
    (F.augmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    ext x : 2
    · rfl
    · refine WidePushout.hom_ext _ _ _ (fun j => ?_) ?_
      · dsimp
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          SimplexCategory.len_mk, Arrow.cechConerve_map, colimit.ι_desc,
          WidePushoutShape.mkCocone_ι_app, colimit.ι_desc_assoc]
        rfl
      · dsimp
        rw [colimit.ι_desc]
        exact congr_app A.w x
  right_inv := by
    intro A
    ext
    · rfl
    · dsimp
      rw [WidePushout.ι_desc]
      nth_rw 2 [← Category.comp_id A.right]
      congr 1
      convert! X.right.map_id _
      ext ⟨a, ha⟩
      simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cechConerveAdjunction` / `cechConerveAdjunction` 的定义

English:
abbreviation cechConerveAdjunction
  signature: : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C)
  body: Adjunction.mkOfHomEquiv { homEquiv := cechConerveEquiv }

中文:
缩写 cechConerveAdjunction
  签名: : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ 箭头 C)
  定义体: Adjunction.mkOfHomEquiv { homEquiv := cechConerveEquiv }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, cechConerveEquiv, homEquiv, mkOfHomEquiv
-/
abbrev cechConerveAdjunction : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C) :=
  Adjunction.mkOfHomEquiv { homEquiv := cechConerveEquiv }

end CosimplicialObject

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cechNerveTerminalFrom` / `cechNerveTerminalFrom` 的定义

English:
definition cechNerveTerminalFrom
  signature: {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C)
  body: ∏ᶜ fun _ : Fin (n.unop.len + 1) => X
  map f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)

中文:
定义 cechNerveTerminalFrom
  签名: {C : 类型u} [范畴.{v} C] [有FiniteProducts C] (X : C)
  定义体: ∏ᶜ fun _ : Fin (n.unop.len + 1) => X
  map f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)

Depends on / 依赖: n.unop.len
-/
def cechNerveTerminalFrom {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :
    SimplicialObject C where
  obj n := ∏ᶜ fun _ : Fin (n.unop.len + 1) => X
  map f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)

namespace CechNerveTerminalFrom

variable [HasTerminal C] (ι : Type w)

/-- The diagram `Option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
@[implicit_reducible]
/--
Definition of `wideCospan` / `wideCospan` 的定义

English:
definition wideCospan
  signature: (X : C)
  body: WidePullbackShape.wideCospan (terminal C) (fun _ : ι => X) fun _ => terminal.from X

中文:
定义 wideCospan
  签名: (X : C)
  定义体: WidePullbackShape.wideCospan (terminal C) (fun _ : ι => X) fun _ => terminal.from X

Depends on / 依赖: WidePullbackShape, WidePullbackShape.wideCospan, terminal, terminal.from, wideCospan
-/
def wideCospan (X : C) : WidePullbackShape ι ⥤ C :=
  WidePullbackShape.wideCospan (terminal C) (fun _ : ι => X) fun _ => terminal.from X

set_option backward.defeqAttrib.useBackward true in
/--
Instance `uniqueToWideCospanNone` / 实例 `uniqueToWideCospanNone`

English:
instance uniqueToWideCospanNone
  signature: (X Y : C)
  body: by
  dsimp [wideCospan]
  infer_instance

中文:
实例 uniqueToWideCospanNone
  签名: (X Y : C)
  定义体: by
  dsimp [wideCospan]
  infer_instance

Depends on / 依赖: infer_instance, wideCospan
-/
instance uniqueToWideCospanNone (X Y : C) : Unique (Y ⟶ (wideCospan ι X).obj none) := by
  dsimp [wideCospan]
  infer_instance

variable [HasFiniteProducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `wideCospan.limitCone` / `wideCospan.limitCone` 的定义

English:
definition wideCospan.limitCone
  signature: [Finite ι] (X : C)
  body: { pt := ∏ᶜ fun _ : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality := fun i j f => by
            cases f
            · cases i
              all_goals simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_ma

中文:
定义 wideCospan.limitCone
  签名: [有限 ι] (X : C)
  定义体: { pt := ∏ᶜ fun _ : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality := fun i j f => by
            cases f
            · cases i
              all_goals simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_ma

Depends on / 依赖: Functor, Functor.const_obj_map, Functor.const_obj_obj, Limits, Limits.Pi.lift, Option.casesOn, all_goals, casesOn, comp_from, const_obj_map, const_obj_obj, isLimit, limit.lift_, naturality, subsingleton, terminal, terminal.comp_from, terminal.from
-/
def wideCospan.limitCone [Finite ι] (X : C) : LimitCone (wideCospan ι X) where
  cone :=
    { pt := ∏ᶜ fun _ : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality := fun i j f => by
            cases f
            · cases i
              all_goals simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, terminal.comp_from]
              subsingleton } }
  isLimit :=
    { lift := fun s => Limits.Pi.lift fun j => s.π.app (some j)
      fac := fun s j => Option.casesOn j (by subsingleton) fun _ => limit.lift_π _ _
      uniq := fun s f h => by
        dsimp
        ext j
        dsimp only [Limits.Pi.lift]
        rw [limit.lift_π]
        dsimp
        rw [← h (some j)] }

/--
Instance `hasWidePullback` / 实例 `hasWidePullback`

English:
instance hasWidePullback
  signature: [Finite ι] (X : C)
  body: by
  cases nonempty_fintype ι
  exact ⟨⟨wideCospan.limitCone ι X⟩⟩

中文:
实例 hasWidePullback
  签名: [有限 ι] (X : C)
  定义体: by
  cases nonempty_fintype ι
  exact ⟨⟨wideCospan.limitCone ι X⟩⟩

Depends on / 依赖: limitCone, nonempty_fintype, wideCospan, wideCospan.limitCone
-/
instance hasWidePullback [Finite ι] (X : C) :
    HasWidePullback (Arrow.mk (terminal.from X)).right
      (fun _ : ι => (Arrow.mk (terminal.from X)).left)
      (fun _ => (Arrow.mk (terminal.from X)).hom) := by
  cases nonempty_fintype ι
  exact ⟨⟨wideCospan.limitCone ι X⟩⟩

/--
Instance `hasWidePullback'` / 实例 `hasWidePullback'`

English:
instance hasWidePullback'
  signature: [Finite ι] (X : C)
  body: hasWidePullback _ _

中文:
实例 hasWidePullback'
  签名: [有限 ι] (X : C)
  定义体: hasWidePullback _ _

Depends on / 依赖: hasWidePullback
-/
instance hasWidePullback' [Finite ι] (X : C) :
    HasWidePullback (⊤_ C)
      (fun _ : ι => X)
      (fun _ => terminal.from X) :=
  hasWidePullback _ _

/--
Instance `hasLimit_wideCospan` / 实例 `hasLimit_wideCospan`

English:
instance hasLimit_wideCospan
  signature: [Finite ι] (X : C)
  body: hasWidePullback _ _

中文:
实例 hasLimit_wideCospan
  签名: [有限 ι] (X : C)
  定义体: hasWidePullback _ _

Depends on / 依赖: hasWidePullback
-/
instance hasLimit_wideCospan [Finite ι] (X : C) : HasLimit (wideCospan ι X) := hasWidePullback _ _

/--
Definition of `wideCospan.limitIsoPi` / `wideCospan.limitIsoPi` 的定义

English:
definition wideCospan.limitIsoPi
  signature: [Finite ι] (X : C)
  body: (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (wideCospan.limitCone ι X).2)

@[reassoc (attr := simp)]

中文:
定义 wideCospan.limitIsoPi
  签名: [有限 ι] (X : C)
  定义体: (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (wideCospan.limitCone ι X).2)

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, limitCone, wideCospan, wideCospan.limitCone
-/
def wideCospan.limitIsoPi [Finite ι] (X : C) :
    limit (wideCospan ι X) ≅ ∏ᶜ fun _ : ι => X :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (wideCospan.limitCone ι X).2)

@[reassoc (attr := simp)]
/--
lemma `wideCospan.limitIsoPi_inv_comp_pi` / 引理 `wideCospan.limitIsoPi_inv_comp_pi`

English:
lemma wideCospan.limitIsoPi_inv_comp_pi
  given: [Finite ι] (X : C) (j : ι)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

中文:
引理 wideCospan.limitIsoPi_inv_comp_pi
  条件: [有限 ι] (X : C) (j : ι)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
lemma wideCospan.limitIsoPi_inv_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).inv ≫ WidePullback.π _ j = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `wideCospan.limitIsoPi_hom_comp_pi` / 引理 `wideCospan.limitIsoPi_hom_comp_pi`

English:
lemma wideCospan.limitIsoPi_hom_comp_pi
  given: [Finite ι] (X : C) (j : ι)
  proof: by
  rw [← wideCospan.limitIsoPi_inv_comp_pi]; rw [Iso.hom_inv_id_assoc]

中文:
引理 wideCospan.limitIsoPi_hom_comp_pi
  条件: [有限 ι] (X : C) (j : ι)
  证明: by
  rw [← wideCospan.limitIsoPi_inv_comp_pi]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc, limitIsoPi_inv_comp_pi, wideCospan, wideCospan.limitIsoPi_inv_comp_pi
-/
lemma wideCospan.limitIsoPi_hom_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).hom ≫ Pi.π _ j = WidePullback.π _ j := by
  rw [← wideCospan.limitIsoPi_inv_comp_pi]; rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (X : C)
  body: NatIso.ofComponents (fun _ => wideCospan.limitIsoPi _ _) (fun {m n} f => by
    dsimp only [cechNerveTerminalFrom, Arrow.cechNerve]
    ext ⟨j⟩
    simp)

中文:
定义 iso
  签名: (X : C)
  定义体: NatIso.ofComponents (fun _ => wideCospan.limitIsoPi _ _) (fun {m n} f => by
    dsimp only [cechNerveTerminalFrom, Arrow.cechNerve]
    ext ⟨j⟩
    simp)

Depends on / 依赖: Arrow.cechNerve, NatIso, NatIso.ofComponents, cechNerve, cechNerveTerminalFrom, limitIsoPi, ofComponents, wideCospan, wideCospan.limitIsoPi
-/
def iso (X : C) : (Arrow.mk (terminal.from X)).cechNerve ≅ cechNerveTerminalFrom X :=
  NatIso.ofComponents (fun _ => wideCospan.limitIsoPi _ _) (fun {m n} f => by
    dsimp only [cechNerveTerminalFrom, Arrow.cechNerve]
    ext ⟨j⟩
    simp)

end CechNerveTerminalFrom

end CategoryTheory
