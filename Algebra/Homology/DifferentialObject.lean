/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `HomologicalComplex` indexed by an `AddCommGroup` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-!
We first prove some results about differential graded objects.

TODO: We should move these to their own file.
-/
namespace CategoryTheory.DifferentialObject

variable {β : Type*} [AddCommGroup β] {b : β}
variable {V : Type*} [Category* V] [HasZeroMorphisms V]
variable (X : DifferentialObject Int (GradedObjectWithShift b V))

/--
Definition of `objEqToHom` / `objEqToHom` 的定义

English:
abbreviation objEqToHom
  signature: {i j : β} (h : i = j)
  body: eqToHom (congr_arg X.obj h)

@[simp]

中文:
缩写 objEqToHom
  签名: {i j : β} (h : i = j)
  定义体: eqToHom (congr_arg X.obj h)

@[simp]

Depends on / 依赖: X.obj, congr_arg, eqToHom
-/
abbrev objEqToHom {i j : β} (h : i = j) :
    X.obj i ⟶ X.obj j :=
  eqToHom (congr_arg X.obj h)

@[simp]
/--
theorem `objEqToHom_refl` / 定理 `objEqToHom_refl`

English:
theorem objEqToHom_refl
  given: (i : β)
  statement: X.objEqToHom (refl i) = 𝟙 _
  proof: rfl

中文:
定理 objEqToHom_refl
  条件: (i : β)
  结论: X.objEqToHom (refl i) = 𝟙 _
  证明: rfl
-/
theorem objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _ :=
  rfl

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
set_option backward.isDefEq.respectTransparency false in -- Needed in dgoToHomologicalComplex
@[reassoc]
/--
theorem `objEqToHom_d` / 定理 `objEqToHom_d`

English:
theorem objEqToHom_d
  given: {x y : β} (h : x = y)
  proof: by cases h; simp

@[reassoc (attr := simp)]

中文:
定理 objEqToHom_d
  条件: {x y : β} (h : x = y)
  证明: by cases h; simp

@[reassoc (attr := simp)]
-/
theorem objEqToHom_d {x y : β} (h : x = y) :
    X.objEqToHom h ≫ X.d y = X.d x ≫ X.objEqToHom (by cases h; rfl) := by cases h; simp

@[reassoc (attr := simp)]
/--
theorem `d_squared_apply` / 定理 `d_squared_apply`

English:
theorem d_squared_apply
  given: {x : β}
  statement: X.d x ≫ X.d _ = 0
  proof: congr_fun X.d_squared _

中文:
定理 d_squared_apply
  条件: {x : β}
  结论: X.d x ≫ X.d _ = 0
  证明: congr_fun X.d_squared _

Depends on / 依赖: X.d_squared, congr_fun, d_squared
-/
theorem d_squared_apply {x : β} : X.d x ≫ X.d _ = 0 := congr_fun X.d_squared _

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
@[reassoc]
/--
theorem `eqToHom_f'` / 定理 `eqToHom_f'`

English:
theorem eqToHom_f'
  statement: {X Y : DifferentialObject Int (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
  proof: by cases h; simp

中文:
定理 eqToHom_f'
  结论: {X Y : 微分对象 整数 (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
  证明: by cases h; simp

Depends on / 依赖: hasHomology
-/
theorem eqToHom_f' {X Y : DifferentialObject Int (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
    (h : x = y) : X.objEqToHom h ≫ f.f y = f.f x ≫ Y.objEqToHom h := by cases h; simp

end CategoryTheory.DifferentialObject

open CategoryTheory.DifferentialObject

namespace HomologicalComplex

variable {β : Type*} [AddCommGroup β] (b : β)
variable (V : Type*) [Category* V] [HasZeroMorphisms V]

@[reassoc]
/--
theorem `d_eqToHom` / 定理 `d_eqToHom`

English:
theorem d_eqToHom
  given: (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z)
  proof: by cases h; simp

中文:
定理 d_eqToHom
  条件: (X : 同调复形 V (余mplexShape.up' b)) {x y z : β} (h : y = z)
  证明: by cases h; simp
-/
theorem d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.X h) = X.d x z := by cases h; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
/--
Definition of `dgoToHomologicalComplex` / `dgoToHomologicalComplex` 的定义

English:
definition dgoToHomologicalComplex
  signature: :
  body: { X := fun i => X.obj i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.objEqToHom (show i + (1 : Int) • b = j by simp [h]) else 0
      shape := fun i j w => by dsimp at w; convert! dif_neg w
      d_comp_d' := fun i j k hij hjk => by
        dsimp at hij hjk; subst hij hjk
        simp [objEqToHom_d_assoc] }
  map {X Y} f :=
    { f := f.f
      comm' := fun i j h => by
        dsimp at h ⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f _ := (congr_fun f.comm i).symm
        simp only [dite_true, Category.assoc, eqToHom_f', reassoc_of% this] }

中文:
定义 dgoToHomologicalComplex
  签名: :
  定义体: { X := fun i => X.obj i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.objEqToHom (show i + (1 : Int) • b = j by simp [h]) else 0
      shape := fun i j w => by dsimp at w; convert! dif_neg w
      d_comp_d' := fun i j k hij hjk => by
        dsimp at hij hjk; subst hij hjk
        simp [objEqToHom_d_assoc] }
  map {X Y} f :=
    { f := f.f
      comm' := fun i j h => by
        dsimp at h ⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f _ := (congr_fun f.comm i).symm
        simp only [dite_true, Category.assoc, eqToHom_f', reassoc_of% this] }

Depends on / 依赖: Category, Category.assoc, X.obj, X.objEqToHom, congr_fun, convert, d_comp_d, dif_neg, dite_true, eqToHom_f, f.comm, objEqToHom, objEqToHom_d_assoc, reassoc_of
-/
def dgoToHomologicalComplex :
    DifferentialObject Int (GradedObjectWithShift b V) ⥤
      HomologicalComplex V (ComplexShape.up' b) where
  obj X :=
    { X := fun i => X.obj i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.objEqToHom (show i + (1 : Int) • b = j by simp [h]) else 0
      shape := fun i j w => by dsimp at w; convert! dif_neg w
      d_comp_d' := fun i j k hij hjk => by
        dsimp at hij hjk; subst hij hjk
        simp [objEqToHom_d_assoc] }
  map {X Y} f :=
    { f := f.f
      comm' := fun i j h => by
        dsimp at h ⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f _ := (congr_fun f.comm i).symm
        simp only [dite_true, Category.assoc, eqToHom_f', reassoc_of% this] }

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
/--
Definition of `homologicalComplexToDGO` / `homologicalComplexToDGO` 的定义

English:
definition homologicalComplexToDGO
  signature: :
  body: { obj := fun i => X.X i
      d := fun i => X.d i _ }
  map {X Y} f := { f := f.f }

中文:
定义 homologicalComplexToDGO
  签名: :
  定义体: { obj := fun i => X.X i
      d := fun i => X.d i _ }
  map {X Y} f := { f := f.f }
-/
def homologicalComplexToDGO :
    HomologicalComplex V (ComplexShape.up' b) ⥤
      DifferentialObject Int (GradedObjectWithShift b V) where
  obj X :=
    { obj := fun i => X.X i
      d := fun i => X.d i _ }
  map {X Y} f := { f := f.f }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
/--
Definition of `dgoEquivHomologicalComplexUnitIso` / `dgoEquivHomologicalComplexUnitIso` 的定义

English:
definition dgoEquivHomologicalComplexUnitIso
  signature: :
  body: NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.obj i) }
      inv := { f := fun i => 𝟙 (X.obj i) } })

中文:
定义 dgoEquivHomologicalComplexUnitIso
  签名: :
  定义体: NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.obj i) }
      inv := { f := fun i => 𝟙 (X.obj i) } })

Depends on / 依赖: NatIso, NatIso.ofComponents, X.obj, ofComponents
-/
def dgoEquivHomologicalComplexUnitIso :
    𝟭 (DifferentialObject Int (GradedObjectWithShift b V)) ≅
      dgoToHomologicalComplex b V ⋙ homologicalComplexToDGO b V :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.obj i) }
      inv := { f := fun i => 𝟙 (X.obj i) } })

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
/--
Definition of `dgoEquivHomologicalComplexCounitIso` / `dgoEquivHomologicalComplexCounitIso` 的定义

English:
definition dgoEquivHomologicalComplexCounitIso
  signature: :
  body: NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.X i) }
      inv := { f := fun i => 𝟙 (X.X i) } })

中文:
定义 dgoEquivHomologicalComplexCounitIso
  签名: :
  定义体: NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.X i) }
      inv := { f := fun i => 𝟙 (X.X i) } })

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def dgoEquivHomologicalComplexCounitIso :
    homologicalComplexToDGO b V ⋙ dgoToHomologicalComplex b V ≅
      𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.X i) }
      inv := { f := fun i => 𝟙 (X.X i) } })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
/--
Definition of `dgoEquivHomologicalComplex` / `dgoEquivHomologicalComplex` 的定义

English:
definition dgoEquivHomologicalComplex
  signature: :
  body: dgoToHomologicalComplex b V
  inverse := homologicalComplexToDGO b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V

中文:
定义 dgoEquivHomologicalComplex
  签名: :
  定义体: dgoToHomologicalComplex b V
  inverse := homologicalComplexToDGO b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V

Depends on / 依赖: dgoToHomologicalComplex
-/
def dgoEquivHomologicalComplex :
    DifferentialObject Int (GradedObjectWithShift b V) ≌
      HomologicalComplex V (ComplexShape.up' b) where
  functor := dgoToHomologicalComplex b V
  inverse := homologicalComplexToDGO b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V

end HomologicalComplex
