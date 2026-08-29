/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Bicomplexes

Given a category `C` with zero morphisms and two complex shapes
`c₁ : ComplexShape I₁` and `c₂ : ComplexShape I₂`, we define
the type of bicomplexes `HomologicalComplex₂ C c₁ c₂` as an
abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`.
In particular, if `K : HomologicalComplex₂ C c₁ c₂`, then
for each `i₁ : I₁`, `K.X i₁` is a column of `K`.

In this file, we obtain the equivalence of categories
`HomologicalComplex₂.flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁`
which is obtained by exchanging the horizontal and vertical directions.

-/

@[expose] public section


open CategoryTheory Limits

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/--
Definition of `HomologicalComplex₂` / `HomologicalComplex₂` 的定义

English:
abbreviation HomologicalComplex₂
  body: HomologicalComplex (HomologicalComplex C c₂) c₁

中文:
缩写 HomologicalComplex₂
  定义体: HomologicalComplex (HomologicalComplex C c₂) c₁

Depends on / 依赖: HomologicalComplex
-/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

namespace HomologicalComplex₂

open HomologicalComplex

variable {C c₁ c₂}

/--
Definition of `toGradedObject` / `toGradedObject` 的定义

English:
definition toGradedObject
  signature: (K : HomologicalComplex₂ C c₁ c₂)
  body: fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

中文:
定义 toGradedObject
  签名: (K : HomologicalComplex₂ C c₁ c₂)
  定义体: fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂
-/
def toGradedObject (K : HomologicalComplex₂ C c₁ c₂) :
    GradedObject (I₁ × I₂) C :=
  fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

/--
Definition of `toGradedObjectMap` / `toGradedObjectMap` 的定义

English:
definition toGradedObjectMap
  signature: {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L)
  body: fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

@[simp]

中文:
定义 toGradedObjectMap
  签名: {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L)
  定义体: fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

@[simp]
-/
def toGradedObjectMap {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) :
    K.toGradedObject ⟶ L.toGradedObject :=
  fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

@[simp]
/--
lemma `toGradedObjectMap_apply` / 引理 `toGradedObjectMap_apply`

English:
lemma toGradedObjectMap_apply
  given: {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂)
  proof: rfl

中文:
引理 toGradedObjectMap_apply
  条件: {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂)
  证明: rfl
-/
lemma toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂ := rfl

variable (C c₁ c₂) in
/-- The functor which sends a bicomplex to its associated graded object. -/
@[simps]
/--
Definition of `toGradedObjectFunctor` / `toGradedObjectFunctor` 的定义

English:
definition toGradedObjectFunctor
  signature: : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  body: K.toGradedObject
  map φ := toGradedObjectMap φ

中文:
定义 toGradedObjectFunctor
  签名: : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  定义体: K.toGradedObject
  map φ := toGradedObjectMap φ

Depends on / 依赖: K.toGradedObject, toGradedObject
-/
def toGradedObjectFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  obj K := K.toGradedObject
  map φ := toGradedObjectMap φ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toGradedObjectFunctor C c₁ c₂).Faithful
  body: by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

中文:
实例 :
  签名: (toGradedObjectFunctor C c₁ c₂).Faithful
  定义体: by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

Depends on / 依赖: congr_fun
-/
instance : (toGradedObjectFunctor C c₁ c₂).Faithful where
  map_injective {_ _ φ₁ φ₂} h := by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

section OfGradedObject

variable (c₁ c₂)
variable (X : GradedObject (I₁ × I₂) C)
    (d₁ : forall (i₁ i₁' : I₁) (i₂ : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁', i₂⟩)
    (d₂ : forall (i₁ : I₁) (i₂ i₂' : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁, i₂'⟩)
    (shape₁ : forall (i₁ i₁' : I₁) (_ : ¬c₁.Rel i₁ i₁') (i₂ : I₂), d₁ i₁ i₁' i₂ = 0)
    (shape₂ : forall (i₁ : I₁) (i₂ i₂' : I₂) (_ : ¬c₂.Rel i₂ i₂'), d₂ i₁ i₂ i₂' = 0)
    (d₁_comp_d₁ : forall (i₁ i₁' i₁'' : I₁) (i₂ : I₂), d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0)
    (d₂_comp_d₂ : forall (i₁ : I₁) (i₂ i₂' i₂'' : I₂), d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0)
    (comm : forall (i₁ i₁' : I₁) (i₂ i₂' : I₂), d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' =
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂')

/-- Constructor for bicomplexes taking as inputs a graded object, horizontal differentials
and vertical differentials satisfying suitable relations. -/
@[simps]
/--
Definition of `ofGradedObject` / `ofGradedObject` 的定义

English:
definition ofGradedObject
  signature: :
  body: { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d

中文:
定义 ofGradedObject
  签名: :
  定义体: { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d

Depends on / 依赖: d_comp_d, intros
-/
def ofGradedObject :
    HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := by ext i₂; apply d₁_comp_d₁

@[simp]
/--
lemma `ofGradedObject_toGradedObject` / 引理 `ofGradedObject_toGradedObject`

English:
lemma ofGradedObject_toGradedObject
  proof: rfl

中文:
引理 ofGradedObject_toGradedObject
  证明: rfl
-/
lemma ofGradedObject_toGradedObject :
    (ofGradedObject c₁ c₂ X d₁ d₂ shape₁ shape₂ d₁_comp_d₁ d₂_comp_d₂ comm).toGradedObject = X :=
  rfl

end OfGradedObject

/-- Constructor for a morphism `K ⟶ L` in the category `HomologicalComplex₂ C c₁ c₂` which
takes as inputs a morphism `f : K.toGradedObject ⟶ L.toGradedObject` and
the compatibilities with both horizontal and vertical differentials. -/
@[simps!]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {K L : HomologicalComplex₂ C c₁ c₂}
  body: { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁

中文:
定义 homMk
  签名: {K L : HomologicalComplex₂ C c₁ c₂}
  定义体: { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁
-/
def homMk {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K.toGradedObject ⟶ L.toGradedObject)
    (comm₁ : forall i₁ i₁' i₂, c₁.Rel i₁ i₁' ->
      f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩)
    (comm₂ : forall i₁ i₂ i₂', c₂.Rel i₂ i₂' ->
      f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ f ⟨i₁, i₂'⟩) : K ⟶ L where
  f i₁ :=
    { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁

/--
lemma `shape_f` / 引理 `shape_f`

English:
lemma shape_f
  given: (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂)
  proof: by
  rw [K.shape _ _ h]; rw [zero_f]

@[reassoc (attr := simp)]

中文:
引理 shape_f
  条件: (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂)
  证明: by
  rw [K.shape _ _ h]; rw [zero_f]

@[reassoc (attr := simp)]

Depends on / 依赖: K.shape, zero_f
-/
lemma shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ = 0 := by
  rw [K.shape _ _ h]; rw [zero_f]

@[reassoc (attr := simp)]
/--
lemma `d_f_comp_d_f` / 引理 `d_f_comp_d_f`

English:
lemma d_f_comp_d_f
  statement: (K : HomologicalComplex₂ C c₁ c₂)
  proof: by
  rw [← comp_f]; rw [d_comp_d]; rw [zero_f]

@[reassoc]

中文:
引理 d_f_comp_d_f
  结论: (K : HomologicalComplex₂ C c₁ c₂)
  证明: by
  rw [← comp_f]; rw [d_comp_d]; rw [zero_f]

@[reassoc]

Depends on / 依赖: comp_f, d_comp_d, zero_f
-/
lemma d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f]; rw [d_comp_d]; rw [zero_f]

@[reassoc]
/--
lemma `d_comm` / 引理 `d_comm`

English:
lemma d_comm
  given: (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂)
  proof: by
  simp

@[reassoc (attr := simp)]

中文:
引理 d_comm
  条件: (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂)
  证明: by
  simp

@[reassoc (attr := simp)]
-/
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

@[reassoc (attr := simp)]
/--
lemma `comm_f` / 引理 `comm_f`

English:
lemma comm_f
  given: {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂)
  proof: congr_hom (f.comm i₁ i₁') i₂

中文:
引理 comm_f
  条件: {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂)
  证明: congr_hom (f.comm i₁ i₁') i₂

Depends on / 依赖: congr_hom, f.comm
-/
lemma comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂ :=
  congr_hom (f.comm i₁ i₁') i₂

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: (K : HomologicalComplex₂ C c₁ c₂)
  body: { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

@[simp]

中文:
定义 flip
  签名: (K : HomologicalComplex₂ C c₁ c₂)
  定义体: { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

@[simp]

Depends on / 依赖: K.shape_f, shape_f
-/
def flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
  X i :=
    { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

@[simp]
/--
lemma `flip_flip` / 引理 `flip_flip`

English:
lemma flip_flip
  given: (K : HomologicalComplex₂ C c₁ c₂)
  statement: K.flip.flip = K
  proof: rfl

中文:
引理 flip_flip
  条件: (K : HomologicalComplex₂ C c₁ c₂)
  结论: K.flip.flip = K
  证明: rfl
-/
lemma flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K := rfl

variable (C c₁ c₂)

set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
/--
Definition of `flipFunctor` / `flipFunctor` 的定义

English:
definition flipFunctor
  signature: :
  body: K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

中文:
定义 flipFunctor
  签名: :
  定义体: K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

Depends on / 依赖: K.flip
-/
def flipFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ where
  obj K := K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
/--
Definition of `flipEquivalenceUnitIso` / `flipEquivalenceUnitIso` 的定义

English:
definition flipEquivalenceUnitIso
  signature: :
  body: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

中文:
定义 flipEquivalenceUnitIso
  签名: :
  定义体: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, cat_disch, isoOfComponents, ofComponents
-/
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c₁ c₂ ⋙ flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
/--
Definition of `flipEquivalenceCounitIso` / `flipEquivalenceCounitIso` 的定义

English:
definition flipEquivalenceCounitIso
  signature: :
  body: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

中文:
定义 flipEquivalenceCounitIso
  签名: :
  定义体: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, cat_disch, isoOfComponents, ofComponents
-/
def flipEquivalenceCounitIso :
    flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (HomologicalComplex₂ C c₂ c₁) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
/--
Definition of `flipEquivalence` / `flipEquivalence` 的定义

English:
definition flipEquivalence
  signature: :
  body: flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

中文:
定义 flipEquivalence
  签名: :
  定义体: flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

Depends on / 依赖: flipFunctor
-/
def flipEquivalence :
    HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁ where
  functor := flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

variable (K : HomologicalComplex₂ C c₁ c₂)

/--
Definition of `XXIsoOfEq` / `XXIsoOfEq` 的定义

English:
definition XXIsoOfEq
  signature: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  body: eqToIso (by subst h₁ h₂; rfl)

@[simp]

中文:
定义 XXIsoOfEq
  签名: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  定义体: eqToIso (by subst h₁ h₂; rfl)

@[simp]

Depends on / 依赖: eqToIso
-/
def XXIsoOfEq {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂) :
    (K.X x₁).X x₂ ≅ (K.X y₁).X y₂ :=
  eqToIso (by subst h₁ h₂; rfl)

@[simp]
/--
lemma `XXIsoOfEq_rfl` / 引理 `XXIsoOfEq_rfl`

English:
lemma XXIsoOfEq_rfl
  given: (i₁ : I₁) (i₂ : I₂)
  proof: rfl

中文:
引理 XXIsoOfEq_rfl
  条件: (i₁ : I₁) (i₂ : I₂)
  证明: rfl
-/
lemma XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) :
    K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl : i₂ = i₂) = Iso.refl _ := rfl


end HomologicalComplex₂
