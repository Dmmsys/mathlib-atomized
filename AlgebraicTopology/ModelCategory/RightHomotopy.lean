/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Right homotopies in model categories

We introduce the types `PrepathObject.RightHomotopy` and `PathObject.RightHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)path object of `Y`.
Given two morphisms `f` and `g`, we introduce the relation `RightHomotopyRel f g`
asserting the existence of a path object `P` and
a right homotopy `P.RightHomotopy f g`, and we define the quotient
type `RightHomotopyClass X Y`. We show that if `Y` is a fibrant
object in a model category, then `RightHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

(This file dualizes the definitions in `Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean`.)

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace PrepathObject

variable {Y : C} (P : PrepathObject Y) {X : C}

/--
Definition of `RightHomotopy` / `RightHomotopy` 的定义

English:
structure RightHomotopy
  parameters: (f g : X ⟶ Y)
  axioms and operations (3):
    - h : X ⟶ P.P
    - h₀ : h ≫ P.p₀ = f  [default: by cat_disch]
    - h₁ : h ≫ P.p₁ = g  [default: by cat_disch]

中文:
结构 RightHomotopy
  参数: (f g : X ⟶ Y)
  公理与运算 (3 个):
    - h : X ⟶ P.P
    - h₀ : h ≫ P.p₀ = f  [默认: by cat_disch]
    - h₁ : h ≫ P.p₁ = g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure RightHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the source to the pre-path object -/
  h : X ⟶ P.P
  h₀ : h ≫ P.p₀ = f := by cat_disch
  h₁ : h ≫ P.p₁ = g := by cat_disch

namespace RightHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is right homotopic to itself relative to any pre-path object. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : X ⟶ Y)
  body: f ≫ P.ι

中文:
定义 refl
  签名: (f : X ⟶ Y)
  定义体: f ≫ P.ι
-/
def refl (f : X ⟶ Y) : P.RightHomotopy f f where
  h := f ≫ P.ι

variable {P}

set_option backward.defeqAttrib.useBackward true in
/-- If `f` and `g` are homotopic relative to a pre-path object `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  body: h.h

中文:
定义 symm
  签名: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  定义体: h.h
-/
def symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f where
  h := h.h

set_option backward.isDefEq.respectTransparency false in
/-- If `f₀` is homotopic to `f₁` relative to a pre-path object `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {f₀ f₁ f₂ : X ⟶ Y}
  body: pullback.lift h.h h'.h (by simp)

中文:
定义 trans
  签名: {f₀ f₁ f₂ : X ⟶ Y}
  定义体: pullback.lift h.h h'.h (by simp)

Depends on / 依赖: pullback, pullback.lift
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PrepathObject Y}
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ where
  h := pullback.lift h.h h'.h (by simp)

/-- Right homotopies are compatible with precomposition. -/
@[simps]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X)
  body: i ≫ h.h

中文:
定义 precomp
  签名: {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X)
  定义体: i ≫ h.h
-/
def precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) where
  h := i ≫ h.h

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fullSubcategoryEquiv` / `fullSubcategoryEquiv` 的定义

English:
definition fullSubcategoryEquiv
  signature: {P : ObjectProperty C} {X Y : P.FullSubcategory}
  body: { h := h.h.hom
      h₀ := by
        dsimp
        simp only [← h.h₀, ObjectProperty.FullSubcategory.comp_hom]
      h₁ := by
        dsimp
        simp only [← h.h₁, ObjectProperty.FullSubcategory.comp_hom] }
  invFun h :=
    { h := P.homMk h.h
      h₀ := by ext; exact h.h₀
      h₁ := by ext; exact h.h₁ }

中文:
定义 fullSubcategoryEquiv
  签名: {P : ObjectProperty C} {X Y : P.满子范畴}
  定义体: { h := h.h.hom
      h₀ := by
        dsimp
        simp only [← h.h₀, ObjectProperty.FullSubcategory.comp_hom]
      h₁ := by
        dsimp
        simp only [← h.h₁, ObjectProperty.FullSubcategory.comp_hom] }
  invFun h :=
    { h := P.homMk h.h
      h₀ := by ext; exact h.h₀
      h₁ := by ext; exact h.h₁ }

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory.comp_hom, P.homMk, comp_hom, h.h.hom, invFun
-/
noncomputable def fullSubcategoryEquiv {P : ObjectProperty C} {X Y : P.FullSubcategory}
    {Q : PrepathObject Y} {f g : X ⟶ Y} :
    Q.RightHomotopy f g ≃ (Q.map P.ι).RightHomotopy f.hom g.hom where
  toFun h :=
    { h := h.h.hom
      h₀ := by
        dsimp
        simp only [← h.h₀, ObjectProperty.FullSubcategory.comp_hom]
      h₁ := by
        dsimp
        simp only [← h.h₁, ObjectProperty.FullSubcategory.comp_hom] }
  invFun h :=
    { h := P.homMk h.h
      h₀ := by ext; exact h.h₀
      h₁ := by ext; exact h.h₁ }

end RightHomotopy

end PrepathObject

namespace PathObject

variable {X Y : C}

/--
Definition of `RightHomotopy` / `RightHomotopy` 的定义

English:
abbreviation RightHomotopy
  signature: [CategoryWithWeakEquivalences C] (P : PathObject Y) (f g : X ⟶ Y)
  body: P.toPrepathObject.RightHomotopy f g

中文:
缩写 RightHomotopy
  签名: [带弱等价范畴 C] (P : PathObject Y) (f g : X ⟶ Y)
  定义体: P.toPrepathObject.RightHomotopy f g

Depends on / 依赖: P.toPrepathObject.RightHomotopy, RightHomotopy, toPrepathObject
-/
abbrev RightHomotopy [CategoryWithWeakEquivalences C] (P : PathObject Y) (f g : X ⟶ Y) : Type v :=
  P.toPrepathObject.RightHomotopy f g

namespace RightHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : PathObject Y)

/--
Definition of `refl` / `refl` 的定义

English:
abbreviation refl
  signature: (f : X ⟶ Y)
  body: PrepathObject.RightHomotopy.refl _ f

中文:
缩写 refl
  签名: (f : X ⟶ Y)
  定义体: PrepathObject.RightHomotopy.refl _ f

Depends on / 依赖: PrepathObject, PrepathObject.RightHomotopy.refl, RightHomotopy
-/
abbrev refl (f : X ⟶ Y) : P.RightHomotopy f f := PrepathObject.RightHomotopy.refl _ f

variable {P} in
/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  signature: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  body: PrepathObject.RightHomotopy.symm h

中文:
缩写 symm
  签名: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  定义体: PrepathObject.RightHomotopy.symm h

Depends on / 依赖: PrepathObject, PrepathObject.RightHomotopy.symm, RightHomotopy
-/
abbrev symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f :=
  PrepathObject.RightHomotopy.symm h

variable {P} in
/--
Definition of `precomp` / `precomp` 的定义

English:
abbreviation precomp
  signature: {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X)
  body: PrepathObject.RightHomotopy.precomp h i

中文:
缩写 precomp
  签名: {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X)
  定义体: PrepathObject.RightHomotopy.precomp h i

Depends on / 依赖: PrepathObject, PrepathObject.RightHomotopy.precomp, RightHomotopy, precomp
-/
abbrev precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) :=
  PrepathObject.RightHomotopy.precomp h i

/--
lemma `weakEquivalence_iff` / 引理 `weakEquivalence_iff`

English:
lemma weakEquivalence_iff
  statement: [(weakEquivalences C).HasTwoOutOfThreeProperty]
  proof: by
  induction h
  grind [weakEquivalence_postcomp_iff]

中文:
引理 weakEquivalence_iff
  结论: [(weakEquivalences C).有TwoOutOfThreeProperty]
  证明: by
  induction h
  grind [weakEquivalence_postcomp_iff]

Depends on / 依赖: weakEquivalence_postcomp_iff
-/
lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  induction h
  grind [weakEquivalence_postcomp_iff]

end

section

variable [ModelCategory C] {P : PathObject Y}

/--
Definition of `trans` / `trans` 的定义

English:
abbreviation trans
  signature: [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
  body: PrepathObject.RightHomotopy.trans h h'

中文:
缩写 trans
  签名: [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
  定义体: PrepathObject.RightHomotopy.trans h h'

Depends on / 依赖: PrepathObject, PrepathObject.RightHomotopy.trans, RightHomotopy
-/
noncomputable abbrev trans [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PathObject Y} [P'.IsGood]
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ :=
  PrepathObject.RightHomotopy.trans h h'

/--
lemma `exists_good_pathObject` / 引理 `exists_good_pathObject`

English:
lemma exists_good_pathObject
  given: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  proof: by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact
   ⟨{ P := d.Z
      p₀ := d.p ≫ prod.fst
      p₁ := d.p ≫ prod.snd
      ι := P.ι ≫ d.i }, ⟨by
        rw [fibration_iff]
        convert! d.hp
        aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

中文:
引理 存在_good_pathObject
  条件: {f g : X ⟶ Y} (h : P.RightHomotopy f g)
  证明: by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact
   ⟨{ P := d.Z
      p₀ := d.p ≫ prod.fst
      p₁ := d.p ≫ prod.snd
      ι := P.ι ≫ d.i }, ⟨by
        rw [fibration_iff]
        convert! d.hp
        aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, convert, d.hp, factorizationData, fibration_iff, fibrations, prod.fst, prod.snd, trivialCofibrations
-/
lemma exists_good_pathObject {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    exists (P' : PathObject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g) := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact
   ⟨{ P := d.Z
      p₀ := d.p ≫ prod.fst
      p₁ := d.p ≫ prod.snd
      ι := P.ι ≫ d.i }, ⟨by
        rw [fibration_iff]
        convert! d.hp
        aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

/--
lemma `homotopy_extension` / 引理 `homotopy_extension`

English:
lemma homotopy_extension
  statement: {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B}
  proof: have sq : CommSq h.h i P.p₀ l₀ := { }
  ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

中文:
引理 homotopy_extension
  结论: {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B}
  证明: have sq : CommSq h.h i P.p₀ l₀ := { }
  ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

Depends on / 依赖: CommSq, P.RightHomotopy, RightHomotopy, cat_disch, sq.lift
-/
lemma homotopy_extension {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B}
    [IsFibrant B] [P.IsGood]
    (h : P.RightHomotopy f₀ f₁) (i : A ⟶ X) [Cofibration i]
    (l₀ : X ⟶ B) (hl₀ : i ≫ l₀ = f₀ := by cat_disch) :
    exists (l₁ : X ⟶ B) (h' : P.RightHomotopy l₀ l₁), i ≫ h'.h = h.h :=
  have sq : CommSq h.h i P.p₀ l₀ := { }
  ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

end

end RightHomotopy

end PathObject

/--
Definition of `RightHomotopyRel` / `RightHomotopyRel` 的定义

English:
definition RightHomotopyRel
  signature: [CategoryWithWeakEquivalences C]
  body: fun _ Y f g => exists (P : PathObject Y), Nonempty (P.RightHomotopy f g)

中文:
定义 RightHomotopyRel
  签名: [带弱等价范畴 C]
  定义体: fun _ Y f g => exists (P : PathObject Y), Nonempty (P.RightHomotopy f g)

Depends on / 依赖: Nonempty, P.RightHomotopy, PathObject, RightHomotopy
-/
def RightHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun _ Y f g => exists (P : PathObject Y), Nonempty (P.RightHomotopy f g)

/--
lemma `PathObject.RightHomotopy.rightHomotopyRel` / 引理 `PathObject.RightHomotopy.rightHomotopyRel`

English:
lemma PathObject.RightHomotopy.rightHomotopyRel
  statement: [CategoryWithWeakEquivalences C]
  proof: ⟨_, ⟨h⟩⟩

中文:
引理 PathObject.RightHomotopy.rightHomotopyRel
  结论: [带弱等价范畴 C]
  证明: ⟨_, ⟨h⟩⟩
-/
lemma PathObject.RightHomotopy.rightHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : PathObject Y} (h : P.RightHomotopy f g) :
    RightHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace RightHomotopyRel

variable (C) in
/--
lemma `factorsThroughLocalization` / 引理 `factorsThroughLocalization`

English:
lemma factorsThroughLocalization
  given: [CategoryWithWeakEquivalences C]
  proof: by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_epi (L.map P.ι), ← L.map_comp]

中文:
引理 factorsThroughLocalization
  条件: [带弱等价范畴 C]
  证明: by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_epi (L.map P.ι), ← L.map_comp]

Depends on / 依赖: L.map, L.map_comp, Localization, Localization.inverts, areEqualizedByLocalization_iff, cancel_epi, infer_instance, inverts, map_comp, weakEquivalence_iff, weakEquivalences
-/
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    RightHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_epi (L.map P.ι), ← L.map_comp]

variable {X Y : C}

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: [ModelCategory C] (f : X ⟶ Y)
  statement: RightHomotopyRel f f
  proof: ⟨Classical.arbitrary _, ⟨PathObject.RightHomotopy.refl _ _⟩⟩

中文:
引理 refl
  条件: [模型范畴 C] (f : X ⟶ Y)
  结论: RightHomotopyRel f f
  证明: ⟨Classical.arbitrary _, ⟨PathObject.RightHomotopy.refl _ _⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, PathObject, PathObject.RightHomotopy.refl, RightHomotopy, arbitrary
-/
lemma refl [ModelCategory C] (f : X ⟶ Y) : RightHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨PathObject.RightHomotopy.refl _ _⟩⟩

/--
lemma `precomp` / 引理 `precomp`

English:
lemma precomp
  statement: [CategoryWithWeakEquivalences C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel

中文:
引理 precomp
  结论: [带弱等价范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel

Depends on / 依赖: h.precomp, precomp, rightHomotopyRel
-/
lemma precomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) {Z : C} (i : Z ⟶ X) :
    RightHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel

/--
lemma `exists_good_pathObject` / 引理 `exists_good_pathObject`

English:
lemma exists_good_pathObject
  given: [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g)
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_pathObject

中文:
引理 存在_good_pathObject
  条件: [模型范畴 C] {f g : X ⟶ Y} (h : RightHomotopyRel f g)
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_pathObject

Depends on / 依赖: exists_good_pathObject, h.exists_good_pathObject
-/
lemma exists_good_pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    exists (P : PathObject Y), P.IsGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_pathObject

/--
lemma `exists_very_good_pathObject` / 引理 `exists_very_good_pathObject`

English:
lemma exists_very_good_pathObject
  statement: [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X]
  proof: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
  let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by cat_disch]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩⟩

中文:
引理 存在_very_good_pathObject
  结论: [模型范畴 C] {f g : X ⟶ Y} [IsCofibrant X]
  证明: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
  let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by cat_disch]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩⟩

Depends on / 依赖: CommSq, Fibration, MorphismProperty, MorphismProperty.factorizationData, PathObject, cat_disch, cofibrations, exists_good_pathObject, fac.Z, fac.fac, fac.i, fac.p, factorizationData, h.exists_good_pathObject, infer_instance, initial, initial.to, sq.lift, trivialFibrations, weakEquivalence_of_postcomp_of_fac
-/
lemma exists_very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X]
    (h : RightHomotopyRel f g) :
    exists (P : PathObject Y), P.IsVeryGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
  let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by cat_disch]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: [CategoryWithWeakEquivalences C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel

中文:
引理 symm
  结论: [带弱等价范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel

Depends on / 依赖: h.symm.rightHomotopyRel, rightHomotopyRel
-/
lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) : RightHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: [ModelCategory C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_pathObject
  exact (h.trans h').rightHomotopyRel

中文:
引理 trans
  结论: [模型范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_pathObject
  exact (h.trans h').rightHomotopyRel

Depends on / 依赖: exists_good_pathObject, h.trans, rightHomotopyRel
-/
lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotopyRel f₀ f₁)
    (h' : RightHomotopyRel f₁ f₂) : RightHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_pathObject
  exact (h.trans h').rightHomotopyRel

/--
lemma `equivalence` / 引理 `equivalence`

English:
lemma equivalence
  given: [ModelCategory C] (X Y : C) [IsFibrant Y]
  proof: .refl
  symm h := h.symm
  trans h h' := h.trans h'

中文:
引理 equivalence
  条件: [模型范畴 C] (X Y : C) [IsFibrant Y]
  证明: .refl
  symm h := h.symm
  trans h h' := h.trans h'
-/
lemma equivalence [ModelCategory C] (X Y : C) [IsFibrant Y] :
    _root_.Equivalence (RightHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `postcomp` / 引理 `postcomp`

English:
lemma postcomp
  statement: [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
  proof: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := { }
  exact ⟨Q,
   ⟨{ h := h.h ≫ sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        simp only [Category.assoc, prod.lift_fst, Q.p_fst] at this
        simp [this]
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        simp only [Category.assoc, prod.lift_snd, Q.p_snd] at this
        simp [this]
    }⟩⟩

中文:
引理 postcomp
  结论: [模型范畴 C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
  证明: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := { }
  exact ⟨Q,
   ⟨{ h := h.h ≫ sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        simp only [Category.assoc, prod.lift_fst, Q.p_fst] at this
        simp [this]
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        simp only [Category.assoc, prod.lift_snd, Q.p_snd] at this
        simp [this]
    }⟩⟩

Depends on / 依赖: Category, Category.assoc, CommSq, PathObject, PathObject.exists_very_good, Q.p_fst, Q.p_snd, exists_very_good, exists_very_good_pathObject, fac_right, h.exists_very_good_pathObject, lift_fst, lift_snd, p_fst, p_snd, prod.fst, prod.lift, prod.lift_fst, prod.lift_snd, prod.snd
-/
lemma postcomp [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
    {Z : C} (p : Y ⟶ Z) : RightHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := { }
  exact ⟨Q,
   ⟨{ h := h.h ≫ sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        simp only [Category.assoc, prod.lift_fst, Q.p_fst] at this
        simp [this]
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        simp only [Category.assoc, prod.lift_snd, Q.p_snd] at this
        simp [this]
    }⟩⟩

end RightHomotopyRel

variable (X Y Z : C)

/--
Definition of `RightHomotopyClass` / `RightHomotopyClass` 的定义

English:
definition RightHomotopyClass
  signature: [CategoryWithWeakEquivalences C]
  body: _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

中文:
定义 RightHomotopyClass
  签名: [带弱等价范畴 C]
  定义体: _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

Depends on / 依赖: RightHomotopyRel, _root_, _root_.Quot
-/
def RightHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/--
Definition of `RightHomotopyClass.mk` / `RightHomotopyClass.mk` 的定义

English:
definition RightHomotopyClass.mk
  signature: [CategoryWithWeakEquivalences C]
  body: Quot.mk _

中文:
定义 RightHomotopyClass.mk
  签名: [带弱等价范畴 C]
  定义体: Quot.mk _

Depends on / 依赖: Quot.mk
-/
def RightHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) -> RightHomotopyClass X Y := Quot.mk _

/--
lemma `RightHomotopyClass.mk_surjective` / 引理 `RightHomotopyClass.mk_surjective`

English:
lemma RightHomotopyClass.mk_surjective
  given: [CategoryWithWeakEquivalences C]
  proof: Quot.mk_surjective

中文:
引理 RightHomotopyClass.mk_surjective
  条件: [带弱等价范畴 C]
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
lemma RightHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) -> _) :=
  Quot.mk_surjective

namespace RightHomotopyClass

/--
lemma `sound` / 引理 `sound`

English:
lemma sound
  given: [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel f g)
  proof: Quot.sound h

中文:
引理 sound
  条件: [带弱等价范畴 C] {f g : X ⟶ Y} (h : RightHomotopyRel f g)
  证明: Quot.sound h

Depends on / 依赖: Quot.sound
-/
lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: [CategoryWithWeakEquivalences C]
  body: fun g f => Quot.lift (fun g => mk (f ≫ g)) (fun _ _ h => sound (h.precomp f)) g

@[simp]

中文:
定义 precomp
  签名: [带弱等价范畴 C]
  定义体: fun g f => Quot.lift (fun g => mk (f ≫ g)) (fun _ _ h => sound (h.precomp f)) g

@[simp]

Depends on / 依赖: Quot.lift, h.precomp, precomp
-/
def precomp [CategoryWithWeakEquivalences C] :
    RightHomotopyClass Y Z -> (X ⟶ Y) -> RightHomotopyClass X Z :=
  fun g f => Quot.lift (fun g => mk (f ≫ g)) (fun _ _ h => sound (h.precomp f)) g

@[simp]
/--
lemma `precomp_mk` / 引理 `precomp_mk`

English:
lemma precomp_mk
  given: [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 precomp_mk
  条件: [带弱等价范畴 C] (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma precomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk g).precomp f = mk (f ≫ g) := rfl

/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  given: [ModelCategory C] [IsFibrant Y] (f g : X ⟶ Y)
  proof: by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

中文:
引理 mk_eq_mk_iff
  条件: [模型范畴 C] [IsFibrant Y] (f g : X ⟶ Y)
  证明: by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

Depends on / 依赖: Quot.eq, RightHomotopyRel, RightHomotopyRel.equivalence, equivalence, eqvGen_iff
-/
lemma mk_eq_mk_iff [ModelCategory C] [IsFibrant Y] (f g : X ⟶ Y) :
    mk f = mk g ↔ RightHomotopyRel f g := by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end RightHomotopyClass

set_option backward.defeqAttrib.useBackward true in
/-- The left homotopy in the opposite category that is deduced from a right homotopy. -/
@[simps]
/--
Definition of `PrepathObject.RightHomotopy.op` / `PrepathObject.RightHomotopy.op` 的定义

English:
definition PrepathObject.RightHomotopy.op
  body: h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

中文:
定义 PrepathObject.RightHomotopy.op
  定义体: h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)
-/
protected def PrepathObject.RightHomotopy.op
    {X Y : C} {P : PrepathObject Y} {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    P.op.LeftHomotopy f.op g.op where
  h := h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The left homotopy that is deduced from a right homotopy in the opposite category. -/
@[simps]
/--
Definition of `PrepathObject.RightHomotopy.unop` / `PrepathObject.RightHomotopy.unop` 的定义

English:
definition PrepathObject.RightHomotopy.unop
  body: h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

中文:
定义 PrepathObject.RightHomotopy.unop
  定义体: h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)
-/
protected def PrepathObject.RightHomotopy.unop
    {X Y : Cᵒᵖ} {P : PrepathObject Y} {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    P.unop.LeftHomotopy f.unop g.unop where
  h := h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The right homotopy in the opposite category that is deduced from a left homotopy. -/
@[simps]
/--
Definition of `Precylinder.LeftHomotopy.op` / `Precylinder.LeftHomotopy.op` 的定义

English:
definition Precylinder.LeftHomotopy.op
  body: h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

中文:
定义 Precylinder.LeftHomotopy.op
  定义体: h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)
-/
protected def Precylinder.LeftHomotopy.op
    {X Y : C} {P : Precylinder X} {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    P.op.RightHomotopy f.op g.op where
  h := h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The right homotopy that is deduced from a left homotopy in the opposite category. -/
@[simps]
/--
Definition of `Precylinder.LeftHomotopy.unop` / `Precylinder.LeftHomotopy.unop` 的定义

English:
definition Precylinder.LeftHomotopy.unop
  body: h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

中文:
定义 Precylinder.LeftHomotopy.unop
  定义体: h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)
-/
protected def Precylinder.LeftHomotopy.unop
    {X Y : Cᵒᵖ} {P : Precylinder X} {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    P.unop.RightHomotopy f.unop g.unop where
  h := h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

end HomotopicalAlgebra
