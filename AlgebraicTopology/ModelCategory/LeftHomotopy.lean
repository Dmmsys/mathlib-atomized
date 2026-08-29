/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Left homotopies in model categories

We introduce the types `Precylinder.LeftHomotopy` and `Cylinder.LeftHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)cylinder of `X`.
Given two morphisms `f` and `g`, we introduce the relation `LeftHomotopyRel f g`
asserting the existence of a cylinder object `P` and
a left homotopy `P.LeftHomotopy f g`, and we define the quotient
type `LeftHomotopyClass X Y`. We show that if `X` is a cofibrant
object in a model category, then `LeftHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace Precylinder

variable {X : C} (P : Precylinder X) {Y : C}

/--
Definition of `LeftHomotopy` / `LeftHomotopy` 的定义

English:
structure LeftHomotopy
  parameters: (f g : X ⟶ Y)
  axioms and operations (3):
    - h : P.I ⟶ Y
    - h₀ : P.i₀ ≫ h = f  [default: by cat_disch]
    - h₁ : P.i₁ ≫ h = g  [default: by cat_disch]

中文:
结构 LeftHomotopy
  参数: (f g : X ⟶ Y)
  公理与运算 (3 个):
    - h : P.I ⟶ Y
    - h₀ : P.i₀ ≫ h = f  [默认: by cat_disch]
    - h₁ : P.i₁ ≫ h = g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LeftHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the (pre)cylinder object to the target -/
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by cat_disch
  h₁ : P.i₁ ≫ h = g := by cat_disch

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is left homotopic to itself relative to any precylinder. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : X ⟶ Y)
  body: P.π ≫ f

中文:
定义 refl
  签名: (f : X ⟶ Y)
  定义体: P.π ≫ f
-/
def refl (f : X ⟶ Y) : P.LeftHomotopy f f where
  h := P.π ≫ f

variable {P}

set_option backward.defeqAttrib.useBackward true in
/-- If `f` and `g` are homotopic relative to a precylinder `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  body: h.h

中文:
定义 symm
  签名: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  定义体: h.h
-/
def symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f where
  h := h.h

set_option backward.isDefEq.respectTransparency false in
/-- If `f₀` is homotopic to `f₁` relative to a precylinder `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {f₀ f₁ f₂ : X ⟶ Y}
  body: pushout.desc h.h h'.h (by simp)

中文:
定义 trans
  签名: {f₀ f₁ f₂ : X ⟶ Y}
  定义体: pushout.desc h.h h'.h (by simp)

Depends on / 依赖: pushout, pushout.desc
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Precylinder X}
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ where
  h := pushout.desc h.h h'.h (by simp)

/-- Left homotopies are compatible with postcomposition. -/
@[simps]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z)
  body: h.h ≫ p

中文:
定义 postcomp
  签名: {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z)
  定义体: h.h ≫ p
-/
def postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) where
  h := h.h ≫ p

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
    {Q : Precylinder X} {f g : X ⟶ Y} :
    Q.LeftHomotopy f g ≃ (Q.map P.ι).LeftHomotopy f.hom g.hom where
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

end LeftHomotopy

end Precylinder

namespace Cylinder

variable {X Y : C}

/--
Definition of `LeftHomotopy` / `LeftHomotopy` 的定义

English:
abbreviation LeftHomotopy
  signature: [CategoryWithWeakEquivalences C] (P : Cylinder X) (f g : X ⟶ Y)
  body: P.toPrecylinder.LeftHomotopy f g

中文:
缩写 LeftHomotopy
  签名: [带弱等价范畴 C] (P : 柱 X) (f g : X ⟶ Y)
  定义体: P.toPrecylinder.LeftHomotopy f g

Depends on / 依赖: LeftHomotopy, P.toPrecylinder.LeftHomotopy, toPrecylinder
-/
abbrev LeftHomotopy [CategoryWithWeakEquivalences C] (P : Cylinder X) (f g : X ⟶ Y) : Type v :=
  P.toPrecylinder.LeftHomotopy f g

namespace LeftHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : Cylinder X)

/--
Definition of `refl` / `refl` 的定义

English:
abbreviation refl
  signature: (f : X ⟶ Y)
  body: Precylinder.LeftHomotopy.refl _ f

中文:
缩写 refl
  签名: (f : X ⟶ Y)
  定义体: Precylinder.LeftHomotopy.refl _ f

Depends on / 依赖: LeftHomotopy, Precylinder, Precylinder.LeftHomotopy.refl
-/
abbrev refl (f : X ⟶ Y) : P.LeftHomotopy f f := Precylinder.LeftHomotopy.refl _ f

variable {P} in
/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  signature: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  body: Precylinder.LeftHomotopy.symm h

中文:
缩写 symm
  签名: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  定义体: Precylinder.LeftHomotopy.symm h

Depends on / 依赖: LeftHomotopy, Precylinder, Precylinder.LeftHomotopy.symm
-/
abbrev symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f :=
  Precylinder.LeftHomotopy.symm h

variable {P} in
/--
Definition of `postcomp` / `postcomp` 的定义

English:
abbreviation postcomp
  signature: {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z)
  body: Precylinder.LeftHomotopy.postcomp h p

中文:
缩写 postcomp
  签名: {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z)
  定义体: Precylinder.LeftHomotopy.postcomp h p

Depends on / 依赖: LeftHomotopy, Precylinder, Precylinder.LeftHomotopy.postcomp, postcomp
-/
abbrev postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) :=
  Precylinder.LeftHomotopy.postcomp h p

/--
lemma `weakEquivalence_iff` / 引理 `weakEquivalence_iff`

English:
lemma weakEquivalence_iff
  statement: [(weakEquivalences C).HasTwoOutOfThreeProperty]
  proof: by
  induction h
  grind [weakEquivalence_precomp_iff]

中文:
引理 weakEquivalence_iff
  结论: [(weakEquivalences C).有TwoOutOfThreeProperty]
  证明: by
  induction h
  grind [weakEquivalence_precomp_iff]

Depends on / 依赖: weakEquivalence_precomp_iff
-/
lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  induction h
  grind [weakEquivalence_precomp_iff]

end

section

variable [ModelCategory C] {P : Cylinder X}

/--
Definition of `trans` / `trans` 的定义

English:
abbreviation trans
  signature: [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
  body: Precylinder.LeftHomotopy.trans h h'

中文:
缩写 trans
  签名: [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
  定义体: Precylinder.LeftHomotopy.trans h h'

Depends on / 依赖: LeftHomotopy, Precylinder, Precylinder.LeftHomotopy.trans
-/
noncomputable abbrev trans [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Cylinder X} [P'.IsGood]
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ :=
  Precylinder.LeftHomotopy.trans h h'

/--
lemma `exists_good_cylinder` / 引理 `exists_good_cylinder`

English:
lemma exists_good_cylinder
  given: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  proof: by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact
   ⟨{ I := d.Z
      i₀ := coprod.inl ≫ d.i
      i₁ := coprod.inr ≫ d.i
      π := d.p ≫ P.π }, ⟨by
        rw [cofibration_iff]
        convert! d.hi
        aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

中文:
引理 存在_good_cylinder
  条件: {f g : X ⟶ Y} (h : P.LeftHomotopy f g)
  证明: by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact
   ⟨{ I := d.Z
      i₀ := coprod.inl ≫ d.i
      i₁ := coprod.inr ≫ d.i
      π := d.p ≫ P.π }, ⟨by
        rw [cofibration_iff]
        convert! d.hi
        aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, cofibration_iff, cofibrations, convert, coprod, coprod.inl, coprod.inr, d.hi, factorizationData, trivialFibrations
-/
lemma exists_good_cylinder {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    exists (P' : Cylinder X), P'.IsGood ∧ Nonempty (P'.LeftHomotopy f g) := by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact
   ⟨{ I := d.Z
      i₀ := coprod.inl ≫ d.i
      i₁ := coprod.inr ≫ d.i
      π := d.p ≫ P.π }, ⟨by
        rw [cofibration_iff]
        convert! d.hi
        aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

/--
lemma `covering_homotopy` / 引理 `covering_homotopy`

English:
lemma covering_homotopy
  statement: {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B}
  proof: have sq : CommSq l₀ P.i₀ p h.h := { }
  ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

中文:
引理 covering_homotopy
  结论: {A E B : C} {P : 柱 A} {f₀ f₁ : A ⟶ B}
  证明: have sq : CommSq l₀ P.i₀ p h.h := { }
  ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

Depends on / 依赖: CommSq, LeftHomotopy, P.LeftHomotopy, cat_disch, sq.lift
-/
lemma covering_homotopy {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B}
    [IsCofibrant A] [P.IsGood]
    (h : P.LeftHomotopy f₀ f₁) (p : E ⟶ B) [Fibration p]
    (l₀ : A ⟶ E) (hl₀ : l₀ ≫ p = f₀ := by cat_disch) :
    exists (l₁ : A ⟶ E) (h' : P.LeftHomotopy l₀ l₁), h'.h ≫ p = h.h :=
  have sq : CommSq l₀ P.i₀ p h.h := { }
  ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

end

end LeftHomotopy

end Cylinder

/--
Definition of `LeftHomotopyRel` / `LeftHomotopyRel` 的定义

English:
definition LeftHomotopyRel
  signature: [CategoryWithWeakEquivalences C]
  body: fun X _ f g => exists (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

中文:
定义 LeftHomotopyRel
  签名: [带弱等价范畴 C]
  定义体: fun X _ f g => exists (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

Depends on / 依赖: Cylinder, LeftHomotopy, Nonempty, P.LeftHomotopy
-/
def LeftHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun X _ f g => exists (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

/--
lemma `Cylinder.LeftHomotopy.leftHomotopyRel` / 引理 `Cylinder.LeftHomotopy.leftHomotopyRel`

English:
lemma Cylinder.LeftHomotopy.leftHomotopyRel
  statement: [CategoryWithWeakEquivalences C]
  proof: ⟨_, ⟨h⟩⟩

中文:
引理 柱.LeftHomotopy.leftHomotopyRel
  结论: [带弱等价范畴 C]
  证明: ⟨_, ⟨h⟩⟩
-/
lemma Cylinder.LeftHomotopy.leftHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : Cylinder X} (h : P.LeftHomotopy f g) :
    LeftHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace LeftHomotopyRel

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
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

中文:
引理 factorsThroughLocalization
  条件: [带弱等价范畴 C]
  证明: by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

Depends on / 依赖: L.map, L.map_comp, Localization, Localization.inverts, areEqualizedByLocalization_iff, cancel_mono, infer_instance, inverts, map_comp, weakEquivalence_iff, weakEquivalences
-/
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    LeftHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

variable {X Y : C}

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: [ModelCategory C] (f : X ⟶ Y)
  statement: LeftHomotopyRel f f
  proof: ⟨Classical.arbitrary _, ⟨Cylinder.LeftHomotopy.refl _ _⟩⟩

中文:
引理 refl
  条件: [模型范畴 C] (f : X ⟶ Y)
  结论: LeftHomotopyRel f f
  证明: ⟨Classical.arbitrary _, ⟨Cylinder.LeftHomotopy.refl _ _⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, Cylinder, Cylinder.LeftHomotopy.refl, LeftHomotopy, arbitrary
-/
lemma refl [ModelCategory C] (f : X ⟶ Y) : LeftHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨Cylinder.LeftHomotopy.refl _ _⟩⟩

/--
lemma `postcomp` / 引理 `postcomp`

English:
lemma postcomp
  statement: [CategoryWithWeakEquivalences C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel

中文:
引理 postcomp
  结论: [带弱等价范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel

Depends on / 依赖: h.postcomp, leftHomotopyRel, postcomp
-/
lemma postcomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) :
    LeftHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel

/--
lemma `exists_good_cylinder` / 引理 `exists_good_cylinder`

English:
lemma exists_good_cylinder
  given: [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g)
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_cylinder

中文:
引理 存在_good_cylinder
  条件: [模型范畴 C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g)
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_cylinder

Depends on / 依赖: exists_good_cylinder, h.exists_good_cylinder
-/
lemma exists_good_cylinder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    exists (P : Cylinder X), P.IsGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_cylinder

/--
lemma `exists_very_good_cylinder` / 引理 `exists_very_good_cylinder`

English:
lemma exists_very_good_cylinder
  statement: [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y]
  proof: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
  let fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by cat_disch]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

中文:
引理 存在_very_good_cylinder
  结论: [模型范畴 C] {f g : X ⟶ Y} [IsFibrant Y]
  证明: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
  let fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by cat_disch]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

Depends on / 依赖: Cofibration, CommSq, Cylinder, MorphismProperty, MorphismProperty.factorizationData, cat_disch, exists_good_cylinder, fac.Z, fac.fac, fac.i, fac.p, factorizationData, fibrations, h.exists_good_cylinder, infer_instance, sq.lift, terminal, terminal.from, trivialCofibrations, weakEquivalence_of_precomp_of_fac
-/
lemma exists_very_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y]
    (h : LeftHomotopyRel f g) :
    exists (P : Cylinder X), P.IsVeryGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
  let fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by cat_disch]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: [CategoryWithWeakEquivalences C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel

中文:
引理 symm
  结论: [带弱等价范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel

Depends on / 依赖: h.symm.leftHomotopyRel, leftHomotopyRel
-/
lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: [ModelCategory C]
  proof: by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_cylinder
  exact (h.trans h').leftHomotopyRel

中文:
引理 trans
  结论: [模型范畴 C]
  证明: by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_cylinder
  exact (h.trans h').leftHomotopyRel

Depends on / 依赖: exists_good_cylinder, h.trans, leftHomotopyRel
-/
lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomotopyRel f₀ f₁)
    (h' : LeftHomotopyRel f₁ f₂) : LeftHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_cylinder
  exact (h.trans h').leftHomotopyRel

/--
lemma `equivalence` / 引理 `equivalence`

English:
lemma equivalence
  given: [ModelCategory C] (X Y : C) [IsCofibrant X]
  proof: .refl
  symm h := h.symm
  trans h h' := h.trans h'

中文:
引理 equivalence
  条件: [模型范畴 C] (X Y : C) [IsCofibrant X]
  证明: .refl
  symm h := h.symm
  trans h h' := h.trans h'
-/
lemma equivalence [ModelCategory C] (X Y : C) [IsCofibrant X] :
    _root_.Equivalence (LeftHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `precomp` / 引理 `precomp`

English:
lemma precomp
  statement: [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
  proof: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q,
   ⟨{ h := sq.lift ≫ h.h
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        simp only [Q.inl_i_assoc, coprod.inl_desc] at this
        simp [reassoc_of% this]
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        simp only [Q.inr_i_assoc, coprod.inr_desc] at this
        simp [reassoc_of% this] }⟩⟩

中文:
引理 precomp
  结论: [模型范畴 C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
  证明: by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q,
   ⟨{ h := sq.lift ≫ h.h
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        simp only [Q.inl_i_assoc, coprod.inl_desc] at this
        simp [reassoc_of% this]
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        simp only [Q.inr_i_assoc, coprod.inr_desc] at this
        simp [reassoc_of% this] }⟩⟩

Depends on / 依赖: CommSq, Cylinder, Cylinder.exists_very_good, Q.inl_i_assoc, Q.inr_i_assoc, aesop_cat, coprod, coprod.desc, coprod.inl, coprod.inl_desc, coprod.inr, coprod.inr_desc, exists_very_good, exists_very_good_cylinder, fac_left, h.exists_very_good_cylinder, inl_desc, inl_i_assoc, inr_desc, inr_i_assoc
-/
lemma precomp [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
    {Z : C} (i : Z ⟶ X) : LeftHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q,
   ⟨{ h := sq.lift ≫ h.h
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        simp only [Q.inl_i_assoc, coprod.inl_desc] at this
        simp [reassoc_of% this]
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        simp only [Q.inr_i_assoc, coprod.inr_desc] at this
        simp [reassoc_of% this] }⟩⟩

end LeftHomotopyRel

variable (X Y Z : C)

/--
Definition of `LeftHomotopyClass` / `LeftHomotopyClass` 的定义

English:
definition LeftHomotopyClass
  signature: [CategoryWithWeakEquivalences C]
  body: _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

中文:
定义 LeftHomotopyClass
  签名: [带弱等价范畴 C]
  定义体: _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

Depends on / 依赖: LeftHomotopyRel, _root_, _root_.Quot
-/
def LeftHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/--
Definition of `LeftHomotopyClass.mk` / `LeftHomotopyClass.mk` 的定义

English:
definition LeftHomotopyClass.mk
  signature: [CategoryWithWeakEquivalences C]
  body: Quot.mk _

中文:
定义 LeftHomotopyClass.mk
  签名: [带弱等价范畴 C]
  定义体: Quot.mk _

Depends on / 依赖: Quot.mk
-/
def LeftHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) -> LeftHomotopyClass X Y := Quot.mk _

/--
lemma `LeftHomotopyClass.mk_surjective` / 引理 `LeftHomotopyClass.mk_surjective`

English:
lemma LeftHomotopyClass.mk_surjective
  given: [CategoryWithWeakEquivalences C]
  proof: Quot.mk_surjective

中文:
引理 LeftHomotopyClass.mk_surjective
  条件: [带弱等价范畴 C]
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
lemma LeftHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) -> _) :=
  Quot.mk_surjective

namespace LeftHomotopyClass

/--
lemma `sound` / 引理 `sound`

English:
lemma sound
  given: [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g)
  proof: Quot.sound h

中文:
引理 sound
  条件: [带弱等价范畴 C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g)
  证明: Quot.sound h

Depends on / 依赖: Quot.sound
-/
lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: [CategoryWithWeakEquivalences C]
  body: fun f g => Quot.lift (fun f => mk (f ≫ g)) (fun _ _ h => sound (h.postcomp g)) f

@[simp]

中文:
定义 postcomp
  签名: [带弱等价范畴 C]
  定义体: fun f g => Quot.lift (fun f => mk (f ≫ g)) (fun _ _ h => sound (h.postcomp g)) f

@[simp]

Depends on / 依赖: Quot.lift, h.postcomp, postcomp
-/
def postcomp [CategoryWithWeakEquivalences C] :
    LeftHomotopyClass X Y -> (Y ⟶ Z) -> LeftHomotopyClass X Z :=
  fun f g => Quot.lift (fun f => mk (f ≫ g)) (fun _ _ h => sound (h.postcomp g)) f

@[simp]
/--
lemma `postcomp_mk` / 引理 `postcomp_mk`

English:
lemma postcomp_mk
  given: [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 postcomp_mk
  条件: [带弱等价范畴 C] (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma postcomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).postcomp g = mk (f ≫ g) := rfl

/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  given: [ModelCategory C] [IsCofibrant X] (f g : X ⟶ Y)
  proof: by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

中文:
引理 mk_eq_mk_iff
  条件: [模型范畴 C] [IsCofibrant X] (f g : X ⟶ Y)
  证明: by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

Depends on / 依赖: LeftHomotopyRel, LeftHomotopyRel.equivalence, Quot.eq, equivalence, eqvGen_iff
-/
lemma mk_eq_mk_iff [ModelCategory C] [IsCofibrant X] (f g : X ⟶ Y) :
    mk f = mk g ↔ LeftHomotopyRel f g := by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end LeftHomotopyClass

end HomotopicalAlgebra
