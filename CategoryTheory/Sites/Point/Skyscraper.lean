/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Skyscraper sheaves

Let `Φ` be a point of a site `(C, J)`. In this file, we construct the
skyscraper sheaf functor `skyscraperSheafFunctor : A ⥤ Sheaf J A` and
show that it is a right adjoint to `Φ.sheafFiber : Sheaf J A ⥤ A`.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A]

/-- Given a point `Φ` on a site `(C, J)`, this is the skyscraper presheaf functor
`A ⥤ Cᵒᵖ ⥤ A`. -/
@[simps!]
/--
Definition of `skyscraperPresheafFunctor` / `skyscraperPresheafFunctor` 的定义

English:
definition skyscraperPresheafFunctor
  signature: : A ⥤ Cᵒᵖ ⥤ A
  body: Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

中文:
定义 skyscraperPresheafFunctor
  签名: : A ⥤ Cᵒᵖ ⥤ A
  定义体: Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

Depends on / 依赖: Functor, Functor.flip, fiber.op, piFunctor
-/
noncomputable def skyscraperPresheafFunctor : A ⥤ Cᵒᵖ ⥤ A :=
  Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

/--
Definition of `skyscraperPresheaf` / `skyscraperPresheaf` 的定义

English:
abbreviation skyscraperPresheaf
  signature: (M : A)
  body: Φ.skyscraperPresheafFunctor.obj M

中文:
缩写 skyscraperPresheaf
  签名: (M : A)
  定义体: Φ.skyscraperPresheafFunctor.obj M

Depends on / 依赖: skyscraperPresheafFunctor, skyscraperPresheafFunctor.obj
-/
noncomputable abbrev skyscraperPresheaf (M : A) :
    Cᵒᵖ ⥤ A :=
  Φ.skyscraperPresheafFunctor.obj M

section

variable {P Q : Cᵒᵖ ⥤ A} {M N : A} [HasColimitsOfSize.{w, w} A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `Φ` is a point of a site `(C, J)`, `P : Cᵒᵖ ⥤ A` and `M : A`, this is
the bijection `(Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M)`
that is part of the adjunction `skyscraperPresheafAdjunction`. -/
@[simps -isSimp apply_app symm_apply]
/--
Definition of `skyscraperPresheafHomEquiv` / `skyscraperPresheafHomEquiv` 的定义

English:
definition skyscraperPresheafHomEquiv
  signature: :
  body: { app X := Pi.lift (fun x => Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x => g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

#adaptation_note

中文:
定义 skyscraperPresheafHomEquiv
  签名: :
  定义体: { app X := Pi.lift (fun x => Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x => g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

#adaptation_note

Depends on / 依赖: Pi.lift, X.unop, cat_disch, g.app, g.unop, invFun, left_inv, naturality, presheafFiberDesc, reassoc_of, right_inv, toPresheafFiber, toPresheafFiber_w
-/
noncomputable def skyscraperPresheafHomEquiv :
    (Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M) where
  toFun f :=
    { app X := Pi.lift (fun x => Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x => g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiber_skyscraperPresheafHomEquiv_symm` / 引理 `toPresheafFiber_skyscraperPresheafHomEquiv_symm`

English:
lemma toPresheafFiber_skyscraperPresheafHomEquiv_symm
  proof: by
  simp [skyscraperPresheafHomEquiv_symm_apply]

中文:
引理 toPresheafFiber_skyscraperPresheafHomEquiv_symm
  证明: by
  simp [skyscraperPresheafHomEquiv_symm_apply]

Depends on / 依赖: skyscraperPresheafHomEquiv_symm_apply
-/
lemma toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (g : P ⟶ Φ.skyscraperPresheaf M) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.skyscraperPresheafHomEquiv.symm g =
      g.app (op X) ≫ Pi.π _ x := by
  simp [skyscraperPresheafHomEquiv_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `skyscraperPresheafHomEquiv_naturality_left_symm` / 引理 `skyscraperPresheafHomEquiv_naturality_left_symm`

English:
lemma skyscraperPresheafHomEquiv_naturality_left_symm
  proof: by
  cat_disch

中文:
引理 skyscraperPresheafHomEquiv_naturality_left_symm
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma skyscraperPresheafHomEquiv_naturality_left_symm
    (f : P ⟶ Q) (g : Q ⟶ Φ.skyscraperPresheaf M) :
    Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) =
      Φ.presheafFiber.map f ≫ Φ.skyscraperPresheafHomEquiv.symm g := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `skyscraperPresheafHomEquiv_app_π` / 引理 `skyscraperPresheafHomEquiv_app_π`

English:
lemma skyscraperPresheafHomEquiv_app_π
  proof: by
  simp [skyscraperPresheafHomEquiv_apply_app]

中文:
引理 skyscraperPresheafHomEquiv_app_π
  证明: by
  simp [skyscraperPresheafHomEquiv_apply_app]

Depends on / 依赖: skyscraperPresheafHomEquiv_apply_app
-/
lemma skyscraperPresheafHomEquiv_app_π
    (f : Φ.presheafFiber.obj P ⟶ M) (X : C) (x : Φ.fiber.obj X) :
    (Φ.skyscraperPresheafHomEquiv f).app (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj X) => M) x =
      Φ.toPresheafFiber X x P ≫ f := by
  simp [skyscraperPresheafHomEquiv_apply_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `skyscraperPresheafHomEquiv_naturality_right` / 引理 `skyscraperPresheafHomEquiv_naturality_right`

English:
lemma skyscraperPresheafHomEquiv_naturality_right
  proof: by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc]; rw [Pi.map_π]; rw [skyscraperPresheafHomEquiv_app_π_assoc]

@[reassoc]

中文:
引理 skyscraperPresheafHomEquiv_naturality_right
  证明: by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc]; rw [Pi.map_π]; rw [skyscraperPresheafHomEquiv_app_π_assoc]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Pi.map_
-/
lemma skyscraperPresheafHomEquiv_naturality_right
    (f : Φ.presheafFiber.obj P ⟶ M) (g : M ⟶ N) :
    Φ.skyscraperPresheafHomEquiv (f ≫ g) =
      Φ.skyscraperPresheafHomEquiv f ≫ Φ.skyscraperPresheafFunctor.map g := by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc]; rw [Pi.map_π]; rw [skyscraperPresheafHomEquiv_app_π_assoc]

@[reassoc]
/--
lemma `skyscraperPresheafHomEquiv_naturality_left` / 引理 `skyscraperPresheafHomEquiv_naturality_left`

English:
lemma skyscraperPresheafHomEquiv_naturality_left
  proof: Φ.skyscraperPresheafHomEquiv.symm.injective
    (by simp [Φ.skyscraperPresheafHomEquiv_naturality_left_symm])

中文:
引理 skyscraperPresheafHomEquiv_naturality_left
  证明: Φ.skyscraperPresheafHomEquiv.symm.injective
    (by simp [Φ.skyscraperPresheafHomEquiv_naturality_left_symm])

Depends on / 依赖: injective, skyscraperPresheafHomEquiv, skyscraperPresheafHomEquiv.symm.injective, skyscraperPresheafHomEquiv_naturality_left_symm
-/
lemma skyscraperPresheafHomEquiv_naturality_left
    (f : P ⟶ Q) (g : Φ.presheafFiber.obj Q ⟶ M) :
    Φ.skyscraperPresheafHomEquiv (Φ.presheafFiber.map f ≫ g) =
      f ≫ Φ.skyscraperPresheafHomEquiv g :=
  Φ.skyscraperPresheafHomEquiv.symm.injective
    (by simp [Φ.skyscraperPresheafHomEquiv_naturality_left_symm])

end

section

variable [HasColimitsOfSize.{w, w} A]

/--
Definition of `skyscraperPresheafAdjunction` / `skyscraperPresheafAdjunction` 的定义

English:
definition skyscraperPresheafAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _ }

@[simp]

中文:
定义 skyscraperPresheafAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _ }

@[simp]

Depends on / 依赖: skyscraperPresheafFunctor
-/
noncomputable def skyscraperPresheafAdjunction :
    Φ.presheafFiber (A := A) ⊣ Φ.skyscraperPresheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _ }

@[simp]
/--
lemma `skyscraperPresheafAdjunction_homEquiv_apply` / 引理 `skyscraperPresheafAdjunction_homEquiv_apply`

English:
lemma skyscraperPresheafAdjunction_homEquiv_apply
  statement: {P : Cᵒᵖ ⥤ A} {M : A}
  proof: by
  simp [skyscraperPresheafAdjunction]

@[simp]

中文:
引理 skyscraperPresheafAdjunction_homEquiv_apply
  结论: {P : Cᵒᵖ ⥤ A} {M : A}
  证明: by
  simp [skyscraperPresheafAdjunction]

@[simp]

Depends on / 依赖: skyscraperPresheafAdjunction
-/
lemma skyscraperPresheafAdjunction_homEquiv_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : Φ.presheafFiber.obj P ⟶ M) :
    Φ.skyscraperPresheafAdjunction.homEquiv _ _ f =
      Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperPresheafAdjunction]

@[simp]
/--
lemma `skyscraperPresheafAdjunction_homEquiv_symm_apply` / 引理 `skyscraperPresheafAdjunction_homEquiv_symm_apply`

English:
lemma skyscraperPresheafAdjunction_homEquiv_symm_apply
  statement: {P : Cᵒᵖ ⥤ A} {M : A}
  proof: by
  simp [skyscraperPresheafAdjunction]

中文:
引理 skyscraperPresheafAdjunction_homEquiv_symm_apply
  结论: {P : Cᵒᵖ ⥤ A} {M : A}
  证明: by
  simp [skyscraperPresheafAdjunction]

Depends on / 依赖: skyscraperPresheafAdjunction
-/
lemma skyscraperPresheafAdjunction_homEquiv_symm_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : P ⟶ Φ.skyscraperPresheaf M) :
    (Φ.skyscraperPresheafAdjunction.homEquiv _ _).symm f =
      Φ.skyscraperPresheafHomEquiv.symm f := by
  simp [skyscraperPresheafAdjunction]

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {Φ} in
/--
lemma `isSheaf_skyscraperPresheaf_aux` / 引理 `isSheaf_skyscraperPresheaf_aux`

English:
lemma isSheaf_skyscraperPresheaf_aux
  proof: by
  suffices forall (x : Φ.fiber.obj X), exists (l : s.pt ⟶ M),
      forall ⦃Y : C⦄ (g : Y ⟶ X) (hg : R g) (y : Φ.fiber.obj Y) (hy : Φ.fiber.map g y = x),
        s.π.app (op (Presieve.categoryMk _ _ hg)) ≫ Pi.π _ y = l by
    choose l hl using this
    exact ⟨Pi.lift l, fun j y => by simpa using! (hl _ j.obj.hom j.property y rfl).symm⟩
  intro x
  obtain ⟨Y₁, f₁, hf₁, y₁, hy₁⟩ := Φ.jointly_surjective _ hR x
  refine ⟨s.π.app (op (Presieve.categoryMk _ _ hf₁)) ≫ Pi.π _ y₁,
    fun Y₂ f₂ hf₂ y₂ hy₂ => ?_⟩
  obtain ⟨Z, p₁, p₂, z, fac, hz₁, hz₂⟩ :
      exists (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
        Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
    let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ x := ⟨f₁, hy₁⟩
    let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ x := ⟨f₂, hy₂⟩
    obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
    rw [Subtype.ext_iff] at fac
    refine ⟨z.1, q₁.1, q₂.1, z.2, fac, ?_, ?_⟩
    all_goals rw [CategoryOfElements.map_snd] -- was `simp`
  let φ₁ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₁ :=
    ObjectProperty.homMk (Over.homMk p₁)
  let φ₂ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₂ :=
    ObjectProperty.homMk (Over.homMk p₂)
  simpa [hz₁, hz₂, φ₁, φ₂] using!
    (Cone.w s φ₂.op =≫ Pi.π _ z).trans (Cone.w s φ₁.op =≫ Pi.π _ z).symm

中文:
引理 isSheaf_skyscraperPresheaf_aux
  证明: by
  suffices forall (x : Φ.fiber.obj X), exists (l : s.pt ⟶ M),
      forall ⦃Y : C⦄ (g : Y ⟶ X) (hg : R g) (y : Φ.fiber.obj Y) (hy : Φ.fiber.map g y = x),
        s.π.app (op (Presieve.categoryMk _ _ hg)) ≫ Pi.π _ y = l by
    choose l hl using this
    exact ⟨Pi.lift l, fun j y => by simpa using! (hl _ j.obj.hom j.property y rfl).symm⟩
  intro x
  obtain ⟨Y₁, f₁, hf₁, y₁, hy₁⟩ := Φ.jointly_surjective _ hR x
  refine ⟨s.π.app (op (Presieve.categoryMk _ _ hf₁)) ≫ Pi.π _ y₁,
    fun Y₂ f₂ hf₂ y₂ hy₂ => ?_⟩
  obtain ⟨Z, p₁, p₂, z, fac, hz₁, hz₂⟩ :
      exists (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
        Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
    let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ x := ⟨f₁, hy₁⟩
    let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ x := ⟨f₂, hy₂⟩
    obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
    rw [Subtype.ext_iff] at fac
    refine ⟨z.1, q₁.1, q₂.1, z.2, fac, ?_, ?_⟩
    all_goals rw [CategoryOfElements.map_snd] -- was `simp`
  let φ₁ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₁ :=
    ObjectProperty.homMk (Over.homMk p₁)
  let φ₂ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₂ :=
    ObjectProperty.homMk (Over.homMk p₂)
  simpa [hz₁, hz₂, φ₁, φ₂] using!
    (Cone.w s φ₂.op =≫ Pi.π _ z).trans (Cone.w s φ₁.op =≫ Pi.π _ z).symm
-/
private lemma isSheaf_skyscraperPresheaf_aux
    {M : A} {X : C} (R : Sieve X) (hR : R in J X)
    (s : Cone (R.arrows.diagram.op ⋙ Φ.skyscraperPresheaf M)) :
    exists (l : s.pt ⟶ ∏ᶜ fun (_ : Φ.fiber.obj X) => M),
      forall (j : R.arrows.category) (y : Φ.fiber.obj j.obj.left),
        l ≫ Pi.π _ (Φ.fiber.map j.obj.hom y) = s.π.app (op j) ≫ Pi.π _ y := by
  suffices forall (x : Φ.fiber.obj X), exists (l : s.pt ⟶ M),
      forall ⦃Y : C⦄ (g : Y ⟶ X) (hg : R g) (y : Φ.fiber.obj Y) (hy : Φ.fiber.map g y = x),
        s.π.app (op (Presieve.categoryMk _ _ hg)) ≫ Pi.π _ y = l by
    choose l hl using this
    exact ⟨Pi.lift l, fun j y => by simpa using! (hl _ j.obj.hom j.property y rfl).symm⟩
  intro x
  obtain ⟨Y₁, f₁, hf₁, y₁, hy₁⟩ := Φ.jointly_surjective _ hR x
  refine ⟨s.π.app (op (Presieve.categoryMk _ _ hf₁)) ≫ Pi.π _ y₁,
    fun Y₂ f₂ hf₂ y₂ hy₂ => ?_⟩
  obtain ⟨Z, p₁, p₂, z, fac, hz₁, hz₂⟩ :
      exists (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
        Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
    let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ x := ⟨f₁, hy₁⟩
    let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ x := ⟨f₂, hy₂⟩
    obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
    rw [Subtype.ext_iff] at fac
    refine ⟨z.1, q₁.1, q₂.1, z.2, fac, ?_, ?_⟩
    all_goals rw [CategoryOfElements.map_snd] -- was `simp`
  let φ₁ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₁ :=
    ObjectProperty.homMk (Over.homMk p₁)
  let φ₂ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₂ :=
    ObjectProperty.homMk (Over.homMk p₂)
  simpa [hz₁, hz₂, φ₁, φ₂] using!
    (Cone.w s φ₂.op =≫ Pi.π _ z).trans (Cone.w s φ₁.op =≫ Pi.π _ z).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isSheaf_skyscraperPresheaf` / 引理 `isSheaf_skyscraperPresheaf`

English:
lemma isSheaf_skyscraperPresheaf
  given: (M : A)
  proof: by
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X R hR
  exact ⟨{
    lift s := (isSheaf_skyscraperPresheaf_aux R hR s).choose
    fac s j := by
      dsimp
      ext y
      simpa using! (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec _ y
    uniq s m hm := by
      dsimp at hm ⊢
      ext x
      obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ hR x
      simpa [← hm (op (Presieve.categoryMk _ _ hg))] using!
        ((isSheaf_skyscraperPresheaf_aux R hR s).choose_spec (Presieve.categoryMk _ _ hg) y).symm }⟩

中文:
引理 isSheaf_skyscraperPresheaf
  条件: (M : A)
  证明: by
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X R hR
  exact ⟨{
    lift s := (isSheaf_skyscraperPresheaf_aux R hR s).choose
    fac s j := by
      dsimp
      ext y
      simpa using! (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec _ y
    uniq s m hm := by
      dsimp at hm ⊢
      ext x
      obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ hR x
      simpa [← hm (op (Presieve.categoryMk _ _ hg))] using!
        ((isSheaf_skyscraperPresheaf_aux R hR s).choose_spec (Presieve.categoryMk _ _ hg) y).symm }⟩

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_isLimit, Presieve, Presieve.categoryMk, categoryMk, choose_spec, isSheaf_iff_isLimit, isSheaf_skyscraperPresheaf_aux, jointly_surjective
-/
lemma isSheaf_skyscraperPresheaf (M : A) :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf M) := by
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X R hR
  exact ⟨{
    lift s := (isSheaf_skyscraperPresheaf_aux R hR s).choose
    fac s j := by
      dsimp
      ext y
      simpa using! (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec _ y
    uniq s m hm := by
      dsimp at hm ⊢
      ext x
      obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ hR x
      simpa [← hm (op (Presieve.categoryMk _ _ hg))] using!
        ((isSheaf_skyscraperPresheaf_aux R hR s).choose_spec (Presieve.categoryMk _ _ hg) y).symm }⟩

/-- Given a point `Φ` of a site `(C, J)`, this is the skyscraper sheaf functor
`A ⥤ Sheaf J A`. -/
@[simps]
/--
Definition of `skyscraperSheafFunctor` / `skyscraperSheafFunctor` 的定义

English:
definition skyscraperSheafFunctor
  signature: : A ⥤ Sheaf J A where
  body: ⟨Φ.skyscraperPresheaf M, Φ.isSheaf_skyscraperPresheaf M⟩
  map f := ⟨Φ.skyscraperPresheafFunctor.map f⟩

中文:
定义 skyscraperSheafFunctor
  签名: : A ⥤ 层 J A where
  定义体: ⟨Φ.skyscraperPresheaf M, Φ.isSheaf_skyscraperPresheaf M⟩
  map f := ⟨Φ.skyscraperPresheafFunctor.map f⟩

Depends on / 依赖: isSheaf_skyscraperPresheaf, skyscraperPresheaf
-/
noncomputable def skyscraperSheafFunctor : A ⥤ Sheaf J A where
  obj M := ⟨Φ.skyscraperPresheaf M, Φ.isSheaf_skyscraperPresheaf M⟩
  map f := ⟨Φ.skyscraperPresheafFunctor.map f⟩

/--
Definition of `skyscraperSheaf` / `skyscraperSheaf` 的定义

English:
abbreviation skyscraperSheaf
  signature: (M : A)
  body: Φ.skyscraperSheafFunctor.obj M

中文:
缩写 skyscraperSheaf
  签名: (M : A)
  定义体: Φ.skyscraperSheafFunctor.obj M

Depends on / 依赖: skyscraperSheafFunctor, skyscraperSheafFunctor.obj
-/
noncomputable abbrev skyscraperSheaf (M : A) :
    Sheaf J A :=
  Φ.skyscraperSheafFunctor.obj M

variable [HasColimitsOfSize.{w, w} A]

/--
Definition of `skyscraperSheafAdjunction` / `skyscraperSheafAdjunction` 的定义

English:
definition skyscraperSheafAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }

中文:
定义 skyscraperSheafAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }

Depends on / 依赖: skyscraperSheafFunctor
-/
noncomputable def skyscraperSheafAdjunction :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Φ.sheafFiber (A := A)).IsLeftAdjoint
  body: Φ.skyscraperSheafAdjunction.isLeftAdjoint

中文:
实例 :
  签名: (Φ.sheafFiber (A := A)).是左伴随
  定义体: Φ.skyscraperSheafAdjunction.isLeftAdjoint

Depends on / 依赖: IsLeftAdjoint
-/
instance : (Φ.sheafFiber (A := A)).IsLeftAdjoint :=
  Φ.skyscraperSheafAdjunction.isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Φ.skyscraperSheafFunctor (A := A)).IsRightAdjoint
  body: Φ.skyscraperSheafAdjunction.isRightAdjoint

中文:
实例 :
  签名: (Φ.skyscraperSheafFunctor (A := A)).是右伴随
  定义体: Φ.skyscraperSheafAdjunction.isRightAdjoint

Depends on / 依赖: IsRightAdjoint
-/
instance : (Φ.skyscraperSheafFunctor (A := A)).IsRightAdjoint :=
  Φ.skyscraperSheafAdjunction.isRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `skyscraperSheafAdjunction_homEquiv_apply_hom` / 引理 `skyscraperSheafAdjunction_homEquiv_apply_hom`

English:
lemma skyscraperSheafAdjunction_homEquiv_apply_hom
  statement: {F : Sheaf J A} {M : A}
  proof: Φ.skyscraperSheafAdjunction.homEquiv F M
    letI a : F.obj ⟶ Φ.skyscraperPresheaf M := (e f).hom
    a = Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

@[deprecated (since := "2026-03-05")]
alias skyscraperSheafAdjunction_homEquiv_apply_val :=
  skyscraperSheafAdjunction_homEquiv_apply_hom

中文:
引理 skyscraperSheafAdjunction_homEquiv_apply_hom
  结论: {F : 层 J A} {M : A}
  证明: Φ.skyscraperSheafAdjunction.homEquiv F M
    letI a : F.obj ⟶ Φ.skyscraperPresheaf M := (e f).hom
    a = Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

@[deprecated (since := "2026-03-05")]
alias skyscraperSheafAdjunction_homEquiv_apply_val :=
  skyscraperSheafAdjunction_homEquiv_apply_hom

Depends on / 依赖: homEquiv, skyscraperSheafAdjunction, skyscraperSheafAdjunction.homEquiv
-/
lemma skyscraperSheafAdjunction_homEquiv_apply_hom {F : Sheaf J A} {M : A}
    (f : Φ.presheafFiber.obj F.obj ⟶ M) :
    letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    letI a : F.obj ⟶ Φ.skyscraperPresheaf M := (e f).hom
    a = Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

@[deprecated (since := "2026-03-05")]
alias skyscraperSheafAdjunction_homEquiv_apply_val :=
  skyscraperSheafAdjunction_homEquiv_apply_hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `skyscraperSheafAdjunction_homEquiv_symm_apply` / 引理 `skyscraperSheafAdjunction_homEquiv_symm_apply`

English:
lemma skyscraperSheafAdjunction_homEquiv_symm_apply
  statement: {F : Sheaf J A} {M : A}
  proof: Φ.skyscraperSheafAdjunction.homEquiv F M
    e.symm f = Φ.skyscraperPresheafHomEquiv.symm f.hom := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

中文:
引理 skyscraperSheafAdjunction_homEquiv_symm_apply
  结论: {F : 层 J A} {M : A}
  证明: Φ.skyscraperSheafAdjunction.homEquiv F M
    e.symm f = Φ.skyscraperPresheafHomEquiv.symm f.hom := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

Depends on / 依赖: homEquiv, skyscraperSheafAdjunction, skyscraperSheafAdjunction.homEquiv
-/
lemma skyscraperSheafAdjunction_homEquiv_symm_apply {F : Sheaf J A} {M : A}
    (f : F ⟶ Φ.skyscraperSheaf M) :
    letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    e.symm f = Φ.skyscraperPresheafHomEquiv.symm f.hom := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

/--
lemma `W_isInvertedBy_presheafFiber` / 引理 `W_isInvertedBy_presheafFiber`

English:
lemma W_isInvertedBy_presheafFiber
  proof: by
  intro P₁ P₂ f hf
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← Function.Bijective.of_comp_iff' Φ.skyscraperPresheafHomEquiv.bijective]
  convert! (hf _ (Φ.isSheaf_skyscraperPresheaf M)).comp Φ.skyscraperPresheafHomEquiv.bijective
  ext g : 1
  simp [skyscraperPresheafHomEquiv_naturality_left]

中文:
引理 W_isInvertedBy_presheafFiber
  证明: by
  intro P₁ P₂ f hf
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← Function.Bijective.of_comp_iff' Φ.skyscraperPresheafHomEquiv.bijective]
  convert! (hf _ (Φ.isSheaf_skyscraperPresheaf M)).comp Φ.skyscraperPresheafHomEquiv.bijective
  ext g : 1
  simp [skyscraperPresheafHomEquiv_naturality_left]

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, bijective, convert, isIso_iff_coyoneda_map_bijective, isSheaf_skyscraperPresheaf, of_comp_iff, skyscraperPresheafHomEquiv, skyscraperPresheafHomEquiv.bijective, skyscraperPresheafHomEquiv_naturality_left
-/
lemma W_isInvertedBy_presheafFiber :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P₁ P₂ f hf
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← Function.Bijective.of_comp_iff' Φ.skyscraperPresheafHomEquiv.bijective]
  convert! (hf _ (Φ.isSheaf_skyscraperPresheaf M)).comp Φ.skyscraperPresheafHomEquiv.bijective
  ext g : 1
  simp [skyscraperPresheafHomEquiv_naturality_left]

instance (P : Cᵒᵖ ⥤ A) [HasWeakSheafify J A] :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J P)) :=
  W_isInvertedBy_presheafFiber _ _ (W_toSheafify J P)

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/--
Definition of `presheafToSheafCompSheafFiberIso` / `presheafToSheafCompSheafFiberIso` 的定义

English:
definition presheafToSheafCompSheafFiberIso
  signature: [HasWeakSheafify J A]
  body: (NatIso.ofComponents
    (fun P => asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
      (by simp [sheafFiber, ← Functor.map_comp])).symm

@[deprecated (since := "2026-03-08")]
alias presheafToSheafCompSheafFiber := presheafToSheafCompSheafFiberIso

中文:
定义 presheafToSheafCompSheafFiberIso
  签名: [HasWeakSheafify J A]
  定义体: (NatIso.ofComponents
    (fun P => asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
      (by simp [sheafFiber, ← Functor.map_comp])).symm

@[deprecated (since := "2026-03-08")]
alias presheafToSheafCompSheafFiber := presheafToSheafCompSheafFiberIso

Depends on / 依赖: CategoryTheory, CategoryTheory.toSheafify, Functor, Functor.map_comp, NatIso, NatIso.ofComponents, map_comp, ofComponents, presheafFiber, sheafFiber, toSheafify
-/
noncomputable def presheafToSheafCompSheafFiberIso [HasWeakSheafify J A] :
    presheafToSheaf J A ⋙ Φ.sheafFiber ≅ Φ.presheafFiber :=
  (NatIso.ofComponents
    (fun P => asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
      (by simp [sheafFiber, ← Functor.map_comp])).symm

@[deprecated (since := "2026-03-08")]
alias presheafToSheafCompSheafFiber := presheafToSheafCompSheafFiberIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: J A] :
  body: Φ.presheafToSheafCompSheafFiberIso A

中文:
实例 [HasWeakSheafify
  签名: J A] :
  定义体: Φ.presheafToSheafCompSheafFiberIso A

Depends on / 依赖: presheafToSheafCompSheafFiberIso
-/
noncomputable instance [HasWeakSheafify J A] :
    Localization.Lifting (presheafToSheaf J A) J.W
      Φ.presheafFiber Φ.sheafFiber where
  iso := Φ.presheafToSheafCompSheafFiberIso A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (Φ.sheafFiber (A := A))
  body: have : PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) := inferInstance
  PreservesColimitsOfSize.preservesFiniteColimits _

中文:
实例 :
  签名: 保持FiniteColimits (Φ.sheafFiber (A := A))
  定义体: have : PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) := inferInstance
  PreservesColimitsOfSize.preservesFiniteColimits _
-/
instance : PreservesFiniteColimits (Φ.sheafFiber (A := A)) :=
  have : PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) := inferInstance
  PreservesColimitsOfSize.preservesFiniteColimits _

end CategoryTheory.GrothendieckTopology.Point
