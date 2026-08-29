/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# `eqToHom` in bicategories

This file records some of the behavior of `eqToHom` 1-morphisms and
2-morphisms in bicategories.

Given an equality of objects `h : x = y` in a bicategory, there is a 1-morphism
`eqToHom h : x ⟶ y` just like in an ordinary category. The definitional property
of this morphism is that if `h : x = x`, `eqToHom h = 𝟙 x`. This is
implemented as the `eqToHom` morphism in the `CategoryStruct` underlying the
bicategory.

Unlike the situation in ordinary category theory, these 1-morphisms do not
compose strictly: `eqToHom h.trans h'` is merely isomorphic to
`eqToHom h ≫ eqToHom h'`. We define this isomorphism as
`CategoryTheory.Bicategory.eqToHomTransIso`.

Given an equality of 1-morphisms, we show that various bicategorical
structure morphisms such as unitors, associators and whiskering conjugate
well under `eqToHom`s.

## TODO
* Define `eqToEquiv` that puts the `eqToHom`s in an `Equivalence` between
  objects.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/--
Definition of `eqToHomTransIso` / `eqToHomTransIso` 的定义

English:
definition eqToHomTransIso
  signature: {x y z : B} (e₁ : x = y) (e₂ : y = z)
  body: e₂ ▸ e₁ ▸ (fun_ (𝟙 x)).symm

@[simp]

中文:
定义 eqToHomTransIso
  签名: {x y z : B} (e₁ : x = y) (e₂ : y = z)
  定义体: e₂ ▸ e₁ ▸ (fun_ (𝟙 x)).symm

@[simp]

Depends on / 依赖: fun_
-/
def eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) :
    eqToHom (e₁.trans e₂) ≅ eqToHom e₁ ≫ eqToHom e₂ :=
  e₂ ▸ e₁ ▸ (fun_ (𝟙 x)).symm

@[simp]
/--
lemma `eqToHomTransIso_refl_refl` / 引理 `eqToHomTransIso_refl_refl`

English:
lemma eqToHomTransIso_refl_refl
  given: (x : B)
  proof: rfl

中文:
引理 eqToHomTransIso_refl_refl
  条件: (x : B)
  证明: rfl
-/
lemma eqToHomTransIso_refl_refl (x : B) :
    eqToHomTransIso (rfl : x = x) rfl = (fun_ (𝟙 x)).symm :=
  rfl

/--
lemma `eqToHomTransIso_refl_right` / 引理 `eqToHomTransIso_refl_right`

English:
lemma eqToHomTransIso_refl_right
  given: {x y : B} (e₁ : x = y)
  proof: by
  ext
  subst e₁
  simp

中文:
引理 eqToHomTransIso_refl_right
  条件: {x y : B} (e₁ : x = y)
  证明: by
  ext
  subst e₁
  simp
-/
lemma eqToHomTransIso_refl_right {x y : B} (e₁ : x = y) :
    eqToHomTransIso e₁ rfl = (ρ_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp

/--
lemma `eqToHomTransIso_refl_left` / 引理 `eqToHomTransIso_refl_left`

English:
lemma eqToHomTransIso_refl_left
  given: {x y : B} (e₁ : x = y)
  proof: by
  ext
  subst e₁
  simp

@[reassoc]

中文:
引理 eqToHomTransIso_refl_left
  条件: {x y : B} (e₁ : x = y)
  证明: by
  ext
  subst e₁
  simp

@[reassoc]
-/
lemma eqToHomTransIso_refl_left {x y : B} (e₁ : x = y) :
    eqToHomTransIso rfl e₁ = (fun_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp

@[reassoc]
/--
lemma `associator_eqToHom_hom` / 引理 `associator_eqToHom_hom`

English:
lemma associator_eqToHom_hom
  statement: {x y z t : B}
  proof: by
  subst_vars
  simp

@[reassoc]

中文:
引理 associator_eqToHom_hom
  结论: {x y z t : B}
  证明: by
  subst_vars
  simp

@[reassoc]
-/
lemma associator_eqToHom_hom {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).hom =
    (eqToHomTransIso e₁ e₂).inv ▷ eqToHom e₃ ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).hom ≫
      eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).hom := by
  subst_vars
  simp

@[reassoc]
/--
lemma `associator_eqToHom_inv` / 引理 `associator_eqToHom_inv`

English:
lemma associator_eqToHom_inv
  statement: {x y z t : B}
  proof: by
  subst_vars
  simp

中文:
引理 associator_eqToHom_inv
  结论: {x y z t : B}
  证明: by
  subst_vars
  simp
-/
lemma associator_eqToHom_inv {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).inv =
    eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).inv ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).hom ≫
      (eqToHomTransIso e₁ e₂).hom ▷ eqToHom e₃ := by
  subst_vars
  simp

/--
lemma `associator_hom_congr` / 引理 `associator_hom_congr`

English:
lemma associator_hom_congr
  statement: {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
  proof: by
  subst_vars
  simp

中文:
引理 associator_hom_congr
  结论: {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
  证明: by
  subst_vars
  simp
-/
lemma associator_hom_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).hom =
    eqToHom (by grind) ≫ (α_ f' g' h').hom ≫ eqToHom (by grind) := by
  subst_vars
  simp

/--
lemma `associator_inv_congr` / 引理 `associator_inv_congr`

English:
lemma associator_inv_congr
  statement: {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
  proof: by
  subst_vars
  simp

中文:
引理 associator_inv_congr
  结论: {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
  证明: by
  subst_vars
  simp
-/
lemma associator_inv_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).inv =
    eqToHom (by grind) ≫ (α_ f' g' h').inv ≫ eqToHom (by grind) := by
  subst_vars
  simp

/--
lemma `congr_whiskerLeft` / 引理 `congr_whiskerLeft`

English:
lemma congr_whiskerLeft
  statement: {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B}
  proof: by
  subst h
  simp

中文:
引理 congr_whiskerLeft
  结论: {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B}
  证明: by
  subst h
  simp
-/
lemma congr_whiskerLeft {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B}
    {g g' : y ⟶ z} (η : g ⟶ g') :
      f ◁ η = eqToHom (by rw [h]) ≫ f' ◁ η ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/--
lemma `whiskerRight_congr` / 引理 `whiskerRight_congr`

English:
lemma whiskerRight_congr
  statement: {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B}
  proof: by
  subst h
  simp

中文:
引理 whiskerRight_congr
  结论: {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B}
  证明: by
  subst h
  simp
-/
lemma whiskerRight_congr {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B}
    {f f' : x ⟶ y} (η : f ⟶ f') :
      η ▷ g = eqToHom (by rw [h]) ≫ η ▷ g' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/--
lemma `leftUnitor_hom_congr` / 引理 `leftUnitor_hom_congr`

English:
lemma leftUnitor_hom_congr
  given: {x y : B} {f f' : x ⟶ y} (h : f = f')
  proof: by
  subst h
  simp

中文:
引理 leftUnitor_hom_congr
  条件: {x y : B} {f f' : x ⟶ y} (h : f = f')
  证明: by
  subst h
  simp
-/
lemma leftUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (fun_ f).hom = 𝟙 _ ◁ (eqToHom h) ≫ (fun_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp

/--
lemma `leftUnitor_inv_congr` / 引理 `leftUnitor_inv_congr`

English:
lemma leftUnitor_inv_congr
  given: {x y : B} {f f' : x ⟶ y} (h : f = f')
  proof: by
  subst h
  simp

中文:
引理 leftUnitor_inv_congr
  条件: {x y : B} {f f' : x ⟶ y} (h : f = f')
  证明: by
  subst h
  simp
-/
lemma leftUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (fun_ f).inv = (eqToHom h) ≫ (fun_ f').inv ≫ 𝟙 _ ◁ eqToHom h.symm := by
  subst h
  simp

/--
lemma `rightUnitor_hom_congr` / 引理 `rightUnitor_hom_congr`

English:
lemma rightUnitor_hom_congr
  given: {x y : B} {f f' : x ⟶ y} (h : f = f')
  proof: by
  subst h
  simp

中文:
引理 rightUnitor_hom_congr
  条件: {x y : B} {f f' : x ⟶ y} (h : f = f')
  证明: by
  subst h
  simp
-/
lemma rightUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).hom = (eqToHom h) ▷ 𝟙 _ ≫ (ρ_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp

/--
lemma `rightUnitor_inv_congr` / 引理 `rightUnitor_inv_congr`

English:
lemma rightUnitor_inv_congr
  given: {x y : B} {f f' : x ⟶ y} (h : f = f')
  proof: by
  subst h
  simp

中文:
引理 rightUnitor_inv_congr
  条件: {x y : B} {f f' : x ⟶ y} (h : f = f')
  证明: by
  subst h
  simp
-/
lemma rightUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).inv = (eqToHom h) ≫ (ρ_ f').inv ≫ eqToHom h.symm ▷ 𝟙 _ := by
  subst h
  simp

end CategoryTheory.Bicategory
