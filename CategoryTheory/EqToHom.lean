/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Morphisms from equations between objects.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eqToHom h : X ⟶ Y`, or `eqToIso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eqToHom` morphisms to drop out at the appropriate moment!
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Opposite

/--
Definition of `eqToHom` / `eqToHom` 的定义

English:
definition eqToHom
  signature: {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y)
  body: by
  rw [p]
  exact 𝟙 _

中文:
定义 eqToHom
  签名: {C : 类型u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y)
  定义体: by
  rw [p]
  exact 𝟙 _

Depends on / 依赖: IsRightAdjoint, preservesZeroMorphisms_of_isRightAdjoint
-/
def eqToHom {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) :
    X ⟶ Y := by
  rw [p]
  exact 𝟙 _

/-- `eqToHom'` is the dual of `eqToHom`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing eqToHom]
/--
Definition of `eqToHom'` / `eqToHom'` 的定义

English:
abbreviation eqToHom'
  signature: {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y)
  body: eqToHom p.symm

@[simp]

中文:
缩写 eqToHom'
  签名: {C : 类型u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y)
  定义体: eqToHom p.symm

@[simp]

Depends on / 依赖: eqToHom, p.symm, preservesZeroMorphisms_of_full
-/
abbrev eqToHom' {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) : Y ⟶ X :=
  eqToHom p.symm

@[simp]
/--
theorem `eqToHom_refl` / 定理 `eqToHom_refl`

English:
theorem eqToHom_refl
  given: {C : Type u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X)
  proof: rfl

中文:
定理 eqToHom_refl
  条件: {C : 类型u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X)
  证明: rfl
-/
theorem eqToHom_refl {C : Type u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X) :
    eqToHom p = 𝟙 X :=
  rfl

variable {C : Type u₁} [Category.{v₁} C]

@[to_dual none, reassoc (attr := simp)]
/--
theorem `eqToHom_trans` / 定理 `eqToHom_trans`

English:
theorem eqToHom_trans
  given: {X Y Z : C} (p : X = Y) (q : Y = Z)
  proof: by
  cases p
  cases q
  simp

中文:
定理 eqToHom_trans
  条件: {X Y Z : C} (p : X = Y) (q : Y = Z)
  证明: by
  cases p
  cases q
  simp
-/
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
  cases p
  cases q
  simp

/-- `eqToHom h` is heterogeneously equal to the identity of its domain. -/
@[to_dual none]
/--
lemma `eqToHom_heq_id_dom` / 引理 `eqToHom_heq_id_dom`

English:
lemma eqToHom_heq_id_dom
  given: (X Y : C) (h : X = Y)
  statement: eqToHom h ≍ 𝟙 X
  proof: by
  subst h; rfl

中文:
引理 eqToHom_heq_id_dom
  条件: (X Y : C) (h : X = Y)
  结论: eqToHom h ≍ 𝟙 X
  证明: by
  subst h; rfl
-/
lemma eqToHom_heq_id_dom (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 X := by
  subst h; rfl

/-- `eqToHom h` is heterogeneously equal to the identity of its codomain. -/
@[to_dual none]
/--
lemma `eqToHom_heq_id_cod` / 引理 `eqToHom_heq_id_cod`

English:
lemma eqToHom_heq_id_cod
  given: (X Y : C) (h : X = Y)
  statement: eqToHom h ≍ 𝟙 Y
  proof: by
  subst h; rfl

中文:
引理 eqToHom_heq_id_cod
  条件: (X Y : C) (h : X = Y)
  结论: eqToHom h ≍ 𝟙 Y
  证明: by
  subst h; rfl
-/
lemma eqToHom_heq_id_cod (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 Y := by
  subst h; rfl

/-- Two morphisms are conjugate via eqToHom if and only if they are heterogeneously equal.
Note this used to be in the Functor namespace, where it doesn't belong. -/
@[to_dual none]
/--
theorem `conj_eqToHom_iff_heq` / 定理 `conj_eqToHom_iff_heq`

English:
theorem conj_eqToHom_iff_heq
  given: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z)
  proof: by
  cases h
  cases h'
  simp

@[to_dual none]

中文:
定理 conj_eqToHom_iff_heq
  条件: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z)
  证明: by
  cases h
  cases h'
  simp

@[to_dual none]
-/
theorem conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ f ≍ g := by
  cases h
  cases h'
  simp

@[to_dual none]
/--
theorem `conj_eqToHom_iff_heq'` / 定理 `conj_eqToHom_iff_heq'`

English:
theorem conj_eqToHom_iff_heq'
  statement: {C} [Category* C] {W X Y Z : C}
  proof: conj_eqToHom_iff_heq _ _ _ h'.symm

@[to_dual none]

中文:
定理 conj_eqToHom_iff_heq'
  结论: {C} [Category* C] {W X Y Z : C}
  证明: conj_eqToHom_iff_heq _ _ _ h'.symm

@[to_dual none]

Depends on / 依赖: conj_eqToHom_iff_heq, preservesZeroMorphisms_of_preserves_initial_object
-/
theorem conj_eqToHom_iff_heq' {C} [Category* C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) :
    f = eqToHom h ≫ g ≫ eqToHom h' ↔ f ≍ g := conj_eqToHom_iff_heq _ _ _ h'.symm

@[to_dual none]
/--
theorem `comp_eqToHom_iff` / 定理 `comp_eqToHom_iff`

English:
theorem comp_eqToHom_iff
  given: {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y')
  proof: { mp h := by simp [← h]
    mpr h := by simp [eq_whisker h (eqToHom p)] }

@[to_dual none]

中文:
定理 comp_eqToHom_iff
  条件: {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y')
  证明: { mp h := by simp [← h]
    mpr h := by simp [eq_whisker h (eqToHom p)] }

@[to_dual none]

Depends on / 依赖: eqToHom, eq_whisker, preservesZeroMorphisms_of_preserves_terminal_object
-/
theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp h := by simp [← h]
    mpr h := by simp [eq_whisker h (eqToHom p)] }

@[to_dual none]
/--
theorem `eqToHom_comp_iff` / 定理 `eqToHom_comp_iff`

English:
theorem eqToHom_comp_iff
  given: {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y)
  proof: { mp h := by simp [← h]
    mpr h := by simp [h] }

@[to_dual none]

中文:
定理 eqToHom_comp_iff
  条件: {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y)
  证明: { mp h := by simp [← h]
    mpr h := by simp [h] }

@[to_dual none]
-/
theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp h := by simp [← h]
    mpr h := by simp [h] }

@[to_dual none]
/--
theorem `eqToHom_comp_heq` / 定理 `eqToHom_comp_heq`

English:
theorem eqToHom_comp_heq
  statement: {C} [Category* C] {W X Y : C}
  proof: by
  rw [← conj_eqToHom_iff_heq _ _ h rfl]; rw [eqToHom_refl]; rw [Category.comp_id]

@[simp, to_dual none]

中文:
定理 eqToHom_comp_heq
  结论: {C} [Category* C] {W X Y : C}
  证明: by
  rw [← conj_eqToHom_iff_heq _ _ h rfl]; rw [eqToHom_refl]; rw [Category.comp_id]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.comp_id, comp_id, conj_eqToHom_iff_heq, eqToHom_refl
-/
theorem eqToHom_comp_heq {C} [Category* C] {W X Y : C}
    (f : Y ⟶ X) (h : W = Y) : eqToHom h ≫ f ≍ f := by
  rw [← conj_eqToHom_iff_heq _ _ h rfl]; rw [eqToHom_refl]; rw [Category.comp_id]

@[simp, to_dual none]
/--
theorem `eqToHom_comp_heq_iff` / 定理 `eqToHom_comp_heq_iff`

English:
theorem eqToHom_comp_heq_iff
  statement: {C} [Category* C] {W X Y Z Z' : C}
  proof: ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp, to_dual none]

中文:
定理 eqToHom_comp_heq_iff
  结论: {C} [Category* C] {W X Y Z Z' : C}
  证明: ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp, to_dual none]

Depends on / 依赖: eqToHom_comp_heq, symm.trans
-/
theorem eqToHom_comp_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    eqToHom h ≫ f ≍ g ↔ f ≍ g :=
  ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp, to_dual none]
/--
theorem `heq_eqToHom_comp_iff` / 定理 `heq_eqToHom_comp_iff`

English:
theorem heq_eqToHom_comp_iff
  statement: {C} [Category* C] {W X Y Z Z' : C}
  proof: ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

@[to_dual none]

中文:
定理 heq_eqToHom_comp_iff
  结论: {C} [Category* C] {W X Y Z Z' : C}
  证明: ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

@[to_dual none]

Depends on / 依赖: eqToHom_comp_heq
-/
theorem heq_eqToHom_comp_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    g ≍ eqToHom h ≫ f ↔ g ≍ f :=
  ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

@[to_dual none]
/--
theorem `comp_eqToHom_heq` / 定理 `comp_eqToHom_heq`

English:
theorem comp_eqToHom_heq
  statement: {C} [Category* C] {X Y Z : C}
  proof: by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp, to_dual none]

中文:
定理 comp_eqToHom_heq
  结论: {C} [Category* C] {X Y Z : C}
  证明: by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.id_comp, conj_eqToHom_iff_heq, eqToHom_refl, id_comp
-/
theorem comp_eqToHom_heq {C} [Category* C] {X Y Z : C}
    (f : X ⟶ Y) (h : Y = Z) : f ≫ eqToHom h ≍ f := by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp, to_dual none]
/--
theorem `comp_eqToHom_heq_iff` / 定理 `comp_eqToHom_heq_iff`

English:
theorem comp_eqToHom_heq_iff
  statement: {C} [Category* C] {W X Y Z Z' : C}
  proof: ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp, to_dual none]

中文:
定理 comp_eqToHom_heq_iff
  结论: {C} [Category* C] {W X Y Z Z' : C}
  证明: ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp, to_dual none]

Depends on / 依赖: comp_eqToHom_heq, symm.trans
-/
theorem comp_eqToHom_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    f ≫ eqToHom h ≍ g ↔ f ≍ g :=
  ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp, to_dual none]
/--
theorem `heq_comp_eqToHom_iff` / 定理 `heq_comp_eqToHom_iff`

English:
theorem heq_comp_eqToHom_iff
  statement: {C} [Category* C] {W X Y Z Z' : C}
  proof: ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

@[to_dual self (reorder := X Z, X' Z', f g, f' g', eq1 eq3, H1 H2)]

中文:
定理 heq_comp_eqToHom_iff
  结论: {C} [Category* C] {W X Y Z Z' : C}
  证明: ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

@[to_dual self (reorder := X Z, X' Z', f g, f' g', eq1 eq3, H1 H2)]

Depends on / 依赖: comp_eqToHom_heq
-/
theorem heq_comp_eqToHom_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    g ≍ f ≫ eqToHom h ↔ g ≍ f :=
  ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

@[to_dual self (reorder := X Z, X' Z', f g, f' g', eq1 eq3, H1 H2)]
/--
theorem `heq_comp` / 定理 `heq_comp`

English:
theorem heq_comp
  statement: {C} [Category* C] {X Y Z X' Y' Z' : C}
  proof: by
  congr!

中文:
定理 heq_comp
  结论: {C} [Category* C] {X Y Z X' Y' Z' : C}
  证明: by
  congr!
-/
theorem heq_comp {C} [Category* C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z')
    (H1 : f ≍ f') (H2 : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  congr!

variable {β : Sort*}

/-- We can push `eqToHom` to the left through families of morphisms. -/
@[to_dual none, reassoc (attr := simp)]
/--
theorem `eqToHom_naturality` / 定理 `eqToHom_naturality`

English:
theorem eqToHom_naturality
  given: {f g : β -> C} (z : forall b, f b ⟶ g b) {j j' : β} (w : j = j')
  proof: by
  cases w
  simp

中文:
定理 eqToHom_naturality
  条件: {f g : β -> C} (z : 对任意 b, f b ⟶ g b) {j j' : β} (w : j = j')
  证明: by
  cases w
  simp
-/
theorem eqToHom_naturality {f g : β -> C} (z : forall b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j' := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[to_dual none, reassoc (attr := simp)]
/--
theorem `eqToHom_iso_hom_naturality` / 定理 `eqToHom_iso_hom_naturality`

English:
theorem eqToHom_iso_hom_naturality
  given: {f g : β -> C} (z : forall b, f b ≅ g b) {j j' : β} (w : j = j')
  proof: by
  cases w
  simp

中文:
定理 eqToHom_iso_hom_naturality
  条件: {f g : β -> C} (z : 对任意 b, f b ≅ g b) {j j' : β} (w : j = j')
  证明: by
  cases w
  simp
-/
theorem eqToHom_iso_hom_naturality {f g : β -> C} (z : forall b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').hom := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[to_dual none, reassoc (attr := simp)]
/--
theorem `eqToHom_iso_inv_naturality` / 定理 `eqToHom_iso_inv_naturality`

English:
theorem eqToHom_iso_inv_naturality
  given: {f g : β -> C} (z : forall b, f b ≅ g b) {j j' : β} (w : j = j')
  proof: by
  cases w
  simp

中文:
定理 eqToHom_iso_inv_naturality
  条件: {f g : β -> C} (z : 对任意 b, f b ≅ g b) {j j' : β} (w : j = j')
  证明: by
  cases w
  simp
-/
theorem eqToHom_iso_inv_naturality {f g : β -> C} (z : forall b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').inv := by
  cases w
  simp

/-- Reducible form of `congrArg_mpr_hom_left` -/
@[simp, to_dual none]
/--
theorem `congrArg_cast_hom_left` / 定理 `congrArg_cast_hom_left`

English:
theorem congrArg_cast_hom_left
  given: {X Y Z : C} (p : X = Y) (q : Y ⟶ Z)
  proof: by
  cases p
  simp

中文:
定理 congrArg_cast_hom_left
  条件: {X Y Z : C} (p : X = Y) (q : Y ⟶ Z)
  证明: by
  cases p
  simp
-/
theorem congrArg_cast_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    cast (congrArg (fun W : C => W ⟶ Z) p.symm) q = eqToHom p ≫ q := by
  cases p
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
@[to_dual none]
/--
theorem `congrArg_mpr_hom_left` / 定理 `congrArg_mpr_hom_left`

English:
theorem congrArg_mpr_hom_left
  given: {X Y Z : C} (p : X = Y) (q : Y ⟶ Z)
  proof: by
  cases p
  simp

中文:
定理 congrArg_mpr_hom_left
  条件: {X Y Z : C} (p : X = Y) (q : Y ⟶ Z)
  证明: by
  cases p
  simp
-/
theorem congrArg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    (congrArg (fun W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q := by
  cases p
  simp

/-- Reducible form of `congrArg_mpr_hom_right` -/
@[simp, to_dual none]
/--
theorem `congrArg_cast_hom_right` / 定理 `congrArg_cast_hom_right`

English:
theorem congrArg_cast_hom_right
  given: {X Y Z : C} (p : X ⟶ Y) (q : Z = Y)
  proof: by
  cases q
  simp

中文:
定理 congrArg_cast_hom_right
  条件: {X Y Z : C} (p : X ⟶ Y) (q : Z = Y)
  证明: by
  cases q
  simp
-/
theorem congrArg_cast_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    cast (congrArg (fun W : C => X ⟶ W) q.symm) p = p ≫ eqToHom q.symm := by
  cases q
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
@[to_dual none]
/--
theorem `congrArg_mpr_hom_right` / 定理 `congrArg_mpr_hom_right`

English:
theorem congrArg_mpr_hom_right
  given: {X Y Z : C} (p : X ⟶ Y) (q : Z = Y)
  proof: by
  cases q
  simp

中文:
定理 congrArg_mpr_hom_right
  条件: {X Y Z : C} (p : X ⟶ Y) (q : Z = Y)
  证明: by
  cases q
  simp
-/
theorem congrArg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    (congrArg (fun W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm := by
  cases q
  simp

/--
Definition of `eqToIso` / `eqToIso` 的定义

English:
definition eqToIso
  signature: {X Y : C} (p : X = Y)
  body: ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩

@[simp]

中文:
定义 eqToIso
  签名: {X Y : C} (p : X = Y)
  定义体: ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩

@[simp]

Depends on / 依赖: eqToHom, p.symm
-/
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩

@[simp]
/--
theorem `eqToIso.hom` / 定理 `eqToIso.hom`

English:
theorem eqToIso.hom
  given: {X Y : C} (p : X = Y)
  statement: (eqToIso p).hom = eqToHom p
  proof: rfl

@[simp, to_dual existing hom]

中文:
定理 eqToIso.hom
  条件: {X Y : C} (p : X = Y)
  结论: (eqToIso p).hom = eqToHom p
  证明: rfl

@[simp, to_dual existing hom]
-/
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).hom = eqToHom p :=
  rfl

@[simp, to_dual existing hom]
/--
theorem `eqToIso.inv` / 定理 `eqToIso.inv`

English:
theorem eqToIso.inv
  given: {X Y : C} (p : X = Y)
  statement: (eqToIso p).inv = eqToHom p.symm
  proof: rfl

@[simp]

中文:
定理 eqToIso.inv
  条件: {X Y : C} (p : X = Y)
  结论: (eqToIso p).inv = eqToHom p.symm
  证明: rfl

@[simp]
-/
theorem eqToIso.inv {X Y : C} (p : X = Y) : (eqToIso p).inv = eqToHom p.symm :=
  rfl

@[simp]
/--
theorem `eqToIso_refl` / 定理 `eqToIso_refl`

English:
theorem eqToIso_refl
  given: {X : C} (p : X = X)
  statement: eqToIso p = Iso.refl X
  proof: rfl

@[simp]

中文:
定理 eqToIso_refl
  条件: {X : C} (p : X = X)
  结论: eqToIso p = Iso.refl X
  证明: rfl

@[simp]
-/
theorem eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X :=
  rfl

@[simp]
/--
theorem `eqToIso_trans` / 定理 `eqToIso_trans`

English:
theorem eqToIso_trans
  given: {X Y Z : C} (p : X = Y) (q : Y = Z)
  proof: by ext; simp

@[simp, to_dual none]

中文:
定理 eqToIso_trans
  条件: {X Y Z : C} (p : X = Y) (q : Y = Z)
  证明: by ext; simp

@[simp, to_dual none]
-/
theorem eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext; simp

@[simp, to_dual none]
/--
theorem `eqToHom_op` / 定理 `eqToHom_op`

English:
theorem eqToHom_op
  given: {X Y : C} (h : X = Y)
  statement: (eqToHom h).op = eqToHom (congr_arg op h.symm)
  proof: by
  cases h
  rfl

@[simp, to_dual none]

中文:
定理 eqToHom_op
  条件: {X Y : C} (h : X = Y)
  结论: (eqToHom h).op = eqToHom (congr_arg op h.symm)
  证明: by
  cases h
  rfl

@[simp, to_dual none]
-/
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) := by
  cases h
  rfl

@[simp, to_dual none]
/--
theorem `eqToHom_unop` / 定理 `eqToHom_unop`

English:
theorem eqToHom_unop
  given: {X Y : Cᵒᵖ} (h : X = Y)
  proof: by
  cases h
  rfl

@[to_dual none]

中文:
定理 eqToHom_unop
  条件: {X Y : Cᵒᵖ} (h : X = Y)
  证明: by
  cases h
  rfl

@[to_dual none]
-/
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) :
    (eqToHom h).unop = eqToHom (congr_arg unop h.symm) := by
  cases h
  rfl

@[to_dual none]
instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom

@[simp, to_dual none]
/--
theorem `inv_eqToHom` / 定理 `inv_eqToHom`

English:
theorem inv_eqToHom
  given: {X Y : C} (h : X = Y)
  statement: inv (eqToHom h) = eqToHom h.symm
  proof: by
  cat_disch

中文:
定理 inv_eqToHom
  条件: {X Y : C} (h : X = Y)
  结论: inv (eqToHom h) = eqToHom h.symm
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm := by
  cat_disch

variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
@[to_dual none]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X)
  proof: by
  match F, G with
  | mk F_obj _ _ _, mk G_obj _ _ _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f

@[to_dual none]

中文:
定理 ext
  结论: {F G : C ⥤ D} (h_obj : 对任意 X, F.obj X = G.obj X)
  证明: by
  match F, G with
  | mk F_obj _ _ _, mk G_obj _ _ _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f

@[to_dual none]

Depends on / 依赖: F_obj, G_obj, cat_disch, h_map, h_obj
-/
theorem ext {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by cat_disch) :
    F = G := by
  match F, G with
  | mk F_obj _ _ _, mk G_obj _ _ _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f

@[to_dual none]
/--
lemma `ext_of_iso` / 引理 `ext_of_iso`

English:
lemma ext_of_iso
  statement: {F G : C ⥤ D} (e : F ≅ G) (hobj : forall X, F.obj X = G.obj X)
  proof: Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y)]; rw [e.hom.naturality f]; rw [happ]; rw [happ]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id])

中文:
引理 ext_of_iso
  结论: {F G : C ⥤ D} (e : F ≅ G) (hobj : 对任意 X, F.obj X = G.obj X)
  证明: Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y)]; rw [e.hom.naturality f]; rw [happ]; rw [happ]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id])

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Functor, Functor.ext, cancel_mono, cat_disch, comp_id, e.hom.app, e.hom.naturality, eqToHom_refl, eqToHom_trans, naturality
-/
lemma ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : forall X, F.obj X = G.obj X)
    (happ : forall X, e.hom.app X = eqToHom (hobj X) := by cat_disch) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y)]; rw [e.hom.naturality f]; rw [happ]; rw [happ]; rw [Category.assoc]; rw [Category.assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.comp_id])

/-- Proving equality between functors using heterogeneous equality. -/
@[to_dual none]
/--
theorem `hext` / 定理 `hext`

English:
theorem hext
  statement: {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X)
  proof: Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 h_map _ _ f

中文:
定理 hext
  结论: {F G : C ⥤ D} (h_obj : 对任意 X, F.obj X = G.obj X)
  证明: Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 h_map _ _ f

Depends on / 依赖: Functor, Functor.ext, conj_eqToHom_iff_heq, h_map, h_obj
-/
theorem hext {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G :=
Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 h_map _ _ f

-- Using equalities between functors.
/--
theorem `congr_obj` / 定理 `congr_obj`

English:
theorem congr_obj
  given: {F G : C ⥤ D} (h : F = G) (X)
  statement: F.obj X = G.obj X
  proof: by rw [h]

@[to_dual none, reassoc]

中文:
定理 congr_obj
  条件: {F G : C ⥤ D} (h : F = G) (X)
  结论: F.obj X = G.obj X
  证明: by rw [h]

@[to_dual none, reassoc]
-/
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]

@[to_dual none, reassoc]
/--
theorem `congr_hom` / 定理 `congr_hom`

English:
theorem congr_hom
  given: {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y)
  proof: by
  subst h; simp

中文:
定理 congr_hom
  条件: {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y)
  证明: by
  subst h; simp
-/
theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h; simp

/--
theorem `congr_inv_of_congr_hom` / 定理 `congr_inv_of_congr_hom`

English:
theorem congr_inv_of_congr_hom
  statement: (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
  proof: by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]

中文:
定理 congr_inv_of_congr_hom
  结论: (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
  证明: by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_inv, IsIso.Iso.inv_hom, IsIso.inv_comp, c.retract_left.instIsSplitMonoI, instIsSplitMonoI, inv_comp, inv_eqToHom, inv_hom, map_inv, retract_left
-/
theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]

section HEq

-- Composition of functors and maps w.r.t. heq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

/--
theorem `map_comp_heq` / 定理 `map_comp_heq`

English:
theorem map_comp_heq
  statement: (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
  proof: by
  rw [F.map_comp]; rw [G.map_comp]
  congr

中文:
定理 map_comp_heq
  结论: (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
  证明: by
  rw [F.map_comp]; rw [G.map_comp]
  congr

Depends on / 依赖: F.map_comp, G.map_comp, c.retract_right.instIsSplitMonoI, instIsSplitMonoI, map_comp, retract_right
-/
theorem map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : F.map f ≍ G.map f) (hg : F.map g ≍ G.map g) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [F.map_comp]; rw [G.map_comp]
  congr

/--
theorem `map_comp_heq'` / 定理 `map_comp_heq'`

English:
theorem map_comp_heq'
  statement: (hobj : forall X : C, F.obj X = G.obj X)
  proof: by
  rw [Functor.hext hobj fun _ _ => hmap]

中文:
定理 map_comp_heq'
  结论: (hobj : 对任意 X : C, F.obj X = G.obj X)
  证明: by
  rw [Functor.hext hobj fun _ _ => hmap]

Depends on / 依赖: Functor, Functor.hext, c.retract_left.instIsSplitEpiR, instIsSplitEpiR, retract_left
-/
theorem map_comp_heq' (hobj : forall X : C, F.obj X = G.obj X)
    (hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [Functor.hext hobj fun _ _ => hmap]

/--
theorem `precomp_map_heq` / 定理 `precomp_map_heq`

English:
theorem precomp_map_heq
  statement: (H : E ⥤ C) (hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) {X Y : E}
  proof: hmap _

中文:
定理 precomp_map_heq
  结论: (H : E ⥤ C) (hmap : 对任意 {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) {X Y : E}
  证明: hmap _

Depends on / 依赖: c.retract_right.instIsSplitEpiR, instIsSplitEpiR, retract_right
-/
theorem precomp_map_heq (H : E ⥤ C) (hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) {X Y : E}
    (f : X ⟶ Y) : (H ⋙ F).map f ≍ (H ⋙ G).map f :=
  hmap _

/--
theorem `postcomp_map_heq` / 定理 `postcomp_map_heq`

English:
theorem postcomp_map_heq
  statement: (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
  proof: by
  dsimp
  congr

中文:
定理 postcomp_map_heq
  结论: (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
  证明: by
  dsimp
  congr
-/
theorem postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : F.map f ≍ G.map f) : (F ⋙ H).map f ≍ (G ⋙ H).map f := by
  dsimp
  congr

/--
theorem `postcomp_map_heq'` / 定理 `postcomp_map_heq'`

English:
theorem postcomp_map_heq'
  statement: (H : D ⥤ E) (hobj : forall X : C, F.obj X = G.obj X)
  proof: by rw [Functor.hext hobj fun _ _ => hmap]

中文:
定理 postcomp_map_heq'
  结论: (H : D ⥤ E) (hobj : 对任意 X : C, F.obj X = G.obj X)
  证明: by rw [Functor.hext hobj fun _ _ => hmap]

Depends on / 依赖: Functor, Functor.hext
-/
theorem postcomp_map_heq' (H : D ⥤ E) (hobj : forall X : C, F.obj X = G.obj X)
    (hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    (F ⋙ H).map f ≍ (G ⋙ H).map f := by rw [Functor.hext hobj fun _ _ => hmap]

/--
theorem `hcongr_hom` / 定理 `hcongr_hom`

English:
theorem hcongr_hom
  given: {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y)
  statement: F.map f ≍ G.map f
  proof: by
  rw [h]

中文:
定理 hcongr_hom
  条件: {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y)
  结论: F.map f ≍ G.map f
  证明: by
  rw [h]
-/
theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f ≍ G.map f := by
  rw [h]

end HEq

end Functor

/-- This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `attribute [local simp] eqToHom_map`, however.
-/
@[to_dual none]
/--
theorem `eqToHom_map` / 定理 `eqToHom_map`

English:
theorem eqToHom_map
  given: (F : C ⥤ D) {X Y : C} (p : X = Y)
  proof: by cases p; simp

@[to_dual none, reassoc (attr := simp)]

中文:
定理 eqToHom_map
  条件: (F : C ⥤ D) {X Y : C} (p : X = Y)
  证明: by cases p; simp

@[to_dual none, reassoc (attr := simp)]
-/
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p; simp

@[to_dual none, reassoc (attr := simp)]
/--
theorem `eqToHom_map_comp` / 定理 `eqToHom_map_comp`

English:
theorem eqToHom_map_comp
  given: (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z)
  proof: by cat_disch

中文:
定理 eqToHom_map_comp
  条件: (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q) := by cat_disch

/--
theorem `eqToIso_map` / 定理 `eqToIso_map`

English:
theorem eqToIso_map
  given: (F : C ⥤ D) {X Y : C} (p : X = Y)
  proof: by ext; cases p; simp

@[simp]

中文:
定理 eqToIso_map
  条件: (F : C ⥤ D) {X Y : C} (p : X = Y)
  证明: by ext; cases p; simp

@[simp]
-/
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext; cases p; simp

@[simp]
/--
theorem `eqToIso_map_trans` / 定理 `eqToIso_map_trans`

English:
theorem eqToIso_map_trans
  given: (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z)
  proof: by cat_disch

@[simp, to_dual none]

中文:
定理 eqToIso_map_trans
  条件: (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z)
  证明: by cat_disch

@[simp, to_dual none]

Depends on / 依赖: cat_disch
-/
theorem eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.mapIso (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q) := by cat_disch

@[simp, to_dual none]
/--
theorem `eqToHom_app` / 定理 `eqToHom_app`

English:
theorem eqToHom_app
  given: {F G : C ⥤ D} (h : F = G) (X : C)
  proof: by subst h; rfl

@[to_dual none]

中文:
定理 eqToHom_app
  条件: {F G : C ⥤ D} (h : F = G) (X : C)
  证明: by subst h; rfl

@[to_dual none]
-/
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h; rfl

@[to_dual none]
/--
theorem `NatTrans.congr` / 定理 `NatTrans.congr`

English:
theorem NatTrans.congr
  given: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y)
  proof: by
  rw [α.naturality_assoc]
  simp [eqToHom_map]

@[to_dual none]

中文:
定理 NatTrans.congr
  条件: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y)
  证明: by
  rw [α.naturality_assoc]
  simp [eqToHom_map]

@[to_dual none]

Depends on / 依赖: eqToHom_map, naturality_assoc
-/
theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) := by
  rw [α.naturality_assoc]
  simp [eqToHom_map]

@[to_dual none]
/--
theorem `eq_conj_eqToHom` / 定理 `eq_conj_eqToHom`

English:
theorem eq_conj_eqToHom
  given: {X Y : C} (f : X ⟶ Y)
  statement: f = eqToHom rfl ≫ f ≫ eqToHom rfl
  proof: by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]

@[to_dual none]

中文:
定理 eq_conj_eqToHom
  条件: {X Y : C} (f : X ⟶ Y)
  结论: f = eqToHom rfl ≫ f ≫ eqToHom rfl
  证明: by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]

@[to_dual none]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, eqToHom_refl, id_comp
-/
theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]

@[to_dual none]
/--
theorem `dcongr_arg` / 定理 `dcongr_arg`

English:
theorem dcongr_arg
  given: {ι : Type*} {F G : ι -> C} (α : forall i, F i ⟶ G i) {i j : ι} (h : i = j)
  proof: by
  subst h
  simp

@[simp]

中文:
定理 dcongr_arg
  条件: {ι : 类型} {F G : ι -> C} (α : 对任意 i, F i ⟶ G i) {i j : ι} (h : i = j)
  证明: by
  subst h
  simp

@[simp]
-/
theorem dcongr_arg {ι : Type*} {F G : ι -> C} (α : forall i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) := by
  subst h
  simp

@[simp]
/--
lemma `InducedCategory.eqToHom_hom` / 引理 `InducedCategory.eqToHom_hom`

English:
lemma InducedCategory.eqToHom_hom
  statement: {C D : Type*} [Category D] {F : C -> D}
  proof: by
  subst h
  rfl

@[simp]

中文:
引理 InducedCategory.eqToHom_hom
  结论: {C D : 类型} [Category D] {F : C -> D}
  证明: by
  subst h
  rfl

@[simp]
-/
lemma InducedCategory.eqToHom_hom {C D : Type*} [Category D] {F : C -> D}
    {X Y : InducedCategory D F} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
/--
lemma `ObjectProperty.eqToHom_hom` / 引理 `ObjectProperty.eqToHom_hom`

English:
lemma ObjectProperty.eqToHom_hom
  statement: {C : Type*} [Category C] {P : ObjectProperty C}
  proof: by
  subst h
  rfl

中文:
引理 ObjectProperty.eqToHom_hom
  结论: {C : 类型} [Category C] {P : Object命题erty C}
  证明: by
  subst h
  rfl
-/
lemma ObjectProperty.eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

/-- If `T ≃ D` is a bijection and `D` is a category, then
`InducedCategory D e` is equivalent to `D`. -/
@[simps]
/--
Definition of `Equivalence.induced` / `Equivalence.induced` 的定义

English:
definition Equivalence.induced
  signature: {T : Type*} (e : T ≃ D)
  body: inducedFunctor e
  inverse :=
    { obj := e.symm
      map f := InducedCategory.homMk (eqToHom (by simp) ≫ f ≫ eqToHom (by simp)) }
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

中文:
定义 Equivalence.induced
  签名: {T : 类型} (e : T ≃ D)
  定义体: inducedFunctor e
  inverse :=
    { obj := e.symm
      map f := InducedCategory.homMk (eqToHom (by simp) ≫ f ≫ eqToHom (by simp)) }
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

Depends on / 依赖: inducedFunctor
-/
def Equivalence.induced {T : Type*} (e : T ≃ D) :
    InducedCategory D e ≌ D where
  functor := inducedFunctor e
  inverse :=
    { obj := e.symm
      map f := InducedCategory.homMk (eqToHom (by simp) ≫ f ≫ eqToHom (by simp)) }
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

end CategoryTheory
