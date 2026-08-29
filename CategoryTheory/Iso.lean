/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure Iso` : a bundled isomorphism between two objects of a category;
- `class IsIso` : an unbundled version of `Iso`;
  note that `IsIso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[IsIso f]`
- `asIso` : convert from `IsIso` to `Iso` (noncomputable);
- `of_iso` : convert from `Iso` to `IsIso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notation

- `X ≅ Y` : same as `Iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `Iso.trans`

## Tags

category, category theory, isomorphism
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

universe v u

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Category

/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `CategoryTheory.Core` for the category with the same objects and isomorphisms playing
the role of morphisms. -/
@[stacks 0017, wikidata Q189112]
/--
Definition of `Iso` / `Iso` 的定义

English:
structure Iso
  parameters: {C : Type u} [Category.{v} C] (X Y : C)
  axioms and operations (4):
    - hom : X ⟶ Y
    - inv : Y ⟶ X
    - hom_inv_id : hom ≫ inv = 𝟙 X  [default: by cat_disch]
    - inv_hom_id : inv ≫ hom = 𝟙 Y  [default: by cat_disch]

中文:
结构 Iso
  参数: {C : 类型u} [Category.{v} C] (X Y : C)
  公理与运算 (4 个):
    - hom : X ⟶ Y
    - inv : Y ⟶ X
    - hom_inv_id : hom ≫ inv = 𝟙 X  [默认: by cat_disch]
    - inv_hom_id : inv ≫ hom = 𝟙 Y  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : X ⟶ Y
  /-- The backwards direction of an isomorphism. -/
  inv : Y ⟶ X
  /-- Composition of the two directions of an isomorphism is the identity on the source. -/
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  /-- Composition of the two directions of an isomorphism in reverse order
  is the identity on the target. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch

attribute [to_dual existing inv] Iso.hom
attribute [to_dual self] Iso.mk Iso.casesOn

attribute [reassoc +to_dual (attr := simp), grind =] Iso.hom_inv_id Iso.inv_hom_id

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅ " => Iso -- type as \cong or \iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

set_option linter.style.whitespace false in -- manual alignment is not recognised
set_option linter.existingAttributeWarning false in
@[ext, grind ext, to_dual ext_inv]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃α β
  statement: X ≅ Y⦄ (w : α.hom = β.hom) : α = β
  proof: suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _ = β.inv := by grind

中文:
定理 ext
  条件: ⦃α β
  结论: X ≅ Y⦄ (w : α.hom = β.hom) : α = β
  证明: suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _ = β.inv := by grind
-/
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _ = β.inv := by grind

/-- Inverse isomorphism. -/
@[symm, implicit_reducible]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (I : X ≅ Y)
  body: I.inv
  inv := I.hom

@[to_dual (attr := simp, grind =) symm_inv]

中文:
定义 symm
  签名: (I : X ≅ Y)
  定义体: I.inv
  inv := I.hom

@[to_dual (attr := simp, grind =) symm_inv]

Depends on / 依赖: I.inv
-/
def symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom

@[to_dual (attr := simp, grind =) symm_inv]
/--
theorem `symm_hom` / 定理 `symm_hom`

English:
theorem symm_hom
  given: (α : X ≅ Y)
  statement: α.symm.hom = α.inv
  proof: rfl

@[simp, grind =, to_dual self]

中文:
定理 symm_hom
  条件: (α : X ≅ Y)
  结论: α.symm.hom = α.inv
  证明: rfl

@[simp, grind =, to_dual self]
-/
theorem symm_hom (α : X ≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp, grind =, to_dual self]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  proof: rfl

@[simp, grind =]

中文:
定理 symm_mk
  条件: {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  证明: rfl

@[simp, grind =]

Depends on / 依赖: hom_inv_id, inv_hom_id
-/
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =
      { hom := inv, inv := hom, hom_inv_id := inv_hom_id, inv_hom_id := hom_inv_id } :=
  rfl

@[simp, grind =]
/--
theorem `symm_symm_eq` / 定理 `symm_symm_eq`

English:
theorem symm_symm_eq
  given: {X Y : C} (α : X ≅ Y)
  statement: α.symm.symm = α
  proof: rfl

中文:
定理 symm_symm_eq
  条件: {X Y : C} (α : X ≅ Y)
  结论: α.symm.symm = α
  证明: rfl
-/
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  given: {X Y : C}
  statement: Function.Bijective (symm : (X ≅ Y) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]

中文:
定理 symm_bijective
  条件: {X Y : C}
  结论: Function.Bijective (symm : (X ≅ Y) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm_eq
-/
theorem symm_bijective {X Y : C} : Function.Bijective (symm : (X ≅ Y) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]
/--
theorem `symm_eq_iff` / 定理 `symm_eq_iff`

English:
theorem symm_eq_iff
  given: {X Y : C} {α β : X ≅ Y}
  statement: α.symm = β.symm ↔ α = β
  proof: symm_bijective.injective.eq_iff

中文:
定理 symm_eq_iff
  条件: {X Y : C} {α β : X ≅ Y}
  结论: α.symm = β.symm ↔ α = β
  证明: symm_bijective.injective.eq_iff

Depends on / 依赖: eq_iff, injective, symm_bijective, symm_bijective.injective.eq_iff
-/
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  symm_bijective.injective.eq_iff

/--
theorem `nonempty_iso_symm` / 定理 `nonempty_iso_symm`

English:
theorem nonempty_iso_symm
  given: (X Y : C)
  statement: Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X)
  proof: ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

中文:
定理 nonempty_iso_symm
  条件: (X Y : C)
  结论: Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X)
  证明: ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

Depends on / 依赖: h.some.symm
-/
theorem nonempty_iso_symm (X Y : C) : Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X) :=
  ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

/-- Identity isomorphism. -/
@[refl, simps (attr := grind =), implicit_reducible]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : C)
  body: 𝟙 X
  inv := 𝟙 X

中文:
定义 refl
  签名: (X : C)
  定义体: 𝟙 X
  inv := 𝟙 X
-/
def refl (X : C) : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

attribute [to_dual existing refl_inv] refl_hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (X ≅ X)
  body: ⟨Iso.refl X⟩

中文:
实例 :
  签名: Inhabited (X ≅ X)
  定义体: ⟨Iso.refl X⟩

Depends on / 依赖: Iso.refl
-/
instance : Inhabited (X ≅ X) := ⟨Iso.refl X⟩

/--
theorem `nonempty_iso_refl` / 定理 `nonempty_iso_refl`

English:
theorem nonempty_iso_refl
  given: (X : C)
  statement: Nonempty (X ≅ X)
  proof: ⟨default⟩

@[simp, grind =]

中文:
定理 nonempty_iso_refl
  条件: (X : C)
  结论: Nonempty (X ≅ X)
  证明: ⟨default⟩

@[simp, grind =]
-/
theorem nonempty_iso_refl (X : C) : Nonempty (X ≅ X) := ⟨default⟩

@[simp, grind =]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  given: (X : C)
  statement: (Iso.refl X).symm = Iso.refl X
  proof: rfl

中文:
定理 refl_symm
  条件: (X : C)
  结论: (Iso.refl X).symm = Iso.refl X
  证明: rfl
-/
theorem refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X := rfl

/-- Composition of two isomorphisms -/
@[simps (attr := grind =), implicit_reducible]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (α : X ≅ Y) (β : Y ≅ Z)
  body: α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

中文:
定义 trans
  签名: (α : X ≅ Y) (β : Y ≅ Z)
  定义体: α.hom ≫ β.hom
  inv := β.inv ≫ α.inv
-/
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

attribute [to_dual existing trans_inv] trans_hom

@[simps]
/--
Instance `instTransIso` / 实例 `instTransIso`

English:
instance instTransIso
  signature: : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  body: trans

中文:
实例 instTransIso
  签名: : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  定义体: trans
-/
instance instTransIso : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  trans := trans

/-- Notation for composition of isomorphisms. -/
infixr:80 " ≪≫ " => Iso.trans -- type as `\ll \gg`.

-- Annotating this with `@[grind =]` triggers a run-away chain of `Category.assoc` instantiations.
-- Hopefully this can be restored when `grind` has support for associative/commutative operations,
-- or direct support for category theory.
@[simp, to_dual self]
/--
theorem `trans_mk` / 定理 `trans_mk`

English:
theorem trans_mk
  statement: {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  proof: rfl

@[simp, grind _=_]

中文:
定理 trans_mk
  结论: {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  证明: rfl

@[simp, grind _=_]
-/
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
    (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans ⟨hom, inv, hom_inv_id, inv_hom_id⟩ ⟨hom', inv', hom_inv_id', inv_hom_id'⟩ =
     ⟨hom ≫ hom', inv' ≫ inv, hom_inv_id'', inv_hom_id''⟩ :=
  rfl

@[simp, grind _=_]
/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  given: (α : X ≅ Y) (β : Y ≅ Z)
  statement: (α ≪≫ β).symm = β.symm ≪≫ α.symm
  proof: rfl

@[simp, grind _=_]

中文:
定理 trans_symm
  条件: (α : X ≅ Y) (β : Y ≅ Z)
  结论: (α ≪≫ β).symm = β.symm ≪≫ α.symm
  证明: rfl

@[simp, grind _=_]
-/
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl

@[simp, grind _=_]
/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z')
  proof: by
  ext; simp only [trans_hom, Category.assoc]

@[simp]

中文:
定理 trans_assoc
  条件: {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z')
  证明: by
  ext; simp only [trans_hom, Category.assoc]

@[simp]

Depends on / 依赖: Category, Category.assoc, trans_hom
-/
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
    (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ := by
  ext; simp only [trans_hom, Category.assoc]

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (α : X ≅ Y)
  statement: Iso.refl X ≪≫ α = α
  proof: by ext; apply Category.id_comp

@[simp]

中文:
定理 refl_trans
  条件: (α : X ≅ Y)
  结论: Iso.refl X ≪≫ α = α
  证明: by ext; apply Category.id_comp

@[simp]

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
theorem refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α := by ext; apply Category.id_comp

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (α : X ≅ Y)
  statement: α ≪≫ Iso.refl Y = α
  proof: by ext; apply Category.comp_id

@[simp]

中文:
定理 trans_refl
  条件: (α : X ≅ Y)
  结论: α ≪≫ Iso.refl Y = α
  证明: by ext; apply Category.comp_id

@[simp]

Depends on / 依赖: Category, Category.comp_id, comp_id
-/
theorem trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α := by ext; apply Category.comp_id

@[simp]
/--
theorem `symm_self_id` / 定理 `symm_self_id`

English:
theorem symm_self_id
  given: (α : X ≅ Y)
  statement: α.symm ≪≫ α = Iso.refl Y
  proof: ext α.inv_hom_id

@[simp]

中文:
定理 symm_self_id
  条件: (α : X ≅ Y)
  结论: α.symm ≪≫ α = Iso.refl Y
  证明: ext α.inv_hom_id

@[simp]

Depends on / 依赖: inv_hom_id
-/
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y :=
  ext α.inv_hom_id

@[simp]
/--
theorem `self_symm_id` / 定理 `self_symm_id`

English:
theorem self_symm_id
  given: (α : X ≅ Y)
  statement: α ≪≫ α.symm = Iso.refl X
  proof: ext α.hom_inv_id

@[simp]

中文:
定理 self_symm_id
  条件: (α : X ≅ Y)
  结论: α ≪≫ α.symm = Iso.refl X
  证明: ext α.hom_inv_id

@[simp]

Depends on / 依赖: hom_inv_id
-/
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X :=
  ext α.hom_inv_id

@[simp]
/--
theorem `symm_self_id_assoc` / 定理 `symm_self_id_assoc`

English:
theorem symm_self_id_assoc
  given: (α : X ≅ Y) (β : Y ≅ Z)
  statement: α.symm ≪≫ α ≪≫ β = β
  proof: by
  rw [← trans_assoc]; rw [symm_self_id]; rw [refl_trans]

@[simp]

中文:
定理 symm_self_id_assoc
  条件: (α : X ≅ Y) (β : Y ≅ Z)
  结论: α.symm ≪≫ α ≪≫ β = β
  证明: by
  rw [← trans_assoc]; rw [symm_self_id]; rw [refl_trans]

@[simp]

Depends on / 依赖: refl_trans, symm_self_id, trans_assoc
-/
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc]; rw [symm_self_id]; rw [refl_trans]

@[simp]
/--
theorem `self_symm_id_assoc` / 定理 `self_symm_id_assoc`

English:
theorem self_symm_id_assoc
  given: (α : X ≅ Y) (β : X ≅ Z)
  statement: α ≪≫ α.symm ≪≫ β = β
  proof: by
  rw [← trans_assoc]; rw [self_symm_id]; rw [refl_trans]

@[to_dual none]

中文:
定理 self_symm_id_assoc
  条件: (α : X ≅ Y) (β : X ≅ Z)
  结论: α ≪≫ α.symm ≪≫ β = β
  证明: by
  rw [← trans_assoc]; rw [self_symm_id]; rw [refl_trans]

@[to_dual none]

Depends on / 依赖: refl_trans, self_symm_id, trans_assoc
-/
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc]; rw [self_symm_id]; rw [refl_trans]

@[to_dual none]
/--
theorem `inv_comp_eq` / 定理 `inv_comp_eq`

English:
theorem inv_comp_eq
  given: (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z}
  statement: α.inv ≫ f = g ↔ f = α.hom ≫ g
  proof: ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]

中文:
定理 inv_comp_eq
  条件: (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z}
  结论: α.inv ≫ f = g ↔ f = α.hom ≫ g
  证明: ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]

Depends on / 依赖: H.symm
-/
theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
/--
theorem `eq_inv_comp` / 定理 `eq_inv_comp`

English:
theorem eq_inv_comp
  given: (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z}
  statement: g = α.inv ≫ f ↔ α.hom ≫ g = f
  proof: (inv_comp_eq α.symm).symm

@[to_dual none]

中文:
定理 eq_inv_comp
  条件: (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z}
  结论: g = α.inv ≫ f ↔ α.hom ≫ g = f
  证明: (inv_comp_eq α.symm).symm

@[to_dual none]

Depends on / 依赖: inv_comp_eq
-/
theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
  (inv_comp_eq α.symm).symm

@[to_dual none]
/--
theorem `comp_inv_eq` / 定理 `comp_inv_eq`

English:
theorem comp_inv_eq
  given: (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X}
  statement: f ≫ α.inv = g ↔ f = g ≫ α.hom
  proof: ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]

中文:
定理 comp_inv_eq
  条件: (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X}
  结论: f ≫ α.inv = g ↔ f = g ≫ α.hom
  证明: ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]

Depends on / 依赖: H.symm
-/
theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
/--
theorem `eq_comp_inv` / 定理 `eq_comp_inv`

English:
theorem eq_comp_inv
  given: (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X}
  statement: g = f ≫ α.inv ↔ g ≫ α.hom = f
  proof: (comp_inv_eq α.symm).symm

@[to_dual none]

中文:
定理 eq_comp_inv
  条件: (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X}
  结论: g = f ≫ α.inv ↔ g ≫ α.hom = f
  证明: (comp_inv_eq α.symm).symm

@[to_dual none]

Depends on / 依赖: comp_inv_eq
-/
theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
  (comp_inv_eq α.symm).symm

@[to_dual none]
/--
theorem `inv_eq_inv` / 定理 `inv_eq_inv`

English:
theorem inv_eq_inv
  given: (f g : X ≅ Y)
  statement: f.inv = g.inv ↔ f.hom = g.hom
  proof: have : forall {X Y : C} (f g : X ≅ Y), f.hom = g.hom -> f.inv = g.inv := fun f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

@[to_dual comp_inv_eq_id]

中文:
定理 inv_eq_inv
  条件: (f g : X ≅ Y)
  结论: f.inv = g.inv ↔ f.hom = g.hom
  证明: have : forall {X Y : C} (f g : X ≅ Y), f.hom = g.hom -> f.inv = g.inv := fun f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

@[to_dual comp_inv_eq_id]

Depends on / 依赖: f.hom, f.inv, f.symm, g.hom, g.inv, g.symm
-/
theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
  have : forall {X Y : C} (f g : X ≅ Y), f.hom = g.hom -> f.inv = g.inv := fun f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

@[to_dual comp_inv_eq_id]
/--
theorem `hom_comp_eq_id` / 定理 `hom_comp_eq_id`

English:
theorem hom_comp_eq_id
  given: (α : X ≅ Y) {f : Y ⟶ X}
  statement: α.hom ≫ f = 𝟙 X ↔ f = α.inv
  proof: by
  rw [← eq_inv_comp]; rw [comp_id]

@[to_dual inv_comp_eq_id]

中文:
定理 hom_comp_eq_id
  条件: (α : X ≅ Y) {f : Y ⟶ X}
  结论: α.hom ≫ f = 𝟙 X ↔ f = α.inv
  证明: by
  rw [← eq_inv_comp]; rw [comp_id]

@[to_dual inv_comp_eq_id]

Depends on / 依赖: comp_id, eq_inv_comp
-/
theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp]; rw [comp_id]

@[to_dual inv_comp_eq_id]
/--
theorem `comp_hom_eq_id` / 定理 `comp_hom_eq_id`

English:
theorem comp_hom_eq_id
  given: (α : X ≅ Y) {f : Y ⟶ X}
  statement: f ≫ α.hom = 𝟙 Y ↔ f = α.inv
  proof: by
  rw [← eq_comp_inv]; rw [id_comp]

@[to_dual inv_eq_hom]

中文:
定理 comp_hom_eq_id
  条件: (α : X ≅ Y) {f : Y ⟶ X}
  结论: f ≫ α.hom = 𝟙 Y ↔ f = α.inv
  证明: by
  rw [← eq_comp_inv]; rw [id_comp]

@[to_dual inv_eq_hom]

Depends on / 依赖: eq_comp_inv, id_comp
-/
theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv]; rw [id_comp]

@[to_dual inv_eq_hom]
/--
theorem `hom_eq_inv` / 定理 `hom_eq_inv`

English:
theorem hom_eq_inv
  given: (α : X ≅ Y) (β : Y ≅ X)
  statement: α.hom = β.inv ↔ β.hom = α.inv
  proof: by
  rw [← symm_inv]; rw [inv_eq_inv α.symm β]; rw [eq_comm]
  rfl

中文:
定理 hom_eq_inv
  条件: (α : X ≅ Y) (β : Y ≅ X)
  结论: α.hom = β.inv ↔ β.hom = α.inv
  证明: by
  rw [← symm_inv]; rw [inv_eq_inv α.symm β]; rw [eq_comm]
  rfl

Depends on / 依赖: eq_comm, inv_eq_inv, symm_inv
-/
theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv := by
  rw [← symm_inv]; rw [inv_eq_inv α.symm β]; rw [eq_comm]
  rfl

attribute [local grind] Function.LeftInverse Function.RightInverse

/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
@[implicit_reducible, to_dual (attr := simps) homFromEquiv
/-- The bijection `(X ⟶ Z) ≃ (Y ⟶ Z)` induced by `α : X ≅ Y`. -/]
/--
Definition of `homToEquiv` / `homToEquiv` 的定义

English:
definition homToEquiv
  signature: (α : X ≅ Y) {Z : C}
  body: f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 homToEquiv
  签名: (α : X ≅ Y) {Z : C}
  定义体: f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch

end Iso

set_option linter.translate.warnInvalid false in
/-- The `IsIso` typeclass expresses that a morphism is invertible.

Given a morphism `f` with `IsIso f`, one can view `f` as an isomorphism via `asIso f` and get
the inverse using `inv f`. -/
@[to_dual self]
/--
Definition of `IsIso` / `IsIso` 的定义

English:
class IsIso
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - out : exists inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

中文:
类 IsIso
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - out : 存在 inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y
-/
class IsIso (f : X ⟶ Y) : Prop where
  /-- The existence of an inverse morphism. -/
  out : exists inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- `IsIso.mk'` is the dual of `IsIso.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/--
theorem `IsIso.mk'` / 定理 `IsIso.mk'`

English:
theorem IsIso.mk'
  given: {f : Y ⟶ X} (out : exists inv : X ⟶ Y, inv ≫ f = 𝟙 X ∧ f ≫ inv = 𝟙 Y)
  statement: IsIso f where
  proof: by simp_all only [and_comm]

中文:
定理 IsIso.mk'
  条件: {f : Y ⟶ X} (out : 存在 inv : X ⟶ Y, inv ≫ f = 𝟙 X ∧ f ≫ inv = 𝟙 Y)
  结论: IsIso f where
  证明: by simp_all only [and_comm]

Depends on / 依赖: and_comm
-/
theorem IsIso.mk' {f : Y ⟶ X} (out : exists inv : X ⟶ Y, inv ≫ f = 𝟙 X ∧ f ≫ inv = 𝟙 Y) : IsIso f where
  out := by simp_all only [and_comm]

/-- The inverse of a morphism `f` when we have `[IsIso f]`. -/
@[to_dual self, no_expose]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (f : X ⟶ Y) [I : IsIso f]
  body: Classical.choose I.1

中文:
定义 inv
  签名: (f : X ⟶ Y) [I : IsIso f]
  定义体: Classical.choose I.1

Depends on / 依赖: Classical, Classical.choose
-/
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X :=
  Classical.choose I.1

namespace IsIso

/--
theorem `hom_inv_id` / 定理 `hom_inv_id`

English:
theorem hom_inv_id
  given: (f : X ⟶ Y) [I : IsIso f]
  statement: f ≫ inv f = 𝟙 X
  proof: (Classical.choose_spec I.1).left

@[to_dual existing (attr := reassoc (attr := simp), grind =) hom_inv_id]

中文:
定理 hom_inv_id
  条件: (f : X ⟶ Y) [I : IsIso f]
  结论: f ≫ inv f = 𝟙 X
  证明: (Classical.choose_spec I.1).left

@[to_dual existing (attr := reassoc (attr := simp), grind =) hom_inv_id]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left

@[to_dual existing (attr := reassoc (attr := simp), grind =) hom_inv_id]
/--
theorem `inv_hom_id` / 定理 `inv_hom_id`

English:
theorem inv_hom_id
  given: (f : X ⟶ Y) [I : IsIso f]
  statement: inv f ≫ f = 𝟙 Y
  proof: (Classical.choose_spec I.1).right

中文:
定理 inv_hom_id
  条件: (f : X ⟶ Y) [I : IsIso f]
  结论: inv f ≫ f = 𝟙 Y
  证明: (Classical.choose_spec I.1).right

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right

end IsIso

/--
Instance `Iso.isIso_hom` / 实例 `Iso.isIso_hom`

English:
instance Iso.isIso_hom
  signature: (e : X ≅ Y)
  body: ⟨e.inv, by simp only [hom_inv_id], by simp⟩

@[to_dual existing isIso_hom]

中文:
实例 Iso.isIso_hom
  签名: (e : X ≅ Y)
  定义体: ⟨e.inv, by simp only [hom_inv_id], by simp⟩

@[to_dual existing isIso_hom]

Depends on / 依赖: e.inv, hom_inv_id
-/
instance Iso.isIso_hom (e : X ≅ Y) : IsIso e.hom :=
  ⟨e.inv, by simp only [hom_inv_id], by simp⟩

@[to_dual existing isIso_hom]
/--
Instance `Iso.isIso_inv` / 实例 `Iso.isIso_inv`

English:
instance Iso.isIso_inv
  signature: (e : X ≅ Y)
  body: e.symm.isIso_hom

中文:
实例 Iso.isIso_inv
  签名: (e : X ≅ Y)
  定义体: e.symm.isIso_hom

Depends on / 依赖: e.symm.isIso_hom, isIso_hom
-/
instance Iso.isIso_inv (e : X ≅ Y) : IsIso e.inv := e.symm.isIso_hom

open IsIso

/-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `X ≅ Y`. -/
@[to_dual asIso' /-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `Y ≅ X`. -/]
/--
Definition of `asIso` / `asIso` 的定义

English:
definition asIso
  signature: (f : X ⟶ Y) [IsIso f]
  body: ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[to_dual (attr := simp) asIso'_hom]

中文:
定义 asIso
  签名: (f : X ⟶ Y) [IsIso f]
  定义体: ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[to_dual (attr := simp) asIso'_hom]

Depends on / 依赖: hom_inv_id, inv_hom_id
-/
noncomputable def asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[to_dual (attr := simp) asIso'_hom]
/--
theorem `asIso_hom` / 定理 `asIso_hom`

English:
theorem asIso_hom
  given: (f : X ⟶ Y) [IsIso f]
  statement: (asIso f).hom = f
  proof: rfl

@[to_dual (attr := simp) asIso'_inv]

中文:
定理 asIso_hom
  条件: (f : X ⟶ Y) [IsIso f]
  结论: (asIso f).hom = f
  证明: rfl

@[to_dual (attr := simp) asIso'_inv]
-/
theorem asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).hom = f :=
  rfl

@[to_dual (attr := simp) asIso'_inv]
/--
theorem `asIso_inv` / 定理 `asIso_inv`

English:
theorem asIso_inv
  given: (f : X ⟶ Y) [IsIso f]
  statement: (asIso f).inv = inv f
  proof: rfl

中文:
定理 asIso_inv
  条件: (f : X ⟶ Y) [IsIso f]
  结论: (asIso f).inv = inv f
  证明: rfl
-/
theorem asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f :=
  rfl

namespace IsIso

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) epi_of_iso (f : X ⟶ Y) [IsIso f] : Epi f where
  left_cancellation g h w := by
    rw [← IsIso.inv_hom_id_assoc f g]; rw [w]; rw [IsIso.inv_hom_id_assoc f h]

@[aesop apply safe (rule_sets := [CategoryTheory]), grind ←=, to_dual inv_eq_of_inv_hom_id]
/--
theorem `inv_eq_of_hom_inv_id` / 定理 `inv_eq_of_hom_inv_id`

English:
theorem inv_eq_of_hom_inv_id
  given: {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X)
  proof: by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual eq_inv_of_inv_hom_id]

中文:
定理 inv_eq_of_hom_inv_id
  条件: {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X)
  证明: by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual eq_inv_of_inv_hom_id]

Depends on / 依赖: hom_inv_id
-/
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    inv f = g := by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual eq_inv_of_inv_hom_id]
/--
theorem `eq_inv_of_hom_inv_id` / 定理 `eq_inv_of_hom_inv_id`

English:
theorem eq_inv_of_hom_inv_id
  given: {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X)
  proof: (inv_eq_of_hom_inv_id hom_inv_id).symm

中文:
定理 eq_inv_of_hom_inv_id
  条件: {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X)
  证明: (inv_eq_of_hom_inv_id hom_inv_id).symm

Depends on / 依赖: hom_inv_id, inv_eq_of_hom_inv_id
-/
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: (X : C)
  body: ⟨⟨𝟙 X, by simp⟩⟩

中文:
实例 id
  签名: (X : C)
  定义体: ⟨⟨𝟙 X, by simp⟩⟩
-/
instance id (X : C) : IsIso (𝟙 X) := ⟨⟨𝟙 X, by simp⟩⟩

variable {f : X ⟶ Y} {h : Y ⟶ Z}

@[to_dual self]
/--
Instance `inv_isIso` / 实例 `inv_isIso`

English:
instance inv_isIso
  signature: [IsIso f]
  body: (asIso f).isIso_inv

@[to_dual self (reorder := X Z, f h, 8 9)]

中文:
实例 inv_isIso
  签名: [IsIso f]
  定义体: (asIso f).isIso_inv

@[to_dual self (reorder := X Z, f h, 8 9)]

Depends on / 依赖: isIso_inv
-/
instance inv_isIso [IsIso f] : IsIso (inv f) :=
  (asIso f).isIso_inv

@[to_dual self (reorder := X Z, f h, 8 9)]
/--
Instance `comp_isIso` / 实例 `comp_isIso`

English:
instance comp_isIso
  signature: [IsIso f] [IsIso h]
  body: (asIso f ≪≫ asIso h).isIso_hom

中文:
实例 comp_isIso
  签名: [IsIso f] [IsIso h]
  定义体: (asIso f ≪≫ asIso h).isIso_hom

Depends on / 依赖: isIso_hom
-/
instance comp_isIso [IsIso f] [IsIso h] : IsIso (f ≫ h) :=
  (asIso f ≪≫ asIso h).isIso_hom

/--
The composition of isomorphisms is an isomorphism. Here the arguments of type `IsIso` are
explicit, to make this easier to use with the `refine` tactic, for instance.
-/
@[to_dual self (reorder := X Z, f h, 8 9)]
/--
lemma `comp_isIso'` / 引理 `comp_isIso'`

English:
lemma comp_isIso'
  given: (_ : IsIso f) (_ : IsIso h)
  statement: IsIso (f ≫ h)
  proof: inferInstance

@[simp]

中文:
引理 comp_isIso'
  条件: (_ : IsIso f) (_ : IsIso h)
  结论: IsIso (f ≫ h)
  证明: inferInstance

@[simp]
-/
lemma comp_isIso' (_ : IsIso f) (_ : IsIso h) : IsIso (f ≫ h) := inferInstance

@[simp]
/--
theorem `inv_id` / 定理 `inv_id`

English:
theorem inv_id
  statement: inv (𝟙 X) = 𝟙 X
  proof: by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, reassoc, push, to_dual self]

中文:
定理 inv_id
  结论: inv (𝟙 X) = 𝟙 X
  证明: by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, reassoc, push, to_dual self]

Depends on / 依赖: inv_eq_of_hom_inv_id
-/
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, reassoc, push, to_dual self]
/--
theorem `inv_comp` / 定理 `inv_comp`

English:
theorem inv_comp
  given: [IsIso f] [IsIso h]
  statement: inv (f ≫ h) = inv h ≫ inv f
  proof: by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, push, to_dual self]

中文:
定理 inv_comp
  条件: [IsIso f] [IsIso h]
  结论: inv (f ≫ h) = inv h ≫ inv f
  证明: by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, push, to_dual self]

Depends on / 依赖: inv_eq_of_hom_inv_id
-/
theorem inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, push, to_dual self]
/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  given: [IsIso f]
  statement: inv (inv f) = f
  proof: by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp, push) inv_hom]

中文:
定理 inv_inv
  条件: [IsIso f]
  结论: inv (inv f) = f
  证明: by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp, push) inv_hom]

Depends on / 依赖: inv_eq_of_hom_inv_id
-/
theorem inv_inv [IsIso f] : inv (inv f) = f := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp, push) inv_hom]
/--
theorem `Iso.inv_inv` / 定理 `Iso.inv_inv`

English:
theorem Iso.inv_inv
  given: (f : X ≅ Y)
  statement: inv f.inv = f.hom
  proof: by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp) comp_inv_eq]

中文:
定理 Iso.inv_inv
  条件: (f : X ≅ Y)
  结论: inv f.inv = f.hom
  证明: by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp) comp_inv_eq]

Depends on / 依赖: inv_eq_of_hom_inv_id
-/
theorem Iso.inv_inv (f : X ≅ Y) : inv f.inv = f.hom := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp) comp_inv_eq]
/--
theorem `inv_comp_eq` / 定理 `inv_comp_eq`

English:
theorem inv_comp_eq
  given: (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z}
  statement: inv α ≫ f = g ↔ f = α ≫ g
  proof: (asIso α).inv_comp_eq

@[to_dual (attr := simp) eq_comp_inv]

中文:
定理 inv_comp_eq
  条件: (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z}
  结论: inv α ≫ f = g ↔ f = α ≫ g
  证明: (asIso α).inv_comp_eq

@[to_dual (attr := simp) eq_comp_inv]

Depends on / 依赖: inv_comp_eq
-/
theorem inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (asIso α).inv_comp_eq

@[to_dual (attr := simp) eq_comp_inv]
/--
theorem `eq_inv_comp` / 定理 `eq_inv_comp`

English:
theorem eq_inv_comp
  given: (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z}
  statement: g = inv α ≫ f ↔ α ≫ g = f
  proof: (asIso α).eq_inv_comp

@[to_dual (reorder := f g) of_isIso_comp_right]

中文:
定理 eq_inv_comp
  条件: (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z}
  结论: g = inv α ≫ f ↔ α ≫ g = f
  证明: (asIso α).eq_inv_comp

@[to_dual (reorder := f g) of_isIso_comp_right]

Depends on / 依赖: eq_inv_comp
-/
theorem eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (asIso α).eq_inv_comp

@[to_dual (reorder := f g) of_isIso_comp_right]
/--
theorem `of_isIso_comp_left` / 定理 `of_isIso_comp_left`

English:
theorem of_isIso_comp_left
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)]
  proof: by
  rw [← id_comp g]; rw [← inv_hom_id f]; rw [assoc]
  infer_instance

@[to_dual of_isIso_fac_right]

中文:
定理 of_isIso_comp_left
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)]
  证明: by
  rw [← id_comp g]; rw [← inv_hom_id f]; rw [assoc]
  infer_instance

@[to_dual of_isIso_fac_right]

Depends on / 依赖: id_comp, infer_instance, inv_hom_id
-/
theorem of_isIso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] :
    IsIso g := by
  rw [← id_comp g]; rw [← inv_hom_id f]; rw [assoc]
  infer_instance

@[to_dual of_isIso_fac_right]
/--
theorem `of_isIso_fac_left` / 定理 `of_isIso_fac_left`

English:
theorem of_isIso_fac_left
  statement: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f]
  proof: by
  rw [← w] at hh
  exact of_isIso_comp_left f g

中文:
定理 of_isIso_fac_left
  结论: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f]
  证明: by
  rw [← w] at hh
  exact of_isIso_comp_left f g

Depends on / 依赖: of_isIso_comp_left
-/
theorem of_isIso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f]
    [hh : IsIso h] (w : f ≫ g = h) : IsIso g := by
  rw [← w] at hh
  exact of_isIso_comp_left f g

end IsIso

@[to_dual (attr := simp) (reorder := f g) isIso_comp_right_iff]
/--
theorem `isIso_comp_left_iff` / 定理 `isIso_comp_left_iff`

English:
theorem isIso_comp_left_iff
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  proof: ⟨fun _ => IsIso.of_isIso_comp_left f g, fun _ => inferInstance⟩

中文:
定理 isIso_comp_left_iff
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  证明: ⟨fun _ => IsIso.of_isIso_comp_left f g, fun _ => inferInstance⟩

Depends on / 依赖: IsIso.of_isIso_comp_left, of_isIso_comp_left
-/
theorem isIso_comp_left_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsIso (f ≫ g) ↔ IsIso g :=
  ⟨fun _ => IsIso.of_isIso_comp_left f g, fun _ => inferInstance⟩

open IsIso

@[to_dual self]
/--
theorem `eq_of_inv_eq_inv` / 定理 `eq_of_inv_eq_inv`

English:
theorem eq_of_inv_eq_inv
  given: {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g)
  statement: f = g
  proof: by
  apply (cancel_epi (inv f)).1
  rw [inv_hom_id]; rw [p]; rw [inv_hom_id]

@[to_dual self]

中文:
定理 eq_of_inv_eq_inv
  条件: {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g)
  结论: f = g
  证明: by
  apply (cancel_epi (inv f)).1
  rw [inv_hom_id]; rw [p]; rw [inv_hom_id]

@[to_dual self]

Depends on / 依赖: cancel_epi, inv_hom_id
-/
theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f = g := by
  apply (cancel_epi (inv f)).1
  rw [inv_hom_id]; rw [p]; rw [inv_hom_id]

@[to_dual self]
/--
theorem `IsIso.inv_eq_inv` / 定理 `IsIso.inv_eq_inv`

English:
theorem IsIso.inv_eq_inv
  given: {f g : X ⟶ Y} [IsIso f] [IsIso g]
  statement: inv f = inv g ↔ f = g
  proof: Iso.inv_eq_inv (asIso f) (asIso g)

@[to_dual comp_hom_eq_id]

中文:
定理 IsIso.inv_eq_inv
  条件: {f g : X ⟶ Y} [IsIso f] [IsIso g]
  结论: inv f = inv g ↔ f = g
  证明: Iso.inv_eq_inv (asIso f) (asIso g)

@[to_dual comp_hom_eq_id]

Depends on / 依赖: Iso.inv_eq_inv, inv_eq_inv
-/
theorem IsIso.inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] : inv f = inv g ↔ f = g :=
  Iso.inv_eq_inv (asIso f) (asIso g)

@[to_dual comp_hom_eq_id]
/--
theorem `hom_comp_eq_id` / 定理 `hom_comp_eq_id`

English:
theorem hom_comp_eq_id
  given: (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X}
  statement: g ≫ f = 𝟙 X ↔ f = inv g
  proof: (asIso g).hom_comp_eq_id

@[to_dual comp_inv_eq_id]

中文:
定理 hom_comp_eq_id
  条件: (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X}
  结论: g ≫ f = 𝟙 X ↔ f = inv g
  证明: (asIso g).hom_comp_eq_id

@[to_dual comp_inv_eq_id]

Depends on / 依赖: hom_comp_eq_id
-/
theorem hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (asIso g).hom_comp_eq_id

@[to_dual comp_inv_eq_id]
/--
theorem `inv_comp_eq_id` / 定理 `inv_comp_eq_id`

English:
theorem inv_comp_eq_id
  given: (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y}
  statement: inv g ≫ f = 𝟙 Y ↔ f = g
  proof: (asIso g).inv_comp_eq_id

@[to_dual isIso_of_comp_hom_eq_id]

中文:
定理 inv_comp_eq_id
  条件: (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y}
  结论: inv g ≫ f = 𝟙 Y ↔ f = g
  证明: (asIso g).inv_comp_eq_id

@[to_dual isIso_of_comp_hom_eq_id]

Depends on / 依赖: inv_comp_eq_id
-/
theorem inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g :=
  (asIso g).inv_comp_eq_id

@[to_dual isIso_of_comp_hom_eq_id]
/--
theorem `isIso_of_hom_comp_eq_id` / 定理 `isIso_of_hom_comp_eq_id`

English:
theorem isIso_of_hom_comp_eq_id
  given: (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X)
  statement: IsIso f
  proof: by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance

中文:
定理 isIso_of_hom_comp_eq_id
  条件: (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X)
  结论: IsIso f
  证明: by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance

Depends on / 依赖: hom_comp_eq_id, infer_instance
-/
theorem isIso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X) : IsIso f := by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance

/--
lemma `isIso_iff_of_thin` / 引理 `isIso_iff_of_thin`

English:
lemma isIso_iff_of_thin
  given: [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y)
  statement: IsIso f ↔ Nonempty (Y ⟶ X)
  proof: ⟨fun _ => ⟨inv f⟩, fun g => ⟨g.some, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

中文:
引理 isIso_iff_of_thin
  条件: [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y)
  结论: IsIso f ↔ Nonempty (Y ⟶ X)
  证明: ⟨fun _ => ⟨inv f⟩, fun g => ⟨g.some, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, g.some
-/
lemma isIso_iff_of_thin [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Nonempty (Y ⟶ X) :=
  ⟨fun _ => ⟨inv f⟩, fun g => ⟨g.some, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

namespace Iso

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
/--
theorem `inv_ext` / 定理 `inv_ext`

English:
theorem inv_ext
  given: {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X)
  statement: f.inv = g
  proof: ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]

中文:
定理 inv_ext
  条件: {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X)
  结论: f.inv = g
  证明: ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]

Depends on / 依赖: hom_comp_eq_id, hom_inv_id
-/
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
/--
theorem `inv_ext'` / 定理 `inv_ext'`

English:
theorem inv_ext'
  given: {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X)
  statement: g = f.inv
  proof: (hom_comp_eq_id f).1 hom_inv_id

中文:
定理 inv_ext'
  条件: {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X)
  结论: g = f.inv
  证明: (hom_comp_eq_id f).1 hom_inv_id

Depends on / 依赖: hom_comp_eq_id, hom_inv_id
-/
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


@[to_dual (attr := simp) (reorder := f g' g) cancel_iso_inv_right]
/--
theorem `cancel_iso_hom_left` / 定理 `cancel_iso_hom_left`

English:
theorem cancel_iso_hom_left
  given: {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z)
  proof: by
  simp only [cancel_epi]

@[to_dual (attr := simp) (reorder := f f' g) cancel_iso_inv_left]

中文:
定理 cancel_iso_hom_left
  条件: {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z)
  证明: by
  simp only [cancel_epi]

@[to_dual (attr := simp) (reorder := f f' g) cancel_iso_inv_left]

Depends on / 依赖: cancel_epi
-/
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
    f.hom ≫ g = f.hom ≫ g' ↔ g = g' := by
  simp only [cancel_epi]

@[to_dual (attr := simp) (reorder := f f' g) cancel_iso_inv_left]
/--
theorem `cancel_iso_hom_right` / 定理 `cancel_iso_hom_right`

English:
theorem cancel_iso_hom_right
  given: {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z)
  proof: by
  simp only [cancel_mono]

中文:
定理 cancel_iso_hom_right
  条件: {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z)
  证明: by
  simp only [cancel_mono]

Depends on / 依赖: cancel_mono
-/
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
    f ≫ g.hom = f' ≫ g.hom ↔ f = f' := by
  simp only [cancel_mono]

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp, to_dual none]
/--
theorem `cancel_iso_hom_right_assoc` / 定理 `cancel_iso_hom_right_assoc`

English:
theorem cancel_iso_hom_right_assoc
  statement: {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  proof: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

中文:
定理 cancel_iso_hom_right_assoc
  结论: {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  证明: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Y ≅ Z) : f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/--
theorem `cancel_iso_inv_right_assoc` / 定理 `cancel_iso_inv_right_assoc`

English:
theorem cancel_iso_inv_right_assoc
  statement: {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  proof: by
  simp only [← Category.assoc, cancel_mono]

中文:
定理 cancel_iso_inv_right_assoc
  结论: {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  证明: by
  simp only [← Category.assoc, cancel_mono]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Z ≅ Y) : f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

section

variable {D : Type*} [Category* D] {X Y : C} (e : X ≅ Y)

@[reassoc +to_dual (attr := simp), grind =]
/--
lemma `map_hom_inv_id` / 引理 `map_hom_inv_id`

English:
lemma map_hom_inv_id
  given: (F : C ⥤ D)
  proof: by grind

@[reassoc +to_dual (attr := simp), grind =]

中文:
引理 map_hom_inv_id
  条件: (F : C ⥤ D)
  证明: by grind

@[reassoc +to_dual (attr := simp), grind =]
-/
lemma map_hom_inv_id (F : C ⥤ D) :
    F.map e.hom ≫ F.map e.inv = 𝟙 _ := by grind

@[reassoc +to_dual (attr := simp), grind =]
/--
lemma `map_inv_hom_id` / 引理 `map_inv_hom_id`

English:
lemma map_inv_hom_id
  given: (F : C ⥤ D)
  proof: by grind

中文:
引理 map_inv_hom_id
  条件: (F : C ⥤ D)
  证明: by grind

Depends on / 依赖: Category, hasPullbacks_of_hasWidePullbacks
-/
lemma map_inv_hom_id (F : C ⥤ D) :
    F.map e.inv ≫ F.map e.hom = 𝟙 _ := by grind

end

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}
variable [Category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps, implicit_reducible]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (F : C ⥤ D) {X Y : C} (i : X ≅ Y)
  body: F.map i.hom
  inv := F.map i.inv

中文:
定义 mapIso
  签名: (F : C ⥤ D) {X Y : C} (i : X ≅ Y)
  定义体: F.map i.hom
  inv := F.map i.inv

Depends on / 依赖: Category, F.map, hasPushouts_of_hasWidePushouts, i.hom
-/
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv

attribute [to_dual existing mapIso_inv] mapIso_hom

@[simp]
/--
theorem `mapIso_symm` / 定理 `mapIso_symm`

English:
theorem mapIso_symm
  given: (F : C ⥤ D) {X Y : C} (i : X ≅ Y)
  statement: F.mapIso i.symm = (F.mapIso i).symm
  proof: rfl

@[simp]

中文:
定理 mapIso_symm
  条件: (F : C ⥤ D) {X Y : C} (i : X ≅ Y)
  结论: F.mapIso i.symm = (F.mapIso i).symm
  证明: rfl

@[simp]
-/
theorem mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl

@[simp]
/--
theorem `mapIso_trans` / 定理 `mapIso_trans`

English:
theorem mapIso_trans
  given: (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z)
  proof: by
  ext; apply Functor.map_comp

@[simp]

中文:
定理 mapIso_trans
  条件: (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z)
  证明: by
  ext; apply Functor.map_comp

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp
-/
theorem mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j := by
  ext; apply Functor.map_comp

@[simp]
/--
theorem `mapIso_refl` / 定理 `mapIso_refl`

English:
theorem mapIso_refl
  given: (F : C ⥤ D) (X : C)
  statement: F.mapIso (Iso.refl X) = Iso.refl (F.obj X)
  proof: Iso.ext F.map_id X

@[to_dual self]

中文:
定理 mapIso_refl
  条件: (F : C ⥤ D) (X : C)
  结论: F.mapIso (Iso.refl X) = Iso.refl (F.obj X)
  证明: Iso.ext F.map_id X

@[to_dual self]

Depends on / 依赖: F.map_id, Iso.ext, map_id
-/
theorem mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
Iso.ext F.map_id X

@[to_dual self]
/--
Instance `map_isIso` / 实例 `map_isIso`

English:
instance map_isIso
  signature: (F : C ⥤ D) (f : X ⟶ Y) [IsIso f]
  body: (F.mapIso (asIso f)).isIso_hom

@[simp, push ←, to_dual self]

中文:
实例 map_isIso
  签名: (F : C ⥤ D) (f : X ⟶ Y) [IsIso f]
  定义体: (F.mapIso (asIso f)).isIso_hom

@[simp, push ←, to_dual self]

Depends on / 依赖: F.mapIso, isIso_hom, mapIso
-/
instance map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  (F.mapIso (asIso f)).isIso_hom

@[simp, push ←, to_dual self]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: F.map (inv f) = inv (F.map f)
  proof: by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

@[to_dual (attr := reassoc) map_inv_hom]

中文:
定理 map_inv
  条件: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f]
  结论: F.map (inv f) = inv (F.map f)
  证明: by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

@[to_dual (attr := reassoc) map_inv_hom]

Depends on / 依赖: F.map_comp, eq_inv_of_hom_inv_id, map_comp
-/
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) := by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

@[to_dual (attr := reassoc) map_inv_hom]
/--
theorem `map_hom_inv` / 定理 `map_hom_inv`

English:
theorem map_hom_inv
  given: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f]
  proof: by simp

中文:
定理 map_hom_inv
  条件: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f]
  证明: by simp
-/
theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by simp

-- The following two lemmas are needed to generate good elementwise lemmas
@[reassoc]
/--
theorem `map_hom_inv'` / 定理 `map_hom_inv'`

English:
theorem map_hom_inv'
  given: (F : C ⥤ D) {X Y : C} (f : X ≅ Y)
  proof: by simp

@[reassoc]

中文:
定理 map_hom_inv'
  条件: (F : C ⥤ D) {X Y : C} (f : X ≅ Y)
  证明: by simp

@[reassoc]
-/
theorem map_hom_inv' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) :
    F.map f.hom ≫ F.map f.inv = 𝟙 (F.obj X) := by simp

@[reassoc]
/--
theorem `map_inv_hom'` / 定理 `map_inv_hom'`

English:
theorem map_inv_hom'
  given: (F : C ⥤ D) {X Y : C} (f : X ≅ Y)
  proof: by simp

中文:
定理 map_inv_hom'
  条件: (F : C ⥤ D) {X Y : C} (f : X ≅ Y)
  证明: by simp
-/
theorem map_inv_hom' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) :
    F.map f.inv ≫ F.map f.hom = 𝟙 (F.obj Y) := by simp

end Functor

end CategoryTheory
