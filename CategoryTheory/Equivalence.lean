/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.Data.Int.Notation
/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphism of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `Equivalence`: bundled (half-)adjoint equivalences of categories
* `Functor.EssSurj`: type class on a functor `F` containing the data of the preimages
  and the isomorphisms `F.obj (preimage d) ≅ d`.
* `Functor.IsEquivalence`: type class on a functor `F` which is full, faithful and
  essentially surjective.

## Main results

* `Equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `isEquivalence_iff_of_iso`: when `F` and `G` are isomorphic functors,
  `F` is an equivalence iff `G` is.
* `Functor.asEquivalenceFunctor`: construction of an equivalence of categories from
  a functor `F` which satisfies the property `F.IsEquivalence` (i.e. `F` is full, faithful
  and essentially surjective).

## Notation

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- An equivalence of categories.

We define an equivalence between `C` and `D`, with notation `C ≌ D`, as a half-adjoint equivalence:
a pair of functors `F : C ⥤ D` and `G : D ⥤ C` with a unit `η : 𝟭 C ≅ F ⋙ G` and counit
`ε : G ⋙ F ≅ 𝟭 D`, such that the natural isomorphisms `η` and `ε` satisfy the triangle law for
`F`: namely, `Fη ≫ εF = 𝟙 F`. Or, in other words, the composite `F` ⟶ `F ⋙ G ⋙ F` ⟶ `F` is the
identity.

In `unit_inverse_comp`, we show that this is sufficient to establish a full adjoint
equivalence. I.e., the composite `G` ⟶ `G ⋙ F ⋙ G` ⟶ `G` is also the identity.

The triangle equation `functor_unitIso_comp` is written as a family of equalities between
morphisms. It is more complicated if we write it as an equality of natural transformations, because
then we would either have to insert natural transformations like `F ⟶ F𝟭` or abuse defeq. -/
@[ext, stacks 001J]
/--
Definition of `Equivalence` / `Equivalence` 的定义

English:
structure Equivalence
  parameters: (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]
  (no additional axioms)

中文:
结构 等价
  参数: (C : 类型u₁) (D : 类型u₂) [范畴.{v₁} C] [范畴.{v₂} D]
  (无附加公理)

Depends on / 依赖: cat_disch
-/
structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  /-- The forwards direction of an equivalence. -/
  functor : C ⥤ D
  /-- The backwards direction of an equivalence. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is isomorphic to the identity. -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is isomorphic to the identity. -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  /-- The triangle law for the forwards direction of an equivalence: the unit and counit compose
  to the identity when whiskered along the forwards direction.

  We state this as a family of equalities among morphisms instead of an equality of natural
  transformations to avoid abusing defeq or inserting natural transformations like `F ⟶ F𝟭`. -/
  functor_unitIso_comp (X : C) :
    dsimp% functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by cat_disch

@[inherit_doc Equivalence]
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

@[to_dual existing functor_unitIso_comp]
/--
theorem `counitIso_functor_comp` / 定理 `counitIso_functor_comp`

English:
theorem counitIso_functor_comp
  given: (e : C ≌ D) (X : C)
  proof: by
  simpa [functor_unitIso_comp] using Iso.inv_eq_inv
    (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X)) (Iso.refl _)

中文:
定理 counitIso_functor_comp
  条件: (e : C ≌ D) (X : C)
  证明: by
  simpa [functor_unitIso_comp] using Iso.inv_eq_inv
    (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X)) (Iso.refl _)

Depends on / 依赖: Iso.inv_eq_inv, Iso.refl, counitIso, e.counitIso.app, e.functor.mapIso, e.functor.obj, e.unitIso.app, functor, functor_unitIso_comp, inv_eq_inv, mapIso, unitIso
-/
theorem counitIso_functor_comp (e : C ≌ D) (X : C) :
    dsimp% e.counitIso.inv.app (e.functor.obj X) ≫ e.functor.map (e.unitIso.inv.app X) =
      𝟙 (e.functor.obj X) := by
  simpa [functor_unitIso_comp] using Iso.inv_eq_inv
    (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X)) (Iso.refl _)

/-- `Equivalence.mk'` is the dual of `Equivalence.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk']
/--
Definition of `mk''` / `mk''` 的定义

English:
abbreviation mk''
  body: by
    simpa [functor_unitIso_comp] using Iso.inv_eq_inv
      (functor.mapIso (unitIso.app X) ≪≫ counitIso.app (functor.obj X)) (Iso.refl _)

中文:
缩写 mk''
  定义体: by
    simpa [functor_unitIso_comp] using Iso.inv_eq_inv
      (functor.mapIso (unitIso.app X) ≪≫ counitIso.app (functor.obj X)) (Iso.refl _)

Depends on / 依赖: Iso.inv_eq_inv, Iso.refl, counitIso, counitIso.app, functor, functor.mapIso, functor.obj, functor_unitIso_comp, inv_eq_inv, mapIso, unitIso, unitIso.app
-/
abbrev mk''
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (functor : C ⥤ D) (inverse : D ⥤ C)
    (unitIso : 𝟭 C ≅ functor ⋙ inverse) (counitIso : inverse ⋙ functor ≅ 𝟭 D)
    (functor_unitIso_comp : dsimp% forall (X : C),
      counitIso.inv.app (functor.obj X) ≫ functor.map (unitIso.inv.app X) = 𝟙 (functor.obj X)) :
    Equivalence C D where
  functor; inverse; unitIso; counitIso
  functor_unitIso_comp X := by
    simpa [functor_unitIso_comp] using Iso.inv_eq_inv
      (functor.mapIso (unitIso.app X) ≪≫ counitIso.app (functor.obj X)) (Iso.refl _)


/-- The unit of an equivalence of categories. -/
@[to_dual unitInv /-- The inverse of the unit of an equivalence of categories. -/]
/--
Definition of `unit` / `unit` 的定义

English:
abbreviation unit
  signature: (e : C ≌ D)
  body: e.unitIso.hom

中文:
缩写 unit
  签名: (e : C ≌ D)
  定义体: e.unitIso.hom

Depends on / 依赖: HasBinaryBiproducts, e.unitIso.hom, hasBinaryProducts_of_hasBinaryBiproducts, unitIso
-/
abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse :=
  e.unitIso.hom

/-- The counit of an equivalence of categories. -/
@[to_dual counitInv /-- The inverse of the counit of an equivalence of categories. -/]
/--
Definition of `counit` / `counit` 的定义

English:
abbreviation counit
  signature: (e : C ≌ D)
  body: e.counitIso.hom

@[reassoc +to_dual]

中文:
缩写 counit
  签名: (e : C ≌ D)
  定义体: e.counitIso.hom

@[reassoc +to_dual]

Depends on / 依赖: HasBinaryBiproducts, counitIso, e.counitIso.hom, hasBinaryCoproducts_of_hasBinaryBiproducts
-/
abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom

@[reassoc +to_dual]
/--
lemma `unitIso_hom_inv_id_app` / 引理 `unitIso_hom_inv_id_app`

English:
lemma unitIso_hom_inv_id_app
  given: (e : C ≌ D) (X : C)
  proof: by
  simp

@[reassoc +to_dual]

中文:
引理 unitIso_hom_inv_id_app
  条件: (e : C ≌ D) (X : C)
  证明: by
  simp

@[reassoc +to_dual]
-/
lemma unitIso_hom_inv_id_app (e : C ≌ D) (X : C) :
    dsimp% e.unit.app X ≫ e.unitInv.app X = 𝟙 X := by
  simp

@[reassoc +to_dual]
/--
lemma `unitIso_inv_hom_id_app` / 引理 `unitIso_inv_hom_id_app`

English:
lemma unitIso_inv_hom_id_app
  given: (e : C ≌ D) (X : C)
  proof: by
  simp

@[reassoc +to_dual]

中文:
引理 unitIso_inv_hom_id_app
  条件: (e : C ≌ D) (X : C)
  证明: by
  simp

@[reassoc +to_dual]
-/
lemma unitIso_inv_hom_id_app (e : C ≌ D) (X : C) :
    dsimp% e.unitInv.app X ≫ e.unit.app X = 𝟙 _ := by
  simp

@[reassoc +to_dual]
/--
lemma `counitIso_hom_inv_id_app` / 引理 `counitIso_hom_inv_id_app`

English:
lemma counitIso_hom_inv_id_app
  given: (e : C ≌ D) (Y : D)
  proof: by
  simp

@[reassoc +to_dual]

中文:
引理 counitIso_hom_inv_id_app
  条件: (e : C ≌ D) (Y : D)
  证明: by
  simp

@[reassoc +to_dual]
-/
lemma counitIso_hom_inv_id_app (e : C ≌ D) (Y : D) :
    dsimp% e.counit.app Y ≫ e.counitInv.app Y = 𝟙 _ := by
  simp

@[reassoc +to_dual]
/--
lemma `counitIso_inv_hom_id_app` / 引理 `counitIso_inv_hom_id_app`

English:
lemma counitIso_inv_hom_id_app
  given: (e : C ≌ D) (Y : D)
  proof: by
  simp

中文:
引理 counitIso_inv_hom_id_app
  条件: (e : C ≌ D) (Y : D)
  证明: by
  simp
-/
lemma counitIso_inv_hom_id_app (e : C ≌ D) (Y : D) :
    dsimp% e.counitInv.app Y ≫ e.counit.app Y = 𝟙 Y := by
  simp

section CategoryStructure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (C ≌ D)
  body: e.functor ⟶ f.functor
  id e := 𝟙 e.functor
  comp {a b c} f g := (f ≫ g : a.functor ⟶ _)

中文:
实例 :
  签名: 范畴 (C ≌ D)
  定义体: e.functor ⟶ f.functor
  id e := 𝟙 e.functor
  comp {a b c} f g := (f ≫ g : a.functor ⟶ _)

Depends on / 依赖: e.functor, f.functor, functor
-/
instance : Category (C ≌ D) where
  Hom e f := e.functor ⟶ f.functor
  id e := 𝟙 e.functor
  comp {a b c} f g := (f ≫ g : a.functor ⟶ _)

/-- Promote a natural transformation `e.functor ⟶ f.functor` to a morphism in `C ≌ D`. -/
@[to_dual self]
/--
Definition of `mkHom` / `mkHom` 的定义

English:
definition mkHom
  signature: {e f : C ≌ D} (η : e.functor ⟶ f.functor)
  body: η

中文:
定义 mkHom
  签名: {e f : C ≌ D} (η : e.functor ⟶ f.functor)
  定义体: η
-/
def mkHom {e f : C ≌ D} (η : e.functor ⟶ f.functor) : e ⟶ f := η

/-- Recover a natural transformation between `e.functor` and `f.functor` from the data of
a morphism `e ⟶ f`. -/
@[to_dual self]
/--
Definition of `asNatTrans` / `asNatTrans` 的定义

English:
definition asNatTrans
  signature: {e f : C ≌ D} (η : e ⟶ f)
  body: η

@[ext, to_dual self]

中文:
定义 as自然数Trans
  签名: {e f : C ≌ D} (η : e ⟶ f)
  定义体: η

@[ext, to_dual self]
-/
def asNatTrans {e f : C ≌ D} (η : e ⟶ f) : e.functor ⟶ f.functor := η

@[ext, to_dual self]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β)
  statement: α = β
  proof: h

@[simp, to_dual self]

中文:
引理 hom_ext
  条件: {e f : C ≌ D} {α β : e ⟶ f} (h : as自然数Trans α = as自然数Trans β)
  结论: α = β
  证明: h

@[simp, to_dual self]
-/
lemma hom_ext {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β) : α = β := h

@[simp, to_dual self]
/--
lemma `mkHom_asNatTrans` / 引理 `mkHom_asNatTrans`

English:
lemma mkHom_asNatTrans
  given: {e f : C ≌ D} (η : e.functor ⟶ f.functor)
  proof: rfl

@[simp, to_dual self]

中文:
引理 mkHom_as自然数Trans
  条件: {e f : C ≌ D} (η : e.functor ⟶ f.functor)
  证明: rfl

@[simp, to_dual self]
-/
lemma mkHom_asNatTrans {e f : C ≌ D} (η : e.functor ⟶ f.functor) :
    mkHom (asNatTrans η) = η :=
  rfl

@[simp, to_dual self]
/--
lemma `asNatTrans_mkHom` / 引理 `asNatTrans_mkHom`

English:
lemma asNatTrans_mkHom
  given: {e f : C ≌ D} (η : e ⟶ f)
  proof: rfl

@[simp]

中文:
引理 as自然数Trans_mkHom
  条件: {e f : C ≌ D} (η : e ⟶ f)
  证明: rfl

@[simp]
-/
lemma asNatTrans_mkHom {e f : C ≌ D} (η : e ⟶ f) :
    asNatTrans (mkHom η) = η :=
  rfl

@[simp]
/--
lemma `id_asNatTrans` / 引理 `id_asNatTrans`

English:
lemma id_asNatTrans
  given: {e : C ≌ D}
  statement: asNatTrans (𝟙 e) = 𝟙 _
  proof: rfl

@[simp, to_dual self, reassoc]

中文:
引理 id_as自然数Trans
  条件: {e : C ≌ D}
  结论: as自然数Trans (𝟙 e) = 𝟙 _
  证明: rfl

@[simp, to_dual self, reassoc]
-/
lemma id_asNatTrans {e : C ≌ D} : asNatTrans (𝟙 e) = 𝟙 _ := rfl

@[simp, to_dual self, reassoc]
/--
lemma `comp_asNatTrans` / 引理 `comp_asNatTrans`

English:
lemma comp_asNatTrans
  given: {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g)
  proof: rfl

@[simp]

中文:
引理 comp_as自然数Trans
  条件: {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g)
  证明: rfl

@[simp]
-/
lemma comp_asNatTrans {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g) :
    asNatTrans (α ≫ β) = asNatTrans α ≫ asNatTrans β :=
  rfl

@[simp]
/--
lemma `mkHom_id_functor` / 引理 `mkHom_id_functor`

English:
lemma mkHom_id_functor
  given: {e : C ≌ D}
  statement: mkHom (𝟙 e.functor) = 𝟙 e
  proof: rfl

@[simp, to_dual self, reassoc]

中文:
引理 mkHom_id_functor
  条件: {e : C ≌ D}
  结论: mkHom (𝟙 e.functor) = 𝟙 e
  证明: rfl

@[simp, to_dual self, reassoc]
-/
lemma mkHom_id_functor {e : C ≌ D} : mkHom (𝟙 e.functor) = 𝟙 e := rfl

@[simp, to_dual self, reassoc]
/--
lemma `mkHom_comp` / 引理 `mkHom_comp`

English:
lemma mkHom_comp
  given: {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor)
  proof: rfl

中文:
引理 mkHom_comp
  条件: {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor)
  证明: rfl
-/
lemma mkHom_comp {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor) :
    mkHom (α ≫ β) = mkHom α ≫ mkHom β :=
  rfl

/-- Construct an isomorphism in `C ≌ D` from a natural isomorphism between the functors
of the equivalences. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {e f : C ≌ D} (η : e.functor ≅ f.functor)
  body: mkHom η.hom
  inv := mkHom η.inv

中文:
定义 mkIso
  签名: {e f : C ≌ D} (η : e.functor ≅ f.functor)
  定义体: mkHom η.hom
  inv := mkHom η.inv
-/
def mkIso {e f : C ≌ D} (η : e.functor ≅ f.functor) : e ≅ f where
  hom := mkHom η.hom
  inv := mkHom η.inv

attribute [to_dual existing mkIso_inv] mkIso_hom

variable (C D) in
/-- The `functor` functor that sends an equivalence of categories to its functor. -/
@[simps!]
/--
Definition of `functorFunctor` / `functorFunctor` 的定义

English:
definition functorFunctor
  signature: : (C ≌ D) ⥤ C ⥤ D where
  body: f.functor
  map α := asNatTrans α

中文:
定义 functorFunctor
  签名: : (C ≌ D) ⥤ C ⥤ D where
  定义体: f.functor
  map α := asNatTrans α

Depends on / 依赖: f.functor, functor
-/
def functorFunctor : (C ≌ D) ⥤ C ⥤ D where
  obj f := f.functor
  map α := asNatTrans α

end CategoryStructure

/-! While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/

@[simp, to_dual none]
/--
theorem `Equivalence_mk'_unit` / 定理 `Equivalence_mk'_unit`

English:
theorem Equivalence_mk'_unit
  given: (functor inverse unit_iso counit_iso f)
  proof: rfl

@[simp, to_dual none]

中文:
定理 Equivalence_mk'_unit
  条件: (functor inverse unit_iso counit_iso f)
  证明: rfl

@[simp, to_dual none]
-/
theorem Equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom :=
  rfl

@[simp, to_dual none]
/--
theorem `Equivalence_mk'_counit` / 定理 `Equivalence_mk'_counit`

English:
theorem Equivalence_mk'_counit
  given: (functor inverse unit_iso counit_iso f)
  proof: rfl

@[simp, to_dual none]

中文:
定理 Equivalence_mk'_counit
  条件: (functor inverse unit_iso counit_iso f)
  证明: rfl

@[simp, to_dual none]
-/
theorem Equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom :=
  rfl

@[simp, to_dual none]
/--
theorem `Equivalence_mk'_unitInv` / 定理 `Equivalence_mk'_unitInv`

English:
theorem Equivalence_mk'_unitInv
  given: (functor inverse unit_iso counit_iso f)
  proof: rfl

@[simp, to_dual none]

中文:
定理 Equivalence_mk'_unitInv
  条件: (functor inverse unit_iso counit_iso f)
  证明: rfl

@[simp, to_dual none]
-/
theorem Equivalence_mk'_unitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl

@[simp, to_dual none]
/--
theorem `Equivalence_mk'_counitInv` / 定理 `Equivalence_mk'_counitInv`

English:
theorem Equivalence_mk'_counitInv
  given: (functor inverse unit_iso counit_iso f)
  proof: rfl

@[to_dual (attr := reassoc) counitInv_naturality]

中文:
定理 Equivalence_mk'_counitInv
  条件: (functor inverse unit_iso counit_iso f)
  证明: rfl

@[to_dual (attr := reassoc) counitInv_naturality]
-/
theorem Equivalence_mk'_counitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl

@[to_dual (attr := reassoc) counitInv_naturality]
/--
theorem `counit_naturality` / 定理 `counit_naturality`

English:
theorem counit_naturality
  given: (e : C ≌ D) {X Y : D} (f : X ⟶ Y)
  proof: e.counit.naturality f

@[to_dual (attr := reassoc) unitInv_naturality]

中文:
定理 counit_naturality
  条件: (e : C ≌ D) {X Y : D} (f : X ⟶ Y)
  证明: e.counit.naturality f

@[to_dual (attr := reassoc) unitInv_naturality]

Depends on / 依赖: counit, e.counit.naturality, naturality
-/
theorem counit_naturality (e : C ≌ D) {X Y : D} (f : X ⟶ Y) :
    dsimp% e.functor.map (e.inverse.map f) ≫ e.counit.app Y = e.counit.app X ≫ f :=
  e.counit.naturality f

@[to_dual (attr := reassoc) unitInv_naturality]
/--
theorem `unit_naturality` / 定理 `unit_naturality`

English:
theorem unit_naturality
  given: (e : C ≌ D) {X Y : C} (f : X ⟶ Y)
  proof: (e.unit.naturality f).symm

@[to_dual (attr := reassoc (attr := simp)) counitInv_functor_comp]

中文:
定理 unit_naturality
  条件: (e : C ≌ D) {X Y : C} (f : X ⟶ Y)
  证明: (e.unit.naturality f).symm

@[to_dual (attr := reassoc (attr := simp)) counitInv_functor_comp]

Depends on / 依赖: e.unit.naturality, naturality
-/
theorem unit_naturality (e : C ≌ D) {X Y : C} (f : X ⟶ Y) :
    dsimp% e.unit.app X ≫ e.inverse.map (e.functor.map f) = f ≫ e.unit.app Y :=
  (e.unit.naturality f).symm

@[to_dual (attr := reassoc (attr := simp)) counitInv_functor_comp]
/--
theorem `functor_unit_comp` / 定理 `functor_unit_comp`

English:
theorem functor_unit_comp
  given: (e : C ≌ D) (X : C)
  proof: e.functor_unitIso_comp X

@[to_dual counitInv_app_functor]

中文:
定理 functor_unit_comp
  条件: (e : C ≌ D) (X : C)
  证明: e.functor_unitIso_comp X

@[to_dual counitInv_app_functor]

Depends on / 依赖: e.functor_unitIso_comp, functor_unitIso_comp
-/
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    dsimp% e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
  e.functor_unitIso_comp X

@[to_dual counitInv_app_functor]
/--
theorem `counit_app_functor` / 定理 `counit_app_functor`

English:
theorem counit_app_functor
  given: (e : C ≌ D) (X : C)
  proof: by
  simpa using Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)) (f := e.counit.app _)

中文:
定理 counit_app_functor
  条件: (e : C ≌ D) (X : C)
  证明: by
  simpa using Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)) (f := e.counit.app _)

Depends on / 依赖: Iso.hom_comp_eq_id, counit, e.counit.app, e.functor.mapIso, e.unitIso.app, functor, hom_comp_eq_id, mapIso, unitIso
-/
theorem counit_app_functor (e : C ≌ D) (X : C) :
    e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X) := by
  simpa using Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)) (f := e.counit.app _)

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[to_dual (attr := reassoc (attr := simp)) inverse_counitInv_comp]
/--
theorem `unit_inverse_comp` / 定理 `unit_inverse_comp`

English:
theorem unit_inverse_comp
  given: (e : C ≌ D) (Y : D)
  proof: by
  rw [← id_comp (e.inverse.map _)]; rw [← map_id e.inverse]; rw [← counitInv_functor_comp]; rw [map_comp]
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _))]; rw [Iso.app_hom]; rw [Iso.app_inv]
  slice_lhs 2 3 => rw [← e.unit_naturality]
  slice_lhs 1 2 => rw [← e.unit_naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [← map_comp e.inverse]
    dsimp
    rw [e.counit_naturality]; rw [e.counitIso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 2 3 =>
    dsimp only [Functor.mapIso_inv, Iso.app_inv]
    rw [← map_comp e.inverse]; rw [← e.counitInv_naturality]; rw [map_comp]
  slice_lhs 3 4 => rw [e.unitInv_naturality]
  slice_lhs 4 5 =>
    rw [← map_comp e.inverse]; rw [← map_comp e.functor]; rw [e.unitIso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [map_id]; rw [map_id]
  rw [id_comp]
  slice_lhs 3 4 => rw [← e.unitInv_naturality]
  slice_lhs 2 3 =>
    rw [← map_comp e.inverse]; rw [e.counitInv_naturality]; rw [e.counitIso.hom_inv_id_app]
  simp

@[to_dual unitInv_app_inverse]

中文:
定理 unit_inverse_comp
  条件: (e : C ≌ D) (Y : D)
  证明: by
  rw [← id_comp (e.inverse.map _)]; rw [← map_id e.inverse]; rw [← counitInv_functor_comp]; rw [map_comp]
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _))]; rw [Iso.app_hom]; rw [Iso.app_inv]
  slice_lhs 2 3 => rw [← e.unit_naturality]
  slice_lhs 1 2 => rw [← e.unit_naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [← map_comp e.inverse]
    dsimp
    rw [e.counit_naturality]; rw [e.counitIso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 2 3 =>
    dsimp only [Functor.mapIso_inv, Iso.app_inv]
    rw [← map_comp e.inverse]; rw [← e.counitInv_naturality]; rw [map_comp]
  slice_lhs 3 4 => rw [e.unitInv_naturality]
  slice_lhs 4 5 =>
    rw [← map_comp e.inverse]; rw [← map_comp e.functor]; rw [e.unitIso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [map_id]; rw [map_id]
  rw [id_comp]
  slice_lhs 3 4 => rw [← e.unitInv_naturality]
  slice_lhs 2 3 =>
    rw [← map_comp e.inverse]; rw [e.counitInv_naturality]; rw [e.counitIso.hom_inv_id_app]
  simp

@[to_dual unitInv_app_inverse]

Depends on / 依赖: Functor, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.hom_inv_id_assoc, app_hom, app_inv, counitInv_functor_comp, counitIso, e.counitIso.app, e.functor.map, e.inverse, e.inverse.map, e.inverse.mapIso, e.unitInv.app, e.unitIso.app, e.unit_naturality, functor, hom_inv_id_assoc, id_comp
-/
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    dsimp% e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _)]; rw [← map_id e.inverse]; rw [← counitInv_functor_comp]; rw [map_comp]
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _))]; rw [Iso.app_hom]; rw [Iso.app_inv]
  slice_lhs 2 3 => rw [← e.unit_naturality]
  slice_lhs 1 2 => rw [← e.unit_naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [← map_comp e.inverse]
    dsimp
    rw [e.counit_naturality]; rw [e.counitIso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 2 3 =>
    dsimp only [Functor.mapIso_inv, Iso.app_inv]
    rw [← map_comp e.inverse]; rw [← e.counitInv_naturality]; rw [map_comp]
  slice_lhs 3 4 => rw [e.unitInv_naturality]
  slice_lhs 4 5 =>
    rw [← map_comp e.inverse]; rw [← map_comp e.functor]; rw [e.unitIso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [map_id]; rw [map_id]
  rw [id_comp]
  slice_lhs 3 4 => rw [← e.unitInv_naturality]
  slice_lhs 2 3 =>
    rw [← map_comp e.inverse]; rw [e.counitInv_naturality]; rw [e.counitIso.hom_inv_id_app]
  simp

@[to_dual unitInv_app_inverse]
/--
theorem `unit_app_inverse` / 定理 `unit_app_inverse`

English:
theorem unit_app_inverse
  given: (e : C ≌ D) (Y : D)
  proof: by
  simpa using Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)) (f := e.unit.app _)

@[to_dual none, reassoc, simp]

中文:
定理 unit_app_inverse
  条件: (e : C ≌ D) (Y : D)
  证明: by
  simpa using Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)) (f := e.unit.app _)

@[to_dual none, reassoc, simp]

Depends on / 依赖: Iso.comp_hom_eq_id, comp_hom_eq_id, counitIso, e.counitIso.app, e.inverse.mapIso, e.unit.app, inverse, mapIso
-/
theorem unit_app_inverse (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  simpa using Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)) (f := e.unit.app _)

@[to_dual none, reassoc, simp]
/--
theorem `fun_inv_map` / 定理 `fun_inv_map`

English:
theorem fun_inv_map
  given: (e : C ≌ D) (X Y : D) (f : X ⟶ Y)
  proof: (NatIso.naturality_2 e.counitIso f).symm

@[to_dual none, reassoc, simp]

中文:
定理 fun_inv_map
  条件: (e : C ≌ D) (X Y : D) (f : X ⟶ Y)
  证明: (NatIso.naturality_2 e.counitIso f).symm

@[to_dual none, reassoc, simp]

Depends on / 依赖: NatIso, NatIso.naturality_2, counitIso, e.counitIso, naturality_2
-/
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm

@[to_dual none, reassoc, simp]
/--
theorem `inv_fun_map` / 定理 `inv_fun_map`

English:
theorem inv_fun_map
  given: (e : C ≌ D) (X Y : C) (f : X ⟶ Y)
  proof: (NatIso.naturality_1 e.unitIso f).symm

中文:
定理 inv_fun_map
  条件: (e : C ≌ D) (X Y : C) (f : X ⟶ Y)
  证明: (NatIso.naturality_1 e.unitIso f).symm

Depends on / 依赖: NatIso, NatIso.naturality_1, e.unitIso, naturality_1, unitIso
-/
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm

section

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/--
Definition of `adjointifyη` / `adjointifyη` 的定义

English:
definition adjointifyη
  signature: : 𝟭 C ≅ F ⋙ G
  body: by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]

中文:
定义 adjointifyη
  签名: : 𝟭 C ≅ F ⋙ G
  定义体: by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]

Depends on / 依赖: associator, isoWhiskerLeft, isoWhiskerRight, leftUnitor
-/
def adjointifyη : 𝟭 C ≅ F ⋙ G := by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]
/--
theorem `adjointify_η_ε` / 定理 `adjointify_η_ε`

English:
theorem adjointify_η_ε
  given: (X : C)
  proof: by
  dsimp [adjointifyη, Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

中文:
定理 adjointify_η_ε
  条件: (X : C)
  证明: by
  dsimp [adjointifyη, Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

Depends on / 依赖: F.map, F.mapIso, F.obj, Trans.trans, comp_id, hom.naturality, hom_inv_id, id_comp, inv.app, mapIso, map_comp, naturality
-/
theorem adjointify_η_ε (X : C) :
    F.map ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp [adjointifyη, Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

end

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
  body: ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

中文:
定义 mk
  签名: (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
  定义体: ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩
-/
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

/-- Equivalence of categories is reflexive. -/
@[refl, simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : C ≌ C
  body: ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩

中文:
定义 refl
  签名: : C ≌ C
  定义体: ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩

Depends on / 依赖: Category, Category.id_comp, Iso.refl, id_comp
-/
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (C ≌ C)
  body: ⟨refl⟩

中文:
实例 :
  签名: 可居 (C ≌ C)
  定义体: ⟨refl⟩
-/
instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[implicit_reducible, symm, simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : C ≌ D)
  body: ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

@[simp]

中文:
定义 symm
  签名: (e : C ≌ D)
  定义体: ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

@[simp]

Depends on / 依赖: counitIso, e.counitIso.symm, e.functor, e.inverse, e.inverse_counitInv_comp, e.unitIso.symm, functor, inverse, inverse_counitInv_comp, unitIso
-/
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

@[simp]
/--
lemma `mkHom_id_inverse` / 引理 `mkHom_id_inverse`

English:
lemma mkHom_id_inverse
  given: {e : C ≌ D}
  statement: mkHom (𝟙 e.inverse) = 𝟙 e.symm
  proof: rfl

@[simp]

中文:
引理 mkHom_id_inverse
  条件: {e : C ≌ D}
  结论: mkHom (𝟙 e.inverse) = 𝟙 e.symm
  证明: rfl

@[simp]
-/
lemma mkHom_id_inverse {e : C ≌ D} : mkHom (𝟙 e.inverse) = 𝟙 e.symm := rfl

@[simp]
/--
lemma `symm_counit` / 引理 `symm_counit`

English:
lemma symm_counit
  given: (e : C ≌ D)
  statement: e.symm.counit = e.unitInv
  proof: rfl

@[simp]

中文:
引理 symm_counit
  条件: (e : C ≌ D)
  结论: e.symm.counit = e.unitInv
  证明: rfl

@[simp]
-/
lemma symm_counit (e : C ≌ D) : e.symm.counit = e.unitInv := rfl

@[simp]
/--
lemma `symm_unit` / 引理 `symm_unit`

English:
lemma symm_unit
  given: (e : C ≌ D)
  statement: e.symm.unit = e.counitInv
  proof: rfl

中文:
引理 symm_unit
  条件: (e : C ≌ D)
  结论: e.symm.unit = e.counitInv
  证明: rfl
-/
lemma symm_unit (e : C ≌ D) : e.symm.unit = e.counitInv := rfl

variable {E : Type u₃} [Category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : C ≌ D) (f : D ≌ E)
  body: e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight (e.functor.rightUnitor.symm ≪≫
    isoWhiskerLeft _ f.unitIso ≪≫ (Functor.associator _ _ _).symm) _ ≪≫ Functor.associator _ _ _
  counitIso := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Functor.associator _ _ _) ≪≫
      isoWhiskerLeft _ e.counitIso ≪≫ f.inverse.rightUnitor) _ ≪≫ f.counitIso
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    simp only [comp_id, id_comp, map_comp, fun_inv_map, comp_obj, id_obj, counitInv,
      functor_unit_comp_assoc, assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp

中文:
定义 trans
  签名: (e : C ≌ D) (f : D ≌ E)
  定义体: e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight (e.functor.rightUnitor.symm ≪≫
    isoWhiskerLeft _ f.unitIso ≪≫ (Functor.associator _ _ _).symm) _ ≪≫ Functor.associator _ _ _
  counitIso := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Functor.associator _ _ _) ≪≫
      isoWhiskerLeft _ e.counitIso ≪≫ f.inverse.rightUnitor) _ ≪≫ f.counitIso
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    simp only [comp_id, id_comp, map_comp, fun_inv_map, comp_obj, id_obj, counitInv,
      functor_unit_comp_assoc, assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp

Depends on / 依赖: e.functor, f.functor, functor
-/
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight (e.functor.rightUnitor.symm ≪≫
    isoWhiskerLeft _ f.unitIso ≪≫ (Functor.associator _ _ _).symm) _ ≪≫ Functor.associator _ _ _
  counitIso := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Functor.associator _ _ _) ≪≫
      isoWhiskerLeft _ e.counitIso ≪≫ f.inverse.rightUnitor) _ ≪≫ f.counitIso
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    simp only [comp_id, id_comp, map_comp, fun_inv_map, comp_obj, id_obj, counitInv,
      functor_unit_comp_assoc, assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp

/--
Definition of `funInvIdAssoc` / `funInvIdAssoc` 的定义

English:
definition funInvIdAssoc
  signature: (e : C ≌ D) (F : C ⥤ E)
  body: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[to_dual (attr := simp) funInvIdAssoc_inv_app]

中文:
定义 funInvIdAssoc
  签名: (e : C ≌ D) (F : C ⥤ E)
  定义体: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[to_dual (attr := simp) funInvIdAssoc_inv_app]

Depends on / 依赖: F.leftUnitor, Functor, Functor.associator, associator, e.unitIso.symm, isoWhiskerRight, leftUnitor, unitIso
-/
def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[to_dual (attr := simp) funInvIdAssoc_inv_app]
/--
theorem `funInvIdAssoc_hom_app` / 定理 `funInvIdAssoc_hom_app`

English:
theorem funInvIdAssoc_hom_app
  given: (e : C ≌ D) (F : C ⥤ E) (X : C)
  proof: by
  dsimp [funInvIdAssoc]
  simp

中文:
定理 funInvIdAssoc_hom_app
  条件: (e : C ≌ D) (F : C ⥤ E) (X : C)
  证明: by
  dsimp [funInvIdAssoc]
  simp

Depends on / 依赖: funInvIdAssoc
-/
theorem funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).hom.app X = F.map (e.unitInv.app X) := by
  dsimp [funInvIdAssoc]
  simp

/--
Definition of `invFunIdAssoc` / `invFunIdAssoc` 的定义

English:
definition invFunIdAssoc
  signature: (e : C ≌ D) (F : D ⥤ E)
  body: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[to_dual (attr := simp) invFunIdAssoc_inv_app]

中文:
定义 invFunIdAssoc
  签名: (e : C ≌ D) (F : D ⥤ E)
  定义体: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[to_dual (attr := simp) invFunIdAssoc_inv_app]

Depends on / 依赖: F.leftUnitor, Functor, Functor.associator, associator, counitIso, e.counitIso, isoWhiskerRight, leftUnitor
-/
def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[to_dual (attr := simp) invFunIdAssoc_inv_app]
/--
theorem `invFunIdAssoc_hom_app` / 定理 `invFunIdAssoc_hom_app`

English:
theorem invFunIdAssoc_hom_app
  given: (e : C ≌ D) (F : D ⥤ E) (X : D)
  proof: by
  dsimp [invFunIdAssoc]
  simp

中文:
定理 invFunIdAssoc_hom_app
  条件: (e : C ≌ D) (F : D ⥤ E) (X : D)
  证明: by
  dsimp [invFunIdAssoc]
  simp

Depends on / 依赖: invFunIdAssoc
-/
theorem invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).hom.app X = F.map (e.counit.app X) := by
  dsimp [invFunIdAssoc]
  simp

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: (e : C ≌ D)
  body: (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

中文:
定义 congrLeft
  签名: (e : C ≌ D)
  定义体: (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

Depends on / 依赖: e.inverse, inverse, whiskeringLeft
-/
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E where
  functor := (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: (e : C ≌ D)
  body: (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

中文:
定义 congrRight
  签名: (e : C ≌ D)
  定义体: (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

Depends on / 依赖: e.functor, functor, whiskeringRight
-/
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D where
  functor := (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

variable (E) in
/-- Promoting `Equivalence.congrRight` to a functor. -/
@[simps]
/--
Definition of `congrRightFunctor` / `congrRightFunctor` 的定义

English:
definition congrRightFunctor
  signature: : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  body: e.congrRight
map {e f} α := mkHom (whiskeringRight _ _ _).map asNatTrans α

中文:
定义 congrRightFunctor
  签名: : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  定义体: e.congrRight
map {e f} α := mkHom (whiskeringRight _ _ _).map asNatTrans α

Depends on / 依赖: congrRight, e.congrRight
-/
def congrRightFunctor : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  obj e := e.congrRight
map {e f} α := mkHom (whiskeringRight _ _ _).map asNatTrans α

section CancellationLemmas

variable (e : C ≌ D)

/- We need special forms of `cancel_natIso_hom_right(_assoc)` and
`cancel_natIso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unitIso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos)

`cancel_unitInv_left` is not a `simp` lemma because it would be redundant.
-/
@[to_dual cancel_unitInv_left, simp]
/--
theorem `cancel_unit_right` / 定理 `cancel_unit_right`

English:
theorem cancel_unit_right
  given: {X Y : C} (f f' : X ⟶ Y)
  proof: by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_unit_left]

中文:
定理 cancel_unit_right
  条件: {X Y : C} (f f' : X ⟶ Y)
  证明: by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_unit_left]

Depends on / 依赖: cancel_mono
-/
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) :
    f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' := by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_unit_left]
/--
theorem `cancel_unitInv_right` / 定理 `cancel_unitInv_right`

English:
theorem cancel_unitInv_right
  given: {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y))
  proof: by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_counitInv_left]

中文:
定理 cancel_unitInv_right
  条件: {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y))
  证明: by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_counitInv_left]

Depends on / 依赖: cancel_mono
-/
theorem cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_counitInv_left]
/--
theorem `cancel_counit_right` / 定理 `cancel_counit_right`

English:
theorem cancel_counit_right
  given: {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y))
  proof: by simp only [cancel_mono]

中文:
定理 cancel_counit_right
  条件: {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y))
  证明: by simp only [cancel_mono]

Depends on / 依赖: cancel_mono
-/
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by simp only [cancel_mono]

/-
`cancel_counit_left` is not a `simp` lemma because it would be redundant.
-/
@[to_dual cancel_counit_left, simp]
/--
theorem `cancel_counitInv_right` / 定理 `cancel_counitInv_right`

English:
theorem cancel_counitInv_right
  given: {X Y : D} (f f' : X ⟶ Y)
  proof: by simp only [cancel_mono]

@[simp, to_dual none]

中文:
定理 cancel_counitInv_right
  条件: {X Y : D} (f f' : X ⟶ Y)
  证明: by simp only [cancel_mono]

@[simp, to_dual none]

Depends on / 依赖: cancel_mono
-/
theorem cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) :
    f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp, to_dual none]
/--
theorem `cancel_unit_right_assoc` / 定理 `cancel_unit_right_assoc`

English:
theorem cancel_unit_right_assoc
  given: {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)
  proof: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

中文:
定理 cancel_unit_right_assoc
  条件: {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)
  证明: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/--
theorem `cancel_counitInv_right_assoc` / 定理 `cancel_counitInv_right_assoc`

English:
theorem cancel_counitInv_right_assoc
  statement: {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  proof: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

中文:
定理 cancel_counitInv_right_assoc
  结论: {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
  证明: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/--
theorem `cancel_unit_right_assoc'` / 定理 `cancel_unit_right_assoc'`

English:
theorem cancel_unit_right_assoc'
  statement: {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

中文:
定理 cancel_unit_right_assoc'
  结论: {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/--
theorem `cancel_counitInv_right_assoc'` / 定理 `cancel_counitInv_right_assoc'`

English:
theorem cancel_counitInv_right_assoc'
  statement: {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp only [← Category.assoc, cancel_mono]

中文:
定理 cancel_counitInv_right_assoc'
  结论: {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp only [← Category.assoc, cancel_mono]

Depends on / 依赖: Category, Category.assoc, cancel_mono
-/
theorem cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔
    f ≫ g ≫ h = f' ≫ g' ≫ h' := by simp only [← Category.assoc, cancel_mono]

end CancellationLemmas

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.
/--
Definition of `powNat` / `powNat` 的定义

English:
definition powNat
  signature: (e : C ≌ C)

中文:
定义 pow自然数
  签名: (e : C ≌ C)
-/
def powNat (e : C ≌ C) : Nat -> (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (powNat e (n + 1))

/--
Definition of `pow` / `pow` 的定义

English:
definition pow
  signature: (e : C ≌ C)

中文:
定义 pow
  签名: (e : C ≌ C)
-/
def pow (e : C ≌ C) : Int -> (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (C ≌ C) Int
  body: ⟨pow⟩

@[simp]

中文:
实例 :
  签名: 幂 (C ≌ C) 整数
  定义体: ⟨pow⟩

@[simp]
-/
instance : Pow (C ≌ C) Int :=
  ⟨pow⟩

@[simp]
/--
theorem `pow_zero` / 定理 `pow_zero`

English:
theorem pow_zero
  given: (e : C ≌ C)
  statement: e ^ (0 : Int) = Equivalence.refl
  proof: rfl

@[simp]

中文:
定理 pow_zero
  条件: (e : C ≌ C)
  结论: e ^ (0 : 整数) = 等价.refl
  证明: rfl

@[simp]
-/
theorem pow_zero (e : C ≌ C) : e ^ (0 : Int) = Equivalence.refl :=
  rfl

@[simp]
/--
theorem `pow_one` / 定理 `pow_one`

English:
theorem pow_one
  given: (e : C ≌ C)
  statement: e ^ (1 : Int) = e
  proof: rfl

@[simp]

中文:
定理 pow_one
  条件: (e : C ≌ C)
  结论: e ^ (1 : 整数) = e
  证明: rfl

@[simp]
-/
theorem pow_one (e : C ≌ C) : e ^ (1 : Int) = e :=
  rfl

@[simp]
/--
theorem `pow_neg_one` / 定理 `pow_neg_one`

English:
theorem pow_neg_one
  given: (e : C ≌ C)
  statement: e ^ (-1 : Int) = e.symm
  proof: rfl

中文:
定理 pow_neg_one
  条件: (e : C ≌ C)
  结论: e ^ (-1 : 整数) = e.symm
  证明: rfl
-/
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : Int) = e.symm :=
  rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.
-- Note: the better formulation of this would involve `HasShift`.
end

/-- The functor of an equivalence of categories is essentially surjective. -/
@[stacks 02C3]
/--
Instance `essSurj_functor` / 实例 `essSurj_functor`

English:
instance essSurj_functor
  signature: (e : C ≌ E)
  body: ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

中文:
实例 essSurj_functor
  签名: (e : C ≌ E)
  定义体: ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

Depends on / 依赖: counitIso, e.counitIso.app, e.inverse.obj, inverse
-/
instance essSurj_functor (e : C ≌ E) : e.functor.EssSurj :=
  ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

/--
Instance `essSurj_inverse` / 实例 `essSurj_inverse`

English:
instance essSurj_inverse
  signature: (e : C ≌ E)
  body: e.symm.essSurj_functor

中文:
实例 essSurj_inverse
  签名: (e : C ≌ E)
  定义体: e.symm.essSurj_functor

Depends on / 依赖: e.symm.essSurj_functor, essSurj_functor
-/
instance essSurj_inverse (e : C ≌ E) : e.inverse.EssSurj :=
  e.symm.essSurj_functor

/--
Definition of `fullyFaithfulFunctor` / `fullyFaithfulFunctor` 的定义

English:
definition fullyFaithfulFunctor
  signature: (e : C ≌ E)
  body: e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

中文:
定义 fullyFaithfulFunctor
  签名: (e : C ≌ E)
  定义体: e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

Depends on / 依赖: e.inverse.map, e.unitIso.hom.app, e.unitIso.inv.app, inverse, unitIso
-/
def fullyFaithfulFunctor (e : C ≌ E) : e.functor.FullyFaithful where
  preimage {X Y} f := e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

/--
Definition of `fullyFaithfulInverse` / `fullyFaithfulInverse` 的定义

English:
definition fullyFaithfulInverse
  signature: (e : C ≌ E)
  body: e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

中文:
定义 fullyFaithfulInverse
  签名: (e : C ≌ E)
  定义体: e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

Depends on / 依赖: counitIso, e.counitIso.hom.app, e.counitIso.inv.app, e.functor.map, functor
-/
def fullyFaithfulInverse (e : C ≌ E) : e.inverse.FullyFaithful where
  preimage {X Y} f := e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

/-- The functor of an equivalence of categories is faithful. -/
@[stacks 02C3]
/--
Instance `faithful_functor` / 实例 `faithful_functor`

English:
instance faithful_functor
  signature: (e : C ≌ E)
  body: e.fullyFaithfulFunctor.faithful

中文:
实例 faithful_functor
  签名: (e : C ≌ E)
  定义体: e.fullyFaithfulFunctor.faithful

Depends on / 依赖: e.fullyFaithfulFunctor.faithful, faithful, fullyFaithfulFunctor
-/
instance faithful_functor (e : C ≌ E) : e.functor.Faithful :=
  e.fullyFaithfulFunctor.faithful

/--
Instance `faithful_inverse` / 实例 `faithful_inverse`

English:
instance faithful_inverse
  signature: (e : C ≌ E)
  body: e.fullyFaithfulInverse.faithful

中文:
实例 faithful_inverse
  签名: (e : C ≌ E)
  定义体: e.fullyFaithfulInverse.faithful

Depends on / 依赖: e.fullyFaithfulInverse.faithful, faithful, fullyFaithfulInverse
-/
instance faithful_inverse (e : C ≌ E) : e.inverse.Faithful :=
  e.fullyFaithfulInverse.faithful

/-- The functor of an equivalence of categories is full. -/
@[stacks 02C3]
/--
Instance `full_functor` / 实例 `full_functor`

English:
instance full_functor
  signature: (e : C ≌ E)
  body: e.fullyFaithfulFunctor.full

中文:
实例 full_functor
  签名: (e : C ≌ E)
  定义体: e.fullyFaithfulFunctor.full

Depends on / 依赖: e.fullyFaithfulFunctor.full, fullyFaithfulFunctor
-/
instance full_functor (e : C ≌ E) : e.functor.Full :=
  e.fullyFaithfulFunctor.full

/--
Instance `full_inverse` / 实例 `full_inverse`

English:
instance full_inverse
  signature: (e : C ≌ E)
  body: e.fullyFaithfulInverse.full

中文:
实例 full_inverse
  签名: (e : C ≌ E)
  定义体: e.fullyFaithfulInverse.full

Depends on / 依赖: e.fullyFaithfulInverse.full, fullyFaithfulInverse
-/
instance full_inverse (e : C ≌ E) : e.inverse.Full :=
  e.fullyFaithfulInverse.full

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose functor is `G`. -/
@[implicit_reducible, simps!]
/--
Definition of `changeFunctor` / `changeFunctor` 的定义

English:
definition changeFunctor
  signature: (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G)
  body: G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso

中文:
定义 changeFunctor
  签名: (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G)
  定义体: G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso
-/
def changeFunctor (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G) : C ≌ D where
  functor := G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso

/--
theorem `changeFunctor_refl` / 定理 `changeFunctor_refl`

English:
theorem changeFunctor_refl
  given: (e : C ≌ D)
  statement: e.changeFunctor (Iso.refl _) = e
  proof: by cat_disch

中文:
定理 changeFunctor_refl
  条件: (e : C ≌ D)
  结论: e.changeFunctor (同构.refl _) = e
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem changeFunctor_refl (e : C ≌ D) : e.changeFunctor (Iso.refl _) = e := by cat_disch

/--
theorem `changeFunctor_trans` / 定理 `changeFunctor_trans`

English:
theorem changeFunctor_trans
  given: (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G')
  proof: by cat_disch

中文:
定理 changeFunctor_trans
  条件: (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G')
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem changeFunctor_trans (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G') :
    (e.changeFunctor iso₁).changeFunctor iso₂ = e.changeFunctor (iso₁ ≪≫ iso₂) := by cat_disch

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose inverse is `G`. -/
@[implicit_reducible, simps!]
/--
Definition of `changeInverse` / `changeInverse` 的定义

English:
definition changeInverse
  signature: (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G)
  body: e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc]; rw [assoc]; rw [iso.hom_inv_id_app]; rw [comp_id]; rw [functor_unit_comp]

中文:
定义 changeInverse
  签名: (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G)
  定义体: e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc]; rw [assoc]; rw [iso.hom_inv_id_app]; rw [comp_id]; rw [functor_unit_comp]

Depends on / 依赖: e.functor, functor
-/
def changeInverse (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G) : C ≌ D where
  functor := e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc]; rw [assoc]; rw [iso.hom_inv_id_app]; rw [comp_id]; rw [functor_unit_comp]

end Equivalence

/--
Definition of `Functor.IsEquivalence` / `Functor.IsEquivalence` 的定义

English:
class Functor.IsEquivalence
  parameters: (F : C ⥤ D)
  axioms and operations (3):
    - faithful : F.Faithful  [default: by infer_instance]
    - full : F.Full  [default: by infer_instance]
    - essSurj : F.EssSurj  [default: by infer_instance]

中文:
类 函子.是等价
  参数: (F : C ⥤ D)
  公理与运算 (3 个):
    - faithful : F.忠实  [默认: by infer_instance]
    - full : F.满  [默认: by infer_instance]
    - essSurj : F.本质满射  [默认: by infer_instance]

Depends on / 依赖: EssSurj, F.EssSurj, F.Full, essSurj, infer_instance
-/
class Functor.IsEquivalence (F : C ⥤ D) : Prop where
  faithful : F.Faithful := by infer_instance
  full : F.Full := by infer_instance
  essSurj : F.EssSurj := by infer_instance

/--
Instance `Equivalence.isEquivalence_functor` / 实例 `Equivalence.isEquivalence_functor`

English:
instance Equivalence.isEquivalence_functor
  signature: (F : C ≌ D)

中文:
实例 等价.isEquivalence_functor
  签名: (F : C ≌ D)
-/
instance Equivalence.isEquivalence_functor (F : C ≌ D) : IsEquivalence F.functor where

/--
Instance `Equivalence.isEquivalence_inverse` / 实例 `Equivalence.isEquivalence_inverse`

English:
instance Equivalence.isEquivalence_inverse
  signature: (F : C ≌ D)
  body: F.symm.isEquivalence_functor

中文:
实例 等价.isEquivalence_inverse
  签名: (F : C ≌ D)
  定义体: F.symm.isEquivalence_functor

Depends on / 依赖: F.symm.isEquivalence_functor, isEquivalence_functor
-/
instance Equivalence.isEquivalence_inverse (F : C ≌ D) : IsEquivalence F.inverse :=
  F.symm.isEquivalence_functor

namespace Functor

namespace IsEquivalence

attribute [instance] faithful full essSurj

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
  proof: inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)

中文:
引理 mk'
  条件: {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
  证明: inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)
-/
protected lemma mk' {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    IsEquivalence F :=
  inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)

end IsEquivalence

/-- A quasi-inverse `D ⥤ C` to a functor that `F : C ⥤ D` that is an equivalence,
i.e. faithful, full, and essentially surjective. -/
@[implicit_reducible]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (F : C ⥤ D) [F.IsEquivalence]
  body: F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp {X Y Z} f g := by apply F.map_injective; simp

中文:
定义 inv
  签名: (F : C ⥤ D) [F.是等价]
  定义体: F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp {X Y Z} f g := by apply F.map_injective; simp

Depends on / 依赖: F.objPreimage, objPreimage
-/
noncomputable def inv (F : C ⥤ D) [F.IsEquivalence] : D ⥤ C where
  obj X := F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp {X Y Z} f g := by apply F.map_injective; simp

/-- Interpret a functor that is an equivalence as an equivalence. -/
@[simps functor, simps -isSimp inverse, simps! -isSimp unitIso_hom_app unitIso_inv_app
  counitIso_hom_app counitIso_inv_app, stacks 02C3]
/--
Definition of `asEquivalence` / `asEquivalence` 的定义

English:
definition asEquivalence
  signature: (F : C ⥤ D) [F.IsEquivalence]
  body: F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])

中文:
定义 asEquivalence
  签名: (F : C ⥤ D) [F.是等价]
  定义体: F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])
-/
noncomputable def asEquivalence (F : C ⥤ D) [F.IsEquivalence] : C ≌ D where
  functor := F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])

/--
Instance `isEquivalence_refl` / 实例 `isEquivalence_refl`

English:
instance isEquivalence_refl
  signature: : IsEquivalence (𝟭 C)
  body: Equivalence.refl.isEquivalence_functor

中文:
实例 isEquivalence_refl
  签名: : 是等价 (𝟭 C)
  定义体: Equivalence.refl.isEquivalence_functor

Depends on / 依赖: Equivalence, Equivalence.refl.isEquivalence_functor, isEquivalence_functor
-/
instance isEquivalence_refl : IsEquivalence (𝟭 C) :=
  Equivalence.refl.isEquivalence_functor

/--
Instance `isEquivalence_inv` / 实例 `isEquivalence_inv`

English:
instance isEquivalence_inv
  signature: (F : C ⥤ D) [IsEquivalence F]
  body: F.asEquivalence.symm.isEquivalence_functor

中文:
实例 isEquivalence_inv
  签名: (F : C ⥤ D) [是等价 F]
  定义体: F.asEquivalence.symm.isEquivalence_functor

Depends on / 依赖: F.asEquivalence.symm.isEquivalence_functor, asEquivalence, isEquivalence_functor
-/
instance isEquivalence_inv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  F.asEquivalence.symm.isEquivalence_functor

variable {E : Type u₃} [Category.{v₃} E]

/--
Instance `isEquivalence_trans` / 实例 `isEquivalence_trans`

English:
instance isEquivalence_trans
  signature: (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G]

中文:
实例 isEquivalence_trans
  签名: (F : C ⥤ D) (G : D ⥤ E) [是等价 F] [是等价 G]
-/
instance isEquivalence_trans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] :
    IsEquivalence (F ⋙ G) where

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringLeft C D E).obj F) :=
inferInstanceAs IsEquivalence (Equivalence.congrLeft F.asEquivalence).inverse

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringRight E C D).obj F) :=
inferInstanceAs IsEquivalence (Equivalence.congrRight F.asEquivalence).functor

end Functor

namespace Functor

@[simp]
/--
theorem `fun_inv_map` / 定理 `fun_inv_map`

English:
theorem fun_inv_map
  given: (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y)
  proof: (NatIso.naturality_2 (α := F.asEquivalence.counitIso) (f := f)).symm

@[simp]

中文:
定理 fun_inv_map
  条件: (F : C ⥤ D) [是等价 F] (X Y : D) (f : X ⟶ Y)
  证明: (NatIso.naturality_2 (α := F.asEquivalence.counitIso) (f := f)).symm

@[simp]

Depends on / 依赖: F.asEquivalence.counitIso, NatIso, NatIso.naturality_2, asEquivalence, counitIso, naturality_2
-/
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y :=
  (NatIso.naturality_2 (α := F.asEquivalence.counitIso) (f := f)).symm

@[simp]
/--
theorem `inv_fun_map` / 定理 `inv_fun_map`

English:
theorem inv_fun_map
  given: (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y)
  proof: (NatIso.naturality_1 (α := F.asEquivalence.unitIso) (f := f)).symm

中文:
定理 inv_fun_map
  条件: (F : C ⥤ D) [是等价 F] (X Y : C) (f : X ⟶ Y)
  证明: (NatIso.naturality_1 (α := F.asEquivalence.unitIso) (f := f)).symm

Depends on / 依赖: F.asEquivalence.unitIso, NatIso, NatIso.naturality_1, asEquivalence, naturality_1, unitIso
-/
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y :=
  (NatIso.naturality_1 (α := F.asEquivalence.unitIso) (f := f)).symm

/--
lemma `isEquivalence_of_iso` / 引理 `isEquivalence_of_iso`

English:
lemma isEquivalence_of_iso
  given: {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence]
  statement: G.IsEquivalence
  proof: ((asEquivalence F).changeFunctor e).isEquivalence_functor

中文:
引理 isEquivalence_of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G) [F.是等价]
  结论: G.是等价
  证明: ((asEquivalence F).changeFunctor e).isEquivalence_functor

Depends on / 依赖: asEquivalence, changeFunctor, isEquivalence_functor
-/
lemma isEquivalence_of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence :=
  ((asEquivalence F).changeFunctor e).isEquivalence_functor

/--
lemma `isEquivalence_iff_of_iso` / 引理 `isEquivalence_iff_of_iso`

English:
lemma isEquivalence_iff_of_iso
  given: {F G : C ⥤ D} (e : F ≅ G)
  proof: ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

中文:
引理 isEquivalence_iff_of_iso
  条件: {F G : C ⥤ D} (e : F ≅ G)
  证明: ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

Depends on / 依赖: e.symm, isEquivalence_of_iso
-/
lemma isEquivalence_iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsEquivalence ↔ G.IsEquivalence :=
  ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

/--
lemma `isEquivalence_of_comp_right` / 引理 `isEquivalence_of_comp_right`

English:
lemma isEquivalence_of_comp_right
  statement: {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

中文:
引理 isEquivalence_of_comp_right
  结论: {E : 类型} [范畴* E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

Depends on / 依赖: F.rightUnitor.symm, G.asEquivalence.symm, G.asEquivalence.unitIso, asEquivalence, asEquivalence.trans, isEquivalence_functor, isEquivalence_iff_of_iso, isoWhiskerLeft, rightUnitor, unitIso
-/
lemma isEquivalence_of_comp_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence G] [IsEquivalence (F ⋙ G)] : IsEquivalence F := by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

/--
lemma `isEquivalence_of_comp_left` / 引理 `isEquivalence_of_comp_left`

English:
lemma isEquivalence_of_comp_left
  statement: {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

中文:
引理 isEquivalence_of_comp_left
  结论: {E : 类型} [范畴* E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

Depends on / 依赖: F.asEquivalence.counitIso.symm, F.asEquivalence.symm.trans, G.leftUnitor.symm, asEquivalence, counitIso, isEquivalence_functor, isEquivalence_iff_of_iso, isoWhiskerRight, leftUnitor
-/
lemma isEquivalence_of_comp_left {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence F] [IsEquivalence (F ⋙ G)] : IsEquivalence G := by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

end Functor

namespace Equivalence

/--
Instance `essSurjInducedFunctor` / 实例 `essSurjInducedFunctor`

English:
instance essSurjInducedFunctor
  signature: {C' : Type*} (e : C' ≃ D)
  body: ⟨e.symm Y, by simpa using ⟨default⟩⟩

中文:
实例 essSurjInducedFunctor
  签名: {C' : 类型} (e : C' ≃ D)
  定义体: ⟨e.symm Y, by simpa using ⟨default⟩⟩

Depends on / 依赖: e.symm
-/
instance essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : (inducedFunctor e).EssSurj where
  mem_essImage Y := ⟨e.symm Y, by simpa using ⟨default⟩⟩

/--
Instance `inducedFunctorOfEquiv` / 实例 `inducedFunctorOfEquiv`

English:
instance inducedFunctorOfEquiv
  signature: {C' : Type*} (e : C' ≃ D)

中文:
实例 inducedFunctorOfEquiv
  签名: {C' : 类型} (e : C' ≃ D)
-/
noncomputable instance inducedFunctorOfEquiv {C' : Type*} (e : C' ≃ D) :
    IsEquivalence (inducedFunctor e) where

/--
Instance `fullyFaithfulToEssImage` / 实例 `fullyFaithfulToEssImage`

English:
instance fullyFaithfulToEssImage
  signature: (F : C ⥤ D) [F.Full] [F.Faithful]

中文:
实例 fullyFaithfulToEssImage
  签名: (F : C ⥤ D) [F.满] [F.忠实]
-/
noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [F.Full] [F.Faithful] :
    IsEquivalence F.toEssImage where

end Equivalence

/-- An equality of properties of objects of a category `C` induces an equivalence of the
respective induced full subcategories of `C`. -/
@[simps]
/--
Definition of `ObjectProperty.fullSubcategoryCongr` / `ObjectProperty.fullSubcategoryCongr` 的定义

English:
definition ObjectProperty.fullSubcategoryCongr
  signature: {P P' : ObjectProperty C} (h : P = P')
  body: ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.symm.le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 ObjectProperty.fullSubcategoryCongr
  签名: {P P' : ObjectProperty C} (h : P = P')
  定义体: ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.symm.le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: ObjectProperty, h.le
-/
def ObjectProperty.fullSubcategoryCongr {P P' : ObjectProperty C} (h : P = P') :
    P.FullSubcategory ≌ P'.FullSubcategory where
  functor := ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.symm.le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

namespace Iso

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E}

/-- Construct an isomorphism `F ⋙ H.inverse ≅ G` from an isomorphism `F ≅ G ⋙ H.functor`. -/
@[simps!]
/--
Definition of `compInverseIso` / `compInverseIso` 的定义

English:
definition compInverseIso
  signature: {H : D ≌ E} (i : F ≅ G ⋙ H.functor)
  body: isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

中文:
定义 compInverseIso
  签名: {H : D ≌ E} (i : F ≅ G ⋙ H.functor)
  定义体: isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

Depends on / 依赖: G.rightUnitor, H.inverse, H.unitIso.symm, associator, inverse, isoWhiskerLeft, isoWhiskerRight, rightUnitor, unitIso
-/
def compInverseIso {H : D ≌ E} (i : F ≅ G ⋙ H.functor) : F ⋙ H.inverse ≅ G :=
  isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

/-- Construct an isomorphism `G ≅ F ⋙ H.inverse` from an isomorphism `G ⋙ H.functor ≅ F`. -/
@[simps!]
/--
Definition of `isoCompInverse` / `isoCompInverse` 的定义

English:
definition isoCompInverse
  signature: {H : D ≌ E} (i : G ⋙ H.functor ≅ F)
  body: G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

中文:
定义 isoCompInverse
  签名: {H : D ≌ E} (i : G ⋙ H.functor ≅ F)
  定义体: G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

Depends on / 依赖: G.rightUnitor.symm, H.inverse, H.unitIso, associator, inverse, isoWhiskerLeft, isoWhiskerRight, rightUnitor, unitIso
-/
def isoCompInverse {H : D ≌ E} (i : G ⋙ H.functor ≅ F) : G ≅ F ⋙ H.inverse :=
  G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

/-- Construct an isomorphism `G.inverse ⋙ F ≅ H` from an isomorphism `F ≅ G.functor ⋙ H`. -/
@[simps!]
/--
Definition of `inverseCompIso` / `inverseCompIso` 的定义

English:
definition inverseCompIso
  signature: {G : C ≌ D} (i : F ≅ G.functor ⋙ H)
  body: isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

中文:
定义 inverseCompIso
  签名: {G : C ≌ D} (i : F ≅ G.functor ⋙ H)
  定义体: isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

Depends on / 依赖: G.counitIso, G.inverse, H.leftUnitor, associator, counitIso, inverse, isoWhiskerLeft, isoWhiskerRight, leftUnitor
-/
def inverseCompIso {G : C ≌ D} (i : F ≅ G.functor ⋙ H) : G.inverse ⋙ F ≅ H :=
  isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

/-- Construct an isomorphism `H ≅ G.inverse ⋙ F` from an isomorphism `G.functor ⋙ H ≅ F`. -/
@[simps!]
/--
Definition of `isoInverseComp` / `isoInverseComp` 的定义

English:
definition isoInverseComp
  signature: {G : C ≌ D} (i : G.functor ⋙ H ≅ F)
  body: H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

中文:
定义 isoInverseComp
  签名: {G : C ≌ D} (i : G.functor ⋙ H ≅ F)
  定义体: H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

Depends on / 依赖: G.counitIso.symm, G.inverse, H.leftUnitor.symm, associator, counitIso, inverse, isoWhiskerLeft, isoWhiskerRight, leftUnitor
-/
def isoInverseComp {G : C ≌ D} (i : G.functor ⋙ H ≅ F) : H ≅ G.inverse ⋙ F :=
  H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.inverse ≅ G.inverse` from an isomorphism `G.functor ≅ G.functor`. -/
@[simps!]
/--
Definition of `isoInverseOfIsoFunctor` / `isoInverseOfIsoFunctor` 的定义

English:
definition isoInverseOfIsoFunctor
  signature: {G G' : C ≌ D} (i : G.functor ≅ G'.functor)
  body: isoCompInverse ((isoWhiskerLeft G.inverse i).symm ≪≫ G.counitIso) ≪≫ leftUnitor G'.inverse

中文:
定义 isoInverseOfIsoFunctor
  签名: {G G' : C ≌ D} (i : G.functor ≅ G'.functor)
  定义体: isoCompInverse ((isoWhiskerLeft G.inverse i).symm ≪≫ G.counitIso) ≪≫ leftUnitor G'.inverse

Depends on / 依赖: G.counitIso, G.inverse, cat_disch, counitIso, inverse, isoCompInverse, isoWhiskerLeft, leftUnitor
-/
def isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) : G.inverse ≅ G'.inverse :=
  isoCompInverse ((isoWhiskerLeft G.inverse i).symm ≪≫ G.counitIso) ≪≫ leftUnitor G'.inverse

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.functor ≅ G.functor` from an isomorphism `G.inverse ≅ G.inverse`. -/
@[simps!]
/--
Definition of `isoFunctorOfIsoInverse` / `isoFunctorOfIsoInverse` 的定义

English:
definition isoFunctorOfIsoInverse
  signature: {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse)
  body: isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

中文:
定义 isoFunctorOfIsoInverse
  签名: {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse)
  定义体: isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

Depends on / 依赖: G.symm, isoInverseOfIsoFunctor
-/
def isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) : G.functor ≅ G'.functor :=
  isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

/-- Sanity check: `isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i)` is just `i`. -/
@[simp]
/--
lemma `isoFunctorOfIsoInverse_isoInverseOfIsoFunctor` / 引理 `isoFunctorOfIsoInverse_isoInverseOfIsoFunctor`

English:
lemma isoFunctorOfIsoInverse_isoInverseOfIsoFunctor
  given: {G G' : C ≌ D} (i : G.functor ≅ G'.functor)
  proof: by
  ext X
  simp [← NatTrans.naturality]

@[simp]

中文:
引理 isoFunctorOfIsoInverse_isoInverseOfIsoFunctor
  条件: {G G' : C ≌ D} (i : G.functor ≅ G'.functor)
  证明: by
  ext X
  simp [← NatTrans.naturality]

@[simp]

Depends on / 依赖: NatTrans, NatTrans.naturality, naturality
-/
lemma isoFunctorOfIsoInverse_isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) :
    isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i) = i := by
  ext X
  simp [← NatTrans.naturality]

@[simp]
/--
lemma `isoInverseOfIsoFunctor_isoFunctorOfIsoInverse` / 引理 `isoInverseOfIsoFunctor_isoFunctorOfIsoInverse`

English:
lemma isoInverseOfIsoFunctor_isoFunctorOfIsoInverse
  given: {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse)
  proof: isoFunctorOfIsoInverse_isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

中文:
引理 isoInverseOfIsoFunctor_isoFunctorOfIsoInverse
  条件: {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse)
  证明: isoFunctorOfIsoInverse_isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

Depends on / 依赖: G.symm, isoFunctorOfIsoInverse_isoInverseOfIsoFunctor
-/
lemma isoInverseOfIsoFunctor_isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) :
    isoInverseOfIsoFunctor (isoFunctorOfIsoInverse i) = i :=
  isoFunctorOfIsoInverse_isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

end Iso

end CategoryTheory
