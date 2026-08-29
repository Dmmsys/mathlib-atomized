/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Descent data as coalgebras

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` be a pseudofunctor
to the bicategory of adjunctions in `Cat`. In particular,
for any morphism `g : X ⟶ Y` in `C`, we have an
adjunction `(g^*, g_*)` between a pullback functor and a
pushforward functor.

In this file, given a family of morphisms `f i : X i ⟶ S` indexed
by a type `ι` in `C`, we introduce a category `F.DescentDataAsCoalgebra f`
of descent data relative to the morphisms `f i`, where the objects are
described as a family of objects `obj i` over `X i`, and the
morphisms relating them are described as morphisms
`obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`, similarly as
Eilenberg-Moore coalgebras. Indeed, when the index type `ι`
contains a unique element, we show that
`F.DescentDataAsCoalgebra (fun (i : ι) ↦ f`
identifies to the category of coalgebras for the comonad attached
to the adjunction `(F.map f.op.toLoc).adj`.

## TODO (@joelriou, @chrisflav)
* Compare `DescentDataAsCoalgebra` with `DescentData` when suitable
  pullbacks exist and certain base change morphisms are isomorphisms

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

variable (F) in
/--
Definition of `DescentDataAsCoalgebra` / `DescentDataAsCoalgebra` 的定义

English:
structure DescentDataAsCoalgebra
  axioms and operations (4):
    - obj((i : ι)) : (F.obj (.mk (op (X i)))).obj
    - hom((i₁ i₂ : ι)) : obj i₁ ⟶ (F.map (f i₁).op.toLoc).l.toFunctor.obj ((F.map (f i₂).op.toLoc).r.toFunctor.obj (obj i₂))
    - counit((i : ι)) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.toNatTrans.app _ = 𝟙 _  [default: by cat_disch]
    - coassoc((i₁ i₂ i₃ : ι)) : hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂ i₃)) = hom i₁ i₃ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _)  [default: by cat_disch]

中文:
结构 DescentDataAsCoalgebra
  公理与运算 (4 个):
    - obj((i : ι)) : (F.obj (.mk (op (X i)))).obj
    - hom((i₁ i₂ : ι)) : obj i₁ ⟶ (F.map (f i₁).op.toLoc).l.toFunctor.obj ((F.map (f i₂).op.toLoc).r.toFunctor.obj (obj i₂))
    - counit((i : ι)) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.to自然数Trans.app _ = 𝟙 _  [默认: by cat_disch]
    - coassoc((i₁ i₂ i₃ : ι)) : hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂ i₃)) = hom i₁ i₃ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).adj.unit.to自然数Trans.app _)  [默认: by cat_disch]

Depends on / 依赖: F.map, adj.unit.toNatTrans.app, cat_disch, coassoc, l.toFunctor.map, op.toLoc, r.toFunctor.map, toFunctor, toNatTrans
-/
structure DescentDataAsCoalgebra
    {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  /-- The compatibility morphisms. -/
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (obj i₂))
  counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.toNatTrans.app _ = 𝟙 _ := by
    cat_disch
  coassoc (i₁ i₂ i₃ : ι) :
    hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂ i₃)) =
    hom i₁ i₃ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _) := by cat_disch

namespace DescentDataAsCoalgebra

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [reassoc (attr := simp)] counit coassoc

section

variable {ι : Type t} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S}

/-- The type of morphisms in `DescentDataAsCoalgebra`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (D₁ D₂ : F.DescentDataAsCoalgebra f)
  axioms and operations (2):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm((i₁ i₂ : ι)) : D₁.hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂)) = hom i₁ ≫ D₂.hom i₁ i₂  [default: by cat_disch]

中文:
结构 Hom
  参数: (D₁ D₂ : F.DescentDataAsCoalgebra f)
  公理与运算 (2 个):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm((i₁ i₂ : ι)) : D₁.hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂)) = hom i₁ ≫ D₂.hom i₁ i₂  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (D₁ D₂ : F.DescentDataAsCoalgebra f) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map
        ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂)) =
    hom i₁ ≫ D₂.hom i₁ i₂ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (F.DescentDataAsCoalgebra f)
  body: Hom
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

@[ext]

中文:
实例 :
  签名: Category (F.DescentDataAsCoalgebra f)
  定义体: Hom
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

@[ext]
-/
instance : Category (F.DescentDataAsCoalgebra f) where
  Hom := Hom
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂}
  proof: Hom.ext (funext h)

@[simp]

中文:
引理 hom_ext
  结论: {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂}
  证明: Hom.ext (funext h)

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂}
    (h : forall i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (D : F.DescentDataAsCoalgebra f) (i : ι)
  proof: rfl

@[reassoc, simp]

中文:
引理 id_hom
  条件: (D : F.DescentDataAsCoalgebra f) (i : ι)
  证明: rfl

@[reassoc, simp]
-/
lemma id_hom (D : F.DescentDataAsCoalgebra f) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[reassoc, simp]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι)
  proof: rfl

中文:
引理 comp_hom
  条件: {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι)
  证明: rfl
-/
lemma comp_hom {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

/-- Constructor for isomorphisms in `DescentDataAsCoalgebra`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
  body: (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_epi (e i₁).hom]; rw [← reassoc_of% (comm i₁ i₂)]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
    simp

中文:
定义 isoMk
  签名: {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : 对任意 (i : ι), D₁.obj i ≅ D₂.obj i)
  定义体: (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_epi (e i₁).hom]; rw [← reassoc_of% (comm i₁ i₂)]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
    simp

Depends on / 依赖: Functor, Functor.map_comp, cancel_epi, cat_disch, hom.comm, hom.hom, inv.comm, inv.hom, map_comp, reassoc_of
-/
def isoMk {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : forall (i₁ i₂ : ι), D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (e i₂).hom) =
      (e i₁).hom ≫ D₂.hom i₁ i₂ := by cat_disch) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_epi (e i₁).hom]; rw [← reassoc_of% (comm i₁ i₂)]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
    simp

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- When the index type `ι` contains a unique element, the category
`DescentDataAsCoalgebra` identifies to the category of coalgebras
over the comonad corresponding to the adjunction
`(F.map f.op.toLoc).adj`. -/
@[simps! functor_obj_A functor_obj_a functor_map_f inverse_obj_obj inverse_obj_hom
  inverse_map_hom counitIso_hom_app_f counitIso_inv_app_f,
  simps! -isSimp unitIso_hom_app_hom unitIso_inv_app_hom]
/--
Definition of `coalgebraEquivalence` / `coalgebraEquivalence` 的定义

English:
definition coalgebraEquivalence
  signature: (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S)
  body: { A := D.obj default
      a := D.hom default default }
  functor.map φ := { f := φ.hom default }
  inverse.obj A :=
    { obj _ := A.A
      hom _ _ := A.a
      counit _ := A.counit
      coassoc _ _ _ := A.coassoc.symm }
  inverse.map φ :=
    { hom i := φ.f
      comm _ _ := φ.h }
  unitIso :=
 

中文:
定义 coalgebraEquivalence
  签名: (ι : 类型) [Unique ι] {X S : C} (f : X ⟶ S)
  定义体: { A := D.obj default
      a := D.hom default default }
  functor.map φ := { f := φ.hom default }
  inverse.obj A :=
    { obj _ := A.A
      hom _ _ := A.a
      counit _ := A.counit
      coassoc _ _ _ := A.coassoc.symm }
  inverse.map φ :=
    { hom i := φ.f
      comm _ _ := φ.h }
  unitIso :=
 

Depends on / 依赖: A.coassoc.symm, A.counit, D.hom, D.obj, NatIso, NatIso.ofComponents, Subsingleton, Subsingleton.elim, coassoc, congr_arg, counit, eqToIso, functor, functor.map, inverse, inverse.map, inverse.obj, ofComponents, subsingleton, unitIso
-/
def coalgebraEquivalence (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S) :
    F.DescentDataAsCoalgebra (fun (_ : ι) => f) ≌
    (Adjunction.ofCat (F.map f.op.toLoc).adj).toComonad.Coalgebra where
  functor.obj D :=
    { A := D.obj default
      a := D.hom default default }
  functor.map φ := { f := φ.hom default }
  inverse.obj A :=
    { obj _ := A.A
      hom _ _ := A.a
      counit _ := A.counit
      coassoc _ _ _ := A.coassoc.symm }
  inverse.map φ :=
    { hom i := φ.f
      comm _ _ := φ.h }
  unitIso :=
    NatIso.ofComponents
      (fun D => isoMk (fun i => eqToIso (congr_arg D.obj (by subsingleton)))
        (fun i₁ i₂ => by
          obtain rfl := Subsingleton.elim i₁ default
          obtain rfl := Subsingleton.elim i₂ default
          simp)) (fun {D₁ D₂} α => by
      ext i
      obtain rfl := Subsingleton.elim i default
      simp)
  counitIso := Iso.refl _

end DescentDataAsCoalgebra

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The functor `(F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f`
when `f i : X i ⟶ S` is a family of morphisms. -/
@[simps]
/--
Definition of `toDescentDataAsCoalgebra` / `toDescentDataAsCoalgebra` 的定义

English:
definition toDescentDataAsCoalgebra
  body: { obj i := (F.map (f i).op.toLoc).l.toFunctor.obj M
      hom i₁ i₂ :=
        (F.map (f i₁).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _)
      coassoc i₁ i₂ i₃ := by
        rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Adj.unit_naturality] }
  map

中文:
定义 toDescentDataAsCoalgebra
  定义体: { obj i := (F.map (f i).op.toLoc).l.toFunctor.obj M
      hom i₁ i₂ :=
        (F.map (f i₁).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _)
      coassoc i₁ i₂ i₃ := by
        rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Adj.unit_naturality] }
  map

Depends on / 依赖: Adj.unit_naturality, F.map, Functor, Functor.map_comp, adj.unit.toNatTrans.app, coassoc, l.toFunctor.map, l.toFunctor.obj, map_comp, op.toLoc, toFunctor, toNatTrans, unit_naturality
-/
def toDescentDataAsCoalgebra
    {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) :
    (F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f where
  obj M :=
    { obj i := (F.map (f i).op.toLoc).l.toFunctor.obj M
      hom i₁ i₂ :=
        (F.map (f i₁).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _)
      coassoc i₁ i₂ i₃ := by
        rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Adj.unit_naturality] }
  map g :=
    { hom i := (F.map (f i).op.toLoc).l.toFunctor.map g
      comm i₁ i₂ := by simp [← Functor.map_comp] }

section

variable (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S)

/-- When `ι` contains a unique element and `f : X ⟶ S` is a morphism,
the composition of `F.toDescentDataAsCoalgebra (fun (_ : ι) ↦ f)`
and the functor of the equivalence
`DescentDataAsCoalgebra.coalgebraEquivalence F ι f` identifies to
`Comonad.comparison` applied to the adjunction corresponding to
`F.map f.op.toLoc`. -/
@[simps!]
/--
Definition of `toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso` / `toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso` 的定义

English:
definition toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso
  body: Iso.refl _

中文:
定义 toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso
    (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S) :
    F.toDescentDataAsCoalgebra (fun (_ : ι) => f) ⋙
      (DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor ≅
    Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj) :=
  Iso.refl _

/--
lemma `isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison` / 引理 `isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison`

English:
lemma isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison
  proof: by
  rw [← Functor.isEquivalence_iff_of_iso
    (F.toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso ι f)]
  exact ⟨fun _ => inferInstance, fun _ =>
    Functor.isEquivalence_of_comp_right _
      ((DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor)⟩

中文:
引理 isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison
  证明: by
  rw [← Functor.isEquivalence_iff_of_iso
    (F.toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso ι f)]
  exact ⟨fun _ => inferInstance, fun _ =>
    Functor.isEquivalence_of_comp_right _
      ((DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor)⟩

Depends on / 依赖: DescentDataAsCoalgebra, DescentDataAsCoalgebra.coalgebraEquivalence, F.toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso, Functor, Functor.isEquivalence_iff_of_iso, Functor.isEquivalence_of_comp_right, coalgebraEquivalence, functor, isEquivalence_iff_of_iso, isEquivalence_of_comp_right, toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso
-/
lemma isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison :
    (F.toDescentDataAsCoalgebra (fun (_ : ι) => f)).IsEquivalence ↔
    (Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj)).IsEquivalence := by
  rw [← Functor.isEquivalence_iff_of_iso
    (F.toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso ι f)]
  exact ⟨fun _ => inferInstance, fun _ =>
    Functor.isEquivalence_of_comp_right _
      ((DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor)⟩

end

end Pseudofunctor

end CategoryTheory
