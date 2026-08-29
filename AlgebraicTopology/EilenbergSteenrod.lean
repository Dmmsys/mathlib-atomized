/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j : Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a typeclass `IsHomotopyInvariant` for the first axiom.
-/

@[expose] public section

open CategoryTheory TopPair ObjectProperty

universe u

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
/--
Definition of `HomologyPretheory` / `HomologyPretheory` 的定义

English:
structure HomologyPretheory
  axioms and operations (5):
    - Hₚ((i : ι)) : TopPair.{u} ⥤ C
    - H((i : ι)) : TopCat.{u} ⥤ C
    - iso((i : ι)) : H i ≅ incl ⋙ Hₚ i
    - δ((i j : ι)) : Hₚ i ⟶ proj₂ ⋙ H j
    - shape_δ((i j : ι) (h : ¬ c.Rel i j)) : δ i j = 0  [default: by cat_disch]

中文:
结构 HomologyPretheory
  公理与运算 (5 个):
    - Hₚ((i : ι)) : TopPair.{u} ⥤ C
    - H((i : ι)) : TopCat.{u} ⥤ C
    - iso((i : ι)) : H i ≅ incl ⋙ Hₚ i
    - δ((i j : ι)) : Hₚ i ⟶ proj₂ ⋙ H j
    - shape_δ((i j : ι) (h : ¬ c.Rel i j)) : δ i j = 0  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure HomologyPretheory
    (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- `Hₚ` and `H` agree on `TopCat`. -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (HP HP' : HomologyPretheory.{u} C c)
  axioms and operations (4):
    - homₚ((i : ι)) : HP.Hₚ i ⟶ HP'.Hₚ i
    - hom((i : ι)) : HP.H i ⟶ HP'.H i  [default: (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv]
    - iso_comm((i : ι)) : (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom  [default: by cat_disch]
    - w((i j : ι)) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j  [default: by cat_disch]

中文:
结构 Hom
  参数: (HP HP' : HomologyPretheory.{u} C c)
  公理与运算 (4 个):
    - homₚ((i : ι)) : HP.Hₚ i ⟶ HP'.Hₚ i
    - hom((i : ι)) : HP.H i ⟶ HP'.H i  [默认: (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv]
    - iso_comm((i : ι)) : (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom  [默认: by cat_disch]
    - w((i j : ι)) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j  [默认: by cat_disch]

Depends on / 依赖: HP.iso, incl.whiskerLeft, whiskerLeft
-/
structure Hom (HP HP' : HomologyPretheory.{u} C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `HomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j := by cat_disch

attribute [reassoc (attr := simp)] Hom.iso_comm
attribute [reassoc (attr := local simp)] Hom.w

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (HomologyPretheory.{u} C c)
  body: HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

中文:
实例 :
  签名: Category (HomologyPretheory.{u} C c)
  定义体: HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

Depends on / 依赖: HomologyPretheory, HomologyPretheory.Hom
-/
instance : Category (HomologyPretheory.{u} C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

variable {HP HP' : HomologyPretheory.{u} C c}

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Hom.iso_comm_app` / 引理 `Hom.iso_comm_app`

English:
lemma Hom.iso_comm_app
  given: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  proof: congr($(f.iso_comm _).app _)

中文:
引理 Hom.iso_comm_app
  条件: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  证明: congr($(f.iso_comm _).app _)

Depends on / 依赖: f.iso_comm, iso_comm
-/
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) = (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Hom.w_app` / 引理 `Hom.w_app`

English:
lemma Hom.w_app
  given: (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u})
  proof: congr($(f.w _ _).app _)

@[reassoc]

中文:
引理 Hom.w_app
  条件: (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u})
  证明: congr($(f.w _ _).app _)

@[reassoc]
-/
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}) :
    (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
/--
lemma `iso_homₚ_inv_hom` / 引理 `iso_homₚ_inv_hom`

English:
lemma iso_homₚ_inv_hom
  given: (f : HP ⟶ HP') (i : ι)
  proof: by simp

中文:
引理 iso_homₚ_inv_hom
  条件: (f : HP ⟶ HP') (i : ι)
  证明: by simp
-/
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `iso_homₚ_inv_hom_app` / 引理 `iso_homₚ_inv_hom_app`

English:
lemma iso_homₚ_inv_hom_app
  given: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  proof: congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]

中文:
引理 iso_homₚ_inv_hom_app
  条件: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  证明: congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
-/
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X = (f.hom i).app X :=
  congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
/--
lemma `inv_hom_iso_homₚ` / 引理 `inv_hom_iso_homₚ`

English:
lemma inv_hom_iso_homₚ
  given: (f : HP ⟶ HP') (i : ι)
  proof: ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

中文:
引理 inv_hom_iso_homₚ
  条件: (f : HP ⟶ HP') (i : ι)
  证明: ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

Depends on / 依赖: HP.iso, Iso.inv_comp_eq, f.iso_comm, inv_comp_eq, iso_comm
-/
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
/--
lemma `inv_hom_iso_homₚ_app` / 引理 `inv_hom_iso_homₚ_app`

English:
lemma inv_hom_iso_homₚ_app
  given: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  proof: congr($(inv_hom_iso_homₚ _ _).app _)

中文:
引理 inv_hom_iso_homₚ_app
  条件: (f : HP ⟶ HP') (i : ι) (X : TopCat.{u})
  证明: congr($(inv_hom_iso_homₚ _ _).app _)
-/
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X = (f.homₚ i).app (ofTopCat X) :=
  congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
/--
Definition of `hₚFunctor` / `hₚFunctor` 的定义

English:
definition hₚFunctor
  signature: (i : ι)
  body: HP.Hₚ i
  map f := f.homₚ i

中文:
定义 hₚFunctor
  签名: (i : ι)
  定义体: HP.Hₚ i
  map f := f.homₚ i
-/
protected def hₚFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hₚFunctor i).map f))

/-- The forgetful functor that sends a `HomologyPretheory` to it's homology functor `H`. -/
@[simps]
/--
Definition of `hFunctor` / `hFunctor` 的定义

English:
definition hFunctor
  signature: (i : ι)
  body: HP.H i
  map f := f.hom i

中文:
定义 hFunctor
  签名: (i : ι)
  定义体: HP.H i
  map f := f.hom i
-/
protected def hFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hFunctor i).map f))

variable (HP HP' : HomologyPretheory.{u} C c)

/--
Definition of `IsHomotopyInvariant` / `IsHomotopyInvariant` 的定义

English:
class IsHomotopyInvariant
  parameters: (HP : HomologyPretheory.{u} C c)
  axioms and operations (1):
    - map_eq_of_homotopy((HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι)) : (HP.Hₚ i).map f = (HP.Hₚ i).map g  [default: by cat_disch]

中文:
类 IsHomotopyInvariant
  参数: (HP : HomologyPretheory.{u} C c)
  公理与运算 (1 个):
    - map_eq_of_homotopy((HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι)) : (HP.Hₚ i).map f = (HP.Hₚ i).map g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/--
Definition of `isHomotopyInvariant` / `isHomotopyInvariant` 的定义

English:
abbreviation isHomotopyInvariant
  signature: : ObjectProperty (HomologyPretheory.{u} C c)
  body: IsHomotopyInvariant

@[simp]

中文:
缩写 isHomotopyInvariant
  签名: : Object命题erty (HomologyPretheory.{u} C c)
  定义体: IsHomotopyInvariant

@[simp]

Depends on / 依赖: IsHomotopyInvariant
-/
abbrev isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

@[simp]
/--
lemma `isHomotopyInvariant_iff` / 引理 `isHomotopyInvariant_iff`

English:
lemma isHomotopyInvariant_iff
  statement: isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP
  proof: .rfl

中文:
引理 isHomotopyInvariant_iff
  结论: isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP
  证明: .rfl
-/
lemma isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c)
  body: ⟨fun F _ => by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

中文:
实例 :
  签名: IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c)
  定义体: ⟨fun F _ => by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

Depends on / 依赖: NatTrans, NatTrans.naturality, cancel_epi, e.hom.hom, map_eq_of_homotopy, naturality
-/
instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ => by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

end HomologyPretheory

end TopPair
