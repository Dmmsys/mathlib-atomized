/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `AlgebraicGeometry.AffineScheme`: The category of affine schemes.
* `AlgebraicGeometry.IsAffine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.isoSpec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `AlgebraicGeometry.AffineScheme.equivCommRingCat`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat`.
* `AlgebraicGeometry.IsAffineOpen`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `AlgebraicGeometry.IsAffineOpen.fromSpec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/--
Definition of `AffineScheme` / `AffineScheme` 的定义

English:
definition AffineScheme
  body: Scheme.Spec.EssImageSubcategory
deriving Category

中文:
定义 仿射概形
  定义体: Scheme.Spec.EssImageSubcategory
deriving Category

Depends on / 依赖: EssImageSubcategory, Scheme, Scheme.Spec.EssImageSubcategory
-/
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category

/--
Definition of `IsAffine` / `IsAffine` 的定义

English:
class IsAffine
  parameters: (X : Scheme)
  axioms and operations (1):
    - affine : IsIso X.toSpecΓ

中文:
类 是仿射
  参数: (X : 概形)
  公理与运算 (1 个):
    - affine : 是同构 X.toSpecΓ
-/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ

attribute [instance] IsAffine.affine

instance (X : Scheme.{u}) [IsAffine X] : IsIso (ΓSpec.adjunction.unit.app X) := @IsAffine.affine X _

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! -isSimp hom]
/--
Definition of `Scheme.isoSpec` / `Scheme.isoSpec` 的定义

English:
definition Scheme.isoSpec
  signature: (X : Scheme) [IsAffine X]
  body: asIso X.toSpecΓ

@[reassoc]

中文:
定义 概形.isoSpec
  签名: (X : 概形) [是仿射 X]
  定义体: asIso X.toSpecΓ

@[reassoc]

Depends on / 依赖: X.toSpec
-/
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso X.toSpecΓ

@[reassoc]
/--
theorem `Scheme.isoSpec_hom_naturality` / 定理 `Scheme.isoSpec_hom_naturality`

English:
theorem Scheme.isoSpec_hom_naturality
  given: {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
  proof: by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

@[reassoc]

中文:
定理 概形.isoSpec_hom_naturality
  条件: {X Y : 概形} [是仿射 X] [是仿射 Y] (f : X ⟶ Y)
  证明: by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

@[reassoc]

Depends on / 依赖: Scheme, Scheme.toSpec, asIso_hom, isoSpec
-/
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

@[reassoc]
/--
theorem `Scheme.isoSpec_inv_naturality` / 定理 `Scheme.isoSpec_inv_naturality`

English:
theorem Scheme.isoSpec_inv_naturality
  given: {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
  proof: by
  rw [Iso.eq_inv_comp]; rw [isoSpec]; rw [asIso_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]; rw [isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

@[reassoc (attr := simp)]

中文:
定理 概形.isoSpec_inv_naturality
  条件: {X Y : 概形} [是仿射 X] [是仿射 Y] (f : X ⟶ Y)
  证明: by
  rw [Iso.eq_inv_comp]; rw [isoSpec]; rw [asIso_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]; rw [isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.comp_id, IsIso.hom_inv_id, Iso.eq_inv_comp, Scheme, Scheme.toSpec, asIso_hom, asIso_inv, comp_id, eq_inv_comp, hom_inv_id, isoSpec
-/
theorem Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.appTop) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp]; rw [isoSpec]; rw [asIso_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]; rw [isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

@[reassoc (attr := simp)]
/--
lemma `Scheme.toSpecΓ_isoSpec_inv` / 引理 `Scheme.toSpecΓ_isoSpec_inv`

English:
lemma Scheme.toSpecΓ_isoSpec_inv
  given: (X : Scheme.{u}) [IsAffine X]
  proof: X.isoSpec.hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 概形.toSpecΓ_isoSpec_inv
  条件: (X : 概形.{u}) [是仿射 X]
  证明: X.isoSpec.hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: X.isoSpec.hom_inv_id, hom_inv_id, isoSpec
-/
lemma Scheme.toSpecΓ_isoSpec_inv (X : Scheme.{u}) [IsAffine X] :
    X.toSpecΓ ≫ X.isoSpec.inv = 𝟙 _ :=
  X.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `Scheme.isoSpec_inv_toSpecΓ` / 引理 `Scheme.isoSpec_inv_toSpecΓ`

English:
lemma Scheme.isoSpec_inv_toSpecΓ
  given: (X : Scheme.{u}) [IsAffine X]
  proof: X.isoSpec.inv_hom_id

中文:
引理 概形.isoSpec_inv_toSpecΓ
  条件: (X : 概形.{u}) [是仿射 X]
  证明: X.isoSpec.inv_hom_id

Depends on / 依赖: X.isoSpec.inv_hom_id, inv_hom_id, isoSpec
-/
lemma Scheme.isoSpec_inv_toSpecΓ (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv ≫ X.toSpecΓ = 𝟙 _ :=
  X.isoSpec.inv_hom_id

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version. -/
@[simps]
/--
Definition of `AffineScheme.mk` / `AffineScheme.mk` 的定义

English:
definition AffineScheme.mk
  signature: (X : Scheme) (_ : IsAffine X)
  body: ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

中文:
定义 仿射概形.mk
  签名: (X : 概形) (_ : 是仿射 X)
  定义体: ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

Depends on / 依赖: Spec.adjunction.mem_essImage_of_unit_isIso, adjunction, mem_essImage_of_unit_isIso
-/
def AffineScheme.mk (X : Scheme) (_ : IsAffine X) : AffineScheme :=
  ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/--
Definition of `AffineScheme.of` / `AffineScheme.of` 的定义

English:
definition AffineScheme.of
  signature: (X : Scheme) [h : IsAffine X]
  body: AffineScheme.mk X h

中文:
定义 仿射概形.of
  签名: (X : 概形) [h : 是仿射 X]
  定义体: AffineScheme.mk X h

Depends on / 依赖: AffineScheme, AffineScheme.mk
-/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h

/--
Definition of `AffineScheme.ofHom` / `AffineScheme.ofHom` 的定义

English:
definition AffineScheme.ofHom
  signature: {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
  body: InducedCategory.homMk f

@[simp]

中文:
定义 仿射概形.ofHom
  签名: {X Y : 概形} [是仿射 X] [是仿射 Y] (f : X ⟶ Y)
  定义体: InducedCategory.homMk f

@[simp]

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  InducedCategory.homMk f

@[simp]
/--
theorem `essImage_Spec` / 定理 `essImage_Spec`

English:
theorem essImage_Spec
  given: {X : Scheme}
  statement: Scheme.Spec.essImage X ↔ IsAffine X
  proof: ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

中文:
定理 essImage_Spec
  条件: {X : 概形}
  结论: 概形.Spec.essImage X ↔ 是仿射 X
  证明: ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, Spec.adjunction.mem_essImage_of_unit_isIso, adjunction, essImage, mem_essImage_of_unit_isIso, unit_isIso
-/
theorem essImage_Spec {X : Scheme} : Scheme.Spec.essImage X ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/--
Instance `isAffine_affineScheme` / 实例 `isAffine_affineScheme`

English:
instance isAffine_affineScheme
  signature: (X : AffineScheme.{u})
  body: ⟨Functor.essImage.unit_isIso X.property⟩

中文:
实例 isAffine_affineScheme
  签名: (X : 仿射概形.{u})
  定义体: ⟨Functor.essImage.unit_isIso X.property⟩

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, X.property, essImage, property, unit_isIso
-/
instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩

instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩

/--
Instance `isAffine_Spec` / 实例 `isAffine_Spec`

English:
instance isAffine_Spec
  signature: (R : CommRingCat)
  body: AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

中文:
实例 isAffine_Spec
  签名: (R : 交换环范畴)
  定义体: AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.isAffine_affineScheme, MorphismProperty, MorphismProperty.pullback_fst, Scheme, Scheme.Spec.obj_mem_essImage, isAffine_affineScheme, obj_mem_essImage, pullback_fst
-/
instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

/--
theorem `IsAffine.of_isIso` / 定理 `IsAffine.of_isIso`

English:
theorem IsAffine.of_isIso
  given: {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y]
  statement: IsAffine X
  proof: by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

中文:
定理 是仿射.of_isIso
  条件: {X Y : 概形} (f : X ⟶ Y) [是同构 f] [h : 是仿射 Y]
  结论: 是仿射 X
  证明: by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

Depends on / 依赖: Functor, Functor.essImage.ofIso, MorphismProperty, MorphismProperty.pullback_snd, essImage, essImage_Spec, pullback_snd
-/
theorem IsAffine.of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

/--
theorem `IsAffine.iff_of_isIso` / 定理 `IsAffine.iff_of_isIso`

English:
theorem IsAffine.iff_of_isIso
  given: {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
  statement: IsAffine X ↔ IsAffine Y
  proof: ⟨fun _ => .of_isIso (inv f), fun _ => .of_isIso f⟩

中文:
定理 是仿射.iff_of_isIso
  条件: {X Y : 概形} (f : X ⟶ Y) [是同构 f]
  结论: 是仿射 X ↔ 是仿射 Y
  证明: ⟨fun _ => .of_isIso (inv f), fun _ => .of_isIso f⟩

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, of_isIso, restrict
-/
theorem IsAffine.iff_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsAffine X ↔ IsAffine Y :=
  ⟨fun _ => .of_isIso (inv f), fun _ => .of_isIso f⟩

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
/--
Definition of `arrowIsoSpecΓOfIsAffine` / `arrowIsoSpecΓOfIsAffine` 的定义

English:
definition arrowIsoSpecΓOfIsAffine
  signature: {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
  body: Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

中文:
定义 arrowIsoSpecΓOfIsAffine
  签名: {X Y : 概形} [是仿射 X] [是仿射 Y] (f : X ⟶ Y)
  定义体: Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

Depends on / 依赖: Arrow.isoMk, Scheme, Scheme.Hom.resLE, Spec.adjunction.unit_naturality, X.isoSpec, Y.isoSpec, adjunction, infer_instance, isoSpec, unit_naturality
-/
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

/--
Definition of `arrowIsoΓSpecOfIsAffine` / `arrowIsoΓSpecOfIsAffine` 的定义

English:
definition arrowIsoΓSpecOfIsAffine
  signature: {A B : CommRingCat} (f : A ⟶ B)
  body: Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

中文:
定义 arrowIsoΓSpecOfIsAffine
  签名: {A B : 交换环范畴} (f : A ⟶ B)
  定义体: Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

Depends on / 依赖: Arrow.isoMk, Scheme
-/
def arrowIsoΓSpecOfIsAffine {A B : CommRingCat} (f : A ⟶ B) :
    Arrow.mk f ≅ Arrow.mk ((Spec.map f).appTop) :=
  Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

/--
theorem `Scheme.isoSpec_Spec` / 定理 `Scheme.isoSpec_Spec`

English:
theorem Scheme.isoSpec_Spec
  given: (R : CommRingCat.{u})
  proof: Iso.ext (SpecMap_ΓSpecIso_hom R).symm

中文:
定理 概形.isoSpec_Spec
  条件: (R : 交换环范畴.{u})
  证明: Iso.ext (SpecMap_ΓSpecIso_hom R).symm

Depends on / 依赖: Iso.ext
-/
theorem Scheme.isoSpec_Spec (R : CommRingCat.{u}) :
    (Spec R).isoSpec = Scheme.Spec.mapIso (Scheme.ΓSpecIso R).op :=
  Iso.ext (SpecMap_ΓSpecIso_hom R).symm

/--
theorem `Scheme.isoSpec_Spec_hom` / 定理 `Scheme.isoSpec_Spec_hom`

English:
theorem Scheme.isoSpec_Spec_hom
  given: (R : CommRingCat.{u})
  proof: (SpecMap_ΓSpecIso_hom R).symm

中文:
定理 概形.isoSpec_Spec_hom
  条件: (R : 交换环范畴.{u})
  证明: (SpecMap_ΓSpecIso_hom R).symm
-/
@[simp] theorem Scheme.isoSpec_Spec_hom (R : CommRingCat.{u}) :
    (Spec R).isoSpec.hom = Spec.map (Scheme.ΓSpecIso R).hom :=
  (SpecMap_ΓSpecIso_hom R).symm

/--
theorem `Scheme.isoSpec_Spec_inv` / 定理 `Scheme.isoSpec_Spec_inv`

English:
theorem Scheme.isoSpec_Spec_inv
  given: (R : CommRingCat.{u})
  proof: congr($(isoSpec_Spec R).inv)

中文:
定理 概形.isoSpec_Spec_inv
  条件: (R : 交换环范畴.{u})
  证明: congr($(isoSpec_Spec R).inv)
-/
@[simp] theorem Scheme.isoSpec_Spec_inv (R : CommRingCat.{u}) :
    (Spec R).isoSpec.inv = Spec.map (Scheme.ΓSpecIso R).inv :=
  congr($(isoSpec_Spec R).inv)

/--
lemma `ext_of_isAffine` / 引理 `ext_of_isAffine`

English:
lemma ext_of_isAffine
  given: {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop)
  proof: by
  rw [← cancel_mono Y.toSpecΓ]; rw [Scheme.toSpecΓ_naturality]; rw [Scheme.toSpecΓ_naturality]; rw [e]

中文:
引理 ext_of_isAffine
  条件: {X Y : 概形} [是仿射 Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop)
  证明: by
  rw [← cancel_mono Y.toSpecΓ]; rw [Scheme.toSpecΓ_naturality]; rw [Scheme.toSpecΓ_naturality]; rw [e]

Depends on / 依赖: Scheme, Scheme.toSpec, Y.toSpec, cancel_mono
-/
lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop) :
    f = g := by
  rw [← cancel_mono Y.toSpecΓ]; rw [Scheme.toSpecΓ_naturality]; rw [Scheme.toSpecΓ_naturality]; rw [e]

instance (P : MorphismProperty Scheme.{u}) {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) :
    IsAffine (𝒰.cover.X i) :=
inferInstanceAs IsAffine (Spec _)

/--
Instance `preservesLimit_rightOp_Γ.` / 实例 `preservesLimit_rightOp_Γ.`

English:
instance preservesLimit_rightOp_Γ.{v,
  signature: w}
  body: by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  suffices PreservesLimit ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) Scheme.Γ.rightOp from
    preservesLimit_o

中文:
实例 preservesLimit_rightOp_Γ.{v,
  签名: w}
  定义体: by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  suffices PreservesLimit ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) Scheme.Γ.rightOp from
    preservesLimit_o

Depends on / 依赖: D.whiskerLeft, IsAffine, IsAffine.affine, NatIso, NatIso.isIso_of_isIso_app, PreservesLimit, Scheme, Scheme.Spec, Spec.adjunction.unit, adjunction, affine, isIso_of_isIso_app, monadicCreatesLimits, preservesLimit_comp_of_createsLimit, preservesLimit_of_iso_diagram, rightOp, whiskerLeft
-/
instance preservesLimit_rightOp_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) [forall i, IsAffine (D.obj i)] :
    PreservesLimit D Scheme.Γ.rightOp := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  suffices PreservesLimit ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) Scheme.Γ.rightOp from
    preservesLimit_of_iso_diagram _ (asIso α).symm
  have := monadicCreatesLimits.{v, w} Scheme.Spec.{u}
  suffices PreservesLimit (D ⋙ Scheme.Γ.rightOp) (Scheme.Spec ⋙ Scheme.Γ.rightOp) from
    preservesLimit_comp_of_createsLimit _ _
  exact preservesLimit_of_natIso _ (NatIso.op Scheme.SpecΓIdentity)

/--
Instance `preservesColimit_Γ.` / 实例 `preservesColimit_Γ.`

English:
instance preservesColimit_Γ.{v,
  signature: w}
  body: by
  have (i : _) : IsAffine (D.leftOp.obj i) := Functor.leftOp_obj D _ ▸ inferInstance
  exact preservesColimit_of_rightOp D Scheme.Γ

中文:
实例 preservesColimit_Γ.{v,
  签名: w}
  定义体: by
  have (i : _) : IsAffine (D.leftOp.obj i) := Functor.leftOp_obj D _ ▸ inferInstance
  exact preservesColimit_of_rightOp D Scheme.Γ

Depends on / 依赖: D.leftOp.obj, Functor, Functor.leftOp_obj, IsAffine, Scheme, leftOp, leftOp_obj, preservesColimit_of_rightOp
-/
instance preservesColimit_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}ᵒᵖ) [forall i, IsAffine (D.obj i).unop] :
    PreservesColimit D Scheme.Γ := by
  have (i : _) : IsAffine (D.leftOp.obj i) := Functor.leftOp_obj D _ ▸ inferInstance
  exact preservesColimit_of_rightOp D Scheme.Γ

namespace AffineScheme

/--
Definition of `Spec` / `Spec` 的定义

English:
definition Spec
  signature: : CommRingCatᵒᵖ ⥤ AffineScheme
  body: Scheme.Spec.toEssImage

中文:
定义 Spec
  签名: : CommRingCatᵒᵖ ⥤ 仿射概形
  定义体: Scheme.Spec.toEssImage

Depends on / 依赖: Scheme, Scheme.Spec.toEssImage, toEssImage
-/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage


/--
Instance `Spec_full` / 实例 `Spec_full`

English:
instance Spec_full
  signature: : Spec.Full
  body: Functor.Full.toEssImage _

中文:
实例 Spec_full
  签名: : Spec.满
  定义体: Functor.Full.toEssImage _

Depends on / 依赖: Functor, Functor.Full.toEssImage, toEssImage
-/
instance Spec_full : Spec.Full := Functor.Full.toEssImage _

/--
Instance `Spec_faithful` / 实例 `Spec_faithful`

English:
instance Spec_faithful
  signature: : Spec.Faithful
  body: Functor.Faithful.toEssImage _

中文:
实例 Spec_faithful
  签名: : Spec.忠实
  定义体: Functor.Faithful.toEssImage _

Depends on / 依赖: Faithful, Functor, Functor.Faithful.toEssImage, toEssImage
-/
instance Spec_faithful : Spec.Faithful := Functor.Faithful.toEssImage _

/--
Instance `Spec_essSurj` / 实例 `Spec_essSurj`

English:
instance Spec_essSurj
  signature: : Spec.EssSurj
  body: Functor.EssSurj.toEssImage (F := _)

中文:
实例 Spec_essSurj
  签名: : Spec.本质满射
  定义体: Functor.EssSurj.toEssImage (F := _)

Depends on / 依赖: EssSurj, Functor, Functor.EssSurj.toEssImage, toEssImage
-/
instance Spec_essSurj : Spec.EssSurj := Functor.EssSurj.toEssImage (F := _)

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps!]
/--
Definition of `forgetToScheme` / `forgetToScheme` 的定义

English:
definition forgetToScheme
  signature: : AffineScheme ⥤ Scheme
  body: Scheme.Spec.essImage.ι

中文:
定义 forgetToScheme
  签名: : 仿射概形 ⥤ 概形
  定义体: Scheme.Spec.essImage.ι

Depends on / 依赖: QuasiSeparated, QuasiSeparated.of_quasiSeparatedSpace, Scheme, Scheme.Spec.essImage, essImage, of_quasiSeparatedSpace
-/
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImage.ι


/--
Instance `forgetToScheme_full` / 实例 `forgetToScheme_full`

English:
instance forgetToScheme_full
  signature: : forgetToScheme.Full
  body: inferInstanceAs Scheme.Spec.essImage.ι.Full

中文:
实例 forgetToScheme_full
  签名: : forgetToScheme.满
  定义体: inferInstanceAs Scheme.Spec.essImage.ι.Full

Depends on / 依赖: Scheme, Scheme.Spec.essImage, essImage
-/
instance forgetToScheme_full : forgetToScheme.Full :=
  inferInstanceAs Scheme.Spec.essImage.ι.Full

/--
Instance `forgetToScheme_faithful` / 实例 `forgetToScheme_faithful`

English:
instance forgetToScheme_faithful
  signature: : forgetToScheme.Faithful
  body: inferInstanceAs Scheme.Spec.essImage.ι.Faithful

中文:
实例 forgetToScheme_faithful
  签名: : forgetToScheme.忠实
  定义体: inferInstanceAs Scheme.Spec.essImage.ι.Faithful

Depends on / 依赖: Faithful, Scheme, Scheme.Spec.essImage, essImage
-/
instance forgetToScheme_faithful : forgetToScheme.Faithful :=
  inferInstanceAs Scheme.Spec.essImage.ι.Faithful

/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : AffineSchemeᵒᵖ ⥤ CommRingCat
  body: forgetToScheme.op ⋙ Scheme.Γ

中文:
定义 Γ
  签名: : AffineSchemeᵒᵖ ⥤ 交换环范畴
  定义体: forgetToScheme.op ⋙ Scheme.Γ

Depends on / 依赖: Scheme, forgetToScheme, forgetToScheme.op
-/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ

/--
Definition of `equivCommRingCat` / `equivCommRingCat` 的定义

English:
definition equivCommRingCat
  signature: : AffineScheme ≌ CommRingCatᵒᵖ
  body: equivEssImageOfReflective.symm

中文:
定义 equivCommRingCat
  签名: : 仿射概形 ≌ CommRingCatᵒᵖ
  定义体: equivEssImageOfReflective.symm

Depends on / 依赖: equivEssImageOfReflective, equivEssImageOfReflective.symm
-/
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Γ.{u}.rightOp.IsEquivalence
  body: equivCommRingCat.isEquivalence_functor

中文:
实例 :
  签名: Γ.{u}.rightOp.是等价
  定义体: equivCommRingCat.isEquivalence_functor

Depends on / 依赖: Scheme, equivCommRingCat, equivCommRingCat.isEquivalence_functor, isEquivalence_functor, quasiCompact_of_compactSpace
-/
instance : Γ.{u}.rightOp.IsEquivalence := equivCommRingCat.isEquivalence_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Γ.{u}.rightOp.op.IsEquivalence
  body: equivCommRingCat.op.isEquivalence_functor

中文:
实例 :
  签名: Γ.{u}.rightOp.op.是等价
  定义体: equivCommRingCat.op.isEquivalence_functor

Depends on / 依赖: equivCommRingCat, equivCommRingCat.op.isEquivalence_functor, isEquivalence_functor
-/
instance : Γ.{u}.rightOp.op.IsEquivalence := equivCommRingCat.op.isEquivalence_functor

/--
Instance `ΓIsEquiv` / 实例 `ΓIsEquiv`

English:
instance ΓIsEquiv
  signature: : Γ.{u}.IsEquivalence
  body: inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence

中文:
实例 ΓIsEquiv
  签名: : Γ.{u}.是等价
  定义体: inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence

Depends on / 依赖: IsEquivalence, functor, opOpEquivalence, rightOp, rightOp.op
-/
instance ΓIsEquiv : Γ.{u}.IsEquivalence :=
  inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence

/--
Instance `hasColimits` / 实例 `hasColimits`

English:
instance hasColimits
  signature: : HasColimits AffineScheme.{u}
  body: haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

中文:
实例 hasColimits
  签名: : 有余极限 仿射概形.{u}
  定义体: haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

Depends on / 依赖: Adjunction, Adjunction.has_colimits_of_equivalence, Adjunction.has_limits_of_equivalence, AffineScheme, has_colimits_of_equivalence, has_limits_of_equivalence, inverse, opOpEquivalence
-/
instance hasColimits : HasColimits AffineScheme.{u} :=
  haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits AffineScheme.{u}
  body: by
  have := Adjunction.has_colimits_of_equivalence Γ.{u}
  have : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse

中文:
实例 hasLimits
  签名: : 有极限 仿射概形.{u}
  定义体: by
  have := Adjunction.has_colimits_of_equivalence Γ.{u}
  have : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse

Depends on / 依赖: Adjunction, Adjunction.has_colimits_of_equivalence, Adjunction.has_limits_of_equivalence, AffineScheme, HasLimits, Limits, Limits.hasLimits_op_of_hasColimits, hasLimits_op_of_hasColimits, has_colimits_of_equivalence, has_limits_of_equivalence, inverse, opOpEquivalence
-/
instance hasLimits : HasLimits AffineScheme.{u} := by
  have := Adjunction.has_colimits_of_equivalence Γ.{u}
  have : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse

/--
Instance `Γ_preservesLimits` / 实例 `Γ_preservesLimits`

English:
instance Γ_preservesLimits
  signature: : PreservesLimits Γ.{u}.rightOp
  body: inferInstance

中文:
实例 Γ_preservesLimits
  签名: : PreservesLimits Γ.{u}.rightOp
  定义体: inferInstance
-/
noncomputable instance Γ_preservesLimits : PreservesLimits Γ.{u}.rightOp := inferInstance

/--
Instance `forgetToScheme_preservesLimits` / 实例 `forgetToScheme_preservesLimits`

English:
instance forgetToScheme_preservesLimits
  signature: : PreservesLimits forgetToScheme
  body: by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

中文:
实例 forgetToScheme_preservesLimits
  签名: : PreservesLimits forgetToScheme
  定义体: by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

Depends on / 依赖: Functor, Functor.isoWhiskerRight, PreservesLimits, Scheme, Scheme.Spec, allowSynthFailures, equivCommRingCat, equivCommRingCat.functor, equivCommRingCat.unitIso, forgetToScheme, functor, infer_instance, isoWhiskerRight, preservesLimits_of_natIso, unitIso
-/
noncomputable instance forgetToScheme_preservesLimits : PreservesLimits forgetToScheme := by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

/--
Instance `createsLimitsForgetToScheme` / 实例 `createsLimitsForgetToScheme`

English:
instance createsLimitsForgetToScheme
  signature: : CreatesLimits forgetToScheme.{u}
  body: ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩⟩

中文:
实例 createsLimitsForgetToScheme
  签名: : CreatesLimits forgetToScheme.{u}
  定义体: ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩⟩

Depends on / 依赖: createsLimitOfReflectsIsomorphismsOfPreserves
-/
instance createsLimitsForgetToScheme : CreatesLimits forgetToScheme.{u} :=
  ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩⟩

end AffineScheme

/--
Definition of `IsAffineOpen` / `IsAffineOpen` 的定义

English:
definition IsAffineOpen
  signature: {X : Scheme} (U : X.Opens)
  body: IsAffine U

中文:
定义 是仿射开集
  签名: {X : 概形} (U : X.Opens)
  定义体: IsAffine U

Depends on / 依赖: IsAffine
-/
def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U

/--
Definition of `Scheme.affineOpens` / `Scheme.affineOpens` 的定义

English:
definition Scheme.affineOpens
  signature: (X : Scheme)
  body: {U : X.Opens | IsAffineOpen U}

中文:
定义 概形.affineOpens
  签名: (X : 概形)
  定义体: {U : X.Opens | IsAffineOpen U}

Depends on / 依赖: IsAffineOpen, X.Opens
-/
def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}

instance {Y : Scheme.{u}} (U : Y.affineOpens) : IsAffine U :=
  U.property

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isAffineOpen_opensRange` / 定理 `isAffineOpen_opensRange`

English:
theorem isAffineOpen_opensRange
  statement: {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
  proof: by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

中文:
定理 isAffineOpen_opensRange
  结论: {X Y : 概形} [是仿射 X] (f : X ⟶ Y)
  证明: by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Subtype, Subtype.range_val.symm, Y.ofRestrict, isoOfRangeEq, ofRestrict, of_isIso, range_val
-/
theorem isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen f.opensRange := by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

/--
theorem `isAffineOpen_top` / 定理 `isAffineOpen_top`

English:
theorem isAffineOpen_top
  given: (X : Scheme) [IsAffine X]
  statement: IsAffineOpen (⊤ : X.Opens)
  proof: by
  convert! isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

中文:
定理 isAffineOpen_top
  条件: (X : 概形) [是仿射 X]
  结论: 是仿射开集 (⊤ : X.Opens)
  证明: by
  convert! isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

Depends on / 依赖: Set.range_id.symm, convert, isAffineOpen_opensRange, range_id
-/
theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens) := by
  convert! isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

/--
theorem `exists_isAffineOpen_mem_and_subset` / 定理 `exists_isAffineOpen_mem_and_subset`

English:
theorem exists_isAffineOpen_mem_and_subset
  statement: {X : Scheme.{u}} {x : X}
  proof: by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩

中文:
定理 存在_isAffineOpen_mem_and_subset
  结论: {X : 概形.{u}} {x : X}
  证明: by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset, AlgebraicGeometry.isAffineOpen_opensRange, Scheme, Scheme.Hom.opensRange, exists_affine_mem_range_and_range_subset, isAffineOpen_opensRange, opensRange
-/
theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x in U) : exists W : X.Opens, IsAffineOpen W ∧ x in W ∧ W.1 subseteq U := by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩

/--
lemma `Scheme.exists_Spec_apply_eq` / 引理 `Scheme.exists_Spec_apply_eq`

English:
lemma Scheme.exists_Spec_apply_eq
  given: {X : Scheme.{u}} (x : X)
  proof: ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩

中文:
引理 概形.存在_Spec_apply_eq
  条件: {X : 概形.{u}} (x : X)
  证明: ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩

Depends on / 依赖: X.affineOpenCover.X, X.affineOpenCover.covers, X.affineOpenCover.f, affineOpenCover, covers
-/
lemma Scheme.exists_Spec_apply_eq {X : Scheme.{u}} (x : X) :
    exists (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
    f.base y = x :=
  ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩

/--
Instance `Scheme.isAffine_affineCover` / 实例 `Scheme.isAffine_affineCover`

English:
instance Scheme.isAffine_affineCover
  signature: (X : Scheme) (i : X.affineCover.I₀)
  body: isAffine_Spec _

中文:
实例 概形.isAffine_affineCover
  签名: (X : 概形) (i : X.affineCover.I₀)
  定义体: isAffine_Spec _

Depends on / 依赖: isAffine_Spec
-/
instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.I₀) :
    IsAffine (X.affineCover.X i) :=
  isAffine_Spec _

/--
Instance `Scheme.isAffine_affineBasisCover` / 实例 `Scheme.isAffine_affineBasisCover`

English:
instance Scheme.isAffine_affineBasisCover
  signature: (X : Scheme) (i : X.affineBasisCover.I₀)
  body: isAffine_Spec _

中文:
实例 概形.isAffine_affineBasisCover
  签名: (X : 概形) (i : X.affineBasisCover.I₀)
  定义体: isAffine_Spec _

Depends on / 依赖: isAffine_Spec
-/
instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.I₀) :
    IsAffine (X.affineBasisCover.X i) :=
  isAffine_Spec _

/--
Instance `Scheme.isAffine_affineOpenCover` / 实例 `Scheme.isAffine_affineOpenCover`

English:
instance Scheme.isAffine_affineOpenCover
  signature: (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀)
  body: inferInstanceAs (IsAffine (Spec (𝒰.X i)))

中文:
实例 概形.isAffine_affineOpenCover
  签名: (X : 概形) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀)
  定义体: inferInstanceAs (IsAffine (Spec (𝒰.X i)))

Depends on / 依赖: IsAffine
-/
instance Scheme.isAffine_affineOpenCover (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀) :
    IsAffine (𝒰.openCover.X i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.X i)))

instance (X : Scheme) [CompactSpace X] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] (i) :
    IsAffine (𝒰.finiteSubcover.X i) :=
  inferInstanceAs (IsAffine (𝒰.X _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {X} [IsAffine X] (i) :
    IsAffine ((Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 X)).X i) := by
  dsimp; infer_instance

/--
theorem `Scheme.isBasis_affineOpens` / 定理 `Scheme.isBasis_affineOpens`

English:
theorem Scheme.isBasis_affineOpens
  given: (X : Scheme)
  statement: Opens.IsBasis X.affineOpens
  proof: by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x in (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _

中文:
定理 概形.isBasis_affineOpens
  条件: (X : 概形)
  结论: Opens.是基 X.affineOpens
  证明: by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x in (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _

Depends on / 依赖: Opens.isBasis_iff_nbhd, U.isOpen, X.affineBasisCover_is_basis.exists_subset_of_mem_open, X.affineBasisCover_is_basis.isOpen, affineBasisCover_is_basis, exists_subset_of_mem_open, isAffineOpen_opensRange, isBasis_iff_nbhd, isOpen
-/
theorem Scheme.isBasis_affineOpens (X : Scheme) : Opens.IsBasis X.affineOpens := by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x in (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _

/--
theorem `iSup_affineOpens_eq_top` / 定理 `iSup_affineOpens_eq_top`

English:
theorem iSup_affineOpens_eq_top
  given: (X : Scheme)
  statement: ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
  proof: by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact X.isBasis_affineOpens

中文:
定理 iSup_affineOpens_eq_top
  条件: (X : 概形)
  结论: ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
  证明: by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact X.isBasis_affineOpens

Depends on / 依赖: IsTopologicalBasis, IsTopologicalBasis.sUnion_eq, Opens.coe_iSup, Opens.ext, Set.image_eq_range, X.isBasis_affineOpens, coe_iSup, image_eq_range, isBasis_affineOpens, sUnion_eq
-/
theorem iSup_affineOpens_eq_top (X : Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact X.isBasis_affineOpens

/--
theorem `Scheme.map_PrimeSpectrum_basicOpen_of_affine` / 定理 `Scheme.map_PrimeSpectrum_basicOpen_of_affine`

English:
theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
  proof: Scheme.toSpecΓ_preimage_basicOpen _ _

中文:
定理 概形.map_PrimeSpectrum_basicOpen_of_affine
  证明: Scheme.toSpecΓ_preimage_basicOpen _ _

Depends on / 依赖: Scheme, Scheme.toSpec
-/
theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
    (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  Scheme.toSpecΓ_preimage_basicOpen _ _

/--
theorem `isBasis_basicOpen` / 定理 `isBasis_basicOpen`

English:
theorem isBasis_basicOpen
  given: (X : Scheme) [IsAffine X]
  proof: by
  convert!
    PrimeSpectrum.isBasis_basic_opens.of_isInducing
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_ofPred,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

中文:
定理 isBasis_basicOpen
  条件: (X : 概形) [是仿射 X]
  证明: by
  convert!
    PrimeSpectrum.isBasis_basic_opens.of_isInducing
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_ofPred,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

Depends on / 依赖: Opens.coe_inj, PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.of_isInducing, Scheme, Scheme.forgetToTop.mapIso, Scheme.toSpec, Set.mem_ofPred, Set.mem_range, TopCat, TopCat.homeoOfIso, X.isoSpec, coe_inj, convert, exists_exists_eq_and, forgetToTop, homeoOfIso, isBasis_basic_opens, isInducing, isoSpec, mapIso
-/
theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) -> X.Opens)) := by
  convert!
    PrimeSpectrum.isBasis_basic_opens.of_isInducing
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_ofPred,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-- The canonical map `U ⟶ Spec Γ(X, U)` for an open `U ⊆ X`. -/
noncomputable
/--
Definition of `Scheme.Opens.toSpecΓ` / `Scheme.Opens.toSpecΓ` 的定义

English:
definition Scheme.Opens.toSpecΓ
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

中文:
定义 概形.Opens.toSpecΓ
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

Depends on / 依赖: Spec.map, U.toScheme.toSpec, U.topIso.inv, toScheme, topIso
-/
def Scheme.Opens.toSpecΓ {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme ⟶ Spec Γ(X, U) :=
  U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map` / 引理 `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`

English:
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map
  given: {X : Scheme} (U V : X.Opens) (h : U <= V)
  proof: by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

中文:
引理 概形.Opens.toSpecΓ_SpecMap_presheaf_map
  条件: {X : 概形} (U V : X.Opens) (h : U <= V)
  证明: by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

Depends on / 依赖: Scheme, Scheme.Opens.toSpec, Spec.map_comp, X.presheaf.map_comp, map_comp, presheaf
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map {X : Scheme} (U V : X.Opens) (h : U <= V) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE h).op) = X.homOfLE h ≫ V.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] -- not simp because simp can prove this.
/--
lemma `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top` / 引理 `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top`

English:
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top
  given: {X : Scheme} (U : X.Opens)
  proof: by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality]

@[simp]

中文:
引理 概形.Opens.toSpecΓ_SpecMap_presheaf_map_top
  条件: {X : 概形} (U : X.Opens)
  证明: by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality]

@[simp]

Depends on / 依赖: Scheme, Scheme.Opens.toSpec, Spec.map_comp, X.presheaf.map_comp, map_comp, presheaf
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top {X : Scheme} (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE le_top).op) = U.ι ≫ X.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality]

@[simp]
/--
lemma `Scheme.Opens.toSpecΓ_top` / 引理 `Scheme.Opens.toSpecΓ_top`

English:
lemma Scheme.Opens.toSpecΓ_top
  given: {X : Scheme}
  proof: by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

中文:
引理 概形.Opens.toSpecΓ_top
  条件: {X : 概形}
  证明: by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

Depends on / 依赖: Scheme, Scheme.Opens.toSpec
-/
lemma Scheme.Opens.toSpecΓ_top {X : Scheme} :
    (⊤ : X.Opens).toSpecΓ = (⊤ : X.Opens).ι ≫ X.toSpecΓ := by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Scheme.Opens.toSpecΓ_appTop` / 引理 `Scheme.Opens.toSpecΓ_appTop`

English:
lemma Scheme.Opens.toSpecΓ_appTop
  given: {X : Scheme.{u}} (U : X.Opens)
  proof: by
  simp [Scheme.Opens.toSpecΓ]

中文:
引理 概形.Opens.toSpecΓ_appTop
  条件: {X : 概形.{u}} (U : X.Opens)
  证明: by
  simp [Scheme.Opens.toSpecΓ]

Depends on / 依赖: Scheme, Scheme.Opens.toSpec
-/
lemma Scheme.Opens.toSpecΓ_appTop {X : Scheme.{u}} (U : X.Opens) :
    U.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [Scheme.Opens.toSpecΓ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.toSpecΓ_naturality` / 引理 `Scheme.Opens.toSpecΓ_naturality`

English:
lemma Scheme.Opens.toSpecΓ_naturality
  given: {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens)
  proof: by
  simp only [toSpecΓ, topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

@[reassoc (attr := simp)]

中文:
引理 概形.Opens.toSpecΓ_naturality
  条件: {X Y : 概形} (f : X ⟶ Y) (U : Y.Opens)
  证明: by
  simp only [toSpecΓ, topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.mapIso_inv, Hom.appLE_map, Hom.app_eq_appLE, Hom.map_appLE, Iso.op_inv, Spec.map_comp, TopologicalSpace, TopologicalSpace.Opens.map_top, appLE_map, app_eq_appLE, eqToHom_op, eqToIso, eqToIso.inv, mapIso_inv, map_appLE, map_comp, map_top
-/
lemma Scheme.Opens.toSpecΓ_naturality {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) = f ∣_ U ≫ U.toSpecΓ := by
  simp only [toSpecΓ, topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

@[reassoc (attr := simp)]
/--
lemma `Scheme.Opens.toSpecΓ_SpecMap_appLE` / 引理 `Scheme.Opens.toSpecΓ_SpecMap_appLE`

English:
lemma Scheme.Opens.toSpecΓ_SpecMap_appLE
  proof: by
  simp [Hom.appLE, Hom.resLE]

中文:
引理 概形.Opens.toSpecΓ_SpecMap_appLE
  证明: by
  simp [Hom.appLE, Hom.resLE]

Depends on / 依赖: Hom.appLE, Hom.resLE, IsZariskiLocalAtTarget
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_appLE
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hUV) :
    V.toSpecΓ ≫ Spec.map (f.appLE U V hUV) = f.resLE U V hUV ≫ U.toSpecΓ := by
  simp [Hom.appLE, Hom.resLE]

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))

set_option backward.isDefEq.respectTransparency.types false in
attribute [-simp] eqToHom_op in
/-- The isomorphism `U ≅ Spec Γ(X, U)` for an affine `U`. -/
@[simps! -isSimp inv]
/--
Definition of `isoSpec` / `isoSpec` 的定义

English:
definition isoSpec
  signature: :
  body: haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op

中文:
定义 isoSpec
  签名: :
  定义体: haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op

Depends on / 依赖: IsAffine, Scheme, Scheme.Spec.mapIso, U.toScheme.isoSpec, U.topIso.symm.op, isoSpec, mapIso, toScheme, topIso
-/
def isoSpec :
    ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op

/--
lemma `isoSpec_hom` / 引理 `isoSpec_hom`

English:
lemma isoSpec_hom
  statement: hU.isoSpec.hom = U.toSpecΓ
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 isoSpec_hom
  结论: hU.isoSpec.hom = U.toSpecΓ
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma isoSpec_hom : hU.isoSpec.hom = U.toSpecΓ := rfl

@[reassoc (attr := simp)]
/--
lemma `toSpecΓ_isoSpec_inv` / 引理 `toSpecΓ_isoSpec_inv`

English:
lemma toSpecΓ_isoSpec_inv
  statement: U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _
  proof: hU.isoSpec.hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 toSpecΓ_isoSpec_inv
  结论: U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _
  证明: hU.isoSpec.hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hU.isoSpec.hom_inv_id, hom_inv_id, isoSpec
-/
lemma toSpecΓ_isoSpec_inv : U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _ := hU.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoSpec_inv_toSpecΓ` / 引理 `isoSpec_inv_toSpecΓ`

English:
lemma isoSpec_inv_toSpecΓ
  statement: hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _
  proof: hU.isoSpec.inv_hom_id

中文:
引理 isoSpec_inv_toSpecΓ
  结论: hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _
  证明: hU.isoSpec.inv_hom_id

Depends on / 依赖: hU.isoSpec.inv_hom_id, inv_hom_id, isoSpec
-/
lemma isoSpec_inv_toSpecΓ : hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _ := hU.isoSpec.inv_hom_id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
/--
lemma `isoSpec_hom_apply` / 引理 `isoSpec_hom_apply`

English:
lemma isoSpec_hom_apply
  given: (x : U)
  proof: by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_apply, Scheme.Opens.toSpecΓ,
    TopCat.Presheaf.Γgerm]
  rw [← Scheme.Hom.comp_apply]; rw [← Spec.map_comp]; rw [(Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial)]; rw [X.presheaf.germ_res_assoc]; r

中文:
引理 isoSpec_hom_apply
  条件: (x : U)
  证明: by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_apply, Scheme.Opens.toSpecΓ,
    TopCat.Presheaf.Γgerm]
  rw [← Scheme.Hom.comp_apply]; rw [← Spec.map_comp]; rw [(Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial)]; rw [X.presheaf.germ_res_assoc]; r

Depends on / 依赖: IsAffineOpen, IsAffineOpen.isoSpec_hom, IsLocalRing, IsLocalRing.comap_closedPoint, Iso.eq_comp_inv, Presheaf, Scheme, Scheme.Hom.comp_apply, Scheme.Opens.germ_stalkIso_hom, Scheme.Opens.toSpec, Scheme.isoSpec_hom, Scheme.toSpec, Spec.map_comp, TopCat, TopCat.Presheaf, U.stalkIso, X.presheaf.germ_res_assoc, comap_closedPoint, comp_apply, eq_comp_inv
-/
lemma isoSpec_hom_apply (x : U) :
    hU.isoSpec.hom x = Spec.map (X.presheaf.germ U x x.2) (closedPoint _) := by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_apply, Scheme.Opens.toSpecΓ,
    TopCat.Presheaf.Γgerm]
  rw [← Scheme.Hom.comp_apply]; rw [← Spec.map_comp]; rw [(Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial)]; rw [X.presheaf.germ_res_assoc]; rw [Spec.map_comp]; rw [Scheme.Hom.comp_apply]
  congr 1
  exact IsLocalRing.comap_closedPoint (U.stalkIso x).inv.hom

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isoSpec_hom_appTop` / 引理 `isoSpec_hom_appTop`

English:
lemma isoSpec_hom_appTop
  proof: by
  simp [isoSpec, Scheme.isoSpec]

中文:
引理 isoSpec_hom_appTop
  证明: by
  simp [isoSpec, Scheme.isoSpec]

Depends on / 依赖: Scheme, Scheme.isoSpec, isoSpec
-/
lemma isoSpec_hom_appTop :
    hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [isoSpec, Scheme.isoSpec]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isoSpec_inv_appTop` / 引理 `isoSpec_inv_appTop`

English:
lemma isoSpec_inv_appTop
  proof: by
  rw [← cancel_mono hU.isoSpec.hom.appTop]; rw [← Scheme.Hom.comp_appTop]; rw [isoSpec_hom_appTop]
  simp
  rfl

中文:
引理 isoSpec_inv_appTop
  证明: by
  rw [← cancel_mono hU.isoSpec.hom.appTop]; rw [← Scheme.Hom.comp_appTop]; rw [isoSpec_hom_appTop]
  simp
  rfl

Depends on / 依赖: Scheme, Scheme.Hom.comp_appTop, appTop, cancel_mono, comp_appTop, hU.isoSpec.hom.appTop, isoSpec, isoSpec_hom_appTop
-/
lemma isoSpec_inv_appTop :
    hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [← cancel_mono hU.isoSpec.hom.appTop]; rw [← Scheme.Hom.comp_appTop]; rw [isoSpec_hom_appTop]
  simp
  rfl

/--
Definition of `fromSpec` / `fromSpec` 的定义

English:
definition fromSpec
  signature: :
  body: haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι

中文:
定义 fromSpec
  签名: :
  定义体: haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι

Depends on / 依赖: IsAffine, hU.isoSpec.inv, isoSpec
-/
def fromSpec :
    Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι

/--
Instance `isOpenImmersion_fromSpec` / 实例 `isOpenImmersion_fromSpec`

English:
instance isOpenImmersion_fromSpec
  signature: :
  body: by
  delta fromSpec
  infer_instance

@[reassoc (attr := simp)]

中文:
实例 isOpenImmersion_fromSpec
  签名: :
  定义体: by
  delta fromSpec
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: fromSpec, infer_instance
-/
instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `isoSpec_inv_ι` / 引理 `isoSpec_inv_ι`

English:
lemma isoSpec_inv_ι
  statement: hU.isoSpec.inv ≫ U.ι = hU.fromSpec
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 isoSpec_inv_ι
  结论: hU.isoSpec.inv ≫ U.ι = hU.fromSpec
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma isoSpec_inv_ι : hU.isoSpec.inv ≫ U.ι = hU.fromSpec := rfl

@[reassoc (attr := simp)]
/--
lemma `isoSpec_hom_fromSpec` / 引理 `isoSpec_hom_fromSpec`

English:
lemma isoSpec_hom_fromSpec
  statement: hU.isoSpec.hom ≫ hU.fromSpec = U.ι
  proof: by
  simp [← cancel_epi hU.isoSpec.inv]

@[reassoc (attr := simp)]

中文:
引理 isoSpec_hom_fromSpec
  结论: hU.isoSpec.hom ≫ hU.fromSpec = U.ι
  证明: by
  simp [← cancel_epi hU.isoSpec.inv]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, hU.isoSpec.inv, isoSpec
-/
lemma isoSpec_hom_fromSpec : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  simp [← cancel_epi hU.isoSpec.inv]

@[reassoc (attr := simp)]
/--
lemma `toSpecΓ_fromSpec` / 引理 `toSpecΓ_fromSpec`

English:
lemma toSpecΓ_fromSpec
  statement: U.toSpecΓ ≫ hU.fromSpec = U.ι
  proof: toSpecΓ_isoSpec_inv_assoc _ _

中文:
引理 toSpecΓ_fromSpec
  结论: U.toSpecΓ ≫ hU.fromSpec = U.ι
  证明: toSpecΓ_isoSpec_inv_assoc _ _
-/
lemma toSpecΓ_fromSpec : U.toSpecΓ ≫ hU.fromSpec = U.ι := toSpecΓ_isoSpec_inv_assoc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `range_fromSpec` / 定理 `range_fromSpec`

English:
theorem range_fromSpec
  proof: by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp]; rw [← TopCat.epi_iff_surjective]
  infer_instance

@[reassoc (attr := simp)]

中文:
定理 range_fromSpec
  证明: by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp]; rw [← TopCat.epi_iff_surjective]
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpec, IsAffineOpen.isoSpec_inv, Set.image_univ, Set.range_comp, Set.range_eq_univ.mpr, Subtype, Subtype.range_coe, TopCat, TopCat.coe_comp, TopCat.epi_iff_surjective, coe_comp, epi_iff_surjective, fromSpec, image_univ, infer_instance, isoSpec_inv, range_coe, range_comp, range_eq_univ
-/
theorem range_fromSpec :
    Set.range hU.fromSpec = U := by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp]; rw [← TopCat.epi_iff_surjective]
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `fromSpec_toSpecΓ` / 引理 `fromSpec_toSpecΓ`

English:
lemma fromSpec_toSpecΓ
  given: {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
  proof: by
  rw [fromSpec]; rw [Category.assoc]; rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]; rw [isoSpec_inv_toSpecΓ_assoc]

@[simp]

中文:
引理 fromSpec_toSpecΓ
  条件: {X : 概形} {U : X.Opens} (hU : 是仿射开集 U)
  证明: by
  rw [fromSpec]; rw [Category.assoc]; rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]; rw [isoSpec_inv_toSpecΓ_assoc]

@[simp]

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.Opens.toSpec, fromSpec
-/
lemma fromSpec_toSpecΓ {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ X.toSpecΓ = Spec.map (X.presheaf.map (homOfLE le_top).op) := by
  rw [fromSpec]; rw [Category.assoc]; rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]; rw [isoSpec_inv_toSpecΓ_assoc]

@[simp]
/--
theorem `opensRange_fromSpec` / 定理 `opensRange_fromSpec`

English:
theorem opensRange_fromSpec
  statement: hU.fromSpec.opensRange = U
  proof: Opens.ext (range_fromSpec hU)

中文:
定理 opensRange_fromSpec
  结论: hU.fromSpec.opensRange = U
  证明: Opens.ext (range_fromSpec hU)

Depends on / 依赖: Opens.ext, range_fromSpec
-/
theorem opensRange_fromSpec : hU.fromSpec.opensRange = U := Opens.ext (range_fromSpec hU)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `map_fromSpec` / 定理 `map_fromSpec`

English:
theorem map_fromSpec
  given: {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V)
  proof: by
  have : IsAffine U := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec]; rw [← X.homOfLE_ι (V := U) f.unop.le]; rw [isoSpec_inv]; rw [Category.assoc]; rw [← Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [Scheme.homOfLE_appTop]; rw [← Functor.map_comp]
  rw [from

中文:
定理 map_fromSpec
  条件: {V : X.Opens} (hV : 是仿射开集 V) (f : op U ⟶ op V)
  证明: by
  have : IsAffine U := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec]; rw [← X.homOfLE_ι (V := U) f.unop.le]; rw [isoSpec_inv]; rw [Category.assoc]; rw [← Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [Scheme.homOfLE_appTop]; rw [← Functor.map_comp]
  rw [from

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, IsAffine, Scheme, Scheme.homOfLE_appTop, Scheme.isoSpec_inv_naturality_assoc, Spec.map_comp_assoc, X.homOfLE_, conv_rhs, f.unop.le, fromSpec, homOfLE_appTop, isoSpec_inv, isoSpec_inv_naturality_assoc, map_comp, map_comp_assoc
-/
theorem map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) :
    Spec.map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine U := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec]; rw [← X.homOfLE_ι (V := U) f.unop.le]; rw [isoSpec_inv]; rw [Category.assoc]; rw [← Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [Scheme.homOfLE_appTop]; rw [← Functor.map_comp]
  rw [fromSpec]; rw [isoSpec_inv]; rw [Category.assoc]; rw [← Spec.map_comp_assoc]; rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `SpecMap_appLE_fromSpec` / 引理 `SpecMap_appLE_fromSpec`

English:
lemma SpecMap_appLE_fromSpec
  statement: (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
  proof: by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc]; rw [← morphismRestrict_ι]; rw [← Category.assoc _ (f ∣_ U) U.ι]; rw [← @Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [← Spec

中文:
引理 SpecMap_appLE_fromSpec
  结论: (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
  证明: by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc]; rw [← morphismRestrict_ι]; rw [← Category.assoc _ (f ∣_ U) U.ι]; rw [← @Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [← Spec

Depends on / 依赖: Category, Category.assoc, IsAffine, IsAffineOpen, IsAffineOpen.fromSpec, Scheme, Scheme.Hom.appL, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_appTop, Scheme.homOfLE_, Scheme.homOfLE_appTop, Scheme.isoSpec_inv_naturality_assoc, Spec.map_comp_assoc, appLE_map, app_eq_appLE, comp_appTop, fromSpec, homOfLE_appTop, isoSpec_inv
-/
lemma SpecMap_appLE_fromSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V <= f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc]; rw [← morphismRestrict_ι]; rw [← Category.assoc _ (f ∣_ U) U.ι]; rw [← @Scheme.isoSpec_inv_naturality_assoc]; rw [← Spec.map_comp_assoc]; rw [← Spec.map_comp_assoc]; rw [Scheme.Hom.comp_appTop]; rw [morphismRestrict_appTop]; rw [Scheme.homOfLE_appTop]; rw [Scheme.Hom.app_eq_appLE]; rw [Scheme.Hom.appLE_map]; rw [Scheme.Hom.appLE_map]; rw [Scheme.Hom.appLE_map]; rw [Scheme.Hom.map_appLE]

/--
lemma `fromSpec_top` / 引理 `fromSpec_top`

English:
lemma fromSpec_top
  given: [IsAffine X]
  statement: (isAffineOpen_top X).fromSpec = X.isoSpec.inv
  proof: by
  rw [fromSpec]; rw [Iso.inv_comp_eq]
  simp [isoSpec_hom]

中文:
引理 fromSpec_top
  条件: [是仿射 X]
  结论: (isAffineOpen_top X).fromSpec = X.isoSpec.inv
  证明: by
  rw [fromSpec]; rw [Iso.inv_comp_eq]
  simp [isoSpec_hom]

Depends on / 依赖: Iso.inv_comp_eq, fromSpec, inv_comp_eq, isoSpec_hom
-/
lemma fromSpec_top [IsAffine X] : (isAffineOpen_top X).fromSpec = X.isoSpec.inv := by
  rw [fromSpec]; rw [Iso.inv_comp_eq]
  simp [isoSpec_hom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSpec_app_of_le` / 引理 `fromSpec_app_of_le`

English:
lemma fromSpec_app_of_le
  given: (V : X.Opens) (h : U <= V)
  proof: by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ => h x.2
  rw [IsAffineOpen.fromSpec]; rw [Scheme.Hom.comp_app]; rw [Scheme.Opens.ι_app]; rw [Scheme.Hom.app_eq _ this]; rw [← Scheme.Hom.appTop]; rw [IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.to

中文:
引理 fromSpec_app_of_le
  条件: (V : X.Opens) (h : U <= V)
  证明: by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ => h x.2
  rw [IsAffineOpen.fromSpec]; rw [Scheme.Hom.comp_app]; rw [Scheme.Opens.ι_app]; rw [Scheme.Hom.app_eq _ this]; rw [← Scheme.Hom.appTop]; rw [IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.to

Depends on / 依赖: Category, Category.assoc, IsAffineOpen, IsAffineOpen.fromSpec, IsAffineOpen.isoSpec_inv_appTop, Scheme, Scheme.Hom.appTop, Scheme.Hom.app_eq, Scheme.Hom.comp_app, Scheme.Opens, Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom, X.presheaf.map_comp_assoc, appTop, app_eq, comp_app, eq_top_iff, eq_top_iff.mpr, fromSpec, isoSpec_inv_appTop
-/
lemma fromSpec_app_of_le (V : X.Opens) (h : U <= V) :
    hU.fromSpec.app V = X.presheaf.map (homOfLE h).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _).presheaf.map (homOfLE le_top).op := by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ => h x.2
  rw [IsAffineOpen.fromSpec]; rw [Scheme.Hom.comp_app]; rw [Scheme.Opens.ι_app]; rw [Scheme.Hom.app_eq _ this]; rw [← Scheme.Hom.appTop]; rw [IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom,
    Category.assoc, ← X.presheaf.map_comp_assoc]
  rfl

include hU in
/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  proof: by
  convert! @IsCompact.image _ _ _ _ Set.univ hU.fromSpec PrimeSpectrum.compactSpace.1 (by fun_prop)
  convert! hU.range_fromSpec.symm
  exact Set.image_univ

中文:
定理 isCompact
  证明: by
  convert! @IsCompact.image _ _ _ _ Set.univ hU.fromSpec PrimeSpectrum.compactSpace.1 (by fun_prop)
  convert! hU.range_fromSpec.symm
  exact Set.image_univ
-/
protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert! @IsCompact.image _ _ _ _ Set.univ hU.fromSpec PrimeSpectrum.compactSpace.1 (by fun_prop)
  convert! hU.range_fromSpec.symm
  exact Set.image_univ

/--
theorem `_root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion` / 定理 `_root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`

English:
theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
  proof: IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) (f ''ᵁ U).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])).inv

include hU in

中文:
定理 _root_.AlgebraicGeometry.概形.态射.isAffineOpen_iff_of_isOpenImmersion
  证明: IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) (f ''ᵁ U).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])).inv

include hU in

Depends on / 依赖: IsAffine, IsAffine.iff_of_isIso, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Scheme, Scheme.Hom.comp_base, Set.range_comp, comp_base, iff_of_isIso, isoOfRangeEq, range_comp
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : X ⟶ Y) [H : IsOpenImmersion f] {U : X.Opens} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U :=
  IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) (f ''ᵁ U).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])).inv

include hU in
/--
theorem `image_of_isOpenImmersion` / 定理 `image_of_isOpenImmersion`

English:
theorem image_of_isOpenImmersion
  given: (f : X ⟶ Y) [H : IsOpenImmersion f]
  proof: by
  rwa [f.isAffineOpen_iff_of_isOpenImmersion]

中文:
定理 image_of_isOpenImmersion
  条件: (f : X ⟶ Y) [H : 是开浸入 f]
  证明: by
  rwa [f.isAffineOpen_iff_of_isOpenImmersion]

Depends on / 依赖: f.isAffineOpen_iff_of_isOpenImmersion, isAffineOpen_iff_of_isOpenImmersion
-/
theorem image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f ''ᵁ U) := by
  rwa [f.isAffineOpen_iff_of_isOpenImmersion]

/--
theorem `preimage_of_isIso` / 定理 `preimage_of_isIso`

English:
theorem preimage_of_isIso
  given: {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f]
  proof: haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)

中文:
定理 preimage_of_isIso
  条件: {U : Y.Opens} (hU : 是仿射开集 U) (f : X ⟶ Y) [是同构 f]
  证明: haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)

Depends on / 依赖: IsAffine, of_isIso
-/
theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)

/--
theorem `preimage_of_isOpenImmersion` / 定理 `preimage_of_isOpenImmersion`

English:
theorem preimage_of_isOpenImmersion
  statement: {U : Y.Opens} (hU : IsAffineOpen U)
  proof: by
  rwa [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hU']

中文:
定理 preimage_of_isOpenImmersion
  结论: {U : Y.Opens} (hU : 是仿射开集 U)
  证明: by
  rwa [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hU']

Depends on / 依赖: f.image_preimage_eq_opensRange_inf, f.isAffineOpen_iff_of_isOpenImmersion, image_preimage_eq_opensRange_inf, inf_eq_right, inf_eq_right.mpr, isAffineOpen_iff_of_isOpenImmersion
-/
theorem preimage_of_isOpenImmersion {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsOpenImmersion f] (hU' : U <= f.opensRange) :
    IsAffineOpen (f ⁻¹ᵁ U) := by
  rwa [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hU']

/-- The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image. -/
@[simps]
/--
Definition of `_root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv` / `_root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv` 的定义

English:
definition _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv
  signature: (f : X ⟶ Y) [H : IsOpenImmersion f]
  body: ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, U.1.2.preimage_of_isOpenImmersion _ U.2⟩
  left_inv _ := Subtype.ext (f.preimage_image_eq _)
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))
  map_rel_iff' := 

中文:
定义 _root_.AlgebraicGeometry.是开浸入.affineOpensEquiv
  签名: (f : X ⟶ Y) [H : 是开浸入 f]
  定义体: ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, U.1.2.preimage_of_isOpenImmersion _ U.2⟩
  left_inv _ := Subtype.ext (f.preimage_image_eq _)
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))
  map_rel_iff' := 

Depends on / 依赖: Set.image_subset_range, image_of_isOpenImmersion, image_subset_range
-/
def _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv (f : X ⟶ Y) [H : IsOpenImmersion f] :
    X.affineOpens ≃o { U : Y.affineOpens // U <= f.opensRange } where
  toFun U := ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, U.1.2.preimage_of_isOpenImmersion _ U.2⟩
  left_inv _ := Subtype.ext (f.preimage_image_eq _)
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))
  map_rel_iff' := f.image_le_image_iff _ _

/-- The affine open sets of an open subscheme
corresponds to the affine open sets containing in the subset. -/
@[simps! apply_coe_coe]
/--
Definition of `_root_.AlgebraicGeometry.affineOpensRestrict` / `_root_.AlgebraicGeometry.affineOpensRestrict` 的定义

English:
definition _root_.AlgebraicGeometry.affineOpensRestrict
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: (IsOpenImmersion.affineOpensEquiv U.ι).toEquiv.trans (Equiv.subtypeEquivProp (by simp))

@[simp]

中文:
定义 _root_.AlgebraicGeometry.affineOpensRestrict
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: (IsOpenImmersion.affineOpensEquiv U.ι).toEquiv.trans (Equiv.subtypeEquivProp (by simp))

@[simp]

Depends on / 依赖: Equiv.subtypeEquivProp, IsOpenImmersion, IsOpenImmersion.affineOpensEquiv, affineOpensEquiv, subtypeEquivProp, toEquiv, toEquiv.trans
-/
def _root_.AlgebraicGeometry.affineOpensRestrict {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme.affineOpens ≃ { V : X.affineOpens // V <= U } :=
  (IsOpenImmersion.affineOpensEquiv U.ι).toEquiv.trans (Equiv.subtypeEquivProp (by simp))

@[simp]
/--
lemma `_root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe` / 引理 `_root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe`

English:
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
  proof: rfl

中文:
引理 _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
  证明: rfl
-/
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
    {X : Scheme.{u}} (U : X.Opens) (V) :
    ((affineOpensRestrict U).symm V).1 = U.ι ⁻¹ᵁ V := rfl

instance (priority := 100) _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine
    (X : Scheme) [IsAffine X] :
    CompactSpace X :=
  ⟨(isAffineOpen_top X).isCompact⟩

@[simp]
/--
theorem `fromSpec_preimage_self` / 定理 `fromSpec_preimage_self`

English:
theorem fromSpec_preimage_self
  proof: by
  simp_rw [← hU.opensRange_fromSpec, Scheme.Hom.preimage_opensRange]

中文:
定理 fromSpec_preimage_self
  证明: by
  simp_rw [← hU.opensRange_fromSpec, Scheme.Hom.preimage_opensRange]

Depends on / 依赖: Scheme, Scheme.Hom.preimage_opensRange, hU.opensRange_fromSpec, opensRange_fromSpec, preimage_opensRange, simp_rw
-/
theorem fromSpec_preimage_self :
    hU.fromSpec ⁻¹ᵁ U = ⊤ := by
  simp_rw [← hU.opensRange_fromSpec, Scheme.Hom.preimage_opensRange]

/--
theorem `ΓSpecIso_hom_fromSpec_app` / 定理 `ΓSpecIso_hom_fromSpec_app`

English:
theorem ΓSpecIso_hom_fromSpec_app
  proof: by
  change _ = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
  simp [IsAffineOpen.fromSpec_app_of_le]

@[elementwise]

中文:
定理 ΓSpecIso_hom_fromSpec_app
  证明: by
  change _ = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
  simp [IsAffineOpen.fromSpec_app_of_le]

@[elementwise]

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpec_app_of_le, fromSpec_app_of_le, homOfLE, le_top, presheaf, presheaf.map
-/
theorem ΓSpecIso_hom_fromSpec_app :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  change _ = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
  simp [IsAffineOpen.fromSpec_app_of_le]

@[elementwise]
/--
theorem `fromSpec_app_self` / 定理 `fromSpec_app_self`

English:
theorem fromSpec_app_self
  proof: by
  rw [← hU.ΓSpecIso_hom_fromSpec_app]; rw [Iso.inv_hom_id_assoc]

中文:
定理 fromSpec_app_self
  证明: by
  rw [← hU.ΓSpecIso_hom_fromSpec_app]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc
-/
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.ΓSpecIso_hom_fromSpec_app]; rw [Iso.inv_hom_id_assoc]

/--
theorem `fromSpec_preimage_basicOpen'` / 定理 `fromSpec_preimage_basicOpen'`

English:
theorem fromSpec_preimage_basicOpen'
  proof: by
  rw [Scheme.preimage_basicOpen]; rw [hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op

中文:
定理 fromSpec_preimage_basicOpen'
  证明: by
  rw [Scheme.preimage_basicOpen]; rw [hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op

Depends on / 依赖: IsSchemeTheoreticallyDominant, Scheme, Scheme.basicOpen_res_eq, Scheme.preimage_basicOpen, basicOpen_res_eq, eqToHom, fromSpec_app_self, fromSpec_preimage_self, hU.fromSpec_app_self, hU.fromSpec_preimage_self, preimage_basicOpen
-/
theorem fromSpec_preimage_basicOpen' :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f) := by
  rw [Scheme.preimage_basicOpen]; rw [hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op

/--
theorem `fromSpec_preimage_basicOpen` / 定理 `fromSpec_preimage_basicOpen`

English:
theorem fromSpec_preimage_basicOpen
  proof: by
  rw [fromSpec_preimage_basicOpen']; rw [← basicOpen_eq_of_affine]

中文:
定理 fromSpec_preimage_basicOpen
  证明: by
  rw [fromSpec_preimage_basicOpen']; rw [← basicOpen_eq_of_affine]

Depends on / 依赖: IsSchemeTheoreticallyDominant, QuasiCompact, basicOpen_eq_of_affine, fromSpec_preimage_basicOpen
-/
theorem fromSpec_preimage_basicOpen :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f := by
  rw [fromSpec_preimage_basicOpen']; rw [← basicOpen_eq_of_affine]

/--
theorem `fromSpec_image_basicOpen` / 定理 `fromSpec_image_basicOpen`

English:
theorem fromSpec_image_basicOpen
  proof: by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec '' hU.fromSpec ⁻¹' (X.basicOpen f : Set X) = _
  rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]; rw [hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

@[simp]

中文:
定理 fromSpec_image_basicOpen
  证明: by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec '' hU.fromSpec ⁻¹' (X.basicOpen f : Set X) = _
  rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]; rw [hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

@[simp]

Depends on / 依赖: IdealSheafData, Scheme, Scheme.Hom.ker_comp, Scheme.IdealSheafData.map_bot, Scheme.basicOpen_le, Set.image_preimage_eq_inter_range, Set.inter_eq_left, X.basicOpen, basicOpen, basicOpen_le, f.ker_eq_bot, fromSpec, fromSpec_preimage_basicOpen, g.ker_eq_bot, hU.fromSpec, hU.fromSpec_preimage_basicOpen, hU.range_fromSpec, image_preimage_eq_inter_range, inter_eq_left, isSchemeTheoreticallyDominant_iff
-/
theorem fromSpec_image_basicOpen :
    hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec '' hU.fromSpec ⁻¹' (X.basicOpen f : Set X) = _
  rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]; rw [hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

@[simp]
/--
theorem `basicOpen_fromSpec_app` / 定理 `basicOpen_fromSpec_app`

English:
theorem basicOpen_fromSpec_app
  proof: by
  rw [← hU.fromSpec_preimage_basicOpen]; rw [Scheme.preimage_basicOpen]

中文:
定理 basicOpen_fromSpec_app
  证明: by
  rw [← hU.fromSpec_preimage_basicOpen]; rw [Scheme.preimage_basicOpen]

Depends on / 依赖: Scheme, Scheme.preimage_basicOpen, fromSpec_preimage_basicOpen, hU.fromSpec_preimage_basicOpen, preimage_basicOpen
-/
theorem basicOpen_fromSpec_app :
    (Spec Γ(X, U)).basicOpen (hU.fromSpec.app U f) = PrimeSpectrum.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen]; rw [Scheme.preimage_basicOpen]

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
theorem `basicOpen` / 定理 `basicOpen`

English:
theorem basicOpen
  proof: by
  rw [← hU.fromSpec_image_basicOpen]; rw [Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert!
    isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f)

中文:
定理 basicOpen
  证明: by
  rw [← hU.fromSpec_image_basicOpen]; rw [Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert!
    isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f)

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Localization, Localization.Away, Opens.ext, PrimeSpectrum, PrimeSpectrum.localization_away_comap_range, Scheme, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion, Spec.map, algebraMap, convert, fromSpec_image_basicOpen, hU.fromSpec_image_basicOpen, isAffineOpen_iff_of_isOpenImmersion, isAffineOpen_opensRange, localization_away_comap_range
-/
theorem basicOpen :
    IsAffineOpen (X.basicOpen f) := by
  rw [← hU.fromSpec_image_basicOpen]; rw [Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert!
    isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm

/--
lemma `Spec_basicOpen` / 引理 `Spec_basicOpen`

English:
lemma Spec_basicOpen
  given: {R : CommRingCat} (f : R)
  proof: basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec <| .of R)).basicOpen _

中文:
引理 Spec_basicOpen
  条件: {R : 交换环范畴} (f : R)
  证明: basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec <| .of R)).basicOpen _

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen, basicOpen
-/
lemma Spec_basicOpen {R : CommRingCat} (f : R) :
    IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen f) :=
  basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec <| .of R)).basicOpen _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffine
  signature: X] (r
  body: (isAffineOpen_top X).basicOpen _

include hU in

中文:
实例 [是仿射
  签名: X] (r
  定义体: (isAffineOpen_top X).basicOpen _

include hU in

Depends on / 依赖: basicOpen, isAffineOpen_top
-/
instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r) :=
  (isAffineOpen_top X).basicOpen _

include hU in
/--
theorem `ι_basicOpen_preimage` / 定理 `ι_basicOpen_preimage`

English:
theorem ι_basicOpen_preimage
  given: (r : Γ(X, ⊤))
  proof: by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; rw [Scheme.Opens.opensRange_ι]; rw [inf_comm]; rw [← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

中文:
定理 ι_basicOpen_preimage
  条件: (r : Γ(X, ⊤))
  证明: by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; rw [Scheme.Opens.opensRange_ι]; rw [inf_comm]; rw [← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

Depends on / 依赖: Scheme, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_, Scheme.basicOpen_res, X.basicOpen, basicOpen, basicOpen_res, hU.basicOpen, homOfLE, image_preimage_eq_opensRange_inf, inf_comm, isAffineOpen_iff_of_isOpenImmersion, isAffineOpen_iff_of_isOpenImmersion.mp, le_top
-/
theorem ι_basicOpen_preimage (r : Γ(X, ⊤)) :
    IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U) := by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; rw [Scheme.Opens.opensRange_ι]; rw [inf_comm]; rw [← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

set_option backward.isDefEq.respectTransparency false in
include hU in
/--
theorem `exists_basicOpen_le` / 定理 `exists_basicOpen_le`

English:
theorem exists_basicOpen_le
  given: {V : X.Opens} (x : V) (h : ↑x in U)
  proof: by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂ : _ <= U.ι ⁻¹ᵁ V⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) in _) (U.ι ⁻¹ᵁ V).isOpen
  replace h₁ : x.1 in X.basicOpen r := by simpa [U.mem_basicOpen_toScheme] using! h₁
  replace h₂ : X.basicOpen r

中文:
定理 存在_basicOpen_le
  条件: {V : X.Opens} (x : V) (h : ↑x in U)
  证明: by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂ : _ <= U.ι ⁻¹ᵁ V⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) in _) (U.ι ⁻¹ᵁ V).isOpen
  replace h₁ : x.1 in X.basicOpen r := by simpa [U.mem_basicOpen_toScheme] using! h₁
  replace h₂ : X.basicOpen r

Depends on / 依赖: IsAffine, Scheme, Scheme.Opens.toScheme_presheaf_obj, Scheme.image_basicOpen, U.mem_basicOpen_toScheme, U.topIso.hom.hom, X.basicOpen, basicOpen, exists_subset_of_mem_open, image_basicOpen, image_mono, image_preimage_le, isBasis_basicOpen, isOpen, mem_basicOpen_toScheme, replace, toScheme_presheaf_obj, topIso
-/
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x in U) :
    exists f : Γ(X, U), X.basicOpen f <= V ∧ ↑x in X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂ : _ <= U.ι ⁻¹ᵁ V⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) in _) (U.ι ⁻¹ᵁ V).isOpen
  replace h₁ : x.1 in X.basicOpen r := by simpa [U.mem_basicOpen_toScheme] using! h₁
  replace h₂ : X.basicOpen r <= V := by
    simpa [Scheme.image_basicOpen] using! (U.ι.image_mono h₂).trans (U.ι.image_preimage_le _)
  exact ⟨U.topIso.hom.hom r, by simp [Scheme.Opens.toScheme_presheaf_obj, h₁, h₂]⟩

set_option backward.isDefEq.respectTransparency.types false in
noncomputable
instance {R : CommRingCat} {U} : Algebra R Γ(Spec R, U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.obj _))

@[simp]
/--
lemma `algebraMap_Spec_obj` / 引理 `algebraMap_Spec_obj`

English:
lemma algebraMap_Spec_obj
  given: {R : CommRingCat} {U}
  statement: algebraMap R Γ(Spec R, U) =
  proof: rfl

中文:
引理 algebraMap_Spec_obj
  条件: {R : 交换环范畴} {U}
  结论: algebraMap R Γ(Spec R, U) =
  证明: rfl
-/
lemma algebraMap_Spec_obj {R : CommRingCat} {U} : algebraMap R Γ(Spec R, U) =
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
instance {R : CommRingCat} {f : R} :
    IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away f
    ((Spec.structureSheaf R).obj.obj (op <| PrimeSpectrum.basicOpen f)))

/--
Definition of `basicOpenSectionsToAffine` / `basicOpenSectionsToAffine` 的定义

English:
definition basicOpenSectionsToAffine
  signature: :
  body: hU.fromSpec.app (X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom (hU.fromSpec_preimage_basicOpen f).symm).op

中文:
定义 basicOpenSectionsToAffine
  签名: :
  定义体: hU.fromSpec.app (X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom (hU.fromSpec_preimage_basicOpen f).symm).op

Depends on / 依赖: X.basicOpen, basicOpen, eqToHom, fromSpec, fromSpec_preimage_basicOpen, hU.fromSpec.app, hU.fromSpec_preimage_basicOpen, presheaf, presheaf.map
-/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.app (X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom (hU.fromSpec_preimage_basicOpen f).symm).op

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `basicOpenSectionsToAffine_isIso` / 实例 `basicOpenSectionsToAffine_isIso`

English:
instance basicOpenSectionsToAffine_isIso
  signature: :
  body: (hU.fromSpec.isIso_app _ (hU.opensRange_fromSpec.symm ▸ X.basicOpen_le f)).comp_isIso'
    inferInstance

中文:
实例 basicOpenSectionsToAffine_isIso
  签名: :
  定义体: (hU.fromSpec.isIso_app _ (hU.opensRange_fromSpec.symm ▸ X.basicOpen_le f)).comp_isIso'
    inferInstance

Depends on / 依赖: X.basicOpen_le, basicOpen_le, comp_isIso, fromSpec, hU.fromSpec.isIso_app, hU.opensRange_fromSpec.symm, isIso_app, opensRange_fromSpec
-/
instance basicOpenSectionsToAffine_isIso :
    IsIso (basicOpenSectionsToAffine hU f) :=
  (hU.fromSpec.isIso_app _ (hU.opensRange_fromSpec.symm ▸ X.basicOpen_le f)).comp_isIso'
    inferInstance

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
theorem `isLocalization_basicOpen` / 定理 `isLocalization_basicOpen`

English:
theorem isLocalization_basicOpen
  proof: by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert! StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  apply Algebra.algebra_ext
  intro _
  congr 1
  dsimp [CommRingCat.of

中文:
定理 isLocalization_basicOpen
  证明: by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert! StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  apply Algebra.algebra_ext
  intro _
  congr 1
  dsimp [CommRingCat.of

Depends on / 依赖: Algebra, Algebra.algebra_ext, CommRingCat, CommRingCat.hom_comp, CommRingCat.ofHom, IsLocalization, IsLocalization.isLocalization_iff_of_ringEquiv, RingHom, RingHom.algebraMap_toAlgebra, StructureSheaf, StructureSheaf.IsLocalization.to_basicOpen, Submonoid, Submonoid.powers, algebraMap_toAlgebra, algebra_ext, basicOpenSectionsToAffine, commRingCatIsoToRingEquiv, convert, fromSpec, fromSpec_app_self
-/
theorem isLocalization_basicOpen :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert! StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  apply Algebra.algebra_ext
  intro _
  congr 1
  dsimp [CommRingCat.ofHom, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    basicOpenSectionsToAffine]
  rw [hU.fromSpec.naturality_assoc]; rw [hU.fromSpec_app_self]
  rfl

/--
Instance `_root_.AlgebraicGeometry.isLocalization_away_of_isAffine` / 实例 `_root_.AlgebraicGeometry.isLocalization_away_of_isAffine`

English:
instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
  body: isLocalization_basicOpen (isAffineOpen_top X) r

中文:
实例 _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
  定义体: isLocalization_basicOpen (isAffineOpen_top X) r

Depends on / 依赖: IsSeparated, isAffineOpen_top, isLocalization_basicOpen, isSeparated_of_mono
-/
instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r

/--
lemma `appLE_eq_away_map` / 引理 `appLE_eq_away_map`

English:
lemma appLE_eq_away_map
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
  proof: hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  let := hU.isLocalization_basicOpen 

中文:
引理 appLE_eq_away_map
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : 是仿射开集 U)
  证明: hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  let := hU.isLocalization_basicOpen 

Depends on / 依赖: hU.isLocalization_basicOpen, isLocalization_basicOpen
-/
lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  let := hU.isLocalization_basicOpen r
  let := hV.isLocalization_basicOpen (f.appLE U V e r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map]; rw [CommRingCat.hom_ofHom]; rw [IsLocalization.map_comp]; rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_comp]; rw [Scheme.Hom.appLE_map]; rw [Scheme.Hom.map_appLE]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `app_basicOpen_eq_away_map` / 引理 `app_basicOpen_eq_away_map`

English:
lemma app_basicOpen_eq_away_map
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
  proof: hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  have := 

中文:
引理 app_basicOpen_eq_away_map
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) {U : Y.Opens}
  证明: hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  have := 

Depends on / 依赖: IsSeparated, QuasiSeparated, hU.isLocalization_basicOpen, isLocalization_basicOpen
-/
lemma app_basicOpen_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  have := hU.isLocalization_basicOpen r
  have := h.isLocalization_basicOpen (f.app U r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map]; rw [CommRingCat.hom_comp]; rw [RingHom.comp_assoc]; rw [CommRingCat.hom_ofHom]; rw [IsLocalization.map_comp]; rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra]; rw [← RingHom.comp_assoc]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_comp]; rw [← X.presheaf.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `appBasicOpenIsoAwayMap` / `appBasicOpenIsoAwayMap` 的定义

English:
definition appBasicOpenIsoAwayMap
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
  body: hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
Arrow.isoMk (Iso.refl _) (X.presheaf.mapI

中文:
定义 appBasicOpenIsoAwayMap
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) {U : Y.Opens}
  定义体: hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
Arrow.isoMk (Iso.refl _) (X.presheaf.mapI

Depends on / 依赖: hU.isLocalization_basicOpen, isLocalization_basicOpen
-/
def appBasicOpenIsoAwayMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
Arrow.isoMk (Iso.refl _) (X.presheaf.mapIso (eqToIso (by simp)).op) by
    simp [hU.app_basicOpen_eq_away_map f h]
    rfl

include hU in
/--
theorem `isLocalization_of_eq_basicOpen` / 定理 `isLocalization_of_eq_basicOpen`

English:
theorem isLocalization_of_eq_basicOpen
  given: {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f)
  proof: by
  subst e; exact isLocalization_basicOpen hU f

中文:
定理 isLocalization_of_eq_basicOpen
  条件: {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f)
  证明: by
  subst e; exact isLocalization_basicOpen hU f

Depends on / 依赖: isLocalization_basicOpen
-/
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e; exact isLocalization_basicOpen hU f

/--
Instance `_root_.AlgebraicGeometry.Γ_restrict_isLocalization` / 实例 `_root_.AlgebraicGeometry.Γ_restrict_isLocalization`

English:
instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
  body: (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in

中文:
实例 _root_.AlgebraicGeometry.Γ_restrict_isLocalization
  定义体: (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in

Depends on / 依赖: Opens.isOpenEmbedding_obj_top, isAffineOpen_top, isLocalization_of_eq_basicOpen, isOpenEmbedding_obj_top
-/
instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X.basicOpen r, ⊤) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in
/--
theorem `basicOpen_basicOpen_is_basicOpen` / 定理 `basicOpen_basicOpen_is_basicOpen`

English:
theorem basicOpen_basicOpen_is_basicOpen
  given: (g : Γ(X, X.basicOpen f))
  proof: by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def]; rw [Scheme.basicOpen_mul]; rw [Scheme.basicOpen_mul]; rw [RingHom.algebraMap_toAlgebra]; rw [Scheme.basicOpen_res]
  refine (inf_eq_left.mpr 

中文:
定理 basicOpen_basicOpen_is_basicOpen
  条件: (g : Γ(X, X.basicOpen f))
  证明: by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def]; rw [Scheme.basicOpen_mul]; rw [Scheme.basicOpen_mul]; rw [RingHom.algebraMap_toAlgebra]; rw [Scheme.basicOpen_res]
  refine (inf_eq_left.mpr 

Depends on / 依赖: Algebra, Algebra.smul_def, IsLocalization, IsLocalization.surj, IsLocalization.toInvSubmonoid, RingHom, RingHom.algebraMap_toAlgebra, Scheme, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit, Scheme.basicOpen_res, Submonoid, Submonoid.leftInv_le_isUnit, Submonoid.powers, X.basicOpen, algebraMap_toAlgebra, basicOpen, basicOpen_mul, basicOpen_of_isUnit, basicOpen_res
-/
theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    exists f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def]; rw [Scheme.basicOpen_mul]; rw [Scheme.basicOpen_mul]; rw [RingHom.algebraMap_toAlgebra]; rw [Scheme.basicOpen_res]
  refine (inf_eq_left.mpr (inf_le_left.trans_eq (Scheme.basicOpen_of_isUnit _ ?_).symm)).symm
  exact
    Submonoid.leftInv_le_isUnit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (Γ(X, X.basicOpen f))
        _).prop

include hU in
/--
theorem `_root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter` / 定理 `_root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter`

English:
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
  proof: by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _))

中文:
定理 _root_.AlgebraicGeometry.存在_basicOpen_le_affine_inter
  证明: by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _))

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_res, X.presheaf.map, basicOpen_basicOpen_is_basicOpen, basicOpen_res, exists_basicOpen_le, hU.exists_basicOpen_le, hV.exists_basicOpen_le, homOfLE, inf_eq_right, inf_eq_right.mpr, presheaf, replace
-/
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x in U ⊓ V) :
    exists (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x in X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩

/--
Definition of `primeIdealOf` / `primeIdealOf` 的定义

English:
definition primeIdealOf
  signature: (x : U)
  body: hU.isoSpec.hom x

中文:
定义 primeIdealOf
  签名: (x : U)
  定义体: hU.isoSpec.hom x

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, hU.isoSpec.hom, isoSpec, pullback_fst
-/
noncomputable def primeIdealOf (x : U) :
    PrimeSpectrum Γ(X, U) :=
  hU.isoSpec.hom x

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fromSpec_primeIdealOf` / 定理 `fromSpec_primeIdealOf`

English:
theorem fromSpec_primeIdealOf
  given: (x : U)
  proof: by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
  rfl

中文:
定理 fromSpec_primeIdealOf
  条件: (x : U)
  证明: by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
  rfl

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpec, IsAffineOpen.primeIdealOf, Iso.hom_inv_id_assoc, MorphismProperty, MorphismProperty.pullback_snd, Scheme, Scheme.Hom.comp_apply, Subtype, Subtype.coe_mk, coe_mk, comp_apply, fromSpec, hom_inv_id_assoc, primeIdealOf, pullback_snd
-/
theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
  rfl

open IsLocalRing in
/--
theorem `primeIdealOf_eq_map_closedPoint` / 定理 `primeIdealOf_eq_map_closedPoint`

English:
theorem primeIdealOf_eq_map_closedPoint
  given: (x : U)
  proof: hU.isoSpec_hom_apply _

中文:
定理 primeIdealOf_eq_map_closedPoint
  条件: (x : U)
  证明: hU.isoSpec_hom_apply _

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, hU.isoSpec_hom_apply, isoSpec_hom_apply, restrict
-/
theorem primeIdealOf_eq_map_closedPoint (x : U) :
    hU.primeIdealOf x = Spec.map (X.presheaf.germ _ x x.2) (closedPoint _) :=
  hU.isoSpec_hom_apply _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `comap_primeIdealOf_appLE` / 引理 `comap_primeIdealOf_appLE`

English:
lemma comap_primeIdealOf_appLE
  statement: {f : X ⟶ Y} {x : X} (U : Y.Opens)
  proof: by
  change Spec.map (f.appLE U V hVU) (hV.primeIdealOf ⟨x, hx⟩) = (hU.primeIdealOf ⟨f x, hVU hx⟩)
  simp only [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  apply Subtype.ext
  si

中文:
引理 comap_primeIdealOf_appLE
  结论: {f : X ⟶ Y} {x : X} (U : Y.Opens)
  证明: by
  change Spec.map (f.appLE U V hVU) (hV.primeIdealOf ⟨x, hx⟩) = (hU.primeIdealOf ⟨f x, hVU hx⟩)
  simp only [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  apply Subtype.ext
  si

Depends on / 依赖: IsAffineOpen, IsAffineOpen.isoSpec_hom, IsAffineOpen.primeIdealOf, Scheme, Scheme.Hom.comp_apply, Scheme.Hom.resLE, Scheme.Opens.toSpec, Spec.map, Subtype, Subtype.ext, comp_apply, f.appLE, hU.primeIdealOf, hV.primeIdealOf, infer_instance, isoSpec_hom, primeIdealOf
-/
lemma comap_primeIdealOf_appLE {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U) (hx : x in V) :
    (hV.primeIdealOf ⟨x, hx⟩).comap (f.appLE U V hVU).hom = hU.primeIdealOf ⟨f x, hVU hx⟩ := by
  change Spec.map (f.appLE U V hVU) (hV.primeIdealOf ⟨x, hx⟩) = (hU.primeIdealOf ⟨f x, hVU hx⟩)
  simp only [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  apply Subtype.ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `primeIdealOf_isMaximal_of_isClosed` / 定理 `primeIdealOf_isMaximal_of_isClosed`

English:
theorem primeIdealOf_isMaximal_of_isClosed
  given: (x : U) (hx : IsClosed {(x : X)})
  proof: by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf]; rw [← Set.image_singleton]
  refine (Topology

中文:
定理 primeIdealOf_isMaximal_of_isClosed
  条件: (x : U) (hx : 是闭集 {(x : X)})
  证明: by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf]; rw [← Set.image_singleton]
  refine (Topology

Depends on / 依赖: Algebra, Algebra.TensorProduct.lmul, CommRingCat, CommRingCat.ofHom, IsClosed, IsClosedEmbedding, IsClosedImmersion, IsHomeomorph, IsHomeomorph.isClosedEmbedding, Limits, Limits.pullback.diagonal, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, Set.image_singleton, Set.preimage_image_eq, Spec.map, Subtype, Subtype.val_injective, TensorProduct, TopCat
-/
theorem primeIdealOf_isMaximal_of_isClosed (x : U) (hx : IsClosed {(x : X)}) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf]; rw [← Set.image_singleton]
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed <|
    IsHomeomorph.isClosedEmbedding ?_).mp hx₀
  apply (TopCat.isIso_iff_isHomeomorph _).mp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLocalization_stalk'` / 定理 `isLocalization_stalk'`

English:
theorem isLocalization_stalk'
  given: (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y in U)
  proof: by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mp

中文:
定理 isLocalization_stalk'
  条件: (y : 素谱 Γ(X, U)) (hy : hU.fromSpec y in U)
  证明: by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mp
-/
theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y in U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_stalk Γ(X, U) y
  delta IsLocalization.AtPrime StructureSheaf.stalkAlgebra
  congr!
  simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, IsAffineOpen.fromSpec_app_self]
  rfl

/--
theorem `isLocalization_stalk` / 定理 `isLocalization_stalk`

English:
theorem isLocalization_stalk
  given: (x : U)
  proof: by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

中文:
定理 isLocalization_stalk
  条件: (x : U)
  证明: by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, clear_value, fromSpec, fromSpec_primeIdealOf, hU.fromSpec, hU.fromSpec_primeIdealOf, hU.isLocalization_stalk, hU.primeIdealOf, isLocalization_stalk, of_isPullback, primeIdealOf, pullback_map_diagonal_isPullback
-/
theorem isLocalization_stalk (x : U) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

/--
lemma `stalkMap_injective` / 引理 `stalkMap_injective`

English:
lemma stalkMap_injective
  statement: (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
  proof: by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  apply (hU.isLocalization_stalk ⟨f x, hx⟩).injective_of_map_algebraMap_zero
  exact h

中文:
引理 stalkMap_injective
  结论: (f : X ⟶ Y) {U : Opens Y} (hU : 是仿射开集 U) (x : X)
  证明: by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  apply (hU.isLocalization_stalk ⟨f x, hx⟩).injective_of_map_algebraMap_zero
  exact h

Depends on / 依赖: Y.presheaf.algebra_section_stalk, algebra_section_stalk, hU.isLocalization_stalk, injective_of_map_algebraMap_zero, isLocalization_stalk, presheaf
-/
lemma stalkMap_injective (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
    (hx : f x in U)
    (h : forall g, f.stalkMap x (Y.presheaf.germ U (f x) hx g) = 0 ->
      Y.presheaf.germ U (f x) hx g = 0) :
    Function.Injective (f.stalkMap x) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  apply (hU.isLocalization_stalk ⟨f x, hx⟩).injective_of_map_algebraMap_zero
  exact h

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
lemma `mem_ideal_iff` / 引理 `mem_ideal_iff`

English:
lemma mem_ideal_iff
  given: {s : Γ(X, U)} {I : Ideal Γ(X, U)}
  proof: by
  refine ⟨fun hs x hxU => Ideal.mem_map_of_mem _ hs, fun H => ?_⟩
  let (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk'

中文:
引理 mem_ideal_iff
  条件: {s : Γ(X, U)} {I : 理想 Γ(X, U)}
  证明: by
  refine ⟨fun hs x hxU => Ideal.mem_map_of_mem _ hs, fun H => ?_⟩
  let (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk'

Depends on / 依赖: Algebra, Algebra.linearMap, AtPrime, Ideal.localized, Ideal.mem_map_of_mem, IsLocalization, IsLocalization.AtPrime, IsPrime, P.IsPrime, Presheaf, Submodule, Submodule.mem_of_localization_maximal, TopCat, TopCat.Presheaf.algebra_section_stalk, X.presheaf, X.presheaf.stalk, algebra_section_stalk, fromSpec, hP.isPrime, hU.fromSpec
-/
lemma mem_ideal_iff {s : Γ(X, U)} {I : Ideal Γ(X, U)} :
    s in I ↔ forall (x : X) (h : x in U), X.presheaf.germ U x h s in I.map (X.presheaf.germ U x h).hom := by
  refine ⟨fun hs x hxU => Ideal.mem_map_of_mem _ hs, fun H => ?_⟩
  let (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv _).2
  refine Submodule.mem_of_localization_maximal
      (fun P hP => X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (fun P hP => Algebra.linearMap _ _) _ _ ?_
  intro P hP
  rw [Ideal.localized₀_eq_restrictScalars_map]
  exact H _ _

include hU in
/--
lemma `ideal_le_iff` / 引理 `ideal_le_iff`

English:
lemma ideal_le_iff
  given: {I J : Ideal Γ(X, U)}
  proof: ⟨fun h _ _ => Ideal.map_mono h,
    fun H _ hs => hU.mem_ideal_iff.mpr fun x hx => H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in

中文:
引理 ideal_le_iff
  条件: {I J : 理想 Γ(X, U)}
  证明: ⟨fun h _ _ => Ideal.map_mono h,
    fun H _ hs => hU.mem_ideal_iff.mpr fun x hx => H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in

Depends on / 依赖: Ideal.map_mono, Ideal.mem_map_of_mem, hU.mem_ideal_iff.mpr, map_mono, mem_ideal_iff, mem_map_of_mem
-/
lemma ideal_le_iff {I J : Ideal Γ(X, U)} :
    I <= J ↔ forall (x : X) (h : x in U),
      I.map (X.presheaf.germ U x h).hom <= J.map (X.presheaf.germ U x h).hom :=
  ⟨fun h _ _ => Ideal.map_mono h,
    fun H _ hs => hU.mem_ideal_iff.mpr fun x hx => H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in
/--
lemma `ideal_ext_iff` / 引理 `ideal_ext_iff`

English:
lemma ideal_ext_iff
  given: {I J : Ideal Γ(X, U)}
  proof: by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

中文:
引理 ideal_ext_iff
  条件: {I J : 理想 Γ(X, U)}
  证明: by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

Depends on / 依赖: forall_and, hU.ideal_le_iff, ideal_le_iff, le_antisymm_iff, simp_rw
-/
lemma ideal_ext_iff {I J : Ideal Γ(X, U)} :
    I = J ↔ forall (x : X) (h : x in U),
      I.map (X.presheaf.germ U x h).hom = J.map (X.presheaf.germ U x h).hom := by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `arrowStalkMapIso` / `arrowStalkMapIso` 的定义

English:
definition arrowStalkMapIso
  signature: (f : X ⟶ Y) {x : X} (U : Y.Opens)
  body: by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · exact ((IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, hVU hx⟩

中文:
定义 arrowStalkMapIso
  签名: (f : X ⟶ Y) {x : X} (U : Y.Opens)
  定义体: by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · exact ((IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, hVU hx⟩

Depends on / 依赖: Arrow.isoMk, AtPrime, IsLocalization, IsLocalization.algEquiv, Localization, Localization.AtPrime, X.presheaf.algebra_section_stalk, Y.presheaf.algebra_section_stalk, Y.presheaf.stalk, algEquiv, algebra_section_stalk, asIdeal, asIdeal.primeCompl, hU.isLocalization_stalk, hU.primeIdealOf, hV.isLocalization_stalk, hV.primeIdealOf, isLocalization_stalk, presheaf, primeCompl
-/
def arrowStalkMapIso (f : X ⟶ Y) {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U)
      (hx : x in V) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (CommRingCat.ofHom <|
      Localization.localRingHom _ _ (f.appLE U V hVU).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · exact ((IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
      (Y.presheaf.stalk (f x))
      (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)).toCommRingCatIso:)
  · exact ((IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).toCommRingCatIso:)
  · rw [← Iso.comp_inv_eq]
    ext1
    apply IsLocalization.ringHom_ext
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
    ext a
    dsimp [← AlgEquiv.symm_toRingEquiv]
    simp only [IsLocalization.map_eq, RingHom.id_apply, Localization.localRingHom_to_map,
      RingHomCompTriple.comp_apply]
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
/--
Definition of `_root_.AlgebraicGeometry.Scheme.affineBasicOpen` / `_root_.AlgebraicGeometry.Scheme.affineBasicOpen` 的定义

English:
definition _root_.AlgebraicGeometry.Scheme.affineBasicOpen
  body: ⟨X.basicOpen f, U.prop.basicOpen f⟩

中文:
定义 _root_.AlgebraicGeometry.概形.affineBasicOpen
  定义体: ⟨X.basicOpen f, U.prop.basicOpen f⟩

Depends on / 依赖: U.prop.basicOpen, X.basicOpen, basicOpen
-/
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩

/--
lemma `_root_.AlgebraicGeometry.Scheme.affineBasicOpen_le` / 引理 `_root_.AlgebraicGeometry.Scheme.affineBasicOpen_le`

English:
lemma _root_.AlgebraicGeometry.Scheme.affineBasicOpen_le
  proof: X.basicOpen_le f

include hU in

中文:
引理 _root_.AlgebraicGeometry.概形.affineBasicOpen_le
  证明: X.basicOpen_le f

include hU in

Depends on / 依赖: X.basicOpen_le, basicOpen_le
-/
lemma _root_.AlgebraicGeometry.Scheme.affineBasicOpen_le
    (X : Scheme) {V : X.affineOpens} (f : Γ(X, V.1)) : X.affineBasicOpen f <= V :=
  X.basicOpen_le f

include hU in
/--
theorem `iSup_basicOpen_eq_self_iff` / 定理 `iSup_basicOpen_eq_self_iff`

English:
theorem iSup_basicOpen_eq_self_iff
  given: {s : Set Γ(X, U)}
  proof: by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans hU.fromSpec ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 = hU.fromSpec ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec at h
      rw [Set.image_preimage_eq_inter_range]; rw [Set.i

中文:
定理 iSup_basicOpen_eq_self_iff
  条件: {s : 集合 Γ(X, U)}
  证明: by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans hU.fromSpec ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 = hU.fromSpec ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec at h
      rw [Set.image_preimage_eq_inter_range]; rw [Set.i

Depends on / 依赖: Opens.c, Opens.carrier_eq_coe, PrimeSpectrum, PrimeSpectrum.basicOpen, Set.Subset.antisymm, Set.iUnion_subset_iff, Set.image, Set.image_preimage_eq_inter_range, Set.inter_eq_right, Set.inter_self, Set.univ, SetCoe, SetCoe.forall, Subset, X.basicOpen, antisymm, apply_fun, basicOpen, carrier_eq_coe, fromSpec
-/
theorem iSup_basicOpen_eq_self_iff {s : Set Γ(X, U)} :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤ := by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans hU.fromSpec ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 = hU.fromSpec ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec at h
      rw [Set.image_preimage_eq_inter_range]; rw [Set.image_preimage_eq_inter_range]; rw [hU.range_fromSpec]
        at h
      simp only [Set.inter_self, Opens.carrier_eq_coe, Set.inter_eq_right] at h
      ext1
      refine Set.Subset.antisymm ?_ h
      simp only [Set.iUnion_subset_iff, SetCoe.forall, Opens.coe_iSup]
      intro x _
      exact X.basicOpen_le x
    · simp only [Opens.iSup_def, Set.preimage_iUnion]
      congr! 1
      · refine congr_arg (Set.iUnion ·) ?_
        ext1 x
        exact congr_arg Opens.carrier (hU.fromSpec_preimage_basicOpen _)
      · exact congr_arg Opens.carrier hU.fromSpec_preimage_self
  · simp only [Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [← Set.compl_iInter]; rw [Set.compl_univ_iff]; rw [← PrimeSpectrum.zeroLocus_iUnion]; rw [←
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]; rw [PrimeSpectrum.zeroLocus_span]
    simp only [Set.iUnion_singleton_eq_range, Subtype.range_val_subtype, Set.ofPred_mem_eq]

include hU in
/--
theorem `self_le_iSup_basicOpen_iff` / 定理 `self_le_iSup_basicOpen_iff`

English:
theorem self_le_iSup_basicOpen_iff
  given: {s : Set Γ(X, U)}
  proof: by
  rw [← hU.iSup_basicOpen_eq_self_iff]; rw [@comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

中文:
定理 self_le_iSup_basicOpen_iff
  条件: {s : 集合 Γ(X, U)}
  证明: by
  rw [← hU.iSup_basicOpen_eq_self_iff]; rw [@comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

Depends on / 依赖: I.inclusion, I.subscheme, IdealSheafData, IsClosedImmersion, Scheme, Scheme.IdealSheafData.inclusion_subscheme, SetCoe, SetCoe.forall, X.basicOpen_le, basicOpen_le, hU.iSup_basicOpen_eq_self_iff, iSup_basicOpen_eq_self_iff, iSup_le_iff, inclusion, infer_instance, le_antisymm, le_of_eq, of_comp
-/
theorem self_le_iSup_basicOpen_iff {s : Set Γ(X, U)} :
    (U <= ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff]; rw [@comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

end IsAffineOpen

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine open cover given by a covering family of affine opens. -/
@[simps I₀ X f]
/--
Definition of `Scheme.AffineOpenCover.ofIsOpenCover` / `Scheme.AffineOpenCover.ofIsOpenCover` 的定义

English:
definition Scheme.AffineOpenCover.ofIsOpenCover
  signature: {X : Scheme.{u}} {ι : Type*} (U : ι -> X.Opens)
  body: ι
  X i := Γ(X, U i)
  f i := (hU' i).fromSpec
  idx x := (hU.exists_mem x).choose
  covers x :=
    ⟨(hU' _).isoSpec.hom ⟨_, (hU.exists_mem x).choose_spec⟩, by simp [← Scheme.Hom.comp_apply]⟩

中文:
定义 概形.AffineOpenCover.ofIsOpenCover
  签名: {X : 概形.{u}} {ι : 类型} (U : ι -> X.Opens)
  定义体: ι
  X i := Γ(X, U i)
  f i := (hU' i).fromSpec
  idx x := (hU.exists_mem x).choose
  covers x :=
    ⟨(hU' _).isoSpec.hom ⟨_, (hU.exists_mem x).choose_spec⟩, by simp [← Scheme.Hom.comp_apply]⟩
-/
def Scheme.AffineOpenCover.ofIsOpenCover {X : Scheme.{u}} {ι : Type*} (U : ι -> X.Opens)
    (hU : IsOpenCover U) (hU' : forall i, IsAffineOpen (U i)) :
    AffineOpenCover X where
  I₀ := ι
  X i := Γ(X, U i)
  f i := (hU' i).fromSpec
  idx x := (hU.exists_mem x).choose
  covers x :=
    ⟨(hU' _).isoSpec.hom ⟨_, (hU.exists_mem x).choose_spec⟩, by simp [← Scheme.Hom.comp_apply]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open _root_.PrimeSpectrum in
/--
Definition of `SpecMapRestrictBasicOpenIso` / `SpecMapRestrictBasicOpenIso` 的定义

English:
definition SpecMapRestrictBasicOpenIso
  signature: {R S : CommRingCat} (f : R ⟶ S) (r : R)
  body: by
  refine Arrow.isoMk ?_ ?_ ?_
  · exact (Spec _).isoOfEq (comap_basicOpen _ _) ≪≫ basicOpenIsoSpecAway (f.hom r)
  · exact basicOpenIsoSpecAway r
  · have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫
        CommRingCat.ofHom (Localization.awayMap f.hom r) =
        f ≫ CommRi

中文:
定义 SpecMapRestrictBasicOpenIso
  签名: {R S : 交换环范畴} (f : R ⟶ S) (r : R)
  定义体: by
  refine Arrow.isoMk ?_ ?_ ?_
  · exact (Spec _).isoOfEq (comap_basicOpen _ _) ≪≫ basicOpenIsoSpecAway (f.hom r)
  · exact basicOpenIsoSpecAway r
  · have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫
        CommRingCat.ofHom (Localization.awayMap f.hom r) =
        f ≫ CommRi

Depends on / 依赖: Arrow.isoMk, Arrow.mk_hom, Category, Category.a, CommRingCat, CommRingCat.ofHom, IsLocalization, IsLocalization.Away.map, Localization, Localization.Away, Localization.awayMap, Spec.map, algebraMap, awayMap, basicOpenIsoSpecAway, cancel_mono, comap_basicOpen, f.hom, isoOfEq, mk_hom
-/
noncomputable def SpecMapRestrictBasicOpenIso {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Arrow.mk (Spec.map f ∣_ (PrimeSpectrum.basicOpen r)) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom (Localization.awayMap f.hom r)) := by
  refine Arrow.isoMk ?_ ?_ ?_
  · exact (Spec _).isoOfEq (comap_basicOpen _ _) ≪≫ basicOpenIsoSpecAway (f.hom r)
  · exact basicOpenIsoSpecAway r
  · have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫
        CommRingCat.ofHom (Localization.awayMap f.hom r) =
        f ≫ CommRingCat.ofHom (algebraMap S (Localization.Away (f.hom r))) := by
      ext x
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R _)))]
    simp only [Arrow.mk_hom, Category.assoc, ← Spec.map_comp]
    simp [hcomp]

/--
lemma `stalkMap_injective_of_isAffine` / 引理 `stalkMap_injective_of_isAffine`

English:
lemma stalkMap_injective_of_isAffine
  statement: {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x : X)
  proof: (isAffineOpen_top Y).stalkMap_injective f x trivial h

中文:
引理 stalkMap_injective_of_isAffine
  结论: {X Y : 概形} (f : X ⟶ Y) [是仿射 Y] (x : X)
  证明: (isAffineOpen_top Y).stalkMap_injective f x trivial h

Depends on / 依赖: isAffineOpen_top, stalkMap_injective
-/
lemma stalkMap_injective_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x : X)
    (h : forall g, f.stalkMap x (Y.presheaf.Γgerm (f x) g) = 0 -> Y.presheaf.Γgerm (f x) g = 0) :
    Function.Injective (f.stalkMap x) :=
  (isAffineOpen_top Y).stalkMap_injective f x trivial h

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iSup_basicOpen_of_span_eq_top` / 引理 `iSup_basicOpen_of_span_eq_top`

English:
lemma iSup_basicOpen_of_span_eq_top
  statement: {X : Scheme} (U) (s : Set Γ(X, U))
  proof: by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ => X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.iSup_basicOpen_eq_self_iff (s := X.presheaf.map (ho

中文:
引理 iSup_basicOpen_of_span_eq_top
  结论: {X : 概形} (U) (s : 集合 Γ(X, U))
  证明: by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ => X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.iSup_basicOpen_eq_self_iff (s := X.presheaf.map (ho

Depends on / 依赖: Ideal.map_span, Ideal.map_top, Opens.carrier_eq_coe, Opens.iSup_mk, Set.biUnion_and, Set.iUnion_coe_set, Set.iUnion_exists, Set.iUnion_iUnion_eq, Set.mem_image, SetLike, SetLike.mem_of_subset, X.basicOpen_le, X.isBasis_affineOpens.exists_subset_of_mem_open, X.presheaf.map, basicOpen_le, biUnion_and, carrier_eq_coe, exists_subset_of_mem_open, hV.iSup_basicOpen_eq_self_iff, homOfLE
-/
lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) : (⨆ i in s, X.basicOpen i) = U := by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ => X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.iSup_basicOpen_eq_self_iff (s := X.presheaf.map (homOfLE hVU).op '' s)).mpr
      (by rw [← Ideal.map_span]; rw [hs]; rw [Ideal.map_top])]
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_coe_set, Set.mem_image,
      Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Scheme.basicOpen_res,
      Opens.coe_inf, Opens.coe_mk, Set.iUnion_subset_iff]
    exact fun i hi => (Set.inter_subset_right.trans
      (Set.subset_iUnion₂ (s := fun x _ => (X.basicOpen x : Set X)) i hi))

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_elim]
/--
theorem `of_affine_open_cover` / 定理 `of_affine_open_cover`

English:
theorem of_affine_open_cover
  statement: {X : Scheme} {P : X.affineOpens -> Prop}
  proof: by
  have : forall (x : V.1), exists f : Γ(X, V), ↑x in X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (iSup_U.ge (Set.mem_univ x))
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩


中文:
定理 of_affine_open_cover
  结论: {X : 概形} {P : X.affineOpens -> 命题}
  证明: by
  have : forall (x : V.1), exists f : Γ(X, V), ↑x in X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (iSup_U.ge (Set.mem_univ x))
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩


Depends on / 依赖: Ideal.span, Ideal.span_eq_top_iff_finite, Opens.mem_iSup.mp, Set.mem_univ, Set.range, V.prop, X.affineBasicOpen, X.basicOpen, affineBasicOpen, basicOpen, convert, exists_basicOpen_le_affine_inter, iSup_U, iSup_U.ge, mem_iSup, mem_univ, openCover, span_eq_top_iff_finite, x.prop
-/
theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens -> Prop}
    {ι} (U : ι -> X.affineOpens) (iSup_U : (⨆ i, U i : X.Opens) = ⊤)
    (V : X.affineOpens)
    (basicOpen : forall (U : X.affineOpens) (f : Γ(X, U)), P U -> P (X.affineBasicOpen f))
    (openCover :
      forall (U : X.affineOpens) (s : Finset (Γ(X, U)))
        (_ : Ideal.span (s : Set (Γ(X, U))) = ⊤),
        (forall f : s, P (X.affineBasicOpen f.1)) -> P U)
    (hU : forall i, P (U i)) : P V := by
  have : forall (x : V.1), exists f : Γ(X, V), ↑x in X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (iSup_U.ge (Set.mem_univ x))
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩
    convert! basicOpen _ g (hU i) using 1
    ext1
    exact e
  choose f hf₁ hf₂ using this
  suffices Ideal.span (Set.range f) = ⊤ by
    obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
    apply openCover V t ht₂
    rintro ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := ht₁ hi
    exact hf₂ x
  rw [← V.prop.self_le_iSup_basicOpen_iff]
  intro x hx
  rw [iSup_range']; rw [Opens.mem_iSup]
  exact ⟨_, hf₁ ⟨x, hx⟩⟩

/--
lemma `eq_of_SpecMap_comp_eq_of_isAffineOpen` / 引理 `eq_of_SpecMap_comp_eq_of_isAffineOpen`

English:
lemma eq_of_SpecMap_comp_eq_of_isAffineOpen
  statement: {R S : CommRingCat} {X : Scheme}
  proof: by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx => hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx => hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.iso

中文:
引理 eq_of_SpecMap_comp_eq_of_isAffineOpen
  结论: {R S : 交换环范畴} {X : 概形}
  证明: by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx => hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx => hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.iso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, IsOpenImmersion, IsOpenImmersion.lift_fac, Set.range_subset_iff, Spec.homEquiv.injective.eq_iff, Spec.map_injective.eq_iff, cancel_mono, eq_iff, hU.isoSpec.hom, hUf.ge, hUg.ge, homEquiv, injective, isoSpec, lift_fac, map_injective, mono_of_injective, range_subset_iff
-/
lemma eq_of_SpecMap_comp_eq_of_isAffineOpen {R S : CommRingCat} {X : Scheme}
    (φ : R ⟶ S) (hφ : Function.Injective φ)
    {f g : Spec R ⟶ X} (U : X.Opens) (hU : IsAffineOpen U) (hUf : f ⁻¹ᵁ U = ⊤) (hUg : g ⁻¹ᵁ U = ⊤)
    (H : Spec.map φ ≫ f = Spec.map φ ≫ g) : f = g := by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx => hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx => hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.isoSpec.hom]; rw [← Spec.homEquiv.injective.eq_iff]; rw [← cancel_mono φ]; rw [← Spec.map_injective.eq_iff]
  simp [← cancel_mono U.ι, H]

section ZeroLocus

namespace Scheme

open ConcreteCategory

variable (X : Scheme.{u})

/--
lemma `toSpecΓ_preimage_zeroLocus` / 引理 `toSpecΓ_preimage_zeroLocus`

English:
lemma toSpecΓ_preimage_zeroLocus
  given: (s : Set Γ(X, ⊤))
  proof: LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

中文:
引理 toSpecΓ_preimage_zeroLocus
  条件: (s : 集合 Γ(X, ⊤))
  证明: LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.to
-/
lemma toSpecΓ_preimage_zeroLocus (s : Set Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocus s :=
  LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isoSpec_image_zeroLocus` / 引理 `isoSpec_image_zeroLocus`

English:
lemma isoSpec_image_zeroLocus
  statement: [IsAffine X]
  proof: by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  simp [Scheme.isoSpec, Set.image_preimage_eq (h := (bijective_of_isIso _).surjective)]

中文:
引理 isoSpec_image_zeroLocus
  结论: [是仿射 X]
  证明: by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  simp [Scheme.isoSpec, Set.image_preimage_eq (h := (bijective_of_isIso _).surjective)]

Depends on / 依赖: Scheme, Scheme.isoSpec, Set.image_preimage_eq, X.toSpec, bijective_of_isIso, image_preimage_eq, isoSpec, surjective
-/
lemma isoSpec_image_zeroLocus [IsAffine X]
    (s : Set Γ(X, ⊤)) :
    X.isoSpec.hom '' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  simp [Scheme.isoSpec, Set.image_preimage_eq (h := (bijective_of_isIso _).surjective)]

/--
lemma `toSpecΓ_image_zeroLocus` / 引理 `toSpecΓ_image_zeroLocus`

English:
lemma toSpecΓ_image_zeroLocus
  given: [IsAffine X] (s : Set Γ(X, ⊤))
  proof: X.isoSpec_image_zeroLocus _

中文:
引理 toSpecΓ_image_zeroLocus
  条件: [是仿射 X] (s : 集合 Γ(X, ⊤))
  证明: X.isoSpec_image_zeroLocus _

Depends on / 依赖: X.isoSpec_image_zeroLocus, isoSpec_image_zeroLocus
-/
lemma toSpecΓ_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toSpecΓ '' X.zeroLocus s = PrimeSpectrum.zeroLocus s :=
  X.isoSpec_image_zeroLocus _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isoSpec_inv_preimage_zeroLocus` / 引理 `isoSpec_inv_preimage_zeroLocus`

English:
lemma isoSpec_inv_preimage_zeroLocus
  given: [IsAffine X] (s : Set Γ(X, ⊤))
  proof: by
  rw [← toSpecΓ_preimage_zeroLocus]; rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [X.isoSpec_inv_toSpecΓ]
  rfl

中文:
引理 isoSpec_inv_preimage_zeroLocus
  条件: [是仿射 X] (s : 集合 Γ(X, ⊤))
  证明: by
  rw [← toSpecΓ_preimage_zeroLocus]; rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [X.isoSpec_inv_toSpecΓ]
  rfl

Depends on / 依赖: Scheme, Scheme.Hom.comp_base, Set.preimage_comp, TopCat, TopCat.coe_comp, X.isoSpec_inv_toSpec, coe_comp, comp_base, preimage_comp
-/
lemma isoSpec_inv_preimage_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← toSpecΓ_preimage_zeroLocus]; rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [X.isoSpec_inv_toSpecΓ]
  rfl

/--
lemma `isoSpec_inv_image_zeroLocus` / 引理 `isoSpec_inv_image_zeroLocus`

English:
lemma isoSpec_inv_image_zeroLocus
  given: [IsAffine X] (s : Set Γ(X, ⊤))
  proof: by
  rw [← isoSpec_inv_preimage_zeroLocus]; rw [Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

中文:
引理 isoSpec_inv_image_zeroLocus
  条件: [是仿射 X] (s : 集合 Γ(X, ⊤))
  证明: by
  rw [← isoSpec_inv_preimage_zeroLocus]; rw [Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

Depends on / 依赖: Set.image_preimage_eq, X.isoSpec.inv.base, bijective_of_isIso, image_preimage_eq, isoSpec, isoSpec_inv_preimage_zeroLocus, surjective
-/
lemma isoSpec_inv_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv '' PrimeSpectrum.zeroLocus s = X.zeroLocus s := by
  rw [← isoSpec_inv_preimage_zeroLocus]; rw [Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

/--
lemma `eq_zeroLocus_of_isClosed_of_isAffine` / 引理 `eq_zeroLocus_of_isClosed_of_isAffine`

English:
lemma eq_zeroLocus_of_isClosed_of_isAffine
  given: [IsAffine X] (s : Set X)
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · let Z : Set (Spec Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus

中文:
引理 eq_zeroLocus_of_isClosed_of_isAffine
  条件: [是仿射 X] (s : 集合 X)
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · let Z : Set (Spec Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus

Depends on / 依赖: I.carrier, IsClosed, PrimeSpectrum, PrimeSpectrum.isClosed_iff_zeroLocus_ideal, Scheme, Scheme.toSpec, Set.preimage_image_eq, X.isoSpec.hom.base, X.isoSpec.hom.homeomorph, X.to, bijective_of_isIso, carrier, homeomorph, injective, isClosedMap, isClosed_iff_zeroLocus_ideal, isoSpec, preimage_image_eq, zeroLocus_isClosed
-/
lemma eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) :
    IsClosed s ↔ exists I : Ideal Γ(X, ⊤), s = X.zeroLocus (U := ⊤) I := by
  refine ⟨fun hs => ?_, ?_⟩
  · let Z : Set (Spec Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus, ← hI, Z]
    symm
    exact Set.preimage_image_eq _ (bijective_of_isIso X.isoSpec.hom.base).injective
  · rintro ⟨I, rfl⟩
    exact zeroLocus_isClosed X I.carrier

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Opens.toSpecΓ_preimage_basicOpen` / 引理 `Opens.toSpecΓ_preimage_basicOpen`

English:
lemma Opens.toSpecΓ_preimage_basicOpen
  given: {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U))
  proof: by
  dsimp [toSpecΓ]
  simp only [Scheme.toSpecΓ_preimage_basicOpen, preimage_basicOpen, ι_app, homOfLE_leOfHom]
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.ι_preimage_self.symm).op]; rw [← ConcreteCategory.comp_apply]
  congr 3
  simp [← Functor.map_comp]
  rfl

中文:
引理 Opens.toSpecΓ_preimage_basicOpen
  条件: {X : 概形.{u}} (U : X.Opens) (r : Γ(X, U))
  证明: by
  dsimp [toSpecΓ]
  simp only [Scheme.toSpecΓ_preimage_basicOpen, preimage_basicOpen, ι_app, homOfLE_leOfHom]
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.ι_preimage_self.symm).op]; rw [← ConcreteCategory.comp_apply]
  congr 3
  simp [← Functor.map_comp]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Functor, Functor.map_comp, IsAffine, IsSeparated, Scheme, Scheme.basicOpen_res_eq, Scheme.toSpec, X.IsSeparated, _preimage_self.symm, basicOpen_res_eq, comp_apply, eqToHom, homOfLE_leOfHom, map_comp, preimage_basicOpen
-/
lemma Opens.toSpecΓ_preimage_basicOpen {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = U.ι ⁻¹ᵁ X.basicOpen r := by
  dsimp [toSpecΓ]
  simp only [Scheme.toSpecΓ_preimage_basicOpen, preimage_basicOpen, ι_app, homOfLE_leOfHom]
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.ι_preimage_self.symm).op]; rw [← ConcreteCategory.comp_apply]
  congr 3
  simp [← Functor.map_comp]
  rfl

open Set.Notation in
/--
lemma `Opens.toSpecΓ_preimage_zeroLocus` / 引理 `Opens.toSpecΓ_preimage_zeroLocus`

English:
lemma Opens.toSpecΓ_preimage_zeroLocus
  given: {X : Scheme.{u}} (U : X.Opens) (s : Set Γ(X, U))
  proof: by
  ext x
  refine .trans (forall₂_congr fun y hy => ?_) Set.mem_iInter₂.symm
  exact iff_not_comm.mp congr(x in $(Opens.toSpecΓ_preimage_basicOpen U y)).to_iff.symm

中文:
引理 Opens.toSpecΓ_preimage_zeroLocus
  条件: {X : 概形.{u}} (U : X.Opens) (s : 集合 Γ(X, U))
  证明: by
  ext x
  refine .trans (forall₂_congr fun y hy => ?_) Set.mem_iInter₂.symm
  exact iff_not_comm.mp congr(x in $(Opens.toSpecΓ_preimage_basicOpen U y)).to_iff.symm

Depends on / 依赖: IsSeparated, Opens.toSpec, QuasiSeparatedSpace, Scheme, Set.mem_iInter, X.IsSeparated, iff_not_comm, iff_not_comm.mp, to_iff, to_iff.symm
-/
lemma Opens.toSpecΓ_preimage_zeroLocus {X : Scheme.{u}} (U : X.Opens) (s : Set Γ(X, U)) :
    U.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = U.1 ↓inter X.zeroLocus s := by
  ext x
  refine .trans (forall₂_congr fun y hy => ?_) Set.mem_iInter₂.symm
  exact iff_not_comm.mp congr(x in $(Opens.toSpecΓ_preimage_basicOpen U y)).to_iff.symm

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsAffineOpen.fromSpec_preimage_zeroLocus` / 引理 `IsAffineOpen.fromSpec_preimage_zeroLocus`

English:
lemma IsAffineOpen.fromSpec_preimage_zeroLocus
  statement: {X : Scheme.{u}} {U : X.Opens}
  proof: by
  ext x
  suffices (forall f in s, ¬f ∉ x.asIdeal) ↔ s subseteq x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using! this
  simp_rw [not_not]
  rfl

中文:
引理 是仿射开集.fromSpec_preimage_zeroLocus
  结论: {X : 概形.{u}} {U : X.Opens}
  证明: by
  ext x
  suffices (forall f in s, ¬f ∉ x.asIdeal) ↔ s subseteq x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using! this
  simp_rw [not_not]
  rfl

Depends on / 依赖: IsSeparated, IsSeparated.of_comp, X.IsSeparated, allowSynthFailures, asIdeal, comp_from, fromSpec_image_basicOpen, hU.fromSpec_image_basicOpen, infer_instance, not_not, of_comp, simp_rw, subseteq, terminal, terminal.comp_from, terminal.from, x.asIdeal
-/
lemma IsAffineOpen.fromSpec_preimage_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (forall f in s, ¬f ∉ x.asIdeal) ↔ s subseteq x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using! this
  simp_rw [not_not]
  rfl

/--
lemma `IsAffineOpen.fromSpec_image_zeroLocus` / 引理 `IsAffineOpen.fromSpec_image_zeroLocus`

English:
lemma IsAffineOpen.fromSpec_image_zeroLocus
  statement: {X : Scheme.{u}} {U : X.Opens}
  proof: by
  rw [← hU.fromSpec_preimage_zeroLocus]; rw [Set.image_preimage_eq_inter_range]; rw [range_fromSpec]

中文:
引理 是仿射开集.fromSpec_image_zeroLocus
  结论: {X : 概形.{u}} {U : X.Opens}
  证明: by
  rw [← hU.fromSpec_preimage_zeroLocus]; rw [Set.image_preimage_eq_inter_range]; rw [range_fromSpec]

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, Set.image_preimage_eq_inter_range, fromSpec_preimage_zeroLocus, hU.fromSpec_preimage_zeroLocus, image_preimage_eq_inter_range, isPullback_equalizer_prod, of_isPullback, range_fromSpec
-/
lemma IsAffineOpen.fromSpec_image_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec '' PrimeSpectrum.zeroLocus s = X.zeroLocus s inter U := by
  rw [← hU.fromSpec_preimage_zeroLocus]; rw [Set.image_preimage_eq_inter_range]; rw [range_fromSpec]

set_option backward.isDefEq.respectTransparency false in
open Set.Notation in
/--
lemma `Scheme.zeroLocus_inf` / 引理 `Scheme.zeroLocus_inf`

English:
lemma Scheme.zeroLocus_inf
  given: (X : Scheme.{u}) {U : X.Opens} (I J : Ideal Γ(X, U))
  proof: by
  suffices U.1 ↓inter (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓inter (X.zeroLocus (U := U) I union X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x in U
    · simpa [hxU] using congr(⟨x, hxU⟩ in $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le

中文:
引理 概形.zeroLocus_inf
  条件: (X : 概形.{u}) {U : X.Opens} (I J : 理想 Γ(X, U))
  证明: by
  suffices U.1 ↓inter (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓inter (X.zeroLocus (U := U) I union X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x in U
    · simpa [hxU] using congr(⟨x, hxU⟩ in $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le

Depends on / 依赖: Set.mem_union, Submodule, Submodule.coe_inf, U.toSpec, X.codisjoint_zeroLocus, X.zeroLocus, codisjoint_iff_compl_le_left, codisjoint_iff_compl_le_left.mp, codisjoint_zeroLocus, coe_inf, mem_union, toSpec, true_or, zeroLocus
-/
lemma Scheme.zeroLocus_inf (X : Scheme.{u}) {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I ⊓ J) = X.zeroLocus (U := U) I union X.zeroLocus (U := U) J := by
  suffices U.1 ↓inter (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓inter (X.zeroLocus (U := U) I union X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x in U
    · simpa [hxU] using congr(⟨x, hxU⟩ in $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I inter J)) hxU,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) I) hxU, true_or]
  simp only [← U.toSpecΓ_preimage_zeroLocus, PrimeSpectrum.zeroLocus_inf I J,
    Set.preimage_union]

/--
lemma `Scheme.zeroLocus_biInf` / 引理 `Scheme.zeroLocus_biInf`

English:
lemma Scheme.zeroLocus_biInf
  proof: by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH => ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp

中文:
引理 概形.zeroLocus_biInf
  证明: by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH => ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp

Depends on / 依赖: Set.iUnion_iUnion_eq_or_left, Set.mem_insert_iff, Set.union_assoc, Submodule, Submodule.coe_inf, X.zeroLocus, coe_inf, ht.induction_on, iUnion_iUnion_eq_or_left, induction_on, mem_insert_iff, union_assoc, zeroLocus, zeroLocus_inf
-/
lemma Scheme.zeroLocus_biInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι -> Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) :
    X.zeroLocus (U := U) ↑(⨅ i in t, I i) = (⋃ i in t, X.zeroLocus (U := U) (I i)) union (↑U)ᶜ := by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH => ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp

/--
lemma `Scheme.zeroLocus_biInf_of_nonempty` / 引理 `Scheme.zeroLocus_biInf_of_nonempty`

English:
lemma Scheme.zeroLocus_biInf_of_nonempty
  proof: by
  rw [zeroLocus_biInf I ht]; rw [Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx => Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)

中文:
引理 概形.zeroLocus_biInf_of_nonempty
  证明: by
  rw [zeroLocus_biInf I ht]; rw [Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx => Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)

Depends on / 依赖: Set.mem_iUnion, Set.union_eq_left, X.codisjoint_zeroLocus, X.zeroLocus, codisjoint_iff_compl_le_left, codisjoint_iff_compl_le_left.mp, codisjoint_zeroLocus, union_eq_left, zeroLocus, zeroLocus_biInf
-/
lemma Scheme.zeroLocus_biInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι -> Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) (ht' : t.Nonempty) :
    X.zeroLocus (U := U) ↑(⨅ i in t, I i) = ⋃ i in t, X.zeroLocus (U := U) (I i) := by
  rw [zeroLocus_biInf I ht]; rw [Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx => Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)

/--
lemma `Scheme.zeroLocus_iInf` / 引理 `Scheme.zeroLocus_iInf`

English:
lemma Scheme.zeroLocus_iInf
  proof: by
  simpa using zeroLocus_biInf I Set.finite_univ

中文:
引理 概形.zeroLocus_iInf
  证明: by
  simpa using zeroLocus_biInf I Set.finite_univ

Depends on / 依赖: Set.finite_univ, X.zeroLocus, finite_univ, zeroLocus, zeroLocus_biInf
-/
lemma Scheme.zeroLocus_iInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι -> Ideal Γ(X, U)) [Finite ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = (⋃ i, X.zeroLocus (U := U) (I i)) union (↑U)ᶜ := by
  simpa using zeroLocus_biInf I Set.finite_univ

/--
lemma `Scheme.zeroLocus_iInf_of_nonempty` / 引理 `Scheme.zeroLocus_iInf_of_nonempty`

English:
lemma Scheme.zeroLocus_iInf_of_nonempty
  proof: by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

中文:
引理 概形.zeroLocus_iInf_of_nonempty
  证明: by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

Depends on / 依赖: Set.finite_univ, X.zeroLocus, finite_univ, zeroLocus, zeroLocus_biInf_of_nonempty
-/
lemma Scheme.zeroLocus_iInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι -> Ideal Γ(X, U)) [Finite ι] [Nonempty ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = ⋃ i, X.zeroLocus (U := U) (I i) := by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

end ZeroLocus

section Factorization

variable {X : Scheme.{u}} {A : CommRingCat}

/--
Definition of `Scheme.Hom.liftQuotient` / `Scheme.Hom.liftQuotient` 的定义

English:
definition Scheme.Hom.liftQuotient
  signature: (f : X.Hom (Spec A)) (I : Ideal A)
  body: X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

中文:
定义 概形.态射.liftQuotient
  签名: (f : X.态射 (Spec A)) (I : 理想 A)
  定义体: X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.Quotient.lift, Quotient, Scheme, Spec.map, X.toSpec, appTop, f.appTop
-/
def Scheme.Hom.liftQuotient (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I <= RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
X ⟶ Spec .of (A ⧸ I) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Scheme.Hom.liftQuotient_comp` / 引理 `Scheme.Hom.liftQuotient_comp`

English:
lemma Scheme.Hom.liftQuotient_comp
  statement: (f : X.Hom (Spec A)) (I : Ideal A)
  proof: by
  rw [Scheme.Hom.liftQuotient]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom

中文:
引理 概形.态射.liftQuotient_comp
  结论: (f : X.态射 (Spec A)) (I : 理想 A)
  证明: by
  rw [Scheme.Hom.liftQuotient]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Ideal.Quotient.lift_comp_mk, Quotient, Scheme, Scheme.Hom.liftQuotient, Scheme.toSpec, Spec.map_comp, hom_comp, liftQuotient, lift_comp_mk, map_comp, ofHom_comp, ofHom_hom
-/
lemma Scheme.Hom.liftQuotient_comp (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I <= RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    f.liftQuotient I hI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = f := by
  rw [Scheme.Hom.liftQuotient]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [← CommRingCat.ofHom_comp]; rw [Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom]
  simp

/--
Definition of `specTargetImageIdeal` / `specTargetImageIdeal` 的定义

English:
definition specTargetImageIdeal
  signature: (f : X ⟶ Spec A)
  body: (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

中文:
定义 specTargetImageIdeal
  签名: (f : X ⟶ Spec A)
  定义体: (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

Depends on / 依赖: RingHom, RingHom.ker, Spec.adjunction, adjunction, homEquiv, unop.hom
-/
def specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A :=
  (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

/--
Definition of `specTargetImage` / `specTargetImage` 的定义

English:
definition specTargetImage
  signature: (f : X ⟶ Spec A)
  body: CommRingCat.of (A ⧸ specTargetImageIdeal f)

中文:
定义 specTargetImage
  签名: (f : X ⟶ Spec A)
  定义体: CommRingCat.of (A ⧸ specTargetImageIdeal f)

Depends on / 依赖: CommRingCat, CommRingCat.of, Smooth, specTargetImageIdeal
-/
def specTargetImage (f : X ⟶ Spec A) : CommRingCat :=
  CommRingCat.of (A ⧸ specTargetImageIdeal f)

/--
Definition of `specTargetImageFactorization` / `specTargetImageFactorization` 的定义

English:
definition specTargetImageFactorization
  signature: (f : X ⟶ Spec A)
  body: f.liftQuotient _ le_rfl

中文:
定义 specTargetImageFactorization
  签名: (f : X ⟶ Spec A)
  定义体: f.liftQuotient _ le_rfl

Depends on / 依赖: f.liftQuotient, le_rfl, liftQuotient
-/
def specTargetImageFactorization (f : X ⟶ Spec A) : X ⟶ Spec (specTargetImage f) :=
  f.liftQuotient _ le_rfl

/--
Definition of `specTargetImageRingHom` / `specTargetImageRingHom` 的定义

English:
definition specTargetImageRingHom
  signature: (f : X ⟶ Spec A)
  body: CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

中文:
定义 specTargetImageRingHom
  签名: (f : X ⟶ Spec A)
  定义体: CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.Quotient.mk, Quotient, specTargetImageIdeal
-/
def specTargetImageRingHom (f : X ⟶ Spec A) : A ⟶ specTargetImage f :=
  CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

variable (f : X ⟶ Spec A)

/--
lemma `specTargetImageRingHom_surjective` / 引理 `specTargetImageRingHom_surjective`

English:
lemma specTargetImageRingHom_surjective
  statement: Function.Surjective (specTargetImageRingHom f)
  proof: Ideal.Quotient.mk_surjective

中文:
引理 specTargetImageRingHom_surjective
  结论: 函数.满射 (specTargetImageRingHom f)
  证明: Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma specTargetImageRingHom_surjective : Function.Surjective (specTargetImageRingHom f) :=
  Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/--
lemma `specTargetImageFactorization_app_injective` / 引理 `specTargetImageFactorization_app_injective`

English:
lemma specTargetImageFactorization_app_injective
  proof: by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
change Function.Injective ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingH

中文:
引理 specTargetImageFactorization_app_injective
  证明: by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
change Function.Injective ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingH

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Function, Function.Injective, Injective, RingHom, RingHom.kerLift, RingHom.kerLift_injective, Scheme, Spec.adjunction, Spec.adjunction.homEquiv, adjunction, appTop, homEquiv, injective, isIso_iff_bijective, kerLift, kerLift_injective
-/
lemma specTargetImageFactorization_app_injective :
Function.Injective (specTargetImageFactorization f).appTop := by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
change Function.Injective ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingHom.kerLift_injective φ.hom).comp
  exact ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso _).hom).mp inferInstance).injective

@[reassoc (attr := simp)]
/--
lemma `specTargetImageFactorization_comp` / 引理 `specTargetImageFactorization_comp`

English:
lemma specTargetImageFactorization_comp
  proof: f.liftQuotient_comp _ _

中文:
引理 specTargetImageFactorization_comp
  证明: f.liftQuotient_comp _ _

Depends on / 依赖: f.liftQuotient_comp, liftQuotient_comp
-/
lemma specTargetImageFactorization_comp :
    specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f) = f :=
  f.liftQuotient_comp _ _

end Factorization

section Stalks

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) (x : PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency.types false in
variable (R) (x : PrimeSpectrum R) in
/-- The stalk of `Spec R` at `x` is isomorphic to `Rₚ`,
where `p` is the prime corresponding to `x`. -/
noncomputable
/--
Definition of `Spec.stalkIso` / `Spec.stalkIso` 的定义

English:
definition Spec.stalkIso
  signature: : (Spec R).presheaf.stalk x ≅ .of (Localization.AtPrime x.asIdeal)
  body: (StructureSheaf.stalkIso ..).toCommRingCatIso.symm

@[reassoc (attr := simp)]

中文:
定义 Spec.stalkIso
  签名: : (Spec R).presheaf.stalk x ≅ .of (Localization.AtPrime x.asIdeal)
  定义体: (StructureSheaf.stalkIso ..).toCommRingCatIso.symm

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, SmoothOfRelativeDimension, StructureSheaf, StructureSheaf.stalkIso, stalkIso, toCommRingCatIso, toCommRingCatIso.symm
-/
def Spec.stalkIso : (Spec R).presheaf.stalk x ≅ .of (Localization.AtPrime x.asIdeal) :=
  (StructureSheaf.stalkIso ..).toCommRingCatIso.symm

@[reassoc (attr := simp)]
/--
lemma `Spec.algebraMap_stalkIso_inv` / 引理 `Spec.algebraMap_stalkIso_inv`

English:
lemma Spec.algebraMap_stalkIso_inv
  proof: by
  ext s : 2
  exact (IsLocalization.algEquiv _ ((structureSheaf R).presheaf.stalk _) _).symm.commutes s

@[reassoc (attr := simp)]

中文:
引理 Spec.algebraMap_stalkIso_inv
  证明: by
  ext s : 2
  exact (IsLocalization.algEquiv _ ((structureSheaf R).presheaf.stalk _) _).symm.commutes s

@[reassoc (attr := simp)]

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, IsOpenImmersion, Smooth, algEquiv, commutes, presheaf, presheaf.stalk, structureSheaf, symm.commutes
-/
lemma Spec.algebraMap_stalkIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (stalkIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial := by
  ext s : 2
  exact (IsLocalization.algEquiv _ ((structureSheaf R).presheaf.stalk _) _).symm.commutes s

@[reassoc (attr := simp)]
/--
lemma `Spec.germ_stalkMapIso_hom` / 引理 `Spec.germ_stalkMapIso_hom`

English:
lemma Spec.germ_stalkMapIso_hom
  proof: by
  simp [← Iso.inv_comp_eq, ← Spec.algebraMap_stalkIso_inv_assoc]

#adaptation_note

中文:
引理 Spec.germ_stalkMapIso_hom
  证明: by
  simp [← Iso.inv_comp_eq, ← Spec.algebraMap_stalkIso_inv_assoc]

#adaptation_note

Depends on / 依赖: Iso.inv_comp_eq, MorphismProperty, MorphismProperty.pullback_fst, Spec.algebraMap_stalkIso_inv_assoc, algebraMap_stalkIso_inv_assoc, inv_comp_eq, pullback_fst
-/
lemma Spec.germ_stalkMapIso_hom :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ (stalkIso R x).hom =
      (Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (algebraMap R _) := by
  simp [← Iso.inv_comp_eq, ← Spec.algebraMap_stalkIso_inv_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`. -/
@[elementwise]
/--
lemma `Scheme.localRingHom_comp_stalkIso` / 引理 `Scheme.localRingHom_comp_stalkIso`

English:
lemma Scheme.localRingHom_comp_stalkIso
  given: {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S)
  proof: AlgebraicGeometry.localRingHom_comp_stalkIso f p

中文:
引理 概形.localRingHom_comp_stalkIso
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S) (p : 素谱 S)
  证明: AlgebraicGeometry.localRingHom_comp_stalkIso f p

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.localRingHom_comp_stalkIso, MorphismProperty, MorphismProperty.pullback_snd, localRingHom_comp_stalkIso, pullback_snd
-/
lemma Scheme.localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (Spec.stalkIso R (p.comap f.hom)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal f.hom rfl) ≫
      (Spec.stalkIso S p).inv = (Spec.map f).stalkMap p :=
  AlgebraicGeometry.localRingHom_comp_stalkIso f p

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Scheme.arrowStalkMapSpecIso` / `Scheme.arrowStalkMapSpecIso` 的定义

English:
definition Scheme.arrowStalkMapSpecIso
  signature: {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S)
  body: Arrow.isoMk
  (Spec.stalkIso R (p.comap f.hom))
(Spec.stalkIso S p) by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

中文:
定义 概形.arrowStalkMapSpecIso
  签名: {R S : 交换环范畴.{u}} (f : R ⟶ S) (p : 素谱 S)
  定义体: Arrow.isoMk
  (Spec.stalkIso R (p.comap f.hom))
(Spec.stalkIso S p) by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

Depends on / 依赖: Arrow.isoMk, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
def Scheme.arrowStalkMapSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    Arrow.mk ((Spec.map f).stalkMap p) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom
      (p.comap f.hom).asIdeal p.asIdeal f.hom rfl) := Arrow.isoMk
  (Spec.stalkIso R (p.comap f.hom))
(Spec.stalkIso S p) by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

end Stalks
end AlgebraicGeometry
