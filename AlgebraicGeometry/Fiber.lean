/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Scheme-theoretic fiber

## Main result
- `AlgebraicGeometry.Scheme.Hom.fiber`: `f.fiber y` is the scheme-theoretic fiber of `f` at `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberHomeo`: `f.fiber y` is homeomorphic to `f ⁻¹' {y}`.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage`: Finite morphisms have finite fibers.
- `AlgebraicGeometry.Scheme.Hom.discrete_fiber`: Finite morphisms have discrete fibers.

-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/--
Definition of `Scheme.Hom.fiber` / `Scheme.Hom.fiber` 的定义

English:
definition Scheme.Hom.fiber
  signature: (f : X ⟶ Y) (y : Y)
  body: pullback f (Y.fromSpecResidueField y)

中文:
定义 Scheme.Hom.fiber
  签名: (f : X ⟶ Y) (y : Y)
  定义体: pullback f (Y.fromSpecResidueField y)

Depends on / 依赖: Y.fromSpecResidueField, fromSpecResidueField, pullback
-/
def Scheme.Hom.fiber (f : X ⟶ Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)

/--
Definition of `Scheme.Hom.fiberι` / `Scheme.Hom.fiberι` 的定义

English:
definition Scheme.Hom.fiberι
  signature: (f : X ⟶ Y) (y : Y)
  body: pullback.fst _ _

中文:
定义 Scheme.Hom.fiberι
  签名: (f : X ⟶ Y) (y : Y)
  定义体: pullback.fst _ _

Depends on / 依赖: pullback, pullback.fst
-/
def Scheme.Hom.fiberι (f : X ⟶ Y) (y : Y) : f.fiber y ⟶ X := pullback.fst _ _

instance (f : X ⟶ Y) (y : Y) : (f.fiber y).CanonicallyOver X where hom := f.fiberι y

/--
Definition of `Scheme.Hom.fiberToSpecResidueField` / `Scheme.Hom.fiberToSpecResidueField` 的定义

English:
definition Scheme.Hom.fiberToSpecResidueField
  signature: (f : X ⟶ Y) (y : Y)
  body: pullback.snd _ _

@[reassoc]

中文:
定义 Scheme.Hom.fiberToSpecResidueField
  签名: (f : X ⟶ Y) (y : Y)
  定义体: pullback.snd _ _

@[reassoc]

Depends on / 依赖: pullback, pullback.snd
-/
def Scheme.Hom.fiberToSpecResidueField (f : X ⟶ Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _

@[reassoc]
/--
lemma `Scheme.Hom.fiber_fac` / 引理 `Scheme.Hom.fiber_fac`

English:
lemma Scheme.Hom.fiber_fac
  given: (f : X ⟶ Y) (y : Y)
  proof: pullback.condition

中文:
引理 Scheme.Hom.fiber_fac
  条件: (f : X ⟶ Y) (y : Y)
  证明: pullback.condition

Depends on / 依赖: condition, pullback, pullback.condition
-/
lemma Scheme.Hom.fiber_fac (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

/--
Definition of `Scheme.Hom.fiberOverSpecResidueField` / `Scheme.Hom.fiberOverSpecResidueField` 的定义

English:
definition Scheme.Hom.fiberOverSpecResidueField
  body: f.fiberToSpecResidueField y

中文:
定义 Scheme.Hom.fiberOverSpecResidueField
  定义体: f.fiberToSpecResidueField y
-/
@[reducible] def Scheme.Hom.fiberOverSpecResidueField
    (f : X ⟶ Y) (y : Y) : (f.fiber y).Over (Spec (Y.residueField y)) where
  hom := f.fiberToSpecResidueField y

/--
lemma `Scheme.Hom.fiberToSpecResidueField_apply` / 引理 `Scheme.Hom.fiberToSpecResidueField_apply`

English:
lemma Scheme.Hom.fiberToSpecResidueField_apply
  given: (f : X ⟶ Y) (y : Y) (x : f.fiber y)
  proof: Subsingleton.elim (α := PrimeSpectrum _) _ _

中文:
引理 Scheme.Hom.fiberToSpecResidueField_apply
  条件: (f : X ⟶ Y) (y : Y) (x : f.fiber y)
  证明: Subsingleton.elim (α := PrimeSpectrum _) _ _

Depends on / 依赖: PrimeSpectrum, Subsingleton, Subsingleton.elim
-/
lemma Scheme.Hom.fiberToSpecResidueField_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f.fiberToSpecResidueField y x = IsLocalRing.closedPoint (Y.residueField y) :=
  Subsingleton.elim (α := PrimeSpectrum _) _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_fiberToSpecResidueField_of_isPullback` / 引理 `isPullback_fiberToSpecResidueField_of_isPullback`

English:
lemma isPullback_fiberToSpecResidueField_of_isPullback
  statement: {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
  proof: by
  refine .of_right (h₁₂ := pullback.fst _ _) ?_ ?_
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (g y)))
  · simpa using! (IsPullback.of_hasPullback _ _).paste_horiz h
  · simp [Scheme.Hom.fiberToSpecResidueField]

中文:
引理 isPullback_fiberToSpecResidueField_of_isPullback
  结论: {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
  证明: by
  refine .of_right (h₁₂ := pullback.fst _ _) ?_ ?_
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (g y)))
  · simpa using! (IsPullback.of_hasPullback _ _).paste_horiz h
  · simp [Scheme.Hom.fiberToSpecResidueField]

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Scheme, Scheme.Hom.fiberToSpecResidueField, Z.fromSpecResidueField, fiberToSpecResidueField, fromSpecResidueField, of_hasPullback, of_right, paste_horiz, pullback, pullback.fst
-/
lemma isPullback_fiberToSpecResidueField_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    IsPullback (pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp))
      (snd.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) := by
  refine .of_right (h₁₂ := pullback.fst _ _) ?_ ?_
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (g y)))
  · simpa using! (IsPullback.of_hasPullback _ _).paste_horiz h
  · simp [Scheme.Hom.fiberToSpecResidueField]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Spec.fiberToSpecResidueFieldIso` / `Spec.fiberToSpecResidueFieldIso` 的定义

English:
definition Spec.fiberToSpecResidueFieldIso
  signature: (R S : Type u) [CommRing R] [CommRing S]
  body: by
  refine Arrow.isoMk' _ _
    (pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S) ?_ ?_
  · refine pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
refine asIso pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.resi

中文:
定义 Spec.fiberToSpecResidueFieldIso
  签名: (R S : 类型u) [CommRing R] [CommRing S]
  定义体: by
  refine Arrow.isoMk' _ _
    (pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S) ?_ ?_
  · refine pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
refine asIso pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.resi

Depends on / 依赖: Arrow.isoMk, ResidueField, Scheme, Scheme.Spec.mapIso, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Scheme.Spec.residueFieldIso, Spec.map, asIdeal, cat_disch, congrHom, mapIso, map_residueFieldIso_inv_eq_fromSpecResidueField, p.asIdeal.ResidueField, pullback, pullback.congrHom, pullback.map, pullbackSpecIso, pullbackSymmetry, residueFieldIso, symm.op
-/
noncomputable def Spec.fiberToSpecResidueFieldIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Arrow.mk ((Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiberToSpecResidueField p) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom <|
        algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
  refine Arrow.isoMk' _ _
    (pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S) ?_ ?_
  · refine pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
refine asIso pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) _).inv)
      (𝟙 _) (𝟙 _) (by simp) (by simp)
  · exact Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso (.of R) _).symm.op
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Hom.range_fiberι` / 引理 `Scheme.Hom.range_fiberι`

English:
lemma Scheme.Hom.range_fiberι
  given: (f : X ⟶ Y) (y : Y)
  proof: by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

中文:
引理 Scheme.Hom.range_fiberι
  条件: (f : X ⟶ Y) (y : Y)
  证明: by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

Depends on / 依赖: Pullback, Scheme, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField, range_fromSpecResidueField, range_fst
-/
lemma Scheme.Hom.range_fiberι (f : X ⟶ Y) (y : Y) :
    Set.range (f.fiberι y) = f ⁻¹' {y} := by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (y : Y) : IsPreimmersion (f.fiberι y) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/--
Definition of `Scheme.Hom.fiberHomeo` / `Scheme.Hom.fiberHomeo` 的定义

English:
definition Scheme.Hom.fiberHomeo
  signature: (f : X ⟶ Y) (y : Y)
  body: .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]

中文:
定义 Scheme.Hom.fiberHomeo
  签名: (f : X ⟶ Y) (y : Y)
  定义体: .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]

Depends on / 依赖: f.fiber, f.range_fiber, isEmbedding, isEmbedding.toHomeomorph, setCongr, toHomeomorph
-/
def Scheme.Hom.fiberHomeo (f : X ⟶ Y) (y : Y) : f.fiber y ≃ₜ f ⁻¹' {y} :=
  .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]
/--
lemma `Scheme.Hom.fiberHomeo_apply` / 引理 `Scheme.Hom.fiberHomeo_apply`

English:
lemma Scheme.Hom.fiberHomeo_apply
  given: (f : X ⟶ Y) (y : Y) (x : f.fiber y)
  proof: rfl

@[simp]

中文:
引理 Scheme.Hom.fiberHomeo_apply
  条件: (f : X ⟶ Y) (y : Y) (x : f.fiber y)
  证明: rfl

@[simp]
-/
lemma Scheme.Hom.fiberHomeo_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    (f.fiberHomeo y x).1 = f.fiberι y x := rfl

@[simp]
/--
lemma `Scheme.Hom.fiberι_fiberHomeo_symm` / 引理 `Scheme.Hom.fiberι_fiberHomeo_symm`

English:
lemma Scheme.Hom.fiberι_fiberHomeo_symm
  given: (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y})
  proof: congr($((f.fiberHomeo y).apply_symm_apply x).1)

中文:
引理 Scheme.Hom.fiberι_fiberHomeo_symm
  条件: (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y})
  证明: congr($((f.fiberHomeo y).apply_symm_apply x).1)

Depends on / 依赖: apply_symm_apply, f.fiberHomeo, fiberHomeo
-/
lemma Scheme.Hom.fiberι_fiberHomeo_symm (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y}) :
    f.fiberι y ((f.fiberHomeo y).symm x) = x :=
  congr($((f.fiberHomeo y).apply_symm_apply x).1)

/--
Definition of `Scheme.Hom.asFiber` / `Scheme.Hom.asFiber` 的定义

English:
definition Scheme.Hom.asFiber
  signature: (f : X ⟶ Y) (x : X)
  body: (f.fiberHomeo (f x)).symm ⟨x, rfl⟩

@[simp]

中文:
定义 Scheme.Hom.asFiber
  签名: (f : X ⟶ Y) (x : X)
  定义体: (f.fiberHomeo (f x)).symm ⟨x, rfl⟩

@[simp]

Depends on / 依赖: f.fiberHomeo, fiberHomeo
-/
def Scheme.Hom.asFiber (f : X ⟶ Y) (x : X) : f.fiber (f x) :=
    (f.fiberHomeo (f x)).symm ⟨x, rfl⟩

@[simp]
/--
lemma `Scheme.Hom.fiberι_asFiber` / 引理 `Scheme.Hom.fiberι_asFiber`

English:
lemma Scheme.Hom.fiberι_asFiber
  given: (f : X ⟶ Y) (x : X)
  statement: f.fiberι _ (f.asFiber x) = x
  proof: f.fiberι_fiberHomeo_symm _ _

中文:
引理 Scheme.Hom.fiberι_asFiber
  条件: (f : X ⟶ Y) (x : X)
  结论: f.fiberι _ (f.asFiber x) = x
  证明: f.fiberι_fiberHomeo_symm _ _

Depends on / 依赖: f.fiber
-/
lemma Scheme.Hom.fiberι_asFiber (f : X ⟶ Y) (x : X) : f.fiberι _ (f.asFiber x) = x :=
  f.fiberι_fiberHomeo_symm _ _

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) [QuasiCompact f] (y : Y) : CompactSpace (f.fiber y) :=
  haveI : QuasiCompact (f.fiberToSpecResidueField y) :=
      MorphismProperty.pullback_snd _ _ inferInstance
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
    (f := f.fiberToSpecResidueField y).mp inferInstance

/--
lemma `Scheme.Hom.isCompact_preimage_singleton` / 引理 `Scheme.Hom.isCompact_preimage_singleton`

English:
lemma Scheme.Hom.isCompact_preimage_singleton
  given: (f : X ⟶ Y) [QuasiCompact f] (y : Y)
  proof: f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

@[deprecated (since := "2026-02-05")]
alias QuasiCompact.isCompact_preimage_singleton := Scheme.Hom.isCompact_preimage_singleton

中文:
引理 Scheme.Hom.isCompact_preimage_singleton
  条件: (f : X ⟶ Y) [QuasiCompact f] (y : Y)
  证明: f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

@[deprecated (since := "2026-02-05")]
alias QuasiCompact.isCompact_preimage_singleton := Scheme.Hom.isCompact_preimage_singleton

Depends on / 依赖: continuous, f.fiber, f.range_fiber, isCompact_range
-/
lemma Scheme.Hom.isCompact_preimage_singleton (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    IsCompact (f ⁻¹' {y}) :=
  f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

@[deprecated (since := "2026-02-05")]
alias QuasiCompact.isCompact_preimage_singleton := Scheme.Hom.isCompact_preimage_singleton

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) [IsAffineHom f] (y : Y) : IsAffine (f.fiber y) :=
  haveI : IsAffineHom (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  isAffine_of_isAffineHom (f.fiberToSpecResidueField y)

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (y : Y) [LocallyOfFiniteType f] : JacobsonSpace (f.fiber y) :=
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField y)

/--
Definition of `Scheme.Hom.asFiberHom` / `Scheme.Hom.asFiberHom` 的定义

English:
definition Scheme.Hom.asFiberHom
  signature: (f : X ⟶ Y) (x : X)
  body: pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap _)) (by simp)

@[reassoc (attr := simp)]

中文:
定义 Scheme.Hom.asFiberHom
  签名: (f : X ⟶ Y) (x : X)
  定义体: pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap _)) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: Spec.map, X.fromSpecResidueField, f.residueFieldMap, fromSpecResidueField, pullback, pullback.lift, residueFieldMap
-/
def Scheme.Hom.asFiberHom (f : X ⟶ Y) (x : X) : Spec (X.residueField x) ⟶ f.fiber (f x) :=
  pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap _)) (by simp)

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.asFiberHom_fiberι` / 引理 `Scheme.Hom.asFiberHom_fiberι`

English:
lemma Scheme.Hom.asFiberHom_fiberι
  given: (f : X ⟶ Y) (x : X)
  proof: pullback.lift_fst ..

@[reassoc (attr := simp)]

中文:
引理 Scheme.Hom.asFiberHom_fiberι
  条件: (f : X ⟶ Y) (x : X)
  证明: pullback.lift_fst ..

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma Scheme.Hom.asFiberHom_fiberι (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberι _ = X.fromSpecResidueField x := pullback.lift_fst ..

@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.asFiberHom_fiberToSpecResidueField` / 引理 `Scheme.Hom.asFiberHom_fiberToSpecResidueField`

English:
lemma Scheme.Hom.asFiberHom_fiberToSpecResidueField
  given: (f : X ⟶ Y) (x : X)
  proof: pullback.lift_snd ..

@[simp]

中文:
引理 Scheme.Hom.asFiberHom_fiberToSpecResidueField
  条件: (f : X ⟶ Y) (x : X)
  证明: pullback.lift_snd ..

@[simp]

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
lemma Scheme.Hom.asFiberHom_fiberToSpecResidueField (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberToSpecResidueField _ = Spec.map (f.residueFieldMap _) :=
  pullback.lift_snd ..

@[simp]
/--
lemma `Scheme.Hom.asFiberHom_apply` / 引理 `Scheme.Hom.asFiberHom_apply`

English:
lemma Scheme.Hom.asFiberHom_apply
  given: (f : X ⟶ Y) (x : X) (y)
  proof: (f.fiberι _).isEmbedding.injective (by simp [← Scheme.Hom.comp_apply])

@[simp]

中文:
引理 Scheme.Hom.asFiberHom_apply
  条件: (f : X ⟶ Y) (x : X) (y)
  证明: (f.fiberι _).isEmbedding.injective (by simp [← Scheme.Hom.comp_apply])

@[simp]

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, comp_apply, f.fiber, injective, isEmbedding, isEmbedding.injective
-/
lemma Scheme.Hom.asFiberHom_apply (f : X ⟶ Y) (x : X) (y) :
    f.asFiberHom x y = f.asFiber x :=
  (f.fiberι _).isEmbedding.injective (by simp [← Scheme.Hom.comp_apply])

@[simp]
/--
lemma `Scheme.Hom.range_asFiberHom` / 引理 `Scheme.Hom.range_asFiberHom`

English:
lemma Scheme.Hom.range_asFiberHom
  given: (f : X ⟶ Y) (x : X)
  proof: by aesop

中文:
引理 Scheme.Hom.range_asFiberHom
  条件: (f : X ⟶ Y) (x : X)
  证明: by aesop
-/
lemma Scheme.Hom.range_asFiberHom (f : X ⟶ Y) (x : X) :
    Set.range (f.asFiberHom x) = {f.asFiber x} := by aesop

instance (f : X ⟶ Y) (x : X) : IsPreimmersion (f.asFiberHom x) :=
  have : IsPreimmersion (f.asFiberHom x ≫ f.fiberι _) := f.asFiberHom_fiberι x ▸ inferInstance
  .of_comp _ (f.fiberι _)

end AlgebraicGeometry
