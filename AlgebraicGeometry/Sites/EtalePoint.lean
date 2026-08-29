/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.FieldTheory.SeparableClosure

/-!

# Points of the étale site

In this file, we show that a morphism `Spec (.of Ω) ⟶ S` where `Ω` is
a separably closed field defines a point on the small étale site of `S`.
We show that these points form a conservative family.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_fac_of_etale_of_isSepClosed` / 引理 `exists_fac_of_etale_of_isSepClosed`

English:
lemma exists_fac_of_etale_of_isSepClosed
  statement: {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
  proof: by
  obtain ⟨⟨s, a⟩, rfl⟩ := (SpecToEquivOfField Ω S).symm.surjective s
  obtain rfl : f x = s := by simp [hx, SpecToEquivOfField]
  let m := (f.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  let b : X.residueField x ->ₐ[S.residueField (f x)] Ω :=
    IsSepClosed.lift
  have : f.resid

中文:
引理 exists_fac_of_etale_of_isSepClosed
  结论: {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
  证明: by
  obtain ⟨⟨s, a⟩, rfl⟩ := (SpecToEquivOfField Ω S).symm.surjective s
  obtain rfl : f x = s := by simp [hx, SpecToEquivOfField]
  let m := (f.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  let b : X.residueField x ->ₐ[S.residueField (f x)] Ω :=
    IsSepClosed.lift
  have : f.resid

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsSepClosed, IsSepClosed.lift, S.residueField, Spec.map, SpecToEquivOfField, X.fromSpecResidueField, X.residueField, a.hom, algebraize, b.comp_algebraMap, b.toRingHom, comp_algebraMap, f.residueFieldMap, fromSpecResidueField, residueField, residueFieldMap, surjective, symm.surjective
-/
lemma exists_fac_of_etale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : X) (hx : f x = s default) :
    exists (l : Spec (.of Ω) ⟶ X), l ≫ f = s ∧ l default = x := by
  obtain ⟨⟨s, a⟩, rfl⟩ := (SpecToEquivOfField Ω S).symm.surjective s
  obtain rfl : f x = s := by simp [hx, SpecToEquivOfField]
  let m := (f.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  let b : X.residueField x ->ₐ[S.residueField (f x)] Ω :=
    IsSepClosed.lift
  have : f.residueFieldMap x ≫ CommRingCat.ofHom b.toRingHom = a := by
    ext1; exact b.comp_algebraMap
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · simp [SpecToEquivOfField, ← this]
    rfl
  · dsimp
    apply fromSpecResidueField_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofiltered (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements
  body: Functor.isCofiltered_elements _

中文:
实例 :
  签名: IsCofiltered (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements
  定义体: Functor.isCofiltered_elements _

Depends on / 依赖: Functor, Functor.isCofiltered_elements, isCofiltered_elements
-/
instance : IsCofiltered (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements :=
  Functor.isCofiltered_elements _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism `s : Spec (.of Ω) ⟶ S` where `Ω` is a separably closed field
defines a point for the small étale site of `S`. -/
@[simps]
/--
Definition of `pointSmallEtale` / `pointSmallEtale` 的定义

English:
definition pointSmallEtale
  signature: : (smallEtaleTopology S).Point where
  body: Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec S)
        (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨X, x⟩
      cases X with |

中文:
定义 pointSmallEtale
  签名: : (smallEtaleTopology S).Point where
  定义体: Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec S)
        (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨X, x⟩
      cases X with |

Depends on / 依赖: Etale.forget, Over.mk, coyoneda, coyoneda.obj, forget
-/
noncomputable def pointSmallEtale : (smallEtaleTopology S).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec S)
        (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨X, x⟩
      cases X with | _ Y f
      obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
      dsimp at y hy
      obtain ⟨R, j, _, y', rfl⟩ : exists (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
          (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
        obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
          (x := y.base default) (U := ⊤) (by simp)
        refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
        rintro _ ⟨a, rfl⟩
        rwa [Subsingleton.elim a default]
      exact ⟨_,
        ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
        ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩)
  jointly_surjective {X} R hR φ := by
    cases X with | _ X f
    obtain ⟨φ : Spec (.of Ω) ⟶ X, rfl : φ ≫ f = s, rfl⟩ := Over.homMk_surjective φ
    obtain ⟨𝒰, h, _, le⟩ := (mem_smallGrothendieckTopology _ _).1 hR
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (φ default)
    obtain ⟨l, hl₁, hl₂⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) φ _ hy
    have : 𝒰.f i ≫ f = 𝒰.X i ↘ S := HomIsOver.comp_over (f := 𝒰.f i) (S := S)
    exact ⟨(𝒰.X i).asOverProp S inferInstance,
      MorphismProperty.Over.homMk (𝒰.f i), le _ _ ⟨i⟩, Over.homMk l, by cat_disch⟩

variable {s₀ : S} (hs₀ : s default = s₀)

/-- Given a morphism `s : Spec (.of Ω) ⟶ S` with image `s₀ : S` where `Ω` is a
separably closed field, this is the canonical map
`(pointSmallEtale s).fiber.obj X ⟶ X.hom ⁻¹' {s₀}` for `X : S.Etale`. -/
@[simps]
/--
Definition of `pointSmallEtaleFiberObjToPreimage` / `pointSmallEtaleFiberObjToPreimage` 的定义

English:
definition pointSmallEtaleFiberObjToPreimage
  signature: {X : S.Etale}
  body: ⟨t.left (default : Spec (.of Ω)), by
    have := (Over.w t).symm
    cat_disch⟩

中文:
定义 pointSmallEtaleFiberObjToPreimage
  签名: {X : S.Etale}
  定义体: ⟨t.left (default : Spec (.of Ω)), by
    have := (Over.w t).symm
    cat_disch⟩

Depends on / 依赖: Over.w, cat_disch, t.left
-/
noncomputable def pointSmallEtaleFiberObjToPreimage {X : S.Etale}
    (t : (pointSmallEtale s).fiber.obj X) :
    X.hom ⁻¹' {s₀} :=
  ⟨t.left (default : Spec (.of Ω)), by
    have := (Over.w t).symm
    cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
instance {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] (x : X) :
    Etale (f.fiberToSpecResidueField x) := by
  dsimp [Hom.fiberToSpecResidueField]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pointSmallEtaleFiberObjToPreimage_surjective` / 引理 `pointSmallEtaleFiberObjToPreimage_surjective`

English:
lemma pointSmallEtaleFiberObjToPreimage_surjective
  given: (X : S.Etale)
  proof: by
  intro y
  obtain ⟨y, rfl⟩ := (X.hom.fiberHomeo s₀).surjective y
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω _).symm.surjective s
  obtain rfl : t = s₀ := by simp [SpecToEquivOfField, ← hs₀]
  obtain ⟨l, hl, rfl⟩ := exists_fac_of_etale_of_isSepClosed
    (X.hom.fiberToSpecResidueField

中文:
引理 pointSmallEtaleFiberObjToPreimage_surjective
  条件: (X : S.Etale)
  证明: by
  intro y
  obtain ⟨y, rfl⟩ := (X.hom.fiberHomeo s₀).surjective y
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω _).symm.surjective s
  obtain rfl : t = s₀ := by simp [SpecToEquivOfField, ← hs₀]
  obtain ⟨l, hl, rfl⟩ := exists_fac_of_etale_of_isSepClosed
    (X.hom.fiberToSpecResidueField

Depends on / 依赖: Over.homMk, Scheme, Scheme.SpecToEquivOfField, Spec.map, SpecToEquivOfField, X.hom.fiber, X.hom.fiberHomeo, X.hom.fiberToSpecResidueField, X.hom.fiber_fac, exists_fac_of_etale_of_isSepClosed, fiberHomeo, fiberToSpecResidueField, fiber_fac, reassoc_of, subsingleton, surjective, symm.surjective
-/
lemma pointSmallEtaleFiberObjToPreimage_surjective (X : S.Etale) :
    Function.Surjective (pointSmallEtaleFiberObjToPreimage s hs₀ (X := X)) := by
  intro y
  obtain ⟨y, rfl⟩ := (X.hom.fiberHomeo s₀).surjective y
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω _).symm.surjective s
  obtain rfl : t = s₀ := by simp [SpecToEquivOfField, ← hs₀]
  obtain ⟨l, hl, rfl⟩ := exists_fac_of_etale_of_isSepClosed
    (X.hom.fiberToSpecResidueField _) (Spec.map a) y (by subsingleton)
  refine ⟨Over.homMk (l ≫ X.hom.fiberι t) ?_, rfl⟩
  simp [X.hom.fiber_fac, reassoc_of% hl]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isConservative_pointSmallEtale` / 引理 `isConservative_pointSmallEtale`

English:
lemma isConservative_pointSmallEtale
  proof: .mk' (fun X R hR => by
    obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ : exists i, s i default = X.hom x := by
      have := Set.mem_univ (X.hom x)
      

中文:
引理 isConservative_pointSmallEtale
  证明: .mk' (fun X R hR => by
    obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ : exists i, s i default = X.hom x := by
      have := Set.mem_univ (X.hom x)
      

Depends on / 依赖: Functor, Functor.id_obj, R.exists_eq_ofArrows, Set.mem_iUnion, Set.mem_range, Set.mem_univ, Subsingleton, Subsingleton.elim, X.hom, exists_eq_ofArrows, id_obj, iff_true, mem_iUnion, mem_range, mem_univ, ofArrows_mem_smallEtaleTopology_iff, pointSmallEtaleFiberObjToPreimage_surjective
-/
lemma isConservative_pointSmallEtale
    {ι : Type*} {S : Scheme.{u}}
    {Ω : ι -> Type u} [forall i, Field (Ω i)] [forall i, IsSepClosed (Ω i)]
    (s : forall i, Spec (.of (Ω i)) ⟶ S)
    (hs : ⋃ i, Set.range (s i) = .univ) :
    (ObjectProperty.ofObj (fun i => pointSmallEtale (s i))).IsConservativeFamilyOfPoints :=
  .mk' (fun X R hR => by
    obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ : exists i, s i default = X.hom x := by
      have := Set.mem_univ (X.hom x)
      simp only [← hs, Functor.id_obj, Set.mem_iUnion, Set.mem_range] at this
      obtain ⟨i, y, hy⟩ := this
      obtain rfl := Subsingleton.elim y default
      exact ⟨i, hy⟩
    obtain ⟨x', hx'⟩ := pointSmallEtaleFiberObjToPreimage_surjective (s i) hi X ⟨x, by simp⟩
    rw [Subtype.ext_iff] at hx'
    simp only [Functor.id_obj, pointSmallEtaleFiberObjToPreimage_coe, Etale.forget_obj_left] at hx'
    subst hx'
    obtain ⟨W, g, ⟨Z, p, _, ⟨a⟩, rfl⟩, y, rfl⟩ := hR ⟨_, ⟨i⟩⟩ x'
    exact ⟨a, (pointSmallEtaleFiberObjToPreimage (s i) hi (y ≫ p.hom)).1, rfl⟩)

/--
lemma `isConservativeFamilyOfPoints_pointSmallEtale'` / 引理 `isConservativeFamilyOfPoints_pointSmallEtale'`

English:
lemma isConservativeFamilyOfPoints_pointSmallEtale'
  given: (S : Scheme.{u})
  proof: isConservative_pointSmallEtale _ (by
    ext s
    simp only [Equiv.invFun_as_coe, Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, by simp [SpecToEquivOfField]⟩)

中文:
引理 isConservativeFamilyOfPoints_pointSmallEtale'
  条件: (S : Scheme.{u})
  证明: isConservative_pointSmallEtale _ (by
    ext s
    simp only [Equiv.invFun_as_coe, Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, by simp [SpecToEquivOfField]⟩)

Depends on / 依赖: Equiv.invFun_as_coe, Set.mem_iUnion, Set.mem_range, Set.mem_univ, SpecToEquivOfField, iff_true, invFun_as_coe, isConservative_pointSmallEtale, mem_iUnion, mem_range, mem_univ
-/
lemma isConservativeFamilyOfPoints_pointSmallEtale' (S : Scheme.{u}) :
    (ObjectProperty.ofObj (fun (s : S) => pointSmallEtale
      ((SpecToEquivOfField (SeparableClosure (S.residueField s)) _).2
        ⟨s, CommRingCat.ofHom
          (algebraMap (S.residueField s) _)⟩))).IsConservativeFamilyOfPoints :=
  isConservative_pointSmallEtale _ (by
    ext s
    simp only [Equiv.invFun_as_coe, Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, by simp [SpecToEquivOfField]⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S)
  body: ⟨_, inferInstance, isConservativeFamilyOfPoints_pointSmallEtale' S⟩

中文:
实例 :
  签名: GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S)
  定义体: ⟨_, inferInstance, isConservativeFamilyOfPoints_pointSmallEtale' S⟩

Depends on / 依赖: isConservativeFamilyOfPoints_pointSmallEtale
-/
instance : GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S) where
  exists_objectProperty :=
    ⟨_, inferInstance, isConservativeFamilyOfPoints_pointSmallEtale' S⟩

end AlgebraicGeometry.Scheme
