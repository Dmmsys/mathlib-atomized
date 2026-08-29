/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Schemes over algebraically closed fields

We show that if `X` is locally of finite type over an algebraically closed field `k`,
then the closed points of `X` are in bijection with the `k`-points of `X`.
See `AlgebraicGeometry.pointEquivClosedPoint`.

-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x})

/--
Definition of `residueFieldIsoBase` / `residueFieldIsoBase` 的定义

English:
definition residueFieldIsoBase
  signature: : X.residueField x ≅ .of K
  body: letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bi

中文:
定义 residueFieldIsoBase
  签名: : X.residueField x ≅ .of K
  定义体: letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bi

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, IsAlgClosed, IsAlgClosed.ringHom_bijective_of_isIntegral, IsFinite, IsIntegralHom, IsIntegralHom.SpecMap_iff, Spec.map_preimage, Spec.preimage, SpecMap_iff, X.fromSpecResidueField, fromSpecResidueField, infer_instance, isClosed_singleton_iff_isClosedImmersion, isFinite_iff_locallyOfFiniteType_of_jacobsonSpace, isIso_iff_bijective, map_preimage, preimage, ringHom_bijective_of_isIntegral
-/
def residueFieldIsoBase : X.residueField x ≅ .of K :=
  letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff]; rw [Spec.map_preimage]
    infer_instance
  (asIso (Spec.preimage (X.fromSpecResidueField x ≫ f))).symm

@[simp, reassoc]
/--
lemma `SpecMap_residueFieldIsoBase_inv` / 引理 `SpecMap_residueFieldIsoBase_inv`

English:
lemma SpecMap_residueFieldIsoBase_inv
  proof: Spec.map_preimage _

中文:
引理 SpecMap_residueFieldIsoBase_inv
  证明: Spec.map_preimage _

Depends on / 依赖: Spec.map_preimage, Surjective, Surjective.of_universallyClosed_of_isDominant, map_preimage, of_universallyClosed_of_isDominant
-/
lemma SpecMap_residueFieldIsoBase_inv :
    Spec.map (residueFieldIsoBase f x hx).inv = X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- If `k` is algebraically closed, this is the `k`-point of `X` associated to a closed point. -/
noncomputable
/--
Definition of `pointOfClosedPoint` / `pointOfClosedPoint` 的定义

English:
definition pointOfClosedPoint
  signature: : Spec (.of K) ⟶ X
  body: Spec.map (residueFieldIsoBase f x hx).hom ≫ X.fromSpecResidueField x

@[reassoc (attr := simp)]

中文:
定义 pointOfClosedPoint
  签名: : Spec (.of K) ⟶ X
  定义体: Spec.map (residueFieldIsoBase f x hx).hom ≫ X.fromSpecResidueField x

@[reassoc (attr := simp)]

Depends on / 依赖: Spec.map, X.fromSpecResidueField, fromSpecResidueField, residueFieldIsoBase
-/
def pointOfClosedPoint : Spec (.of K) ⟶ X :=
  Spec.map (residueFieldIsoBase f x hx).hom ≫ X.fromSpecResidueField x

@[reassoc (attr := simp)]
/--
lemma `pointOfClosedPoint_comp` / 引理 `pointOfClosedPoint_comp`

English:
lemma pointOfClosedPoint_comp
  statement: pointOfClosedPoint f x hx ≫ f = 𝟙 _
  proof: by
  simp [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv, ← Spec.map_comp]

@[simp]

中文:
引理 pointOfClosedPoint_comp
  结论: pointOfClosedPoint f x hx ≫ f = 𝟙 _
  证明: by
  simp [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv, ← Spec.map_comp]

@[simp]

Depends on / 依赖: Spec.map_comp, SpecMap_residueFieldIsoBase_inv, map_comp, pointOfClosedPoint
-/
lemma pointOfClosedPoint_comp : pointOfClosedPoint f x hx ≫ f = 𝟙 _ := by
  simp [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv, ← Spec.map_comp]

@[simp]
/--
lemma `pointOfClosedPoint_apply` / 引理 `pointOfClosedPoint_apply`

English:
lemma pointOfClosedPoint_apply
  given: (a : _)
  statement: pointOfClosedPoint f x hx a = x
  proof: by
  simp [pointOfClosedPoint]

中文:
引理 pointOfClosedPoint_apply
  条件: (a : _)
  结论: pointOfClosedPoint f x hx a = x
  证明: by
  simp [pointOfClosedPoint]

Depends on / 依赖: pointOfClosedPoint
-/
lemma pointOfClosedPoint_apply (a : _) : pointOfClosedPoint f x hx a = x := by
  simp [pointOfClosedPoint]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `k` is algebraically closed,
then the closed points of `X` are in bijection with the `k`-points of `X`. -/
@[simps]
/--
Definition of `pointEquivClosedPoint` / `pointEquivClosedPoint` 的定义

English:
definition pointEquivClosedPoint
  signature: :
  body: ⟨p.1 (IsLocalRing.closedPoint K), by
    have := isClosedImmersion_of_comp_eq_id _ _ p.2
    have := p.1.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at this
    exact fun x => congr(p.1 $(Subsingleton.elim _ _))⟩
  invFun x := ⟨pointOfClosedPoint f x.1 x.2, pointOfClosedPoint_c

中文:
定义 pointEquivClosedPoint
  签名: :
  定义体: ⟨p.1 (IsLocalRing.closedPoint K), by
    have := isClosedImmersion_of_comp_eq_id _ _ p.2
    have := p.1.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at this
    exact fun x => congr(p.1 $(Subsingleton.elim _ _))⟩
  invFun x := ⟨pointOfClosedPoint f x.1 x.2, pointOfClosedPoint_c

Depends on / 依赖: Category, Category.id_comp, IsLocalRing, IsLocalRing.closedPoint, Scheme, Scheme.SpecToEquivOfField, Scheme.SpecToEquivOfField_eq_iff, Set.range_eq_singleton, SpecToEquivOfField, SpecToEquivOfField_eq_iff, Subsingleton, Subsingleton.elim, closedPoint, id_comp, invFun, isClosedEmbedding, isClosedEmbedding.isClosed_range, isClosedImmersion_of_comp_eq_id, isClosed_range, left_inv
-/
def pointEquivClosedPoint :
    {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoints X where
  toFun p := ⟨p.1 (IsLocalRing.closedPoint K), by
    have := isClosedImmersion_of_comp_eq_id _ _ p.2
    have := p.1.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at this
    exact fun x => congr(p.1 $(Subsingleton.elim _ _))⟩
  invFun x := ⟨pointOfClosedPoint f x.1 x.2, pointOfClosedPoint_comp f x.1 x.2⟩
  left_inv p := by
    ext
    refine ((Scheme.SpecToEquivOfField _ _).symm_apply_eq (x := ⟨_, _⟩)).mpr ?_
    rw [Scheme.SpecToEquivOfField_eq_iff]
    dsimp [Scheme.SpecToEquivOfField]
    simp only [Category.id_comp, exists_const]
    generalize_proofs _ h
    refine (Category.comp_id _).symm.trans (((residueFieldIsoBase f _ h).eq_inv_comp).mp ?_)
    rw [← Spec.map_injective.eq_iff]
    simp only [Spec.map_id, Spec.map_comp, SpecMap_residueFieldIsoBase_inv]
    rw [reassoc_of% Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]; rw [p.2]
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext_of_apply_closedPoint_eq` / 引理 `ext_of_apply_closedPoint_eq`

English:
lemma ext_of_apply_closedPoint_eq
  proof: congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

中文:
引理 ext_of_apply_closedPoint_eq
  证明: congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

Depends on / 依赖: Subtype, Subtype.ext, UniversallyInjective, injective, pointEquivClosedPoint
-/
lemma ext_of_apply_closedPoint_eq
    {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K))
    [LocallyOfFiniteType h]
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g :=
  congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext_of_apply_eq` / 引理 `ext_of_apply_eq`

English:
lemma ext_of_apply_eq
  statement: {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [IsSeparated i] [LocallyOfFiniteType i]
  proof: by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S inter closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw 

中文:
引理 ext_of_apply_eq
  结论: {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [是分离 i] [局部有限型 i]
  证明: by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S inter closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw 

Depends on / 依赖: Category, Category.assoc, JacobsonSpace, JacobsonSpace.closure_inter_closedPoints_eq_closure, LocallyOfFiniteType, LocallyOfFiniteType.jacobsonSpace, Spec.map, SpecMap_residueFieldIsoBase_inv, cancel_epi, closedPoints, closure_inter_closedPoints_eq_closure, dense_iff_closure_eq, ext_of_apply_closedPoint_eq, ext_of_fromSpecResidueField_eq, jacobsonSpace, residueFieldIsoBase
-/
lemma ext_of_apply_eq {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [IsSeparated i] [LocallyOfFiniteType i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : forall x in S, IsClosed {x} -> f x = g x)
    (H' : f ≫ i = g ≫ i) : f = g := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S inter closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ i) x hx).hom)]
    refine ext_of_apply_closedPoint_eq i ?_ ?_ (by simpa using H x hxS hx) <;>
      simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, ← H']

end AlgebraicGeometry
