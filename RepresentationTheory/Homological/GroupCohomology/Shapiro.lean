/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Shapiro's lemma for group cohomology

Given a commutative ring `k` and a subgroup `S ≤ G`, the file
`Mathlib/RepresentationTheory/Coinduced.lean` proves that the functor
`Coind_S^G : Rep k S ⥤ Rep k G` preserves epimorphisms. Since `Res(S) : Rep k G ⥤ Rep k S` is left
adjoint to `Coind_S^G`, this means `Res(S)` preserves projective objects. Since `Res(S)` is also
exact, given a projective resolution `P` of `k` as a trivial `k`-linear `G`-representation,
`Res(S)(P)` is a projective resolution of `k` as a trivial `k`-linear `S`-representation.

Since `Hom(Res(S)(P), A) ≅ Hom(P, Coind_S^G(A))` for any `S`-representation `A`, we conclude
Shapiro's lemma for group cohomology: `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)` for all `n`.

## Main definitions

* `groupCohomology.coindIso A n`: Shapiro's lemma for group cohomology: an isomorphism
  `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)`, given a subgroup `S ≤ G` and an `S`-representation `A`.

!-/

@[expose] public section

universe u

namespace groupCohomology

open CategoryTheory Finsupp TensorProduct Rep

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S)

set_option backward.defeqAttrib.useBackward true in
-- Note: this proof breaks if `resCoindHomEquiv.{u}` is replaced with `resCoindHomEquiv`.
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `linearYonedaObjResProjectiveResolutionIso` / `linearYonedaObjResProjectiveResolutionIso` 的定义

English:
definition linearYonedaObjResProjectiveResolutionIso
  body: HomologicalComplex.Hom.isoOfComponents
    (fun _ => (resCoindHomEquiv.{u} _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Rep.hom_ext <| by
        ext; simp [← ModuleCat.ofHom_comp, resCoindHomEquiv, hom_comm_apply])

中文:
定义 linearYonedaObjResProjectiveResolutionIso
  定义体: HomologicalComplex.Hom.isoOfComponents
    (fun _ => (resCoindHomEquiv.{u} _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Rep.hom_ext <| by
        ext; simp [← ModuleCat.ofHom_comp, resCoindHomEquiv, hom_comm_apply])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, LinearMap, LinearMap.ext, ModuleCat, ModuleCat.hom_ext, ModuleCat.ofHom_comp, Rep.hom_ext, hom_comm_apply, hom_ext, isoOfComponents, ofHom_comp, resCoindHomEquiv, toModuleIso
-/
noncomputable def linearYonedaObjResProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep.{u} k S) :
    ((resFunctor S.subtype).mapProjectiveResolution P).complex.linearYonedaObj k A ≅
      P.complex.linearYonedaObj k (coind S.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (resCoindHomEquiv.{u} _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Rep.hom_ext <| by
        ext; simp [← ModuleCat.ofHom_comp, resCoindHomEquiv, hom_comm_apply])

/--
Definition of `coindIso` / `coindIso` 的定义

English:
definition coindIso
  signature: (A : Rep k S) (n : Nat)
  body: (HomologicalComplex.homologyFunctor _ _ _).mapIso
    (inhomogeneousCochainsIso (coind S.subtype A) ≪≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).symm) ≪≫
  (groupCohomologyIso A n ((resFunctor _).mapProjectiveResolution <| barResolution k G)).symm

中文:
定义 coindIso
  签名: (A : Rep k S) (n : 自然数)
  定义体: (HomologicalComplex.homologyFunctor _ _ _).mapIso
    (inhomogeneousCochainsIso (coind S.subtype A) ≪≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).symm) ≪≫
  (groupCohomologyIso A n ((resFunctor _).mapProjectiveResolution <| barResolution k G)).symm

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyFunctor, S.subtype, barResolution, groupCohomologyIso, homologyFunctor, inhomogeneousCochainsIso, linearYonedaObjResProjectiveResolutionIso, mapIso, mapProjectiveResolution, resFunctor, subtype
-/
noncomputable def coindIso (A : Rep k S) (n : Nat) :
    groupCohomology (coind S.subtype A) n ≅ groupCohomology A n :=
  (HomologicalComplex.homologyFunctor _ _ _).mapIso
    (inhomogeneousCochainsIso (coind S.subtype A) ≪≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).symm) ≪≫
  (groupCohomologyIso A n ((resFunctor _).mapProjectiveResolution <| barResolution k G)).symm

end groupCohomology
