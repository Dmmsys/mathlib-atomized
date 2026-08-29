/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Shapiro's lemma for group homology

Given a commutative ring `k` and a subgroup `S ≤ G`,
the file `Mathlib/RepresentationTheory/Coinduced.lean` proves that
the functor `Coind_S^G : Rep k S ⥤ Rep k G` preserves epimorphisms.
Since `Res(S) : Rep k G ⥤ Rep k S` is left adjoint to `Coind_S^G`,
this means `Res(S)` preserves projective objects.
Since `Res(S)` is also exact,
given a projective resolution `P` of `k` as a trivial `k`-linear `G`-representation,
`Res(S)(P)` is a projective resolution of `k` as a trivial `k`-linear `S`-representation.

In `Mathlib/RepresentationTheory/Induced.lean`,
given a `G`-representation `X`,
we define a natural isomorphism between the functors `Rep k S ⥤ ModuleCat k` sending `A` to
`(Ind_S^G A ⊗ X)_G` and to `(A ⊗ Res(S)(X))_S`. Hence a projective resolution `P` of `k` as a
trivial `G`-representation induces an isomorphism of complexes
`(Ind_S^G A ⊗ P)_G ≅ (A ⊗ Res(S)(P))_S`, and since the homology of these complexes calculate
group homology, we conclude Shapiro's lemma: `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)` for all `n`.

## Main definitions

* `groupHomology.indIso A n`: Shapiro's lemma for group homology: an isomorphism
  `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A)`, given a subgroup `S ≤ G` and an `S`-representation `A`.

-/

@[expose] public section

universe u

namespace groupHomology

open CategoryTheory Finsupp TensorProduct Rep Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)

/--
Definition of `coinvariantsTensorResProjectiveResolutionIso` / `coinvariantsTensorResProjectiveResolutionIso` 的定义

English:
abbreviation coinvariantsTensorResProjectiveResolutionIso
  body: (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

中文:
缩写 coinvariantsTensorResProjectiveResolutionIso
  定义体: (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

Depends on / 依赖: NatIso, NatIso.mapHomologicalComplex, S.subtype, coinvariantsTensorIndNatIso, mapHomologicalComplex, subtype
-/
noncomputable abbrev coinvariantsTensorResProjectiveResolutionIso
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    ((resFunctor S.subtype).mapProjectiveResolution P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (ind S.subtype A) :=
  (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).app _

-- The smiley face in this proof can be avoided if you replace `ind` with `ind.{_, _, _, u}`.
-- The proof still compiles without this, but it takes much longer because of universe
-- unification issues.
-- Similarly, replacing `resFunctor.{u}` with `resFunctor` works but makes the proof
-- three times as slow.
/--
Definition of `indIso` / `indIso` 的定义

English:
definition indIso
  signature: [DecidableEq G] (A : Rep.{u} k S) (n : Nat)
  body: (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down Nat) n).mapIso
  (inhomogeneousChainsIso (ind S.subtype A :) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((resFunctor.{u} S.subtype).mapProjectiveResolution <|
    barResolution k G)).symm

中文:
定义 indIso
  签名: [DecidableEq G] (A : Rep.{u} k S) (n : 自然数)
  定义体: (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down Nat) n).mapIso
  (inhomogeneousChainsIso (ind S.subtype A :) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((resFunctor.{u} S.subtype).mapProjectiveResolution <|
    barResolution k G)).symm

Depends on / 依赖: ComplexShape, ComplexShape.down, HomologicalComplex, HomologicalComplex.homologyFunctor, ModuleCat, S.subtype, barResolution, coinvariantsTensorResProjectiveResolutionIso, groupHomologyIso, homologyFunctor, inhomogeneousChainsIso, mapIso, mapProjectiveResolution, resFunctor, subtype
-/
noncomputable def indIso [DecidableEq G] (A : Rep.{u} k S) (n : Nat) :
    groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down Nat) n).mapIso
  (inhomogeneousChainsIso (ind S.subtype A :) ≪≫
    (coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm) ≪≫
  (groupHomologyIso A n ((resFunctor.{u} S.subtype).mapProjectiveResolution <|
    barResolution k G)).symm

end groupHomology
