/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel

/-!
# Basic definitions for factorization lemmas

We define the class of morphisms
`degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ)`
in the category of cochain complexes in an abelian category `C`.

When restricted to the full subcategory of bounded below cochain complexes in an
abelian category `C` that has enough injectives, this is the class of
fibrations for a model category structure on the bounded below
category of cochain complexes in `C`. In this folder, we intend to prove two factorization
lemmas in the category of bounded below cochain complexes (TODO):
* CM5a: any morphism `K ⟶ L` can be factored as `K ⟶ K' ⟶ L` where `i : K ⟶ K'` is a
  trivial cofibration (a mono that is also a quasi-isomorphism) and `p : K' ⟶ L` is a fibration.
* CM5b: any morphism `K ⟶ L` can be factored as `K ⟶ L' ⟶ L` where `i : K ⟶ L'` is a
  cofibration (i.e. a mono) and `p : L' ⟶ L` is a trivial fibration (i.e. a quasi-isomorphism
  which is also a fibration)

The difficult part is CM5a (whose proof uses CM5b). These lemmas shall be essential
ingredients in the proof that the bounded below derived category of an abelian
category `C` with enough injectives identifies to the bounded below homotopy category
of complexes of injective objects in `C`. This will be used in the construction
of total derived functors (and a refactor of the sequence of derived functors).

-/

@[expose] public section


open CategoryTheory Abelian Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

/--
Definition of `degreewiseEpiWithInjectiveKernel` / `degreewiseEpiWithInjectiveKernel` 的定义

English:
definition degreewiseEpiWithInjectiveKernel
  signature: : MorphismProperty (CochainComplex C Int)
  body: fun _ _ φ => forall (i : Int), epiWithInjectiveKernel (φ.f i)

中文:
定义 degreewiseEpiWithInjectiveKernel
  签名: : MorphismProperty (上链复形 C 整数)
  定义体: fun _ _ φ => forall (i : Int), epiWithInjectiveKernel (φ.f i)

Depends on / 依赖: epiWithInjectiveKernel
-/
def degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C Int) :=
  fun _ _ φ => forall (i : Int), epiWithInjectiveKernel (φ.f i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (degreewiseEpiWithInjectiveKernel (C := C)).IsMultiplicative
  body: MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)

中文:
实例 :
  签名: (degreewiseEpiWithInjectiveKernel (C := C)).是Multiplicative
  定义体: MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)

Depends on / 依赖: IsMultiplicative
-/
instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsMultiplicative where
  id_mem _ _ := MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (degreewiseEpiWithInjectiveKernel (C := C)).IsStableUnderRetracts
  body: MorphismProperty.of_retract (r.map (HomologicalComplex.eval _ _ i)) (h i)

中文:
实例 :
  签名: (degreewiseEpiWithInjectiveKernel (C := C)).是StableUnderRetracts
  定义体: MorphismProperty.of_retract (r.map (HomologicalComplex.eval _ _ i)) (h i)

Depends on / 依赖: IsStableUnderRetracts
-/
instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract r h i :=
    MorphismProperty.of_retract (r.map (HomologicalComplex.eval _ _ i)) (h i)

/--
lemma `degreewiseEpiWithInjectiveKernel_iff_of_isZero` / 引理 `degreewiseEpiWithInjectiveKernel_iff_of_isZero`

English:
lemma degreewiseEpiWithInjectiveKernel_iff_of_isZero
  statement: {K L : CochainComplex C Int}
  proof: forall_congr' (fun n => by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact (HomologicalComplex.eval _ _ n).map_isZero hL)

中文:
引理 degreewiseEpiWithInjectiveKernel_iff_of_isZero
  结论: {K L : 上链复形 C 整数}
  证明: forall_congr' (fun n => by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact (HomologicalComplex.eval _ _ n).map_isZero hL)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, epiWithInjectiveKernel_iff_of_isZero, forall_congr, map_isZero
-/
lemma degreewiseEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C Int}
    (f : K ⟶ L) (hL : IsZero L) :
    degreewiseEpiWithInjectiveKernel f ↔ forall (n : Int), Injective (K.X n) :=
  forall_congr' (fun n => by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact (HomologicalComplex.eval _ _ n).map_isZero hL)

/--
lemma `degreewiseEpiWithInjectiveKernel.epi` / 引理 `degreewiseEpiWithInjectiveKernel.epi`

English:
lemma degreewiseEpiWithInjectiveKernel.epi
  statement: {K L : CochainComplex C Int} {f : K ⟶ L}
  proof: HomologicalComplex.epi_of_epi_f f (fun n => (h n).1)

中文:
引理 degreewiseEpiWithInjectiveKernel.epi
  结论: {K L : 上链复形 C 整数} {f : K ⟶ L}
  证明: HomologicalComplex.epi_of_epi_f f (fun n => (h n).1)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.epi_of_epi_f, epi_of_epi_f
-/
lemma degreewiseEpiWithInjectiveKernel.epi {K L : CochainComplex C Int} {f : K ⟶ L}
    (h : degreewiseEpiWithInjectiveKernel f) : Epi f :=
  HomologicalComplex.epi_of_epi_f f (fun n => (h n).1)

end CochainComplex
