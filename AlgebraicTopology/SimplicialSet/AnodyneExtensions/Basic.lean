/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Anodyne extensions

Anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of fibrations (for the Quillen model category structure:
fibrations are morphisms that have the right lifting property with respect
to horn inclusions). When the Quillen model category structure is fully
upstreamed (TODO @joelriou), it can be shown that a morphism `f` is an
anodyne extension iff `f` is a cofibration that is also a weak equivalence.

We also introduce the class of strong anodyne extensions that could be defined
as a closure similarly as anodyne extensions, but without taking the closure
under retracts. Sean Moss has given a combinatorial description of these
strong anodyne extensions: the inclusion `A.ι : A ⟶ X` of a subcomplex `A`
of a simplicial set `X` is a strong anodyne extension iff there exists
a regular pairing for `A`. In this file, we define strong anodyne extensions
in terms of such regular pairings, and using the main result of the file
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/RelativeCellComplex.lean`
we show that a strong anodyne extension is an anodyne extension.

## TODO
* introduce inner variants of these definitions
* show that strong anodyne extensions are indeed stable under coproducts,
  transfinite compositions and pushouts (the proof should reduce to the
  construction of pairings)
* study the interaction between anodyne extension and binary products:
  the critical case consists in showing that inclusions
  `Λ[m, i] ⊗ Δ[n] ∪ Δ[m] ⊗ ∂Δ[n] ⟶ Δ[m] ⊗ Δ[n]` are strong anodyne extensions (@joelriou)
* show that anodyne extensions are stable under the subdivision functor (@joelriou)

## References
* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, IV.2][gabriel-zisman-1967]
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

open modelCategoryQuillen in
/--
Definition of `anodyneExtensions` / `anodyneExtensions` 的定义

English:
definition anodyneExtensions
  signature: : MorphismProperty SSet.{u}
  body: (fibrations _).llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

中文:
定义 anodyneExtensions
  签名: : Morphism命题erty SSet.{u}
  定义体: (fibrations _).llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

Depends on / 依赖: fibrations
-/
def anodyneExtensions : MorphismProperty SSet.{u} := (fibrations _).llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

/--
lemma `anodyneExtensions.of_isIso` / 引理 `anodyneExtensions.of_isIso`

English:
lemma anodyneExtensions.of_isIso
  given: {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f]
  proof: MorphismProperty.of_isIso anodyneExtensions f

中文:
引理 anodyneExtensions.of_isIso
  条件: {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f]
  证明: MorphismProperty.of_isIso anodyneExtensions f

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isIso, anodyneExtensions, of_isIso
-/
lemma anodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso anodyneExtensions f

/--
lemma `anodyneExtensions_eq_llp_rlp` / 引理 `anodyneExtensions_eq_llp_rlp`

English:
lemma anodyneExtensions_eq_llp_rlp
  proof: rfl

中文:
引理 anodyneExtensions_eq_llp_rlp
  证明: rfl
-/
lemma anodyneExtensions_eq_llp_rlp :
    anodyneExtensions.{u} = modelCategoryQuillen.J.rlp.llp :=
  rfl

/--
lemma `anodyneExtensions.horn_ι` / 引理 `anodyneExtensions.horn_ι`

English:
lemma anodyneExtensions.horn_ι
  given: {n : Nat} [NeZero n] (i : Fin (n + 1))
  proof: by
  rw [anodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (modelCategoryQuillen.horn_ι_mem_J n i)

中文:
引理 anodyneExtensions.horn_ι
  条件: {n : 自然数} [NeZero n] (i : Fin (n + 1))
  证明: by
  rw [anodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (modelCategoryQuillen.horn_ι_mem_J n i)

Depends on / 依赖: anodyneExtensions_eq_llp_rlp, le_llp_rlp, modelCategoryQuillen, modelCategoryQuillen.horn_
-/
lemma anodyneExtensions.horn_ι {n : Nat} [NeZero n] (i : Fin (n + 1)) :
    anodyneExtensions.{u} Λ[n, i].ι := by
  rw [anodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (modelCategoryQuillen.horn_ι_mem_J n i)

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance (n : Nat) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u} (fun (i : Fin (n + 2)) => Λ[n + 1, i].ι)) :=
  isSmall_ofHoms ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsSmall.{u} modelCategoryQuillen.J.{u}
  body: isSmall_iSup ..

中文:
实例 :
  签名: Morphism命题erty.IsSmall.{u} modelCategoryQuillen.J.{u}
  定义体: isSmall_iSup ..

Depends on / 依赖: isSmall_iSup
-/
instance : MorphismProperty.IsSmall.{u} modelCategoryQuillen.J.{u} :=
  isSmall_iSup ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalForSmallObjectArgument modelCategoryQuillen.J.{u} Cardinal.aleph0.{u}
  body: by
    have : IsFinitelyPresentable.{u} A := by
      simp only [modelCategoryQuillen.J, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

中文:
实例 :
  签名: IsCardinalForSmallObjectArgument modelCategoryQuillen.J.{u} Cardinal.aleph0.{u}
  定义体: by
    have : IsFinitelyPresentable.{u} A := by
      simp only [modelCategoryQuillen.J, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

Depends on / 依赖: IsFinitelyPresentable, iSup_iff, infer_instance, modelCategoryQuillen, modelCategoryQuillen.J
-/
instance : IsCardinalForSmallObjectArgument modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [modelCategoryQuillen.J, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSmallObjectArgument.{u} modelCategoryQuillen.J.{u}
  body: ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

中文:
实例 :
  签名: HasSmallObjectArgument.{u} modelCategoryQuillen.J.{u}
  定义体: ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

Depends on / 依赖: aleph0
-/
instance : HasSmallObjectArgument.{u} modelCategoryQuillen.J.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/--
lemma `anodyneExtensions_eq_retracts_transfiniteCompositions` / 引理 `anodyneExtensions_eq_retracts_transfiniteCompositions`

English:
lemma anodyneExtensions_eq_retracts_transfiniteCompositions
  proof: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

中文:
引理 anodyneExtensions_eq_retracts_transfiniteCompositions
  证明: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

Depends on / 依赖: anodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument
-/
lemma anodyneExtensions_eq_retracts_transfiniteCompositions :
    anodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts).retracts := by
  rw [anodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

/--
lemma `anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape` / 引理 `anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape`

English:
lemma anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape
  proof: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

中文:
引理 anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape
  证明: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

Depends on / 依赖: SmallObject, SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0, anodyneExtensions_eq_llp_rlp, llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
-/
lemma anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    anodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts Nat).retracts := by
  rw [anodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/--
Definition of `strongAnodyneExtensions` / `strongAnodyneExtensions` 的定义

English:
definition strongAnodyneExtensions
  signature: : MorphismProperty SSet.{u}
  body: fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing), P.IsRegular

中文:
定义 strongAnodyneExtensions
  签名: : Morphism命题erty SSet.{u}
  定义体: fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing), P.IsRegular

Depends on / 依赖: IsRegular, P.IsRegular, Pairing, Subcomplex, Subcomplex.range
-/
def strongAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing), P.IsRegular

/--
lemma `strongAnodyneExtensions.mono` / 引理 `strongAnodyneExtensions.mono`

English:
lemma strongAnodyneExtensions.mono
  statement: {X Y : SSet.{u}} {f : X ⟶ Y}
  proof: hf.1

中文:
引理 strongAnodyneExtensions.mono
  结论: {X Y : SSet.{u}} {f : X ⟶ Y}
  证明: hf.1
-/
lemma strongAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongAnodyneExtensions f) : Mono f := hf.1

/--
lemma `Subcomplex.Pairing.strongAnodyneExtensions` / 引理 `Subcomplex.Pairing.strongAnodyneExtensions`

English:
lemma Subcomplex.Pairing.strongAnodyneExtensions
  statement: {X : SSet.{u}} {A : X.Subcomplex}
  proof: ⟨inferInstance, by
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩

中文:
引理 Subcomplex.Pairing.strongAnodyneExtensions
  结论: {X : SSet.{u}} {A : X.Subcomplex}
  证明: ⟨inferInstance, by
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩

Depends on / 依赖: Subcomplex, Subcomplex.range, generalize, h.symm
-/
lemma Subcomplex.Pairing.strongAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    strongAnodyneExtensions A.ι :=
  ⟨inferInstance, by
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩

/--
lemma `strongAnodyneExtensions_ι_iff` / 引理 `strongAnodyneExtensions_ι_iff`

English:
lemma strongAnodyneExtensions_ι_iff
  given: {X : SSet.{u}} (A : X.Subcomplex)
  proof: ⟨fun hA => by
    obtain ⟨_, P, _, rfl⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing), P.IsRegular ∧ B = A := by
      obtain ⟨_, P, _⟩ := hA
      exact ⟨_, P, inferInstance, by simp⟩
    exact ⟨P, inferInstance⟩,
  fun ⟨P, _⟩ => P.strongAnodyneExtensions⟩

中文:
引理 strongAnodyneExtensions_ι_iff
  条件: {X : SSet.{u}} (A : X.Subcomplex)
  证明: ⟨fun hA => by
    obtain ⟨_, P, _, rfl⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing), P.IsRegular ∧ B = A := by
      obtain ⟨_, P, _⟩ := hA
      exact ⟨_, P, inferInstance, by simp⟩
    exact ⟨P, inferInstance⟩,
  fun ⟨P, _⟩ => P.strongAnodyneExtensions⟩

Depends on / 依赖: B.Pairing, IsRegular, P.IsRegular, P.strongAnodyneExtensions, Pairing, Subcomplex, X.Subcomplex, strongAnodyneExtensions
-/
lemma strongAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongAnodyneExtensions A.ι ↔ exists (P : A.Pairing), P.IsRegular :=
  ⟨fun hA => by
    obtain ⟨_, P, _, rfl⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing), P.IsRegular ∧ B = A := by
      obtain ⟨_, P, _⟩ := hA
      exact ⟨_, P, inferInstance, by simp⟩
    exact ⟨P, inferInstance⟩,
  fun ⟨P, _⟩ => P.strongAnodyneExtensions⟩

/--
lemma `Subcomplex.Pairing.anodyneExtensions` / 引理 `Subcomplex.Pairing.anodyneExtensions`

English:
lemma Subcomplex.Pairing.anodyneExtensions
  statement: {X : SSet.{u}} {A : X.Subcomplex}
  proof: transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, cop

中文:
引理 Subcomplex.Pairing.anodyneExtensions
  结论: {X : SSet.{u}} {A : X.Subcomplex}
  证明: transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, cop

Depends on / 依赖: MorphismProperty, P.rankFunction.relativeCellComplex.attachCells, P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, attachCells, c.index, coproducts_le_iff, pushouts_coproducts, pushouts_le_iff, rankFunction, relativeCellComplex, toTransfiniteCompositionOfShape, transfiniteCompositionsOfShape_le
-/
lemma Subcomplex.Pairing.anodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    anodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact .horn_ι c.index⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: strongAnodyneExtensions.{u}.RespectsIso
  body: by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e,
      Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferI

中文:
实例 :
  签名: strongAnodyneExtensions.{u}.RespectsIso
  定义体: by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e,
      Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferI

Depends on / 依赖: Iso.refl, P.ofIso, Subcomplex, Subcomplex.image_top, Subcomplex.preimage_inv, Subcomplex.range_comp, Subcomplex.range_eq_top, image_top, postcomp, preimage_inv, range_comp, range_eq_top
-/
instance : strongAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e,
      Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]

/--
lemma `strongAnodyneExtensions_le_anodyneExtensions` / 引理 `strongAnodyneExtensions_le_anodyneExtensions`

English:
lemma strongAnodyneExtensions_le_anodyneExtensions
  proof: by
  rintro X Y f ⟨_, P, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.anodyneExtensions

中文:
引理 strongAnodyneExtensions_le_anodyneExtensions
  证明: by
  rintro X Y f ⟨_, P, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.anodyneExtensions

Depends on / 依赖: P.anodyneExtensions, Subfunctor, Subfunctor.toRange_, anodyneExtensions, comp_mem, of_isIso
-/
lemma strongAnodyneExtensions_le_anodyneExtensions :
    strongAnodyneExtensions.{u} <= anodyneExtensions := by
  rintro X Y f ⟨_, P, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.anodyneExtensions

end SSet
