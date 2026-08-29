/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Inner anodyne extensions

Much of this file is mirrored from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic`.

*Inner* anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains *inner* horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, inner anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of inner fibrations.

-/

public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

/-- In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respect
to inner horn inclusions. -/
@[expose, kerodon 01BR]
/--
Definition of `innerAnodyneExtensions` / `innerAnodyneExtensions` 的定义

English:
definition innerAnodyneExtensions
  signature: : MorphismProperty SSet.{u}
  body: innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

中文:
定义 innerAnodyneExtensions
  签名: : Morphism命题erty SSet.{u}
  定义体: innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

Depends on / 依赖: innerFibrations, innerFibrations.llp
-/
def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

/--
lemma `innerAnodyneExtensions.of_isIso` / 引理 `innerAnodyneExtensions.of_isIso`

English:
lemma innerAnodyneExtensions.of_isIso
  given: {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f]
  proof: MorphismProperty.of_isIso innerAnodyneExtensions f

中文:
引理 innerAnodyneExtensions.of_isIso
  条件: {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f]
  证明: MorphismProperty.of_isIso innerAnodyneExtensions f

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isIso, innerAnodyneExtensions, of_isIso
-/
lemma innerAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    innerAnodyneExtensions f :=
  MorphismProperty.of_isIso innerAnodyneExtensions f

/--
lemma `innerAnodyneExtensions_eq_llp_rlp` / 引理 `innerAnodyneExtensions_eq_llp_rlp`

English:
lemma innerAnodyneExtensions_eq_llp_rlp
  proof: rfl

中文:
引理 innerAnodyneExtensions_eq_llp_rlp
  证明: rfl
-/
lemma innerAnodyneExtensions_eq_llp_rlp :
    innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp :=
  rfl

/--
lemma `innerAnodyneExtensions.horn_ι` / 引理 `innerAnodyneExtensions.horn_ι`

English:
lemma innerAnodyneExtensions.horn_ι
  statement: {n : Nat} {i : Fin (n + 1)}
  proof: by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

中文:
引理 innerAnodyneExtensions.horn_ι
  结论: {n : 自然数} {i : Fin (n + 1)}
  证明: by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

Depends on / 依赖: innerAnodyneExtensions_eq_llp_rlp, le_llp_rlp
-/
lemma innerAnodyneExtensions.horn_ι {n : Nat} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) :
    innerAnodyneExtensions.{u} Λ[n, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

/--
lemma `innerAnodyneExtensions_le` / 引理 `innerAnodyneExtensions_le`

English:
lemma innerAnodyneExtensions_le
  statement: innerAnodyneExtensions <= anodyneExtensions.{u}
  proof: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [innerAnodyneExtensions_eq_llp_rlp]; rw [le_llp_iff_le_rlp]; rw [rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

中文:
引理 innerAnodyneExtensions_le
  结论: innerAnodyneExtensions <= anodyneExtensions.{u}
  证明: by
  rw [anodyneExtensions_eq_llp_rlp]; rw [innerAnodyneExtensions_eq_llp_rlp]; rw [le_llp_iff_le_rlp]; rw [rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

Depends on / 依赖: anodyneExtensions_eq_llp_rlp, antitone_rlp, innerAnodyneExtensions_eq_llp_rlp, innerHornInclusions_le_J, le_llp_iff_le_rlp, rlp_llp_rlp
-/
lemma innerAnodyneExtensions_le : innerAnodyneExtensions <= anodyneExtensions.{u} := by
  rw [anodyneExtensions_eq_llp_rlp]; rw [innerAnodyneExtensions_eq_llp_rlp]; rw [le_llp_iff_le_rlp]; rw [rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsSmall.{u} innerHornInclusions.{u}
  body: by
  rw [innerHornInclusions_eq_iSup]
  have (n : Nat) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} => Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

中文:
实例 :
  签名: Morphism命题erty.IsSmall.{u} innerHornInclusions.{u}
  定义体: by
  rw [innerHornInclusions_eq_iSup]
  have (n : Nat) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} => Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

Depends on / 依赖: Fin.last, IsSmall, MorphismProperty, MorphismProperty.IsSmall, MorphismProperty.ofHoms, innerHornInclusions_eq_iSup, isSmall_iSup, isSmall_ofHoms, ofHoms
-/
instance : MorphismProperty.IsSmall.{u} innerHornInclusions.{u} := by
  rw [innerHornInclusions_eq_iSup]
  have (n : Nat) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} => Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u}
  body: by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

中文:
实例 :
  签名: IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u}
  定义体: by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

Depends on / 依赖: IsFinitelyPresentable, iSup_iff, infer_instance, innerHornInclusions_eq_iSup
-/
instance : IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSmallObjectArgument.{u} innerHornInclusions.{u}
  body: ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

中文:
实例 :
  签名: HasSmallObjectArgument.{u} innerHornInclusions.{u}
  定义体: ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

Depends on / 依赖: aleph0
-/
instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/--
lemma `innerAnodyneExtensions_eq_retracts_transfiniteCompositions` / 引理 `innerAnodyneExtensions_eq_retracts_transfiniteCompositions`

English:
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions
  proof: by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

中文:
引理 innerAnodyneExtensions_eq_retracts_transfiniteCompositions
  证明: by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

Depends on / 依赖: innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} innerHornInclusions.{u}).pushouts).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [llp_rlp_of_hasSmallObjectArgument]

/--
lemma `innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape` / 引理 `innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape`

English:
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape
  proof: by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

中文:
引理 innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape
  证明: by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

Depends on / 依赖: SmallObject, SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0, innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    innerAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} innerHornInclusions.{u}).pushouts Nat).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp]; rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/--
Definition of `strongInnerAnodyneExtensions` / `strongInnerAnodyneExtensions` 的定义

English:
definition strongInnerAnodyneExtensions
  signature: : MorphismProperty SSet.{u}
  body: fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

中文:
定义 strongInnerAnodyneExtensions
  签名: : Morphism命题erty SSet.{u}
  定义体: fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

Depends on / 依赖: IsInner, IsRegular, P.IsInner, P.IsRegular, Pairing, Subcomplex, Subcomplex.range
-/
def strongInnerAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f => Mono f ∧ exists (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

/--
lemma `strongInnerAnodyneExtensions.mono` / 引理 `strongInnerAnodyneExtensions.mono`

English:
lemma strongInnerAnodyneExtensions.mono
  statement: {X Y : SSet.{u}} {f : X ⟶ Y}
  proof: hf.1

中文:
引理 strongInnerAnodyneExtensions.mono
  结论: {X Y : SSet.{u}} {f : X ⟶ Y}
  证明: hf.1
-/
lemma strongInnerAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongInnerAnodyneExtensions f) : Mono f := hf.1

/--
lemma `strongInnerAnodyneExtensions_le_strongAnodyneExtensions` / 引理 `strongInnerAnodyneExtensions_le_strongAnodyneExtensions`

English:
lemma strongInnerAnodyneExtensions_le_strongAnodyneExtensions
  proof: fun _ _ _ ⟨_, P, _, _⟩ => ⟨inferInstance, P, inferInstance⟩

中文:
引理 strongInnerAnodyneExtensions_le_strongAnodyneExtensions
  证明: fun _ _ _ ⟨_, P, _, _⟩ => ⟨inferInstance, P, inferInstance⟩
-/
lemma strongInnerAnodyneExtensions_le_strongAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} <= strongAnodyneExtensions :=
  fun _ _ _ ⟨_, P, _, _⟩ => ⟨inferInstance, P, inferInstance⟩

/--
lemma `Subcomplex.Pairing.strongInnerAnodyneExtensions` / 引理 `Subcomplex.Pairing.strongInnerAnodyneExtensions`

English:
lemma Subcomplex.Pairing.strongInnerAnodyneExtensions
  statement: {X : SSet.{u}} {A : X.Subcomplex}
  proof: ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩

中文:
引理 Subcomplex.Pairing.strongInnerAnodyneExtensions
  结论: {X : SSet.{u}} {A : X.Subcomplex}
  证明: ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩

Depends on / 依赖: Iso.refl, Iso.refl_hom, Pairing, Pairing.ofIso, Subfunctor, Subfunctor.range_, preimage_id, refl_hom
-/
lemma Subcomplex.Pairing.strongInnerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [h₁ : P.IsRegular] [h₂ : P.IsInner] :
    strongInnerAnodyneExtensions A.ι :=
  ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩

/--
lemma `strongInnerAnodyneExtensions_ι_iff` / 引理 `strongInnerAnodyneExtensions_ι_iff`

English:
lemma strongInnerAnodyneExtensions_ι_iff
  given: {X : SSet.{u}} (A : X.Subcomplex)
  proof: ⟨fun hA => by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ => P.strong

中文:
引理 strongInnerAnodyneExtensions_ι_iff
  条件: {X : SSet.{u}} (A : X.Subcomplex)
  证明: ⟨fun hA => by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ => P.strong

Depends on / 依赖: B.Pairing, IsInner, IsRegular, P.IsInner, P.IsRegular, P.strongInnerAnodyneExtensions, Pairing, Subcomplex, X.Subcomplex, strongInnerAnodyneExtensions
-/
lemma strongInnerAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongInnerAnodyneExtensions A.ι ↔ exists (P : A.Pairing) (_ : P.IsRegular), P.IsInner :=
  ⟨fun hA => by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        exists (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ => P.strongInnerAnodyneExtensions⟩

/--
lemma `Subcomplex.Pairing.innerAnodyneExtensions` / 引理 `Subcomplex.Pairing.innerAnodyneExtensions`

English:
lemma Subcomplex.Pairing.innerAnodyneExtensions
  statement: {X : SSet.{u}} {A : X.Subcomplex}
  proof: transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, cop

中文:
引理 Subcomplex.Pairing.innerAnodyneExtensions
  结论: {X : SSet.{u}} {A : X.Subcomplex}
  证明: transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, cop

Depends on / 依赖: Fin.lt_last_iff_ne_last.mpr, Fin.pos_iff_ne_zero.mpr, IsInner, IsInner.ne_last, IsInner.ne_zero, MorphismProperty, NeZero, P.rankFunction.relativeCellComplex.attachCells, P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, attachCells, c.dim, coproducts_le_iff, lt_last_iff_ne_last, ne_last, ne_zero, pos_iff_ne_zero, pushouts_coproducts, pushouts_le_iff, rankFunction, relativeCellComplex
-/
lemma Subcomplex.Pairing.innerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsInner] :
    innerAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj => by
      refine (?_ : (_ : MorphismProperty _) <= _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have h0 := Fin.pos_iff_ne_zero.mpr (IsInner.ne_zero c.s rfl)
      have hn := Fin.lt_last_iff_ne_last.mpr (IsInner.ne_last c.s rfl)
      have : NeZero c.dim := ⟨by grind⟩
      exact .horn_ι h0 hn⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: strongInnerAnodyneExtensions.{u}.RespectsIso
  body: by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso

中文:
实例 :
  签名: strongInnerAnodyneExtensions.{u}.RespectsIso
  定义体: by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso

Depends on / 依赖: Iso.refl, P.ofIso, Subcomplex, Subcomplex.image_top, Subcomplex.preimage_inv, Subcomplex.range_comp, Subcomplex.range_eq_top, image_top, postcomp, preimage_inv, range_comp, range_eq_top
-/
instance : strongInnerAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]

/--
lemma `strongInnerAnodyneExtensions_le_innerAnodyneExtensions` / 引理 `strongInnerAnodyneExtensions_le_innerAnodyneExtensions`

English:
lemma strongInnerAnodyneExtensions_le_innerAnodyneExtensions
  proof: by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

中文:
引理 strongInnerAnodyneExtensions_le_innerAnodyneExtensions
  证明: by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

Depends on / 依赖: P.innerAnodyneExtensions, Subfunctor, Subfunctor.toRange_, comp_mem, innerAnodyneExtensions, of_isIso
-/
lemma strongInnerAnodyneExtensions_le_innerAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} <= innerAnodyneExtensions := by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

end SSet
