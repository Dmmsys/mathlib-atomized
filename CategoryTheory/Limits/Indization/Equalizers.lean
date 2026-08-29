/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Indization.ParallelPair
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Equalizers of ind-objects

We show that if a category `C` has equalizers, then ind-objects are closed under equalizers.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 6.1
-/

public section

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C)

/--
theorem `isIndObject_limit_comp_yoneda_comp_colim` / 定理 `isIndObject_limit_comp_yoneda_comp_colim`

English:
theorem isIndObject_limit_comp_yoneda_comp_colim
  proof: by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvalu

中文:
定理 isIndObject_limit_comp_yoneda_comp_colim
  证明: by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvalu

Depends on / 依赖: Functor, Functor.whiskeringRight, HasLimit, HasLimit.isoOfNatIso, IsIndObject, IsIndObject.map, colimitFlipIsoCompColim, colimitLimitIso, isIndObject_colimit, isoOfNatIso, limitObjIsoLimitCompEvaluation, whiskeringRight, yoneda
-/
theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : forall i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)

end

/--
Instance `isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair` / 实例 `isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair`

English:
instance isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair
  signature: [HasEqualizers C]
  body: .mk' (by
    rintro _ ⟨F, h⟩
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation (h WalkingParallelPair.zero)
      (h WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)
    exact IsIndObject.map
      (HasLimit.isoOfNatIso (P.parallelPairIsoPa

中文:
实例 isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair
  签名: [HasEqualizers C]
  定义体: .mk' (by
    rintro _ ⟨F, h⟩
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation (h WalkingParallelPair.zero)
      (h WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)
    exact IsIndObject.map
      (HasLimit.isoOfNatIso (P.parallelPairIsoPa

Depends on / 依赖: WalkingParallelPair
-/
instance isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair [HasEqualizers C] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C := C)) WalkingParallelPair :=
  .mk' (by
    rintro _ ⟨F, h⟩
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation (h WalkingParallelPair.zero)
      (h WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)
    exact IsIndObject.map
      (HasLimit.isoOfNatIso (P.parallelPairIsoParallelPairCompYoneda.symm ≪≫
        (diagramIsoParallelPair _).symm)).hom
      (isIndObject_limit_comp_yoneda_comp_colim (parallelPair P.φ P.ψ)
        (fun i => isIndObject_limit_comp_yoneda _)))

end CategoryTheory.Limits
