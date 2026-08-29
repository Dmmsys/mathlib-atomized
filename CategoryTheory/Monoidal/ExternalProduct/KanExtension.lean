/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Preservation of pointwise left Kan extensions by external products

We prove that if a functor `H' : D' ⥤ V` is a pointwise left Kan extension of
`H : D ⥤ V` along `L : D ⥤ D'`, and if `K : E ⥤ V` is any functor such that
for any `e : E`, the functor `tensorRight (K.obj e)` commutes with colimits of
shape `CostructuredArrow L d`, then the functor `H' ⊠ K` is a pointwise left Kan extension
of `H ⊠ K` along `L.prod (𝟭 E)`.

We also prove a similar criterion to establish that `K ⊠ H'` is a pointwise left Kan
extension of `K ⊠ H` along `(𝟭 E).prod L`.
-/

@[expose] public section
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.MonoidalCategory.ExternalProduct

noncomputable section
open scoped CategoryTheory.Prod

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
  {D : Type u₂} {D' : Type u₃} {E : Type u₄}
  [Category.{v₂} D] [Category.{v₃} D'] [Category.{v₄} E]
  {H : D ⥤ V} {L : D ⥤ D'} (H' : D' ⥤ V) (α : H ⟶ L ⋙ H') (K : E ⥤ V)

/--
Definition of `extensionUnitLeft` / `extensionUnitLeft` 的定义

English:
abbreviation extensionUnitLeft
  signature: : H ⊠ K ⟶ L.prod (𝟭 E) ⋙ H' ⊠ K
  body: (externalProductBifunctor D E V).map (α ×ₘ K.leftUnitor.inv)

中文:
缩写 extensionUnitLeft
  签名: : H ⊠ K ⟶ L.乘积 (𝟭 E) ⋙ H' ⊠ K
  定义体: (externalProductBifunctor D E V).map (α ×ₘ K.leftUnitor.inv)

Depends on / 依赖: E.sieve, K.leftUnitor.inv, Sieve.pullback_id, cat_disch, condition, externalProductBifunctor, leftUnitor, pullback, pullback.condition, pullback_id
-/
abbrev extensionUnitLeft : H ⊠ K ⟶ L.prod (𝟭 E) ⋙ H' ⊠ K :=
    (externalProductBifunctor D E V).map (α ×ₘ K.leftUnitor.inv)

/--
Definition of `extensionUnitRight` / `extensionUnitRight` 的定义

English:
abbreviation extensionUnitRight
  signature: : K ⊠ H ⟶ (𝟭 E).prod L ⋙ K ⊠ H'
  body: (externalProductBifunctor E D V).map (K.leftUnitor.inv ×ₘ α)

中文:
缩写 extensionUnitRight
  签名: : K ⊠ H ⟶ (𝟭 E).乘积 L ⋙ K ⊠ H'
  定义体: (externalProductBifunctor E D V).map (K.leftUnitor.inv ×ₘ α)

Depends on / 依赖: K.leftUnitor.inv, externalProductBifunctor, leftUnitor
-/
abbrev extensionUnitRight : K ⊠ H ⟶ (𝟭 E).prod L ⋙ K ⊠ H' :=
    (externalProductBifunctor E D V).map (K.leftUnitor.inv ×ₘ α)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseLeftKanExtensionAtExtensionUnitLeft` / `isPointwiseLeftKanExtensionAtExtensionUnitLeft` 的定义

English:
definition isPointwiseLeftKanExtensionAtExtensionUnitLeft
  body: by
.coconeAt (d, e) set cone := Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence L (𝟭 E) d e
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ (CostructuredArrow L d) × CostructuredArrow (𝟭 E) e :=
 

中文:
定义 isPointwiseLeftKanExtensionAtExtensionUnitLeft
  定义体: by
.coconeAt (d, e) set cone := Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence L (𝟭 E) d e
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ (CostructuredArrow L d) × CostructuredArrow (𝟭 E) e :=
 

Depends on / 依赖: CostructuredArrow, CostructuredArrow.prodEquivalence, Functor, Functor.LeftExtension.mk, IsColimit, LeftExtension, Limits, Limits.IsColimit.ofWhiskerEquivalence, coconeAt, extensionUnitLeft, ofWhiskerEquivalence, prodEquivalence
-/
def isPointwiseLeftKanExtensionAtExtensionUnitLeft
    (d : D') (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtensionAt d) (e : E)
    [Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorRight <| K.obj e)] :
.IsPointwiseLeftKanExtensionAt Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
      (d, e) := by
.coconeAt (d, e) set cone := Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence L (𝟭 E) d e
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ (CostructuredArrow L d) × CostructuredArrow (𝟭 E) e :=
    -- this definition makes it easier to prove finality of I
    (prod.rightUnitorEquivalence (CostructuredArrow L d)).inverse ⋙
      (𝟭 _).prod (Functor.fromPUnit.{0} <| .mk <| 𝟙 _)
  letI : I.Final := by
.Final := let : Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e)
Functor.final_fromPUnit_of_isTerminal CostructuredArrow.mkIdTerminal (S := 𝟭 E) (Y := e)
apply Iff.mp Functor.final_iff_final_comp
      (F := (prod.rightUnitorEquivalence <| CostructuredArrow L d).inverse)
      (G := (𝟭 _).prod <| Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e))
    infer_instance
.toFun apply Functor.Final.isColimitWhiskerEquiv I (Limits.Cocone.whisker equiv.functor cone)
  -- through all the equivalences above, the new cocone we consider is in fact
  -- `tensorRight (K.obj e)|>.mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d`
  let diag_iso :
      (CostructuredArrow.proj L d ⋙ H) ⋙ tensorRight (K.obj e) ≅
      I ⋙ equiv.functor ⋙ CostructuredArrow.proj (L.prod <| 𝟭 E) (d, e) ⋙ H ⊠ K :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  apply Limits.IsColimit.equivOfNatIsoOfIso diag_iso
    (d := Limits.Cocone.whisker I (Limits.Cocone.whisker equiv.functor cone))
    (c := tensorRight (K.obj e) |>.mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d)
.toFun (Limits.Cocone.ext <| .refl _)
.some exact Limits.PreservesColimit.preserves (F := tensorRight <| K.obj e) P

/--
Definition of `isPointwiseLeftKanExtensionExtensionUnitLeft` / `isPointwiseLeftKanExtensionExtensionUnitLeft` 的定义

English:
definition isPointwiseLeftKanExtensionExtensionUnitLeft
  body: Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
  fun ⟨d, e⟩ => isPointwiseLeftKanExtensionAtExtensionUnitLeft H' α K d (P d) e

中文:
定义 isPointwiseLeftKanExtensionExtensionUnitLeft
  定义体: Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
  fun ⟨d, e⟩ => isPointwiseLeftKanExtensionAtExtensionUnitLeft H' α K d (P d) e

Depends on / 依赖: Functor, Functor.LeftExtension.mk, LeftExtension, extensionUnitLeft
-/
def isPointwiseLeftKanExtensionExtensionUnitLeft
    [forall d : D', forall e : E,
      Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorRight <| K.obj e)]
    (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtension) :
.IsPointwiseLeftKanExtension := Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K)
  fun ⟨d, e⟩ => isPointwiseLeftKanExtensionAtExtensionUnitLeft H' α K d (P d) e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseLeftKanExtensionAtExtensionUnitRight` / `isPointwiseLeftKanExtensionAtExtensionUnitRight` 的定义

English:
definition isPointwiseLeftKanExtensionAtExtensionUnitRight
  body: by
  set cone := Functor.LeftExtension.mk (K ⊠ H')
.coconeAt (e, d) (extensionUnitRight H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence (𝟭 E) L e d
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ CostructuredArrow (𝟭 E) e × CostructuredArrow L d :=


中文:
定义 isPointwiseLeftKanExtensionAtExtensionUnitRight
  定义体: by
  set cone := Functor.LeftExtension.mk (K ⊠ H')
.coconeAt (e, d) (extensionUnitRight H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence (𝟭 E) L e d
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ CostructuredArrow (𝟭 E) e × CostructuredArrow L d :=


Depends on / 依赖: CostructuredArrow, CostructuredArrow.prodEquivalence, Functor, Functor.LeftExtension.mk, IsColimit, LeftExtension, Limits, Limits.IsColimit.ofWhiskerEquivalence, coconeAt, extensionUnitRight, ofWhiskerEquivalence, prodEquivalence
-/
def isPointwiseLeftKanExtensionAtExtensionUnitRight
    (d : D') (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtensionAt d) (e : E)
    [Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorLeft <| K.obj e)] :
    (Functor.LeftExtension.mk (K ⊠ H')
      (extensionUnitRight H' α K)).IsPointwiseLeftKanExtensionAt (e, d) := by
  set cone := Functor.LeftExtension.mk (K ⊠ H')
.coconeAt (e, d) (extensionUnitRight H' α K)
.symm let equiv := CostructuredArrow.prodEquivalence (𝟭 E) L e d
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ CostructuredArrow (𝟭 E) e × CostructuredArrow L d :=
    -- this definition makes it easier to prove finality of I
    (prod.leftUnitorEquivalence <| CostructuredArrow L d).inverse ⋙
      (Functor.fromPUnit.{0} <| .mk <| 𝟙 _).prod (𝟭 _)
  letI : I.Final := by
.Final := let : Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e)
Functor.final_fromPUnit_of_isTerminal CostructuredArrow.mkIdTerminal (S := 𝟭 E) (Y := e)
apply Iff.mp Functor.final_iff_final_comp
      (F := (prod.leftUnitorEquivalence <| CostructuredArrow L d).inverse)
      (G := Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e) |>.prod <| 𝟭 _)
    infer_instance
.toFun apply Functor.Final.isColimitWhiskerEquiv I (Limits.Cocone.whisker equiv.functor cone)
  -- through all the equivalences above, the new cocone we consider is in fact
  -- `(tensorLeft <| K.obj e).mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d`
  let diag_iso :
      (CostructuredArrow.proj L d ⋙ H) ⋙ tensorLeft (K.obj e) ≅
      I ⋙ equiv.functor ⋙ CostructuredArrow.proj (𝟭 E |>.prod L) (e, d) ⋙ K ⊠ H :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  apply Limits.IsColimit.equivOfNatIsoOfIso diag_iso
    (d := Limits.Cocone.whisker I <| Limits.Cocone.whisker equiv.functor cone)
    (c := (tensorLeft <| K.obj e).mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d)
.toFun (Limits.Cocone.ext <| .refl _)
.some exact Limits.PreservesColimit.preserves (F := tensorLeft <| K.obj e) P

/--
Definition of `isPointwiseLeftKanExtensionExtensionUnitRight` / `isPointwiseLeftKanExtensionExtensionUnitRight` 的定义

English:
definition isPointwiseLeftKanExtensionExtensionUnitRight
  body: Functor.LeftExtension.mk (K ⊠ H') (extensionUnitRight H' α K)
  fun ⟨e, d⟩ => isPointwiseLeftKanExtensionAtExtensionUnitRight H' α K d (P d) e

中文:
定义 isPointwiseLeftKanExtensionExtensionUnitRight
  定义体: Functor.LeftExtension.mk (K ⊠ H') (extensionUnitRight H' α K)
  fun ⟨e, d⟩ => isPointwiseLeftKanExtensionAtExtensionUnitRight H' α K d (P d) e

Depends on / 依赖: Functor, Functor.LeftExtension.mk, LeftExtension, extensionUnitRight
-/
def isPointwiseLeftKanExtensionExtensionUnitRight
    [forall d : D', forall e : E,
      Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorLeft <| K.obj e)]
    (P : Functor.LeftExtension.mk H' α |>.IsPointwiseLeftKanExtension) :
.IsPointwiseLeftKanExtension := Functor.LeftExtension.mk (K ⊠ H') (extensionUnitRight H' α K)
  fun ⟨e, d⟩ => isPointwiseLeftKanExtensionAtExtensionUnitRight H' α K d (P d) e

end

end CategoryTheory.MonoidalCategory.ExternalProduct
