/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# (Co)limits in over categories

We show that if `P` is a morphism property in `Scheme` that is local at the source, then
colimits in `P.Over ⊤ X` for `X : Scheme` of locally directed diagrams of open immersions
exist and agree with the colimit in `Scheme`.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (P : MorphismProperty Scheme.{u})

section Over

variable {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ Over S)
  [forall {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: have {i j} (f : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map f) :=
inferInstanceAs IsOpenImmersion (F.map f).left
  have : ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := ‹_›
  hasColimit_of_created _ (Over.forget S)

中文:
实例 :
  签名: 有余极限 F
  定义体: have {i j} (f : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map f) :=
inferInstanceAs IsOpenImmersion (F.map f).left
  have : ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := ‹_›
  hasColimit_of_created _ (Over.forget S)

Depends on / 依赖: F.map, IsLocallyDirected, IsOpenImmersion, Over.forget, Scheme, Scheme.forget, SimplicialObject, SimplicialObject.Truncated.sk.full, Truncated, forget, hasColimit_of_created
-/
noncomputable instance : HasColimit F :=
  have {i j} (f : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map f) :=
inferInstanceAs IsOpenImmersion (F.map f).left
  have : ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := ‹_›
  hasColimit_of_created _ (Over.forget S)

end Over

section OverProp

instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] (i : WalkingPair) :
    Mono ((span f g ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).map
      (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using! f.left.isOpenEmbedding.injective
  · simpa using! g.left.isOpenEmbedding.injective

instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    {i j : WalkingSpan} (t : i ⟶ j) :
      IsOpenImmersion ((span f g).map t).left := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

variable [IsZariskiLocalAtSource P] {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ P.Over ⊤ S)
  [forall {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

local instance :
    (((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) ⋙
      Scheme.forget).IsLocallyDirected :=
  ‹_›

local instance {i j} (f : i ⟶ j) :
IsOpenImmersion
      ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S).map f :=
inferInstanceAs IsOpenImmersion (F.map f).left

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimit F (MorphismProperty.Over.forget P ⊤ S)
  body: by
  have : HasColimit (F ⋙ MorphismProperty.Over.forget P ⊤ S) :=
    hasColimit_of_created _ (Over.forget S)
  refine createsColimitOfFullyFaithfulOfIso
      { toComma := colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)
        prop := ?_ } (Iso.refl _)
  let e : (colimit (F ⋙ MorphismProperty.Ov

中文:
实例 :
  签名: 创造余极限 F (MorphismProperty.Over.forget P ⊤ S)
  定义体: by
  have : HasColimit (F ⋙ MorphismProperty.Over.forget P ⊤ S) :=
    hasColimit_of_created _ (Over.forget S)
  refine createsColimitOfFullyFaithfulOfIso
      { toComma := colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)
        prop := ?_ } (Iso.refl _)
  let e : (colimit (F ⋙ MorphismProperty.Ov

Depends on / 依赖: HasColimit, IsLoca, Iso.refl, MorphismProperty, MorphismProperty.Over.forget, OpenCover, Over.forget, Scheme, Scheme.IsLoca, SimplicialObject, SimplicialObject.Truncated.sk.faithful, Truncated, colimit, createsColimitOfFullyFaithfulOfIso, faithful, forget, hasColimit_of_created, left.OpenCover, preservesColimitIso, toComma
-/
noncomputable instance : CreatesColimit F (MorphismProperty.Over.forget P ⊤ S) := by
  have : HasColimit (F ⋙ MorphismProperty.Over.forget P ⊤ S) :=
    hasColimit_of_created _ (Over.forget S)
  refine createsColimitOfFullyFaithfulOfIso
      { toComma := colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)
        prop := ?_ } (Iso.refl _)
  let e : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left ≅
      colimit ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) :=
    preservesColimitIso (Over.forget S) _
  let 𝒰 : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left.OpenCover :=
    (Scheme.IsLocallyDirected.openCover _).pushforwardIso e.inv
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) 𝒰]
  intro i
  simpa [𝒰, e] using! (F.obj i).prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: hasColimit_of_created _ (MorphismProperty.Over.forget P ⊤ S)

中文:
实例 :
  签名: 有余极限 F
  定义体: hasColimit_of_created _ (MorphismProperty.Over.forget P ⊤ S)

Depends on / 依赖: MorphismProperty, MorphismProperty.Over.forget, SimplicialObject, SimplicialObject.Truncated.skAdj.coreflective, Truncated, coreflective, forget, hasColimit_of_created
-/
instance : HasColimit F := hasColimit_of_created _ (MorphismProperty.Over.forget P ⊤ S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F (MorphismProperty.Over.forget P ⊤ S)
  body: -- this is only `inferInstance` with the local instances above
  inferInstance

中文:
实例 :
  签名: 保持余极限 F (MorphismProperty.Over.forget P ⊤ S)
  定义体: -- this is only `inferInstance` with the local instances above
  inferInstance
-/
instance : PreservesColimit F (MorphismProperty.Over.forget P ⊤ S) :=
  -- this is only `inferInstance` with the local instances above
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance (j : J) : IsOpenImmersion (colimit.ι F j).left := by
  rw [← MorphismProperty.Over.forget_comp_forget_map]
  let e : (colimit F).left ≅ colimit (F ⋙ _) :=
    preservesColimitIso (MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S) F
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _ e.hom]
  simp only [e, CategoryTheory.ι_preservesColimitIso_hom]
exact inferInstanceAs IsOpenImmersion
    (colimit.ι ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) j)

instance {ι : Type*} [Small.{u} ι] : HasCoproductsOfShape ι (P.Over ⊤ S) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteCoproducts (P.Over ⊤ S)
  body: inferInstance

中文:
实例 :
  签名: 有FiniteCoproducts (P.Over ⊤ S)
  定义体: inferInstance
-/
instance : HasFiniteCoproducts (P.Over ⊤ S) where
  out := inferInstance

noncomputable instance (J : Type*) [Small.{u} J] :
    CreatesColimitsOfShape (Discrete J) (MorphismProperty.Over.forget P ⊤ S) where

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

/--
Instance `IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete` / 实例 `IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete`

English:
instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
  signature: {ι : Type*} [Small.{u} ι]
  body: CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ => coproductIsCoproduct' _)
    (fun _ _ _ _ h => IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)) _

中文:
实例 IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
  签名: {ι : 类型} [Small.{u} ι]
  定义体: CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ => coproductIsCoproduct' _)
    (fun _ _ _ _ h => IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)) _

Depends on / 依赖: Discrete, IsClosedUnderColimitsOfShape
-/
instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete {ι : Type*} [Small.{u} ι]
    {C : Type*} [Category* C] [HasColimitsOfShape (Discrete ι) C] (L : C ⥤ Scheme.{u})
    [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) :=
  CostructuredArrow.isClosedUnderColimitsOfShape _ (fun _ => coproductIsCoproduct' _)
    (fun _ _ _ _ h => IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)) _

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S)
  body: by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

中文:
实例 :
  签名: 有FiniteCoproducts (P.CostructuredArrow ⊤ 概形.Spec S)
  定义体: by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

Depends on / 依赖: Discrete, IsClosedUnderColimitsOfShape, IsZariskiLocalAtSource, IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete, MorphismProperty, MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape, MorphismProperty.commaObj, Scheme, Scheme.Spec, commaObj, fromPUnit, hasColimitsOfShape_of_closedUnderColimitsOfShape, isClosedUnderColimitsOfShape_discrete
-/
instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

end OverProp

end AlgebraicGeometry
