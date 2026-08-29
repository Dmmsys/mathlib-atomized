/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Pairwise
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
  with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → Opens X` provides a functor `diagram U : overlap ι ⥤ (Opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `isup U`,
and in fact this is a limit cone.

A presheaf `F : Presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `isLimit (F.mapCone (cone U))`, or
* `preservesLimit (diagram U) F`

We show that this sheaf condition is equivalent to the `OpensLeCover` sheaf condition, and
thereby also equivalent to the default sheaf condition.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid

noncomputable section

universe w

open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] {X : TopCat.{w}}

namespace TopCat.Presheaf

section

/--
Definition of `IsSheafPairwiseIntersections` / `IsSheafPairwiseIntersections` 的定义

English:
definition IsSheafPairwiseIntersections
  signature: (F : Presheaf C X)
  body: forall ⦃ι : Type w⦄ (U : ι -> Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

中文:
定义 IsSheafPairwise整数ersections
  签名: (F : 预层 C X)
  定义体: forall ⦃ι : Type w⦄ (U : ι -> Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

Depends on / 依赖: F.mapCone, IsLimit, Nonempty, Pairwise, Pairwise.cocone, cocone, mapCone
-/
def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  forall ⦃ι : Type w⦄ (U : ι -> Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

/--
Definition of `IsSheafPreservesLimitPairwiseIntersections` / `IsSheafPreservesLimitPairwiseIntersections` 的定义

English:
definition IsSheafPreservesLimitPairwiseIntersections
  signature: (F : Presheaf C X)
  body: forall ⦃ι : Type w⦄ (U : ι -> Opens X), PreservesLimit (Pairwise.diagram U).op F

中文:
定义 IsSheafPreservesLimitPairwise整数ersections
  签名: (F : 预层 C X)
  定义体: forall ⦃ι : Type w⦄ (U : ι -> Opens X), PreservesLimit (Pairwise.diagram U).op F

Depends on / 依赖: Pairwise, Pairwise.diagram, PreservesLimit, diagram
-/
def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  forall ⦃ι : Type w⦄ (U : ι -> Opens X), PreservesLimit (Pairwise.diagram U).op F

end

namespace SheafCondition

variable {ι : Type*} (U : ι -> Opens X)

open CategoryTheory.Pairwise

/-- Implementation detail:
the object level of `pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U`
-/
@[simp]
/--
Definition of `pairwiseToOpensLeCoverObj` / `pairwiseToOpensLeCoverObj` 的定义

English:
definition pairwiseToOpensLeCoverObj
  signature: : Pairwise ι -> OpensLeCover U

中文:
定义 pairwiseToOpensLeCoverObj
  签名: : 两两 ι -> OpensLeCover U
-/
def pairwiseToOpensLeCoverObj : Pairwise ι -> OpensLeCover U
  | single i => ⟨U i, ⟨i, le_rfl⟩⟩
  | Pairwise.pair i j => ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

open CategoryTheory.Pairwise.Hom

/--
Definition of `pairwiseToOpensLeCoverMap` / `pairwiseToOpensLeCoverMap` 的定义

English:
definition pairwiseToOpensLeCoverMap
  signature: :

中文:
定义 pairwiseToOpensLeCoverMap
  签名: :
-/
def pairwiseToOpensLeCoverMap :
    forall {V W : Pairwise ι}, (V ⟶ W) -> (pairwiseToOpensLeCoverObj U V ⟶ pairwiseToOpensLeCoverObj U W)
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => ObjectProperty.homMk (homOfLE inf_le_left)
  | _, _, right _ _ => ObjectProperty.homMk (homOfLE inf_le_right)

/-- The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
/--
Definition of `pairwiseToOpensLeCover` / `pairwiseToOpensLeCover` 的定义

English:
definition pairwiseToOpensLeCover
  signature: : Pairwise ι ⥤ OpensLeCover U where
  body: pairwiseToOpensLeCoverObj U
  map {_ _} i := pairwiseToOpensLeCoverMap U i

中文:
定义 pairwiseToOpensLeCover
  签名: : 两两 ι ⥤ OpensLeCover U where
  定义体: pairwiseToOpensLeCoverObj U
  map {_ _} i := pairwiseToOpensLeCoverMap U i

Depends on / 依赖: pairwiseToOpensLeCoverObj
-/
def pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U where
  obj := pairwiseToOpensLeCoverObj U
  map {_ _} i := pairwiseToOpensLeCoverMap U i

instance (V : OpensLeCover U) : Nonempty (StructuredArrow V (pairwiseToOpensLeCover U)) :=
  ⟨StructuredArrow.mk (Y := single V.index) (ObjectProperty.homMk V.homToIndex)⟩

-- This is a case bash: for each pair of types of objects in `Pairwise ι`,
-- we have to explicitly construct a zigzag.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Final (pairwiseToOpensLeCover U)
  body: ⟨fun V =>
    isConnected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
              right := pair i i'
              hom := ObjectProperty.homMk (homOfLE
                (by simpa using le_

中文:
实例 :
  签名: 函子.终 (pairwiseToOpensLeCover U)
  定义体: ⟨fun V =>
    isConnected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
              right := pair i i'
              hom := ObjectProperty.homMk (homOfLE
                (by simpa using le_

Depends on / 依赖: IsChain, List.IsChain.cons_cons, List.IsChain.singleton, ObjectProperty, ObjectProperty.homMk, Or.inl, Or.inr, a.hom.le, b.hom.le, cons_cons, homOfLE, isConnected_of_zigzag, le_inf, singleton
-/
instance : Functor.Final (pairwiseToOpensLeCover U) :=
  ⟨fun V =>
    isConnected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
              right := pair i i'
              hom := ObjectProperty.homMk (homOfLE
                (by simpa using le_inf a.hom.le b.hom.le)) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inr
              ⟨{ left := 𝟙 _
                  right := left i i' }⟩)
            (List.IsChain.cons_cons
              (Or.inl
                ⟨{ left := 𝟙 _
                    right := right i i' }⟩)
              (List.IsChain.singleton _))
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
                right := pair i' i
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf (b.hom.le.trans (by simp)) a.hom.le)) },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := ObjectProperty.homMk (homOfLE (b.hom.le.trans (by simp))) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inr
              ⟨{ left := 𝟙 _
                  right := right i' i }⟩)
            (List.IsChain.cons_cons
              (Or.inl
                ⟨{ left := 𝟙 _
                    right := left i' i }⟩)
              (List.IsChain.cons_cons
                (Or.inr
                  ⟨{ left := 𝟙 _
                      right := left i' j' }⟩)
                (List.IsChain.singleton _)))
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
                right := single i
                hom := ObjectProperty.homMk (homOfLE (a.hom.le.trans (by simp))) },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf ((a.hom.le).trans (by simp)) b.hom.le)) }, _],
                ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inl
              ⟨{ left := 𝟙 _
                  right := left i j }⟩)
            (List.IsChain.cons_cons
              (Or.inr
                ⟨{ left := 𝟙 _
                    right := left i i' }⟩)
              (List.IsChain.cons_cons
                (Or.inl
                  ⟨{ left := 𝟙 _
                      right := right i i' }⟩)
                (List.IsChain.singleton _)))
      · refine
          ⟨[{ left := ⟨⟨⟩⟩
                right := single i
                hom := ObjectProperty.homMk (homOfLE (a.hom.le.trans (by simp))) },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := ObjectProperty.homMk (homOfLE
                  (le_inf (a.hom.le.trans (by simp)) (b.hom.le.trans (by simp)))) },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := ObjectProperty.homMk (homOfLE (b.hom.le.trans (by simp))) }, _], ?_, rfl⟩
        exact
          List.IsChain.cons_cons
            (Or.inl
              ⟨{ left := 𝟙 _
                  right := left i j }⟩)
            (List.IsChain.cons_cons
              (Or.inr
                ⟨{ left := 𝟙 _
                    right := left i i' }⟩)
              (List.IsChain.cons_cons
                (Or.inl
                  ⟨{ left := 𝟙 _
                      right := right i i' }⟩)
                (List.IsChain.cons_cons
                  (Or.inr
                    ⟨{ left := 𝟙 _
                        right := left i' j' }⟩)
                  (List.IsChain.singleton _))))⟩

/--
Definition of `pairwiseDiagramIso` / `pairwiseDiagramIso` 的定义

English:
definition pairwiseDiagramIso
  signature: :
  body: { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }

中文:
定义 pairwiseDiagramIso
  签名: :
  定义体: { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
-/
def pairwiseDiagramIso :
    Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ ObjectProperty.ι _ where
  hom := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }

/--
Definition of `pairwiseCoconeIso` / `pairwiseCoconeIso` 的定义

English:
definition pairwiseCoconeIso
  signature: :
  body: Cone.ext (Iso.refl _) (by cat_disch)

中文:
定义 pairwiseCoconeIso
  签名: :
  定义体: Cone.ext (Iso.refl _) (by cat_disch)

Depends on / 依赖: Cone.ext, Iso.refl, cat_disch
-/
def pairwiseCoconeIso :
    (Pairwise.cocone U).op ≅
      (Cone.postcomposeEquivalence (NatIso.op (pairwiseDiagramIso U :) :)).functor.obj
        ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op) :=
  Cone.ext (Iso.refl _) (by cat_disch)

end SheafCondition

open SheafCondition

variable (F : Presheaf C X) {ι : Type*} (U : ι -> Opens X)

/--
Definition of `isLimitOpensLeCoverEquivPairwise` / `isLimitOpensLeCoverEquivPairwise` 的定义

English:
definition isLimitOpensLeCoverEquivPairwise
  signature: :
  body: calc
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
        IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
      (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
    _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pa

中文:
定义 isLimitOpensLeCoverEquivPairwise
  签名: :
  定义体: calc
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
        IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
      (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
    _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pa

Depends on / 依赖: Cone.postcomposeEquivalence, F.mapCone, F.mapConeWhisker.symm, Functor, Functor.Initial.isLimitWhiskerEquiv, Initial, IsLimit, IsLimit.equivIsoLimit, equivIsoLimit, functor, functor.obj, isLimitWhiskerEquiv, mapCone, mapConeWhisker, op.whisker, opensLeCoverCocone, pairwiseToOpensLeCover, postcomposeEquivalence, whisker
-/
def isLimitOpensLeCoverEquivPairwise :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
  calc
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
        IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
      (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
    _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op)) :=
      (IsLimit.equivIsoLimit F.mapConeWhisker.symm)
    _ ≃
        IsLimit
          ((Cone.postcomposeEquivalence _).functor.obj
            (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
      (IsLimit.postcomposeHomEquiv _ _).symm
    _ ≃
        IsLimit
          (F.mapCone
            ((Cone.postcomposeEquivalence _).functor.obj
              ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
      (IsLimit.equivIsoLimit (Functor.mapConePostcomposeEquivalenceFunctor _).symm)
    _ ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
      IsLimit.equivIsoLimit ((Cone.functoriality _ _).mapIso (pairwiseCoconeIso U :).symm)

/--
theorem `isSheafOpensLeCover_iff_isSheafPairwiseIntersections` / 定理 `isSheafOpensLeCover_iff_isSheafPairwiseIntersections`

English:
theorem isSheafOpensLeCover_iff_isSheafPairwiseIntersections
  proof: forall₂_congr fun _ U => (F.isLimitOpensLeCoverEquivPairwise U).nonempty_congr

中文:
定理 isSheafOpensLeCover_iff_isSheafPairwise整数ersections
  证明: forall₂_congr fun _ U => (F.isLimitOpensLeCoverEquivPairwise U).nonempty_congr

Depends on / 依赖: F.isLimitOpensLeCoverEquivPairwise, isLimitOpensLeCoverEquivPairwise, nonempty_congr
-/
theorem isSheafOpensLeCover_iff_isSheafPairwiseIntersections :
    F.IsSheafOpensLeCover ↔ F.IsSheafPairwiseIntersections :=
  forall₂_congr fun _ U => (F.isLimitOpensLeCoverEquivPairwise U).nonempty_congr

variable {F} in
/--
theorem `IsSheaf.isSheafPairwiseIntersections` / 定理 `IsSheaf.isSheafPairwiseIntersections`

English:
theorem IsSheaf.isSheafPairwiseIntersections
  given: (h : F.IsSheaf)
  proof: (h.isSheafOpensLeCover U).map (F.isLimitOpensLeCoverEquivPairwise _)

中文:
定理 是层.isSheafPairwise整数ersections
  条件: (h : F.是层)
  证明: (h.isSheafOpensLeCover U).map (F.isLimitOpensLeCoverEquivPairwise _)

Depends on / 依赖: F.isLimitOpensLeCoverEquivPairwise, h.isSheafOpensLeCover, isLimitOpensLeCoverEquivPairwise, isSheafOpensLeCover
-/
theorem IsSheaf.isSheafPairwiseIntersections (h : F.IsSheaf) :
    Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op)) :=
  (h.isSheafOpensLeCover U).map (F.isLimitOpensLeCoverEquivPairwise _)

/--
theorem `isSheaf_iff_isSheafPairwiseIntersections` / 定理 `isSheaf_iff_isSheafPairwiseIntersections`

English:
theorem isSheaf_iff_isSheafPairwiseIntersections
  statement: F.IsSheaf ↔ F.IsSheafPairwiseIntersections
  proof: by
  rw [isSheaf_iff_isSheafOpensLeCover]; rw [isSheafOpensLeCover_iff_isSheafPairwiseIntersections]

中文:
定理 isSheaf_iff_isSheafPairwise整数ersections
  结论: F.是层 ↔ F.IsSheafPairwise整数ersections
  证明: by
  rw [isSheaf_iff_isSheafOpensLeCover]; rw [isSheafOpensLeCover_iff_isSheafPairwiseIntersections]

Depends on / 依赖: isSheafOpensLeCover_iff_isSheafPairwiseIntersections, isSheaf_iff_isSheafOpensLeCover
-/
theorem isSheaf_iff_isSheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections := by
  rw [isSheaf_iff_isSheafOpensLeCover]; rw [isSheafOpensLeCover_iff_isSheafPairwiseIntersections]

variable {F} in
/--
theorem `IsSheaf.isSheafPreservesLimitPairwiseIntersections` / 定理 `IsSheaf.isSheafPreservesLimitPairwiseIntersections`

English:
theorem IsSheaf.isSheafPreservesLimitPairwiseIntersections
  given: (h : F.IsSheaf)
  proof: preservesLimit_of_preserves_limit_cone (Pairwise.coconeIsColimit U).op
    (h.isSheafPairwiseIntersections U).some

中文:
定理 是层.isSheafPreservesLimitPairwise整数ersections
  条件: (h : F.是层)
  证明: preservesLimit_of_preserves_limit_cone (Pairwise.coconeIsColimit U).op
    (h.isSheafPairwiseIntersections U).some

Depends on / 依赖: Pairwise, Pairwise.coconeIsColimit, coconeIsColimit, h.isSheafPairwiseIntersections, isSheafPairwiseIntersections, preservesLimit_of_preserves_limit_cone
-/
theorem IsSheaf.isSheafPreservesLimitPairwiseIntersections (h : F.IsSheaf) :
    PreservesLimit (Pairwise.diagram U).op F :=
  preservesLimit_of_preserves_limit_cone (Pairwise.coconeIsColimit U).op
    (h.isSheafPairwiseIntersections U).some

/--
theorem `isSheaf_iff_isSheafPreservesLimitPairwiseIntersections` / 定理 `isSheaf_iff_isSheafPreservesLimitPairwiseIntersections`

English:
theorem isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
  proof: by
  refine ⟨fun h U => h.isSheafPreservesLimitPairwiseIntersections,
    fun h => F.isSheaf_iff_isSheafPairwiseIntersections.mpr fun ι U => ?_⟩
  have := h U
  exact ⟨isLimitOfPreserves _ (Pairwise.coconeIsColimit U).op⟩

中文:
定理 isSheaf_iff_isSheafPreservesLimitPairwise整数ersections
  证明: by
  refine ⟨fun h U => h.isSheafPreservesLimitPairwiseIntersections,
    fun h => F.isSheaf_iff_isSheafPairwiseIntersections.mpr fun ι U => ?_⟩
  have := h U
  exact ⟨isLimitOfPreserves _ (Pairwise.coconeIsColimit U).op⟩

Depends on / 依赖: F.isSheaf_iff_isSheafPairwiseIntersections.mpr, Pairwise, Pairwise.coconeIsColimit, coconeIsColimit, h.isSheafPreservesLimitPairwiseIntersections, isLimitOfPreserves, isSheafPreservesLimitPairwiseIntersections, isSheaf_iff_isSheafPairwiseIntersections
-/
theorem isSheaf_iff_isSheafPreservesLimitPairwiseIntersections :
    F.IsSheaf ↔ F.IsSheafPreservesLimitPairwiseIntersections := by
  refine ⟨fun h U => h.isSheafPreservesLimitPairwiseIntersections,
    fun h => F.isSheaf_iff_isSheafPairwiseIntersections.mpr fun ι U => ?_⟩
  have := h U
  exact ⟨isLimitOfPreserves _ (Pairwise.coconeIsColimit U).op⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/--
Definition of `interUnionPullbackCone` / `interUnionPullbackCone` 的定义

English:
definition interUnionPullbackCone
  signature: :
  body: PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op) by
    rw [← F.1.map_comp]; rw [← F.1.map_comp]
    congr 1

@[simp]

中文:
定义 interUnionPullbackCone
  签名: :
  定义体: PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op) by
    rw [← F.1.map_comp]; rw [← F.1.map_comp]
    congr 1

@[simp]

Depends on / 依赖: PullbackCone, PullbackCone.mk, homOfLE, le_sup_left, le_sup_right, map_comp
-/
def interUnionPullbackCone :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op)
      (F.1.map (homOfLE inf_le_right).op) :=
PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op) by
    rw [← F.1.map_comp]; rw [← F.1.map_comp]
    congr 1

@[simp]
/--
theorem `interUnionPullbackCone_pt` / 定理 `interUnionPullbackCone_pt`

English:
theorem interUnionPullbackCone_pt
  statement: (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V)
  proof: rfl

@[simp]

中文:
定理 interUnionPullbackCone_pt
  结论: (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V)
  证明: rfl

@[simp]
-/
theorem interUnionPullbackCone_pt : (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V) :=
  rfl

@[simp]
/--
theorem `interUnionPullbackCone_fst` / 定理 `interUnionPullbackCone_fst`

English:
theorem interUnionPullbackCone_fst
  proof: rfl

@[simp]

中文:
定理 interUnionPullbackCone_fst
  证明: rfl

@[simp]
-/
theorem interUnionPullbackCone_fst :
    (interUnionPullbackCone F U V).fst = F.1.map (homOfLE le_sup_left).op :=
  rfl

@[simp]
/--
theorem `interUnionPullbackCone_snd` / 定理 `interUnionPullbackCone_snd`

English:
theorem interUnionPullbackCone_snd
  proof: rfl

中文:
定理 interUnionPullbackCone_snd
  证明: rfl
-/
theorem interUnionPullbackCone_snd :
    (interUnionPullbackCone F U V).snd = F.1.map (homOfLE le_sup_right).op :=
  rfl

variable
  (s :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (homOfLE inf_le_right).op))

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `interUnionPullbackConeLift` / `interUnionPullbackConeLift` 的定义

English:
definition interUnionPullbackConeLift
  signature: : s.pt ⟶ F.1.obj (op (U ⊔ V))
  body: by
  let ι : ULift.{w} WalkingPair -> Opens X := fun j => WalkingPair.casesOn j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, 

中文:
定义 interUnionPullbackConeLift
  签名: : s.pt ⟶ F.1.obj (op (U ⊔ V))
  定义体: by
  let ι : ULift.{w} WalkingPair -> Opens X := fun j => WalkingPair.casesOn j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, 

Depends on / 依赖: F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp, Opens.coe_iSup, Or.inl, Or.inr, Set.mem_iUnion, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, casesOn, coe_iSup, eqToHom, exacts, isSheaf_iff_isSheafPairwiseIntersections, j.down, mem_iUnion, naturality, presheaf, s.fst, s.pt
-/
def interUnionPullbackConeLift : s.pt ⟶ F.1.obj (op (U ⊔ V)) := by
  let ι : ULift.{w} WalkingPair -> Opens X := fun j => WalkingPair.casesOn j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  refine
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.lift
        ⟨s.pt,
          { app := ?_
            naturality := ?_ }⟩ ≫
      F.1.map (eqToHom hι).op
  · rintro ((_ | _) | (_ | _))
    exacts [s.fst, s.snd, s.fst ≫ F.1.map (homOfLE inf_le_left).op,
      s.snd ≫ F.1.map (homOfLE inf_le_left).op]
  rintro ⟨i⟩ ⟨j⟩ f
  let g : j ⟶ i := f.unop
  have : f = g.op := rfl
  clear_value g
  subst this
  rcases i with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases j with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases g with ⟨⟩ <;>
  dsimp [Pairwise.diagram] <;>
  simp only [ι, Category.id_comp, s.condition, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← cancel_mono (F.1.map (eqToHom <| inf_comm U V : U ⊓ V ⟶ _).op)]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.1.map_comp]; rw [← F.1.map_comp]
  exact s.condition.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `interUnionPullbackConeLift_left` / 定理 `interUnionPullbackConeLift_left`

English:
theorem interUnionPullbackConeLift_left
  proof: by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.left

中文:
定理 interUnionPullbackConeLift_left
  证明: by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.left

Depends on / 依赖: Category, Category.assoc, F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp, Pairwise, Pairwise.single, ULift.up, WalkingPair, WalkingPair.left, interUnionPullbackConeLift, isSheaf_iff_isSheafPairwiseIntersections, map_comp, presheaf, single, some.fac
-/
theorem interUnionPullbackConeLift_left :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_left).op = s.fst := by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `interUnionPullbackConeLift_right` / 定理 `interUnionPullbackConeLift_right`

English:
theorem interUnionPullbackConeLift_right
  proof: by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.right

中文:
定理 interUnionPullbackConeLift_right
  证明: by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.right

Depends on / 依赖: Category, Category.assoc, F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp, Pairwise, Pairwise.single, ULift.up, WalkingPair, WalkingPair.right, interUnionPullbackConeLift, isSheaf_iff_isSheafPairwiseIntersections, map_comp, presheaf, single, some.fac
-/
theorem interUnionPullbackConeLift_right :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_right).op = s.snd := by
  rw [interUnionPullbackConeLift]; rw [Category.assoc]; rw [← F.1.map_comp]
  exact
(F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _
op Pairwise.single ULift.up WalkingPair.right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitPullbackCone` / `isLimitPullbackCone` 的定义

English:
definition isLimitPullbackCone
  signature: : IsLimit (interUnionPullbackCone F U V)
  body: by
  let ι : ULift.{w} WalkingPair -> Opens X := fun ⟨j⟩ => WalkingPair.casesOn j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩


中文:
定义 isLimitPullbackCone
  签名: : 是极限 (interUnionPullbackCone F U V)
  定义体: by
  let ι : ULift.{w} WalkingPair -> Opens X := fun ⟨j⟩ => WalkingPair.casesOn j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩


Depends on / 依赖: Opens.coe_iSup, Or.inl, Or.inr, PullbackCone, PullbackCone.isLimitAux, Set.mem_iUnion, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, casesOn, coe_iSup, exacts, interUnionPullbackConeLift, interUnionPullbackConeLift_left, interUnionPullbackConeLift_right, isLimitAux, mem_iUnion
-/
def isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V) := by
  let ι : ULift.{w} WalkingPair -> Opens X := fun ⟨j⟩ => WalkingPair.casesOn j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup]; rw [Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  apply PullbackCone.isLimitAux'
  intro s
  use interUnionPullbackConeLift F U V s
  refine ⟨?_, ?_, ?_⟩
  · apply interUnionPullbackConeLift_left
  · apply interUnionPullbackConeLift_right
  · intro m h₁ h₂
    rw [← cancel_mono (F.1.map (eqToHom hι.symm).op)]
    apply (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.hom_ext
    rintro ((_ | _) | (_ | _)) <;>
    rw [Category.assoc]; rw [Category.assoc]; rw [Functor.mapCone_π_app]; rw [← F.1.map_comp]
    · convert! h₁
      apply interUnionPullbackConeLift_left
    · convert! h₂
      apply interUnionPullbackConeLift_right
    all_goals
      dsimp only [Functor.op, Pairwise.cocone_ι_app, Functor.mapCone_π_app, Cocone.op,
        Pairwise.coconeιApp, unop_op, op_comp, NatTrans.op]
      simp_rw [F.1.map_comp, ← Category.assoc]
      congr 1
      simp_rw [Category.assoc, ← F.1.map_comp]
    · convert! h₁
      apply interUnionPullbackConeLift_left
    · convert! h₂
      apply interUnionPullbackConeLift_right

/--
Definition of `isProductOfDisjoint` / `isProductOfDisjoint` 的定义

English:
definition isProductOfDisjoint
  signature: (h : U ⊓ V = ⊥)
  body: isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)

中文:
定义 isProductOfDisjoint
  签名: (h : U ⊓ V = ⊥)
  定义体: isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)

Depends on / 依赖: F.isTerminalOfEqEmpty, isLimitPullbackCone, isProductOfIsTerminalIsPullback, isTerminalOfEqEmpty
-/
def isProductOfDisjoint (h : U ⊓ V = ⊥) :
    IsLimit
      (BinaryFan.mk (F.1.map (homOfLE le_sup_left : _ ⟶ U ⊔ V).op)
        (F.1.map (homOfLE le_sup_right : _ ⟶ U ⊔ V).op)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)

end TopCat.Sheaf
