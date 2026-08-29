/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The transfinite iteration of a successor structure

Given a successor structure `Φ : SuccStruct C`
(see the file `Mathlib/CategoryTheory/SmallObject/Iteration/Basic.lean`)
and a well-ordered type `J`, we define the iteration `Φ.iteration J : C`. It is
defined as the colimit of a functor `Φ.iterationFunctor J : J ⥤ C`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Category Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

variable {J} in
/--
Definition of `iter` / `iter` 的定义

English:
definition iter
  signature: (j : J)
  body: Classical.arbitrary _

中文:
定义 iter
  签名: (j : J)
  定义体: Classical.arbitrary _

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
noncomputable def iter (j : J) : Φ.Iteration j := Classical.arbitrary _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `iterationFunctor` / `iterationFunctor` 的定义

English:
definition iterationFunctor
  signature: : J ⥤ C where
  body: (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

中文:
定义 iterationFunctor
  签名: : J ⥤ C where
  定义体: (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

Depends on / 依赖: F.obj
-/
noncomputable def iterationFunctor : J ⥤ C where
  obj j := (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

/--
Definition of `iteration` / `iteration` 的定义

English:
definition iteration
  signature: : C
  body: colimit (Φ.iterationFunctor J)

中文:
定义 iteration
  签名: : C
  定义体: colimit (Φ.iterationFunctor J)

Depends on / 依赖: colimit, iterationFunctor
-/
noncomputable def iteration : C := colimit (Φ.iterationFunctor J)

/--
Definition of `iterationCocone` / `iterationCocone` 的定义

English:
definition iterationCocone
  signature: : Cocone (Φ.iterationFunctor J)
  body: colimit.cocone _

@[simp]

中文:
定义 iterationCocone
  签名: : 余锥 (Φ.iterationFunctor J)
  定义体: colimit.cocone _

@[simp]

Depends on / 依赖: cocone, colimit, colimit.cocone
-/
noncomputable def iterationCocone : Cocone (Φ.iterationFunctor J) :=
  colimit.cocone _

@[simp]
/--
lemma `iterationCocone_pt` / 引理 `iterationCocone_pt`

English:
lemma iterationCocone_pt
  statement: (Φ.iterationCocone J).pt = Φ.iteration J
  proof: rfl

中文:
引理 iterationCocone_pt
  结论: (Φ.iterationCocone J).pt = Φ.iteration J
  证明: rfl
-/
lemma iterationCocone_pt : (Φ.iterationCocone J).pt = Φ.iteration J := rfl

/--
Definition of `isColimitIterationCocone` / `isColimitIterationCocone` 的定义

English:
definition isColimitIterationCocone
  signature: : IsColimit (Φ.iterationCocone J)
  body: colimit.isColimit _

中文:
定义 isColimitIterationCocone
  签名: : 是余极限 (Φ.iterationCocone J)
  定义体: colimit.isColimit _

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
noncomputable def isColimitIterationCocone : IsColimit (Φ.iterationCocone J) :=
  colimit.isColimit _

variable {J}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iterationFunctor_obj` / 引理 `iterationFunctor_obj`

English:
lemma iterationFunctor_obj
  given: (i : J) {j : J} (iter : Φ.Iteration j) (hi : i <= j)
  proof: Iteration.congr_obj (Φ.iter i) iter i (by simp) hi

中文:
引理 iterationFunctor_obj
  条件: (i : J) {j : J} (iter : Φ.Iteration j) (hi : i <= j)
  证明: Iteration.congr_obj (Φ.iter i) iter i (by simp) hi

Depends on / 依赖: Iteration, Iteration.congr_obj, congr_obj
-/
lemma iterationFunctor_obj (i : J) {j : J} (iter : Φ.Iteration j) (hi : i <= j) :
    (Φ.iterationFunctor J).obj i = iter.F.obj ⟨i, hi⟩ :=
  Iteration.congr_obj (Φ.iter i) iter i (by simp) hi

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `arrowMk_iterationFunctor_map` / 引理 `arrowMk_iterationFunctor_map`

English:
lemma arrowMk_iterationFunctor_map
  statement: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂)
  proof: by
  dsimp [iterationFunctor]
  rw [Iteration.arrow_mk_mapObj]
  exact Arrow.ext (Iteration.congr_obj _ _ _ _ _)
    (Iteration.congr_obj _ _ _ _ _) (Iteration.congr_map _ _ _ _ _)

中文:
引理 arrowMk_iterationFunctor_map
  结论: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂)
  证明: by
  dsimp [iterationFunctor]
  rw [Iteration.arrow_mk_mapObj]
  exact Arrow.ext (Iteration.congr_obj _ _ _ _ _)
    (Iteration.congr_obj _ _ _ _ _) (Iteration.congr_map _ _ _ _ _)

Depends on / 依赖: Arrow.ext, Iteration, Iteration.arrow_mk_mapObj, Iteration.congr_map, Iteration.congr_obj, arrow_mk_mapObj, congr_map, congr_obj, iterationFunctor
-/
lemma arrowMk_iterationFunctor_map (i₁ i₂ : J) (h₁₂ : i₁ <= i₂)
    {j : J} (iter : Φ.Iteration j) (hj : i₂ <= j) :
    Arrow.mk ((Φ.iterationFunctor J).map (homOfLE h₁₂)) =
      Arrow.mk (iter.F.map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans hj⟩ ⟶ ⟨i₂, hj⟩)) := by
  dsimp [iterationFunctor]
  rw [Iteration.arrow_mk_mapObj]
  exact Arrow.ext (Iteration.congr_obj _ _ _ _ _)
    (Iteration.congr_obj _ _ _ _ _) (Iteration.congr_map _ _ _ _ _)

variable (J)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Φ.iterationFunctor J).IsWellOrderContinuous
  body: ⟨by
    let e : (Set.principalSegIio i).monotone.functor ⋙
      (Φ.iterationFunctor J) ≅ restrictionLT (Φ.iter i).F (by simp) :=
      NatIso.ofComponents (fun _ => eqToIso (Φ.iterationFunctor_obj _ _ _)) (by
        rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
        apply Arrow.mk_injective
        simpa using! Φ.arrowMk_iterationFunctor_map k₁ k₂ (leOfHom f) (Φ.iter i) h₂.le)
    refine (IsColimit.precomposeInvEquiv e _).1 ?_
    refine IsColimit.ofIsoColimit ((Φ.iter i).isColimit i hi (by simp)) ?_
    refine Cocone.ext (eqToIso (Φ.iterationFunctor_obj i (Φ.iter i) (by simp)).symm) ?_
    rintro ⟨k, hk⟩
    apply Arrow.mk_injective
    simp [Φ.arrowMk_iterationFunctor_map k i hk.le (Φ.iter i) (by simp), e]⟩

中文:
实例 :
  签名: (Φ.iterationFunctor J).是WellOrderContinuous
  定义体: ⟨by
    let e : (Set.principalSegIio i).monotone.functor ⋙
      (Φ.iterationFunctor J) ≅ restrictionLT (Φ.iter i).F (by simp) :=
      NatIso.ofComponents (fun _ => eqToIso (Φ.iterationFunctor_obj _ _ _)) (by
        rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
        apply Arrow.mk_injective
        simpa using! Φ.arrowMk_iterationFunctor_map k₁ k₂ (leOfHom f) (Φ.iter i) h₂.le)
    refine (IsColimit.precomposeInvEquiv e _).1 ?_
    refine IsColimit.ofIsoColimit ((Φ.iter i).isColimit i hi (by simp)) ?_
    refine Cocone.ext (eqToIso (Φ.iterationFunctor_obj i (Φ.iter i) (by simp)).symm) ?_
    rintro ⟨k, hk⟩
    apply Arrow.mk_injective
    simp [Φ.arrowMk_iterationFunctor_map k i hk.le (Φ.iter i) (by simp), e]⟩

Depends on / 依赖: Arrow.mk_injective, Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, NatIso, NatIso.ofComponents, Set.principalSegIio, arrowMk_iterationFunctor_map, eqToIso, functor, isColimit, iterationFunctor, iterationFunctor_obj, leOfHom, mk_injective, monotone, monotone.functor, ofComponents
-/
instance : (Φ.iterationFunctor J).IsWellOrderContinuous where
  nonempty_isColimit i hi := ⟨by
    let e : (Set.principalSegIio i).monotone.functor ⋙
      (Φ.iterationFunctor J) ≅ restrictionLT (Φ.iter i).F (by simp) :=
      NatIso.ofComponents (fun _ => eqToIso (Φ.iterationFunctor_obj _ _ _)) (by
        rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
        apply Arrow.mk_injective
        simpa using! Φ.arrowMk_iterationFunctor_map k₁ k₂ (leOfHom f) (Φ.iter i) h₂.le)
    refine (IsColimit.precomposeInvEquiv e _).1 ?_
    refine IsColimit.ofIsoColimit ((Φ.iter i).isColimit i hi (by simp)) ?_
    refine Cocone.ext (eqToIso (Φ.iterationFunctor_obj i (Φ.iter i) (by simp)).symm) ?_
    rintro ⟨k, hk⟩
    apply Arrow.mk_injective
    simp [Φ.arrowMk_iterationFunctor_map k i hk.le (Φ.iter i) (by simp), e]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `iterationFunctorObjBotIso` / `iterationFunctorObjBotIso` 的定义

English:
definition iterationFunctorObjBotIso
  signature: : (Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀
  body: eqToIso (Φ.iter ⊥).obj_bot

中文:
定义 iterationFunctorObjBotIso
  签名: : (Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀
  定义体: eqToIso (Φ.iter ⊥).obj_bot

Depends on / 依赖: eqToIso, obj_bot
-/
noncomputable def iterationFunctorObjBotIso : (Φ.iterationFunctor J).obj ⊥ ≅ Φ.X₀ :=
  eqToIso (Φ.iter ⊥).obj_bot

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ιIterationFunctor` / `ιIterationFunctor` 的定义

English:
definition ιIterationFunctor
  signature: :
  body: (Φ.iterationFunctorObjBotIso J).inv ≫
    (Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)
  naturality _ _ f := by
    dsimp
    rw [id_comp]; rw [assoc]; rw [← Functor.map_comp]
    rfl

中文:
定义 ιIterationFunctor
  签名: :
  定义体: (Φ.iterationFunctorObjBotIso J).inv ≫
    (Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)
  naturality _ _ f := by
    dsimp
    rw [id_comp]; rw [assoc]; rw [← Functor.map_comp]
    rfl

Depends on / 依赖: iterationFunctorObjBotIso
-/
noncomputable def ιIterationFunctor :
    (Functor.const _).obj Φ.X₀ ⟶ Φ.iterationFunctor J where
  app j := (Φ.iterationFunctorObjBotIso J).inv ≫
    (Φ.iterationFunctor J).map (homOfLE bot_le : ⊥ ⟶ j)
  naturality _ _ f := by
    dsimp
    rw [id_comp]; rw [assoc]; rw [← Functor.map_comp]
    rfl

/--
Definition of `ιIteration` / `ιIteration` 的定义

English:
definition ιIteration
  signature: : Φ.X₀ ⟶ Φ.iteration J
  body: (Φ.iterationFunctorObjBotIso J).inv ≫ colimit.ι _ ⊥

中文:
定义 ιIteration
  签名: : Φ.X₀ ⟶ Φ.iteration J
  定义体: (Φ.iterationFunctorObjBotIso J).inv ≫ colimit.ι _ ⊥

Depends on / 依赖: colimit, iterationFunctorObjBotIso
-/
noncomputable def ιIteration : Φ.X₀ ⟶ Φ.iteration J :=
  (Φ.iterationFunctorObjBotIso J).inv ≫ colimit.ι _ ⊥

/-- The inclusion `Φ.ιIteration J` is a transfinite composition of
shape `J` of morphisms in `Φ.prop`. -/
@[simps]
/--
Definition of `transfiniteCompositionOfShapeιIteration` / `transfiniteCompositionOfShapeιIteration` 的定义

English:
definition transfiniteCompositionOfShapeιIteration
  signature: :
  body: Φ.iterationFunctorObjBotIso J
  map_mem j hj := by
    have := (Φ.iter (Order.succ j)).prop_map_succ j (Order.lt_succ_of_not_isMax hj)
    rw [prop_iff] at this ⊢
    simp only [Φ.iterationFunctor_obj j (Φ.iter (Order.succ j)) (Order.le_succ j),
      Φ.arrowMk_iterationFunctor_map _ _ (Order.le_succ j) (Φ.iter (Order.succ j)) (by simp),
      this]
  F := Φ.iterationFunctor J
  incl := (Φ.iterationCocone J).ι
  isColimit := Φ.isColimitIterationCocone J

中文:
定义 transfiniteCompositionOfShapeιIteration
  签名: :
  定义体: Φ.iterationFunctorObjBotIso J
  map_mem j hj := by
    have := (Φ.iter (Order.succ j)).prop_map_succ j (Order.lt_succ_of_not_isMax hj)
    rw [prop_iff] at this ⊢
    simp only [Φ.iterationFunctor_obj j (Φ.iter (Order.succ j)) (Order.le_succ j),
      Φ.arrowMk_iterationFunctor_map _ _ (Order.le_succ j) (Φ.iter (Order.succ j)) (by simp),
      this]
  F := Φ.iterationFunctor J
  incl := (Φ.iterationCocone J).ι
  isColimit := Φ.isColimitIterationCocone J

Depends on / 依赖: iterationFunctorObjBotIso
-/
noncomputable def transfiniteCompositionOfShapeιIteration :
    Φ.prop.TransfiniteCompositionOfShape J (Φ.ιIteration J) where
  isoBot := Φ.iterationFunctorObjBotIso J
  map_mem j hj := by
    have := (Φ.iter (Order.succ j)).prop_map_succ j (Order.lt_succ_of_not_isMax hj)
    rw [prop_iff] at this ⊢
    simp only [Φ.iterationFunctor_obj j (Φ.iter (Order.succ j)) (Order.le_succ j),
      Φ.arrowMk_iterationFunctor_map _ _ (Order.le_succ j) (Φ.iter (Order.succ j)) (by simp),
      this]
  F := Φ.iterationFunctor J
  incl := (Φ.iterationCocone J).ι
  isColimit := Φ.isColimitIterationCocone J

variable {J}

/--
lemma `prop_iterationFunctor_map_succ` / 引理 `prop_iterationFunctor_map_succ`

English:
lemma prop_iterationFunctor_map_succ
  given: (j : J) (hj : ¬ IsMax j)
  proof: (Φ.transfiniteCompositionOfShapeιIteration J).map_mem j hj

中文:
引理 prop_iterationFunctor_map_succ
  条件: (j : J) (hj : ¬ IsMax j)
  证明: (Φ.transfiniteCompositionOfShapeιIteration J).map_mem j hj

Depends on / 依赖: map_mem
-/
lemma prop_iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    Φ.prop ((Φ.iterationFunctor J).map (homOfLE (Order.le_succ j))) :=
  (Φ.transfiniteCompositionOfShapeιIteration J).map_mem j hj

/--
Definition of `iterationFunctorObjSuccIso` / `iterationFunctorObjSuccIso` 的定义

English:
definition iterationFunctorObjSuccIso
  signature: (j : J) (hj : ¬ IsMax j)
  body: eqToIso ((Φ.prop_iterationFunctor_map_succ j hj).succ_eq.symm)

@[reassoc]

中文:
定义 iterationFunctorObjSuccIso
  签名: (j : J) (hj : ¬ IsMax j)
  定义体: eqToIso ((Φ.prop_iterationFunctor_map_succ j hj).succ_eq.symm)

@[reassoc]

Depends on / 依赖: eqToIso, prop_iterationFunctor_map_succ, succ_eq, succ_eq.symm
-/
noncomputable def iterationFunctorObjSuccIso (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).obj (Order.succ j) ≅
      Φ.succ ((Φ.iterationFunctor J).obj j) :=
  eqToIso ((Φ.prop_iterationFunctor_map_succ j hj).succ_eq.symm)

@[reassoc]
/--
lemma `iterationFunctor_map_succ` / 引理 `iterationFunctor_map_succ`

English:
lemma iterationFunctor_map_succ
  given: (j : J) (hj : ¬ IsMax j)
  proof: (Φ.prop_iterationFunctor_map_succ j hj).fac

中文:
引理 iterationFunctor_map_succ
  条件: (j : J) (hj : ¬ IsMax j)
  证明: (Φ.prop_iterationFunctor_map_succ j hj).fac

Depends on / 依赖: prop_iterationFunctor_map_succ
-/
lemma iterationFunctor_map_succ (j : J) (hj : ¬ IsMax j) :
    (Φ.iterationFunctor J).map (homOfLE (Order.le_succ j)) =
      Φ.toSucc _ ≫ (Φ.iterationFunctorObjSuccIso j hj).inv :=
  (Φ.prop_iterationFunctor_map_succ j hj).fac

end CategoryTheory.SmallObject.SuccStruct
