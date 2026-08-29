/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Limits and colimits in the category of homological complexes

In this file, it is shown that if a category `C` has (co)limits of shape `J`,
then it is also the case of the categories `HomologicalComplex C c`,
and the evaluation functors `eval C c i : HomologicalComplex C c ⥤ C`
commute to these.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι J : Type*} [Category* C] [Category* J] {c : ComplexShape ι} [HasZeroMorphisms C]

section

variable (F : J ⥤ HomologicalComplex C c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitOfEval` / `isLimitOfEval` 的定义

English:
definition isLimitOfEval
  signature: (s : Cone F)
  body: { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_ap

中文:
定义 isLimitOfEval
  签名: (s : Cone F)
  定义体: { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_ap

Depends on / 依赖: Functor, Functor.mapCone_, Hom.comm, IsLimit, IsLimit.hom_ext, SingleFunctors, SingleFunctors.postcomp, comp_f, eval_map, hom_ext, infer_instance, mapCone, postcomp, reassoc_of, singleFunctor, singleFunctors
-/
def isLimitOfEval (s : Cone F)
    (hs : forall (i : ι), IsLimit ((eval C c i).mapCone s)) : IsLimit s where
  lift t :=
    { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_app, eval_map, assoc]
        rw [eq i']; rw [← Hom.comm]; rw [reassoc_of% (eq i)]; rw [Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCone t)
    intro j
    dsimp
    simp only [← comp_f, hm]

variable [forall (n : ι), HasLimit (F ⋙ eval C c n)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the limit `F ⋙ eval C c n`. -/
@[simps]
/--
Definition of `coneOfHasLimitEval` / `coneOfHasLimitEval` 的定义

English:
definition coneOfHasLimitEval
  signature: : Cone F where
  body: { X := fun n => limit (F ⋙ eval C c n)
      d := fun n m => limMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [limMap_π]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [comp_zero]; rw [zero_comp] }
  π :=
    { app := fun j => { f := fun _ =>

中文:
定义 coneOfHasLimitEval
  签名: : Cone F where
  定义体: { X := fun n => limit (F ⋙ eval C c n)
      d := fun n m => limMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [limMap_π]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [comp_zero]; rw [zero_comp] }
  π :=
    { app := fun j => { f := fun _ =>

Depends on / 依赖: Category, Category.id_comp, CochainComplex, CochainComplex.singleFunctor, F.obj, Functor, Functor.Linear, Functor.comp_map, HomotopyCategory, HomotopyCategory.quotient, Linear, comp_map, comp_zero, eval_map, id_comp, limMap, limit.w, naturality, quotient, singleFunctor
-/
noncomputable def coneOfHasLimitEval : Cone F where
  pt :=
    { X := fun n => limit (F ⋙ eval C c n)
      d := fun n m => limMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [limMap_π]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [comp_zero]; rw [zero_comp] }
  π :=
    { app := fun j => { f := fun _ => limit.π _ j }
      naturality := fun i j φ => by
        ext n
        dsimp
        simp only [Category.id_comp]
        rw [← eval_map]; rw [← Functor.comp_map]; rw [limit.w] }

/--
Definition of `isLimitConeOfHasLimitEval` / `isLimitConeOfHasLimitEval` 的定义

English:
definition isLimitConeOfHasLimitEval
  signature: : IsLimit (coneOfHasLimitEval F)
  body: isLimitOfEval _ _ (fun _ => limit.isLimit _)

中文:
定义 isLimitConeOfHasLimitEval
  签名: : IsLimit (coneOfHasLimitEval F)
  定义体: isLimitOfEval _ _ (fun _ => limit.isLimit _)

Depends on / 依赖: isLimit, isLimitOfEval, limit.isLimit
-/
noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) :=
  isLimitOfEval _ _ (fun _ => limit.isLimit _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimit F
  body: ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

中文:
实例 :
  签名: HasLimit F
  定义体: ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

Depends on / 依赖: isLimitConeOfHasLimitEval
-/
instance : HasLimit F := ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

noncomputable instance (n : ι) : PreservesLimit F (eval C c n) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F) (limit.isLimit _)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] : HasLimitsOfShape J (HomologicalComplex C c)
  body: ⟨inferInstance⟩

中文:
实例 [HasLimitsOfShape
  签名: J C] : HasLimitsOfShape J (HomologicalComplex C c)
  定义体: ⟨inferInstance⟩
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] (n
  body: ⟨inferInstance⟩

中文:
实例 [HasLimitsOfShape
  签名: J C] (n
  定义体: ⟨inferInstance⟩
-/
noncomputable instance [HasLimitsOfShape J C] (n : ι) :
    PreservesLimitsOfShape J (eval C c n) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] : HasFiniteLimits (HomologicalComplex C c)
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 [HasFiniteLimits
  签名: C] : HasFiniteLimits (HomologicalComplex C c)
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance [HasFiniteLimits C] : HasFiniteLimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] (n
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 [HasFiniteLimits
  签名: C] (n
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance [HasFiniteLimits C] (n : ι) : PreservesFiniteLimits (eval C c n) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] {K L
  body: by
  change Mono ((HomologicalComplex.eval C c n).map φ)
  infer_instance

中文:
实例 [HasFiniteLimits
  签名: C] {K L
  定义体: by
  change Mono ((HomologicalComplex.eval C c n).map φ)
  infer_instance

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, infer_instance
-/
instance [HasFiniteLimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Mono φ] (n : ι) :
    Mono (φ.f n) := by
  change Mono ((HomologicalComplex.eval C c n).map φ)
  infer_instance

section

variable (F : J ⥤ HomologicalComplex C c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitOfEval` / `isColimitOfEval` 的定义

English:
definition isColimitOfEval
  signature: (s : Cocone F)
  body: { f := fun i => (hs i).desc ((eval C c i).mapCocone t)
      comm' := fun i i' _ => by
        apply IsColimit.hom_ext (hs i)
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCocone t)
        simp only [Functor.mapCocone_ι_app, eval_map] at eq
        simp only [Functor.mapCo

中文:
定义 isColimitOfEval
  签名: (s : Cocone F)
  定义体: { f := fun i => (hs i).desc ((eval C c i).mapCocone t)
      comm' := fun i i' _ => by
        apply IsColimit.hom_ext (hs i)
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCocone t)
        simp only [Functor.mapCocone_ι_app, eval_map] at eq
        simp only [Functor.mapCo

Depends on / 依赖: Functor, Functor.mapCocone_, Hom.comm, Hom.comm_assoc, IsColimit, IsColimit.hom_ext, comm_assoc, comp_f, eval_map, hom_ext, mapCocone, reassoc_of
-/
def isColimitOfEval (s : Cocone F)
    (hs : forall (i : ι), IsColimit ((eval C c i).mapCocone s)) : IsColimit s where
  desc t :=
    { f := fun i => (hs i).desc ((eval C c i).mapCocone t)
      comm' := fun i i' _ => by
        apply IsColimit.hom_ext (hs i)
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCocone t)
        simp only [Functor.mapCocone_ι_app, eval_map] at eq
        simp only [Functor.mapCocone_ι_app, eval_map]
        rw [reassoc_of% (eq i)]; rw [Hom.comm_assoc]; rw [eq i']; rw [Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCocone t)
    intro j
    dsimp
    simp only [← comp_f, hm]


variable [forall (n : ι), HasColimit (F ⋙ HomologicalComplex.eval C c n)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the colimit of `F ⋙ eval C c n`. -/
@[simps]
/--
Definition of `coconeOfHasColimitEval` / `coconeOfHasColimitEval` 的定义

English:
definition coconeOfHasColimitEval
  signature: : Cocone F where
  body: { X := fun n => colimit (F ⋙ eval C c n)
      d := fun n m => colimMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [ι_colimMap]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [zero_comp]; rw [comp_zero] }
  ι :=
    { app := fun j => { f := fu

中文:
定义 coconeOfHasColimitEval
  签名: : Cocone F where
  定义体: { X := fun n => colimit (F ⋙ eval C c n)
      d := fun n m => colimMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [ι_colimMap]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [zero_comp]; rw [comp_zero] }
  ι :=
    { app := fun j => { f := fu

Depends on / 依赖: Category, Category.comp_id, F.obj, Functor, Functor.comp_map, colimMap, colimit, colimit.w, comp_id, comp_map, comp_zero, eval_map, naturality, zero_comp
-/
noncomputable def coconeOfHasColimitEval : Cocone F where
  pt :=
    { X := fun n => colimit (F ⋙ eval C c n)
      d := fun n m => colimMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [ι_colimMap]
        dsimp
        rw [(F.obj j).shape _ _ h]; rw [zero_comp]; rw [comp_zero] }
  ι :=
    { app := fun j => { f := fun n => colimit.ι (F ⋙ eval C c n) j }
      naturality := fun i j φ => by
        ext n
        dsimp
        simp only [Category.comp_id]
        rw [← eval_map]; rw [← Functor.comp_map]; rw [colimit.w] }

/--
Definition of `isColimitCoconeOfHasColimitEval` / `isColimitCoconeOfHasColimitEval` 的定义

English:
definition isColimitCoconeOfHasColimitEval
  signature: : IsColimit (coconeOfHasColimitEval F)
  body: isColimitOfEval _ _ (fun _ => colimit.isColimit _)

中文:
定义 isColimitCoconeOfHasColimitEval
  签名: : IsColimit (coconeOfHasColimitEval F)
  定义体: isColimitOfEval _ _ (fun _ => colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitOfEval
-/
noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) :=
  isColimitOfEval _ _ (fun _ => colimit.isColimit _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

中文:
实例 :
  签名: HasColimit F
  定义体: ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

Depends on / 依赖: isColimitCoconeOfHasColimitEval
-/
instance : HasColimit F := ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

noncomputable instance (n : ι) : PreservesColimit F (eval C c n) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    (colimit.isColimit _)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J C] : HasColimitsOfShape J (HomologicalComplex C c)
  body: ⟨inferInstance⟩

中文:
实例 [HasColimitsOfShape
  签名: J C] : HasColimitsOfShape J (HomologicalComplex C c)
  定义体: ⟨inferInstance⟩
-/
instance [HasColimitsOfShape J C] : HasColimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J C] (n
  body: ⟨inferInstance⟩

中文:
实例 [HasColimitsOfShape
  签名: J C] (n
  定义体: ⟨inferInstance⟩
-/
noncomputable instance [HasColimitsOfShape J C] (n : ι) :
    PreservesColimitsOfShape J (eval C c n) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] : HasFiniteColimits (HomologicalComplex C c)
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 [HasFiniteColimits
  签名: C] : HasFiniteColimits (HomologicalComplex C c)
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance [HasFiniteColimits C] : HasFiniteColimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] (n
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 [HasFiniteColimits
  签名: C] (n
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance [HasFiniteColimits C] (n : ι) :
    PreservesFiniteColimits (eval C c n) := ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] {K L
  body: by
  change Epi ((HomologicalComplex.eval C c n).map φ)
  infer_instance

中文:
实例 [HasFiniteColimits
  签名: C] {K L
  定义体: by
  change Epi ((HomologicalComplex.eval C c n).map φ)
  infer_instance

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, infer_instance
-/
instance [HasFiniteColimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Epi φ] (n : ι) :
    Epi (φ.f n) := by
  change Epi ((HomologicalComplex.eval C c n).map φ)
  infer_instance

/--
lemma `preservesLimitsOfShape_of_eval` / 引理 `preservesLimitsOfShape_of_eval`

English:
lemma preservesLimitsOfShape_of_eval
  statement: {D : Type*} [Category* D]
  proof: ⟨fun {_} => ⟨fun hs => ⟨isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

中文:
引理 preservesLimitsOfShape_of_eval
  结论: {D : 类型} [Category* D]
  证明: ⟨fun {_} => ⟨fun hs => ⟨isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

Depends on / 依赖: isLimitOfEval, isLimitOfPreserves
-/
lemma preservesLimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : forall (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) :
    PreservesLimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs => ⟨isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

/--
lemma `preservesColimitsOfShape_of_eval` / 引理 `preservesColimitsOfShape_of_eval`

English:
lemma preservesColimitsOfShape_of_eval
  statement: {D : Type*} [Category* D]
  proof: ⟨fun {_} => ⟨fun hs => ⟨isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

中文:
引理 preservesColimitsOfShape_of_eval
  结论: {D : 类型} [Category* D]
  证明: ⟨fun {_} => ⟨fun hs => ⟨isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

Depends on / 依赖: isColimitOfEval, isColimitOfPreserves
-/
lemma preservesColimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : forall (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c i)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs => ⟨isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

section

variable [HasZeroObject C] [DecidableEq ι] (i : ι)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (single C c i)
  body: preservesLimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesLimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

中文:
实例 :
  签名: PreservesLimitsOfShape J (single C c i)
  定义体: preservesLimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesLimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

Depends on / 依赖: Functor, Functor.preservesLimitsOfShape_of_isZero, isZero_single_comp_eval, preservesLimitsOfShape_of_eval, preservesLimitsOfShape_of_isZero, preservesLimitsOfShape_of_natIso, singleCompEvalIsoSelf
-/
noncomputable instance : PreservesLimitsOfShape J (single C c i) :=
  preservesLimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesLimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (single C c i)
  body: preservesColimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesColimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

中文:
实例 :
  签名: PreservesColimitsOfShape J (single C c i)
  定义体: preservesColimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesColimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

Depends on / 依赖: Functor, Functor.preservesColimitsOfShape_of_isZero, isZero_single_comp_eval, preservesColimitsOfShape_of_eval, preservesColimitsOfShape_of_isZero, preservesColimitsOfShape_of_natIso, singleCompEvalIsoSelf
-/
noncomputable instance : PreservesColimitsOfShape J (single C c i) :=
  preservesColimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesColimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (single C c i)
  body: ⟨by intros; infer_instance⟩

中文:
实例 :
  签名: PreservesFiniteLimits (single C c i)
  定义体: ⟨by intros; infer_instance⟩

Depends on / 依赖: infer_instance, intros
-/
noncomputable instance : PreservesFiniteLimits (single C c i) := ⟨by intros; infer_instance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (single C c i)
  body: ⟨by intros; infer_instance⟩

中文:
实例 :
  签名: PreservesFiniteColimits (single C c i)
  定义体: ⟨by intros; infer_instance⟩

Depends on / 依赖: infer_instance, intros
-/
noncomputable instance : PreservesFiniteColimits (single C c i) := ⟨by intros; infer_instance⟩

end

end HomologicalComplex
