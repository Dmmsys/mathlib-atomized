/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Single functors from the homotopy category

Let `C` be a preadditive category with a zero object.
In this file, we put together all the single functors `C ⥤ CochainComplex C ℤ`
along with their compatibilities with shifts into the definition
`CochainComplex.singleFunctors C : SingleFunctors C (CochainComplex C ℤ) ℤ`.
Similarly, we define
`HomotopyCategory.singleFunctors C : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe v' u' v u

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

open HomologicalComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `singleFunctors` / `singleFunctors` 的定义

English:
definition singleFunctors
  signature: : SingleFunctors C (CochainComplex C Int) Int where
  body: single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by lia
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsim

中文:
定义 singleFunctors
  签名: : SingleFunctors C (上链复形 C 整数) 整数 where
  定义体: single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by lia
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsim

Depends on / 依赖: single
-/
noncomputable def singleFunctors : SingleFunctors C (CochainComplex C Int) Int where
  functor n := single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by lia
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsimp [single]
          rw [if_neg h]; rw [if_neg (fun h' => h (by lia))])))
    (fun {X Y} f => by
      obtain rfl : a' = a + n := by lia
      ext
      simp [single])
  shiftIso_zero a := by
    ext
    dsimp
    simp only [single, shiftFunctorZero_eq, shiftFunctorZero'_hom_app_f,
      XIsoOfEq, eqToIso.hom]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext
    dsimp
    simp only [shiftFunctorAdd_eq, shiftFunctorAdd'_hom_app_f, XIsoOfEq,
      eqToIso.hom, eqToHom_trans, id_comp]

instance (n : Int) : ((singleFunctors C).functor n).Additive := by
  dsimp only [singleFunctors]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (R : Type*) [Ring R] (n : Int) [Linear R C] :
    Functor.Linear R ((singleFunctors C).functor n) where
  map_smul f r := by
    dsimp [CochainComplex.singleFunctors, HomologicalComplex.single]
    aesop

/--
Definition of `singleFunctor` / `singleFunctor` 的定义

English:
abbreviation singleFunctor
  signature: (n : Int)
  body: (singleFunctors C).functor n

中文:
缩写 singleFunctor
  签名: (n : 整数)
  定义体: (singleFunctors C).functor n

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, LeftHomologyMapData, LeftHomologyMapData.ofEpiOfIsIsoOfMono, _comp, comp_id, functor, infer_instance, leftHomologyMap, ofEpiOfIsIsoOfMono, singleFunctors
-/
noncomputable abbrev singleFunctor (n : Int) := (singleFunctors C).functor n

variable {C} in
@[simp]
/--
lemma `singleFunctor_obj_d` / 引理 `singleFunctor_obj_d`

English:
lemma singleFunctor_obj_d
  given: (X : C) (n p q : Int)
  proof: rfl

中文:
引理 singleFunctor_obj_d
  条件: (X : C) (n p q : 整数)
  证明: rfl

Depends on / 依赖: infer_instance, leftHomologyMap
-/
lemma singleFunctor_obj_d (X : C) (n p q : Int) :
    ((singleFunctor C n).obj X).d p q = 0 := rfl

instance (n : Int) : (singleFunctor C n).Full :=
  inferInstanceAs (single _ _ _).Full

instance (n : Int) : (singleFunctor C n).Faithful :=
  inferInstanceAs (single _ _ _).Faithful

end CochainComplex

section

variable {C} {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
Definition of `CategoryTheory.Functor.mapCochainComplexSingleFunctor` / `CategoryTheory.Functor.mapCochainComplexSingleFunctor` 的定义

English:
definition CategoryTheory.Functor.mapCochainComplexSingleFunctor
  signature: (n : Int)
  body: HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n

中文:
定义 范畴论.函子.mapCochainComplexSingleFunctor
  签名: (n : 整数)
  定义体: HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.singleMapHomologicalComplex, singleMapHomologicalComplex
-/
noncomputable def CategoryTheory.Functor.mapCochainComplexSingleFunctor (n : Int) :
    CochainComplex.singleFunctor C n ⋙ F.mapHomologicalComplex (ComplexShape.up Int) ≅
      F ⋙ CochainComplex.singleFunctor D n :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n

end

namespace HomotopyCategory

/--
Definition of `singleFunctors` / `singleFunctors` 的定义

English:
definition singleFunctors
  signature: : SingleFunctors C (HomotopyCategory C (ComplexShape.up Int)) Int
  body: (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

中文:
定义 singleFunctors
  签名: : SingleFunctors C (HomotopyCategory C (余mplexShape.up 整数)) 整数
  定义体: (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctors, HomotopyCategory, HomotopyCategory.quotient, postcomp, quotient, singleFunctors
-/
noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up Int)) Int :=
  (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

/--
Definition of `singleFunctor` / `singleFunctor` 的定义

English:
abbreviation singleFunctor
  signature: (n : Int)
  body: (singleFunctors C).functor n

中文:
缩写 singleFunctor
  签名: (n : 整数)
  定义体: (singleFunctors C).functor n

Depends on / 依赖: functor, singleFunctors
-/
noncomputable abbrev singleFunctor (n : Int) :
    C ⥤ HomotopyCategory C (ComplexShape.up Int) :=
  (singleFunctors C).functor n

instance (n : Int) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor, singleFunctors, SingleFunctors.postcomp]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQuotientIso`.
/--
theorem `quotient_obj_singleFunctors_obj` / 定理 `quotient_obj_singleFunctors_obj`

English:
theorem quotient_obj_singleFunctors_obj
  given: (n : Int) (X : C)
  proof: rfl

中文:
定理 quotient_obj_singleFunctors_obj
  条件: (n : 整数) (X : C)
  证明: rfl
-/
@[simp] theorem quotient_obj_singleFunctors_obj (n : Int) (X : C) :
    (HomotopyCategory.quotient C (ComplexShape.up Int)).obj
      ((CochainComplex.singleFunctor C n).obj X) =
        (HomotopyCategory.singleFunctor C n).obj X :=
  rfl

instance (R : Type*) [Ring R] [Linear R C] (n : Int) :
    Functor.Linear R (HomotopyCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (CochainComplex.singleFunctor C n ⋙
    HomotopyCategory.quotient _ _))

/--
Definition of `singleFunctorsPostcompQuotientIso` / `singleFunctorsPostcompQuotientIso` 的定义

English:
definition singleFunctorsPostcompQuotientIso
  signature: :
  body: Iso.refl _

中文:
定义 singleFunctorsPostcompQuotientIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def singleFunctorsPostcompQuotientIso :
    singleFunctors C ≅
      (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _) :=
  Iso.refl _

/--
Definition of `singleFunctorPostcompQuotientIso` / `singleFunctorPostcompQuotientIso` 的定义

English:
definition singleFunctorPostcompQuotientIso
  signature: (n : Int)
  body: (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

中文:
定义 singleFunctorPostcompQuotientIso
  签名: (n : 整数)
  定义体: (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

Depends on / 依赖: SingleFunctors, SingleFunctors.evaluation, evaluation, mapIso, singleFunctorsPostcompQuotientIso
-/
noncomputable def singleFunctorPostcompQuotientIso (n : Int) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ quotient _ _ :=
  (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

end HomotopyCategory
