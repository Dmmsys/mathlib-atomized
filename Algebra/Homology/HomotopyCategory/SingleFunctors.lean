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
/-- The collection of all single functors `C ⥤ CochainComplex C ℤ` along with
their compatibilities with shifts. (This definition has purposely no `simps`
attribute, as the generated lemmas would not be very useful.) -/
/-
**CochainComplex.singleFunctors** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：singleFunctors : SingleFunctors C (CochainComplex C Int) Int where functor
 n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def singleFunctors : SingleFunctors C (CochainComplex C ℤ) ℤ where
  functor n := single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by lia
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsimp [single]
          rw [if_neg h, if_neg (fun h' => h (by lia))])))
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
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : ((singleFunctors C).functor n).Additive := by
  dsimp only [singleFunctors]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Ring R] (n : ℤ) [Linear R C] :
    Functor.Linear R ((singleFunctors C).functor n) where
  map_smul f r := by
    dsimp [CochainComplex.singleFunctors, HomologicalComplex.single]
    aesop

/-- The single functor `C ⥤ CochainComplex C ℤ` which sends `X` to the complex
consisting of `X` in degree `n : ℤ` and zero otherwise.
(This is definitionally equal to `HomologicalComplex.single C (up ℤ) n`,
but `singleFunctor C n` is the preferred term when interactions with shifts are relevant.) -/
/-
**CochainComplex.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：singleFunctor (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single functor `C ⥤ CochainComplex C ℤ` which sends `X` to the complex
consisting of `X` in degree `n : ℤ` and zero otherwise.
(This is definitionally equal to `HomologicalComplex.single C (up ℤ) n`,
but `singleFunctor C n` is the preferred term when interactions with shifts are 
relevant.)
-/
noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

variable {C} in
@[simp]
/-
**CochainComplex.singleFunctor_obj_d** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：singleFunctor_obj_d (X : C) (n p q : Int) : ((singleFunctor C n).obj X).d 
p q = 0
参数：X : C；n p q : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma singleFunctor_obj_d (X : C) (n p q : ℤ) :
    ((singleFunctor C n).obj X).d p q = 0 := rfl
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Full :=
  inferInstanceAs (single _ _ _).Full
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Faithful :=
  inferInstanceAs (single _ _ _).Faithful

end CochainComplex

section

variable {C} {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- `CochainComplex.singleFunctor` commutes with `F` and `F.mapHomologicalComplex`. -/
/-
**CategoryTheory.Functor.mapCochainComplexSingleFunctor** 是 Mathlib 中的一个定义，位于命名空
间 ``。
形式化陈述：CategoryTheory.Functor.mapCochainComplexSingleFunctor (n : Int) : CochainC
omplex.singleFunctor C n ⋙ F.mapHomologicalComplex (ComplexShape.up Int) ≅ F ⋙ C
ochainComplex.singleFunctor D n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
`CochainComplex.singleFunctor` commutes with `F` and `F.mapHomologicalComplex`.
-/
noncomputable def CategoryTheory.Functor.mapCochainComplexSingleFunctor (n : ℤ) :
    CochainComplex.singleFunctor C n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F ⋙ CochainComplex.singleFunctor D n :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n

end

namespace HomotopyCategory

/-- The collection of all single functors `C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
for `n : ℤ` along with their compatibilities with shifts. -/
/-
**HomotopyCategory.singleFunctors** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up Int
)) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of all single functors `C ⥤ HomotopyCategory C (ComplexShape.up ℤ
)`
for `n : ℤ` along with their compatibilities with shifts.
-/
noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ :=
  (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

/-- The single functor `C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
which sends `X` to the complex consisting of `X` in degree `n : ℤ` and zero otherwise. -/
/-
**HomotopyCategory.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyCategory`。
形式化陈述：singleFunctor (n : Int) : C ⥤ HomotopyCategory C (ComplexShape.up Int)
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single functor `C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
which sends `X` to the complex consisting of `X` in degree `n : ℤ` and zero othe
rwise.
-/
noncomputable abbrev singleFunctor (n : ℤ) :
    C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  (singleFunctors C).functor n
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor, singleFunctors, SingleFunctors.postcomp]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQuotientIso`.
/-
**HomotopyCategory.quotient_obj_singleFunctors_obj** 是 Mathlib 中的一个定理，位于命名空间 `Ho
motopyCategory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroObject C] (n : ℤ
) (X : C),   (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj ((CochainComp
lex.singleFunctor C n).obj X) =     (HomotopyCategory.singleFunctor C n).obj X
参数：C : Type u；n : ℤ；X : C；HomotopyCategory.quotient C (ComplexShape.up ℤ)；(Cocha
inComplex.singleFunctor C n).obj X；HomotopyCategory.singleFunctor C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
@[simp] theorem quotient_obj_singleFunctors_obj (n : ℤ) (X : C) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C n).obj X) =
        (HomotopyCategory.singleFunctor C n).obj X :=
  rfl
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Ring R] [Linear R C] (n : ℤ) :
    Functor.Linear R (HomotopyCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (CochainComplex.singleFunctor C n ⋙
    HomotopyCategory.quotient _ _))

/-- The isomorphism given by the very definition of `singleFunctors C`. -/
/-
**HomotopyCategory.singleFunctorsPostcompQuotientIso** 是 Mathlib 中的一个定义，位于命名空间 `
HomotopyCategory`。
形式化陈述：singleFunctorsPostcompQuotientIso : singleFunctors C ≅ (CochainComplex.sin
gleFunctors C).postcomp (HomotopyCategory.quotient _ _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism given by the very definition of `singleFunctors C`.
-/
noncomputable def singleFunctorsPostcompQuotientIso :
    singleFunctors C ≅
      (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _) :=
  Iso.refl _

/-- `HomotopyCategory.singleFunctor C n` is induced by `CochainComplex.singleFunctor C n`. -/
/-
**HomotopyCategory.singleFunctorPostcompQuotientIso** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopyCategory`。
形式化陈述：singleFunctorPostcompQuotientIso (n : Int) : singleFunctor C n ≅ CochainCo
mplex.singleFunctor C n ⋙ quotient _ _
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomotopyCategory.singleFunctor C n` is induced by `CochainComplex.singleFunctor
 C n`.
-/
noncomputable def singleFunctorPostcompQuotientIso (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ quotient _ _ :=
  (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

end HomotopyCategory

