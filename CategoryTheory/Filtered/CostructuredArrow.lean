/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Inferring Filteredness from Filteredness of Costructured Arrow Categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8

-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits CategoryTheory.Functor

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isFiltered_of_isFiltered_costructuredArrow_small** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isFiltered_of_isFiltered_costructuredArrow_small (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    exact filtered_colim_preservesFiniteLimits
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

/-- Given functors `L : A ⥤ T` and `R : B ⥤ T` with a common codomain we can conclude that `A`
is filtered given that `R` is final, `B` is filtered and each costructured arrow category
`CostructuredArrow L (R.obj b)` is filtered. -/
/-
**CategoryTheory.isFiltered_of_isFiltered_costructuredArrow** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：isFiltered_of_isFiltered_costructuredArrow (L : A ⥤ T) (R : B ⥤ T) [IsFilt
ered B] [Final R] [forall b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFil
tered A
参数：L : A ⥤ T；R : B ⥤ T；CostructuredArrow L (R.obj b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.CostructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `_private.Mathlib.CategoryTheory.Filtered.CostructuredArrow.0.CategoryThe
ory.isFiltered_of_isFiltered_costructuredArrow_small`：∀ {A : Type u₁} [inst : Ca
tegoryTheory.SmallCategory A] {B : Type u₁} [inst_1 : CategoryTheory.SmallCatego
ry B]   {T : Type u₁} [inst_2 : Ca…
· 使用定理 `CategoryTheory.instIsFilteredAsSmall`：∀ (C : Type u) [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.IsFiltered C],   CategoryTheory.IsFiltere
d (CategoryTheory.AsSmall …
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
Given functors `L : A ⥤ T` and `R : B ⥤ T` with a common codomain we can conclud
e that `A`
is filtered given that `R` is final, `B` is filtered and each costructured arrow
 category
`CostructuredArrow L (R.obj b)` is filtered.
-/
theorem isFiltered_of_isFiltered_costructuredArrow (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : ∀ b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.functor).obj ⟨b⟩) ≌ CostructuredArrow L (R.obj b) := fun b =>
    (CostructuredArrow.pre sA.inverse (L ⋙ sT.functor) _).asEquivalence.trans
      (CostructuredArrow.post L sT.functor _).asEquivalence.symm
  have : ∀ b, IsFiltered (CostructuredArrow _ ((sB.inverse ⋙ R ⋙ sT.functor).obj b)) :=
    fun b => IsFiltered.of_equivalence (sC b.1).symm
  have := isFiltered_of_isFiltered_costructuredArrow_small
    (sA.inverse ⋙ L ⋙ sT.functor) (sB.inverse ⋙ R ⋙ sT.functor)
  exact IsFiltered.of_equivalence sA.symm

end CategoryTheory

