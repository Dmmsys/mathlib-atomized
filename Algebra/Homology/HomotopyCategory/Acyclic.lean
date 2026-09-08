/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Localization

/-!
# The triangulated subcategory of acyclic complex in the homotopy category

In this file, we define the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of the homotopy category of
cochain complexes in an abelian category `C`.
In the lemma `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W` we obtain
that the class of quasiisomorphisms `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

/-- The triangulated subcategory of `HomotopyCategory C (ComplexShape.up ℤ)` consisting
of acyclic complexes. -/
/-
**HomotopyCategory.subcategoryAcyclic** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategor
y`。
形式化陈述：subcategoryAcyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up I
nt))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The triangulated subcategory of `HomotopyCategory C (ComplexShape.up ℤ)` consist
ing
of acyclic complexes.
-/
def subcategoryAcyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologicalKernel
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (subcategoryAcyclic C).IsTriangulated := by
  dsimp [subcategoryAcyclic]
  infer_instance
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (subcategoryAcyclic C).IsClosedUnderIsomorphisms := by
  dsimp [subcategoryAcyclic]
  infer_instance

variable {C}
/-
**HomotopyCategory.mem_subcategoryAcyclic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
yCategory`。
形式化陈述：mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up Int)) 
: subcategoryAcyclic C X ↔ forall (n : Int), IsZero ((homologyFunctor _ _ n).obj
 X)
参数：X : HomotopyCategory C (ComplexShape.up Int)。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用引理 `CategoryTheory.Functor.mem_homologicalKernel_iff`：mem_homologicalKernel_
iff [F.ShiftSequence Int] (X : C) : F.homologicalKernel X ↔ forall (n : Int), Is
Zero ((F.shift n).obj X)
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    subcategoryAcyclic C X ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X
/-
**HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt** 是 Mathlib 中
的一个引理，位于命名空间 `HomotopyCategory`。
形式化陈述：quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C Int)
 : subcategoryAcyclic C ((quotient _ _).obj K) ↔ forall (n : Int), K.ExactAt n
参数：K : CochainComplex C Int。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopyCategory.mem_subcategoryAcyclic_iff`：mem_subcategoryAcyclic_iff 
(X : HomotopyCategory C (ComplexShape.up Int)) : subcategoryAcyclic C X ↔ forall
 (n : Int), IsZero ((homologyFunc…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
-/
lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff
/-
**HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic** 是 Mathlib 中
的一个引理，位于命名空间 `HomotopyCategory`。
形式化陈述：quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C Int)
 : subcategoryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic
参数：K : CochainComplex C Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt`：quotie
nt_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C Int) : subcatego
ryAcyclic C ((quotient _ _).obj K) ↔ forall (n : Int),…
-/
lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C ℤ) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic :=
  quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

variable (C)
/-
**HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopyCategory`。
形式化陈述：quasiIso_eq_trW_subcategoryAcyclic : quasiIso C (ComplexShape.up Int) = (s
ubcategoryAcyclic C).trW
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Functor.mem_homologicalKernel_trW_iff`：mem_homologicalKer
nel_trW_iff {X Y : C} (f : X ⟶ Y) : F.homologicalKernel.trW f ↔ forall (n : Int)
, IsIso ((F.shift n).map f)
· 使用定理 `HomotopyCategory.instIsHomologicalIntUpHomologyFunctor`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C] (n : ℤ),   (HomotopyCategory.homologyFunc…
-/
lemma quasiIso_eq_trW_subcategoryAcyclic :
    quasiIso C (ComplexShape.up ℤ) = (subcategoryAcyclic C).trW := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up ℤ) 0).mem_homologicalKernel_trW_iff f).symm

@[deprecated (since := "2026-05-06")] alias quasiIso_eq_subcategoryAcyclic_W :=
  quasiIso_eq_trW_subcategoryAcyclic
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

end HomotopyCategory

