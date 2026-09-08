/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Mathlib/Algebra/Homology/Localization.lean` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the file
`HomotopyCategory.Acyclic`, it was shown that this class of quasiisomorphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`)
using the localization theorem for triangulated categories which was obtained
in the file `Mathlib/CategoryTheory/Localization/Triangulated.lean`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
  of cochain complexes (done), and compare the associated connecting homomorphism
  with the one defined in `Algebra.Homology.HomologySequence`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

@[expose] public noncomputable section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The assumption that a localized category for
`(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that the morphisms
in this chosen category are in `Type w`. -/
/-
**HasDerivedCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HasDerivedCategory
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The assumption that a localized category for
`(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that 
the morphisms
in this chosen category are in `Type w`.
-/
abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The derived category obtained using the constructed localized category of cochain complexes
with respect to quasi-isomorphisms. This should be used only while proving statements
which do not involve the derived category. -/
@[instance_reducible]
/-
**HasDerivedCategory.standard** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasDerivedCategory.standard : HasDerivedCategory.{max u v} C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The derived category obtained using the constructed localized category of cochai
n complexes
with respect to quasi-isomorphisms. This should be used only while proving state
ments
which do not involve the derived category.
-/
def HasDerivedCategory.standard : HasDerivedCategory.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w} C]

/-- The derived category of an abelian category. -/
/-
**DerivedCategory** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DerivedCategory : Type (max u v)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The derived category of an abelian category.
-/
def DerivedCategory : Type (max u v) := HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)
deriving Category

namespace DerivedCategory

variable {C}

/-- The localization functor `CochainComplex C ℤ ⥤ DerivedCategory C`. -/
/-
**DerivedCategory.Q** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：Q : CochainComplex C Int ⥤ DerivedCategory C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The localization functor `CochainComplex C ℤ ⥤ DerivedCategory C`.
-/
def Q : CochainComplex C ℤ ⥤ DerivedCategory C := HomologicalComplexUpToQuasiIso.Q

set_option backward.isDefEq.respectTransparency false in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (Q.map f) :=
  Localization.inverts Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    (inferInstanceAs (QuasiIso f))

/-- The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`. -/
/-
**DerivedCategory.Qh** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：Qh : HomotopyCategory C (ComplexShape.up Int) ⥤ DerivedCategory C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCatego
ry C`.
-/
def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  HomologicalComplexUpToQuasiIso.Qh

variable (C) in
/-- The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q`. -/
/-
**DerivedCategory.quotientCompQhIso** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up Int) ⋙ Qh
 ≅ Q
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ 
Q`.
-/
def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up ℤ)

#adaptation_note /-- Prior to nightly-2026-05-07, the LHS of these statements was guarded with
`dsimp%`; it now reports `made no progress`, so we write the (already-reduced) form directly. -/
@[reassoc (attr := simp)]
/-
**DerivedCategory.quotientCompQhIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `De
rivedCategory`。
形式化陈述：quotientCompQhIso_hom_naturality {K L : CochainComplex C Int} (f : K ⟶ L) 
: Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ (quotientCompQhIso C).hom.app
 L = (quotientCompQhIso C).hom.app K ≫ Q.map f
参数：f : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G

--- 原说明 ---
Prior to nightly-2026-05-07, the LHS of these statements was guarded with
`dsimp%`; it now reports `made no progress`, so we write the (already-reduced) f
orm directly.
-/
lemma quotientCompQhIso_hom_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ (quotientCompQhIso C).hom.app L =
      (quotientCompQhIso C).hom.app K ≫ Q.map f :=
  (quotientCompQhIso C).hom.naturality f

@[reassoc]
/-
**DerivedCategory.quotientCompQhIso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `De
rivedCategory`。
形式化陈述：quotientCompQhIso_inv_naturality {K L : CochainComplex C Int} (f : K ⟶ L) 
: Q.map f ≫ (quotientCompQhIso C).inv.app L = (quotientCompQhIso C).inv.app K ≫ 
Qh.map ((HomotopyCategory.quotient _ _).map f)
参数：f : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma quotientCompQhIso_inv_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Q.map f ≫ (quotientCompQhIso C).inv.app L =
      (quotientCompQhIso C).inv.app K ≫ Qh.map ((HomotopyCategory.quotient _ _).map f) :=
  (quotientCompQhIso C).inv.naturality f

set_option backward.isDefEq.respectTransparency false in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW := by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Q (C := C)).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso (Qh.commShiftIso n)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Q : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)
/-
**DerivedCategory.mem_distTriang_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`
。
形式化陈述：mem_distTriang_iff (T : Triangle (DerivedCategory C)) : (T in distTriang (
DerivedCategory C)) ↔ exists (X Y : CochainComplex C Int) (f : X ⟶ Y), Nonempty 
(T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
参数：T : Triangle (DerivedCategory C)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `DerivedCategory.instCommShiftHomologicalComplexIntUpHomFunctorQuotientCo
mpQhIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Cate
goryTheory.Abelian C]   [inst_2 : HasDerivedCategory C], CategoryTheo…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `DerivedCategory.instIsTriangulatedHomotopyCategoryIntUpQh`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] 
  [inst_2 : HasDerivedCategory C], DerivedCateg…
-/
lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

section

open CochainComplex

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-
**DerivedCategory.mappingCone_triangle_distinguished** 是 Mathlib 中的一个引理，位于命名空间 `
DerivedCategory`。
形式化陈述：mappingCone_triangle_distinguished : DerivedCategory.Q.mapTriangle.obj (ma
ppingCone.triangle φ) in distTriang _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.mem_distTriang_iff`：mem_distTriang_iff (T : Triangle (De
rivedCategory C)) : (T in distTriang (DerivedCategory C)) ↔ exists (X Y : Cochai
nComplex C Int) (f : X ⟶…
-/
lemma mappingCone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle φ) ∈ distTriang _ := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩
/-
**DerivedCategory.mappingCocone_triangle_distinguished** 是 Mathlib 中的一个引理，位于命名空间
 `DerivedCategory`。
形式化陈述：mappingCocone_triangle_distinguished : DerivedCategory.Q.mapTriangle.obj (
mappingCocone.triangle φ) in distTriang _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pretriangulated.rotate_distinguished_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `DerivedCategory.mappingCone_triangle_distinguished`：mappingCone_triangle
_distinguished : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle φ) in d
istTriang _
· 使用定理 `DerivedCategory.instAdditiveCochainComplexIntQ`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 HasDerivedCategory C], DerivedCateg…
-/
lemma mappingCocone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ) ∈ distTriang _ := by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

end

variable (C)

/-- The single functors `C ⥤ DerivedCategory C` for all `n : ℤ` along with
their compatibilities with shifts. -/
/-
**DerivedCategory.singleFunctors** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：singleFunctors : SingleFunctors C (DerivedCategory C) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The single functors `C ⥤ DerivedCategory C` for all `n : ℤ` along with
their compatibilities with shifts.
-/
def singleFunctors : SingleFunctors C (DerivedCategory C) ℤ :=
  (HomotopyCategory.singleFunctors C).postcomp Qh

/-- The single functor `C ⥤ DerivedCategory C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
/-
**DerivedCategory.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：singleFunctor (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single functor `C ⥤ DerivedCategory C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`.
-/
abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

set_option backward.defeqAttrib.useBackward true in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQhIso`.
/-
**DerivedCategory.Qh_obj_singleFunctors_obj** 是 Mathlib 中的一个定理，位于命名空间 `DerivedCa
tegory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : HasDerivedCategory C] (n : ℤ) (X : C),   DerivedC
ategory.Qh.obj (((HomotopyCategory.singleFunctors C).functor n).obj X) =     (De
rivedCategory.singleFunctor C n).obj X
参数：C : Type u；n : ℤ；X : C；((HomotopyCategory.singleFunctors C).functor n).obj X；
DerivedCategory.singleFunctor C n。
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
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
@[simp] theorem Qh_obj_singleFunctors_obj (n : ℤ) (X : C) :
    Qh.obj (((HomotopyCategory.singleFunctors C).functor n).obj X) = (singleFunctor C n).obj X :=
  rfl
/-
**DerivedCategory.Q_obj_single_obj** 是 Mathlib 中的一个定理，位于命名空间 `DerivedCategory`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : HasDerivedCategory C] (n : ℤ) (X : C),   DerivedC
ategory.Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj X) =     
(DerivedCategory.singleFunctor C n).obj X
参数：C : Type u；n : ℤ；X : C；(HomologicalComplex.single C (ComplexShape.up ℤ) n).ob
j X；DerivedCategory.singleFunctor C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
@[simp] theorem Q_obj_single_obj (n : ℤ) (X : C) :
    Q.obj ((HomologicalComplex.single C _ n).obj X) = (singleFunctor C n).obj X :=
  rfl

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh` given
by the definition of `DerivedCategory.singleFunctors`. -/
/-
**DerivedCategory.singleFunctorsPostcompQhIso** 是 Mathlib 中的一个定义，位于命名空间 `Derived
Category`。
形式化陈述：singleFunctorsPostcompQhIso : singleFunctors C ≅ (HomotopyCategory.singleF
unctors C).postcomp Qh
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism
`DerivedCategory.singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp
 Qh` given
by the definition of `DerivedCategory.singleFunctors`.
-/
def singleFunctorsPostcompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh :=
  Iso.refl _

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q`. -/
/-
**DerivedCategory.singleFunctorsPostcompQIso** 是 Mathlib 中的一个定义，位于命名空间 `DerivedC
ategory`。
形式化陈述：singleFunctorsPostcompQIso : singleFunctors C ≅ (CochainComplex.singleFunc
tors C).postcomp Q
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `DerivedCategory.instCommShiftHomologicalComplexIntUpHomFunctorQuotientCo
mpQhIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Cate
goryTheory.Abelian C]   [inst_2 : HasDerivedCategory C], CategoryTheo…

--- 原说明 ---
The isomorphism
`DerivedCategory.singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q
`.
-/
def singleFunctorsPostcompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q :=
  (SingleFunctors.postcompFunctor C ℤ (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**DerivedCategory.singleFunctorsPostcompQIso_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `
DerivedCategory`。
形式化陈述：singleFunctorsPostcompQIso_hom_hom (n : Int) : (singleFunctorsPostcompQIso
 C).hom.hom n = 𝟙 _
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**DerivedCategory.singleFunctorsPostcompQIso_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `
DerivedCategory`。
形式化陈述：singleFunctorsPostcompQIso_inv_hom (n : Int) : (singleFunctorsPostcompQIso
 C).inv.hom n = 𝟙 _
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DerivedCategory.instCommShiftHomologicalComplexIntUpHomFunctorQuotientCo
mpQhIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Cate
goryTheory.Abelian C]   [inst_2 : HasDerivedCategory C], CategoryTheo…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

/-- The isomorphism `singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`. -/
/-
**DerivedCategory.singleFunctorIsoCompQ** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCatego
ry`。
形式化陈述：singleFunctorIsoCompQ (n : Int) : singleFunctor C n ≅ CochainComplex.singl
eFunctor C n ⋙ Q
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`.
-/
def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _
/-
**DerivedCategory.isIso_Q_map_iff_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCat
egory`。
形式化陈述：isIso_Q_map_iff_quasiIso {K L : CochainComplex C Int} (φ : K ⟶ L) : IsIso 
(Q.map φ) ↔ QuasiIso φ
参数：φ : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso`：isIso_Q_map
_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) : IsIso (Q.map f) ↔
 HomologicalComplex.quasiIso C c f
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso
/-
**DerivedCategory.Q_map_eq_of_homotopy** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategor
y`。
形式化陈述：Q_map_eq_of_homotopy {K L : CochainComplex C Int} {f g : K ⟶ L} (h : Homot
opy f g) : DerivedCategory.Q.map f = DerivedCategory.Q.map g
参数：h : Homotopy f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy`：Q_map_eq_of_homotop
y {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) : Q.map f = Q.
map g
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `instQFactorsThroughHomotopyIntUp`：∀ (C : Type u_1) [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [CategoryTheo
ry.Limits.HasBinaryBip…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
-/
lemma Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

end DerivedCategory

