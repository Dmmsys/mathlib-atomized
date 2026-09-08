/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Cohomology of `HomComplex` and morphisms in the derived category

Let `K` and `L` be two cochain complexes in an abelian category `C`.
Given a class `x : HomComplex.CohomologyClass K L n`, we construct an
element in the type
`SmallShiftedHom (HomologicalComplex.quasiIso C (.up ℤ)) K L n`, and
compute its image as a morphism `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the
derived category when `x` is given as the class of a cocycle.

-/

@[expose] public section

universe w v u

open CategoryTheory Localization

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

/-- Given `x : CohomologyClass K L n`, this is the element in the type
`SmallShiftedHom` relatively to quasi-isomorphisms that is associated
to the `x`. -/
/-
**CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom** 是 Mathlib 中的一个定义
，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：toSmallShiftedHom (x : CohomologyClass K L n) : SmallShiftedHom.{w} (Homol
ogicalComplex.quasiIso C (.up Int)) K L n
参数：x : CohomologyClass K L n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
Given `x : CohomologyClass K L n`, this is the element in the type
`SmallShiftedHom` relatively to quasi-isomorphisms that is associated
to the `x`.
-/
noncomputable def toSmallShiftedHom (x : CohomologyClass K L n) :
    SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Quotient.lift (fun y ↦ SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    let := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono, DerivedCategory.Q_map_eq_of_homotopy]
    apply HomotopyCategory.homotopyOfEq
    rw [← toHom_mk, ← toHom_mk]
    congr 1
    exact Quotient.sound h) x
/-
**CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk** 是 Mathlib 中的一
个引理，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：toSmallShiftedHom_mk (x : Cocycle K L n) : (mk x).toSmallShiftedHom = Smal
lShiftedHom.mk _ (Cocycle.equivHomShift.symm x)
参数：x : Cocycle K L n。
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma toSmallShiftedHom_mk (x : Cocycle K L n) :
    (mk x).toSmallShiftedHom =
      SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x) := rfl

@[simp]
/-
**CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk** 是 Mathl
ib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.CohomologyClass`。
形式化陈述：equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) : Sm
allShiftedHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom = ShiftedHom.ma
p (Cocycle.equivHomShift.symm x) DerivedCategory.Q
参数：x : Cocycle K L n。
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_mk`：equiv_mk [HasSmall
LocalizedShiftedHom.{w} W M X Y] {m : M} (f : ShiftedHom X Y m) : equiv W L (.mk
 _ f) = f.map L
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) :
    SmallShiftedHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q := by
  simp [toSmallShiftedHom_mk]

end CochainComplex.HomComplex.CohomologyClass

