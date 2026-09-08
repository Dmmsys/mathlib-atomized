/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Chosen finite products in `GrpCat` and friends
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory ConcreteCategory

universe u

namespace GrpCat

/-- Construct limit data for a binary product in `GrpCat`, using `GrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/-
**GrpCat.binaryProductLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：binaryProductLimitCone (G H : GrpCat.{u}) : LimitCone (pair G H) where con
e
参数：G H : GrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct limit data for a binary product in `GrpCat`, using `GrpCat.of (G × H)`
-/
def binaryProductLimitCone (G H : GrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `GrpCat.of (G × H)` as the product of `G` and `H` and `GrpCat.of PUnit` as
the terminal object. -/
/-
**GrpCat.cartesianMonoidalCategoryGrp** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
形式化陈述：cartesianMonoidalCategoryGrp : CartesianMonoidalCategory GrpCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We choose `GrpCat.of (G × H)` as the product of `G` and `H` and `GrpCat.of PUnit
` as
the terminal object.
-/
noncomputable instance cartesianMonoidalCategoryGrp : CartesianMonoidalCategory GrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (GrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : BraidedCategory GrpCat.{u} := .ofCartesianMonoidalCategory
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (forget GrpCat.{u}).Braided := .ofChosenFiniteProducts _
/-
**GrpCat.tensorObj_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：tensorObj_eq (G H : GrpCat.{u}) : (G otimes H) = of (G × H)
参数：G H : GrpCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_eq (G H : GrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
/-
**GrpCat.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_forget_apply {G H : GrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget GrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

end GrpCat

namespace AddGrpCat

/-- Construct limit data for a binary product in `AddGrpCat`, using `AddGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/-
**AddGrpCat.binaryProductLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `AddGrpCat`。
形式化陈述：binaryProductLimitCone (G H : AddGrpCat.{u}) : LimitCone (pair G H) where 
cone
参数：G H : AddGrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct limit data for a binary product in `AddGrpCat`, using `AddGrpCat.of (G
 × H)`
-/
def binaryProductLimitCone (G H : AddGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `AddGrpCat.of (G × H)` as the product of `G` and `H` and `AddGrpCat.of PUnit` as
the terminal object. -/
/-
**AddGrpCat.cartesianMonoidalCategoryAddGrp** 是 Mathlib 中的一个实例，位于命名空间 `AddGrpCat
`。
形式化陈述：cartesianMonoidalCategoryAddGrp : CartesianMonoidalCategory AddGrpCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We choose `AddGrpCat.of (G × H)` as the product of `G` and `H` and `AddGrpCat.of
 PUnit` as
the terminal object.
-/
noncomputable instance cartesianMonoidalCategoryAddGrp : CartesianMonoidalCategory AddGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H
/-
**AddGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : BraidedCategory AddGrpCat.{u} := .ofCartesianMonoidalCategory
/-
**AddGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (forget AddGrpCat.{u}).Braided := .ofChosenFiniteProducts _
/-
**AddGrpCat.tensorObj_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddGrpCat`。
形式化陈述：tensorObj_eq (G H : AddGrpCat.{u}) : (G otimes H) = of (G × H)
参数：G H : AddGrpCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_eq (G H : AddGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
/-
**AddGrpCat.** 是 Mathlib 中的一个定理，位于命名空间 `AddGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_forget_apply {G H : AddGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

end AddGrpCat

namespace CommGrpCat

/-- Construct limit data for a binary product in `CommGrpCat`, using `CommGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/-
**CommGrpCat.binaryProductLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat`。
形式化陈述：binaryProductLimitCone (G H : CommGrpCat.{u}) : LimitCone (pair G H) where
 cone
参数：G H : CommGrpCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct limit data for a binary product in `CommGrpCat`, using `CommGrpCat.of 
(G × H)`
-/
def binaryProductLimitCone (G H : CommGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `CommGrpCat.of (G × H)` as the product of `G` and `H` and `CommGrpCat.of PUnit` as
the terminal object. -/
/-
**CommGrpCat.cartesianMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
形式化陈述：cartesianMonoidalCategory : CartesianMonoidalCategory CommGrpCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We choose `CommGrpCat.of (G × H)` as the product of `G` and `H` and `CommGrpCat.
of PUnit` as
the terminal object.
-/
noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory CommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : BraidedCategory CommGrpCat.{u} := .ofCartesianMonoidalCategory
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (forget CommGrpCat.{u}).Braided := .ofChosenFiniteProducts _
/-
**CommGrpCat.tensorObj_eq** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：tensorObj_eq (G H : CommGrpCat.{u}) : (G otimes H) = of (G × H)
参数：G H : CommGrpCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_eq (G H : CommGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
/-
**CommGrpCat.** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_forget_apply {G H : CommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget CommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

end CommGrpCat

namespace AddCommGrpCat

/-- We choose `AddCommGrpCat.of (G × H)` as the product of `G` and `H` and
`AddCommGrpCat.of PUnit` as the terminal object. -/
@[instance_reducible]
/-
**AddCommGrpCat.cartesianMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpC
at`。
形式化陈述：cartesianMonoidalCategory : CartesianMonoidalCategory AddCommGrpCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We choose `AddCommGrpCat.of (G × H)` as the product of `G` and `H` and
`AddCommGrpCat.of PUnit` as the terminal object.
-/
noncomputable def cartesianMonoidalCategory : CartesianMonoidalCategory AddCommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

attribute [local instance] cartesianMonoidalCategory
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : BraidedCategory AddCommGrpCat.{u} := .ofCartesianMonoidalCategory
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (forget AddCommGrpCat.{u}).Braided := .ofChosenFiniteProducts _
/-
**AddCommGrpCat.tensorObj_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：tensorObj_eq (G H : AddCommGrpCat.{u}) : (G otimes H) = of (G × H)
参数：G H : AddCommGrpCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_eq (G H : AddCommGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
/-
**AddCommGrpCat.** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_forget_apply {G H : AddCommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddCommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X ↦ X) (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

end AddCommGrpCat

