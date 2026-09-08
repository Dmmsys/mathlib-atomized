/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Cylinders

We introduce a notion of cylinder for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `π : I ⟶ A` equipped with two sections
`i₀` and `i₁`. This notion shall be important in the definition of "left homotopies"
in model categories.

## Implementation notes

The most important definition in this file is `Cylinder A`. This structure
extends another structure `Precylinder A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of cylinders are stated as typeclasses `Cylinder.IsGood`
and `Cylinder.IsVeryGood`.

The existence of very good cylinder objects in model categories is stated
in the lemma `Cylinder.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A precylinder for `A : C` is the data of a morphism
`π : I ⟶ A` equipped with two sections. -/
/-
**HomotopicalAlgebra.Precylinder** 是 Mathlib 中的一个结构，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：Precylinder (A : C) where /-- the underlying object of a (pre)cylinder -/ 
I : C /-- the first "inclusion" in the (pre)cylinder -/ i₀ : A ⟶ I /-- the secon
d "inclusion" in the (pre)cylinder -/ i₁ : A ⟶ I /-- the codiagonal of the (pre)
cylinder -/ π : I ⟶ A i₀_π : i₀ ≫ π = 𝟙 A
参数：A : C；pre。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precylinder for `A : C` is the data of a morphism
`π : I ⟶ A` equipped with two sections.
-/
structure Precylinder (A : C) where
  /-- the underlying object of a (pre)cylinder -/
  I : C
  /-- the first "inclusion" in the (pre)cylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the (pre)cylinder -/
  i₁ : A ⟶ I
  /-- the codiagonal of the (pre)cylinder -/
  π : I ⟶ A
  i₀_π : i₀ ≫ π = 𝟙 A := by cat_disch
  i₁_π : i₁ ≫ π = 𝟙 A := by cat_disch

namespace Precylinder

attribute [reassoc (attr := simp)] i₀_π i₁_π

variable {A : C} (P : Precylinder A)

/-- The precylinder object obtained by switching the two inclusions. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.symm** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.Precylinder`。
形式化陈述：symm : Precylinder A where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precylinder object obtained by switching the two inclusions.
-/
def symm : Precylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two precylinders. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.trans** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlg
ebra.Precylinder`。
形式化陈述：trans (P' : Precylinder A) [HasPushout P.i₁ P'.i₀] : Precylinder A where I
参数：P' : Precylinder A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing of two precylinders.
-/
noncomputable def trans (P' : Precylinder A) [HasPushout P.i₁ P'.i₀] :
    Precylinder A where
  I := pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)

section

variable [HasBinaryCoproduct A A]

/-- the map from the coproduct of two copies of `A` to `P.I`, when `P` is
a cylinder object for `A`. `P` shall be a *good* cylinder object
when this morphism is a cofibration. -/
/-
**HomotopicalAlgebra.Precylinder.i** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra
.Precylinder`。
形式化陈述：i : A ⨿ A ⟶ P.I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the map from the coproduct of two copies of `A` to `P.I`, when `P` is
a cylinder object for `A`. `P` shall be a *good* cylinder object
when this morphism is a cofibration.
-/
noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.Precylinder.inl_i** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlg
ebra.Precylinder`。
形式化陈述：inl_i : coprod.inl ≫ P.i = P.i₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.Precylinder.inr_i** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlg
ebra.Precylinder`。
形式化陈述：inr_i : coprod.inr ≫ P.i = P.i₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

end

@[simp, reassoc]
/-
**HomotopicalAlgebra.Precylinder.symm_i** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAl
gebra.Precylinder`。
形式化陈述：symm_i [HasBinaryCoproducts C] : P.symm.i = (coprod.braiding A A).hom ≫ P.
i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.braiding_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts 
C]   (P Q : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomotopicalAlgebra.Precylinder.inr_i`：inr_i : coprod.inr ≫ P.i = P.i₁
· 使用引理 `HomotopicalAlgebra.Precylinder.inl_i`：inl_i : coprod.inl ≫ P.i = P.i₀
-/
lemma symm_i [HasBinaryCoproducts C] : P.symm.i = (coprod.braiding A A).hom ≫ P.i := by cat_disch

/-- The precylinder in a full subcategory of `C` induced by a precylinder
in the category `C`. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.toFullSubcategory** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.Precylinder`。
形式化陈述：toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : Prec
ylinder X.obj) (hQ : P Q.I) : Precylinder X where I
参数：Q : Precylinder X.obj；hQ : P Q.I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precylinder in a full subcategory of `C` induced by a precylinder
in the category `C`.
-/
def toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : Precylinder X.obj)
    (hQ : P Q.I) :
    Precylinder X where
  I := ⟨Q.I, hQ⟩
  i₀ := P.homMk Q.i₀
  i₁ := P.homMk Q.i₁
  π := P.homMk Q.π

/-- The image of a precylinder by a functor. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.map** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgeb
ra.Precylinder`。
形式化陈述：map {X : C} (P : Precylinder X) {D : Type*} [Category* D] (F : C ⥤ D) : Pr
ecylinder (F.obj X) where I
参数：P : Precylinder X；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a precylinder by a functor.
-/
def map {X : C} (P : Precylinder X) {D : Type*} [Category* D] (F : C ⥤ D) :
    Precylinder (F.obj X) where
  I := F.obj P.I
  i₀ := F.map P.i₀
  i₁ := F.map P.i₁
  π := F.map P.π
  i₀_π := by simp [← F.map_comp]
  i₁_π := by simp [← F.map_comp]

end Precylinder

/-- In a category with weak equivalences, a cylinder is the
data of a weak equivalence `π : I ⟶ A` equipped with two sections -/
/-
**HomotopicalAlgebra.Cylinder** 是 Mathlib 中的一个结构，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：Cylinder [CategoryWithWeakEquivalences C] (A : C) extends Precylinder A wh
ere weakEquivalence_π : WeakEquivalence π
参数：A : C。
继承自：Precylinder A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with weak equivalences, a cylinder is the
data of a weak equivalence `π : I ⟶ A` equipped with two sections
-/
structure Cylinder [CategoryWithWeakEquivalences C] (A : C) extends Precylinder A where
  weakEquivalence_π : WeakEquivalence π := by infer_instance

namespace Cylinder

attribute [instance] weakEquivalence_π

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : Cylinder A)

set_option backward.defeqAttrib.useBackward true in
/-- The cylinder object obtained by switching the two inclusions. -/
@[simps!]
/-
**HomotopicalAlgebra.Cylinder.symm** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra
.Cylinder`。
形式化陈述：symm : Cylinder A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cylinder object obtained by switching the two inclusions.
-/
def symm : Cylinder A where
  __ := P.toPrecylinder.symm
  weakEquivalence_π := by dsimp; infer_instance

@[simp, reassoc]
/-
**HomotopicalAlgebra.Cylinder.symm_i** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgeb
ra.Cylinder`。
形式化陈述：symm_i [HasBinaryCoproducts C] : P.symm.i = (coprod.braiding A A).hom ≫ P.
i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.Precylinder.symm_i`：symm_i [HasBinaryCoproducts C] : 
P.symm.i = (coprod.braiding A A).hom ≫ P.i
-/
lemma symm_i [HasBinaryCoproducts C] :
    P.symm.i = (coprod.braiding A A).hom ≫ P.i :=
  P.toPrecylinder.symm_i

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac P.i₀_π
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac P.i₁_π

end

/-- A cylinder object `P` is good if the morphism
`P.i : A ⨿ A ⟶ P.I` is a cofibration. -/
/-
**HomotopicalAlgebra.Cylinder.IsGood** 是 Mathlib 中的一个类，位于命名空间 `HomotopicalAlgebr
a.Cylinder`。
形式化陈述：IsGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C] : Prop where 
cofibration_i : Cofibration P.i
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cylinder object `P` is good if the morphism
`P.i : A ⨿ A ⟶ P.I` is a cofibration.
-/
class IsGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C] : Prop where
  cofibration_i : Cofibration P.i := by infer_instance

/-- A good cylinder object `P` is very good if `P.π` is a (trivial) fibration. -/
/-
**HomotopicalAlgebra.Cylinder.IsVeryGood** 是 Mathlib 中的一个类，位于命名空间 `HomotopicalAl
gebra.Cylinder`。
形式化陈述：IsVeryGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C] [Category
WithFibrations C] : Prop extends P.IsGood where fibration_π : Fibration P.π
继承自：P.IsGood。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A good cylinder object `P` is very good if `P.π` is a (trivial) fibration.
-/
class IsVeryGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
    [CategoryWithFibrations C] : Prop extends P.IsGood where
  fibration_π : Fibration P.π := by infer_instance

attribute [instance] IsGood.cofibration_i IsVeryGood.fibration_π

section

variable [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  [HasInitial C] [(cofibrations C).IsStableUnderComposition]
  [(cofibrations C).IsStableUnderCobaseChange]
  [IsCofibrant A] [P.IsGood]

/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Cofibration P.i₀ := by
  rw [← P.inl_i]
  infer_instance
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Cofibration P.i₁ := by
  rw [← P.inr_i]
  infer_instance
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCofibrant P.I :=
  isCofibrant_of_cofibration P.i₀

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryCoproducts C] [CategoryWithCofibrations C] [P.IsGood]
    [(cofibrations C).RespectsIso] : P.symm.IsGood where
  cofibration_i := by
    have hi : cofibrations C P.i := by rw [← cofibration_iff]; infer_instance
    rw [P.symm_i, cofibration_iff]
    refine ((cofibrations C).arrow_mk_iso_iff ?_).2 hi
    exact Arrow.isoMk (coprod.braiding A A) (Iso.refl _)

section

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [(fibrations C).IsStableUnderComposition]

/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryCoproduct A A] [HasTerminal C] [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I :=
  isFibrant_of_fibration P.π

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).RespectsIso] [HasBinaryCoproducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  fibration_π := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : Cylinder A)

section

variable (h : MorphismProperty.MapFactorizationData (cofibrations C) (trivialFibrations C)
    (codiag A))

set_option backward.isDefEq.respectTransparency false in
/-- A cylinder object for `A` can be obtained from a factorization of the obvious
map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration. -/
@[simps]
/-
**HomotopicalAlgebra.Cylinder.ofFactorizationData** 是 Mathlib 中的一个定义，位于命名空间 `Hom
otopicalAlgebra.Cylinder`。
形式化陈述：ofFactorizationData : Cylinder A where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cylinder object for `A` can be obtained from a factorization of the obvious
map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration.
-/
noncomputable def ofFactorizationData : Cylinder A where
  I := h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

@[simp]
/-
**HomotopicalAlgebra.Cylinder.ofFactorizationData_i** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra.Cylinder`。
形式化陈述：ofFactorizationData_i : (ofFactorizationData h).i = h.i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HomotopicalAlgebra.Precylinder.inl_i`：inl_i : coprod.inl ≫ P.i = P.i₀
· 使用定理 `HomotopicalAlgebra.Cylinder.ofFactorizationData_i₀`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory 
C] {A : C}   (h :     (HomotopicalAlgebr…
· 使用引理 `HomotopicalAlgebra.Precylinder.inr_i`：inr_i : coprod.inr ≫ P.i = P.i₁
· 使用定理 `HomotopicalAlgebra.Cylinder.ofFactorizationData_i₁`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory 
C] {A : C}   (h :     (HomotopicalAlgebr…
-/
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by cat_disch

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ofFactorizationData h).IsVeryGood where
  cofibration_i := by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasTerminal C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
    IsFibrant (ofFactorizationData h).I :=
  isFibrant_of_fibration (ofFactorizationData h).π

end

variable (A) in
/-
**HomotopicalAlgebra.Cylinder.exists_very_good** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra.Cylinder`。
形式化陈述：exists_very_good : exists (P : Cylinder A), P.IsVeryGood
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.cofibrations C).…
· 使用定理 `HomotopicalAlgebra.Cylinder.instIsVeryGoodOfFactorizationData`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Mod
elCategory C] {A : C}   (h :     (HomotopicalAlgebr…
-/
lemma exists_very_good :
    ∃ (P : Cylinder A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Cylinder A) := ⟨(exists_very_good A).choose⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two good cylinders. -/
@[simps!]
/-
**HomotopicalAlgebra.Cylinder.trans** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebr
a.Cylinder`。
形式化陈述：trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] : Cylinder A where _
_
参数：P P' : Cylinder A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing of two good cylinders.
-/
noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] :
    Cylinder A where
  __ := P.toPrecylinder.trans P'.toPrecylinder
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Precylinder.i₀_π]
      infer_instance
    dsimp
    apply weakEquivalence_of_precomp (P.i₀ ≫ pushout.inl _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.Cylinder.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.Cyl
inder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofibrant A] (P P' : Cylinder A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  cofibration_i := by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i, ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condition]
      · simp [ψ]
    have sq : IsPushout P.i₁ (coprod.inl ≫ P'.i) (coprod.inl ≫ ψ) (pushout.inr _ _) := by
      simpa [ψ] using IsPushout.of_hasPushout P.i₁ P'.i₀
    have : Cofibration ψ := by
      rw [cofibration_iff]
      exact (cofibrations C).of_isPushout
        (IsPushout.of_top sq fac (IsPushout.of_coprod_inl_with_id P.i₁ A).flip)
        (by rw [← cofibration_iff]; infer_instance)
    infer_instance

end Cylinder

end HomotopicalAlgebra

