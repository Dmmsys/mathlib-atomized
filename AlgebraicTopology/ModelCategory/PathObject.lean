/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Path objects

We introduce a notion of path object for an object `A : C` in a model category.
It consists of an object `P`, a weak equivalence `ι : A ⟶ P` equipped with two retractions
`p₀` and `p₁`. This notion shall be important in the definition of "right homotopies"
in model categories.

This file dualizes the definitions in the file
`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean`.

## Implementation notes

The most important definition in this file is `PathObject A`. This structure
extends another structure `PrepathObject A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of path objects are stated as typeclasses `PathObject.IsGood`
and `PathObject.IsVeryGood`.

The existence of very good path objects in model categories is stated
in the lemma `PathObject.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/path+space+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A pre-path object for `A : C` is the data of a morphism
`ι : A ⟶ P` equipped with two retractions. -/
/-
**HomotopicalAlgebra.PrepathObject** 是 Mathlib 中的一个结构，位于命名空间 `HomotopicalAlgebra
`。
形式化陈述：PrepathObject (A : C) where /-- the underlying object of a (pre)path objec
t -/ P : C /-- the first "projection" from the (pre)path object -/ p₀ : P ⟶ A /-
- the second "projection" from the (pre)path object -/ p₁ : P ⟶ A /-- the diagon
al of the (pre)path object -/ ι : A ⟶ P ι_p₀ : ι ≫ p₀ = 𝟙 A
参数：A : C；pre。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pre-path object for `A : C` is the data of a morphism
`ι : A ⟶ P` equipped with two retractions.
-/
structure PrepathObject (A : C) where
  /-- the underlying object of a (pre)path object -/
  P : C
  /-- the first "projection" from the (pre)path object -/
  p₀ : P ⟶ A
  /-- the second "projection" from the (pre)path object -/
  p₁ : P ⟶ A
  /-- the diagonal of the (pre)path object -/
  ι : A ⟶ P
  ι_p₀ : ι ≫ p₀ = 𝟙 A := by aesop_cat
  ι_p₁ : ι ≫ p₁ = 𝟙 A := by aesop_cat

namespace PrepathObject

attribute [reassoc (attr := simp)] ι_p₀ ι_p₁

variable {A : C} (P : PrepathObject A)

/-- The pre-path object obtained by switching the two projections. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.symm** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAl
gebra.PrepathObject`。
形式化陈述：symm : PrepathObject A where P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-path object obtained by switching the two projections.
-/
def symm : PrepathObject A where
  P := P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two pre-path objects. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.trans** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalA
lgebra.PrepathObject`。
形式化陈述：trans (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀] : PrepathObject A wh
ere P
参数：P' : PrepathObject A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing of two pre-path objects.
-/
noncomputable def trans (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀] :
    PrepathObject A where
  P := pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)

section

variable [HasBinaryProduct A A]

/-- The map from `P.P` to the product of two copies of `A`, when `P` is
a pre-path object for `A`. `P` shall be a *good* path object
when this morphism is a fibration. -/
/-
**HomotopicalAlgebra.PrepathObject.p** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgeb
ra.PrepathObject`。
形式化陈述：p : P.P ⟶ A ⨯ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `P.P` to the product of two copies of `A`, when `P` is
a pre-path object for `A`. `P` shall be a *good* path object
when this morphism is a fibration.
-/
noncomputable def p : P.P ⟶ A ⨯ A := prod.lift P.p₀ P.p₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.PrepathObject.p_fst** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.PrepathObject`。
形式化陈述：p_fst : P.p ≫ prod.fst = P.p₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma p_fst : P.p ≫ prod.fst = P.p₀ := by simp [p]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.PrepathObject.p_snd** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.PrepathObject`。
形式化陈述：p_snd : P.p ≫ prod.snd = P.p₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma p_snd : P.p ≫ prod.snd = P.p₁ := by simp [p]

end

@[simp, reassoc]
/-
**HomotopicalAlgebra.PrepathObject.symm_p** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra.PrepathObject`。
形式化陈述：symm_p [HasBinaryProducts C] : P.symm.p = P.p ≫ (prod.braiding A A).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.braiding_hom`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (P Q : C) [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct P Q]   [inst_2 : Categor…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
-/
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom := by aesop_cat

/-- The pre-path object in a full subcategory of `C` induced by a pre-path object
in the category `C`. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.toFullSubcategory** 是 Mathlib 中的一个定义，位于命名空间 `
HomotopicalAlgebra.PrepathObject`。
形式化陈述：toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : Prep
athObject X.obj) (hQ : P Q.P) : PrepathObject X where P
参数：Q : PrepathObject X.obj；hQ : P Q.P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-path object in a full subcategory of `C` induced by a pre-path object
in the category `C`.
-/
def toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : PrepathObject X.obj)
    (hQ : P Q.P) :
    PrepathObject X where
  P := ⟨Q.P, hQ⟩
  p₀ := P.homMk Q.p₀
  p₁ := P.homMk Q.p₁
  ι := P.homMk Q.ι

/-- The image of a pre-path object by a functor. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.map** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlg
ebra.PrepathObject`。
形式化陈述：map {X : C} (P : PrepathObject X) {D : Type*} [Category* D] (F : C ⥤ D) : 
PrepathObject (F.obj X) where P
参数：P : PrepathObject X；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a pre-path object by a functor.
-/
def map {X : C} (P : PrepathObject X) {D : Type*} [Category* D] (F : C ⥤ D) :
    PrepathObject (F.obj X) where
  P := F.obj P.P
  p₀ := F.map P.p₀
  p₁ := F.map P.p₁
  ι := F.map P.ι
  ι_p₀ := by simp [← F.map_comp]
  ι_p₁ := by simp [← F.map_comp]

end PrepathObject

/-- In a category with weak equivalences, a path object is the
data of a weak equivalence `ι : A ⟶ P` equipped with two retractions. -/
/-
**HomotopicalAlgebra.PathObject** 是 Mathlib 中的一个结构，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：PathObject [CategoryWithWeakEquivalences C] (A : C) extends PrepathObject 
A where weakEquivalence_ι : WeakEquivalence ι
参数：A : C。
继承自：PrepathObject A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with weak equivalences, a path object is the
data of a weak equivalence `ι : A ⟶ P` equipped with two retractions.
-/
structure PathObject [CategoryWithWeakEquivalences C] (A : C) extends PrepathObject A where
  weakEquivalence_ι : WeakEquivalence ι := by infer_instance

namespace PathObject

attribute [instance] weakEquivalence_ι

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : PathObject A)

set_option backward.defeqAttrib.useBackward true in
/-- The path object obtained by switching the two projections. -/
@[simps!]
/-
**HomotopicalAlgebra.PathObject.symm** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgeb
ra.PathObject`。
形式化陈述：symm : PathObject A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path object obtained by switching the two projections.
-/
def symm : PathObject A where
  __ := P.toPrepathObject.symm
  weakEquivalence_ι := by dsimp; infer_instance

@[simp, reassoc]
/-
**HomotopicalAlgebra.PathObject.symm_p** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlg
ebra.PathObject`。
形式化陈述：symm_p [HasBinaryProducts C] : P.symm.p = P.p ≫ (prod.braiding A A).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.PrepathObject.symm_p`：symm_p [HasBinaryProducts C] : 
P.symm.p = P.p ≫ (prod.braiding A A).hom
-/
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom :=
  P.toPrepathObject.symm_p

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence P.p₀ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₀
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence P.p₁ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₁

end

/-- A path object `P` is good if the morphism
`P.p : P.P ⟶ A ⨯ A` is a fibration. -/
/-
**HomotopicalAlgebra.PathObject.IsGood** 是 Mathlib 中的一个类，位于命名空间 `HomotopicalAlge
bra.PathObject`。
形式化陈述：IsGood [HasBinaryProduct A A] [CategoryWithFibrations C] : Prop where fibr
ation_p : Fibration P.p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path object `P` is good if the morphism
`P.p : P.P ⟶ A ⨯ A` is a fibration.
-/
class IsGood [HasBinaryProduct A A] [CategoryWithFibrations C] : Prop where
  fibration_p : Fibration P.p := by infer_instance

/-- A good path object `P` is very good if `P.ι` is a (trivial) cofibration. -/
/-
**HomotopicalAlgebra.PathObject.IsVeryGood** 是 Mathlib 中的一个类，位于命名空间 `Homotopical
Algebra.PathObject`。
形式化陈述：IsVeryGood [HasBinaryProduct A A] [CategoryWithFibrations C] [CategoryWith
Cofibrations C] : Prop extends P.IsGood where cofibration_ι : Cofibration P.ι
继承自：P.IsGood。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A good path object `P` is very good if `P.ι` is a (trivial) cofibration.
-/
class IsVeryGood [HasBinaryProduct A A] [CategoryWithFibrations C]
    [CategoryWithCofibrations C] : Prop extends P.IsGood where
  cofibration_ι : Cofibration P.ι := by infer_instance

attribute [instance] IsGood.fibration_p IsVeryGood.cofibration_ι

section

variable [HasBinaryProduct A A] [CategoryWithFibrations C]
  [HasTerminal C] [(fibrations C).IsStableUnderComposition]
  [(fibrations C).IsStableUnderBaseChange]
  [IsFibrant A] [P.IsGood]

/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fibration P.p₀ := by
  rw [← P.p_fst]
  infer_instance
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fibration P.p₁ := by
  rw [← P.p_snd]
  infer_instance
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFibrant P.P :=
  isFibrant_of_fibration P.p₀

end

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryProducts C] [CategoryWithFibrations C] [P.IsGood]
    [(fibrations C).RespectsIso] : P.symm.IsGood where
  fibration_p := by
    have hp : fibrations C P.p := by rw [← fibration_iff]; infer_instance
    rw [P.symm_p, fibration_iff]
    refine ((fibrations C).arrow_mk_iso_iff ?_).2 hp
    exact Arrow.isoMk (Iso.refl _) (prod.braiding A A)

section

variable [CategoryWithFibrations C] [CategoryWithCofibrations C]
  [(cofibrations C).IsStableUnderComposition]

/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryProduct A A] [HasInitial C] [IsCofibrant A] [P.IsVeryGood] : IsCofibrant P.P :=
  isCofibrant_of_cofibration P.ι

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(fibrations C).RespectsIso] [HasBinaryProducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  cofibration_ι := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : PathObject A)

section

variable (h : MorphismProperty.MapFactorizationData
  (trivialCofibrations C) (fibrations C) (diag A))

set_option backward.isDefEq.respectTransparency false in
/-- A path object for `A` can be obtained from a factorization of the obvious
map `A ⟶ A ⨯ A` as a trivial cofibration followed by a fibration. -/
@[simps]
/-
**HomotopicalAlgebra.PathObject.ofFactorizationData** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopicalAlgebra.PathObject`。
形式化陈述：ofFactorizationData : PathObject A where P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path object for `A` can be obtained from a factorization of the obvious
map `A ⟶ A ⨯ A` as a trivial cofibration followed by a fibration.
-/
noncomputable def ofFactorizationData : PathObject A where
  P := h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

@[simp]
/-
**HomotopicalAlgebra.PathObject.ofFactorizationData_p** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.PathObject`。
形式化陈述：ofFactorizationData_p : (ofFactorizationData h).p = h.p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
· 使用定理 `HomotopicalAlgebra.PathObject.ofFactorizationData_p₀`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategor
y C] {A : C}   (h :     (HomotopicalAlgebr…
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用定理 `HomotopicalAlgebra.PathObject.ofFactorizationData_p₁`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategor
y C] {A : C}   (h :     (HomotopicalAlgebr…
-/
lemma ofFactorizationData_p : (ofFactorizationData h).p = h.p := by aesop_cat

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ofFactorizationData h).IsVeryGood where
  fibration_p := by simpa using inferInstanceAs (Fibration h.p)
  cofibration_ι := by dsimp; infer_instance
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasInitial C] [IsCofibrant A] [(cofibrations C).IsStableUnderComposition] :
    IsCofibrant (ofFactorizationData h).P :=
  isCofibrant_of_cofibration (ofFactorizationData h).ι

end

variable (A) in
/-
**HomotopicalAlgebra.PathObject.exists_very_good** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.PathObject`。
形式化陈述：exists_very_good : exists (P : PathObject A), P.IsVeryGood
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.trivialCofibrati…
· 使用定理 `HomotopicalAlgebra.PathObject.instIsVeryGoodOfFactorizationData`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.M
odelCategory C] {A : C}   (h :     (HomotopicalAlgebr…
-/
lemma exists_very_good :
    ∃ (P : PathObject A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (PathObject A) := ⟨(exists_very_good A).choose⟩

set_option backward.defeqAttrib.useBackward true in
/-- The gluing of two good path objects. -/
@[simps!]
/-
**HomotopicalAlgebra.PathObject.trans** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.PathObject`。
形式化陈述：trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] : PathObject A where
 __
参数：P P' : PathObject A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing of two good path objects.
-/
noncomputable def trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] :
    PathObject A where
  __ := P.toPrepathObject.trans P'.toPrepathObject
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫
        pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc, PrepathObject.ι_p₀]
      infer_instance
    dsimp
    apply weakEquivalence_of_postcomp _ (pullback.fst P.p₁ P'.p₀ ≫ P.p₀)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.PathObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra.P
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFibrant A] (P P' : PathObject A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  fibration_p := by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PrepathObject.p, ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condition]
      · simp [ψ]
    have sq : IsPullback (ψ ≫ prod.fst) (pullback.snd P.p₁ P'.p₀) P.p₁ (P'.p ≫ prod.fst) := by
      simpa [ψ] using IsPullback.of_hasPullback P.p₁ P'.p₀
    have : Fibration ψ := by
      rw [fibration_iff]
      exact (fibrations C).of_isPullback
        (IsPullback.of_right sq fac (IsPullback.of_prod_fst_with_id P.p₁ A)).flip
          (by rw [← fibration_iff]; infer_instance)
    infer_instance

end PathObject

/-- The opposite of a pre-path object is a precylinder object. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.op** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.PrepathObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : C} →
 HomotopicalAlgebra.PrepathObject A → HomotopicalAlgebra.Precylinder (Opposite.o
p A)
参数：Opposite.op A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a pre-path object is a precylinder object.
-/
protected def PrepathObject.op {A : C} (P : PrepathObject A) :
    Precylinder (op A) where
  I := op P.P
  i₀ := P.p₀.op
  i₁ := P.p₁.op
  π := P.ι.op
  i₀_π := Quiver.Hom.unop_inj (by simp)
  i₁_π := Quiver.Hom.unop_inj (by simp)

/-- The precylinder object obtained from a pre-path object in the opposite category. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.unop** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAl
gebra.PrepathObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : Cᵒᵖ}
 → HomotopicalAlgebra.PrepathObject A → HomotopicalAlgebra.Precylinder (Opposite
.unop A)
参数：Opposite.unop A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precylinder object obtained from a pre-path object in the opposite category.
-/
protected def PrepathObject.unop {A : Cᵒᵖ} (P : PrepathObject A) :
    Precylinder A.unop where
  I := P.P.unop
  i₀ := P.p₀.unop
  i₁ := P.p₁.unop
  π := P.ι.unop
  i₀_π := Quiver.Hom.op_inj (by simp)
  i₁_π := Quiver.Hom.op_inj (by simp)

/-- The opposite of a precylinder object is a pre-path object. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.op** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebr
a.Precylinder`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : C} →
 HomotopicalAlgebra.Precylinder A → HomotopicalAlgebra.PrepathObject (Opposite.o
p A)
参数：Opposite.op A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a precylinder object is a pre-path object.
-/
protected def Precylinder.op {A : C} (P : Precylinder A) :
    PrepathObject (op A) where
  P := op P.I
  p₀ := P.i₀.op
  p₁ := P.i₁.op
  ι := P.π.op
  ι_p₀ := Quiver.Hom.unop_inj (by simp)
  ι_p₁ := Quiver.Hom.unop_inj (by simp)

/-- The pre-path object object obtained from a cylinder in the opposite category. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.unop** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.Precylinder`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : Cᵒᵖ}
 → HomotopicalAlgebra.Precylinder A → HomotopicalAlgebra.PrepathObject (Opposite
.unop A)
参数：Opposite.unop A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-path object object obtained from a cylinder in the opposite category.
-/
protected def Precylinder.unop {A : Cᵒᵖ} (P : Precylinder A) :
    PrepathObject A.unop where
  P := P.I.unop
  p₀ := P.i₀.unop
  p₁ := P.i₁.unop
  ι := P.π.unop
  ι_p₀ := Quiver.Hom.op_inj (by simp)
  ι_p₁ := Quiver.Hom.op_inj (by simp)

end HomotopicalAlgebra

