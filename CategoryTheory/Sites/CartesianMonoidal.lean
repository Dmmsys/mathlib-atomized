/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Chosen finite products on sheaves

In this file, we put a `CartesianMonoidalCategory` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a `CartesianMonoidalCategory` instance.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Category Limits Sieve MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [CartesianMonoidalCategory A]

namespace Sheaf
variable (X Y : Sheaf J A)

/-
**CategoryTheory.Sheaf.tensorProd_isSheaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：tensorProd_isSheaf : Presheaf.IsSheaf J (X.obj otimes Y.obj)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSheaf_of_isLimit`：isSheaf_of_isLimit (F : K ⥤ She
af J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (hE : IsLimit E) : Presheaf.IsSheaf
 J E.pt
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.obj ⊗ Y.obj) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)
/-
**CategoryTheory.Sheaf.tensorUnit_isSheaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSheaf_of_isLimit`：isSheaf_of_isLimit (F : K ⥤ She
af J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (hE : IsLimit E) : Presheaf.IsSheaf
 J E.pt
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsMonoidal (Presheaf.IsSheaf J (A := A)) where
  prop_unit := tensorUnit_isSheaf _
  prop_tensor F G hF hG := tensorProd_isSheaf J ⟨F, hF⟩ ⟨G, hG⟩
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CartesianMonoidalCategory (Sheaf J A) :=
  inferInstance
/-
**CategoryTheory.Sheaf.cartesianMonoidalCategoryFst_hom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   (J : CategoryTheory.Grothendieck
Topology C) [inst_2 : CategoryTheory.CartesianMonoidalCategory A]   (X Y : Categ
oryTheory.Sheaf J A),   (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y).h
om =     CategoryTheory.SemiCartesianMonoidalCategory.fst X.obj Y.obj
参数：J : CategoryTheory.GrothendieckTopology C；X Y : CategoryTheory.Sheaf J A；Cate
goryTheory.SemiCartesianMonoidalCategory.fst X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsShea
f`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.
GrothendieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] lemma cartesianMonoidalCategoryFst_hom : (fst X Y).hom = fst X.obj Y.obj := rfl
/-
**CategoryTheory.Sheaf.cartesianMonoidalCategorySnd_hom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   (J : CategoryTheory.Grothendieck
Topology C) [inst_2 : CategoryTheory.CartesianMonoidalCategory A]   (X Y : Categ
oryTheory.Sheaf J A),   (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y).h
om =     CategoryTheory.SemiCartesianMonoidalCategory.snd X.obj Y.obj
参数：J : CategoryTheory.GrothendieckTopology C；X Y : CategoryTheory.Sheaf J A；Cate
goryTheory.SemiCartesianMonoidalCategory.snd X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsShea
f`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.
GrothendieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] lemma cartesianMonoidalCategorySnd_hom : (snd X Y).hom = snd X.obj Y.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryFst_val := cartesianMonoidalCategoryFst_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategorySnd_val := cartesianMonoidalCategorySnd_hom

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)
/-
**CategoryTheory.Sheaf.cartesianMonoidalCategoryLift_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   (J : CategoryTheory.Grothendieck
Topology C) [inst_2 : CategoryTheory.CartesianMonoidalCategory A]   {X Y W : Cat
egoryTheory.Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y),   (CategoryTheory.CartesianMonoi
dalCategory.lift f g).hom = CategoryTheory.CartesianMonoidalCategory.lift f.hom 
g.hom
参数：J : CategoryTheory.GrothendieckTopology C；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.
CartesianMonoidalCategory.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsShea
f`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.
GrothendieckTopology C} {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] lemma cartesianMonoidalCategoryLift_hom : (lift f g).hom = lift f.hom g.hom := rfl
/-
**CategoryTheory.Sheaf.cartesianMonoidalCategoryWhiskerLeft_hom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：cartesianMonoidalCategoryWhiskerLeft_hom : (X ◁ f).hom = X.obj ◁ f.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
-/
lemma cartesianMonoidalCategoryWhiskerLeft_hom : (X ◁ f).hom = X.obj ◁ f.hom := rfl
/-
**CategoryTheory.Sheaf.cartesianMonoidalCategoryWhiskerRight_hom** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：cartesianMonoidalCategoryWhiskerRight_hom : (f ▷ X).hom = f.hom ▷ X.obj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
-/
lemma cartesianMonoidalCategoryWhiskerRight_hom : (f ▷ X).hom = f.hom ▷ X.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryLift_val := cartesianMonoidalCategoryLift_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerLeft_val := cartesianMonoidalCategoryWhiskerLeft_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerRight_val := cartesianMonoidalCategoryWhiskerRight_hom

end Sheaf

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-
**CategoryTheory.sheafToPresheaf_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
/-
**CategoryTheory.sheafToPresheaf_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}
/-
**CategoryTheory.sheafToPresheaf_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
/-
**CategoryTheory.sheafToPresheaf_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory

