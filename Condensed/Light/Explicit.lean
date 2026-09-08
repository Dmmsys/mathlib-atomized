/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Condensed.Light.Module
/-!

# The explicit sheaf condition for light condensed sets

We give an explicit description of light condensed sets:

* `LightCondensed.ofSheafLightProfinite`: A finite-product-preserving presheaf on `LightProfinite`,
  satisfying `EqualizerCondition`.

The property `EqualizerCondition` is defined in
`Mathlib/CategoryTheory/Sites/Coherent/RegularSheaves.lean` and it says that for any effective epi
`X ⟶ B` (in this case that is equivalent to being a continuous surjection), the presheaf `F`
exhibits `F(B)` as the equalizer of the two maps `F(X) ⇉ F(X ×_B X)`.

We also give variants for light condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

variable {A : Type*} [Category* A]

namespace LightCondensed

/--
The light condensed object associated to a presheaf on `LightProfinite` which preserves finite
products and satisfies the equalizer condition.
-/
@[simps]
/-
**LightCondensed.ofSheafLightProfinite** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed
`。
形式化陈述：ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProdu
cts F] (hF : EqualizerCondition F) : LightCondensed A where obj
参数：F : LightProfinite.{u}ᵒᵖ ⥤ A；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The light condensed object associated to a presheaf on `LightProfinite` which pr
eserves finite
products and satisfies the equalizer condition.
-/
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : LightCondensed A where
  obj := F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/--
The light condensed object associated to a presheaf on `LightProfinite` whose postcomposition with
the forgetful functor preserves finite products and satisfies the equalizer condition.
-/
@[simps]
/-
**LightCondensed.ofSheafForgetLightProfinite** 是 Mathlib 中的一个定义，位于命名空间 `LightCon
densed`。
形式化陈述：ofSheafForgetLightProfinite {FA : A -> A -> Type*} {CA : A -> Type*} [fora
ll X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [ReflectsFiniteL
imits (CategoryTheory.forget A)] (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFinite
Products (F ⋙ CategoryTheory.forget A)] (hF : EqualizerCondition (F ⋙ CategoryTh
eory.forget A)) : LightCondensed A where obj
参数：FA X Y；CA X；CA Y；CategoryTheory.forget A；F : LightProfinite.{u}ᵒᵖ ⥤ A；F ⋙ Cat
egoryTheory.forget A；hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The light condensed object associated to a presheaf on `LightProfinite` whose po
stcomposition with
the forgetful functor preserves finite products and satisfies the equalizer cond
ition.
-/
noncomputable def ofSheafForgetLightProfinite
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : LightCondensed A where
  obj := F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/-- A light condensed object satisfies the equalizer condition. -/
/-
**LightCondensed.equalizerCondition** 是 Mathlib 中的一个定理，位于命名空间 `LightCondensed`。
形式化陈述：equalizerCondition (X : LightCondensed A) : EqualizerCondition X.obj
参数：X : LightCondensed A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalize
rCondition`：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregul
ar C] [FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [Effective…
· 使用定理 `CompHausLike.instHasLimitWalkingCospanCospan`：∀ {P : TopCat → Prop} {X Y
 B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [CompHausLike.HasExplicitPullback f
 g],   CategoryTheory.Limits.HasLi…
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…
· 使用定理 `LightProfinite.instTotallyDisconnectedSpaceCarrierToTopAndSecondCountabl
eTopology`：∀ {X : LightProfinite}, TotallyDisconnectedSpace ↑X.toTop
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `LightProfinite.instSecondCountableTopologyCarrierToTopAndTotallyDisconne
ctedSpace`：∀ {X : LightProfinite}, SecondCountableTopology ↑X.toTop
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
A light condensed object satisfies the equalizer condition.
-/
theorem equalizerCondition (X : LightCondensed A) : EqualizerCondition X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp X.property |>.2

/-- A light condensed object preserves finite products. -/
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A light condensed object preserves finite products.
-/
noncomputable instance (X : LightCondensed A) : PreservesFiniteProducts X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp X.property |>.1

end LightCondensed

namespace LightCondSet

/-- A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`. -/
/-
**LightCondSet.ofSheafLightProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondSet`。
形式化陈述：ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) [PreservesFinite
Products F] (hF : EqualizerCondition F) : LightCondSet
参数：F : LightProfinite.{u}ᵒᵖ ⥤ Type u；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`.
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

/-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
/-
**LightCondMod.ofSheafLightProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondMod`。
形式化陈述：ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) [Preser
vesFiniteProducts F] (hF : EqualizerCondition F) : LightCondMod.{u} R
参数：F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`.
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondMod.{u} R :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondMod

namespace LightCondAb

/-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
/-
**LightCondAb.ofSheafLightProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondAb`。
形式化陈述：ofSheafLightProfinite (F : LightProfiniteᵒᵖ ⥤ ModuleCat Int) [PreservesFin
iteProducts F] (hF : EqualizerCondition F) : LightCondAb
参数：F : LightProfiniteᵒᵖ ⥤ ModuleCat Int；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`.
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondAb :=
  LightCondMod.ofSheafLightProfinite ℤ F hF

end LightCondAb

