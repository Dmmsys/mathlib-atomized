/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/
module

public import Mathlib.Condensed.Module
public import Mathlib.Condensed.Equivalence
/-!

# The explicit sheaf condition for condensed sets

We give the following three explicit descriptions of condensed objects:

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `Stonean`.

* `Condensed.ofSheafProfinite`: A finite-product-preserving presheaf on `Profinite`, satisfying
  `EqualizerCondition`.

* `Condensed.ofSheafCompHaus`: A finite-product-preserving presheaf on `CompHaus`, satisfying
  `EqualizerCondition`.

The property `EqualizerCondition` is defined in
`Mathlib/CategoryTheory/Sites/Coherent/RegularSheaves.lean` and it says that for any effective epi
`X ⟶ B` (in this case that is equivalent to being a continuous surjection), the presheaf `F`
exhibits `F(B)` as the equalizer of the two maps `F(X) ⇉ F(X ×_B X)`.

We also give variants for condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

namespace Condensed

variable {A : Type*} [Category* A]

/-- The condensed object associated to a finite-product-preserving presheaf on `Stonean`. -/
/-
**Condensed.ofSheafStonean** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafStonean [forall X, HasLimitsOfShape (StructuredArrow X Stonean.toCo
mpHaus.op) A] (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] : Condensed A
参数：StructuredArrow X Stonean.toCompHaus.op；F : Stonean.{u}ᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a finite-product-preserving presheaf on `Ston
ean`.
-/
noncomputable def ofSheafStonean
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] :
    Condensed A :=
  StoneanCompHaus.equivalence A |>.functor.obj {
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_of_projective F]
      exact ⟨fun _ ↦ inferInstance⟩ }

/--
The condensed object associated to a presheaf on `Stonean` whose postcomposition with the
forgetful functor preserves finite products.
-/
/-
**Condensed.ofSheafForgetStonean** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafForgetStonean [forall X, HasLimitsOfShape (StructuredArrow X Stonea
n.toCompHaus.op) A] {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, FunLik
e (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [ReflectsFiniteProducts (Categ
oryTheory.forget A)] (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ Categ
oryTheory.forget A)] : Condensed A
参数：StructuredArrow X Stonean.toCompHaus.op；FA X Y；CA X；CA Y；CategoryTheory.forge
t A；F : Stonean.{u}ᵒᵖ ⥤ A；F ⋙ CategoryTheory.forget A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a presheaf on `Stonean` whose postcomposition
 with the
forgetful functor preserves finite products.
-/
noncomputable def ofSheafForgetStonean
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteProducts (CategoryTheory.forget A)]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)] :
    Condensed A :=
  StoneanCompHaus.equivalence A |>.functor.obj {
    obj := F
    property := by
      apply isSheaf_coherent_of_projective_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_of_projective]
      exact ⟨fun _ ↦ inferInstance⟩ }

/--
The condensed object associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
/-
**Condensed.ofSheafProfinite** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafProfinite [forall X, HasLimitsOfShape (StructuredArrow X profiniteT
oCompHaus.op) A] (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] (hF : Equ
alizerCondition F) : Condensed A
参数：StructuredArrow X profiniteToCompHaus.op；F : Profinite.{u}ᵒᵖ ⥤ A；hF : Equaliz
erCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a presheaf on `Profinite` which preserves fin
ite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafProfinite
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A :=
  ProfiniteCompHaus.equivalence A |>.functor.obj {
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩ }

/--
The condensed object associated to a presheaf on `Profinite` whose postcomposition with the
forgetful functor preserves finite products and satisfies the equalizer condition.
-/
/-
**Condensed.ofSheafForgetProfinite** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafForgetProfinite [forall X, HasLimitsOfShape (StructuredArrow X prof
initeToCompHaus.op) A] {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, Fun
Like (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [ReflectsFiniteLimits (Cate
goryTheory.forget A)] (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ Ca
tegoryTheory.forget A)] (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) 
: Condensed A
参数：StructuredArrow X profiniteToCompHaus.op；FA X Y；CA X；CA Y；CategoryTheory.forg
et A；F : Profinite.{u}ᵒᵖ ⥤ A；F ⋙ CategoryTheory.forget A；hF : EqualizerCondition
 (F ⋙ CategoryTheory.forget A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a presheaf on `Profinite` whose postcompositi
on with the
forgetful functor preserves finite products and satisfies the equalizer conditio
n.
-/
noncomputable def ofSheafForgetProfinite
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) :
    Condensed A :=
  ProfiniteCompHaus.equivalence A |>.functor.obj {
    obj := F
    property := by
      apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
      exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩ }

/--
The condensed object associated to a presheaf on `CompHaus` which preserves finite products and
satisfies the equalizer condition.
-/
/-
**Condensed.ofSheafCompHaus** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] (hF :
 EqualizerCondition F) : Condensed A where obj
参数：F : CompHaus.{u}ᵒᵖ ⥤ A；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a presheaf on `CompHaus` which preserves fini
te products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafCompHaus
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A where
  obj := F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/--
The condensed object associated to a presheaf on `CompHaus` whose postcomposition with the
forgetful functor preserves finite products and satisfies the equalizer condition.
-/
/-
**Condensed.ofSheafForgetCompHaus** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：ofSheafForgetCompHaus {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y
, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [ReflectsFiniteLimits 
(CategoryTheory.forget A)] (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F 
⋙ CategoryTheory.forget A)] (hF : EqualizerCondition (F ⋙ CategoryTheory.forget 
A)) : Condensed A where obj
参数：FA X Y；CA X；CA Y；CategoryTheory.forget A；F : CompHaus.{u}ᵒᵖ ⥤ A；F ⋙ CategoryT
heory.forget A；hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condensed object associated to a presheaf on `CompHaus` whose postcompositio
n with the
forgetful functor preserves finite products and satisfies the equalizer conditio
n.
-/
noncomputable def ofSheafForgetCompHaus
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : Condensed A where
  obj := F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/-- A condensed object satisfies the equalizer condition. -/
/-
**Condensed.equalizerCondition** 是 Mathlib 中的一个定理，位于命名空间 `Condensed`。
形式化陈述：equalizerCondition (X : Condensed A) : EqualizerCondition X.obj
参数：X : Condensed A。
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
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalize
rCondition`：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregul
ar C] [FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [Effective…
· 使用定理 `CompHausLike.instHasLimitWalkingCospanCospan`：∀ {P : TopCat → Prop} {X Y
 B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [CompHausLike.HasExplicitPullback f
 g],   CategoryTheory.Limits.HasLi…
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
A condensed object satisfies the equalizer condition.
-/
theorem equalizerCondition (X : Condensed A) : EqualizerCondition X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp X.property |>.2

/-- A condensed object preserves finite products. -/
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A condensed object preserves finite products.
-/
noncomputable instance (X : Condensed A) : PreservesFiniteProducts X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp
    X.property |>.1

/-- A condensed object regarded as a sheaf on `Profinite` preserves finite products. -/
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A condensed object regarded as a sheaf on `Profinite` preserves finite products.
-/
noncomputable instance (X : Sheaf (coherentTopology Profinite.{u}) A) :
    PreservesFiniteProducts X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp
    X.property |>.1

/-- A condensed object regarded as a sheaf on `Profinite` satisfies the equalizer condition. -/
/-
**Condensed.equalizerCondition_profinite** 是 Mathlib 中的一个定理，位于命名空间 `Condensed`。
形式化陈述：equalizerCondition_profinite (X : Sheaf (coherentTopology Profinite.{u}) A
) : EqualizerCondition X.obj
参数：X : Sheaf (coherentTopology Profinite.{u}) A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `Profinite.instHasExplicitPullbacksTotallyDisconnectedSpaceCarrier`：CompH
ausLike.HasExplicitPullbacks fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instPreregular`：CategoryTheory.Preregular Profinite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalize
rCondition`：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregul
ar C] [FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [Effective…
· 使用定理 `CompHausLike.instHasLimitWalkingCospanCospan`：∀ {P : TopCat → Prop} {X Y
 B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [CompHausLike.HasExplicitPullback f
 g],   CategoryTheory.Limits.HasLi…
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
A condensed object regarded as a sheaf on `Profinite` satisfies the equalizer co
ndition.
-/
theorem equalizerCondition_profinite (X : Sheaf (coherentTopology Profinite.{u}) A) :
    EqualizerCondition X.obj :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj |>.mp X.property |>.2

/-- A condensed object regarded as a sheaf on `Stonean` preserves finite products. -/
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A condensed object regarded as a sheaf on `Stonean` preserves finite products.
-/
noncomputable instance (X : Sheaf (coherentTopology Stonean.{u}) A) :
    PreservesFiniteProducts X.obj :=
  isSheaf_iff_preservesFiniteProducts_of_projective X.obj |>.mp X.property

end Condensed

namespace CondensedSet

/-- A `CondensedSet` version of `Condensed.ofSheafStonean`. -/
/-
**CondensedSet.ofSheafStonean** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedSet`。
形式化陈述：ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts
 F] : CondensedSet
参数：F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedSet` version of `Condensed.ofSheafStonean`.
-/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] : CondensedSet :=
  Condensed.ofSheafStonean F

/-- A `CondensedSet` version of `Condensed.ofSheafProfinite`. -/
/-
**CondensedSet.ofSheafProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedSet`。
形式化陈述：ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProd
ucts F] (hF : EqualizerCondition F) : CondensedSet
参数：F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedSet` version of `Condensed.ofSheafProfinite`.
-/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafProfinite F hF

/-- A `CondensedSet` version of `Condensed.ofSheafCompHaus`. -/
/-
**CondensedSet.ofSheafCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedSet`。
形式化陈述：ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProduc
ts F] (hF : EqualizerCondition F) : CondensedSet
参数：F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1)；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedSet` version of `Condensed.ofSheafCompHaus`.
-/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafCompHaus F hF

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

/-- A `CondensedMod` version of `Condensed.ofSheafStonean`. -/
/-
**CondensedMod.ofSheafStonean** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedMod`。
形式化陈述：ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R) [PreservesFiniteP
roducts F] : CondensedMod R
参数：F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedMod` version of `Condensed.ofSheafStonean`.
-/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafStonean F

/-- A `CondensedMod` version of `Condensed.ofSheafProfinite`. -/
/-
**CondensedMod.ofSheafProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedMod`。
形式化陈述：ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R) [PreservesFin
iteProducts F] (hF : EqualizerCondition F) : CondensedMod R
参数：F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedMod` version of `Condensed.ofSheafProfinite`.
-/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafProfinite F hF

/-- A `CondensedMod` version of `Condensed.ofSheafCompHaus`. -/
/-
**CondensedMod.ofSheafCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 `CondensedMod`。
形式化陈述：ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R) [PreservesFinit
eProducts F] (hF : EqualizerCondition F) : CondensedMod R
参数：F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R；hF : EqualizerCondition F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CondensedMod` version of `Condensed.ofSheafCompHaus`.
-/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  Condensed.ofSheafCompHaus F hF

end CondensedMod

