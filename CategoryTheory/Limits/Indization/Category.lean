/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Indization.Equalizers
public import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
public import Mathlib.CategoryTheory.Limits.Indization.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Presheaf

/-!
# The category of Ind-objects

We define the `v`-category of Ind-objects of a category `C`, called `Ind C`, as well as the functors
`Ind.yoneda : C ⥤ Ind C` and `Ind.inclusion C : Ind C ⥤ Cᵒᵖ ⥤ Type v`.

For a small filtered category `I`, we also define `Ind.lim I : (I ⥤ C) ⥤ Ind C` and show that
it preserves finite limits and finite colimits.

This file will mainly collect results about ind-objects (stated in terms of `IsIndObject`) and
reinterpret them in terms of `Ind C`.

Adopting the theorem numbering of [Kashiwara2006], we show the following properties:

Limits:
* If `C` has products indexed by `α`, then `Ind C` has products indexed by `α`, and the functor
  `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates such products (6.1.17),
* if `C` has equalizers, then `Ind C` has equalizers, and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v`
  creates them (6.1.17)
* if `C` has small limits (resp. finite limits), then `Ind C` has small limits (resp. finite limits)
  and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates them (6.1.17),
* the functor `C ⥤ Ind C` preserves small limits (6.1.17).

Colimits:
* `Ind C` has filtered colimits (6.1.8), and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves filtered
  colimits,
* if `C` has coproducts indexed by a finite type `α`, then `Ind C` has coproducts indexed by `α`
  (6.1.18(ii)),
* if `C` has finite coproducts, then `Ind C` has small coproducts (6.1.18(ii)),
* if `C` has coequalizers, then `Ind C` has coequalizers (6.1.18(i)),
* if `C` has finite colimits, then `Ind C` has small colimits (6.1.18(iii)).
* `C ⥤ Ind C` preserves finite colimits (6.1.6),

Note that:
* the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` does not preserve any kind of colimit in general except for
  filtered colimits and
* the functor `C ⥤ Ind C` preserves finite colimits, but not infinite colimits in general.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The category of Ind-objects of `C`. -/
/-
**CategoryTheory.Ind** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Ind : Type (max u (v + 1))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Ind-objects of `C`.
-/
def Ind : Type (max u (v + 1)) :=
  ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C)))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Category.{v} (Ind C) :=
  inferInstanceAs <| Category.{v}
    (ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C))))

variable (C) in
/-- The defining properties of `Ind C` are that its morphisms live in `v` and that it is equivalent
to the full subcategory of `Cᵒᵖ ⥤ Type v` containing the ind-objects. -/
/-
**CategoryTheory.Ind.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ind`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Ind C ≌ CategoryTheory.ObjectProperty.FullSubcategory CategoryTheory.Limit
s.IsIndObject
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallFullSubcategoryFunctorOppositeTypeIsIndOb
ject`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   CategoryTheory
.LocallySmall.{v, max u v, max u (v + 1)}     (CategoryTheory.Obje…

--- 原说明 ---
The defining properties of `Ind C` are that its morphisms live in `v` and that i
t is equivalent
to the full subcategory of `Cᵒᵖ ⥤ Type v` containing the ind-objects.
-/
noncomputable def Ind.equivalence :
    Ind C ≌ ObjectProperty.FullSubcategory (IsIndObject (C := C)) :=
  (ShrinkHoms.equivalence _).symm

variable (C) in
/-- The canonical inclusion of ind-objects into presheaves. -/
/-
**CategoryTheory.Ind.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ind`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Functor (CategoryTheory.Ind C) (CategoryTheory.Functor Cᵒᵖ (Type v))
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion of ind-objects into presheaves.
-/
protected noncomputable def Ind.inclusion : Ind C ⥤ Cᵒᵖ ⥤ Type v :=
  (Ind.equivalence C).functor ⋙ ObjectProperty.ι _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Ind.inclusion C).Full :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Full
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Ind.inclusion C).Faithful :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Faithful

/-- The functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` is fully faithful. -/
/-
**CategoryTheory.Ind.inclusion.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Ind.inclusion`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (CategoryTheory
.Ind.inclusion C).FullyFaithful
参数：CategoryTheory.Ind.inclusion C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instFullIndFunctorOppositeTypeInclusion`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.Ind.inclusion C).Full
· 使用定理 `CategoryTheory.instFaithfulIndFunctorOppositeTypeInclusion`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.Ind.inclusion C).F
aithful

--- 原说明 ---
The functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` is fully faithful.
-/
protected noncomputable def Ind.inclusion.fullyFaithful : (Ind.inclusion C).FullyFaithful :=
  .ofFullyFaithful _

/-- The inclusion of `C` into `Ind C` induced by the Yoneda embedding. -/
/-
**CategoryTheory.Ind.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ind`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C (CategoryTheory.Ind C)
参数：CategoryTheory.Ind C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIndObject_yoneda`：isIndObject_yoneda (X : C) : I
sIndObject (yoneda.obj X)

--- 原说明 ---
The inclusion of `C` into `Ind C` induced by the Yoneda embedding.
-/
protected noncomputable def Ind.yoneda : C ⥤ Ind C :=
  ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Ind.yoneda (C := C)).Full :=
  inferInstanceAs <| Functor.Full <|
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Ind.yoneda (C := C)).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/-- The functor `C ⥤ Ind C` is fully faithful. -/
/-
**CategoryTheory.Ind.yoneda.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Ind.yoneda`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Ind.yoneda.FullyFaithful
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instFullIndYoneda`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C], CategoryTheory.Ind.yoneda.Full
· 使用定理 `CategoryTheory.instFaithfulIndYoneda`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C], CategoryTheory.Ind.yoneda.Faithful

--- 原说明 ---
The functor `C ⥤ Ind C` is fully faithful.
-/
protected noncomputable def Ind.yoneda.fullyFaithful : (Ind.yoneda (C := C)).FullyFaithful :=
  .ofFullyFaithful _

/-- The composition `C ⥤ Ind C ⥤ (Cᵒᵖ ⥤ Type v)` is just the Yoneda embedding. -/
/-
**CategoryTheory.Ind.yonedaCompInclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Ind`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Ind.yoneda.comp (CategoryTheory.Ind.inclusion C) ≅ CategoryTheory.yoneda
参数：CategoryTheory.Ind.inclusion C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIndObject_yoneda`：isIndObject_yoneda (X : C) : I
sIndObject (yoneda.obj X)

--- 原说明 ---
The composition `C ⥤ Ind C ⥤ (Cᵒᵖ ⥤ Type v)` is just the Yoneda embedding.
-/
noncomputable def Ind.yonedaCompInclusion : Ind.yoneda ⋙ Ind.inclusion C ≅ CategoryTheory.yoneda :=
  isoWhiskerLeft (ObjectProperty.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (IsIndObject (C := C)) J :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact isIndObject_colimit _ _ hF)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    CreatesColimitsOfShape J (Ind.inclusion C) :=
  inferInstanceAs <|
    CreatesColimitsOfShape J ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFilteredColimits (Ind C) where
  HasColimitsOfShape _ _ _ :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C := C)) (Discrete J) :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact isIndObject_limit_of_discrete_of_hasLimitsOfShape _ hF)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    CreatesLimitsOfShape (Discrete J) (Ind.inclusion C) :=
  inferInstanceAs <|
    CreatesLimitsOfShape (Discrete J) ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    HasLimitsOfShape (Discrete J) (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasLimitsOfShape WalkingParallelPair C] :
    CreatesLimitsOfShape WalkingParallelPair (Ind.inclusion C) :=
  inferInstanceAs <|
    CreatesLimitsOfShape WalkingParallelPair
      ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape WalkingParallelPair C] :
    HasLimitsOfShape WalkingParallelPair (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasFiniteLimits C] : CreatesFiniteLimits (Ind.inclusion C) :=
  letI _ : CreatesFiniteProducts (Ind.inclusion C) :=
    { creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift) _ }
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] : HasFiniteLimits (Ind C) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasLimits C] : CreatesLimitsOfSize.{v, v} (Ind.inclusion C) :=
  createsLimitsOfSizeOfCreatesEqualizersAndProducts.{v, v} (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] : HasLimits (Ind C) :=
  hasLimits_of_hasLimits_createsLimits (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimits (Ind.yoneda (C := C)) :=
  letI _ : PreservesLimitsOfSize.{v, v} (Ind.yoneda ⋙ Ind.inclusion C) :=
    preservesLimits_of_natIso Ind.yonedaCompInclusion.symm
  preservesLimits_of_reflects_of_preserves Ind.yoneda (Ind.inclusion C)
/-
**CategoryTheory.Ind.isIndObject_inclusion_obj** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Ind`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X : CategoryTheo
ry.Ind C),   CategoryTheory.Limits.IsIndObject ((CategoryTheory.Ind.inclusion C)
.obj X)
参数：X : CategoryTheory.Ind C；(CategoryTheory.Ind.inclusion C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem Ind.isIndObject_inclusion_obj (X : Ind C) : IsIndObject ((Ind.inclusion C).obj X) :=
  X.2

/-- Pick a presentation of an ind-object `X` using choice. -/
/-
**CategoryTheory.Ind.presentation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ind`
。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (X : Cate
goryTheory.Ind C) → CategoryTheory.Limits.IndObjectPresentation ((CategoryTheory
.Ind.inclusion C).obj X)
参数：X : CategoryTheory.Ind C；(CategoryTheory.Ind.inclusion C).obj X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Ind.isIndObject_inclusion_obj`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] (X : CategoryTheory.Ind C),   CategoryTheory.Limi
ts.IsIndObject ((CategoryTheory.In…

--- 原说明 ---
Pick a presentation of an ind-object `X` using choice.
-/
noncomputable def Ind.presentation (X : Ind C) : IndObjectPresentation ((Ind.inclusion C).obj X) :=
  X.isIndObject_inclusion_obj.presentation

/-- An ind-object `X` is the colimit (in `Ind C`!) of the filtered diagram presenting it. -/
/-
**CategoryTheory.Ind.colimitPresentationCompYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Ind`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (X : Cate
goryTheory.Ind C) → CategoryTheory.Limits.colimit (X.presentation.F.comp Categor
yTheory.Ind.yoneda) ≅ X
参数：X : CategoryTheory.Ind C；X.presentation.F.comp CategoryTheory.Ind.yoneda。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An ind-object `X` is the colimit (in `Ind C`!) of the filtered diagram presentin
g it.
-/
noncomputable def Ind.colimitPresentationCompYoneda (X : Ind C) :
    colimit (X.presentation.F ⋙ Ind.yoneda) ≅ X :=
  Ind.inclusion.fullyFaithful.isoEquiv.symm <| calc
    (Ind.inclusion C).obj (colimit (X.presentation.F ⋙ Ind.yoneda))
      ≅ colimit (X.presentation.F ⋙ Ind.yoneda ⋙ Ind.inclusion C) := preservesColimitIso _ _
    _ ≅ colimit (X.presentation.F ⋙ yoneda) :=
          HasColimit.isoOfNatIso (isoWhiskerLeft X.presentation.F Ind.yonedaCompInclusion)
    _ ≅ (Ind.inclusion C).obj X :=
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) X.presentation.isColimit
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RepresentablyCoflat (Ind.yoneda (C := C)) := by
  refine ⟨fun X => ?_⟩
  suffices IsFiltered (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) from
    IsFiltered.of_equivalence
      ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)).symm
  exact ((isIndObject_iff _).1 (Ind.isIndObject_inclusion_obj X)).1
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteColimits (Ind.yoneda (C := C)) :=
  preservesFiniteColimits_of_coflat _

/-- This is the functor `(I ⥤ C) ⥤ Ind C` that sends a functor `F` to `colim (Y ∘ F)`, where `Y`
is the Yoneda embedding. It is known as "ind-lim" and denoted `“colim”` in [Kashiwara2006]. -/
/-
**CategoryTheory.Ind.lim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ind`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (I : Type
 v) →       [inst_1 : CategoryTheory.SmallCategory I] →         [CategoryTheory.
IsFiltered I] → CategoryTheory.Functor (CategoryTheory.Functor I C) (CategoryThe
ory.Ind C)
参数：I : Type v；CategoryTheory.Functor I C；CategoryTheory.Ind C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the functor `(I ⥤ C) ⥤ Ind C` that sends a functor `F` to `colim (Y ∘ F)
`, where `Y`
is the Yoneda embedding. It is known as "ind-lim" and denoted `“colim”` in [Kash
iwara2006].
-/
protected noncomputable def Ind.lim (I : Type v) [SmallCategory I] [IsFiltered I] :
    (I ⥤ C) ⥤ Ind C :=
  (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim

/-- Computing ind-lims in `Ind C` is the same as computing them in `Cᵒᵖ ⥤ Type v`. -/
/-
**CategoryTheory.Ind.limCompInclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Ind`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {I : Type
 v} →       [inst_1 : CategoryTheory.SmallCategory I] →         [inst_2 : Catego
ryTheory.IsFiltered I] →           (CategoryTheory.Ind.lim I).comp (CategoryTheo
ry.Ind.inclusion C) ≅             ((CategoryTheory.Functor.whiskeringRight I C (
CategoryTheory.Functor Cᵒᵖ (Type v))).obj                   CategoryTheory.yoned
a).comp               CategoryTheory.Limits.colim
参数：CategoryTheory.Ind.lim I；CategoryTheory.Ind.inclusion C；(CategoryTheory.Funct
or.whiskeringRight I C (CategoryTheory.Functor Cᵒᵖ (Type v))).obj               
    CategoryTheory.yoneda。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computing ind-lims in `Ind C` is the same as computing them in `Cᵒᵖ ⥤ Type v`.
-/
noncomputable def Ind.limCompInclusion {I : Type v} [SmallCategory I] [IsFiltered I] :
    Ind.lim I ⋙ Ind.inclusion C ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim := calc
  Ind.lim I ⋙ Ind.inclusion C
    ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ⋙ Ind.inclusion C := Functor.associator _ _ _
  _ ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C) ⋙ colim :=
    isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C)) ⋙ colim := (Functor.associator _ _ _).symm
  _ ≅ (whiskeringRight _ _ _).obj (Ind.yoneda ⋙ Ind.inclusion C) ⋙ colim :=
    isoWhiskerRight (whiskeringRightObjCompIso _ _) colim
  _ ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
    isoWhiskerRight ((whiskeringRight _ _ _).mapIso (Ind.yonedaCompInclusion)) colim
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type w} [SmallCategory α] [FinCategory α] [HasLimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesLimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  haveI : PreservesLimitsOfShape α (Ind.lim I ⋙ Ind.inclusion C) :=
    preservesLimitsOfShape_of_natIso Ind.limCompInclusion.symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (Ind.inclusion C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type w} [SmallCategory α] [FinCategory α] [HasColimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  inferInstanceAs (PreservesColimitsOfShape α (_ ⋙ colim))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type v} [Finite α] [HasColimitsOfShape (Discrete α) C] :
    HasColimitsOfShape (Discrete α) (Ind C) := by
  refine ⟨fun F => ?_⟩
  let I : α → Type v := fun s => (F.obj ⟨s⟩).presentation.I
  let G : ∀ s, I s ⥤ C := fun s => (F.obj ⟨s⟩).presentation.F
  let iso : Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
      (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ≅ F := by
    refine Discrete.natIso (fun s => ?_)
    refine (Functor.Final.colimitIso (Pi.eval I s.as) (G s.as ⋙ Ind.yoneda)) ≪≫ ?_
    exact Ind.colimitPresentationCompYoneda _
  -- The actual proof happens during typeclass resolution in the following line, which deduces
  -- ```
  -- HasColimit Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
  --    (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim
  -- ```
  -- from the fact that finite limits commute with filtered colimits and from the fact that
  -- `Ind.yoneda` preserves finite colimits.
  exact hasColimit_of_iso iso.symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteCoproducts C] : HasCoproducts.{v} (Ind C) :=
  have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

/-- Given an `IndParallelPairPresentation f g`, we can understand the parallel pair `(f, g)` as
the colimit of `(P.φ, P.ψ)` in `Ind C`. -/
/-
**CategoryTheory.IndParallelPairPresentation.parallelPairIsoParallelPairCompIndY
oneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IndParallelPairPresentation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A B : Ca
tegoryTheory.Ind C} →       {f g : A ⟶ B} →         (P :             CategoryThe
ory.IndParallelPairPresentation ((CategoryTheory.Ind.inclusion C).map f)        
       ((CategoryTheory.Ind.inclusion C).map g)) →           CategoryTheory.Limi
ts.parallelPair f g ≅             (CategoryTheory.Limits.parallelPair P.φ P.ψ).c
omp (CategoryTheory.Ind.lim P.I)
参数：P :             CategoryTheory.IndParallelPairPresentation ((CategoryTheory.I
nd.inclusion C).map f)               ((CategoryTheory.Ind.inclusion C).map g)；Ca
tegoryTheory.Limits.parallelPair P.φ P.ψ；CategoryTheory.Ind.lim P.I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `IndParallelPairPresentation f g`, we can understand the parallel pair 
`(f, g)` as
the colimit of `(P.φ, P.ψ)` in `Ind C`.
-/
noncomputable def IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda
    {A B : Ind C} {f g : A ⟶ B}
    (P : IndParallelPairPresentation ((Ind.inclusion _).map f) ((Ind.inclusion _).map g)) :
    parallelPair f g ≅ parallelPair P.φ P.ψ ⋙ Ind.lim P.I :=
  ((whiskeringRight WalkingParallelPair _ _).obj (Ind.inclusion C)).preimageIso <|
    diagramIsoParallelPair _ ≪≫
      P.parallelPairIsoParallelPairCompYoneda ≪≫
      isoWhiskerLeft (parallelPair _ _) Ind.limCompInclusion.symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape WalkingParallelPair C] :
    HasColimitsOfShape WalkingParallelPair (Ind C) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation (F.obj WalkingParallelPair.zero).2
    (F.obj WalkingParallelPair.one).2 (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.left)
    (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.right)
  exact hasColimit_of_iso (diagramIsoParallelPair _ ≪≫ P.parallelPairIsoParallelPairCompIndYoneda)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] : HasColimits (Ind C) :=
  has_colimits_of_hasCoequalizers_and_coproducts

set_option backward.isDefEq.respectTransparency.types false in
/-- A way to understand morphisms in `Ind C`: every morphism is induced by a natural transformation
of diagrams. -/
/-
**CategoryTheory.Ind.exists_nonempty_arrow_mk_iso_ind_lim** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Ind`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B : CategoryTh
eory.Ind C} {f : A ⟶ B},   ∃ I x,     ∃ (x_1 : CategoryTheory.IsFiltered I),    
   ∃ F G φ, Nonempty (CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk ((Cate
goryTheory.Ind.lim I).map φ))
参数：x_1 : CategoryTheory.IsFiltered I；CategoryTheory.Arrow.mk f ≅ CategoryTheory.
Arrow.mk ((CategoryTheory.Ind.lim I).map φ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.nonempty_indParallelPairPresentation`：nonempty_indParalle
lPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A) (hB : IsIndObject B
) (f g : A ⟶ B) : Nonempty (IndParallelPa…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.instIsFilteredI`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v₁)} {f g : A ⟶ B}  
 (P : CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
A way to understand morphisms in `Ind C`: every morphism is induced by a natural
 transformation
of diagrams.
-/
theorem Ind.exists_nonempty_arrow_mk_iso_ind_lim {A B : Ind C} {f : A ⟶ B} :
    ∃ (I : Type v) (_ : SmallCategory I) (_ : IsFiltered I) (F G : I ⥤ C) (φ : F ⟶ G),
      Nonempty (Arrow.mk f ≅ Arrow.mk ((Ind.lim _).map φ)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation A.2 B.2
    (Ind.inclusion _ |>.map f) (Ind.inclusion _ |>.map f)
  refine ⟨P.I, inferInstance, inferInstance, P.F₁, P.F₂, P.φ, ⟨Arrow.isoMk ?_ ?_ ?_⟩⟩
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.zero
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.one
  · simpa using!
      (P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality WalkingParallelPairHom.left).symm

section Small

variable (C : Type u) [SmallCategory C] [HasFiniteColimits C]

/-- For small finitely cocomplete categories `C : Type u`, the category of Ind-objects `Ind C` is
equivalent to the category of left-exact functors `Cᵒᵖ ⥤ Type u` -/
/-
**CategoryTheory.Ind.leftExactFunctorEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Ind`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.SmallCategory C] →     [CategoryTh
eory.Limits.HasFiniteColimits C] → CategoryTheory.Ind C ≌ Cᵒᵖ ⥤ₗ Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For small finitely cocomplete categories `C : Type u`, the category of Ind-objec
ts `Ind C` is
equivalent to the category of left-exact functors `Cᵒᵖ ⥤ Type u`
-/
noncomputable def Ind.leftExactFunctorEquivalence : Ind C ≌ LeftExactFunctor Cᵒᵖ (Type u) :=
  (Ind.equivalence _).trans <| ObjectProperty.fullSubcategoryCongr
    (by ext; apply isIndObject_iff_preservesFiniteLimits)

end Small

end CategoryTheory

