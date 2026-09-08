/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Bounded below cochain complexes

In this file, we consider the full subcategory `CochainComplex.Plus C`
of `CochainComplex C ℤ` consisting of bounded below cochain complexes
in a category `C`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C]

/-- The property of cochain complexes that are bounded below. -/
/-
**CochainComplex.plus** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → CategoryTheory.ObjectProperty
 (CochainComplex C ℤ)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of cochain complexes that are bounded below.
-/
protected def plus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyGE n
/-
**CochainComplex.plus_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：plus_iff [HasZeroMorphisms C] (K : CochainComplex C Int) : CochainComplex.
plus C K ↔ exists (n : Int), K.IsStrictlyGE n
参数：K : CochainComplex C Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma plus_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.plus C K ↔ ∃ (n : ℤ), K.IsStrictlyGE n := Iff.rfl
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

/-- The full subcategory of `CochainComplex C ℤ` consisting of bounded below complexes. -/
/-
**CochainComplex.Plus** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：Plus [HasZeroMorphisms C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of `CochainComplex C ℤ` consisting of bounded below complex
es.
-/
abbrev Plus [HasZeroMorphisms C] :=
  (CochainComplex.plus C).FullSubcategory

namespace Plus

section

variable [HasZeroMorphisms C]

/-- The inclusion of the full subcategory of bounded below cochain complexes. -/
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the full subcategory of bounded below cochain complexes.
-/
abbrev ι : Plus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

/-- The inclusion of the full subcategory of bounded below cochain complexes
is fully faithful. -/
/-
**CochainComplex.Plus.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Pl
us`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the full subcategory of bounded below cochain complexes
is fully faithful.
-/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [SmallCategory J] [FinCategory J] [HasLimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_tgt _ _)
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [SmallCategory J] [FinCategory J] [HasColimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_src _ _)
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] : HasFiniteLimits (Plus C) where
  out J _ _ := by infer_instance
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] : HasFiniteColimits (Plus C) where
  out J _ _ := by infer_instance

variable {C} in
/-
**CochainComplex.Plus.mono_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.Plus`。
形式化陈述：mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) : M
ono f ↔ Mono f.hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom :=
  ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) [Mono f] :
    Mono f.hom := by
  rwa [← mono_iff]

/-- The class of quasi-isomorphisms in the category of bounded
below cochain complexes. -/
/-
**CochainComplex.Plus.quasiIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Plus`。
形式化陈述：quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of quasi-isomorphisms in the category of bounded
below cochain complexes.
-/
def quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance
/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithHomology C] : (quasiIso C).IsStableUnderRetracts := by
  dsimp [quasiIso]
  infer_instance

end

/-
**CochainComplex.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : (CochainComplex.plus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ ↦ ⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩⟩

end Plus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
/-- The functor on categories of bounded below cochain complexes that
is induced by a functor (which preserves zero morphisms). -/
@[simps!]
/-
**CategoryTheory.Functor.mapCochainComplexPlus** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor on categories of bounded below cochain complexes that
is induced by a functor (which preserves zero morphisms).
-/
def mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

/-- The isomorphism between `F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D`
and `CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _` when `F : C ⥤ D`
is a functor which preserves zero morphisms -/
@[simps!]
/-
**CategoryTheory.Functor.mapCochainComplexPlusComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D`
and `CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _` when `F : C ⥤ D`
is a functor which preserves zero morphisms
-/
def mapCochainComplexPlusCompι :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D ≅
      CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory

