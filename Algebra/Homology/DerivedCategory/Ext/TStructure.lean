/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Morphisms between bounded complexes are small

Let `C` be an abelian category. Assuming `HasExt.{w} C`, we show that
if two cochain complexes `K` and `L` are cohomologically in a single degree,
then the type of morphisms from `K` to `L⟦n⟧` in the derived category is `w`-small
for any `n : ℤ`, which we phrase here by saying that
`HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso _ _) ℤ K L` hold.

## TODO
* When more definitions are introduced for t-structures (e.g. the heart),
  show that the conclusion holds when `K` and `L` are cohomologically bounded.

-/

public section

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

namespace HasExt

variable {C} in
/-
**CategoryTheory.HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.HasExt`。
形式化陈述：hasSmallLocalizedShiftedHom_of_isLE_of_isGE [HasExt.{w} C] (K L : CochainC
omplex C Int) (a b : Int) [K.IsGE a] [K.IsLE a] [L.IsGE b] [L.IsLE b] : HasSmall
LocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up Int)) In
t K L
参数：K L : CochainComplex C Int；a b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用引理 `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`：exists_iso
_singleFunctor_obj_of_isGE_of_isLE (X : DerivedCategory C) (n : Int) [X.IsGE n] 
[X.IsLE n] : exists (Y : C), Nonempty (X ≅ (single…
· 使用定理 `DerivedCategory.instIsGEObjCochainComplexIntQOfIsGE`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : HasDerivedCategory C] (K : CochainC…
· 使用定理 `DerivedCategory.instIsLEObjCochainComplexIntQOfIsLE`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : HasDerivedCategory C] (K : CochainC…
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedShiftedHom_iff`：hasSmallLoc
alizedShiftedHom_iff (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] (X Y : C) 
: HasSmallLocalizedShiftedHom.{w} W M X Y ↔ foral…
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `CategoryTheory.instSmallHomDerivedCategoryObjSingleFunctorOfHasExt`：∀ (C
 : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Ab
elian C] [CategoryTheory.HasExt C]   (X Y : C) (a b : ℤ)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsEquivalenceShiftFunctor`：∀ (C : Type u) {A : Type u
_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst_2 : 
CategoryTheory.HasShift C A] (i : …
（共 43 条，此处仅展示前 30 条）
-/
lemma hasSmallLocalizedShiftedHom_of_isLE_of_isGE
    [HasExt.{w} C] (K L : CochainComplex C ℤ)
    (a b : ℤ) [K.IsGE a] [K.IsLE a] [L.IsGE b] [L.IsLE b] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L := by
  let := HasDerivedCategory.standard
  obtain ⟨X, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj K) a
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj L) b
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  exact fun p q ↦ small_of_injective (f := fun φ ↦
    ((singleFunctors C).shiftIso p (a - p) a (by simp)).inv.app X ≫
      eX.inv⟦p⟧' ≫ φ ≫ eY.hom⟦q⟧' ≫
        ((singleFunctors C).shiftIso q (b - q) b (by simp)).hom.app Y)
    (fun φ₁ φ₂ h ↦ by simpa [cancel_epi, cancel_mono] using h)
/-
**CategoryTheory.HasExt.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.HasExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExt.{w} C] (K L : CochainComplex C ℤ)
    [K.IsGE 0] [K.IsLE 0] [L.IsGE 0] [L.IsLE 0] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L :=
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0

end HasExt

end CategoryTheory

