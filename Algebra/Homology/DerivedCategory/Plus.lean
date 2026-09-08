/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The bounded below derived category

Let `C` be an abelian category. In this file, we show that
the bounded below derived category `DerivedCategory.Plus C` (defined
as a full subcategory of `DerivedCategory C`) is the localization
of the bounded below homotopy category `HomotopyCategory.Plus C`
with respect to quasi-isomorphisms.

-/

@[expose] public section

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace HomotopyCategory.Plus

variable (C)

/-- The property of objects in `HomotopyCategory.Plus C` that is satisfied
by acyclic complexes. -/
/-
**HomotopyCategory.Plus.subcategoryAcyclic** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopy
Category.Plus`。
形式化陈述：subcategoryAcyclic : ObjectProperty (HomotopyCategory.Plus C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in `HomotopyCategory.Plus C` that is satisfied
by acyclic complexes.
-/
abbrev subcategoryAcyclic :
    ObjectProperty (HomotopyCategory.Plus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW** 是 Mathlib 中的一个引理，位于
命名空间 `HomotopyCategory.Plus`。
形式化陈述：quasiIso_eq_subcategoryAcyclic_trW : HomotopyCategory.Plus.quasiIso C = (s
ubcategoryAcyclic C).trW
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.ObjectProperty.instHasZeroObjectFullSubcategoryOfContains
Zero`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C) [P.ContainsZero],   CategoryTheory.Limits.Has…
· 使用定理 `HomotopyCategory.instContainsZeroIntUpPlusOfHasZeroObject`：∀ (C : Type u
_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [CategoryTheory.Limits.HasZeroObjec…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomotopyCategory.instIsStableUnderShiftIntUpPlus`：∀ (C : Type u_1) [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
,   (HomotopyCategory.plus C).IsStable…
· 使用定理 `CategoryTheory.ObjectProperty.instAdditiveFullSubcategoryShiftFunctor`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheor
y.ObjectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `HomotopyCategory.instIsTriangulatedIntUpPlus`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Lim
its.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff_of_distinguished`：trW_iff_of_disti
nguished [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T in distTriang C)
 : P.trW T.mor₁ ↔ P T.obj₃
· 使用定理 `HomotopyCategory.instIsClosedUnderIsomorphismsIntUpSubcategoryAcyclic`：∀
 (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.Abelian C],   (HomotopyCategory.subcategoryAcyclic C).IsCl…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedFullSubcategoryι`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsInverseImage`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 
: CategoryTheory.Category.{v', u'} D]   (P : CategoryTheory.O…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`：quasiIso_eq_trW_sub
categoryAcyclic : quasiIso C (ComplexShape.up Int) = (subcategoryAcyclic C).trW
-/
lemma quasiIso_eq_subcategoryAcyclic_trW :
    HomotopyCategory.Plus.quasiIso C = (subcategoryAcyclic C).trW := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Plus.ι C).map_distinguished _ mem)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at this
  rwa [dsimp% (subcategoryAcyclic C).trW_iff_of_distinguished _ mem]

end HomotopyCategory.Plus

namespace DerivedCategory

open TStructure

variable [HasDerivedCategory C]

namespace Plus

/-- The localization functor `HomotopyCategory.Plus C ⥤ DerivedCategory.Plus C`. -/
/-
**DerivedCategory.Plus.Qh** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.Plus`。
形式化陈述：Qh : HomotopyCategory.Plus C ⥤ Plus C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The localization functor `HomotopyCategory.Plus C ⥤ DerivedCategory.Plus C`.
-/
noncomputable def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hK
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app K) n⟩)
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Qh : _ ⥤ Plus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**DerivedCategory.Plus.Qh_map_bijective_of_isKInjective** 是 Mathlib 中的一个引理，位于命名空
间 `DerivedCategory.Plus`。
形式化陈述：Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C) (_ : Coch
ainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) -> _)
参数：K L : HomotopyCategory.Plus C；_ : CochainComplex.IsKInjective L.1.as。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `CochainComplex.IsKInjective.Qh_map_bijective`：Qh_map_bijective [HasDeriv
edCategory C] (K : HomotopyCategory C (ComplexShape.up Int)) (L : CochainComplex
 C Int) [L.IsKInjective] : Functio…
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_bijective`：map_bijective (X Y :
 C) : Function.Bijective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
-/
lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) → _) := by
  have := CochainComplex.IsKInjective.Qh_map_bijective K.1 L.1.as
  rw [← Function.Bijective.of_comp_iff _
    ((HomotopyCategory.Plus.fullyFaithfulι C).map_bijective _ _)] at this
  rwa [← Function.Bijective.of_comp_iff' (t.plus.fullyFaithfulι.map_bijective _ _)]
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.plus C).IsVerdierRightLocalizing
    (HomotopyCategory.subcategoryAcyclic C) where
  fac {K L} φ hK hL := by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hL
    obtain ⟨n, hn⟩ := hL
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    refine ⟨(HomotopyCategory.quotient _ _).obj (K.truncGE n),
      (HomotopyCategory.quotient _ _).map (K.πTruncGE n),
      (HomotopyCategory.quotient _ _).map (CochainComplex.truncGEMap φ n ≫ inv (L.πTruncGE n)),
      ?_, ?_, by simp [← Functor.map_comp]⟩
    · simp only [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hK.truncGE _

variable (C)

/-- The functor `DerivedCategory.Plus.Qh : HomotopyCategory.Plus C ⥤ DerivedCategory.Plus C`
is induced by `DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory C`. -/
/-
**DerivedCategory.Plus.QhComp** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `DerivedCategory.Plus.Qh : HomotopyCategory.Plus C ⥤ DerivedCategory
.Plus C`
is induced by `DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory
 C`.
-/
noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Plus.ι ≅ HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh := Iso.refl _
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).EssSurj where
  mem_essImage := by
    intro ⟨X, n, K, e, h⟩
    refine ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, ?_⟩,
      ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
    simp only [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨n, h⟩
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).trW :=
  ((HomotopyCategory.plus C).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic C)).isLocalization_of_isLocalizedFullyFaithful
      (QhCompιIsoιCompQh C).symm
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C) := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

/-- The single functors `C ⥤ DerivedCategory.Plus C` for all `n : ℤ` along with
their compatibilities with shifts. -/
/-
**DerivedCategory.Plus.singleFunctors** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory
.Plus`。
形式化陈述：singleFunctors : SingleFunctors C (Plus C) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The single functors `C ⥤ DerivedCategory.Plus C` for all `n : ℤ` along with
their compatibilities with shifts.
-/
noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

/-- The single functor `C ⥤ DerivedCategory.Plus C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
/-
**DerivedCategory.Plus.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategor
y.Plus`。
形式化陈述：singleFunctor (n : Int) : C ⥤ Plus C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The single functor `C ⥤ DerivedCategory.Plus C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`.
-/
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

/-- The single functors on `DerivedCategory.Plus C` are induced by the
single functors on `DerivedCategory C`. -/
/-
**DerivedCategory.Plus.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategor
y.Plus`。
形式化陈述：singleFunctor (n : Int) : C ⥤ Plus C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The single functors on `DerivedCategory.Plus C` are induced by the
single functors on `DerivedCategory C`.
-/
noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ Plus.ι ≅ DerivedCategory.singleFunctor C n :=
  Iso.refl _
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

/-- The homology functor `DerivedCategory.Plus C ⥤ C` in degree `n : ℤ`. -/
/-
**DerivedCategory.Plus.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategor
y.Plus`。
形式化陈述：homologyFunctor (n : Int) : Plus C ⥤ C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The homology functor `DerivedCategory.Plus C ⥤ C` in degree `n : ℤ`.
-/
noncomputable def homologyFunctor (n : ℤ) : Plus C ⥤ C :=
  Plus.ι ⋙ DerivedCategory.homologyFunctor C n
deriving Functor.IsHomological
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _
    (HomotopyCategory.Plus.subcategoryAcyclic C).trW

variable {C}

/-- The canonical t-structure on `DerivedCategory.Plus C`. -/
/-
**DerivedCategory.Plus.TStructure.t** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.P
lus.TStructure`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Abelian C] →       [inst_2 : HasDerivedCategory C] → Categ
oryTheory.Triangulated.TStructure (DerivedCategory.Plus C)
参数：DerivedCategory.Plus C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The canonical t-structure on `DerivedCategory.Plus C`.
-/
noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Plus C) :=
  (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

/-- Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure. -/
/-
**DerivedCategory.Plus.IsGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory.Plus`。
形式化陈述：IsGE (X : Plus C) (n : Int) : Prop
参数：X : Plus C；n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure.
-/
abbrev IsGE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsGE X n

/-- Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure. -/
/-
**DerivedCategory.Plus.IsLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory.Plus`。
形式化陈述：IsLE (X : Plus C) (n : Int) : Prop
参数：X : Plus C；n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure.
-/
abbrev IsLE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsLE X n
/-
**DerivedCategory.Plus.isGE_** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isGE_ι_obj_iff (X : Plus C) (n : ℤ) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h ↦ ⟨h.1⟩
/-
**DerivedCategory.Plus.isLE_** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLE_ι_obj_iff (X : Plus C) (n : ℤ) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h ↦ ⟨h.1⟩
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Plus C) (n : ℤ) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Plus C) (n : ℤ) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence ℤ :=
  inferInstanceAs ((ι ⋙ DerivedCategory.homologyFunctor C 0).ShiftSequence ℤ)
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  rw [← isGE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  rw [← isLE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance
/-
**DerivedCategory.Plus.isZero_homology_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `Derive
dCategory.Plus`。
形式化陈述：isZero_homology_of_isGE (X : Plus C) (n : Int) [X.IsGE n] (i : Int) (hi : 
i < n) : IsZero ((homologyFunctor C i).obj X)
参数：X : Plus C；n : Int；i : Int；hi : i < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DerivedCategory.isZero_of_isGE`：isZero_of_isGE (X : DerivedCategory C) (
n i : Int) (hi : i < n) [hX : X.IsGE n] : IsZero ((homologyFunctor _ i).obj X)
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `DerivedCategory.Plus.instIsGEObjιOfIsGE`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : 
HasDerivedCategory C] (X : De…
-/
lemma isZero_homology_of_isGE
    (X : Plus C) (n : ℤ) [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi
/-
**DerivedCategory.Plus.isZero_homology_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `Derive
dCategory.Plus`。
形式化陈述：isZero_homology_of_isLE (X : Plus C) (n : Int) [X.IsLE n] (i : Int) (hi : 
n < i) : IsZero ((homologyFunctor C i).obj X)
参数：X : Plus C；n : Int；i : Int；hi : n < i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DerivedCategory.isZero_of_isLE`：isZero_of_isLE (X : DerivedCategory C) (
n i : Int) (hi : n < i) [hX : X.IsLE n] : IsZero ((homologyFunctor _ i).obj X)
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `DerivedCategory.Plus.instIsLEObjιOfIsLE`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : 
HasDerivedCategory C] (X : De…
-/
lemma isZero_homology_of_isLE
    (X : Plus C) (n : ℤ) [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi
/-
**DerivedCategory.Plus.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory.Plus
`。
形式化陈述：isIso_iff {X Y : Plus C} (f : X ⟶ Y) : IsIso f ↔ forall (n : Int), IsIso (
(homologyFunctor C n).map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.isIso_iff`：isIso_iff {K L : DerivedCategory C} (f : K ⟶ 
L) : IsIso f ↔ forall (n : Int), IsIso ((homologyFunctor C n).map f)
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f
-/
lemma isIso_iff {X Y : Plus C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  refine ⟨fun _ _ ↦ inferInstance, fun _ ↦ ?_⟩
  have : IsIso (ι.map f) := by rwa [DerivedCategory.isIso_iff]
  exact isIso_of_fully_faithful ι _

/-- The localization functor `CochainComplex.Plus C ⥤ DerivedCategory.Plus C`. -/
/-
**DerivedCategory.Plus.Q** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.Plus`。
形式化陈述：Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The localization functor `CochainComplex.Plus C ⥤ DerivedCategory.Plus C`.
-/
noncomputable def Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C :=
  HomotopyCategory.Plus.quotient C ⋙ Qh

-- TODO: show that `Q` is indeed a localization functor with respect to quasi-isomorphisms

end Plus

end DerivedCategory

