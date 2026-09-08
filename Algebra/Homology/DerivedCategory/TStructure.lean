/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The canonical t-structure on the derived category

In this file, we introduce the canonical t-structure on the
derived category of an abelian category.

-/

@[expose] public section

open CategoryTheory Category Pretriangulated Triangulated Limits Preadditive

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical t-structure on `DerivedCategory C`. -/
/-
**DerivedCategory.TStructure.t** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.TStruc
ture`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : HasDerivedCategory C] → CategoryThe
ory.Triangulated.TStructure (DerivedCategory C)
参数：DerivedCategory C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The canonical t-structure on `DerivedCategory C`.
-/
noncomputable def TStructure.t : TStructure (DerivedCategory C) where
  le n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyLE n
  ge n X := ∃ (K : CochainComplex C ℤ) (_ : X ≅ DerivedCategory.Q.obj K), K.IsStrictlyGE n
  le_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  ge_isClosedUnderIsomorphisms n :=
    { of_iso := by
        rintro X Y e ⟨K, e', _⟩
        exact ⟨K, e.symm ≪≫ e', inferInstance⟩ }
  le_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyLE_shift n a n' h⟩
  ge_shift := by
    rintro n a n' h X ⟨K, e, _⟩
    exact ⟨(shiftFunctor (CochainComplex C ℤ) a).obj K,
      (shiftFunctor (DerivedCategory C) a).mapIso e ≪≫ (Q.commShiftIso a).symm.app K,
      K.isStrictlyGE_shift n a n' h⟩
  zero' X Y f := by
    rintro ⟨K, e₁, _⟩ ⟨L, e₂, _⟩
    rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom, comp_zero, zero_comp]
    apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE K L 0 1 (by simp)).elim
  le_zero_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyLE_of_le 0 1 (by lia)⟩
  ge_one_le := by
    rintro X ⟨K, e, _⟩
    exact ⟨K, e, K.isStrictlyGE_of_ge 0 1 (by lia)⟩
  exists_triangle_zero_one X := by
    obtain ⟨K, ⟨e₂⟩⟩ : ∃ K, Nonempty (Q.obj K ≅ X) := ⟨_, ⟨Q.objObjPreimageIso X⟩⟩
    have h := K.shortComplexTruncLE_shortExact 0
    refine ⟨Q.obj (K.truncLE 0), Q.obj (K.truncGE 1),
      ⟨_, Iso.refl _, inferInstance⟩, ⟨_, Iso.refl _, inferInstance⟩,
      Q.map (K.ιTruncLE 0) ≫ e₂.hom, e₂.inv ≫ Q.map (K.πTruncGE 1),
      inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by lia))) ≫ (triangleOfSES h).mor₃,
      isomorphic_distinguished _ (triangleOfSES_distinguished h) _ (Iso.symm ?_)⟩
    refine Triangle.isoMk _ _ (Iso.refl _) e₂
      (asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE 0 1 (by lia)))) ?_ ?_ (by simp)
    · dsimp
      rw [id_comp]
      rfl
    · dsimp
      rw [← Q.map_comp, CochainComplex.g_shortComplexTruncLEX₃ToTruncGE ..,
        Iso.hom_inv_id_assoc]

/-- Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure. -/
/-
**DerivedCategory.IsLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：IsLE (X : DerivedCategory C) (n : Int) : Prop
参数：X : DerivedCategory C；n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure.
-/
abbrev IsLE (X : DerivedCategory C) (n : ℤ) : Prop := TStructure.t.IsLE X n

/-- Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure. -/
/-
**DerivedCategory.IsGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：IsGE (X : DerivedCategory C) (n : Int) : Prop
参数：X : DerivedCategory C；n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
Given `X : DerivedCategory C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure.
-/
abbrev IsGE (X : DerivedCategory C) (n : ℤ) : Prop := TStructure.t.IsGE X n
/-
**DerivedCategory.isGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isGE_iff (X : DerivedCategory C) (n : Int) : X.IsGE n ↔ forall (i : Int) (
_ : i < n), IsZero ((homologyFunctor C i).obj X)
参数：X : DerivedCategory C；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用引理 `CochainComplex.exactAt_of_isGE`：exactAt_of_isGE (n i : Int) (hi : i < n
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `DerivedCategory.instEssSurjCochainComplexIntQ`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : 
HasDerivedCategory C], DerivedCateg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isGE_iff`：isGE_iff (n : Int) : K.IsGE n ↔ forall (i : Int
) (_ : i < n), K.ExactAt i
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CochainComplex.instQuasiIsoIntπTruncGEOfIsGE`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (K : CochainComplex C ℤ…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
-/
lemma isGE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncGE n, (Q.objObjPreimageIso X).symm ≪≫
      asIso (Q.map ((Q.objPreimage X).πTruncGE n)), inferInstance⟩
/-
**DerivedCategory.isLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isLE_iff (X : DerivedCategory C) (n : Int) : X.IsLE n ↔ forall (i : Int) (
_ : n < i), IsZero ((homologyFunctor C i).obj X)
参数：X : DerivedCategory C；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用引理 `CochainComplex.exactAt_of_isLE`：exactAt_of_isLE (n i : Int) (hi : n < i
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `DerivedCategory.instEssSurjCochainComplexIntQ`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : 
HasDerivedCategory C], DerivedCateg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isLE_iff`：isLE_iff (n : Int) : K.IsLE n ↔ forall (i : Int
) (_ : n < i), K.ExactAt i
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CochainComplex.instQuasiIsoIntιTruncLEOfIsLE`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (K : CochainComplex C ℤ…
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
-/
lemma isLE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncLE n, (Q.objObjPreimageIso X).symm ≪≫
      (asIso (Q.map ((Q.objPreimage X).ιTruncLE n))).symm, inferInstance⟩
/-
**DerivedCategory.isZero_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isZero_of_isGE (X : DerivedCategory C) (n i : Int) (hi : i < n) [hX : X.Is
GE n] : IsZero ((homologyFunctor _ i).obj X)
参数：X : DerivedCategory C；n i : Int；hi : i < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.isGE_iff`：isGE_iff (X : DerivedCategory C) (n : Int) : X
.IsGE n ↔ forall (i : Int) (_ : i < n), IsZero ((homologyFunctor C i).obj X)
-/
lemma isZero_of_isGE (X : DerivedCategory C) (n i : ℤ) (hi : i < n) [hX : X.IsGE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isGE_iff] at hX
  exact hX i hi
/-
**DerivedCategory.isZero_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isZero_of_isLE (X : DerivedCategory C) (n i : Int) (hi : n < i) [hX : X.Is
LE n] : IsZero ((homologyFunctor _ i).obj X)
参数：X : DerivedCategory C；n i : Int；hi : n < i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.isLE_iff`：isLE_iff (X : DerivedCategory C) (n : Int) : X
.IsLE n ↔ forall (i : Int) (_ : n < i), IsZero ((homologyFunctor C i).obj X)
-/
lemma isZero_of_isLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) [hX : X.IsLE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [isLE_iff] at hX
  exact hX i hi
/-
**DerivedCategory.isGE_Q_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isGE_Q_obj_iff (K : CochainComplex C Int) (n : Int) : (Q.obj K).IsGE n ↔ K
.IsGE n
参数：K : CochainComplex C Int；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HomologicalComplex.homologyFunctor_obj`：∀ (C : Type u_1) [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} (c : Com…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isGE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]
/-
**DerivedCategory.isLE_Q_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCategory`。
形式化陈述：isLE_Q_obj_iff (K : CochainComplex C Int) (n : Int) : (Q.obj K).IsLE n ↔ K
.IsLE n
参数：K : CochainComplex C Int；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HomologicalComplex.homologyFunctor_obj`：∀ (C : Type u_1) [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} (c : Com…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    (Q.obj K).IsGE n := by
  rw [isGE_Q_obj_iff]
  infer_instance
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsLE n] :
    (Q.obj K).IsLE n := by
  rw [isLE_Q_obj_iff]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isGE_of_iso e.symm n

set_option backward.defeqAttrib.useBackward true in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  let e := (singleFunctorIsoCompQ C n).app X
  dsimp only [Functor.comp_obj] at e
  exact TStructure.t.isLE_of_iso e.symm n
/-
**DerivedCategory.exists_iso_Q_obj_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCat
egory`。
形式化陈述：exists_iso_Q_obj_of_isLE (X : DerivedCategory C) (n : Int) [hX : X.IsLE n]
 : exists (K : CochainComplex C Int) (_ : K.IsStrictlyLE n), Nonempty (X ≅ Q.obj
 K)
参数：X : DerivedCategory C；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma exists_iso_Q_obj_of_isLE (X : DerivedCategory C) (n : ℤ) [hX : X.IsLE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyLE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩
/-
**DerivedCategory.exists_iso_Q_obj_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `DerivedCat
egory`。
形式化陈述：exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : Int) [hX : X.IsGE n]
 : exists (K : CochainComplex C Int) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj
 K)
参数：X : DerivedCategory C；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : ℤ) [hX : X.IsGE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩
/-
**DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `De
rivedCategory`。
形式化陈述：exists_iso_Q_obj_of_isGE_of_isLE (X : DerivedCategory C) (a b : Int) [X.Is
GE a] [X.IsLE b] : exists (K : CochainComplex C Int) (_ : K.IsStrictlyGE a) (_ :
 K.IsStrictlyLE b), Nonempty (X ≅ Q.obj K)
参数：X : DerivedCategory C；a b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.exists_iso_Q_obj_of_isLE`：exists_iso_Q_obj_of_isLE (X : 
DerivedCategory C) (n : Int) [hX : X.IsLE n] : exists (K : CochainComplex C Int)
 (_ : K.IsStrictlyLE n), Nonem…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DerivedCategory.isGE_Q_obj_iff`：isGE_Q_obj_iff (K : CochainComplex C Int
) (n : Int) : (Q.obj K).IsGE n ↔ K.IsGE n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_iso`：isGE_of_iso {X Y : C
} (e : X ≅ Y) (n : Int) [t.IsGE X n] : t.IsGE Y n where ge
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst :
 CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
· 使用定理 `HomologicalComplex.instIsStrictlySupportedTruncGE_1`：∀ {ι : Type u_1} {ι
' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst
 : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CochainComplex.instQuasiIsoIntπTruncGEOfIsGE`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (K : CochainComplex C ℤ…
-/
lemma exists_iso_Q_obj_of_isGE_of_isLE (X : DerivedCategory C) (a b : ℤ) [X.IsGE a] [X.IsLE b] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b),
      Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩
/-
**DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE** 是 Mathlib 中的一个引
理，位于命名空间 `DerivedCategory`。
形式化陈述：exists_iso_singleFunctor_obj_of_isGE_of_isLE (X : DerivedCategory C) (n : 
Int) [X.IsGE n] [X.IsLE n] : exists (Y : C), Nonempty (X ≅ (singleFunctor C n).o
bj Y)
参数：X : DerivedCategory C；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`：exists_iso_Q_obj_of_is
GE_of_isLE (X : DerivedCategory C) (a b : Int) [X.IsGE a] [X.IsLE b] : exists (K
 : CochainComplex C Int) (_ : K.IsStri…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CochainComplex.exists_iso_single`：exists_iso_single (n : Int) [K.IsStric
tlyGE n] [K.IsStrictlyLE n] : exists (M : C), Nonempty (K ≅ (single _ _ n).obj M
)
-/
lemma exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    ∃ (Y : C), Nonempty (X ≅ (singleFunctor C n).obj Y) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

open DerivedCategory.TStructure

variable (C)

/-- The bounded above derived category of an abelian category. -/
/-
**DerivedCategory.Minus** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：Minus : Type max u v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The bounded above derived category of an abelian category.
-/
abbrev Minus : Type max u v := (t : TStructure (DerivedCategory C)).minus.FullSubcategory

/-- The bounded below derived category of an abelian category. -/
/-
**DerivedCategory.Plus** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：Plus : Type max u v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The bounded below derived category of an abelian category.
-/
abbrev Plus : Type max u v := (t : TStructure (DerivedCategory C)).plus.FullSubcategory

/-- The bounded derived category of an abelian category. -/
/-
**DerivedCategory.Bounded** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
形式化陈述：Bounded : Type max u v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…

--- 原说明 ---
The bounded derived category of an abelian category.
-/
abbrev Bounded : Type max u v := (t : TStructure (DerivedCategory C)).bounded.FullSubcategory

variable {C}

/-- The inclusion of the bounded above derived category. -/
/-
**DerivedCategory.Minus.** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the bounded above derived category.
-/
noncomputable abbrev Minus.ι : Minus C ⥤ DerivedCategory C := t.minus.ι

/-- The inclusion of the bounded below derived category. -/
/-
**DerivedCategory.Plus.** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the bounded below derived category.
-/
noncomputable abbrev Plus.ι : Plus C ⥤ DerivedCategory C := t.plus.ι

/-- The inclusion of the bounded derived category. -/
/-
**DerivedCategory.Bounded.** 是 Mathlib 中的一个缩写定义，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the bounded derived category.
-/
noncomputable abbrev Bounded.ι : Bounded C ⥤ DerivedCategory C := t.bounded.ι

end DerivedCategory

