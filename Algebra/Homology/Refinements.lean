/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Refinements

This file contains lemmas about "refinements" that are specific to
the study of the homology of `HomologicalComplex`. General
lemmas about refinements and the case of `ShortComplex` appear
in the file `Mathlib/CategoryTheory/Abelian/Refinements.lean`.

-/

public section

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

namespace HomologicalComplex

/-
**HomologicalComplex.exactAt_iff_exact_up_to_refinements** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex`。
形式化陈述：exactAt_iff_exact_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ forall ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k 
= 0), exists (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = x₁ ≫ 
K.d i j
参数：i j k : ι；hi : c.prev j = i；hk : c.next j = k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
-/
lemma exactAt_iff_exact_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = x₁ ≫ K.d i j := by
  rw [K.exactAt_iff' i j k hi hk]
  exact (K.sc' i j k).exact_iff_exact_up_to_refinements
/-
**HomologicalComplex.eq_liftCycles_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_liftCycles_homologyπ_up_to_refinements {A : C} {i : ι} (γ : A ⟶ K.homology i)
    (j : ι) (hj : c.next i = j) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ K.X i) (hz : z ≫ K.d i j = 0),
      π ≫ γ = K.liftCycles z j hj hz ≫ K.homologyπ i := by
  subst hj
  exact (K.sc i).eq_liftCycles_homologyπ_up_to_refinements γ
/-
**HomologicalComplex.liftCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {A : C} (x₂ : A ⟶ K.X j) (hx₂ : x₂ ≫ K.d j k = 0) :
    K.liftCycles x₂ k hk hx₂ ≫ K.homologyπ j = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = x₁ ≫ K.d i j := by
  subst hi hk
  exact (K.sc j).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements x₂ hx₂
/-
**HomologicalComplex.liftCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {A : C} (x₂ x₂' : A ⟶ K.X j) (hx₂ : x₂ ≫ K.d j k = 0) (hx₂' : x₂' ≫ K.d j k = 0) :
    K.liftCycles x₂ k hk hx₂ ≫ K.homologyπ j = K.liftCycles x₂' k hk hx₂' ≫ K.homologyπ j ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = π ≫ x₂' + x₁ ≫ K.d i j := by
  subst hi hk
  exact (K.sc j).liftCycles_comp_homologyπ_eq_iff_up_to_refinements x₂ x₂' hx₂ hx₂'
/-
**HomologicalComplex.comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_homologyπ_eq_zero_iff_up_to_refinements
    (i j : ι) (hi : c.prev j = i)
    {A : C} (z₂ : A ⟶ K.cycles j) : z₂ ≫ K.homologyπ j = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ z₂ = x₁ ≫ K.toCycles i j := by
  subst hi
  exact (K.sc j).comp_homologyπ_eq_zero_iff_up_to_refinements z₂
/-
**HomologicalComplex.comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_homologyπ_eq_iff_up_to_refinements
    (i j : ι) (hi : c.prev j = i)
    {A : C} (z₂ z₂' : A ⟶ K.cycles j) : z₂ ≫ K.homologyπ j = z₂' ≫ K.homologyπ j ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i),
        π ≫ z₂ = π ≫ z₂' + x₁ ≫ K.toCycles i j := by
  subst hi
  exact (K.sc j).comp_homologyπ_eq_iff_up_to_refinements z₂ z₂'
/-
**HomologicalComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements** 是 Mathlib 中的
一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：comp_pOpcycles_eq_zero_iff_up_to_refinements {A : C} {i : ι} (z : A ⟶ K.X 
i) (j : ι) (hj : c.prev i = j) : z ≫ K.pOpcycles i = 0 ↔ exists (A' : C) (π : A'
 ⟶ A) (_ : Epi π) (x : A' ⟶ K.X j), π ≫ z = x ≫ K.d j i
参数：z : A ⟶ K.X i；j : ι；hj : c.prev i = j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.ShortComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categ
oryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C} {A …
-/
lemma comp_pOpcycles_eq_zero_iff_up_to_refinements
      {A : C} {i : ι} (z : A ⟶ K.X i) (j : ι) (hj : c.prev i = j) :
      z ≫ K.pOpcycles i = 0 ↔
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ K.X j), π ≫ z = x ≫ K.d j i := by
  subst hj
  apply (K.sc i).comp_pOpcycles_eq_zero_iff_up_to_refinements

variable {K L}
/-
**HomologicalComplex.mono_homologyMap_iff_up_to_refinements** 是 Mathlib 中的一个引理，位
于命名空间 `HomologicalComplex`。
形式化陈述：mono_homologyMap_iff_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk
 : c.next j = k) : Mono (homologyMap φ j) ↔ forall ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ :
 x₂ ≫ K.d j k = 0) (y₁ : A ⟶ L.X i) (_ : x₂ ≫ φ.f j = y₁ ≫ L.d i j), exists (A' 
: C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = x₁ ≫ K.d i j
参数：i j k : ι；hi : c.prev j = i；hk : c.next j = k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.ShortComplex.mono_homologyMap_iff_up_to_refinements`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Abelian C]   {S₁ S₂ : CategoryTheory.ShortComplex C}…
-/
lemma mono_homologyMap_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Mono (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0) (y₁ : A ⟶ L.X i)
          (_ : x₂ ≫ φ.f j = y₁ ≫ L.d i j),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i),
          π ≫ x₂ = x₁ ≫ K.d i j := by
  subst hi hk
  apply ShortComplex.mono_homologyMap_iff_up_to_refinements
/-
**HomologicalComplex.epi_homologyMap_iff_up_to_refinements** 是 Mathlib 中的一个引理，位于
命名空间 `HomologicalComplex`。
形式化陈述：epi_homologyMap_iff_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk 
: c.next j = k) : Epi (homologyMap φ j) ↔ forall ⦃A : C⦄ (y₂ : A ⟶ L.X j) (_ : y
₂ ≫ L.d j k = 0), exists (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ K.X j) (_ 
: x₂ ≫ K.d j k = 0) (y₁ : A' ⟶ L.X i), π ≫ y₂ = x₂ ≫ φ.f j + y₁ ≫ L.d i j
参数：i j k : ι；hi : c.prev j = i；hk : c.next j = k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.ShortComplex.epi_homologyMap_iff_up_to_refinements`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Abelian C]   {S₁ S₂ : CategoryTheory.ShortComplex C}…
-/
lemma epi_homologyMap_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Epi (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ L.X j) (_ : y₂ ≫ L.d j k = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0)
          (y₁ : A' ⟶ L.X i), π ≫ y₂ = x₂ ≫ φ.f j + y₁ ≫ L.d i j := by
  subst hi hk
  apply ShortComplex.epi_homologyMap_iff_up_to_refinements

end HomologicalComplex

