/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.TotalComplex

/-! # The symmetry of the total complex of a bicomplex

Let `K : HomologicalComplex₂ C c₁ c₂` be a bicomplex. If we assume both
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we may form
the total complex `K.total c` and `K.flip.total c`.

In this file, we show that if we assume `[TotalComplexShapeSymmetry c₁ c₂ c]`,
then there is an isomorphism `K.totalFlipIso c : K.flip.total c ≅ K.total c`.

Moreover, if we also have `[TotalComplexShapeSymmetry c₂ c₁ c]` and that the signs
are compatible `[TotalComplexShapeSymmetrySymmetry c₁ c₂ c]`, then the isomorphisms
`K.totalFlipIso c` and `K.flip.totalFlipIso c` are inverse to each other.

-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

/-
**HomologicalComplex₂.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasTotal c] : K.flip.HasTotal c := fun j =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) _
    (ComplexShape.symmetryEquiv c₁ c₂ c j) (fun _ => Iso.refl _)
/-
**HomologicalComplex₂.flip_hasTotal_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex₂`。
形式化陈述：flip_hasTotal_iff : K.flip.HasTotal c ↔ K.HasTotal c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex₂.instHasTotalFlip`：∀ {C : Type u_1} {I₁ : Type u_2} {
I₂ : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Pre…
-/
lemma flip_hasTotal_iff : K.flip.HasTotal c ↔ K.HasTotal c := by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

variable [K.HasTotal c] [DecidableEq J]

attribute [local simp] smul_smul

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `totalFlipIso`. -/
/-
**HomologicalComplex₂.totalFlipIsoX** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x₂`。
形式化陈述：totalFlipIsoX (j : J) : (K.flip.total c).X j ≅ (K.total c).X j where hom
参数：j : J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex₂.instHasTotalFlip`：∀ {C : Type u_1} {I₁ : Type u_2} {
I₂ : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Pre…

--- 原说明 ---
Auxiliary definition for `totalFlipIso`.
-/
noncomputable def totalFlipIsoX (j : J) : (K.flip.total c).X j ≅ (K.total c).X j where
  hom := K.flip.totalDesc (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j (by
    rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]))
  inv := K.totalDesc (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j (by
    rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]))
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex₂.totalFlipIsoX_hom_D** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma totalFlipIsoX_hom_D₁ (j j' : J) :
    (K.totalFlipIsoX c j).hom ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIsoX c j').hom := by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc, Linear.units_smul_comp, ι_D₁, ι_D₂_assoc]
    dsimp
    by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
    · have h₃ : ComplexShape.π c₂ c₁ c ⟨i₂, c₁.next i₁⟩ = j' := by
        rw [← ComplexShape.next_π₂ c₂ c i₂ h₂, h₁, c.next_eq' h₀]
      have h₄ : ComplexShape.π c₁ c₂ c ⟨c₁.next i₁, i₂⟩ = j' := by
        rw [← h₃, ComplexShape.π_symm c₁ c₂ c]
      rw [K.d₁_eq _ h₂ _ _ h₄, K.flip.d₂_eq _ _ h₂ _ h₃, Linear.units_smul_comp,
        assoc, ι_totalDesc, Linear.comp_units_smul, smul_smul, smul_smul,
        ComplexShape.σ_ε₁ c₂ c h₂ i₂]
      dsimp only [flip_X_X, flip_X_d]
    · rw [K.d₁_eq_zero _ _ _ _ h₂, K.flip.d₂_eq_zero _ _ _ _ h₂, smul_zero, zero_comp]
  · rw [K.D₁_shape _ _ _ h₀, K.flip.D₂_shape c _ _ h₀, zero_comp, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex₂.totalFlipIsoX_hom_D** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma totalFlipIsoX_hom_D₂ (j j' : J) :
    (K.totalFlipIsoX c j).hom ≫ K.D₂ c j j' =
      K.flip.D₁ c j j' ≫ (K.totalFlipIsoX c j').hom := by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [totalFlipIsoX]
    rw [ι_totalDesc_assoc, Linear.units_smul_comp, ι_D₂, ι_D₁_assoc]
    dsimp
    by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
    · have h₃ : ComplexShape.π c₂ c₁ c (ComplexShape.next c₂ i₂, i₁) = j' := by
        rw [← ComplexShape.next_π₁ c₁ c h₂ i₁, h₁, c.next_eq' h₀]
      have h₄ : ComplexShape.π c₁ c₂ c (i₁, ComplexShape.next c₂ i₂) = j' := by
        rw [← h₃, ComplexShape.π_symm c₁ c₂ c]
      rw [K.d₂_eq _ _ h₂ _ h₄, K.flip.d₁_eq _ h₂ _ _ h₃, Linear.units_smul_comp,
        assoc, ι_totalDesc, Linear.comp_units_smul, smul_smul, smul_smul,
        ComplexShape.σ_ε₂ c₁ c i₁ h₂]
      rfl
    · rw [K.d₂_eq_zero _ _ _ _ h₂, K.flip.d₁_eq_zero _ _ _ _ h₂, smul_zero, zero_comp]
  · rw [K.D₂_shape _ _ _ h₀, K.flip.D₁_shape c _ _ h₀, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The symmetry isomorphism `K.flip.total c ≅ K.total c` of the total complex of a
bicomplex when we have `[TotalComplexShapeSymmetry c₁ c₂ c]`. -/
/-
**HomologicalComplex₂.totalFlipIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
₂`。
形式化陈述：totalFlipIso : K.flip.total c ≅ K.total c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex₂.instHasTotalFlip`：∀ {C : Type u_1} {I₁ : Type u_2} {
I₂ : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Pre…

--- 原说明 ---
The symmetry isomorphism `K.flip.total c ≅ K.total c` of the total complex of a
bicomplex when we have `[TotalComplexShapeSymmetry c₁ c₂ c]`.
-/
noncomputable def totalFlipIso : K.flip.total c ≅ K.total c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalFlipIsoX c) (fun j j' _ => by
    simp only [total_d, Preadditive.comp_add, totalFlipIsoX_hom_D₁,
      totalFlipIsoX_hom_D₂, Preadditive.add_comp]
    rw [add_comm])

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex₂.totalFlipIso_hom_f_D** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma totalFlipIso_hom_f_D₁ (j j' : J) :
    (K.totalFlipIso c).hom.f j ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIso c).hom.f j' := by
  apply totalFlipIsoX_hom_D₁

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex₂.totalFlipIso_hom_f_D** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma totalFlipIso_hom_f_D₂ (j j' : J) :
    (K.totalFlipIso c).hom.f j ≫ K.D₂ c j j' =
      K.flip.D₁ c j j' ≫ (K.totalFlipIso c).hom.f j' := by
  apply totalFlipIsoX_hom_D₂

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex₂.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTotal_totalFlipIso_f_hom
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₂ c₁ c (i₂, i₁) = j) :
    K.flip.ιTotal c i₂ i₁ j h ≫ (K.totalFlipIso c).hom.f j =
      ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]) := by
  simp [totalFlipIso, totalFlipIsoX]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex₂.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTotal_totalFlipIso_f_inv
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    K.ιTotal c i₁ i₂ j h ≫ (K.totalFlipIso c).inv.f j =
      ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]) := by
  simp [totalFlipIso, totalFlipIsoX]
/-
**HomologicalComplex₂.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : K.flip.flip.HasTotal c := (inferInstance : K.HasTotal c)

section

variable [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex₂.flip_totalFlipIso** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex₂`。
形式化陈述：flip_totalFlipIso : K.flip.totalFlipIso c = (K.totalFlipIso c).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `HomologicalComplex₂.instHasTotalFlip`：∀ {C : Type u_1} {I₁ : Type u_2} {
I₂ : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Pre…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex₂.total.hom_ext`：hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K
.total c₁₂).X i₁₂ ⟶ A} (h : forall (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c
₂ c₁₂ (i₁, i₂) = i₁₂), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用引理 `HomologicalComplex₂.ιTotal_totalFlipIso_f_hom`：ιTotal_totalFlipIso_f_hom
 (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₂ c₁ c (i₂, i₁) = j) : K.flip.
ιTotal c i₂ i₁ j h ≫ (K.totalFlipIs…
· 使用引理 `HomologicalComplex₂.ιTotal_totalFlipIso_f_inv`：ιTotal_totalFlipIso_f_inv
 (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) : K.ιTota
l c i₁ i₂ j h ≫ (K.totalFlipIso c).…
· 使用引理 `ComplexShape.σ_symm`：σ_symm (i₁ : I₁) (i₂ : I₂) : σ c₂ c₁ c₁₂ i₂ i₁ = σ 
c₁ c₂ c₁₂ i₁ i₂
-/
lemma flip_totalFlipIso : K.flip.totalFlipIso c = (K.totalFlipIso c).symm := by
  ext j i₁ i₂ h
  rw [Iso.symm_hom, ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_flip]
  rw [ιTotal_totalFlipIso_f_inv, ComplexShape.σ_symm]

end

end HomologicalComplex₂

