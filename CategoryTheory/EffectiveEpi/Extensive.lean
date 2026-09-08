/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Preserving and reflecting effective epis on extensive categories

We prove that a functor between `FinitaryPreExtensive` categories preserves (resp. reflects) finite
effective epi families if it preserves (resp. reflects) effective epis.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [FinitaryPreExtensive C]

/-
**CategoryTheory.effectiveEpi_desc_iff_effectiveEpiFamily** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory`。
形式化陈述：effectiveEpi_desc_iff_effectiveEpiFamily {α : Type} [Finite α] {B : C} (X 
: α -> C) (π : (a : α) -> X a ⟶ B) : EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiF
amily X π
参数：X : α -> C；π : (a : α) -> X a ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasPullbacks_of_inclusions`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Finita
ryPreExtensive C] {X Z : C}   {α : Type u_1} (f : X …
· 使用定理 `CategoryTheory.Limits.instIsIsoDescι`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limit
s.HasCoproduct f],   Categ…
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.FinitaryPreEx
tensive C] {α : Type}   [inst_2 : Finite α] {…
· 使用定理 `CategoryTheory.instEffectiveEpiDescOfEffectiveEpiFamily`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} (X : α → 
C)   (π : (a : α) → X a ⟶ B) [inst_1 : Catego…
-/
theorem effectiveEpi_desc_iff_effectiveEpiFamily {α : Type} [Finite α]
    {B : C} (X : α → C) (π : (a : α) → X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h ↦ ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g ↦
    (FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a ↦ Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ ↦ inferInstance⟩

variable {D : Type*} [Category* D] [FinitaryPreExtensive D]
variable (F : C ⥤ D) [PreservesFiniteCoproducts F]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.ReflectsEffectiveEpis] : F.ReflectsFiniteEffectiveEpiFamilies where
  reflects {α _ B} X π h := by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    apply F.effectiveEpi_of_map
    convert!
      (inferInstance :
        EffectiveEpi (inv (sigmaComparison F X) ≫ (Sigma.desc (fun a ↦ F.map (π a)))))
    simp
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.PreservesEffectiveEpis] : F.PreservesFiniteEffectiveEpiFamilies where
  preserves {α _ B} X π h := by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    convert! (inferInstance : EffectiveEpi ((sigmaComparison F X) ≫ (F.map (Sigma.desc π))))
    simp

end CategoryTheory

