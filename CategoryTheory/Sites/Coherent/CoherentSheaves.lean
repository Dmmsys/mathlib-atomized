/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the coherent topology

This file characterises sheaves for the coherent topology

## Main result

* `isSheaf_coherent`: a presheaf of types is a sheaf for the coherent topology if and only
  if it satisfies the sheaf condition with respect to every presieve consisting of a finite
  effective epimorphic family.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C]

universe w in
/-
**CategoryTheory.isSheaf_coherent** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) : Presieve.IsSheaf (coherentTopology C
) P ↔ (forall (B : C) (α : Type) [Finite α] (X : α -> C) (π : (a : α) -> (X a ⟶ 
B)), EffectiveEpiFamily X π -> (Presieve.ofArrows X π).IsSheafFor P)
参数：P : Cᵒᵖ ⥤ Type w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (coherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      EffectiveEpiFamily X π → (Presieve.ofArrows X π).IsSheafFor P) := by
  constructor
  · intro hP B α _ X π h
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    apply hP
    exact ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS

namespace coherentTopology

/-- Every Yoneda-presheaf is a sheaf for the coherent topology. -/
/-
**CategoryTheory.coherentTopology.isSheaf_yoneda_obj** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.coherentTopology`。
形式化陈述：isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda
.obj W)
参数：W : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isSheaf_coherent`：isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) : P
resieve.IsSheaf (coherentTopology C) P ↔ (forall (B : C) (α : Type) [Finite α] (
X : α -> C) (π : (a :…
· 使用定理 `CategoryTheory.EffectiveEpiFamily.effectiveEpiFamily`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {B : C} {α : Type u_2} {X : α → C} 
  {π : (a : α) → X a ⟶ B} [self : Category…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.sieveExtend`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor
 Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Sieve.forallYonedaIsSheaf_iff_colimit`：forallYonedaIsShea
f_iff_colimit (S : Sieve X) : (forall W : C, Presieve.IsSheafFor (yoneda.obj W) 
(S : Presieve X)) ↔ Nonempty (IsColimit S.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generateFamily_eq`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {B : C} {α : Type u_1} (X : α → C) (π : (a : α) → X a ⟶
 B),   CategoryTheory.Sieve.…
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Presieve.restrict_extend`：restrict_extend {x : FamilyOfEl
ements P R} (t : x.Compatible) : x.sieveExtend.restrict (le_generate R) = x
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_restrict`：isAmalgamation_restrict
 {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂) (t : P.obj (op 
X)) (ht : x.IsAmalgamation t) : (x.re…
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_sieveExtend`：isAmalgamation_sieve
Extend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X)) (ht : x.Is
Amalgamation t) : x.sieveExtend.IsAmalga…

--- 原说明 ---
Every Yoneda-presheaf is a sheaf for the coherent topology.
-/
theorem isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [← Sieve.generateFamily_eq] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows Y π)
  obtain ⟨t, t_amalg, t_uniq⟩ : ∃! t, x_ext.IsAmalgamation t :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict (Sieve.le_generate (Presieve.ofArrows Y π)) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

variable (C) in
/-- The coherent topology on a precoherent category is subcanonical. -/
/-
**CategoryTheory.coherentTopology.subcanonical** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.coherentTopology`。
形式化陈述：subcanonical : (coherentTopology C).Subcanonical
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用定理 `CategoryTheory.coherentTopology.isSheaf_yoneda_obj`：isSheaf_yoneda_obj (
W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W)

--- 原说明 ---
The coherent topology on a precoherent category is subcanonical.
-/
instance subcanonical : (coherentTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end coherentTopology

end CategoryTheory

