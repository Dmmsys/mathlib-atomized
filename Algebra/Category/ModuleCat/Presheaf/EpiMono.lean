/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits

/-!
# Epimorphisms and monomorphisms in the category of presheaves of modules

In this file, we give characterizations of epimorphisms and monomorphisms
in the category of presheaves of modules.

-/

public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

/-
**PresheafOfModules.epi_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：epi_of_surjective (hf : forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) :
 Epi f where left_cancellation g₁ g₂ hg
参数：hf : forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
-/
lemma epi_of_surjective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m₁
/-
**PresheafOfModules.mono_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：mono_of_injective (hf : forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : 
Mono f where right_cancellation {M} g₁ g₂ hg
参数：hf : forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
-/
lemma mono_of_injective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m)

variable (f)
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Epi f] (X : Cᵒᵖ) : Epi (f.app X) :=
  inferInstanceAs (Epi ((evaluation R X).map f))
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] (X : Cᵒᵖ) : Mono (f.app X) :=
  inferInstanceAs (Mono ((evaluation R X).map f))
/-
**PresheafOfModules.surjective_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：surjective_of_epi [Epi f] (X : Cᵒᵖ) : Function.Surjective (f.app X)
参数：X : Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `PresheafOfModules.instEpiModuleCatCarrierObjOppositeRingCatApp`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryTheory.Functor 
Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfModules R} (f : M₁…
-/
lemma surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance
/-
**PresheafOfModules.injective_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：injective_of_mono [Mono f] (X : Cᵒᵖ) : Function.Injective (f.app X)
参数：X : Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `PresheafOfModules.instMonoModuleCatCarrierObjOppositeRingCatApp`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryTheory.Functor
 Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfModules R} (f : M₁…
-/
lemma injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance
/-
**PresheafOfModules.epi_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModu
les`。
形式化陈述：epi_iff_surjective : Epi f ↔ forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app 
X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.surjective_of_epi`：surjective_of_epi [Epi f] (X : Cᵒᵖ)
 : Function.Surjective (f.app X)
· 使用引理 `PresheafOfModules.epi_of_surjective`：epi_of_surjective (hf : forall ⦃X :
 Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where left_cancellation g₁ g₂ hg
-/
lemma epi_iff_surjective :
    Epi f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) :=
  ⟨fun _ ↦ surjective_of_epi f, epi_of_surjective⟩
/-
**PresheafOfModules.mono_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMod
ules`。
形式化陈述：mono_iff_surjective : Mono f ↔ forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app
 X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.injective_of_mono`：injective_of_mono [Mono f] (X : Cᵒᵖ
) : Function.Injective (f.app X)
· 使用引理 `PresheafOfModules.mono_of_injective`：mono_of_injective (hf : forall ⦃X :
 Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where right_cancellation {M} g₁ g₂
 hg
-/
lemma mono_iff_surjective :
    Mono f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) :=
  ⟨fun _ ↦ injective_of_mono f, mono_of_injective⟩

end PresheafOfModules

