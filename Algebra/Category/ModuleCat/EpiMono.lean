/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

@[expose] public section


universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
**ModuleCat.ker_eq_bot_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_cancel`：ker_eq_bot_of_cancel {f : M ->ₛₗ[τ₁₂] M₂
} (h : forall u v : ker f ->ₗ[R] M, f.comp u = f.comp v -> u = v) : ker f = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h
/-
**ModuleCat.range_eq_top_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_eq_top_of_cancel`：range_eq_top_of_cancel {f : M ->ₛₗ[τ₁₂
] M₂} (h : forall u v : M₂ ->ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f -> u = v)
 : range f = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h
/-
**ModuleCat.mono_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.ker_eq_bot_of_mono`：ker_eq_bot_of_mono [Mono f] : LinearMap.ke
r f.hom = ⊥
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert! LinearMap.ker_eq_bot.1 hf⟩
/-
**ModuleCat.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：mono_iff_injective : Mono f ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.mono_iff_ker_eq_bot`：mono_iff_ker_eq_bot : Mono f ↔ LinearMap.
ker f.hom = ⊥
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]
/-
**ModuleCat.epi_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.range_eq_top_of_epi`：range_eq_top_of_epi [Epi f] : LinearMap.r
ange f.hom = ⊤
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
-/
theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| by convert! LinearMap.range_eq_top.1 hf⟩
/-
**ModuleCat.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：epi_iff_surjective : Epi f ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.epi_iff_range_eq_top`：epi_iff_range_eq_top : Epi f ↔ LinearMap
.range f.hom = ⊤
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
@[instance_reducible]
/-
**ModuleCat.uniqueOfEpiZero** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M
参数：X；0 : X ⟶ of R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the zero morphism is an epi then the codomain is trivial.
-/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)
/-
**ModuleCat.mono_as_hom'_subtype** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X : ModuleCat R} (U : Submodule R ↑X), Cat
egoryTheory.Mono (ModuleCat.ofHom U.subtype)
参数：U : Submodule R ↑X；ModuleCat.ofHom U.subtype。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ModuleCat.mono_iff_ker_eq_bot`：mono_iff_ker_eq_bot : Mono f ↔ LinearMap.
ker f.hom = ⊥
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
instance mono_as_hom'_subtype (U : Submodule R X) : Mono (ModuleCat.ofHom U.subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)
/-
**ModuleCat.epi_as_hom''_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X : ModuleCat R} (U : Submodule R ↑X), Cat
egoryTheory.Epi (ModuleCat.ofHom U.mkQ)
参数：U : Submodule R ↑X；ModuleCat.ofHom U.mkQ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ModuleCat.epi_iff_range_eq_top`：epi_iff_range_eq_top : Epi f ↔ LinearMap
.range f.hom = ⊤
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
-/
instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (ModuleCat.ofHom U.mkQ) :=
  (epi_iff_range_eq_top _).mpr <| Submodule.range_mkQ _
/-
**ModuleCat.forget_preservesEpimorphisms** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorp
hisms where preserves f hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ofHom_epi_iff_surjective`：ofHom_epi_iff_surjective {X Y :
 Type u} (f : X -> Y) : Epi (ofHom f) ↔ Function.Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
-/
instance forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorphisms where
    preserves f hf := by
      rw [CategoryTheory.ofHom_epi_iff_surjective, ← epi_iff_surjective]
      exact hf
/-
**ModuleCat.forget_preservesMonomorphisms** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomo
rphisms where preserves f hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ofHom_mono_iff_injective`：ofHom_mono_iff_injective {X Y :
 Type u} (f : X -> Y) : Mono (ofHom f) ↔ Function.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
-/
instance forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomorphisms where
    preserves f hf := by
      rw [CategoryTheory.ofHom_mono_iff_injective, ← mono_iff_injective]
      exact hf

end ModuleCat

