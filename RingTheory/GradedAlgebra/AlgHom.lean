/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `R`-linear homomorphisms of graded algebras

This file defines bundled `R`-linear homomorphisms of graded `R`-algebras.

## Main definitions

* `GradedAlgHom R 𝒜 ℬ`: the type of `R`-linear homomorphisms of `R`-graded algebras `𝒜` to `ℬ`.

## Notation

* `𝒜 →ₐᵍ[R] ℬ` : `R`-linear graded homomorphism from `𝒜` to `ℬ`.
-/

@[expose] public section

/-- An `R`-linear homomorphism of graded algebras, denoted `𝒜 →ₐᵍ[R] ℬ`. -/
/-
**GradedAlgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   {A : Type u_2} →     {B : Type u_3} →       {ι : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : Semiring A] →       
      [inst_2 : Semiring B] →               [inst_3 : Algebra R A] →            
     [inst_4 : Algebra R B] →                   [inst_5 : DecidableEq ι] →      
               [inst_6 : AddMonoid ι] →                       (𝒜 : ι → Submodule
 R A) →                         (ℬ : ι → Submodule R B) → [GradedAlgebra 𝒜] → [G
radedAlgebra ℬ] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-linear homomorphism of graded algebras, denoted `𝒜 →ₐᵍ[R] ℬ`.
-/
structure GradedAlgHom (R : Type*) {A B ι : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A →ₐ[R] B, 𝒜 →+*ᵍ ℬ

/-- Reinterpret a graded algebra homomorphism as a graded ring homomorphism. -/
add_decl_doc GradedAlgHom.toGradedRingHom

@[inherit_doc]
notation:25 𝒜 " →ₐᵍ[" R "] " ℬ => GradedAlgHom R 𝒜 ℬ

namespace GradedAlgHom

variable {R S T U V A B C D ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} {𝒞 : ι → Submodule R C} {𝒟 : ι → Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

section ofClass
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]` into an actual `GradedAlgHom`.

In future mathlib this will be deprioritised in favour of using structural projections. -/
/-
**GradedAlgHom.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：ofClass (f : F) : 𝒜 ->ₐᵍ[R] ℬ
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …

--- 原说明 ---
Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]` into an actual `Gr
adedAlgHom`.

In future mathlib this will be deprioritised in favour of using structural proje
ctions.
-/
def ofClass (f : F) : 𝒜 →ₐᵍ[R] ℬ :=
  { (AlgHomClass.toAlgHom f : A →ₐ[R] B), (.ofClass f : 𝒜 →+*ᵍ ℬ) with }

end ofClass

/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (𝒜 →ₐᵍ[R] ℬ) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr
/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GradedFunLike (𝒜 →ₐᵍ[R] ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem
/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlgHomClass (𝒜 →ₐᵍ[R] ℬ) R A B where
  map_add f := f.map_add
  map_zero f := f.map_zero
  map_mul f := f.map_mul
  map_one f := f.map_one
  commutes f := f.commutes

attribute [coe] GradedAlgHom.toAlgHom
/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (𝒜 →ₐᵍ[R] ℬ) (A →ₐ[R] B) := ⟨toAlgHom⟩
/-
**GradedAlgHom.toAlgHom_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] {F : Type u_11}   [inst_9 : FunLike F A B] [inst_10 : GradedFun
Like F 𝒜 ℬ] [inst_11 : AlgHomClass F R A B] (f : F),   ↑(GradedAlgHom.ofClass f)
 = ↑f
参数：f : F；GradedAlgHom.ofClass f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAlgHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : (ofClass f : A →ₐ[R] B) = AlgHomClass.toAlgHom f := rfl
/-
**GradedAlgHom.toGradedRingHom_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] {F : Type u_11}   [inst_9 : FunLike F A B] [inst_10 : GradedFun
Like F 𝒜 ℬ] [inst_11 : AlgHomClass F R A B] (f : F),   (GradedAlgHom.ofClass f).
toGradedRingHom = ↑f
参数：f : F；GradedAlgHom.ofClass f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toGradedRingHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) :
    ((ofClass f).toGradedRingHom : 𝒜 →+*ᵍ ℬ) = GradedRingHom.ofClass f := rfl

initialize_simps_projections GradedAlgHom (toFun → apply)
/-
**GradedAlgHom.coe_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] {F : Type u_11}   [inst_9 : FunLike F A B] [inst_10 : GradedFun
Like F 𝒜 ℬ] [inst_11 : AlgHomClass F R A B] (f : F),   ⇑(GradedAlgHom.ofClass f)
 = ⇑f
参数：f : F；GradedAlgHom.ofClass f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : ⇑(.ofClass f : 𝒜 →ₐᵍ[R] ℬ) = f := rfl
/-
**GradedAlgHom.coe_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ]   (f : 𝒜 →ₐᵍ[R] ℬ), ⇑↑f = ⇑f
参数：f : 𝒜 →ₐᵍ[R] ℬ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toAlgHom (f : 𝒜 →ₐᵍ[R] ℬ) : ⇑f.toAlgHom = f := rfl
/-
**GradedAlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] {f : A →ₐ[R] B}   (h : ∀ {i : ι} {x : A}, x ∈ 𝒜 i → f.toRingHom
 x ∈ ℬ i), ⇑{ toAlgHom := f, map_mem := h } = ⇑f
参数：h : ∀ {i : ι} {x : A}, x ∈ 𝒜 i → f.toRingHom x ∈ ℬ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A → B) = f := rfl

@[norm_cast]
/-
**GradedAlgHom.coe_mks** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_mks {f : A -> B} (h₁ h₂ h₃ h₄ h₅ h₆) : ⇑(⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅
⟩, h₆⟩ : 𝒜 ->ₐᵍ[R] ℬ) = f
参数：h₁ h₂ h₃ h₄ h₅ h₆。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅ h₆) :
    ⇑(⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 →ₐᵍ[R] ℬ) = f := rfl
/-
**GradedAlgHom.coe_toAlgHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_toAlgHom_mk {f : A ->ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A ->ₐ[R] 
B) = f
参数：h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgHom_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A →ₐ[R] B) = f := by
  dsimp only

@[deprecated (since := "2026-05-05")] alias coe_algHom_mk := coe_toAlgHom_mk

variable (f : 𝒜 →ₐᵍ[R] ℬ)
/-
**GradedAlgHom.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_fn_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_fn_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → (A → B)) :=
  DFunLike.coe_injective
/-
**GradedAlgHom.coe_fn_inj** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_fn_inj {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} : (f₁ : A -> B) = f₂ ↔ f₁ = f₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_fn_inj {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} : (f₁ : A → B) = f₂ ↔ f₁ = f₂ :=
  DFunLike.coe_fn_eq
/-
**GradedAlgHom.coe_toAlgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_toAlgHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[
R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.coe_fn_injective`：coe_fn_injective : Function.Injective ((↑
) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₐ[R] B) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective
/-
**GradedAlgHom.toGradedRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom
`。
形式化陈述：toGradedRingHom_injective : Function.Injective (toGradedRingHom (𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.coe_fn_injective`：coe_fn_injective : Function.Injective ((↑
) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toGradedRingHom_injective : Function.Injective (toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ)) :=
  fun _ _ h ↦ coe_fn_injective congr($h)
/-
**GradedAlgHom.coe_linearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_linearMap_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₗ
[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₗ[R] B) :=
  AlgHom.toLinearMap_injective.comp coe_toAlgHom_injective
/-
**GradedAlgHom.coe_ringHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_ringHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+* 
B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
-/
theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+* B) :=
  AlgHom.coe_ringHom_injective.comp coe_toAlgHom_injective
/-
**GradedAlgHom.coe_monoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->*
 B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_monoidHom_injective`：coe_monoidHom_injective : Function.Injec
tive ((↑) : (A ->ₐ[R] B) -> A ->* B)
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
-/
theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →* B) :=
  AlgHom.coe_monoidHom_injective.comp coe_toAlgHom_injective
/-
**GradedAlgHom.coe_addMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHo
m`。
形式化陈述：coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A 
->+ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `AlgHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Function
.Injective ((↑) : (A ->ₐ[R] B) -> A ->+ B)
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+ B) :=
  AlgHom.coe_addMonoidHom_injective.comp coe_toAlgHom_injective

/-- Consider using `congr($H x)` instead. -/
/-
**GradedAlgHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ]   {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ}, f₁ = f₂ → ∀ (x : A), f₁ x = f₂ x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Consider using `congr($H x)` instead.
-/
protected theorem congr_fun {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} (H : f₁ = f₂) (x : A) : f₁ x = f₂ x :=
  DFunLike.congr_fun H x

/-- Consider using `congr(f $h)` instead. -/
/-
**GradedAlgHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] (f : 𝒜 →ₐᵍ[R] ℬ)   {x y : A}, x = y → f x = f y
参数：f : 𝒜 →ₐᵍ[R] ℬ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y

--- 原说明 ---
Consider using `congr(f $h)` instead.
-/
protected theorem congr_arg (f : 𝒜 →ₐᵍ[R] ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
/-
**GradedAlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：ext {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : forall x, f₁ x = f₂ x) : f₁ = f₂
参数：H : forall x, f₁ x = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} (H : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ H

@[simp]
/-
**GradedAlgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：mk_coe {f : 𝒜 ->ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆) : (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩,
 h₅⟩, h₆⟩ : 𝒜 ->ₐᵍ[R] ℬ) = f
参数：h₁ h₂ h₃ h₄ h₅ h₆。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe {f : 𝒜 →ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 →ₐᵍ[R] ℬ) = f :=
  rfl

@[simp]
/-
**GradedAlgHom.commutes** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：commutes (r : R) : f (algebraMap R A r) = algebraMap R B r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem commutes (r : R) : f (algebraMap R A r) = algebraMap R B r :=
  f.commutes' r
/-
**GradedAlgHom.comp_ofId** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：comp_ofId : (f : A ->ₐ[R] B).comp (Algebra.ofId R A) = Algebra.ofId R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `GradedAlgHom.commutes`：commutes (r : R) : f (algebraMap R A r) = algebra
Map R B r
-/
theorem comp_ofId : (f : A →ₐ[R] B).comp (Algebra.ofId R A) = Algebra.ofId R B :=
  AlgHom.ext f.commutes

/-- If a `GradedRingHom` is `R`-linear, then it is a `GradedAlgHom`. -/
/-
**GradedAlgHom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：mk' (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x) : 𝒜 ->ₐᵍ
[R] ℬ
参数：f : 𝒜 ->+*ᵍ ℬ；h : forall (c : R) (x), f (c • x) = c • f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `GradedRingHom` is `R`-linear, then it is a `GradedAlgHom`.
-/
def mk' (f : 𝒜 →+*ᵍ ℬ) (h : ∀ (c : R) (x), f (c • x) = c • f x) : 𝒜 →ₐᵍ[R] ℬ :=
  { AlgHom.mk' _ h, f with }

@[simp]
/-
**GradedAlgHom.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_mk' (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x) : ⇑(
mk' f h) = f
参数：f : 𝒜 ->+*ᵍ ℬ；h : forall (c : R) (x), f (c • x) = c • f x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : 𝒜 →+*ᵍ ℬ) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section id
variable (R 𝒜)

/-- Identity map as a `GradedAlgHom`. -/
/-
**GradedAlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：(R : Type u_1) →   {A : Type u_6} →     {ι : Type u_10} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A]
 →             [inst_3 : DecidableEq ι] →               [inst_4 : AddMonoid ι] →
 (𝒜 : ι → Submodule R A) → [inst_5 : GradedAlgebra 𝒜] → 𝒜 →ₐᵍ[R] 𝒜
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as a `GradedAlgHom`.
-/
@[simps!] protected def id : 𝒜 →ₐᵍ[R] 𝒜 :=
  { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]
/-
**GradedAlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_id : ⇑(GradedAlgHom.id R 𝒜) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(GradedAlgHom.id R 𝒜) = id := rfl

@[simp]
/-
**GradedAlgHom.id_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：id_toAlgHom : (GradedAlgHom.id R 𝒜 : A ->ₐ[R] A) = AlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toAlgHom : (GradedAlgHom.id R 𝒜 : A →ₐ[R] A) = AlgHom.id R A := rfl

end id

/-- If `g` and `f` are `R`-linear graded algebra homomorphisms with the domain of `g` equal to
the codomain of `f`, then `g.comp f` is the graded algebra homomorphism `x ↦ g (f x)`.
-/
/-
**GradedAlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_6} →     {B : Type u_7} →       {C : Type u
_8} →         {ι : Type u_10} →           [inst : CommSemiring R] →             
[inst_1 : Semiring A] →               [inst_2 : Semiring B] →                 [i
nst_3 : Semiring C] →                   [inst_4 : Algebra R A] →                
     [inst_5 : Algebra R B] →                       [inst_6 : Algebra R C] →    
                     [inst_7 : DecidableEq ι] →                           [inst_
8 : AddMonoid ι] →                             {𝒜 : ι → Submodule R A} →        
                       {ℬ : ι → Submodule R B} →                                
 {𝒞 : ι → Submodule R C} →                                   [inst_9 : GradedAlg
ebra 𝒜] →                                     [inst_10 : GradedAlgebra ℬ] →     
                                  [inst_11 : GradedAlgebra 𝒞] → (ℬ →ₐᵍ[R] 𝒞) → (
𝒜 →ₐᵍ[R] ℬ) → 𝒜 →ₐᵍ[R] 𝒞
参数：ℬ →ₐᵍ[R] 𝒞；𝒜 →ₐᵍ[R] ℬ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` and `f` are `R`-linear graded algebra homomorphisms with the domain of `g
` equal to
the codomain of `f`, then `g.comp f` is the graded algebra homomorphism `x ↦ g (
f x)`.
-/
@[simps!] def comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R] 𝒞 :=
  { (g : B →ₐ[R] C).comp (f : A →ₐ[R] B),
    (g.toGradedRingHom : ℬ →+*ᵍ 𝒞).comp (f.toGradedRingHom : 𝒜 →+*ᵍ ℬ) with }

@[simp]
/-
**GradedAlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：coe_comp (g : B ->ₐ[R] C) (f : 𝒜 ->ₐᵍ[R] ℬ) : ⇑(g.comp f) = g ∘ f
参数：g : B ->ₐ[R] C；f : 𝒜 ->ₐᵍ[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : B →ₐ[R] C) (f : 𝒜 →ₐᵍ[R] ℬ) : ⇑(g.comp f) = g ∘ f := rfl
/-
**GradedAlgHom.comp_toGradedRingHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：comp_toGradedRingHom (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ) : (g.comp f).toGr
adedRingHom = g.toGradedRingHom.comp f.toGradedRingHom
参数：g : ℬ ->ₐᵍ[R] 𝒞；f : 𝒜 ->ₐᵍ[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toGradedRingHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f).toGradedRingHom = g.toGradedRingHom.comp f.toGradedRingHom := rfl
/-
**GradedAlgHom.comp_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：comp_toAlgHom (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ) : (g.comp f : A ->ₐ[R] C
) = (g : B ->ₐ[R] C).comp f
参数：g : ℬ ->ₐᵍ[R] 𝒞；f : 𝒜 ->ₐᵍ[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toAlgHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f : A →ₐ[R] C) = (g : B →ₐ[R] C).comp f := rfl

@[simp]
/-
**GradedAlgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：comp_id : f.comp (.id R 𝒜) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id : f.comp (.id R 𝒜) = f := rfl

@[simp]
/-
**GradedAlgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：id_comp : (GradedAlgHom.id R ℬ).comp f = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp : (GradedAlgHom.id R ℬ).comp f = f := rfl
/-
**GradedAlgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：comp_assoc (fCD : 𝒞 ->ₐᵍ[R] 𝒟) (fBC : ℬ ->ₐᵍ[R] 𝒞) (fAB : 𝒜 ->ₐᵍ[R] ℬ) : (
fCD.comp fBC).comp fAB = fCD.comp (fBC.comp fAB)
参数：fCD : 𝒞 ->ₐᵍ[R] 𝒟；fBC : ℬ ->ₐᵍ[R] 𝒞；fAB : 𝒜 ->ₐᵍ[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (fCD : 𝒞 →ₐᵍ[R] 𝒟) (fBC : ℬ →ₐᵍ[R] 𝒞) (fAB : 𝒜 →ₐᵍ[R] ℬ) :
    (fCD.comp fBC).comp fAB = fCD.comp (fBC.comp fAB) := rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (𝒜 →ₐᵍ[R] 𝒜) where
  mul := comp
  one := .id R 𝒜
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
/-
**GradedAlgHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {ι : Type u_10} [inst : CommSemiring R] [i
nst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : DecidableEq ι] [inst_4 : 
AddMonoid ι] {𝒜 : ι → Submodule R A} [inst_5 : GradedAlgebra 𝒜], ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_one : ⇑(1 : 𝒜 →ₐᵍ[R] 𝒜) = id := rfl
/-
**GradedAlgHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {ι : Type u_10} [inst : CommSemiring R] [i
nst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : DecidableEq ι] [inst_4 : 
AddMonoid ι] {𝒜 : ι → Submodule R A} [inst_5 : GradedAlgebra 𝒜] (f g : 𝒜 →ₐᵍ[R] 
𝒜),   ⇑(f * g) = ⇑f ∘ ⇑g
参数：f g : 𝒜 →ₐᵍ[R] 𝒜；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mul (f g : 𝒜 →ₐᵍ[R] 𝒜) : ⇑(f * g) = f ∘ g := rfl
/-
**GradedAlgHom.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {ι : Type u_10} [inst : CommSemiring R] [i
nst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : DecidableEq ι] [inst_4 : 
AddMonoid ι] {𝒜 : ι → Submodule R A} [inst_5 : GradedAlgebra 𝒜] (f : 𝒜 →ₐᵍ[R] 𝒜)
   (n : ℕ), ⇑(f ^ n) = (⇑f)^[n]
参数：f : 𝒜 →ₐᵍ[R] 𝒜；n : ℕ；f ^ n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
@[simp] theorem coe_pow (f : 𝒜 →ₐᵍ[R] 𝒜) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]
/-
**GradedAlgHom.cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `GradedAlgHom`。
形式化陈述：cancel_right {g₁ g₂ : ℬ ->ₐᵍ[R] 𝒞} {f : 𝒜 ->ₐᵍ[R] ℬ} (hf : Function.Surjec
tive f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgHom.cancel_right`：cancel_right {g₁ g₂ : B ->ₐ[R] C} {f : A ->ₐ[R] B} 
(hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma cancel_right {g₁ g₂ : ℬ →ₐᵍ[R] 𝒞} {f : 𝒜 →ₐᵍ[R] ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ coe_toAlgHom_injective <| (AlgHom.cancel_right hf).1 congr($h), fun h ↦ h ▸ rfl⟩
/-
**GradedAlgHom.cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `GradedAlgHom`。
形式化陈述：cancel_left {g₁ g₂ : 𝒜 ->ₐᵍ[R] ℬ} {f : ℬ ->ₐᵍ[R] 𝒞} (hf : Function.Injecti
ve f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.I
njective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgHom.cancel_left`：cancel_left {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (h
f : Function.Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma cancel_left {g₁ g₂ : 𝒜 →ₐᵍ[R] ℬ} {f : ℬ →ₐᵍ[R] 𝒞} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h ↦ coe_toAlgHom_injective <| (AlgHom.cancel_left hf).1 congr($h), fun h ↦ h ▸ rfl⟩

/-- We enrich the existing function `toAlgHom` with the structure of a `MonoidHom`, to produce a
bundled function that we now call `toEnd`. -/
/-
**GradedAlgHom.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_6} →     {ι : Type u_10} →       [inst : Co
mmSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A]
 →             [inst_3 : DecidableEq ι] →               [inst_4 : AddMonoid ι] →
 {𝒜 : ι → Submodule R A} → [inst_5 : GradedAlgebra 𝒜] → (𝒜 →ₐᵍ[R] 𝒜) →* A →ₐ[R] 
A
参数：𝒜 →ₐᵍ[R] 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We enrich the existing function `toAlgHom` with the structure of a `MonoidHom`, 
to produce a
bundled function that we now call `toEnd`.
-/
@[simps] def toEnd : (𝒜 →ₐᵍ[R] 𝒜) →* (A →ₐ[R] A) where
  toFun := toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Subsingleton B]

/-
**GradedAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (𝒜 →ₐᵍ[R] ℬ) where
  default := { (default : A →ₐ[R] B) with map_mem hx := by aesop }
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

@[simp]
/-
**GradedAlgHom.default_apply** 是 Mathlib 中的一个引理，位于命名空间 `GradedAlgHom`。
形式化陈述：default_apply (x : A) : (default : 𝒜 ->ₐᵍ[R] ℬ) x = 0
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma default_apply (x : A) : (default : 𝒜 →ₐᵍ[R] ℬ) x = 0 :=
  rfl

end

section restrictScalars

/-- Restrict the base ring to a "smaller" ring. -/
/-
**GradedAlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `GradedAlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_6} →     {B : Type u_7} →       {ι : Type u
_10} →         [inst : CommSemiring R] →           [inst_1 : Semiring A] →      
       [inst_2 : Semiring B] →               [inst_3 : Algebra R A] →           
      [inst_4 : Algebra R B] →                   [inst_5 : DecidableEq ι] →     
                [inst_6 : AddMonoid ι] →                       {𝒜 : ι → Submodul
e R A} →                         {ℬ : ι → Submodule R B} →                      
     [inst_7 : GradedAlgebra 𝒜] →                             [inst_8 : GradedAl
gebra ℬ] →                               (R₀ : Type u_11) →                     
            [inst_9 : CommSemiring R₀] →                                   [inst
_10 : Algebra R₀ R] →                                     [inst_11 : Algebra R₀ 
A] →                                       [inst_12 : Algebra R₀ B] →           
                              [inst_13 : IsScalarTower R₀ R A] →                
                           [inst_14 : IsScalarTower R₀ R B] →                   
                          (𝒜 →ₐᵍ[R] ℬ) →                                        
       (fun x => Submodule.restrictScalars R₀ (𝒜 x)) →ₐᵍ[R₀] fun x =>           
                                      Submodule.restrictScalars R₀ (ℬ x)
参数：R₀ : Type u_11；𝒜 →ₐᵍ[R] ℬ；fun x => Submodule.restrictScalars R₀ (𝒜 x)；ℬ x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.map_mem`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} {ι 
: Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B
] [inst_3 …

--- 原说明 ---
Restrict the base ring to a "smaller" ring.
-/
@[coe, simps!] def restrictScalars (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 →ₐᵍ[R] ℬ) : (𝒜 · |>.restrictScalars R₀) →ₐᵍ[R₀] (ℬ · |>.restrictScalars R₀) :=
  { f.toAlgHom.restrictScalars R₀, f with }

variable (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 →ₐᵍ[R] ℬ)
/-
**GradedAlgHom.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] (R₀ : Type u_11)   [inst_9 : CommSemiring R₀] [inst_10 : Algebr
a R₀ R] [inst_11 : Algebra R₀ A] [inst_12 : Algebra R₀ B]   [inst_13 : IsScalarT
ower R₀ R A] [inst_14 : IsScalarTower R₀ R B] (f : 𝒜 →ₐᵍ[R] ℬ), ⇑(↑R₀ f) = ⇑f
参数：R₀ : Type u_11；f : 𝒜 →ₐᵍ[R] ℬ；↑R₀ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_restrictScalars : ⇑(f.restrictScalars R₀) = f := rfl
/-
**GradedAlgHom.restrictScalars_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedAlgHom`
。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] (R₀ : Type u_11)   [inst_9 : CommSemiring R₀] [inst_10 : Algebr
a R₀ R] [inst_11 : Algebra R₀ A] [inst_12 : Algebra R₀ B]   [inst_13 : IsScalarT
ower R₀ R A] [inst_14 : IsScalarTower R₀ R B] (f : 𝒜 →ₐᵍ[R] ℬ),   AlgHom.restric
tScalars R₀ ↑f = ↑(↑R₀ f)
参数：R₀ : Type u_11；f : 𝒜 →ₐᵍ[R] ℬ；↑R₀ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalars_toAlgHom :
    (f : A →ₐ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

@[deprecated (since := "2026-05-05")]
alias restrictScalars_coe_algHom := restrictScalars_toAlgHom
/-
**GradedAlgHom.restrictScalars_coe_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `GradedAl
gHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_6} {B : Type u_7} {ι : Type u_10} [inst : Com
mSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A
] [inst_4 : Algebra R B] [inst_5 : DecidableEq ι] [inst_6 : AddMonoid ι]   {𝒜 : 
ι → Submodule R A} {ℬ : ι → Submodule R B} [inst_7 : GradedAlgebra 𝒜] [inst_8 : 
GradedAlgebra ℬ] (R₀ : Type u_11)   [inst_9 : CommSemiring R₀] [inst_10 : Algebr
a R₀ R] [inst_11 : Algebra R₀ A] [inst_12 : Algebra R₀ B]   [inst_13 : IsScalarT
ower R₀ R A] [inst_14 : IsScalarTower R₀ R B] (f : 𝒜 →ₐᵍ[R] ℬ), ↑R₀ ↑f = ↑(↑R₀ f
)
参数：R₀ : Type u_11；f : 𝒜 →ₐᵍ[R] ℬ；↑R₀ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `GradedAlgHom.instAlgHomClass`：∀ {R : Type u_1} {A : Type u_6} {B : Type 
u_7} {ι : Type u_10} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : S
emiring B] [inst_3…
-/
@[simp] lemma restrictScalars_coe_linearMap :
    (f : A →ₗ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl
/-
**GradedAlgHom.restrictScalars_injective** 是 Mathlib 中的一个引理，位于命名空间 `GradedAlgHom
`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R₀ : (𝒜 ->
ₐᵍ[R] ℬ) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedAlgHom.coe_fn_injective`：coe_fn_injective : Function.Injective ((↑
) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma restrictScalars_injective :
    Function.Injective (restrictScalars R₀ : (𝒜 →ₐᵍ[R] ℬ) → _) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

end restrictScalars

end GradedAlgHom

