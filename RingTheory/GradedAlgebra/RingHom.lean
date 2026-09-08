/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.FunLike.Graded
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homomorphisms of graded (semi)rings

This file defines bundled homomorphisms of graded (semi)rings. We use the same structure
`GradedRingHom 𝒜 ℬ`, a.k.a. `𝒜 →+*ᵍ ℬ`, for both types of homomorphisms.

We do **not** define a separate class of graded ring homomorphisms; instead, we use
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.

## Main definitions

* `GradedRingHom`: Graded (semi)ring homomorphisms. Ring homomorphism which preserves the grading.

## Notation

* `→+*ᵍ`: Graded (semi)ring hom.

## Implementation notes

* We don't really need the fact that they are graded rings until the theorem
  `DirectSum.decompose_map` which describes how the decomposition interacts with the map.
-/

@[expose] public section

variable {ι A B C D σ τ ψ ω : Type*}
  [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [SetLike σ A] [SetLike τ B] [SetLike ψ C] [SetLike ω D]

open Graded

section SetLike

/-- Bundled graded (semi)ring homomorphisms. Use `GradedRingHom` for the namespace and other
identifiers, and `𝒜 →+*ᵍ ℬ` for the notation. -/
/-
**GradedRingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {σ : Type u
_6} →         {τ : Type u_7} →           [Semiring A] → [Semiring B] → [SetLike 
σ A] → [SetLike τ B] → (ι → σ) → (ι → τ) → Type (max u_2 u_3)
参数：ι → σ；ι → τ；max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled graded (semi)ring homomorphisms. Use `GradedRingHom` for the namespace a
nd other
identifiers, and `𝒜 →+*ᵍ ℬ` for the notation.
-/
structure GradedRingHom (𝒜 : ι → σ) (ℬ : ι → τ) extends A →+* B where
  protected map_mem {i : ι} {x : A} : x ∈ 𝒜 i → toRingHom x ∈ ℬ i

variable {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ψ} {𝒟 : ι → ω}

@[inherit_doc]
notation:25 𝒜 " →+*ᵍ " ℬ => GradedRingHom 𝒜 ℬ

namespace GradedRingHom

section ofClass
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]` into an actual `GradedRingHom`.

This should not be used directly. In the future, Mathlib will prefer structural projections over
these general constructions from hom classes. -/
@[coe]
/-
**GradedRingHom.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：ofClass (f : F) : 𝒜 ->+*ᵍ ℬ where __
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i

--- 原说明 ---
Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]` into an actual `Gra
dedRingHom`.

This should not be used directly. In the future, Mathlib will prefer structural 
projections over
these general constructions from hom classes.
-/
def ofClass (f : F) : 𝒜 →+*ᵍ ℬ where
  __ := (f : A →+* B)
  map_mem := map_mem f

end ofClass

section coe

/-
**GradedRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (𝒜 →+*ᵍ ℬ) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h
/-
**GradedRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GradedFunLike (𝒜 →+*ᵍ ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem
/-
**GradedRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingHomClass (𝒜 →+*ᵍ ℬ) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections GradedRingHom (toFun → apply)

attribute [coe] GradedRingHom.toRingHom

@[simp]
/-
**GradedRingHom.toRingHom_eq_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`
。
形式化陈述：toRingHom_eq_toRingHom (f : 𝒜 ->+*ᵍ ℬ) : RingHomClass.toRingHom f = f.toRi
ngHom
参数：f : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
-/
theorem toRingHom_eq_toRingHom (f : 𝒜 →+*ᵍ ℬ) : RingHomClass.toRingHom f = f.toRingHom := rfl

@[simp]
/-
**GradedRingHom.coe_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_toRingHom (f : 𝒜 ->+*ᵍ ℬ) : ⇑f.toRingHom = f
参数：f : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRingHom (f : 𝒜 →+*ᵍ ℬ) : ⇑f.toRingHom = f := rfl

@[simp]
/-
**GradedRingHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_mk (f : A ->+* B) (h) : ((⟨f, h⟩ : 𝒜 ->+*ᵍ ℬ) : A -> B) = f
参数：f : A ->+* B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A →+* B) (h) : ((⟨f, h⟩ : 𝒜 →+*ᵍ ℬ) : A → B) = f := rfl

@[simp]
/-
**GradedRingHom.coe_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClas
s F A B] (f : F) : ((.ofClass f : 𝒜 ->+*ᵍ ℬ) : A -> B) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]
    (f : F) : ((.ofClass f : 𝒜 →+*ᵍ ℬ) : A → B) = f := rfl
/-
**GradedRingHom.coeToRingHom** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
形式化陈述：coeToRingHom : CoeOut (𝒜 ->+*ᵍ ℬ) (A ->+* B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeToRingHom : CoeOut (𝒜 →+*ᵍ ℬ) (A →+* B) :=
  ⟨GradedRingHom.toRingHom⟩

/-- Copy of a `GradedRingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**GradedRingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：copy (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : 𝒜 ->+*ᵍ ℬ where __
参数：f : 𝒜 ->+*ᵍ ℬ；f' : A -> B；h : f' = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `GradedRingHom` with a new `toFun` equal to the old one. Useful to fix
 definitional
equalities.
-/
def copy (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : 𝒜 →+*ᵍ ℬ where
  __ := f.toRingHom.copy f' h
  map_mem hx := congr($h _ ∈ ℬ _).to_iff.mpr <| map_mem f hx

@[simp]
/-
**GradedRingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_copy (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : 𝒜 ->+*ᵍ ℬ；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**GradedRingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：copy_eq (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : f.copy f' h = f
参数：f : 𝒜 ->+*ᵍ ℬ；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable (f : 𝒜 →+*ᵍ ℬ)

/-
**GradedRingHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} {f g : 𝒜 →+*ᵍ ℬ}, f = g → ∀ (x : A), f x = 
g x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : 𝒜 →+*ᵍ ℬ} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x
/-
**GradedRingHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} (f : 𝒜 →+*ᵍ ℬ) {x y : A}, x = y → f x = f y
参数：f : 𝒜 →+*ᵍ ℬ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (f : 𝒜 →+*ᵍ ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
/-
**GradedRingHom.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_inj ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ (h : (f : A -> B) = g) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_inj ⦃f g : 𝒜 →+*ᵍ ℬ⦄ (h : (f : A → B) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
/-
**GradedRingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : 𝒜 →+*ᵍ ℬ⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
/-
**GradedRingHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：mk_coe (f : 𝒜 ->+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅) : .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ =
 f
参数：f : 𝒜 ->+*ᵍ ℬ；h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
-/
theorem mk_coe (f : 𝒜 →+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅) : .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ = f :=
  ext fun _ => rfl
/-
**GradedRingHom.coe_ringHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_ringHom_injective : (fun f : 𝒜 ->+*ᵍ ℬ => (f : A ->+* B)).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem coe_ringHom_injective : (fun f : 𝒜 →+*ᵍ ℬ => (f : A →+* B)).Injective := fun _ _ h =>
  ext <| DFunLike.congr_fun (F := A →+* B) h

/-- Graded ring homomorphisms map zero to zero. -/
/-
**GradedRingHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} (f : 𝒜 →+*ᵍ ℬ), f 0 = 0
参数：f : 𝒜 →+*ᵍ ℬ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms map zero to zero.
-/
protected theorem map_zero (f : 𝒜 →+*ᵍ ℬ) : f 0 = 0 :=
  map_zero f

/-- Graded ring homomorphisms map one to one. -/
/-
**GradedRingHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} (f : 𝒜 →+*ᵍ ℬ), f 1 = 1
参数：f : 𝒜 →+*ᵍ ℬ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms map one to one.
-/
protected theorem map_one (f : 𝒜 →+*ᵍ ℬ) : f 1 = 1 :=
  map_one f

/-- Graded ring homomorphisms preserve addition. -/
/-
**GradedRingHom.map_add** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} (f : 𝒜 →+*ᵍ ℬ) (a b : A), f (a + b) = f a +
 f b
参数：f : 𝒜 →+*ᵍ ℬ；a b : A；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms preserve addition.
-/
protected theorem map_add (f : 𝒜 →+*ᵍ ℬ) (a b : A) : f (a + b) = f a + f b :=
  map_add ..

/-- Graded ring homomorphisms preserve multiplication. -/
/-
**GradedRingHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} (f : 𝒜 →+*ᵍ ℬ) (a b : A), f (a * b) = f a *
 f b
参数：f : 𝒜 →+*ᵍ ℬ；a b : A；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms preserve multiplication.
-/
protected theorem map_mul (f : 𝒜 →+*ᵍ ℬ) (a b : A) : f (a * b) = f a * f b :=
  map_mul ..

end

section Ring
variable {A B σ τ : Type*}
variable [Ring A] [Ring B] [SetLike σ A] [SetLike τ B]
variable (𝒜 : ι → σ) (ℬ : ι → τ)

/-- Graded ring homomorphisms preserve additive inverse. -/
/-
**GradedRingHom.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_10} {B : Type u_11} {σ : Type u_12} {τ : Type
 u_13} [inst : Ring A] [inst_1 : Ring B]   [inst_2 : SetLike σ A] [inst_3 : SetL
ike τ B] (𝒜 : ι → σ) (ℬ : ι → τ) (f : 𝒜 →+*ᵍ ℬ) (x : A), f (-x) = -f x
参数：𝒜 : ι → σ；ℬ : ι → τ；f : 𝒜 →+*ᵍ ℬ；x : A；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms preserve additive inverse.
-/
protected theorem map_neg (f : 𝒜 →+*ᵍ ℬ) (x : A) : f (-x) = -f x :=
  map_neg f x

/-- Graded ring homomorphisms preserve subtraction. -/
/-
**GradedRingHom.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_10} {B : Type u_11} {σ : Type u_12} {τ : Type
 u_13} [inst : Ring A] [inst_1 : Ring B]   [inst_2 : SetLike σ A] [inst_3 : SetL
ike τ B] (𝒜 : ι → σ) (ℬ : ι → τ) (f : 𝒜 →+*ᵍ ℬ) (x y : A), f (x - y) = f x - f y
参数：𝒜 : ι → σ；ℬ : ι → τ；f : 𝒜 →+*ᵍ ℬ；x y : A；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Graded ring homomorphisms preserve subtraction.
-/
protected theorem map_sub (f : 𝒜 →+*ᵍ ℬ) (x y : A) :
    f (x - y) = f x - f y :=
  map_sub f x y

end Ring

variable (𝒜) in
/-- The identity graded ring homomorphism from a graded ring to itself. -/
/-
**GradedRingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：id : 𝒜 ->+*ᵍ 𝒜 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity graded ring homomorphism from a graded ring to itself.
-/
def id : 𝒜 →+*ᵍ 𝒜 where
  __ := RingHom.id _
  map_mem h := h

@[simp, norm_cast]
/-
**GradedRingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_id : ⇑(GradedRingHom.id 𝒜) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(GradedRingHom.id 𝒜) = _root_.id := rfl

@[simp]
/-
**GradedRingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：id_apply (x : A) : GradedRingHom.id 𝒜 x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : A) : GradedRingHom.id 𝒜 x = x :=
  rfl

@[simp]
/-
**GradedRingHom.toRingHom_id** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：toRingHom_id : (id 𝒜).toRingHom = RingHom.id A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_id : (id 𝒜).toRingHom = RingHom.id A :=
  rfl

/-- Composition of graded ring homomorphisms is a graded ring homomorphism. -/
/-
**GradedRingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：comp (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ) : 𝒜 ->+*ᵍ 𝒞 where __
参数：g : ℬ ->+*ᵍ 𝒞；f : 𝒜 ->+*ᵍ ℬ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Composition of graded ring homomorphisms is a graded ring homomorphism.
-/
def comp (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) : 𝒜 →+*ᵍ 𝒞 where
  __ := g.toRingHom.comp f
  map_mem := g.map_mem ∘ f.map_mem

/-- Composition of graded ring homomorphisms is associative. -/
/-
**GradedRingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：comp_assoc (h : 𝒞 ->+*ᵍ 𝒟) (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ) : (h.comp g).co
mp f = h.comp (g.comp f)
参数：h : 𝒞 ->+*ᵍ 𝒟；g : ℬ ->+*ᵍ 𝒞；f : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of graded ring homomorphisms is associative.
-/
theorem comp_assoc (h : 𝒞 →+*ᵍ 𝒟) (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**GradedRingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：coe_comp (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) : (hnp.comp hmn : A -> C) = h
np ∘ hmn
参数：hnp : ℬ ->+*ᵍ 𝒞；hmn : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (hnp : ℬ →+*ᵍ 𝒞) (hmn : 𝒜 →+*ᵍ ℬ) : (hnp.comp hmn : A → C) = hnp ∘ hmn :=
  rfl
/-
**GradedRingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：comp_apply (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) (x : A) : (hnp.comp hmn : A
 -> C) x = hnp (hmn x)
参数：hnp : ℬ ->+*ᵍ 𝒞；hmn : 𝒜 ->+*ᵍ ℬ；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (hnp : ℬ →+*ᵍ 𝒞) (hmn : 𝒜 →+*ᵍ ℬ) (x : A) :
    (hnp.comp hmn : A → C) x = hnp (hmn x) :=
  rfl

@[simp]
/-
**GradedRingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：comp_id (f : 𝒜 ->+*ᵍ ℬ) : f.comp (id 𝒜) = f
参数：f : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
-/
theorem comp_id (f : 𝒜 →+*ᵍ ℬ) : f.comp (id 𝒜) = f :=
  ext fun _ => rfl

@[simp]
/-
**GradedRingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：id_comp (f : 𝒜 ->+*ᵍ ℬ) : (id ℬ).comp f = f
参数：f : 𝒜 ->+*ᵍ ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
-/
theorem id_comp (f : 𝒜 →+*ᵍ ℬ) : (id ℬ).comp f = f :=
  ext fun _ => rfl
/-
**GradedRingHom.instOne** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
形式化陈述：instOne : One (𝒜 ->+*ᵍ 𝒜) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (𝒜 →+*ᵍ 𝒜) where one := id _
/-
**GradedRingHom.instMul** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
形式化陈述：instMul : Mul (𝒜 ->+*ᵍ 𝒜) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (𝒜 →+*ᵍ 𝒜) where mul := comp
/-
**GradedRingHom.one_def** 是 Mathlib 中的一个引理，位于命名空间 `GradedRingHom`。
形式化陈述：one_def : (1 : 𝒜 ->+*ᵍ 𝒜) = id 𝒜
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : 𝒜 →+*ᵍ 𝒜) = id 𝒜 := rfl
/-
**GradedRingHom.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `GradedRingHom`。
形式化陈述：mul_def (f g : 𝒜 ->+*ᵍ 𝒜) : f * g = f.comp g
参数：f g : 𝒜 ->+*ᵍ 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : 𝒜 →+*ᵍ 𝒜) : f * g = f.comp g := rfl
/-
**GradedRingHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_6} [inst : Semiring A] [inst_1
 : SetLike σ A] {𝒜 : ι → σ}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : 𝒜 →+*ᵍ 𝒜) = _root_.id := rfl
/-
**GradedRingHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_6} [inst : Semiring A] [inst_1
 : SetLike σ A] {𝒜 : ι → σ} (f g : 𝒜 →+*ᵍ 𝒜),   ⇑(f * g) = ⇑f ∘ ⇑g
参数：f g : 𝒜 →+*ᵍ 𝒜；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (f g : 𝒜 →+*ᵍ 𝒜) : ⇑(f * g) = f ∘ g := rfl
/-
**GradedRingHom.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `GradedRingHom`。
形式化陈述：instMonoid : Monoid (𝒜 ->+*ᵍ 𝒜) where mul_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.comp_assoc`：comp_assoc (h : 𝒞 ->+*ᵍ 𝒟) (g : ℬ ->+*ᵍ 𝒞) (f 
: 𝒜 ->+*ᵍ ℬ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `GradedRingHom.id_comp`：id_comp (f : 𝒜 ->+*ᵍ ℬ) : (id ℬ).comp f = f
· 使用定理 `GradedRingHom.comp_id`：comp_id (f : 𝒜 ->+*ᵍ ℬ) : f.comp (id 𝒜) = f
-/
instance instMonoid : Monoid (𝒜 →+*ᵍ 𝒜) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *]
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _
/-
**GradedRingHom.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_6} [inst : Semiring A] [inst_1
 : SetLike σ A] {𝒜 : ι → σ} (f : 𝒜 →+*ᵍ 𝒜)   (n : ℕ), ⇑(f ^ n) = (⇑f)^[n]
参数：f : 𝒜 →+*ᵍ 𝒜；n : ℕ；f ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (f : 𝒜 →+*ᵍ 𝒜) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
/-
**GradedRingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：cancel_right {g₁ g₂ : ℬ ->+*ᵍ 𝒞} {f : 𝒜 ->+*ᵍ ℬ} (hf : Function.Surjective
 f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GradedRingHom.ext_iff`：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ
 : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 
: SetLike σ…
-/
theorem cancel_right {g₁ g₂ : ℬ →+*ᵍ 𝒞} {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (GradedRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/-
**GradedRingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`。
形式化陈述：cancel_left {g : ℬ ->+*ᵍ 𝒞} {f₁ f₂ : 𝒜 ->+*ᵍ ℬ} (hg : Function.Injective g
) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.ext`：ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GradedRingHom.comp_apply`：comp_apply (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ)
 (x : A) : (hnp.comp hmn : A -> C) x = hnp (hmn x)
-/
theorem cancel_left {g : ℬ →+*ᵍ 𝒞} {f₁ f₂ : 𝒜 →+*ᵍ ℬ} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

-- Note: if `GradedAddHom` is added later, then the assumptions can be relaxed.
/-- A graded ring homomorphism descends to an additive homomorphism on each indexed component. -/
/-
**GradedRingHom.gradedAddHom** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {σ : Type u
_6} →         {τ : Type u_7} →           [inst : Semiring A] →             [inst
_1 : Semiring B] →               [inst_2 : SetLike σ A] →                 [inst_
3 : SetLike τ B] →                   {𝒜 : ι → σ} →                     {ℬ : ι → 
τ} →                       [inst_4 : AddSubmonoidClass σ A] →                   
      [inst_5 : AddSubmonoidClass τ B] → (𝒜 →+*ᵍ ℬ) → (i : ι) → ↥(𝒜 i) →+ ↥(ℬ i)
参数：𝒜 →+*ᵍ ℬ；i : ι；𝒜 i；ℬ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded ring homomorphism descends to an additive homomorphism on each indexed 
component.
-/
@[simps!] def gradedAddHom [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
    (f : 𝒜 →+*ᵍ ℬ) (i : ι) : 𝒜 i →+ ℬ i where
  toFun x := ⟨f x, map_mem f x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- A graded ring homomorphism descends to a ring homomorphism on the zeroth component. -/
/-
**GradedRingHom.gradedZeroRingHom** 是 Mathlib 中的一个定义，位于命名空间 `GradedRingHom`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {σ : Type u
_6} →         {τ : Type u_7} →           [inst : Semiring A] →             [inst
_1 : Semiring B] →               [inst_2 : SetLike σ A] →                 [inst_
3 : SetLike τ B] →                   {𝒜 : ι → σ} →                     {ℬ : ι → 
τ} →                       [inst_4 : AddSubmonoidClass σ A] →                   
      [inst_5 : AddSubmonoidClass τ B] →                           [inst_6 : Add
Monoid ι] →                             [inst_7 : SetLike.GradedMonoid 𝒜] →     
                          [inst_8 : SetLike.GradedMonoid ℬ] → (𝒜 →+*ᵍ ℬ) → ↥(𝒜 0
) →+* ↥(ℬ 0)
参数：𝒜 →+*ᵍ ℬ；𝒜 0；ℬ 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded ring homomorphism descends to a ring homomorphism on the zeroth compone
nt.
-/
@[simps!] def gradedZeroRingHom [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddMonoid ι]
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ] (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  __ := f.gradedAddHom 0
  map_one' := Subtype.ext <| map_one _
  map_mul' _ _ := Subtype.ext <| map_mul ..

end GradedRingHom

end SetLike

section GradedRing
variable [DecidableEq ι] [AddMonoid ι] [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
variable (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

-- not simp because `𝒜` cannot be inferred
/-
**DirectSum.decompose_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirectSum.decompose_map (f : F) {x : A} : DirectSum.decompose ℬ (f x) = .m
ap (GradedRingHom.gradedAddHom <| .ofClass f) (.decompose 𝒜 x)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `DirectSum.decompose_sum`：decompose_sum {ι'} (s : Finset ι') (f : ι' -> M
) : decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `DirectSum.map_of`：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u_5}
 [inst : (i : ι) → AddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (β i
)] (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma DirectSum.decompose_map (f : F) {x : A} :
    DirectSum.decompose ℬ (f x) =
      .map (GradedRingHom.gradedAddHom <| .ofClass f) (.decompose 𝒜 x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum, DirectSum.decompose_sum,
    DirectSum.decompose_sum, map_sum]
  congr 1
  simp [DirectSum.decompose_of_mem _ (map_mem f (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of, GradedRingHom.gradedAddHom]

-- not simp because `ℬ` cannot be inferred
-- for every concrete instance of GradedFunLike, we need one simp lemma
/-
**map_directSumDecompose** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_directSumDecompose (f : F) {x : A} {i : ι} : f (DirectSum.decompose 𝒜 
x i) = DirectSum.decompose ℬ (f x) i
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `DirectSum.decompose_map`：DirectSum.decompose_map (f : F) {x : A} : Direc
tSum.decompose ℬ (f x) = .map (GradedRingHom.gradedAddHom <| .ofClass f) (.decom
pose 𝒜 x)
· 使用定理 `DirectSum.map_apply`：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u
_5} [inst : (i : ι) → AddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (
β i)] (f …
· 使用定理 `GradedRingHom.gradedAddHom_apply_coe`：∀ {ι : Type u_1} {A : Type u_2} {B
 : Type u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semirin
g B]   [inst_2 : SetLike σ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_directSumDecompose (f : F) {x : A} {i : ι} :
    f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i := by
  simp [DirectSum.decompose_map 𝒜]
/-
**GradedRingHom.map_directSumDecompose** 是 Mathlib 中的一个定理，位于命名空间 `GradedRingHom`
。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ : Type u_6} {τ : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : DecidableEq ι] [inst_5 : AddMonoid ι]   [inst_6 : AddSubm
onoidClass σ A] [inst_7 : AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) {x : A} {i : ι},   f ↑
(((DirectSum.decompose 𝒜) x) i) = ↑(((DirectSum.decompose ℬ) (f x)) i)
参数：𝒜 : ι → σ；ℬ : ι → τ；f : 𝒜 →+*ᵍ ℬ；((DirectSum.decompose 𝒜) x) i；((DirectSum.de
compose ℬ) (f x)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_directSumDecompose`：map_directSumDecompose (f : F) {x : A} {i : ι} :
 f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
-/
@[simp] lemma GradedRingHom.map_directSumDecompose (f : 𝒜 →+*ᵍ ℬ) {x : A} {i : ι} :
    f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i :=
  _root_.map_directSumDecompose ..

end GradedRing

