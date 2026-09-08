/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMulWithZero

/-!
# The pointwise product on `Finsupp`.

For the convolution product on `Finsupp` when the domain has a binary operation,
see the type synonyms `AddMonoidAlgebra`
(which is in turn used to define `Polynomial` and `MvPolynomial`)
and `MonoidAlgebra`.
-/

@[expose] public section


noncomputable section

open Finset

universe u₁ u₂ u₃ u₄ u₅

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace Finsupp

/-! ### Declarations about the pointwise product on `Finsupp`s -/


section

variable [MulZeroClass β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`.
-/
instance : Mul (α →₀ β) :=
  ⟨zipWith (· * ·) (mul_zero 0)⟩
/-
**Finsupp.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_mul (g₁ g₂ : α ->₀ β) : ⇑(g₁ * g₂) = g₁ * g₂
参数：g₁ g₂ : α ->₀ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl

@[simp]
/-
**Finsupp.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mul_apply {g₁ g₂ : α ->₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

@[simp]
/-
**Finsupp.single_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_mul (a : α) (b₁ b₂ : β) : single a (b₁ * b₂) = single a b₁ * single
 a b₂
参数：a : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.zipWith_single_single`：zipWith_single_single (f : M -> N -> P) (
hf : f 0 0 = 0) (a : α) (m : M) (n : N) : zipWith f hf (single a m) (single a n)
 = single a (f m n)
-/
theorem single_mul (a : α) (b₁ b₂ : β) : single a (b₁ * b₂) = single a b₁ * single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm
/-
**Finsupp.support_mul_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_mul_subset_left {g₁ g₂ : α ->₀ β} : (g₁ * g₂).support subseteq g₁.
support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma support_mul_subset_left {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support := fun x hx => by
  aesop
/-
**Finsupp.support_mul_subset_right** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_mul_subset_right {g₁ g₂ : α ->₀ β} : (g₁ * g₂).support subseteq g₂
.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma support_mul_subset_right {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₂.support := fun x hx => by
  aesop
/-
**Finsupp.support_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_mul [DecidableEq α] {g₁ g₂ : α ->₀ β} : (g₁ * g₂).support subseteq
 g₁.support inter g₂.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_inter`：subset_inter {s₁ s₂ u : Finset α} : s₁ subseteq s₂ 
-> s₁ subseteq u -> s₁ subseteq s₂ inter u
· 使用引理 `Finsupp.support_mul_subset_left`：support_mul_subset_left {g₁ g₂ : α ->₀ 
β} : (g₁ * g₂).support subseteq g₁.support
· 使用引理 `Finsupp.support_mul_subset_right`：support_mul_subset_right {g₁ g₂ : α ->
₀ β} : (g₁ * g₂).support subseteq g₂.support
-/
theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
  subset_inter support_mul_subset_left support_mul_subset_right
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulZeroClass (α →₀ β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

end

/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing β] : NonUnitalCommRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**Finsupp.pointwise_smul_support_finite** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：pointwise_smul_support_finite [Zero γ] [SMulZeroClass β γ] (f : α -> β) (g
 : α ->₀ γ) : (fun x => f x • g x).support.Finite
参数：f : α -> β；g : α ->₀ γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finsupp.hasFiniteSupport`：hasFiniteSupport (f : α ->₀ M) : HasFiniteSupp
ort f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.fun_support_eq`：fun_support_eq (f : α ->₀ M) : Function.support 
f = f.support
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma pointwise_smul_support_finite [Zero γ] [SMulZeroClass β γ] (f : α → β)
    (g : α →₀ γ) : (fun x ↦ f x • g x).support.Finite :=
  Set.Finite.subset g.hasFiniteSupport (by simp; grind [smul_zero])

-- TODO(Paul-Lez): add a `DFinsupp` version of this.
-- Note: this creates an instance diamond with `SMul (α → β) (α →₀ (α → β))`, so this is an
-- def rather than an instance.
/-- Pointwise scalar multiplication given by `(f • g) x = f x • g x`. -/
-- see Note [reducible non-instances]
/-
**Finsupp.pointwiseScalar** 是 Mathlib 中的一个缩写定义，位于命名空间 `Finsupp`。
形式化陈述：pointwiseScalar [Zero γ] [SMulZeroClass β γ] : SMul (α -> β) (α ->₀ γ) whe
re smul f g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.pointwise_smul_support_finite`：pointwise_smul_support_finite [Ze
ro γ] [SMulZeroClass β γ] (f : α -> β) (g : α ->₀ γ) : (fun x => f x • g x).supp
ort.Finite
-/
abbrev pointwiseScalar [Zero γ] [SMulZeroClass β γ] : SMul (α → β) (α →₀ γ) where
  smul f g := Finsupp.ofSupportFinite (fun a ↦ f a • g a) (pointwise_smul_support_finite ..)
/-
**Finsupp.pointwiseScalarSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：pointwiseScalarSemiring [Semiring β] : SMul (α -> β) (α ->₀ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pointwiseScalarSemiring [Semiring β] : SMul (α → β) (α →₀ β) := pointwiseScalar

@[simp]
/-
**Finsupp.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_pointwise_smul [Semiring β] (f : α -> β) (g : α ->₀ β) : ⇑(f • g) = f 
• ⇑g
参数：f : α -> β；g : α ->₀ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul [Semiring β] (f : α → β) (g : α →₀ β) : ⇑(f • g) = f • ⇑g :=
  rfl

/-- The pointwise multiplicative action of functions on finitely supported functions -/
/-
**Finsupp.pointwiseModule** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：pointwiseModule [Semiring β] : Module (α -> β) (α ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.coe_pointwise_smul`：coe_pointwise_smul [Semiring β] (f : α -> β)
 (g : α ->₀ β) : ⇑(f • g) = f • ⇑g

--- 原说明 ---
The pointwise multiplicative action of functions on finitely supported functions
-/
instance pointwiseModule [Semiring β] : Module (α → β) (α →₀ β) :=
  Function.Injective.module _ coeFnAddHom DFunLike.coe_injective coe_pointwise_smul
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring β] : IsScalarTower β (α → β) (α →₀ β) where
  smul_assoc r f m := by ext; simp [mul_assoc]

end Finsupp

