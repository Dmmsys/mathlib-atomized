/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Pi
public import Mathlib.RingTheory.Unramified.Pi
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!

# Formal-étaleness of finite products of rings

## Main result

- `Algebra.FormallyEtale.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-étale
  if and only if each `A i` is `R`-formally-étale.

-/

public section

namespace Algebra.FormallyEtale

variable {R : Type*} {I : Type*} (A : I → Type*)
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

/-
**Algebra.FormallyEtale.pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyEtale`
。
形式化陈述：pi_iff [Finite I] : FormallyEtale R (Π i, A i) ↔ forall i, FormallyEtale R
 (A i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Algebra.FormallyUnramified.pi_iff`：pi_iff : FormallyUnramified R (forall
 i, f i) ↔ forall i, FormallyUnramified R (f i)
· 使用定理 `Algebra.FormallySmooth.pi_iff`：pi_iff [Finite I] : FormallySmooth R (Π i
, A i) ↔ forall i, FormallySmooth R (A i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pi_iff [Finite I] :
    FormallyEtale R (Π i, A i) ↔ ∀ i, FormallyEtale R (A i) := by
  simp_rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, forall_and]
  rw [FormallyUnramified.pi_iff A, FormallySmooth.pi_iff A]
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite I] [∀ i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i) :=
  .of_formallyUnramified_and_formallySmooth
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite I] [∀ i, Etale R (A i)] : Etale R (Π i, A i) where

end Algebra.FormallyEtale

