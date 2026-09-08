/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!

# Basis of a polynomial ring

-/

@[expose] public noncomputable section

open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

/-- The monomials form a basis on `R[X]`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`. -/
/-
**Polynomial.basisMonomials** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：basisMonomials : Basis Nat R R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monomials form a basis on `R[X]`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`.
-/
def basisMonomials : Basis ℕ R R[X] :=
  .ofRepr <| (toFinsuppIsoLinear R).trans <| AddMonoidAlgebra.coeffLinearEquiv _

@[simp]
/-
**Polynomial.coe_basisMonomials** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_basisMonomials : (basisMonomials R : Nat -> R[X]) = fun s => monomial 
s 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.ofFinsupp_single`：ofFinsupp_single (n : Nat) (r : R) : (⟨.sin
gle n r⟩ : R[X]) = monomial n r
-/
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _

end Polynomial

