/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basis of an opposite space

This file defines the basis of an opposite space and shows
that the opposite space is finite-dimensional and free when the original space is.
-/

@[expose] public section

open Module MulOpposite

variable {R H : Type*}

namespace Module.Basis

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

/-- The multiplicative opposite of a basis: `b.mulOpposite i ↦ op (b i)`. -/
/-
**Module.Basis.mulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ
参数：b : Basis ι R H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative opposite of a basis: `b.mulOpposite i ↦ op (b i)`.
-/
noncomputable def mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ :=
  b.map (opLinearEquiv R)

@[simp]
/-
**Module.Basis.mulOpposite_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mulOpposite_apply (b : Basis ι R H) (i : ι) : b.mulOpposite i = op (b i)
参数：b : Basis ι R H；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulOpposite_apply (b : Basis ι R H) (i : ι) :
    b.mulOpposite i = op (b i) := rfl
/-
**Module.Basis.mulOpposite_repr_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mulOpposite_repr_eq (b : Basis ι R H) : b.mulOpposite.repr = (opLinearEqui
v R).symm.trans b.repr
参数：b : Basis ι R H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulOpposite_repr_eq (b : Basis ι R H) :
    b.mulOpposite.repr = (opLinearEquiv R).symm.trans b.repr := rfl

@[simp]
/-
**Module.Basis.repr_unop_eq_mulOpposite_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.B
asis`。
形式化陈述：repr_unop_eq_mulOpposite_repr (b : Basis ι R H) (x : Hᵐᵒᵖ) : b.repr (unop 
x) = b.mulOpposite.repr x
参数：b : Basis ι R H；x : Hᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_unop_eq_mulOpposite_repr (b : Basis ι R H) (x : Hᵐᵒᵖ) :
    b.repr (unop x) = b.mulOpposite.repr x := rfl

@[simp]
/-
**Module.Basis.mulOpposite_repr_op** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mulOpposite_repr_op (b : Basis ι R H) (x : H) : b.mulOpposite.repr (op x) 
= b.repr x
参数：b : Basis ι R H；x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulOpposite_repr_op (b : Basis ι R H) (x : H) :
    b.mulOpposite.repr (op x) = b.repr x := rfl

end Module.Basis

namespace MulOpposite

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing R] [AddCommGroup H] [Module R H]
    [FiniteDimensional R H] : FiniteDimensional R Hᵐᵒᵖ := FiniteDimensional.of_finite_basis
  (Basis.ofVectorSpace R H).mulOpposite (Basis.ofVectorSpaceIndex R H).toFinite
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.Free R Hᵐᵒᵖ :=
  let ⟨b⟩ := Module.Free.exists_basis (R := R) (M := H)
  Module.Free.of_basis b.2.mulOpposite
/-
**MulOpposite.rank** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：rank [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H] [
Module.Free R H] : Module.rank R Hᵐᵒᵖ = Module.rank R H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.nonempty_linearEquiv_iff_rank_eq`：Module.nonempty_linearEquiv_iff
_rank_eq : Nonempty (M ≃ₗ[R] M₁) ↔ Module.rank R M = Module.rank R M₁
· 使用定理 `MulOpposite.instFree`：∀ {R : Type u_1} {H : Type u_2} [inst : Semiring R
] [inst_1 : AddCommMonoid H] [inst_2 : _root_.Module R H]   [Module.Free R H], M
odule.Free…
-/
theorem rank [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.rank R Hᵐᵒᵖ = Module.rank R H :=
  Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨(opLinearEquiv R).symm⟩
/-
**MulOpposite.finrank** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：finrank [DivisionRing R] [AddCommGroup H] [Module R H] : Module.finrank R 
Hᵐᵒᵖ = Module.finrank R H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_nat_card_basis`：finrank_eq_nat_card_basis (h : Basis ι
 R M) : finrank R M = Nat.card ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem finrank [DivisionRing R] [AddCommGroup H] [Module R H] :
    Module.finrank R Hᵐᵒᵖ = Module.finrank R H := by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis b.mulOpposite]

end MulOpposite

