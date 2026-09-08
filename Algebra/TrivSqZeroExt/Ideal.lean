/-
Copyright (c) 2026 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The square zero ideal of the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal`: the ideal in the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal_sq `: this ideal has square zero.

-/

@[expose] public section

namespace TrivSqZeroExt

open Ideal

variable (R M : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The kernel of the `AlgHom` `fstHom R R M` -/
/-
**TrivSqZeroExt.kerIdeal** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：kerIdeal : Ideal (TrivSqZeroExt R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of the `AlgHom` `fstHom R R M`
-/
def kerIdeal : Ideal (TrivSqZeroExt R M) := RingHom.ker (fstHom R R M)

set_option backward.isDefEq.respectTransparency false in
/-
**TrivSqZeroExt.mem_kerIdeal_iff_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x in kerIdeal R M ↔ x = inr
 x.snd
参数：x : TrivSqZeroExt R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TrivSqZeroExt.fstHom_apply`：∀ (S : Type u_1) (R : Type u) (M : Type v) [
inst : CommSemiring S] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_
3 : Algebra S R]…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.fst_mk`：fst_mk (r : R) (m : M) : fst (r, m) = r
· 使用定理 `TrivSqZeroExt.fst_inr`：fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst
 = 0
-/
theorem mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x ∈ kerIdeal R M ↔ x = inr x.snd := by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩
/-
**TrivSqZeroExt.kerIdeal_sq** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ (R : Type u_1) (M : Type u_2) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : _root_.Module Rᵐᵒᵖ M] [inst_4 
: IsCentralScalar R M], TrivSqZeroExt.kerIdeal R M ^ 2 = ⊥
参数：R : Type u_1；M : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `TrivSqZeroExt.inr_mul_inr`：inr_mul_inr [Semiring R] [AddCommMonoid M] [M
odule R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) : (inr m₁ * inr m₂ : tsze R M) = 0
-/
@[simp] theorem kerIdeal_sq : kerIdeal R M ^ 2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, mul_le, mem_kerIdeal_iff_inr]
  rintro x hx y hy
  rw [hx, hy, mem_bot, inr_mul_inr]

end TrivSqZeroExt

end

