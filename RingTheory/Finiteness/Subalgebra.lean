/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Bilinear

/-!
# Subalgebras that are finitely generated as submodules
-/

public section

open Function (Surjective)
open Finsupp

namespace Subalgebra

open Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-
**Subalgebra.fg_bot_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_bot_toSubmodule : (⊥ : Subalgebra R A).toSubmodule.FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fg_bot_toSubmodule : (⊥ : Subalgebra R A).toSubmodule.FG :=
  ⟨{1}, by simp [Algebra.toSubmodule_bot, one_eq_span]⟩
/-
**Subalgebra.finite_bot** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：finite_bot : Module.Finite R (⊥ : Subalgebra R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finite_bot : Module.Finite R (⊥ : Subalgebra R A) :=
  Module.Finite.range (Algebra.linearMap R A)

end Subalgebra

namespace Submodule

/-
**Submodule.fg_unit** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Su
bmodule R A)ˣ) : (I : Submodule R A).FG
参数：I : (Submodule R A)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_mul_finite_of_mem_mul`：mem_span_mul_finite_of_mem_mul
 {P Q : Submodule R A} {x : A} (hx : x in P * Q) : exists T T' : Finset A, (T : 
Set A) subseteq P ∧ (T' : Set …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
-/
theorem fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ) :
    (I : Submodule R A).FG := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.mul_inv ▸ one_le.mp le_rfl)
  refine ⟨T, span_eq_of_le _ hT ?_⟩
  rw [← one_mul I, ← mul_one (span R (T : Set A))]
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  grw [← span_le.mpr hT', Units.val_mul, Units.val_one, span_mul_span, one_le.2 one_mem]
/-
**Submodule.fg_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_of_isUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I 
: Submodule R A} (hI : IsUnit I) : I.FG
参数：hI : IsUnit I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_unit`：fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [
Algebra R A] (I : (Submodule R A)ˣ) : (I : Submodule R A).FG
-/
theorem fg_of_isUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
    (hI : IsUnit I) : I.FG :=
  fg_unit hI.unit

section Mul

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable {M N : Submodule R A}

/-
**Submodule.FG.mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   {M N : Submodule R A}, M.FG → N.FG → (M * N).FG
参数：M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用定理 `Submodule.FG.map₂`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P : T
ype u_4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommM
onoid N…
-/
theorem FG.mul (hm : M.FG) (hn : N.FG) : (M * N).FG := by
  rw [mul_eq_map₂]; exact hm.map₂ _ hn
/-
**Submodule.FG.pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   {M : Submodule R A}, M.FG → ∀ (n : ℕ), (M ^ n).FG
参数：n : ℕ；M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Submodule.FG.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M N : Submodule R A}, M.FG → N
.FG → …
-/
theorem FG.pow (h : M.FG) (n : ℕ) : (M ^ n).FG :=
  Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using ih.mul h

end Mul

end Submodule

