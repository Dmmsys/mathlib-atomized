/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic.Contrapose

/-!
# `NoZeroSMulDivisors`

This file defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).

## Usage notes

Note that `NoZeroSMulDivisors` is deprecated in favor of `Module.IsTorsionFree`, which is the
mathematically correct generalisation to semimodules.
-/

public section

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀

variable {R M G : Type*}

/-- `NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplication.
-/
@[mk_iff]
/-
**NoZeroSMulDivisors** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_4) → (M : Type u_5) → [Zero R] → [Zero M] → [SMul R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either arg
ument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is ze
ro-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0
`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplica
tion.
-/
class NoZeroSMulDivisors (R M : Type*) [Zero R] [Zero M] [SMul R M] : Prop where
  /-- If scalar multiplication yields zero, either the scalar or the vector was zero. -/
  eq_zero_or_eq_zero_of_smul_eq_zero : ∀ {c : R} {x : M}, c • x = 0 → c = 0 ∨ x = 0

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/-- Pullback a `NoZeroSMulDivisors` instance along an injective function. -/
/-
**Function.Injective.noZeroSMulDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Z
ero N] [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M -> N) (hf : Functio
n.Injective f) (h0 : f 0 = 0) (hs : forall (c : R) (x : M), f (c • x) = c • f x)
 : NoZeroSMulDivisors R M
参数：f : M -> N；hf : Function.Injective f；h0 : f 0 = 0；hs : forall (c : R) (x : M)
, f (c • x) = c • f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero`：∀ {R : Type u_4} 
{M : Type u_5} {inst : Zero R} {inst_1 : Zero M} {inst_2 : SMul R M} [self : NoZ
eroSMulDivisors R M]   {c : R} {x : M}, c •…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Pullback a `NoZeroSMulDivisors` instance along an injective function.
-/
theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M → N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h =>
    Or.imp_right (@hf _ _) <| h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NoZeroDivisors.toNoZeroSMulDivisors [Zero R] [Mul R]
    [NoZeroDivisors R] : NoZeroSMulDivisors R R :=
  ⟨fun {_ _} => eq_zero_or_eq_zero_of_mul_eq_zero⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
    Module.IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    dsimp at hm
    rw [← sub_eq_zero, ← smul_sub] at hm
    simpa [hr.ne_zero, sub_eq_zero] using eq_zero_or_eq_zero_of_smul_eq_zero hm
/-
**noZeroSMulDivisors_iff_right_eq_zero_of_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] 
: NoZeroSMulDivisors R M ↔ forall r : R, r != 0 -> forall m : M, r • m = 0 -> m 
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] :
    NoZeroSMulDivisors R M ↔ ∀ r : R, r ≠ 0 → ∀ m : M, r • m = 0 → m = 0 := by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq ↦ h eq hr, fun h r m eq hr ↦ h r hr m eq⟩
/-
**IsAddTorsionFree.to_noZeroSMulDivisors_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree
 M] : NoZeroSMulDivisors Nat M where eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2
/-
**IsAddTorsionFree.to_noZeroSMulDivisors_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree 
G] : NoZeroSMulDivisors Int G where eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `zsmul_right_injective`：∀ {G : Type u_2} [inst : AddGroup G] [IsAddTorsio
nFree G] {n : ℤ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree G] :
    NoZeroSMulDivisors ℤ G where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2
