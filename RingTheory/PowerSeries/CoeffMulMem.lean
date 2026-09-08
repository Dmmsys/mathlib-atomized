/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Some results on the coefficients of multiplication of two power series

## Main results

- `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` and `g` are
  in ideals `I` and `J`, respectively, then for all `i ≤ n` (resp. for all `i`), the `i`-th
  coefficients of `f * g` are in `I * J`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `g` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

-/

public section

namespace PowerSeries

variable {A : Type*} [Semiring A] {I J : Ideal A} {f g : A⟦X⟧} (n : ℕ)

/-
**PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal** 是 Mathlib 中的一个定
理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coef
f i f in I) (hg : forall i <= n, coeff i g in J) : forall i <= n, coeff i (f * g
) in I * J
参数：hf : forall i <= n, coeff i f in I；hg : forall i <= n, coeff i g in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.snd_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
-/
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : ∀ i ≤ n, coeff i f ∈ I)
    (hg : ∀ i ≤ n, coeff i g ∈ J) : ∀ i ≤ n, coeff i (f * g) ∈ I * J := fun i hi ↦ by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp ↦ Ideal.mul_mem_mul
    (hf _ ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hi))
/-
**PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'** 是 Mathlib 中的一个
定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : forall i, coeff i 
f in I) (hg : forall i, coeff i g in J) : forall i, coeff i (f * g) in I * J
参数：hf : forall i, coeff i f in I；hg : forall i, coeff i g in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`：coeff_mul_
mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coeff i f in I) (hg 
: forall i <= n, coeff i g in J) : forall i <= n, …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : ∀ i, coeff i f ∈ I)
    (hg : ∀ i, coeff i g ∈ J) : ∀ i, coeff i (f * g) ∈ I * J :=
  fun i ↦ coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i
    (fun i _ ↦ hf i) (fun i _ ↦ hg i) i le_rfl
/-
**PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal** 是 Mathlib 中的一个定理，位于
命名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_of_coeff_right_mem_ideal (hg : forall i <= n, coeff i 
g in I) : forall i <= n, coeff i (f * g) in I
参数：hg : forall i <= n, coeff i g in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.top_mul`：top_mul : ⊤ * I = I
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`：coeff_mul_
mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coeff i f in I) (hg 
: forall i <= n, coeff i g in J) : forall i <= n, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
    (hg : ∀ i ≤ n, coeff i g ∈ I) : ∀ i ≤ n, coeff i (f * g) ∈ I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) (f := f) n (by simp) hg
/-
**PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal'** 是 Mathlib 中的一个定理，位
于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (hg : forall i, coeff i g in
 I) : forall i, coeff i (f * g) in I
参数：hg : forall i, coeff i g in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.top_mul`：top_mul : ⊤ * I = I
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`：coeff_mul
_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : forall i, coeff i f in I) (hg : f
orall i, coeff i g in J) : forall i, coeff i (f * g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (hg : ∀ i, coeff i g ∈ I) : ∀ i, coeff i (f * g) ∈ I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) (f := f) (by simp) hg

variable [I.IsTwoSided]
/-
**PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal** 是 Mathlib 中的一个定理，位于命
名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_of_coeff_left_mem_ideal (hf : forall i <= n, coeff i f
 in I) : forall i <= n, coeff i (f * g) in I
参数：hf : forall i <= n, coeff i f in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsTwoSided.mul_one`：∀ {R : Type u} [inst : Semiring R] {I : Ideal 
R} [I.IsTwoSided], I * 1 = I
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`：coeff_mul_
mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coeff i f in I) (hg 
: forall i <= n, coeff i g in J) : forall i <= n, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
    (hf : ∀ i ≤ n, coeff i f ∈ I) : ∀ i ≤ n, coeff i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) (g := g) n hf (by simp)
/-
**PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal'** 是 Mathlib 中的一个定理，位于
命名空间 `PowerSeries`。
形式化陈述：coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (hf : forall i, coeff i f in 
I) : forall i, coeff i (f * g) in I
参数：hf : forall i, coeff i f in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsTwoSided.mul_one`：∀ {R : Type u} [inst : Semiring R] {I : Ideal 
R} [I.IsTwoSided], I * 1 = I
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`：coeff_mul
_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : forall i, coeff i f in I) (hg : f
orall i, coeff i g in J) : forall i, coeff i (f * g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
    (hf : ∀ i, coeff i f ∈ I) : ∀ i, coeff i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) (g := g) hf (by simp)

end PowerSeries

