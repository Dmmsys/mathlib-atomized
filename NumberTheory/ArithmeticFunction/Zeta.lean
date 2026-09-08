/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# The arithmetic function `ζ`

We define `ζ` to be the arithmetic function with `ζ n = 1` for `0 < n` (whose Dirichlet series
is the Riemann zeta function).

## Main Definitions

* `ArithmeticFunction.zeta` is the arithmetic function such that `ζ x = 1` for `0 < x`. The notation
  `ζ` for this function is available by opening `ArithmeticFunction.zeta`.
* `ArithmeticFunction.pmul` and `ArithmeticFunction.pdiv` are the pointwise multiplication and
  division on `ArithmeticFunction`s (for which `ζ` is the identity). These are not the same as
  the multiplication instance defined by Dirichlet convolution.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann `ζ`. -/
/-
**ArithmeticFunction.zeta** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：zeta : ArithmeticFunction Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann `ζ`.
-/
def zeta : ArithmeticFunction ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta

open scoped zeta

section Zeta

@[simp]
/-
**ArithmeticFunction.zeta_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：zeta_apply {x : Nat} : ζ x = if x = 0 then 0 else 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeta_apply {x : ℕ} : ζ x = if x = 0 then 0 else 1 :=
  rfl
/-
**ArithmeticFunction.zeta_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：zeta_apply_ne {x : Nat} (h : x != 0) : ζ x = 1
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 :=
  if_neg h

set_option backward.isDefEq.respectTransparency false in
/-
**ArithmeticFunction.zeta_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：zeta_eq_zero {x : Nat} : ζ x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zeta_eq_zero {x : ℕ} : ζ x = 0 ↔ x = 0 := by simp [zeta]
/-
**ArithmeticFunction.zeta_pos** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：zeta_pos {x : Nat} : 0 < ζ x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zeta_pos {x : ℕ} : 0 < ζ x ↔ 0 < x := by simp [pos_iff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**ArithmeticFunction.coe_zeta_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [MulAction R M] {f 
: ArithmeticFunction M} {x : Nat} : ((↑ζ : ArithmeticFunction R) • f) x = ∑ i in
 divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.smul_apply`：smul_apply {f : ArithmeticFunction R} {g 
: ArithmeticFunction M} {n : Nat} : (f • g) n = ∑ x in divisorsAntidiagonal n, f
 x.fst • g x.snd
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `ArithmeticFunction.natCoe_apply`：natCoe_apply [AddMonoidWithOne R] {f : 
ArithmeticFunction Nat} {x : Nat} : (f : ArithmeticFunction R) x = f x
· 使用定理 `ArithmeticFunction.zeta_apply_ne`：zeta_apply_ne {x : Nat} (h : x != 0) :
 ζ x = 1
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.map_div_left_divisors`：map_div_left_divisors : n.divisors.map ⟨fun d
 => (n / d, d), fun _ _ => congr_arg Prod.snd⟩ = n.divisorsAntidiagonal
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
theorem coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    ((↑ζ : ArithmeticFunction R) • f) x = ∑ i ∈ divisors x, f i := by
  rw [smul_apply]
  trans ∑ i ∈ divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]

/-- `@[simp]`-normal form of `coe_zeta_smul_apply`. -/
@[simp]
/-
**ArithmeticFunction.sum_divisorsAntidiagonal_eq_sum_divisors** 是 Mathlib 中的一个定理
，位于命名空间 `ArithmeticFunction`。
形式化陈述：sum_divisorsAntidiagonal_eq_sum_divisors {M} [Semiring R] [AddCommMonoid M
] [MulAction R M] {f : ArithmeticFunction M} {x : Nat} : (∑ x in x.divisorsAntid
iagonal, if x.1 = 0 then (0 : R) • f x.2 else f x.2) = ∑ i in divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.coe_zeta_smul_apply`：coe_zeta_smul_apply {M} [Semirin
g R] [AddCommMonoid M] [MulAction R M] {f : ArithmeticFunction M} {x : Nat} : ((
↑ζ : ArithmeticFunction R) •…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`@[simp]`-normal form of `coe_zeta_smul_apply`.
-/
theorem sum_divisorsAntidiagonal_eq_sum_divisors {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    (∑ x ∈ x.divisorsAntidiagonal, if x.1 = 0 then (0 : R) • f x.2 else f x.2) =
      ∑ i ∈ divisors x, f i := by
  simp [← coe_zeta_smul_apply (R := R)]
/-
**ArithmeticFunction.coe_zeta_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：coe_zeta_mul_comm [Semiring R] {f : ArithmeticFunction R} : ζ * f = f * ζ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `Nat.sum_divisorsAntidiagonal`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.div
isors, f i (n / i)
· 使用定理 `Nat.sum_divisorsAntidiagonal'`：∀ {M : Type u_1} [inst : AddCommMonoid M]
 (f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.di
visors, f (n / i) i
-/
theorem coe_zeta_mul_comm [Semiring R] {f : ArithmeticFunction R} : ζ * f = f * ζ := by
  ext n
  simp_rw [mul_apply, natCoe_apply, (cast_commute ..).eq]
  rw [sum_divisorsAntidiagonal fun x y ↦ f y * ζ x, sum_divisorsAntidiagonal' fun x y ↦ f x * ζ y]
/-
**ArithmeticFunction.coe_zeta_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : Nat} : (ζ 
* f) x = ∑ i in divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.coe_zeta_smul_apply`：coe_zeta_smul_apply {M} [Semirin
g R] [AddCommMonoid M] [MulAction R M] {f : ArithmeticFunction M} {x : Nat} : ((
↑ζ : ArithmeticFunction R) •…
-/
theorem coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (ζ * f) x = ∑ i ∈ divisors x, f i :=
  coe_zeta_smul_apply

set_option backward.isDefEq.respectTransparency false in
/-
**ArithmeticFunction.coe_mul_zeta_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : Nat} : (f 
* ζ) x = ∑ i in divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.coe_zeta_mul_comm`：coe_zeta_mul_comm [Semiring R] {f 
: ArithmeticFunction R} : ζ * f = f * ζ
· 使用定理 `ArithmeticFunction.coe_zeta_mul_apply`：coe_zeta_mul_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i
-/
theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (f * ζ) x = ∑ i ∈ divisors x, f i := by
  rw [← coe_zeta_mul_comm, coe_zeta_mul_apply]
/-
**ArithmeticFunction.zeta_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：zeta_mul_apply {f : ArithmeticFunction Nat} {x : Nat} : (ζ * f) x = ∑ i in
 divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.natCoe_nat`：natCoe_nat (f : ArithmeticFunction Nat) :
 natToArithmeticFunction f = f
· 使用定理 `ArithmeticFunction.coe_zeta_mul_apply`：coe_zeta_mul_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i
-/
theorem zeta_mul_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (ζ * f) x = ∑ i ∈ divisors x, f i := by
  rw [← natCoe_nat ζ, coe_zeta_mul_apply]
/-
**ArithmeticFunction.mul_zeta_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：mul_zeta_apply {f : ArithmeticFunction Nat} {x : Nat} : (f * ζ) x = ∑ i in
 divisors x, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.natCoe_nat`：natCoe_nat (f : ArithmeticFunction Nat) :
 natToArithmeticFunction f = f
· 使用定理 `ArithmeticFunction.coe_mul_zeta_apply`：coe_mul_zeta_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (f * ζ) x = ∑ i in divisors x, f i
-/
theorem mul_zeta_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (f * ζ) x = ∑ i ∈ divisors x, f i := by
  rw [← natCoe_nat ζ, coe_mul_zeta_apply]
/-
**ArithmeticFunction.zeta_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：zeta_mul_comm {f : ArithmeticFunction Nat} : ζ * f = f * ζ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.natCoe_nat`：natCoe_nat (f : ArithmeticFunction Nat) :
 natToArithmeticFunction f = f
· 使用定理 `ArithmeticFunction.coe_zeta_mul_comm`：coe_zeta_mul_comm [Semiring R] {f 
: ArithmeticFunction R} : ζ * f = f * ζ
-/
theorem zeta_mul_comm {f : ArithmeticFunction ℕ} : ζ * f = f * ζ := by
  rw [← natCoe_nat ζ, coe_zeta_mul_comm]

end Zeta

section Pmul

/-- This is the pointwise product of `ArithmeticFunction`s. -/
/-
**ArithmeticFunction.pmul** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R
参数：f g : ArithmeticFunction R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the pointwise product of `ArithmeticFunction`s.
-/
def pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun x => f x * g x, by simp⟩

@[simp]
/-
**ArithmeticFunction.pmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : Nat} : f.pmu
l g x = f x * g x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : ℕ} : f.pmul g x = f x * g x :=
  rfl
/-
**ArithmeticFunction.pmul_comm** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g =
 g.pmul f
参数：f g : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  simp [mul_comm]
/-
**ArithmeticFunction.pmul_assoc** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pmul_assoc [SemigroupWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R) : pmul 
(pmul f₁ f₂) f₃ = pmul f₁ (pmul f₂ f₃)
参数：f₁ f₂ f₃ : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pmul_assoc [SemigroupWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R) :
    pmul (pmul f₁ f₂) f₃ = pmul f₁ (pmul f₂ f₃) := by
  ext
  simp only [pmul_apply, mul_assoc]

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
/-
**ArithmeticFunction.pmul_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f
参数：f : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  cases x <;> simp

@[simp]
/-
**ArithmeticFunction.zeta_pmul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f =
 f
参数：f : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  cases x <;> simp

end NonAssocSemiring

variable [Semiring R]

open scoped zeta

/-- This is the pointwise power of `ArithmeticFunction`s. -/
/-
**ArithmeticFunction.ppow** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow (f : ArithmeticFunction R) (k : Nat) : ArithmeticFunction R
参数：f : ArithmeticFunction R；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the pointwise power of `ArithmeticFunction`s.
-/
def ppow (f : ArithmeticFunction R) (k : ℕ) : ArithmeticFunction R :=
  if h0 : k = 0 then ζ else ⟨fun x ↦ f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ArithmeticFunction.ppow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ppow.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : 
ArithmeticFunction R) (k : ℕ),   f.ppow k = if h0 : k = 0 then ↑ArithmeticFuncti
on.zeta else { toF…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]

@[simp]
/-
**ArithmeticFunction.ppow_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow_one {f : ArithmeticFunction R} : f.ppow 1 = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ppow_one {f : ArithmeticFunction R} : f.ppow 1 = f := by
  ext; simp [ppow]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ArithmeticFunction.ppow_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow_apply {f : ArithmeticFunction R} {k x : Nat} (kpos : 0 < k) : f.ppow 
k x = f x ^ k
参数：kpos : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ppow.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : 
ArithmeticFunction R) (k : ℕ),   f.ppow k = if h0 : k = 0 then ↑ArithmeticFuncti
on.zeta else { toF…
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ArithmeticFunction.coe_mk`：coe_mk (f : Nat -> R) (hf) : @DFunLike.coe (A
rithmeticFunction R) _ _ _ (ZeroHom.mk f hf) = f
-/
theorem ppow_apply {f : ArithmeticFunction R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow, dif_neg (Nat.ne_of_gt kpos), coe_mk]
/-
**ArithmeticFunction.ppow_succ'** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow_succ' {f : ArithmeticFunction R} {k : Nat} : f.ppow (k + 1) = f.pmul 
(f.ppow k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ppow_apply`：ppow_apply {f : ArithmeticFunction R} {k 
x : Nat} (kpos : 0 < k) : f.ppow k x = f x ^ k
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.ppow_zero`：ppow_zero {f : ArithmeticFunction R} : f.p
pow 0 = ζ
· 使用定理 `ArithmeticFunction.pmul_zeta`：pmul_zeta (f : ArithmeticFunction R) : f.p
mul ↑ζ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem ppow_succ' {f : ArithmeticFunction R} {k : ℕ} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  rw [ppow_apply (succ_pos k), _root_.pow_succ']
  induction k <;> simp
/-
**ArithmeticFunction.ppow_succ** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ppow_succ {f : ArithmeticFunction R} {k : Nat} {kpos : 0 < k} : f.ppow (k 
+ 1) = (f.ppow k).pmul f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ppow_apply`：ppow_apply {f : ArithmeticFunction R} {k 
x : Nat} (kpos : 0 < k) : f.ppow k x = f x ^ k
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ArithmeticFunction.ppow_zero`：ppow_zero {f : ArithmeticFunction R} : f.p
pow 0 = ζ
· 使用定理 `ArithmeticFunction.zeta_pmul`：zeta_pmul (f : ArithmeticFunction R) : (ζ 
: ArithmeticFunction R).pmul f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem ppow_succ {f : ArithmeticFunction R} {k : ℕ} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  rw [ppow_apply (succ_pos k), _root_.pow_succ]
  induction k <;> simp

end Pmul

section Pdiv

/-- This is the pointwise division of `ArithmeticFunction`s. -/
/-
**ArithmeticFunction.pdiv** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R
参数：f g : ArithmeticFunction R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the pointwise division of `ArithmeticFunction`s.
-/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, div_zero]⟩

@[simp]
/-
**ArithmeticFunction.pdiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : Nat) : pdiv
 f g n = f n / g n
参数：f g : ArithmeticFunction R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coercion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
/-
**ArithmeticFunction.pdiv_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) : pdiv f zeta = 
f
参数：f : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a

--- 原说明 ---
This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s becau
se zeta takes
values in ℕ, and hence the coercion requires an `AddMonoidWithOne`. TODO: Genera
lise zeta
-/
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  cases n <;> simp

end Pdiv

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_zeta** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：isMultiplicative_zeta : IsMultiplicative ζ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.IsMultiplicative.iff_ne_zero`：iff_ne_zero [MonoidWith
Zero R] {f : ArithmeticFunction R} : IsMultiplicative f ↔ f 1 = 1 ∧ forall {m n 
: Nat}, m != 0 -> n != 0 -> m.Coprime…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

namespace IsMultiplicative

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.pmul** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function.IsMultiplicative`。
形式化陈述：pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicativ
e) (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g)
参数：hf : f.IsMultiplicative；hg : g.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.pdiv** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function.IsMultiplicative`。
形式化陈述：pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplica
tive f) (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g)
参数：hf : IsMultiplicative f；hg : IsMultiplicative g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
-/
theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop, div_eq_mul_inv,
      mul_inv]
    apply mul_mul_mul_comm ⟩

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.ppow** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function.IsMultiplicative`。
形式化陈述：ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
 {k : Nat} : IsMultiplicative (f.ppow k)
参数：hf : f.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.natCast`：natCast {f : ArithmeticFunc
tion Nat} [Semiring R] (h : f.IsMultiplicative) : IsMultiplicative (f : Arithmet
icFunction R)
· 使用定理 `ArithmeticFunction.isMultiplicative_zeta`：isMultiplicative_zeta : IsMult
iplicative ζ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ppow_succ'`：ppow_succ' {f : ArithmeticFunction R} {k 
: Nat} : f.ppow (k + 1) = f.pmul (f.ppow k)
· 使用定理 `ArithmeticFunction.IsMultiplicative.pmul`：pmul [CommSemiring R] {f g : A
rithmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMul
tiplicative (f.pmul g)
-/
theorem ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

end IsMultiplicative

end ArithmeticFunction

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.zeta`. -/
@[positivity ArithmeticFunction.zeta _]
meta def evalArithmeticFunctionZeta : PositivityExt where eval {u α} z p? e :=
  match p? with | none => throwError "no PartialOrder instance" | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(ArithmeticFunction.zeta $n) =>
    assumeInstancesCommute
    let rn ← core z p n
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.zeta_pos $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.zeta"

end Mathlib.Meta.Positivity

