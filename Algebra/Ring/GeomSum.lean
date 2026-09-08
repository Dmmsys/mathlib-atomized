/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.GrindInstances

/-!
# Partial sums of geometric series in a ring

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

public section

assert_not_exists Field IsOrderedRing

open Finset MulOpposite

variable {R S : Type*}

section Semiring
variable [Semiring R] [Semiring S] {x y : R}

/-
**geom_sum_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_succ {x : R} {n : Nat} : ∑ i in range (n + 1), x ^ i = (x * ∑ i i
n range n, x ^ i) + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma geom_sum_succ {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]
/-
**geom_sum_succ'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_succ' {x : R} {n : Nat} : ∑ i in range (n + 1), x ^ i = x ^ n + ∑
 i in range n, x ^ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma geom_sum_succ' {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)
/-
**geom_sum_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_zero (x : R) : ∑ i in range 0, x ^ i = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum_zero (x : R) : ∑ i ∈ range 0, x ^ i = 0 :=
  rfl
/-
**geom_sum_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_one (x : R) : ∑ i in range 1, x ^ i = 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma geom_sum_one (x : R) : ∑ i ∈ range 1, x ^ i = 1 := by simp

@[simp]
/-
**geom_sum_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_two {x : R} : ∑ i in range 2, x ^ i = x + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `geom_sum_succ'`：geom_sum_succ' {x : R} {n : Nat} : ∑ i in range (n + 1),
 x ^ i = x ^ n + ∑ i in range n, x ^ i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma geom_sum_two {x : R} : ∑ i ∈ range 2, x ^ i = x + 1 := by simp [geom_sum_succ']

@[simp]
/-
**zero_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {n : ℕ}, ∑ i ∈ Finset.range n, 0 ^ i 
= if n = 0 then 0 else 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : R) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]
/-
**one_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_geom_sum (n : Nat) : ∑ i in range n, (1 : R) ^ i = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : R) ^ i = n := by simp
/-
**op_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_geom_sum (x : R) (n : Nat) : op (∑ i in range n, x ^ i) = ∑ i in range 
n, op x ^ i
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_geom_sum (x : R) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp

@[simp]
/-
**op_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_geom_sum (x : R) (n : Nat) : op (∑ i in range n, x ^ i) = ∑ i in range 
n, op x ^ i
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_geom_sum₂ (x y : R) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  grind
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_with_one (x : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
/-
**Commute.geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
$x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs.
-/
protected lemma Commute.geom_sum₂_mul_add {x y : R} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f : ℕ → ℕ → R := fun m i : ℕ => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i ∈ range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction n with
  | zero => rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  | succ n ih =>
    have f_last : f (n + 1) n = (x + y) ^ n := by
      dsimp only [f]
      rw [← tsub_add_eq_tsub_tsub, Nat.add_comm, tsub_self, pow_zero, mul_one]
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i := fun i hi => by
      dsimp only [f]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ' y (n - 1 - i), add_tsub_cancel_right,
        ← tsub_add_eq_tsub_tsub, add_comm 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_comm (i + 1)] at this
      rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc, add_tsub_cancel_right]
    rw [pow_succ' (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc,
      (((Commute.refl x).add_right h).pow_right n).eq, sum_congr rfl f_succ, ← mul_sum,
      pow_succ' y, mul_assoc, ← mul_add y, ih]
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_self (x : R) (n : ℕ) : ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i ∈ Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| Finset.mem_range.1 hi
    _ = #(range n) • x ^ (n - 1) := sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]
/-
**geom_sum_mul_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_mul_add (x : R) (n : Nat) : (∑ i in range n, (x + 1) ^ i) * x + 1
 = (x + 1) ^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.geom_sum₂_mul_add`：∀ {R : Type u_1} [inst : Semiring R] {x y : R
},   Commute x y → ∀ (n : ℕ), (∑ i ∈ Finset.range n, (x + y) ^ i * y ^ (n - 1 - 
i)) * x + y ^ n…
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `geom_sum₂_with_one`：geom_sum₂_with_one (x : R) (n : Nat) : ∑ i in range 
n, x ^ i * 1 ^ (n - 1 - i) = ∑ i in range n, x ^ i
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma geom_sum_mul_add (x : R) (n : ℕ) : (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this
/-
**Commute.geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Commute.geom_sum₂_comm (n : ℕ) (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using! h.pow_pow _ _

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
/-
**RingHom.map_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.map_geom_sum (x : R) (n : Nat) (f : R ->+* S) : f (∑ i in range n,
 x ^ i) = ∑ i in range n, f x ^ i
参数：x : R；n : Nat；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.map_geom_sum (x : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]
/-
**RingHom.map_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.map_geom_sum (x : R) (n : Nat) (f : R ->+* S) : f (∑ i in range n,
 x ^ i) = ∑ i in range n, f x ^ i
参数：x : R；n : Nat；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.map_geom_sum₂ (x y : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]

end Semiring

section CommSemiring
variable [CommSemiring R]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
$x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs.
-/
lemma geom_sum₂_mul_add (x y : R) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_comm (x y : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_mul_of_ge (hxy : y ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_mul_of_le (hxy : x ≤ y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert! geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  lia
/-
**geom_sum_mul_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_mul_of_one_le (hx : 1 <= x) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
参数：hx : 1 <= x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `geom_sum₂_mul_of_ge`：geom_sum₂_mul_of_ge (hxy : y <= x) (n : Nat) : (∑ i
 in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
-/
lemma geom_sum_mul_of_one_le (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by simpa using geom_sum₂_mul_of_ge hx n
/-
**geom_sum_mul_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_mul_of_le_one (hx : x <= 1) (n : Nat) : (∑ i in range n, x ^ i) *
 (1 - x) = 1 - x ^ n
参数：hx : x <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `geom_sum₂_mul_of_le`：geom_sum₂_mul_of_le (hxy : x <= y) (n : Nat) : (∑ i
 in range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n
-/
lemma geom_sum_mul_of_le_one (hx : x ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by simpa using geom_sum₂_mul_of_le hx n

end CommSemiring

section Ring
variable [Ring R] {x y : R}

@[simp]
/-
**neg_one_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_geom_sum {n : Nat} : ∑ i in range n, (-1 : R) ^ i = if Even n then
 0 else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `geom_sum_succ'`：geom_sum_succ' {x : R} {n : Nat} : ∑ i in range (n + 1),
 x ^ i = x ^ n + ∑ i in range n, x ^ i
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
lemma neg_one_geom_sum {n : ℕ} : ∑ i ∈ range n, (-1 : R) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]
/-
**Commute.geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Commute.geom_sum₂_mul (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]
/-
**Commute.mul_neg_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Commute.mul_neg_geom_sum₂ (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]
/-
**Commute.mul_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Commute.mul_geom_sum₂ (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]
/-
**Commute.sub_dvd_pow_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.sub_dvd_pow_sub_pow (h : Commute x y) (n : Nat) : x - y ∣ x ^ n - 
y ^ n
参数：h : Commute x y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用引理 `Commute.mul_geom_sum₂`：Commute.mul_geom_sum₂ (h : Commute x y) (n : Nat)
 : ((x - y) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n
-/
lemma Commute.sub_dvd_pow_sub_pow (h : Commute x y) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  Dvd.intro _ <| h.mul_geom_sum₂ _
/-
**one_sub_dvd_one_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_sub_dvd_one_sub_pow (x : R) (n : Nat) : 1 - x ∣ 1 - x ^ n
参数：x : R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Commute.sub_dvd_pow_sub_pow`：Commute.sub_dvd_pow_sub_pow (h : Commute x 
y) (n : Nat) : x - y ∣ x ^ n - y ^ n
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
-/
lemma one_sub_dvd_one_sub_pow (x : R) (n : ℕ) : 1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n
/-
**sub_one_dvd_pow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_one_dvd_pow_sub_one (x : R) (n : Nat) : x - 1 ∣ x ^ n - 1
参数：x : R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Commute.sub_dvd_pow_sub_pow`：Commute.sub_dvd_pow_sub_pow (h : Commute x 
y) (n : Nat) : x - y ∣ x ^ n - y ^ n
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
-/
lemma sub_one_dvd_pow_sub_one (x : R) (n : ℕ) : x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n
/-
**pow_one_sub_dvd_pow_mul_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_one_sub_dvd_pow_mul_sub_one (x : R) (m n : Nat) : x ^ m - 1 ∣ x ^ (m *
 n) - 1
参数：x : R；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `sub_one_dvd_pow_sub_one`：sub_one_dvd_pow_sub_one (x : R) (n : Nat) : x -
 1 ∣ x ^ n - 1
-/
lemma pow_one_sub_dvd_pow_mul_sub_one (x : R) (m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n
/-
**dvd_pow_sub_one_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_pow_sub_one_of_dvd {r : R} {a b : Nat} (h : a ∣ b) : r ^ a - 1 ∣ r ^ b
 - 1
参数：h : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_one_sub_dvd_pow_mul_sub_one`：pow_one_sub_dvd_pow_mul_sub_one (x : R)
 (m n : Nat) : x ^ m - 1 ∣ x ^ (m * n) - 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_pow_sub_one_of_dvd {r : R} {a b : ℕ} (h : a ∣ b) :
    r ^ a - 1 ∣ r ^ b - 1 := by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n
/-
**dvd_pow_pow_sub_self_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_pow_pow_sub_self_of_dvd {r : R} {p a b : Nat} (h : a ∣ b) : r ^ p ^ a 
- r ∣ r ^ p ^ b - r
参数：h : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_sub_one`：mul_sub_one (a b : α) : a * (b - 1) = a * b - a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `dvd_pow_sub_one_of_dvd`：dvd_pow_sub_one_of_dvd {r : R} {a b : Nat} (h : 
a ∣ b) : r ^ a - 1 ∣ r ^ b - 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem dvd_pow_pow_sub_self_of_dvd {r : R} {p a b : ℕ} (h : a ∣ b) :
    r ^ p ^ a - r ∣ r ^ p ^ b - r := by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀, zero_pow ha₀, zero_pow hb₀]
  have hp (c) : 1 ≤ p ^ c := Nat.pow_pos <| pos_of_ne_zero hp₀
  rw [← Nat.sub_add_cancel (hp a), ← Nat.sub_add_cancel (hp b), pow_succ', pow_succ',
    ← mul_sub_one, ← mul_sub_one]
  refine mul_dvd_mul_left _ <| dvd_pow_sub_one_of_dvd <| Int.natCast_dvd_natCast.mp ?_
  push_cast [hp a, hp b]
  exact dvd_pow_sub_one_of_dvd h
/-
**geom_sum_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) * (x - 1) = x ^ n
 - 1
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.geom_sum₂_mul`：∀ {R : Type u_1} [inst : Ring R] {x y : R},   Com
mute x y → ∀ (n : ℕ), (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y) 
= x ^ n - y…
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `geom_sum₂_with_one`：geom_sum₂_with_one (x : R) (n : Nat) : ∑ i in range 
n, x ^ i * 1 ^ (n - 1 - i) = ∑ i in range n, x ^ i
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma geom_sum_mul (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this
/-
**mul_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n, x ^ i) = x ^ n
 - 1
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
-/
lemma mul_geom_sum (x : R) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by simpa using geom_sum_mul (op x) n
/-
**geom_sum_mul_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_mul_neg (x : R) (n : Nat) : (∑ i in range n, x ^ i) * (1 - x) = 1
 - x ^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma geom_sum_mul_neg (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this
/-
**mul_neg_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_neg_geom_sum (x : R) (n : Nat) : ((1 - x) * ∑ i in range n, x ^ i) = 1
 - x ^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `geom_sum_mul_neg`：geom_sum_mul_neg (x : R) (n : Nat) : (∑ i in range n, 
x ^ i) * (1 - x) = 1 - x ^ n
-/
lemma mul_neg_geom_sum (x : R) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n
/-
**Commute.mul_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Commute.mul_geom_sum₂_Ico (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k ∈ range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k ∈ range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    lia
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]
/-
**Commute.geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Commute.geom_sum₂_succ_eq (h : Commute x y) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  lia
/-
**Commute.geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Commute.geom_sum₂_Ico_mul (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k ∈ Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k ∈ Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_pow (Commute.op h.symm) (n - 1 - k) k
    simpa [Commute, SemiconjBy] using hp
  simp only [this]
  convert! (Commute.op h).mul_geom_sum₂_Ico hmn
/-
**geom_sum_Ico_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_Ico_mul (x : R) {m n : Nat} (hmn : m <= n) : (∑ i in Finset.Ico m
 n, x ^ i) * (x - 1) = x ^ n - x ^ m
参数：x : R；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sub`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f : ℕ →
 δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k -
 ∑ k ∈ Fins…
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
-/
lemma geom_sum_Ico_mul (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]
/-
**geom_sum_Ico_mul_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：geom_sum_Ico_mul_neg (x : R) {m n : Nat} (hmn : m <= n) : (∑ i in Finset.I
co m n, x ^ i) * (1 - x) = x ^ m - x ^ n
参数：x : R；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sub`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f : ℕ →
 δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k -
 ∑ k ∈ Fins…
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `geom_sum_mul_neg`：geom_sum_mul_neg (x : R) (n : Nat) : (∑ i in range n, 
x ^ i) * (1 - x) = 1 - x ^ n
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
-/
lemma geom_sum_Ico_mul_neg (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

end Ring

section CommRing
variable [CommRing R]

/-
**pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum {x : R} {m n : Nat} :
 (x ^ m - 1) * ∑ k in range n, x ^ k = (x ^ n - 1) * ∑ k in range m, x ^ k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum {x : R} {m n : ℕ} :
    (x ^ m - 1) * ∑ k ∈ range n, x ^ k = (x ^ n - 1) * ∑ k ∈ range m, x ^ k := by
  grind [geom_sum_mul]
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_mul (x y : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n
/-
**sub_dvd_pow_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_dvd_pow_sub_pow (x y : R) (n : Nat) : x - y ∣ x ^ n - y ^ n
参数：x y : R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.sub_dvd_pow_sub_pow`：Commute.sub_dvd_pow_sub_pow (h : Commute x 
y) (n : Nat) : x - y ∣ x ^ n - y ^ n
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sub_dvd_pow_sub_pow (x y : R) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  (Commute.all x y).sub_dvd_pow_sub_pow n
/-
**Odd.add_dvd_pow_add_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.add_dvd_pow_add_pow (x y : R) {n : Nat} (h : Odd n) : x + y ∣ x ^ n + 
y ^ n
参数：x y : R；h : Odd n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
-/
lemma Odd.add_dvd_pow_add_pow (x y : R) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁
/-
**geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma geom_sum₂_succ_eq (x y : R) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) = x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq
/-
**mul_geom_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n, x ^ i) = x ^ n
 - 1
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
-/
lemma mul_geom_sum₂_Ico (x y : R) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

end CommRing

namespace Nat
variable {m k : ℕ} (x y n : ℕ)

/-
**Nat.sub_dvd_pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (x y n : ℕ), x - y ∣ x ^ n - y ^ n
参数：x y n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sub_dvd_pow_sub_pow`：sub_dvd_pow_sub_pow (x y : R) (n : Nat) : x - y ∣ x
 ^ n - y ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
-/
protected lemma sub_dvd_pow_sub_pow : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_gt y x with h | h
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)
/-
**Nat.sub_one_dvd_pow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sub_one_dvd_pow_sub_one : x - 1 ∣ x ^ n - 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.sub_dvd_pow_sub_pow`：∀ (x y n : ℕ), x - y ∣ x ^ n - y ^ n
-/
lemma sub_one_dvd_pow_sub_one : x - 1 ∣ x ^ n - 1 := by
  simpa using x.sub_dvd_pow_sub_pow 1 n
/-
**Nat.pow_sub_pow_dvd_pow_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_sub_pow_dvd_pow_sub_pow (hmk : m ∣ k) : x ^ m - y ^ m ∣ x ^ k - y ^ k
参数：hmk : m ∣ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.sub_dvd_pow_sub_pow`：∀ (x y n : ℕ), x - y ∣ x ^ n - y ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_sub_pow_dvd_pow_sub_pow (hmk : m ∣ k) : x ^ m - y ^ m ∣ x ^ k - y ^ k := by
  obtain ⟨n, rfl⟩ := hmk; simpa [pow_mul] using (x ^ m).sub_dvd_pow_sub_pow (y ^ m) n
/-
**Nat.pow_sub_one_dvd_pow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_sub_one_dvd_pow_sub_one (hmk : m ∣ k) : x ^ m - 1 ∣ x ^ k - 1
参数：hmk : m ∣ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Nat.pow_sub_pow_dvd_pow_sub_pow`：pow_sub_pow_dvd_pow_sub_pow (hmk : m ∣ 
k) : x ^ m - y ^ m ∣ x ^ k - y ^ k
-/
lemma pow_sub_one_dvd_pow_sub_one (hmk : m ∣ k) : x ^ m - 1 ∣ x ^ k - 1 := by
  simpa using pow_sub_pow_dvd_pow_sub_pow x 1 hmk
/-
**Nat._root_.Odd.nat_add_dvd_pow_add_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Odd.nat_add_dvd_pow_add_pow {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h

/-- Value of a geometric sum over the naturals. Note: see `geom_sum_mul_add` for a formulation
that avoids division and subtraction. -/
/-
**Nat.geomSum_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：geomSum_eq (hm : 2 <= m) (n : Nat) : ∑ k in range n, m ^ k = (m ^ n - 1) /
 (m - 1)
参数：hm : 2 <= m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `geom_sum_mul_add`：geom_sum_mul_add (x : R) (n : Nat) : (∑ i in range n, 
(x + 1) ^ i) * x + 1 = (x + 1) ^ n

--- 原说明 ---
Value of a geometric sum over the naturals. Note: see `geom_sum_mul_add` for a f
ormulation
that avoids division and subtraction.
-/
lemma geomSum_eq (hm : 2 ≤ m) (n : ℕ) : ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by lia : 1 ≤ m), eq_comm] using geom_sum_mul_add (m - 1) n

end Nat

