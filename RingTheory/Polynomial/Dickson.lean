/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `Polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `Polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `Polynomial.dickson_one_one_charP`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `LinearRecurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

@[expose] public section


noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (k : ℕ) (a : R)

/-- `dickson` is the `n`-th (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
/-
**Polynomial.dickson** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → ℕ → R → ℕ → Polynomial R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dickson` is the `n`-th (generalised) Dickson polynomial of the `k`-th kind asso
ciated to the
element `a ∈ R`.
-/
noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n

@[simp]
/-
**Polynomial.dickson_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_zero : dickson k a 0 = 3 - k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl

@[simp]
/-
**Polynomial.dickson_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_one : dickson k a 1 = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dickson_one : dickson k a 1 = X :=
  rfl
/-
**Polynomial.dickson_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X]) := by
  simp only [dickson, sq]

@[simp]
/-
**Polynomial.dickson_add_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_add_two (n : Nat) : dickson k a (n + 2) = X * dickson k a (n + 1) 
- C a * dickson k a n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.dickson.eq_3`：∀ {R : Type u_1} [inst : CommRing R] (k : ℕ) (a
 : R) (n : ℕ),   Polynomial.dickson k a n.succ.succ =     Polynomial.X * Polynom
ial.dickson k…
-/
theorem dickson_add_two (n : ℕ) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]
/-
**Polynomial.dickson_of_two_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_of_two_le {n : Nat} (h : 2 <= n) : dickson k a n = X * dickson k a
 (n - 1) - C a * dickson k a (n - 2)
参数：h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.dickson_add_two`：dickson_add_two (n : Nat) : dickson k a (n +
 2) = X * dickson k a (n + 1) - C a * dickson k a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n

variable {k a}
/-
**Polynomial.map_dickson** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{k : ℕ} {a : R} (f : R →+* S) (n : ℕ),   Polynomial.map f (Polynomial.dickson k 
a n) = Polynomial.dickson k (f a) n
参数：f : R →+* S；n : ℕ；Polynomial.dickson k a n；f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp_rw [dickson_zero, Polynomial.map_sub, Polynomial.map_natCast, Polynomial.map_ofNat]
  | 1 => by simp only [dickson_one, map_X]
  | n + 2 => by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    rw [map_dickson f n, map_dickson f (n + 1)]

@[simp]
/-
**Polynomial.dickson_two_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (n : ℕ), Polynomial.dickson 2 0 n = P
olynomial.X ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    norm_num
  | 1 => by simp only [dickson_one, pow_one]
  | n + 2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero (n + 1), pow_add X (n + 1) 1, mul_comm, pow_one]

section Dickson

/-!

### A Lambda structure on `ℤ[X]`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `ℤ[X]` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `ℤ[X]` in terms of binomial polynomials.

-/

/-
**Polynomial.dickson_one_one_eval_add_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) : forall n, (dickso
n 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n | 0 => by simp only [pow_zero, dicks
on_zero]; norm_num | 1 => by simp only [eval_X, dickson_one, pow_one] | n + 2 =>
 by simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv x y h _, eval_X,
 dickson_add_two, C_1, eval_one] conv_lhs => simp only [pow_succ', add_mul, mul_
add, h, ← mul_assoc, mul_comm y x, one_mul] ring  variable (R)  private theorem 
two_mul_C_half_eq_one [Inv
参数：x y : R；h : x * y = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### A Lambda structure on `ℤ[X]`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `ℤ[X]` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `ℤ[X]` in terms of binomial polyn
omials.
-/
theorem dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
    ∀ n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by
    simp only [pow_zero, dickson_zero]; norm_num
  | 1 => by simp only [eval_X, dickson_one, pow_one]
  | n + 2 => by
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv x y h _, eval_X, dickson_add_two,
      C_1, eval_one]
    conv_lhs => simp only [pow_succ', add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul]
    ring

variable (R)
/-
**Polynomial.two_mul_C_half_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem two_mul_C_half_eq_one [Invertible (2 : R)] : 2 * C (⅟2 : R) = 1 := by
  rw [two_mul, ← C_add, invOf_two_add_invOf_two, C_1]
/-
**Polynomial.C_half_mul_two_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem C_half_mul_two_eq_one [Invertible (2 : R)] : C (⅟2 : R) * 2 = 1 := by
  rw [mul_comm, two_mul_C_half_eq_one]
/-
**Polynomial.dickson_one_one_eq_chebyshev_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] (n : ℕ), Polynomial.dickson 1 1 n = P
olynomial.Chebyshev.C R ↑n
参数：R : Type u_1；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dickson_one_one_eq_chebyshev_C : ∀ n, dickson 1 (1 : R) n = Chebyshev.C R n
  | 0 => by
    simp only [dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, Nat.cast_one, Chebyshev.C_one]
  | n + 2 => by
    rw [dickson_add_two, C_1, Nat.cast_add, Nat.cast_two, Chebyshev.C_add_two,
      dickson_one_one_eq_chebyshev_C (n + 1), dickson_one_one_eq_chebyshev_C n]
    push_cast
    ring
/-
**Polynomial.dickson_one_one_eq_chebyshev_T** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] (n : Nat) : dickson 1 
(1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟2) * X)
参数：2 : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.dickson_one_one_eq_chebyshev_C`：∀ (R : Type u_1) [inst : Comm
Ring R] (n : ℕ), Polynomial.dickson 1 1 n = Polynomial.Chebyshev.C R ↑n
· 使用定理 `Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X`：C_eq_two_mul_T_comp
_half_mul_X [Invertible (2 : R)] (n : Int) : C R n = 2 * (T R n).comp (Polynomia
l.C ⅟2 * X)
-/
theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] (n : ℕ) :
    dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟2) * X) :=
  (dickson_one_one_eq_chebyshev_C R n).trans (Chebyshev.C_eq_two_mul_T_comp_half_mul_X R n)
/-
**Polynomial.chebyshev_T_eq_dickson_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : Nat) : Chebyshev.
T R n = C (⅟2) * (dickson 1 1 n).comp (2 * X)
参数：2 : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Chebyshev.T_eq_half_mul_C_comp_two_mul_X`：T_eq_half_mul_C_com
p_two_mul_X [Invertible (2 : R)] (n : Int) : T R n = Polynomial.C ⅟2 * (C R n).c
omp (2 * X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.dickson_one_one_eq_chebyshev_C`：∀ (R : Type u_1) [inst : Comm
Ring R] (n : ℕ), Polynomial.dickson 1 1 n = Polynomial.Chebyshev.C R ↑n
-/
theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
    Chebyshev.T R n = C (⅟2) * (dickson 1 1 n).comp (2 * X) :=
  dickson_one_one_eq_chebyshev_C R n ▸ Chebyshev.T_eq_half_mul_C_comp_two_mul_X R n
/-
**Polynomial.dickson_two_one_eq_chebyshev_S** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] (n : ℕ), Polynomial.dickson 2 1 n = P
olynomial.Chebyshev.S R ↑n
参数：R : Type u_1；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dickson_two_one_eq_chebyshev_S : ∀ n, dickson 2 (1 : R) n = Chebyshev.S R n
  | 0 => by
    simp only [dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, Nat.cast_one, Chebyshev.S_one]
  | n + 2 => by
    rw [dickson_add_two, C_1, Nat.cast_add, Nat.cast_two, Chebyshev.S_add_two,
      dickson_two_one_eq_chebyshev_S (n + 1), dickson_two_one_eq_chebyshev_S n]
    push_cast
    ring
/-
**Polynomial.dickson_two_one_eq_chebyshev_U** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：dickson_two_one_eq_chebyshev_U [Invertible (2 : R)] (n : Nat) : dickson 2 
(1 : R) n = (Chebyshev.U R n).comp (C (⅟2) * X)
参数：2 : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.dickson_two_one_eq_chebyshev_S`：∀ (R : Type u_1) [inst : Comm
Ring R] (n : ℕ), Polynomial.dickson 2 1 n = Polynomial.Chebyshev.S R ↑n
· 使用定理 `Polynomial.Chebyshev.S_eq_U_comp_half_mul_X`：S_eq_U_comp_half_mul_X [Inv
ertible (2 : R)] (n : Int) : S R n = (U R n).comp (Polynomial.C ⅟2 * X)
-/
theorem dickson_two_one_eq_chebyshev_U [Invertible (2 : R)] (n : ℕ) :
    dickson 2 (1 : R) n = (Chebyshev.U R n).comp (C (⅟2) * X) :=
  (dickson_two_one_eq_chebyshev_S R n).trans (Chebyshev.S_eq_U_comp_half_mul_X R n)
/-
**Polynomial.chebyshev_U_eq_dickson_two_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：chebyshev_U_eq_dickson_two_one (n : Nat) : Chebyshev.U R n = (dickson 2 (1
 : R) n).comp (2 * X)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Chebyshev.S_comp_two_mul_X`：S_comp_two_mul_X (n : Int) : (S R
 n).comp (2 * X) = U R n
· 使用定理 `Polynomial.dickson_two_one_eq_chebyshev_S`：∀ (R : Type u_1) [inst : Comm
Ring R] (n : ℕ), Polynomial.dickson 2 1 n = Polynomial.Chebyshev.S R ↑n
-/
theorem chebyshev_U_eq_dickson_two_one (n : ℕ) :
    Chebyshev.U R n = (dickson 2 (1 : R) n).comp (2 * X) :=
  dickson_two_one_eq_chebyshev_S R n ▸ (Chebyshev.S_comp_two_mul_X R n).symm

/-- The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
/-
**Polynomial.dickson_one_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_one_one_mul (m n : Nat) : dickson 1 (1 : R) (m * n) = (dickson 1 1
 m).comp (dickson 1 1 n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_dickson`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing
 R] [inst_1 : CommRing S] {k : ℕ} {a : R} (f : R →+* S) (n : ℕ),   Polynomial.ma
p f (Polynom…
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.dickson_one_one_eq_chebyshev_T`：dickson_one_one_eq_chebyshev_
T [Invertible (2 : R)] (n : Nat) : dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).c
omp (C (⅟2) * X)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Polynomial.Chebyshev.T_mul`：T_mul (m n : Int) : T R (m * n) = (T R m).co
mp (T R n)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.eval₂_congr`：eval₂_congr {R S : Type*} [Semiring R] [Semiring
 S] {f g : R ->+* S} {s t : S} {φ ψ : R[X]} : f = g -> s = t -> φ = ψ -> eval₂ f
 s φ = eval₂…
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.Dickson.0.Polynomial.C_half_mul_t
wo_eq_one`：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : Invertible 2], Polynom
ial.C ⅟2 * 2 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The `(m * n)`-th Dickson polynomial of the first kind is the composition of the 
`m`-th and
`n`-th.
-/
theorem dickson_one_one_mul (m n : ℕ) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) := by
  have h : (1 : R) = Int.castRingHom R 1 := by simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_one_one_eq_chebyshev_T,
    Nat.cast_mul, Chebyshev.T_mul, two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  apply eval₂_congr rfl rfl
  rw [comp_assoc]
  apply eval₂_congr rfl _ rfl
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, C_half_mul_two_eq_one, one_mul]
/-
**Polynomial.dickson_one_one_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_one_one_comp_comm (m n : Nat) : (dickson 1 (1 : R) m).comp (dickso
n 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.dickson_one_one_mul`：dickson_one_one_mul (m n : Nat) : dickso
n 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dickson_one_one_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul, mul_comm, dickson_one_one_mul]
/-
**Polynomial.dickson_one_one_zmod_p** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_one_one_zmod_p (p : Nat) [Fact p.Prime] : dickson 1 (1 : ZMod p) p
 = X ^ p
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.charP_iff_charP`：RingHom.charP_iff_charP {K L : Type*} [Division
Ring K] [NonAssocSemiring L] [Nontrivial L] (f : K ->+* L) (p : Nat) : CharP K p
 ↔ CharP L p
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.map_dickson`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing
 R] [inst_1 : CommRing S] {k : ℕ} {a : R} (f : R →+* S) (n : ℕ),   Polynomial.ma
p f (Polynom…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eq_of_infinite_eval_eq`：eq_of_infinite_eval_eq (p q : R[X]) (
h : Set.Infinite { x | eval x p = eval x q }) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.cast_one'`：cast_one' : (cast (1 : ZMod n) : R) = 1
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.dickson_one_one_eval_add_inv`：dickson_one_one_eval_add_inv (x
 y : R) (h : x * y = 1) : forall n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n +
 y ^ n | 0 => by simp only [p…
（共 106 条，此处仅展示前 30 条）
-/
theorem dickson_one_one_zmod_p (p : ℕ) [Fact p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p := by
  -- Recall that `dickson_one_one_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `Polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type) (_ : Field K), ∃ _ : CharP K p, Infinite K := by
    let K := FractionRing (Polynomial (ZMod p))
    let f : ZMod p →+* K := (algebraMap _ (FractionRing _)).comp C
    have : CharP K p := by
      rw [← f.charP_iff_charP]
      infer_instance
    have : Infinite K :=
      Infinite.of_injective (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        (IsFractionRing.injective _ _)
    refine ⟨K, ?_, ?_, ?_⟩ <;> infer_instance
  apply map_injective (ZMod.castHom (dvd_refl p) K) (RingHom.injective _)
  rw [map_dickson, Polynomial.map_pow, map_X]
  apply eq_of_infinite_eval_eq
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @Set.Infinite.mono _ { x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0 }
  · rintro _ ⟨x, rfl, hx⟩
    simp only [eval_X, eval_pow, Set.mem_ofPred_eq, ZMod.cast_one', add_pow_char,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ hx), ZMod.castHom_apply]
  -- Now we need to show that the set of such `x` is infinite.
  -- If the set is finite, then we will show that `K` is also finite.
  · intro h
    rw [← Set.infinite_univ_iff] at H
    apply H
    -- To each `x` of the form `x = y + y⁻¹`
    -- we `bind` the set of `y` that solve the equation `x = y + y⁻¹`.
    -- For every `x`, that set is finite (since it is governed by a quadratic equation).
    -- For the moment, we claim that all these sets together cover `K`.
    suffices (Set.univ : Set K) =
        ⋃ x ∈ { x : K | ∃ y : K, x = y + y⁻¹ ∧ y ≠ 0 }, { y | x = y + y⁻¹ ∨ y = 0 }  by
      rw [this]
      clear this
      refine h.biUnion fun x _ => ?_
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : K[X] := X ^ 2 - C x * X + 1
      have hφ : φ ≠ 0 := by
        intro H
        have : φ.eval 0 = 0 := by rw [H, eval_zero]
        simpa [φ, eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add, eval_mul,
          mul_zero, sq, zero_add, one_ne_zero]
      classical
        convert! (φ.roots ∪ {0}).toFinset.finite_toSet using 1
        ext1 y
        simp only [φ, Multiset.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_union,
          mem_roots hφ, IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          Multiset.mem_singleton]
        by_cases hy : y = 0
        · simp only [hy, or_true]
        apply or_congr _ Iff.rfl
        rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel₀ hy]
        apply eq_iff_eq_cancel_right.mpr
        ring
    -- Finally, we prove the claim that our finite union of finite sets covers all of `K`.
    apply (Set.eq_univ_of_forall _).symm
    intro x
    simp only [exists_prop, Set.mem_iUnion, Ne, Set.mem_ofPred_eq]
    by_cases hx : x = 0
    · simp only [hx, and_true, inv_zero, or_true]
      exact ⟨_, 1, rfl, one_ne_zero⟩
    · simp only [hx, or_false, exists_eq_right]
      exact ⟨_, rfl, hx⟩
/-
**Polynomial.dickson_one_one_charP** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dickson_one_one_charP (p : Nat) [Fact p.Prime] [CharP R p] : dickson 1 (1 
: R) p = X ^ p
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_one'`：cast_one' : (cast (1 : ZMod n) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_dickson`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing
 R] [inst_1 : CommRing S] {k : ℕ} {a : R} (f : R →+* S) (n : ℕ),   Polynomial.ma
p f (Polynom…
· 使用定理 `Polynomial.dickson_one_one_zmod_p`：dickson_one_one_zmod_p (p : Nat) [Fac
t p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
-/
theorem dickson_one_one_charP (p : ℕ) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p := by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h, ← map_dickson (ZMod.castHom (dvd_refl p) R), dickson_one_one_zmod_p, Polynomial.map_pow,
    map_X]

end Dickson

end Polynomial

