/-
Copyright (c) 2025 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jinzhao Pan
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# shifted Legendre Polynomials

In this file, we define the shifted Legendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the Legendre polynomials.

* `factorial_mul_shiftedLegendre_eq`: The analogue of Rodrigues' formula for the shifted Legendre
  polynomials;
* `shiftedLegendre_eval_symm`: The values of the shifted Legendre polynomial at `x` and `1 - x`
  differ by a factor `(-1)ⁿ`.

## Reference

* <https://en.wikipedia.org/wiki/Legendre_polynomials>

## Tags

shifted Legendre polynomials, derivative
-/

@[expose] public section

open Nat Finset

namespace Polynomial

/-- `shiftedLegendre n` is an integer polynomial for each `n : ℕ`, defined by:
`Pₙ(x) = ∑ k ∈ Finset.range (n + 1), (-1)ᵏ * choose n k * choose (n + k) n * xᵏ`
These polynomials appear in combinatorics and the theory of orthogonal polynomials. -/
/-
**Polynomial.shiftedLegendre** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：shiftedLegendre (n : Nat) : Int[X]
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`shiftedLegendre n` is an integer polynomial for each `n : ℕ`, defined by:
`Pₙ(x) = ∑ k ∈ Finset.range (n + 1), (-1)ᵏ * choose n k * choose (n + k) n * xᵏ`
These polynomials appear in combinatorics and the theory of orthogonal polynomia
ls.
-/
noncomputable def shiftedLegendre (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((-1 : ℤ) ^ k * n.choose k * (n + k).choose n) * X ^ k

set_option backward.isDefEq.respectTransparency false in
/-- The shifted Legendre polynomial multiplied by a factorial equals the higher-order derivative of
the combinatorial function `X ^ n * (1 - X) ^ n`. This is the analogue of Rodrigues' formula for
the shifted Legendre polynomials. -/
/-
**Polynomial.factorial_mul_shiftedLegendre_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：factorial_mul_shiftedLegendre_eq (n : Nat) : (n ! : Int[X]) * (shiftedLege
ndre n) = derivative^[n] (X ^ n * (1 - (X : Int[X])) ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_one_sub`：mul_one_sub (a b : α) : a * (1 - b) = a - a * b
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `pow_mul_pow_sub`：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n -
 m) = a ^ n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
The shifted Legendre polynomial multiplied by a factorial equals the higher-orde
r derivative of
the combinatorial function `X ^ n * (1 - X) ^ n`. This is the analogue of Rodrig
ues' formula for
the shifted Legendre polynomials.
-/
theorem factorial_mul_shiftedLegendre_eq (n : ℕ) : (n ! : ℤ[X]) * (shiftedLegendre n) =
    derivative^[n] (X ^ n * (1 - (X : ℤ[X])) ^ n) := by
  symm
  calc
  _ = derivative^[n] (((X : ℤ[X]) - X ^ 2) ^ n) := by
    rw [← mul_pow, mul_one_sub, ← pow_two]
  _ = derivative^[n] (∑ m ∈ range (n + 1), n.choose m • (-1) ^ m * X ^ (n + m)) := by
    congr
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw [neg_pow, pow_two, mul_pow, ← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw [Finset.mem_range] at hm
    linarith
  _ = ∑ x ∈ range (n + 1), ↑((n + x)! / x !) * C (↑(n.choose x) * (-1) ^ x) * X ^ x := by
    rw [iterate_derivative_sum]
    congr! 1 with x _
    rw [show (n.choose x • (-1) ^ x : ℤ[X]) = C (n.choose x • (-1) ^ x) by simp,
      iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
      descFactorial_eq_div (by lia), show n + x - n = x by lia]
    simp only [Int.reduceNeg, nsmul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow, Int.cast_neg, Int.cast_one, zsmul_eq_mul]
    ring
  _ = ∑ i ∈ range (n + 1), ↑n ! * C ((-1) ^ i * ↑(n.choose i) * ↑((n + i).choose n)) * X ^ i := by
    congr! 2 with x _
    rw [C_mul (b := ((n + x).choose n : ℤ)), mul_comm, mul_comm (n ! : ℤ[X]), mul_comm _ ((-1) ^ x),
      mul_assoc]
    congr 1
    rw [add_comm, add_choose]
    simp only [Int.natCast_ediv, cast_mul, eq_intCast]
    norm_cast
    rw [mul_comm, ← Nat.mul_div_assoc]
    · rw [mul_comm, Nat.mul_div_mul_right _ _ (by positivity)]
    · simp only [factorial_mul_factorial_dvd_factorial_add]
  _ = (n ! : ℤ[X]) * (shiftedLegendre n) := by simp [← mul_assoc, shiftedLegendre, mul_sum]

/-- The coefficient of the shifted Legendre polynomial at `k` is
`(-1) ^ k * (n.choose k) * (n + k).choose n`. -/
/-
**Polynomial.coeff_shiftedLegendre** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_shiftedLegendre (n k : Nat) : (shiftedLegendre n).coeff k = (-1) ^ k
 * n.choose k * (n + k).choose n
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.shiftedLegendre.eq_1`：∀ (n : ℕ),   Polynomial.shiftedLegendre
 n =     ∑ k ∈ Finset.range (n + 1), Polynomial.C ((-1) ^ k * ↑(n.choose k) * ↑(
(n + k).choose n)) * …
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The coefficient of the shifted Legendre polynomial at `k` is
`(-1) ^ k * (n.choose k) * (n + k).choose n`.
-/
theorem coeff_shiftedLegendre (n k : ℕ) :
    (shiftedLegendre n).coeff k = (-1) ^ k * n.choose k * (n + k).choose n := by
  rw [shiftedLegendre, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [choose_eq_zero_of_lt]

/-- The degree of `shiftedLegendre n` is `n`. -/
/-
**Polynomial.degree_shiftedLegendre** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (n : ℕ), (Polynomial.shiftedLegendre n).degree = ↑n
参数：n : ℕ；Polynomial.shiftedLegendre n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_shiftedLegendre`：coeff_shiftedLegendre (n k : Nat) : (s
hiftedLegendre n).coeff k = (-1) ^ k * n.choose k * (n + k).choose n
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The degree of `shiftedLegendre n` is `n`.
-/
@[simp] theorem degree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).degree = n := by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (choose_pos (show n ≤ n + n by simp)).ne']
/-
**Polynomial.natDegree_shiftedLegendre** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (n : ℕ), (Polynomial.shiftedLegendre n).natDegree = n
参数：n : ℕ；Polynomial.shiftedLegendre n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_shiftedLegendre`：∀ (n : ℕ), (Polynomial.shiftedLegendr
e n).degree = ↑n
-/
@[simp] theorem natDegree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)
/-
**Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial`。
形式化陈述：neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n : Nat) : (-1) ^ n * (
shiftedLegendre n).comp (1 - X) = shiftedLegendre n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nat_mul_inj'`：nat_mul_inj' {n : Nat} {a b : R} (h : (n : R) * a = (n : R
) * b) (w : n != 0) : a = b
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.natCast_mul_comp`：natCast_mul_comp {n : Nat} : ((n : R[X]) * 
p).comp r = n * p.comp r
· 使用定理 `Polynomial.factorial_mul_shiftedLegendre_eq`：factorial_mul_shiftedLegend
re_eq (n : Nat) : (n ! : Int[X]) * (shiftedLegendre n) = derivative^[n] (X ^ n *
 (1 - (X : Int[X])) ^ n)
· 使用定理 `Polynomial.iterate_derivative_comp_one_sub_X`：iterate_derivative_comp_on
e_sub_X (p : R[X]) (k : Nat) : derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (der
ivative^[k] p).comp (1 - X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.pow_comp`：pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) 
(n : Nat) : (p ^ n).comp q = p.comp q ^ n
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
-/
theorem neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n : ℕ) :
    (-1) ^ n * (shiftedLegendre n).comp (1 - X) = shiftedLegendre n := by
  refine nat_mul_inj' ?_ (factorial_ne_zero n)
  rw [← mul_assoc, mul_comm (n ! : ℤ[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  simp [mul_comm]

/-- The values of the Legendre polynomial at `x` and `1 - x` differ by a factor `(-1)ⁿ`. -/
/-
**Polynomial.shiftedLegendre_eval_symm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：shiftedLegendre_eval_symm (n : Nat) {R : Type*} [Ring R] (x : R) : aeval x
 (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n)
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq`：neg_one_po
w_mul_shiftedLegendre_comp_one_sub_X_eq (n : Nat) : (-1) ^ n * (shiftedLegendre 
n).comp (1 - X) = shiftedLegendre n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_neg`：aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A
) : aeval x (-p) = -aeval x p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The values of the Legendre polynomial at `x` and `1 - x` differ by a factor `(-1
)ⁿ`.
-/
lemma shiftedLegendre_eval_symm (n : ℕ) {R : Type*} [Ring R] (x : R) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n) := by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

end Polynomial

