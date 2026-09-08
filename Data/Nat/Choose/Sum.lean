/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.
-/

public section

open Nat Finset

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}

/-- A version of the **binomial theorem** for commuting elements in noncommutative semirings. -/
/-
**Commute.add_pow** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m in range (n + 1), 
x ^ m * y ^ (n - m) * n.choose m
参数：h : Commute x y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.succ_sub_succ`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Nat.succ_sub`：∀ {m n : ℕ}, n ≤ m → m.succ - n = (m - n).succ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A version of the **binomial theorem** for commuting elements in noncommutative s
emirings.
-/
theorem add_pow (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m := by
  let t : ℕ → ℕ → R := fun n m ↦ x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m ∈ range (n + 1), t n m
  have h_first : ∀ n, t n 0 = y ^ n := fun n ↦ by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, Nat.sub_zero]
  have h_last : ∀ n, t n n.succ = 0 := fun n ↦ by
    simp only [t, choose_succ_self, cast_zero, mul_zero]
  have h_middle :
      ∀ n i : ℕ, i ∈ range n.succ → (t n.succ i.succ) = x * t n i + y * t n i.succ := by
    intro n i h_mem
    have h_le : i ≤ n := le_of_lt_succ (mem_range.mp h_mem)
    dsimp only [t]
    rw [choose_succ_succ, cast_add, mul_add]
    congr 1
    · rw [pow_succ' x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, cast_zero, mul_zero, mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ' y, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  induction n with
  | zero =>
    rw [pow_zero, sum_range_succ, range_zero, sum_empty, zero_add]
    dsimp only [t]
    rw [pow_zero, pow_zero, choose_self, cast_one, mul_one, mul_one]
  | succ n ih =>
    rw [sum_range_succ', h_first, sum_congr rfl (h_middle n), sum_add_distrib, add_assoc,
      pow_succ' (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    rw [sum_range_succ', sum_range_succ, h_first, h_last, mul_zero, add_zero, _root_.pow_succ']

/-- A version of `Commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
/-
**Commute.add_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m in antidiagonal n
, n.choose m.1 • (x ^ m.1 * y ^ m.2)
参数：h : Commute x y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `Commute.add_pow` that avoids ℕ-subtraction by summing over the ant
idiagonal and
also with the binomial coefficient applied via scalar action of ℕ.
-/
theorem add_pow' (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) := by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p ↦ n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

end Commute

/-- The **binomial theorem** -/
/-
**add_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ m in range 
(n + 1), x ^ m * y ^ (n - m) * n.choose m
参数：x y : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
The **binomial theorem**
-/
theorem add_pow [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m :=
  (Commute.all x y).add_pow n

/-- A special case of the **binomial theorem** -/
/-
**sub_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_pow [CommRing R] (x y : R) (n : Nat) : (x - y) ^ n = ∑ m in range (n +
 1), (-1) ^ (m + n) * x ^ m * y ^ (n - m) * n.choose m
参数：x y : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
A special case of the **binomial theorem**
-/
theorem sub_pow [CommRing R] (x y : R) (n : ℕ) :
    (x - y) ^ n = ∑ m ∈ range (n + 1), (-1) ^ (m + n) * x ^ m * y ^ (n - m) * n.choose m := by
  rw [sub_eq_add_neg, add_pow]
  congr! 1 with m hm
  have : (-1 : R) ^ (n - m) = (-1) ^ (n + m) := by
    rw [mem_range] at hm
    simp [show n + m = n - m + 2 * m by lia, pow_add]
  rw [neg_pow, this]
  ring

namespace Nat

/-- The sum of entries in a row of Pascal's triangle -/
/-
**Nat.sum_range_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_range_choose (n : Nat) : (∑ m in range (n + 1), n.choose m) = 2 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)

--- 原说明 ---
The sum of entries in a row of Pascal's triangle
-/
theorem sum_range_choose (n : ℕ) : (∑ m ∈ range (n + 1), n.choose m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this
/-
**Nat.sum_range_choose_halfway** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_range_choose_halfway (m : Nat) : (∑ i in range (m + 1), (2 * m + 1).ch
oose i) = 4 ^ m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 75 条，此处仅展示前 30 条）
-/
theorem sum_range_choose_halfway (m : ℕ) : (∑ i ∈ range (m + 1), (2 * m + 1).choose i) = 4 ^ m :=
  have : (∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i ∈ range (m + 1), (2 * m + 1).choose i :=
    sum_congr rfl fun i hi ↦ choose_symm <| by linarith [mem_range.1 hi]
  mul_right_injective₀ two_ne_zero <|
    calc
      (2 * ∑ i ∈ range (m + 1), (2 * m + 1).choose i) =
          (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i) := by rw [two_mul, this]
      _ = (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ Ico (m + 1) (2 * m + 2), (2 * m + 1).choose i := by
        rw [range_eq_Ico, sum_Ico_reflect _ _ (by lia)]
        congr
        lia
      _ = ∑ i ∈ range (2 * m + 2), (2 * m + 1).choose i := sum_range_add_sum_Ico _ (by lia)
      _ = 2 ^ (2 * m + 1) := sum_range_choose (2 * m + 1)
      _ = 2 * 4 ^ m := by rw [pow_succ, pow_mul, mul_comm]; rfl
/-
**Nat.choose_middle_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_middle_le_pow (n : Nat) : (2 * n + 1).choose n <= 4 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.self_mem_range_succ`：self_mem_range_succ (n : Nat) : n in range (
n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sum_range_choose_halfway`：sum_range_choose_halfway (m : Nat) : (∑ i 
in range (m + 1), (2 * m + 1).choose i) = 4 ^ m
-/
theorem choose_middle_le_pow (n : ℕ) : (2 * n + 1).choose n ≤ 4 ^ n := by
  have t : (2 * n + 1).choose n ≤ ∑ i ∈ range (n + 1), (2 * n + 1).choose i :=
    single_le_sum (fun x _ ↦ by lia) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t
/-
**Nat.four_pow_le_two_mul_add_one_mul_central_binom** 是 Mathlib 中的一个定理，位于命名空间 `N
at`。
形式化陈述：four_pow_le_two_mul_add_one_mul_central_binom (n : Nat) : 4 ^ n <= (2 * n 
+ 1) * (2 * n).choose n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.choose_le_middle`：choose_le_middle (r n : Nat) : choose n r <= choos
e n (n / 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * (2 * n).choose n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m ∈ range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ ≤ ∑ _ ∈ range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

/-- **Zhu Shijie's identity** aka hockey-stick identity, version with `Icc`. -/
/-
**Nat.sum_Icc_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_Icc_choose (n k : Nat) : ∑ m in Icc k n, m.choose k = (n + 1).choose (
k + 1)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Finset.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a
 b) = Icc a b
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Finset.Ico_add_one_right_eq_Icc`：Ico_add_one_right_eq_Icc (a b : α) : Ic
o a (b + 1) = Icc a b
· 使用定理 `Nat.choose_succ_succ'`：choose_succ_succ' (n k : Nat) : choose (n + 1) (k
 + 1) = choose n k + choose n (k + 1)

--- 原说明 ---
**Zhu Shijie's identity** aka hockey-stick identity, version with `Icc`.
-/
theorem sum_Icc_choose (n k : ℕ) : ∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1) := by
  rcases lt_or_ge n k with h | h
  · rw [choose_eq_zero_of_lt (by lia), Icc_eq_empty_of_lt h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← Ico_insert_right (by lia), sum_insert (by simp), Ico_add_one_right_eq_Icc, ih,
        choose_succ_succ' (n + 1)]

/-- **Zhu Shijie's identity** aka hockey-stick identity, version with `range`.
Summing `(i + k).choose k` for `i ∈ [0, n]` gives `(n + k + 1).choose (k + 1)`.

Combinatorial interpretation: `(i + k).choose k` is the number of decompositions of `[0, i)` in
`k + 1` (possibly empty) intervals (this follows from a stars and bars description). In particular,
`(n + k + 1).choose (k + 1)` corresponds to decomposing `[0, n)` into `k + 2` intervals.
By putting away the last interval (of some length `n - i`),
we have to decompose the remaining interval `[0, i)` into `k + 1` intervals, hence the sum. -/
/-
**Nat.sum_range_add_choose** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sum_range_add_choose (n k : Nat) : ∑ i in Finset.range (n + 1), (i + k).ch
oose k = (n + k + 1).choose (k + 1)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_Icc_choose`：sum_Icc_choose (n k : Nat) : ∑ m in Icc k n, m.choos
e k = (n + 1).choose (k + 1)
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Finset.map_add_right_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用引理 `Finset.Ico_add_one_right_eq_Icc`：Ico_add_one_right_eq_Icc (a b : α) : Ic
o a (b + 1) = Icc a b
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
**Zhu Shijie's identity** aka hockey-stick identity, version with `range`.
Summing `(i + k).choose k` for `i ∈ [0, n]` gives `(n + k + 1).choose (k + 1)`.

Combinatorial interpretation: `(i + k).choose k` is the number of decompositions
 of `[0, i)` in
`k + 1` (possibly empty) intervals (this follows from a stars and bars descripti
on). In particular,
`(n + k + 1).choose (k + 1)` corresponds to decomposing `[0, n)` into `k + 2` in
tervals.
By putting away the last interval (of some length `n - i`),
we have to decompose the remaining interval `[0, i)` into `k + 1` intervals, hen
ce the sum.
-/
lemma sum_range_add_choose (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1) := by
  rw [← sum_Icc_choose, range_eq_Ico]
  convert! (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [map_add_right_Ico, zero_add, add_right_comm, Ico_add_one_right_eq_Icc]

/-- Summing `i * (n.choose i)` for `i ∈ [0, n]` gives `n * 2 ^ (n - 1)`. -/
/-
**Nat.sum_range_mul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_range_mul_choose (n : Nat) : ∑ i in Finset.range (n + 1), i * (n.choos
e i) = n * 2 ^ (n - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_flip`：∀ {M : Type u_4} [inst : AddCommMonoid M] {n : ℕ} (f : 
ℕ → M),   ∑ r ∈ Finset.range (n + 1), f (n - r) = ∑ k ∈ Finset.range (n + 1), f 
k
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Summing `i * (n.choose i)` for `i ∈ [0, n]` gives `n * 2 ^ (n - 1)`.
-/
theorem sum_range_mul_choose (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i * (n.choose i) = n * 2 ^ (n - 1) := by
  by_cases h : n = 0
  · simp [h]
  apply (mul_right_inj' two_ne_zero).1
  calc
    2 * ∑ i ∈ Finset.range (n + 1), i * n.choose i
      = ∑ i ∈ Finset.range (n + 1), (n - i) * n.choose (n - i)
        + ∑ i ∈ Finset.range (n + 1), i * n.choose i := by
      rw [two_mul, ← sum_flip]
    _ = ∑ i ∈ Finset.range (n + 1), (n - i) * n.choose i
        + ∑ i ∈ Finset.range (n + 1), i * n.choose i := by
      congr! 2 with _ h'
      rw [choose_symm (mem_range_succ_iff.mp h')]
    _ = ∑ i ∈ Finset.range (n + 1), n * n.choose i := by
      rw [← sum_add_distrib]
      congr! 1 with _ h'
      rw [← add_mul, Nat.sub_add_cancel (mem_range_succ_iff.mp h')]
    _ = n * 2 ^ n := by
      rw [← mul_sum, Nat.sum_range_choose]
    _ = 2 * (n * 2 ^ (n - 1)) := by
      rw [← mul_assoc, mul_comm 2 n, mul_assoc, mul_pow_sub_one h]
/-
**Nat.sum_range_multichoose** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sum_range_multichoose (n k : Nat) : ∑ i in Finset.range (n + 1), k.multich
oose i = (n + k).choose k
参数：n k : Nat。
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.multichoose_zero_succ`：multichoose_zero_succ (k : Nat) : multichoose
 0 (k + 1) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Nat.multichoose_zero_right`：multichoose_zero_right (n : Nat) : multichoo
se n 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sum_range_multichoose (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), k.multichoose i = (n + k).choose k := by
  cases k with
  | zero => simp [Finset.sum_range_succ']
  | succ k => grind [multichoose_eq, choose_symm_of_eq_add, sum_range_add_choose]

end Nat

/-
**Int.alternating_sum_range_choose_eq_choose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.alternating_sum_range_choose_eq_choose {n m : Nat} : (∑ k in range (m 
+ 1), ((-1) ^ k * (n + 1).choose k : Int)) = (-1) ^ m * n.choose m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
-/
theorem Int.alternating_sum_range_choose_eq_choose {n m : ℕ} :
    (∑ k ∈ range (m + 1), ((-1) ^ k * (n + 1).choose k : ℤ)) = (-1) ^ m * n.choose m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [sum_range_succ, hm, choose_succ_succ]
    grind
/-
**Int.alternating_sum_range_choose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.alternating_sum_range_choose {n : Nat} : (∑ m in range (n + 1), ((-1) 
^ m * n.choose m : Int)) = if n = 0 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.alternating_sum_range_choose_eq_choose`：Int.alternating_sum_range_ch
oose_eq_choose {n m : Nat} : (∑ k in range (m + 1), ((-1) ^ k * (n + 1).choose k
 : Int)) = (-1) ^ m * n.choose m
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem Int.alternating_sum_range_choose {n : ℕ} :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Int.alternating_sum_range_choose_eq_choose]
/-
**Int.alternating_sum_range_choose_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.alternating_sum_range_choose_of_ne {n : Nat} (h0 : n != 0) : (∑ m in r
ange (n + 1), ((-1) ^ m * n.choose m : Int)) = 0
参数：h0 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.alternating_sum_range_choose`：Int.alternating_sum_range_choose {n : 
Nat} : (∑ m in range (n + 1), ((-1) ^ m * n.choose m : Int)) = if n = 0 then 1 e
lse 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = 0 := by
  rw [Int.alternating_sum_range_choose, if_neg h0]

namespace Finset

/-
**Finset.sum_powerset_apply_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_powerset_apply_card {α β : Type*} [AddCommMonoid α] (f : Nat -> α) {x 
: Finset β} : ∑ m in x.powerset, f #m = ∑ m in range (#x + 1), (#x).choose m • f
 m
参数：f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_fiberwise_of_maps_to`：∀ {ι : Type u_1} {κ : Type u_2} {M : Ty
pe u_4} [inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ}   [inst_1 : Decid
ableEq κ] {g : ι → κ}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.powersetCard_eq_filter`：powersetCard_eq_filter {n} {s : Finset α}
 : powersetCard n s = (powerset s).filter fun x => x.card = n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
-/
theorem sum_powerset_apply_card {α β : Type*} [AddCommMonoid α] (f : ℕ → α) {x : Finset β} :
    ∑ m ∈ x.powerset, f #m = ∑ m ∈ range (#x + 1), (#x).choose m • f m := by
  trans ∑ m ∈ range (#x + 1), ∑ j ∈ x.powerset with #j = m, f #j
  · refine (sum_fiberwise_of_maps_to ?_ _).symm
    intro y hy
    rw [mem_range, Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_card hy
  · refine sum_congr rfl fun y _ ↦ ?_
    rw [← card_powersetCard, ← sum_const]
    refine sum_congr powersetCard_eq_filter.symm fun z hz ↦ ?_
    rw [(mem_powersetCard.1 hz).2]
/-
**Finset.sum_powerset_neg_one_pow_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_powerset_neg_one_pow_card {α : Type*} [DecidableEq α] {x : Finset α} :
 (∑ m in x.powerset, (-1 : Int) ^ #m) = if x = ∅ then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_powerset_apply_card`：sum_powerset_apply_card {α β : Type*} [A
ddCommMonoid α] (f : Nat -> α) {x : Finset β} : ∑ m in x.powerset, f #m = ∑ m in
 range (#x + 1), (#x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul'`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (a : α) (n :
 ℕ), n • a = a * ↑n
· 使用定理 `Int.alternating_sum_range_choose`：Int.alternating_sum_range_choose {n : 
Nat} : (∑ m in range (n + 1), ((-1) ^ m * n.choose m : Int)) = if n = 0 then 1 e
lse 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_powerset_neg_one_pow_card {α : Type*} [DecidableEq α] {x : Finset α} :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = if x = ∅ then 1 else 0 := by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]
/-
**Finset.sum_powerset_neg_one_pow_card_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset`。
形式化陈述：sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : Finset α} (h0 :
 x.Nonempty) : (∑ m in x.powerset, (-1 : Int) ^ #m) = 0
参数：h0 : x.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_powerset_neg_one_pow_card`：sum_powerset_neg_one_pow_card {α :
 Type*} [DecidableEq α] {x : Finset α} : (∑ m in x.powerset, (-1 : Int) ^ #m) = 
if x = ∅ then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
-/
theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : Finset α} (h0 : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = 0 := by
  classical
  rw [sum_powerset_neg_one_pow_card]
  exact if_neg (nonempty_iff_ne_empty.mp h0)

variable [NonAssocSemiring R]

@[to_additive sum_choose_succ_nsmul]
/-
**Finset.prod_pow_choose_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pow_choose_succ {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n :
 Nat) : (∏ i in range (n + 2), f i (n + 1 - i) ^ (n + 1).choose i) = (∏ i in ran
ge (n + 1), f i (n + 1 - i) ^ n.choose i) * ∏ i in range (n + 1), f (i + 1) (n -
 i) ^ n.choose i
参数：f : Nat -> Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem prod_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ i ∈ range (n + 2), f i (n + 1 - i) ^ (n + 1).choose i) =
      (∏ i ∈ range (n + 1), f i (n + 1 - i) ^ n.choose i) *
        ∏ i ∈ range (n + 1), f (i + 1) (n - i) ^ n.choose i := by
  have A : (∏ i ∈ range (n + 1), f (i + 1) (n - i) ^ (n.choose (i + 1))) * f 0 (n + 1) =
      ∏ i ∈ range (n + 1), f i (n + 1 - i) ^ (n.choose i) := by
    rw [prod_range_succ, prod_range_succ']; simp
  rw [prod_range_succ']
  simpa [choose_succ_succ, pow_add, prod_mul_distrib, A, mul_assoc] using mul_comm _ _

@[to_additive sum_antidiagonal_choose_succ_nsmul]
/-
**Finset.prod_antidiagonal_pow_choose_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_antidiagonal_pow_choose_succ {M : Type*} [CommMonoid M] (f : Nat -> N
at -> M) (n : Nat) : (∏ ij in antidiagonal (n + 1), f ij.1 ij.2 ^ (n + 1).choose
 ij.1) = (∏ ij in antidiagonal n, f ij.1 (ij.2 + 1) ^ n.choose ij.1) * ∏ ij in a
ntidiagonal n, f (ij.1 + 1) ij.2 ^ n.choose ij.2
参数：f : Nat -> Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk`：prod_antidiagonal_eq
_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : Nat × Nat -> M) (n : Nat) : 
∏ ij in antidiagonal n, f ij = ∏ k in ra…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_pow_choose_succ`：prod_pow_choose_succ {M : Type*} [CommMonoi
d M] (f : Nat -> Nat -> M) (n : Nat) : (∏ i in range (n + 2), f i (n + 1 - i) ^ 
(n + 1).choose i)…
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
-/
theorem prod_antidiagonal_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ ij ∈ antidiagonal (n + 1), f ij.1 ij.2 ^ (n + 1).choose ij.1) =
      (∏ ij ∈ antidiagonal n, f ij.1 (ij.2 + 1) ^ n.choose ij.1) *
        ∏ ij ∈ antidiagonal n, f (ij.1 + 1) ij.2 ^ n.choose ij.2 := by
  simp only [Nat.prod_antidiagonal_eq_prod_range_succ_mk, prod_pow_choose_succ]
  have : ∀ i ∈ range (n + 1), i ≤ n := fun i hi ↦ by simpa [Nat.lt_succ_iff] using hi
  congr 1
  · refine prod_congr rfl fun i hi ↦ ?_
    rw [tsub_add_eq_add_tsub (this _ hi)]
  · refine prod_congr rfl fun i hi ↦ ?_
    rw [choose_symm (this _ hi)]

/-- The sum of `(n+1).choose i * f i (n+1-i)` can be split into two sums at rank `n`,
respectively of `n.choose i * f i (n+1-i)` and `n.choose i * f (i+1) (n-i)`. -/
/-
**Finset.sum_choose_succ_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_choose_succ_mul (f : Nat -> Nat -> R) (n : Nat) : (∑ i in range (n + 2
), ((n + 1).choose i : R) * f i (n + 1 - i)) = (∑ i in range (n + 1), (n.choose 
i : R) * f i (n + 1 - i)) + ∑ i in range (n + 1), (n.choose i : R) * f (i + 1) (
n - i)
参数：f : Nat -> Nat -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_choose_succ_nsmul`：∀ {M : Type u_2} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) (n : ℕ),   ∑ i ∈ Finset.range (n + 2), (n + 1).choose i • f i (n
 + 1 - i) =     ∑ …

--- 原说明 ---
The sum of `(n+1).choose i * f i (n+1-i)` can be split into two sums at rank `n`
,
respectively of `n.choose i * f i (n+1-i)` and `n.choose i * f (i+1) (n-i)`.
-/
theorem sum_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ i ∈ range (n + 2), ((n + 1).choose i : R) * f i (n + 1 - i)) =
      (∑ i ∈ range (n + 1), (n.choose i : R) * f i (n + 1 - i)) +
        ∑ i ∈ range (n + 1), (n.choose i : R) * f (i + 1) (n - i) := by
  simpa only [nsmul_eq_mul] using sum_choose_succ_nsmul f n

/-- The sum along the antidiagonal of `(n+1).choose i * f i j` can be split into two sums along the
antidiagonal at rank `n`, respectively of `n.choose i * f i (j+1)` and `n.choose j * f (i+1) j`. -/
/-
**Finset.sum_antidiagonal_choose_succ_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_antidiagonal_choose_succ_mul (f : Nat -> Nat -> R) (n : Nat) : (∑ ij i
n antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2) = (∑ ij in anti
diagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)) + ∑ ij in antidiagonal n, (
n.choose ij.2 : R) * f (ij.1 + 1) ij.2
参数：f : Nat -> Nat -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_antidiagonal_choose_succ_nsmul`：∀ {M : Type u_2} [inst : AddC
ommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidiagon
al (n + 1), (n + 1).choose ij.1…

--- 原说明 ---
The sum along the antidiagonal of `(n+1).choose i * f i j` can be split into two
 sums along the
antidiagonal at rank `n`, respectively of `n.choose i * f i (j+1)` and `n.choose
 j * f (i+1) j`.
-/
theorem sum_antidiagonal_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ ij ∈ antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2) =
      (∑ ij ∈ antidiagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)) +
        ∑ ij ∈ antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2 := by
  simpa only [nsmul_eq_mul] using sum_antidiagonal_choose_succ_nsmul f n
/-
**Finset.sum_antidiagonal_choose_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_antidiagonal_choose_add (d n : Nat) : (∑ ij in antidiagonal n, (d + ij
.2).choose d) = (d + n + 1).choose (d + 1)
参数：d n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_zero`：∀ {A : Type u_1} [inst : AddCo
mmMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fins
et.HasAntidiagonal A], Finset.…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.Nat.sum_antidiagonal_succ`：sum_antidiagonal_succ {n : Nat} {f : N
at × Nat -> N} : (∑ p in antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p in anti
diagonal n, f (p.1 + 1…
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem sum_antidiagonal_choose_add (d n : ℕ) :
    (∑ ij ∈ antidiagonal n, (d + ij.2).choose d) = (d + n + 1).choose (d + 1) := by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.sum_antidiagonal_succ, hn, Nat.choose_succ_succ (d + (n + 1)), ← add_assoc]

end Finset

