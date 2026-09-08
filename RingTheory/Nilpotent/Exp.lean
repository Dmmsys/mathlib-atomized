/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.FieldSimp

/-!
# Exponential map on algebras

This file defines the exponential map `IsNilpotent.exp` on `ℚ`-algebras. The definition of
`IsNilpotent.exp a` applies to any element `a` in an algebra over `ℚ`, though it yields meaningful
(non-junk) values only when `a` is nilpotent.

The main result is `IsNilpotent.exp_add_of_commute`, which establishes the expected connection
between the additive and multiplicative structures of `A` for commuting nilpotent elements.

Additionally, `IsNilpotent.isUnit_exp` shows that if `a` is nilpotent in `A`, then
`IsNilpotent.exp a` is a unit in `A`.

Note: Although the definition works with `ℚ`-algebras, the results can be applied to any algebra
over a characteristic zero field.

## Main definitions

  * `IsNilpotent.exp`

## Tags

algebra, exponential map, nilpotent
-/

@[expose] public section

namespace IsNilpotent

variable {A : Type*} [Ring A] [Module ℚ A]

open Finset
open scoped Nat

/-- The exponential map on algebras, defined in analogy with the usual exponential series.
It provides meaningful (non-junk) values for nilpotent elements. -/
/-
**IsNilpotent.exp** 是 Mathlib 中的一个定义，位于命名空间 `IsNilpotent`。
形式化陈述：exp (a : A) : A
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponential map on algebras, defined in analogy with the usual exponential s
eries.
It provides meaningful (non-junk) values for nilpotent elements.
-/
noncomputable def exp (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i)
/-
**IsNilpotent.exp_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : exp a = ∑ i in range k, (i.
factorial : Rat)⁻¹ • (a ^ i)
参数：h : a ^ k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_add_sum_Ico`：∀ {M : Type u_3} [inst : AddCommMonoid M] 
(f : ℕ → M) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.range m, f k + ∑ k ∈ Finset.Ico m 
n, f k = ∑ k ∈ Fin…
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用引理 `pow_nilpotencyClass`：pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nil
potencyClass x) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem exp_eq_sum {a : A} {k : ℕ} (h : a ^ k = 0) :
    exp a = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) := by
  have h₁ : ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) =
      ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i) +
        ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) = 0 by
    dsimp [exp]
    rw [h₁, this, add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k, h⟩), smul_zero]
/-
**IsNilpotent.exp_smul_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_smul_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module Rat M] {
a : A} {m : M} {k : Nat} (h : (a ^ k) • m = 0) (hn : IsNilpotent a) : exp a • m 
= ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i) • m
参数：h : (a ^ k) • m = 0；hn : IsNilpotent a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNilpotent.exp_eq_sum`：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : e
xp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i)
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用引理 `pow_nilpotencyClass`：pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nil
potencyClass x) = 0
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsNilpotent.exp.eq_1`：∀ {A : Type u_1} [inst : Ring A] [inst_1 : _root_.
Module ℚ A] (a : A),   IsNilpotent.exp a = ∑ i ∈ Finset.range (nilpotencyClass a
), (↑i.fac…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_add_sum_Ico`：∀ {M : Type u_3} [inst : AddCommMonoid M] 
(f : ℕ → M) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.range m, f k + ∑ k ∈ Finset.Ico m 
n, f k = ∑ k ∈ Fin…
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `pow_sub_mul_pow`：pow_sub_mul_pow (a : M) (h : m <= n) : a ^ (n - m) * a 
^ m = a ^ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem exp_smul_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module ℚ M] {a : A} {m : M}
    {k : ℕ} (h : (a ^ k) • m = 0) (hn : IsNilpotent a) :
    exp a • m = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) • m := by
  rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
  · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)), sum_smul, smul_assoc]
  rw [exp, sum_smul, ← sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
  suffices ∑ i ∈ Ico k (nilpotencyClass a), ((i.factorial : ℚ)⁻¹ • (a ^ i)) • m = 0 by
    simp_rw [this, add_zero, smul_assoc]
  refine sum_eq_zero fun r h₂ ↦ ?_
  rw [smul_assoc, ← pow_sub_mul_pow a (mem_Ico.1 h₂).1, mul_smul, h, smul_zero, smul_zero]
/-
**IsNilpotent.exp_add_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_add_of_commute {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ :
 IsNilpotent b) : exp (a + b) = exp a * exp b
参数：h₁ : Commute a b；h₂ : IsNilpotent a；h₃ : IsNilpotent b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNilpotent.exp_eq_sum`：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : e
xp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i)
· 使用定理 `Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`：add_pow_eq_zero_o
f_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n k : Nat} (hx : x ^ m = 
0) (hy : y ^ n = 0) (h : m + n <= k + 1) : …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用引理 `Nat.cast_div`：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K
) = m / n
· 使用定理 `Nat.factorial_mul_factorial_dvd_factorial`：factorial_mul_factorial_dvd_f
actorial {n k : Nat} (hk : k <= n) : k ! * (n - k)! ∣ n !
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 137 条，此处仅展示前 30 条）
-/
theorem exp_add_of_commute {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp (a + b) = exp a * exp b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [exp_eq_sum (k := 2 * N + 1)
    (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ (by lia)),
    exp_eq_sum h₄, exp_eq_sum h₅]
  set R2N := range (2 * N + 1) with hR2N
  set RN := range (N + 1) with hRN
  have s₁ := by
    calc ∑ i ∈ R2N, (i ! : ℚ)⁻¹ • (a + b) ^ i
        = ∑ i ∈ R2N, (i ! : ℚ)⁻¹ • ∑ j ∈ range (i + 1), a ^ j * b ^ (i - j) * i.choose j := ?_
      _ = ∑ i ∈ R2N, (∑ j ∈ range (i + 1),
            ((j ! : ℚ)⁻¹ * ((i - j) ! : ℚ)⁻¹) • (a ^ j * b ^ (i - j))) := ?_
      _ = ∑ ij ∈ R2N ×ˢ R2N with ij.1 + ij.2 ≤ 2 * N,
            ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · refine sum_congr rfl fun i _ ↦ ?_
      rw [Commute.add_pow h₁ i]
    · simp_rw [smul_sum]
      refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
      simp only [mem_range] at hi hj
      replace hj := Nat.le_of_lt_succ hj
      suffices (i ! : ℚ)⁻¹ * (i.choose j) = ((j ! : ℚ)⁻¹ * ((i - j)! : ℚ)⁻¹) by
        rw [← Nat.cast_commute (i.choose j), ← this, ← mul_smul_comm, ← nsmul_eq_mul,
          mul_smul, ← smul_assoc, smul_comm, smul_assoc]
        norm_cast
      rw [Nat.choose_eq_factorial_div_factorial hj,
        Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hj) (by positivity)]
      simp [field]
    · rw [hR2N, sum_sigma']
      apply sum_bij (fun ⟨i, j⟩ _ ↦ (j, i - j))
      · simp only [mem_sigma, mem_range, mem_filter, mem_product, and_imp]
        lia
      · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
        rintro ⟨x₁, y₁⟩ - h₁ ⟨x₂, y₂⟩ - h₂ h₃ h₄
        simp_all
        lia
      · simp only [mem_filter, mem_product, mem_range, mem_sigma, exists_prop, Sigma.exists,
          and_imp, Prod.forall, Prod.mk.injEq]
        exact fun x y _ _ _ ↦ ⟨x + y, x, by lia⟩
      · simp only [mem_sigma, mem_range, implies_true]
  have z₁ : ∑ ij ∈ R2N ×ˢ R2N with ¬ ij.1 + ij.2 ≤ 2 * N,
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
      rw [mem_filter] at hi
      cases le_or_gt (N + 1) i.1 with
        | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
        | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅, mul_zero, smul_zero]
  have split₁ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij ↦ ij.1 + ij.2 ≤ 2 * N)
    (fun ij ↦ ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₁, add_zero] at split₁
  rw [split₁] at s₁
  have z₂ : ∑ ij ∈ R2N ×ˢ R2N with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N),
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
    simp only [not_and, not_le, mem_filter] at hi
    cases le_or_gt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅, mul_zero, smul_zero]
  have split₂ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij ↦ ij.1 ≤ N ∧ ij.2 ≤ N)
    (fun ij ↦ ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₂, add_zero] at split₂
  rw [← split₂] at s₁
  have restrict : ∑ ij ∈ R2N ×ˢ R2N with ij.1 ≤ N ∧ ij.2 ≤ N,
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij ∈ RN ×ˢ RN, ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    apply sum_congr
    · ext x
      simp only [mem_filter, mem_product, mem_range, hR2N, hRN]
      lia
    · tauto
  rw [restrict] at s₁
  have s₂ := by
    calc (∑ i ∈ RN, (i ! : ℚ)⁻¹ • a ^ i) * ∑ i ∈ RN, (i ! : ℚ)⁻¹ • b ^ i
        = ∑ i ∈ RN, ∑ j ∈ RN, ((i ! : ℚ)⁻¹ * (j ! : ℚ)⁻¹) • (a ^ i * b ^ j) := ?_
      _ = ∑ ij ∈ RN ×ˢ RN, ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · rw [sum_mul_sum]
      refine sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    · rw [sum_sigma']
      apply sum_bijective (fun ⟨i, j⟩ ↦ (i, j))
      · exact ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h ↦ by cases h; rfl, fun ⟨i, j⟩ ↦ ⟨⟨i, j⟩, rfl⟩⟩
      · simp only [mem_sigma, mem_product, implies_true]
      · simp only [implies_true]
  rwa [s₂.symm] at s₁

@[simp]
/-
**IsNilpotent.exp_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_zero : exp (0 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNilpotent.exp_eq_sum`：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : e
xp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_zero :
    exp (0 : A) = 1 := by
  simp [exp_eq_sum (pow_one 0)]
/-
**IsNilpotent.exp_mul_exp_neg_self** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_mul_exp_neg_self {a : A} (h : IsNilpotent a) : exp a * exp (-a) = 1
参数：h : IsNilpotent a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNilpotent.exp_add_of_commute`：exp_add_of_commute {a b : A} (h₁ : Commu
te a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) : exp (a + b) = exp a * exp b
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `IsNilpotent.neg`：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpot
ent (-x)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `IsNilpotent.exp_zero`：exp_zero : exp (0 : A) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_mul_exp_neg_self {a : A} (h : IsNilpotent a) :
    exp a * exp (-a) = 1 := by
  simp [← exp_add_of_commute (Commute.neg_right rfl) h h.neg]
/-
**IsNilpotent.exp_neg_mul_exp_self** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_neg_mul_exp_self {a : A} (h : IsNilpotent a) : exp (-a) * exp a = 1
参数：h : IsNilpotent a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNilpotent.exp_add_of_commute`：exp_add_of_commute {a b : A} (h₁ : Commu
te a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) : exp (a + b) = exp a * exp b
· 使用定理 `Commute.neg_left`：neg_left : Commute a b -> Commute (-a) b
· 使用定理 `IsNilpotent.neg`：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpot
ent (-x)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `IsNilpotent.exp_zero`：exp_zero : exp (0 : A) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_neg_mul_exp_self {a : A} (h : IsNilpotent a) :
    exp (-a) * exp a = 1 := by
  simp [← exp_add_of_commute (Commute.neg_left rfl) h.neg h]
/-
**IsNilpotent.isUnit_exp** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：isUnit_exp {a : A} (h : IsNilpotent a) : IsUnit (exp a)
参数：h : IsNilpotent a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `IsNilpotent.exp_mul_exp_neg_self`：exp_mul_exp_neg_self {a : A} (h : IsNi
lpotent a) : exp a * exp (-a) = 1
· 使用定理 `IsNilpotent.exp_neg_mul_exp_self`：exp_neg_mul_exp_self {a : A} (h : IsNi
lpotent a) : exp (-a) * exp a = 1
-/
theorem isUnit_exp {a : A} (h : IsNilpotent a) : IsUnit (exp a) := by
  apply isUnit_iff_exists.2
  use exp (-a)
  exact ⟨exp_mul_exp_neg_self h, exp_neg_mul_exp_self h⟩
/-
**IsNilpotent.map_exp** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：map_exp {B F : Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Modul
e Rat B] {a : A} (ha : IsNilpotent a) (f : F) : f (exp a) = exp (f a)
参数：ha : IsNilpotent a；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsNilpotent.exp_eq_sum`：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : e
xp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
theorem map_exp {B F : Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module ℚ B]
    {a : A} (ha : IsNilpotent a) (f : F) :
    f (exp a) = exp (f a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (f a) ^ k = 0 := by simp [← map_pow, hk]
  simp [exp_eq_sum hk, exp_eq_sum hk', map_rat_smul]
/-
**IsNilpotent.exp_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：exp_smul {G : Type*} [Monoid G] [MulSemiringAction G A] (g : G) {a : A} (h
a : IsNilpotent a) : exp (g • a) = g • exp a
参数：g : G；ha : IsNilpotent a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNilpotent.map_exp`：map_exp {B F : Type*} [Ring B] [FunLike F A B] [Rin
gHomClass F A B] [Module Rat B] {a : A} (ha : IsNilpotent a) (f : F) : f (exp a)
 = exp (f…
-/
theorem exp_smul {G : Type*} [Monoid G] [MulSemiringAction G A]
    (g : G) {a : A} (ha : IsNilpotent a) :
    exp (g • a) = g • exp a :=
  (map_exp ha (MulSemiringAction.toRingHom G A g)).symm
/-
**IsNilpotent.isNilpotent_exp_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsNilpotent`。
形式化陈述：isNilpotent_exp_sub_one {a : A} (ha : IsNilpotent a) : IsNilpotent (exp a 
- 1)
参数：ha : IsNilpotent a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNilpotent.exp.eq_1`：∀ {A : Type u_1} [inst : Ring A] [inst_1 : _root_.
Module ℚ A] (a : A),   IsNilpotent.exp a = ∑ i ∈ Finset.range (nilpotencyClass a
), (↑i.fac…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_nilpotencyClass_iff`：∀ {R : Type u_1} {x : R} [inst : MonoidWithZero
 R] [Nontrivial R], 0 < nilpotencyClass x ↔ IsNilpotent x
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Commute.isNilpotent_sum`：∀ {R : Type u_1} [inst : Semiring R] {ι : Type 
u_3} {s : Finset ι} {f : ι → R},   (∀ i ∈ s, IsNilpotent (f i)) → (∀ (i j : ι), 
i ∈ s → j ∈ s…
· 使用引理 `IsNilpotent.smul`：IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S]
 [MulActionWithZero R S] [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha
 : IsN…
· 使用引理 `IsNilpotent.pow_of_pos`：IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWi
thZero S] {x : S} (hx : IsNilpotent x) (hn : n != 0) : IsNilpotent (x ^ n)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 35 条，此处仅展示前 30 条）
-/
theorem isNilpotent_exp_sub_one {a : A} (ha : IsNilpotent a) : IsNilpotent (exp a - 1) := by
  nontriviality A
  rw [exp, ← Nat.sub_add_cancel (pos_nilpotencyClass_iff.2 ha), Finset.sum_range_succ']
  simp only [Nat.succ_eq_add_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul, add_sub_cancel_right]
  apply Commute.isNilpotent_sum fun _ _ ↦ smul (pow_of_pos ha <| by positivity) _
  simp [Nat.factorial_ne_zero]

end IsNilpotent

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module ℚ M] [Module ℚ N]

open IsNilpotent TensorProduct

/-
**Module.End.commute_exp_left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：commute_exp_left_of_commute {fM : Module.End R M} {fN : Module.End R N} {g
 : M ->ₗ[R] N} (hfM : IsNilpotent fM) (hfN : IsNilpotent fN) (h : fN ∘ₗ g = g ∘ₗ
 fM) : exp fN ∘ₗ g = g ∘ₗ exp fM
参数：hfM : IsNilpotent fM；hfN : IsNilpotent fN；h : fN ∘ₗ g = g ∘ₗ fM。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `IsNilpotent.exp_eq_sum`：exp_eq_sum {a : A} {k : Nat} (h : a ^ k = 0) : e
xp a = ∑ i in range k, (i.factorial : Rat)⁻¹ • (a ^ i)
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commute_exp_left_of_commute
    {fM : Module.End R M} {fN : Module.End R N} {g : M →ₗ[R] N}
    (hfM : IsNilpotent fM)
    (hfN : IsNilpotent fN)
    (h : fN ∘ₗ g = g ∘ₗ fM) :
    exp fN ∘ₗ g = g ∘ₗ exp fM := by
  ext m
  obtain ⟨k, hfM⟩ := hfM
  obtain ⟨l, hfN⟩ := hfN
  let kl := max k l
  replace hfM : fM ^ kl = 0 := pow_eq_zero_of_le (by omega) hfM
  replace hfN : fN ^ kl = 0 := pow_eq_zero_of_le (by omega) hfN
  have (i : ℕ) : (fN ^ i) (g m) = g ((fM ^ i) m) := by
    simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) m
  simp [exp_eq_sum hfM, exp_eq_sum hfN, this, map_rat_smul]
/-
**Module.End.exp_mul_of_derivation** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：exp_mul_of_derivation (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B]
 [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [Module Rat B] (D : B 
->ₗ[R] B) (h_der : forall x y, D (x * y) = x * D y + (D x) * y) (h_nil : IsNilpo
tent D) (x y : B) : exp D (x * y) = (exp D x) * (exp D y)
参数：R B : Type*；D : B ->ₗ[R] B；h_der : forall x y, D (x * y) = x * D y + (D x) * 
y；h_nil : IsNilpotent D；x y : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.End.commute_exp_left_of_commute`：commute_exp_left_of_commute {fM 
: Module.End R M} {fN : Module.End R N} {g : M ->ₗ[R] N} (hfM : IsNilpotent fM) 
(hfN : IsNilpotent fN) (h : …
· 使用定理 `Commute.isNilpotent_add`：isNilpotent_add (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y)
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNilpotent.map_exp`：map_exp {B F : Type*} [Ring B] [FunLike F A B] [Rin
gHomClass F A B] [Module Rat B] {a : A} (ha : IsNilpotent a) (f : F) : f (exp a)
 = exp (f…
· 使用定理 `IsNilpotent.exp_add_of_commute`：exp_add_of_commute {a b : A} (h₁ : Commu
te a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) : exp (a + b) = exp a * exp b
-/
theorem exp_mul_of_derivation (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B]
    [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [Module ℚ B]
    (D : B →ₗ[R] B) (h_der : ∀ x y, D (x * y) = x * D y + (D x) * y)
    (h_nil : IsNilpotent D) (x y : B) :
    exp D (x * y) = (exp D x) * (exp D y) := by
  let DL : Module.End R (B ⊗[R] B) := D.lTensor B
  let DR : Module.End R (B ⊗[R] B) := D.rTensor B
  have h_nilL : IsNilpotent DL := h_nil.map <| lTensorAlgHom R B B
  have h_nilR : IsNilpotent DR := h_nil.map <| rTensorAlgHom R B B
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m : B ⊗[R] B →ₗ[R] B := LinearMap.mul' R B with hm
  have h₁ : exp D (x * y) = m (exp (DL + DR) (x ⊗ₜ[R] y)) := by
    suffices exp D ∘ₗ m = m ∘ₗ exp (DL + DR) by simpa using! LinearMap.congr_fun this (x ⊗ₜ[R] y)
    apply commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h_nil
    ext
    simp [DL, DR, hm, h_der]
  have h₂ : exp DL = (exp D).lTensor B := (h_nil.map_exp (lTensorAlgHom R B B)).symm
  have h₃ : exp DR = (exp D).rTensor B := (h_nil.map_exp (rTensorAlgHom R B B)).symm
  simp [h₁, exp_add_of_commute h_comm h_nilL h_nilR, h₂, h₃, hm]

end Module.End

