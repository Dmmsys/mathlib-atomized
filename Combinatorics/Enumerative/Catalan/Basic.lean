/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Central

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Field

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
  `catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_centralBinom_div`: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = Nat.centralBinom n / (n + 1)`.

## Implementation details

The proof of `catalan_eq_centralBinom_div` follows https://math.stackexchange.com/questions/3304415

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Provide the many variants of Catalan numbers, e.g. associated to complex reflection groups,
  Fuss-Catalan, etc.

-/

@[expose] public section


open Finset

/-- The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)` -/
/-
**catalan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`
-/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ i : Fin n.succ,
      catalan i * catalan (n - i)

@[simp]
/-
**catalan_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_zero : catalan 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan.eq_1`：catalan 0 = 1
-/
theorem catalan_zero : catalan 0 = 1 := by rw [catalan]
/-
**catalan_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_succ (n : Nat) : catalan (n + 1) = ∑ i : Fin n.succ, catalan i * c
atalan (n - i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan.eq_2`：∀ (n : ℕ), catalan n.succ = ∑ i, catalan ↑i * catalan (n -
 ↑i)
-/
theorem catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i) := by
  rw [catalan]
/-
**catalan_succ'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_succ' (n : Nat) : catalan (n + 1) = ∑ ij in antidiagonal n, catala
n ij.1 * catalan ij.2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan_succ`：catalan_succ (n : Nat) : catalan (n + 1) = ∑ i : Fin n.suc
c, catalan i * catalan (n - i)
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
-/
theorem catalan_succ' (n : ℕ) :
    catalan (n + 1) = ∑ ij ∈ antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [catalan_succ, Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n,
    sum_range]

@[simp]
/-
**catalan_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_one : catalan 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan_succ`：catalan_succ (n : Nat) : catalan (n + 1) = ∑ i : Fin n.suc
c, catalan i * catalan (n - i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `catalan_zero`：catalan_zero : catalan 0 = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem catalan_one : catalan 1 = 1 := by simp [catalan_succ]

/-- A helper sequence that can be used to prove the equality of the recursive and the explicit
definition using a telescoping sum argument. -/
/-
**gosperCatalan** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper sequence that can be used to prove the equality of the recursive and th
e explicit
definition using a telescoping sum argument.
-/
private def gosperCatalan (n j : ℕ) : ℚ :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))
/-
**gosper_trick** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem gosper_trick {n i : ℕ} (h : i ≤ n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) := by
  have l₁ : (i : ℚ) + 1 ≠ 0 := by norm_cast
  have l₂ : (n : ℚ) - i + 1 ≠ 0 := by norm_cast
  have h₁ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (i + 1))) l₁).symm
  have h₂ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (n - i + 1))) l₂).symm
  have h₃ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ i
  have h₄ :
    ((n : ℚ) - i + 1) * (n - i + 1).centralBinom = 2 * (2 * (n - i) + 1) * (n - i).centralBinom :=
      mod_cast Nat.succ_mul_centralBinom_succ (n - i)
  simp only [gosperCatalan]
  push_cast
  rw [show n + 1 - i = n - i + 1 by rw [Nat.add_comm (n - i) 1, ← (Nat.add_sub_assoc h 1),
    add_comm]]
  rw [h₁, h₂, h₃, h₄]
  field
/-
**gosper_catalan_sub_eq_central_binom_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem gosper_catalan_sub_eq_central_binom_div (n : ℕ) : gosperCatalan (n + 1) (n + 1) -
    gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) := by
  simp only [gosperCatalan, tsub_self, Nat.centralBinom_zero, Nat.cast_one, mul_one, Nat.cast_add,
    Nat.sub_zero, one_mul, Nat.cast_zero, mul_zero, zero_sub, neg_add_rev]
  field
/-
**catalan_eq_centralBinom_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_eq_centralBinom_div (n : Nat) : catalan n = n.centralBinom / (n + 
1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan_zero`：catalan_zero : catalan 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.centralBinom_zero`：centralBinom_zero : centralBinom 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `catalan_succ`：catalan_succ (n : Nat) : catalan (n + 1) = ∑ i : Fin n.suc
c, catalan i * catalan (n - i)
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Catalan.Basic.0.gosper_trick`
：∀ {n i : ℕ},   i ≤ n →     gosperCatalan✝ (n + 1) (i + 1) - gosperCatalan✝ (n +
 1) i =       ↑i.centralBinom / (↑i + 1) * ↑(n - i).centralBi…
· 使用定理 `Fin.is_le`：∀ {n : ℕ} (i : Fin (n + 1)), ↑i ≤ n
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Catalan.Basic.0.gosper_catala
n_sub_eq_central_binom_div`：∀ (n : ℕ), gosperCatalan✝ (n + 1) (n + 1) - gosperCa
talan✝ (n + 1) 0 = ↑(n + 1).centralBinom / (↑n + 2)
· 使用定理 `Nat.succ_dvd_centralBinom`：succ_dvd_centralBinom (n : Nat) : n + 1 ∣ n.c
entralBinom
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem catalan_eq_centralBinom_div (n : ℕ) : catalan n = n.centralBinom / (n + 1) := by
  suffices (catalan n : ℚ) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    exact mod_cast this
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.centralBinom i / (i + 1) *
                            (Nat.centralBinom (d - i) / (d - i + 1)) : ℚ)
    · congr
      ext1 x
      have m_le_d : x.val ≤ d := by lia
      have d_minus_x_le_d : (d - x.val) ≤ d := tsub_le_self
      rw [hd _ m_le_d, hd _ d_minus_x_le_d]
      norm_cast
    · trans (∑ i : Fin d.succ, (gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i))
      · refine sum_congr rfl fun i _ => ?_
        rw [gosper_trick i.is_le, mul_div]
      · rw [← sum_range fun i => gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i,
            sum_range_sub, Nat.succ_eq_add_one]
        rw [gosper_catalan_sub_eq_central_binom_div d]
        norm_cast
/-
**succ_mul_catalan_eq_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：succ_mul_catalan_eq_centralBinom (n : Nat) : (n + 1) * catalan n = n.centr
alBinom
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_mul_of_div_eq_right`：∀ {a b c : ℕ}, b ∣ a → a / b = c → a = b * c
· 使用定理 `Nat.succ_dvd_centralBinom`：succ_dvd_centralBinom (n : Nat) : n + 1 ∣ n.c
entralBinom
· 使用定理 `catalan_eq_centralBinom_div`：catalan_eq_centralBinom_div (n : Nat) : cat
alan n = n.centralBinom / (n + 1)
-/
theorem succ_mul_catalan_eq_centralBinom (n : ℕ) : (n + 1) * catalan n = n.centralBinom :=
  (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm
/-
**catalan_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_two : catalan 2 = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan_eq_centralBinom_div`：catalan_eq_centralBinom_div (n : Nat) : cat
alan n = n.centralBinom / (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_natDiv`：∀ {a b a' b' c : ℕ},   Mathlib.Meta.N
ormNum.IsNat a a' →     Mathlib.Meta.NormNum.IsNat b b' → a'.div b' = c → Mathli
b.Meta.NormNum.IsNat (a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem catalan_two : catalan 2 = 2 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
/-
**catalan_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：catalan_three : catalan 3 = 5
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `catalan_eq_centralBinom_div`：catalan_eq_centralBinom_div (n : Nat) : cat
alan n = n.centralBinom / (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_natDiv`：∀ {a b a' b' c : ℕ},   Mathlib.Meta.N
ormNum.IsNat a a' →     Mathlib.Meta.NormNum.IsNat b b' → a'.div b' = c → Mathli
b.Meta.NormNum.IsNat (a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem catalan_three : catalan 3 = 5 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
