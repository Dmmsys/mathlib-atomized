/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Group.Int.Even

/-!
# Basic parity lemmas for the ring `ℤ`

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Parity -/

variable {m n : ℤ}

@[grind =]
/-
**Int.odd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：odd_iff : Odd n ↔ n % 2 = 1 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_iff : Odd n ↔ n % 2 = 1 where
  mp := fun ⟨m, hm⟩ ↦ by grind
  mpr h := ⟨n / 2, by grind⟩
/-
**Int.not_odd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：not_odd_iff : ¬Odd n ↔ n % 2 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind
/-
**Int.not_odd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：¬Odd 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_odd_zero : ¬Odd (0 : ℤ) := by grind
/-
**Int.not_odd_iff_even** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, ¬Odd n ↔ Even n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
/-
**Int.not_even_iff_odd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, ¬Even n ↔ Odd n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind
/-
**Int.even_or_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_or_odd (n : Int) : Even n ∨ Odd n
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_or_odd (n : ℤ) : Even n ∨ Odd n := by grind
/-
**Int.even_or_odd'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_or_odd' (n : Int) : exists k, n = 2 * k ∨ n = 2 * k + 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.even_or_odd`：even_or_odd (n : Int) : Even n ∨ Odd n
-/
lemma even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n
/-
**Int.even_xor_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_xor_odd (n : Int) : Xor (Even n) (Odd n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_xor_odd (n : ℤ) : Xor (Even n) (Odd n) := by
  grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd := even_xor_odd
/-
**Int.even_xor_odd'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_xor_odd' (n : Int) : exists k, Xor (n = 2 * k) (n = 2 * k + 1)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.even_or_odd`：even_or_odd (n : Int) : Even n ∨ Odd n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma even_xor_odd' (n : ℤ) : ∃ k, Xor (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    grind

@[deprecated (since := "2026-04-27")] alias even_xor'_odd' := even_xor_odd'
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (Odd : ℤ → Prop) := fun _ => decidable_of_iff _ not_even_iff_odd
/-
**Int.even_add'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_add' : Even (m + n) ↔ (Odd m ↔ Odd n)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind
/-
**Int.not_even_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：not_even_two_mul_add_one (n : Int) : ¬ Even (2 * n + 1)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_even_two_mul_add_one (n : ℤ) : ¬ Even (2 * n + 1) := by grind
/-
**Int.even_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind
/-
**Int.odd_mul** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [← not_even_iff_odd, not_or, parity_simps]
/-
**Int.Odd.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Int.Odd`。
形式化陈述：∀ {m n : ℤ}, Odd (m * n) → Odd m
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.odd_mul`：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
-/
lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m := (odd_mul.mp h).1
/-
**Int.Odd.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Int.Odd`。
形式化陈述：∀ {m n : ℤ}, Odd (m * n) → Odd n
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.odd_mul`：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
-/
lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n := (odd_mul.mp h).2
/-
**Int.odd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m : ℤ} {n : ℕ}, Odd (m ^ n) ↔ Odd m ∨ n = 0
参数：m ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma odd_pow {n : ℕ} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by grind
/-
**Int.odd_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：odd_pow' {n : Nat} (h : n != 0) : Odd (m ^ n) ↔ Odd m
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m := by grind
/-
**Int.odd_add** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m n : ℤ}, Odd (m + n) ↔ (Odd m ↔ Even n)
参数：m + n；Odd m ↔ Even n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind
/-
**Int.odd_add'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind
/-
**Int.ne_of_odd_add** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：ne_of_odd_add (h : Odd (m + n)) : m != n
参数：h : Odd (m + n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind
/-
**Int.odd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m n : ℤ}, Odd (m - n) ↔ (Odd m ↔ Even n)
参数：m - n；Odd m ↔ Even n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind
/-
**Int.odd_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind
/-
**Int.even_mul_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_mul_succ_self (n : Int) : Even (n * (n + 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) := by grind
/-
**Int.even_mul_pred_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_mul_pred_self (n : Int) : Even (n * (n - 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_mul_pred_self (n : ℤ) : Even (n * (n - 1)) := by grind
/-
**Int.odd_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℕ), Odd ↑n ↔ Odd n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by grind
/-
**Int.natAbs_even** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, Even n.natAbs ↔ Even n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma natAbs_even : Even n.natAbs ↔ Even n := by grind

@[simp]
/-
**Int.natAbs_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_odd : Odd n.natAbs ↔ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natAbs_odd : Odd n.natAbs ↔ Odd n := by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd
/-
**Int.four_dvd_add_or_sub_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：four_dvd_add_or_sub_of_odd {a b : Int} (ha : Odd a) (hb : Odd b) : 4 ∣ a +
 b ∨ 4 ∣ a - b
参数：ha : Odd a；hb : Odd b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by grind
/-
**Int.two_dvd_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_dvd_mul_add_one (k : Int) : 2 ∣ k * (k + 1)
参数：k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用引理 `Int.even_mul_succ_self`：even_mul_succ_self (n : Int) : Even (n * (n + 1)
)
-/
lemma two_dvd_mul_add_one (k : ℤ) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)
/-
**Int.two_mul_ediv_two_add_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_mul_ediv_two_add_one_of_odd : Odd n -> 2 * (n / 2) + 1 = n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n := by grind
/-
**Int.ediv_two_mul_two_add_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：ediv_two_mul_two_add_one_of_odd : Odd n -> n / 2 * 2 + 1 = n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n := by grind
/-
**Int.add_one_ediv_two_mul_two_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：add_one_ediv_two_mul_two_of_odd : Odd n -> 1 + n / 2 * 2 = n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n := by grind
/-
**Int.two_mul_ediv_two_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 := by grind

@[simp]
/-
**Int.even_sign_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：even_sign_iff {z : Int} : Even z.sign ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even_sign_iff {z : ℤ} : Even z.sign ↔ z = 0 := by grind

@[simp]
/-
**Int.odd_sign_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：odd_sign_iff {z : Int} : Odd z.sign ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem odd_sign_iff {z : ℤ} : Odd z.sign ↔ z ≠ 0 := by grind

@[norm_cast, simp]
/-
**Int.isSquare_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isSquare_natCast_iff {n : Nat} : IsSquare (n : Int) ↔ IsSquare n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_mul_natAbs_eq`：∀ {a b : ℤ} {c : ℕ}, a * b = ↑c → a.natAbs * b
.natAbs = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℤ) ↔ IsSquare n := by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

@[simp]
/-
**Int.isSquare_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isSquare_ofNat_iff {n : Nat} : IsSquare (ofNat(n) : Int) ↔ IsSquare (ofNat
(n) : Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.isSquare_natCast_iff`：isSquare_natCast_iff {n : Nat} : IsSquare (n :
 Int) ↔ IsSquare n
-/
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℤ) ↔ IsSquare (ofNat(n) : ℕ) :=
  isSquare_natCast_iff

-- These next two don't make good `norm_cast` lemmas.
/-
**Int.natCast_pow_pred** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natCast_pow_pred (b p : Nat) (w : 0 < b) : ((b ^ p - 1 : Nat) : Int) = (b 
: Int) ^ p - 1
参数：b p : Nat；w : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem natCast_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1 := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  norm_cast
/-
**Int.coe_nat_two_pow_pred** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：coe_nat_two_pow_pred (p : Nat) : ((2 ^ p - 1 : Nat) : Int) = (2 ^ p - 1 : 
Int)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_pow_pred`：natCast_pow_pred (b p : Nat) (w : 0 < b) : ((b ^ p
 - 1 : Nat) : Int) = (b : Int) ^ p - 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  natCast_pow_pred 2 p (by decide)

end Int

section DivisionMonoid

variable {α : Type*} [DivisionMonoid α] [HasDistribNeg α] {n : ℤ}

/-
**Odd.neg_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n
参数：h : Odd n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast]
    norm_cast
    simp [pow_add]
  | negSucc k =>
    simp_rw [Int.negSucc_eq, show 2 * -(↑k + 1) + (1 : ℤ) = - (1 + k*2) by grind, _root_.zpow_neg]
    norm_cast
    simp [pow_add]
/-
**Odd.neg_one_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Odd.neg_zpow`：Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
-/
theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionMonoid

