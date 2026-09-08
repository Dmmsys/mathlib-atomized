/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Int.Sqrt

/-!
# Parity of integers
-/

public section

open Nat

namespace Int

/-! #### Parity -/

variable {m n : ℤ}

/-
**Int.emod_two_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, ¬n % 2 = 1 ↔ n % 2 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by grind
/-
**Int.one_emod_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：1 % 2 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_emod_two : (1 : Int) % 2 = 1 := rfl

-- `EuclideanDomain.mod_eq_zero` uses (2 ∣ n) as normal form
/-
**Int.emod_two_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, ¬n % 2 = 0 ↔ n % 2 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[local simp] lemma emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by grind

@[grind =]
/-
**Int.even_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_iff : Even n ↔ n % 2 = 0 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_emod_right`：∀ (a b : ℤ), a * b % a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩
/-
**Int.not_even_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：not_even_iff : ¬Even n ↔ n % 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_even_iff : ¬Even n ↔ n % 2 = 1 := by grind
/-
**Int.two_dvd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, ¬2 ∣ n ↔ n % 2 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 := by grind
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (Even : ℤ → Prop) := fun _ ↦ decidable_of_iff _ even_iff.symm

/-- `IsSquare` can be decided on `ℤ` by checking against the square root. -/
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSquare` can be decided on `ℤ` by checking against the square root.
-/
instance : DecidablePred (IsSquare : ℤ → Prop) :=
  fun m ↦ decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]
/-
**Int.not_even_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：¬Even 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma not_even_one : ¬Even (1 : ℤ) := by simp [even_iff]
/-
**Int.even_add** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m n : ℤ}, Even (m + n) ↔ (Even m ↔ Even n)
参数：m + n；Even m ↔ Even n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by grind
/-
**Int.two_not_dvd_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_not_dvd_two_mul_add_one (n : Int) : ¬2 ∣ 2 * n + 1
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ 2 * n + 1 := by grind

@[parity_simps]
/-
**Int.even_sub** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_sub : Even (m - n) ↔ (Even m ↔ Even n)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by grind
/-
**Int.even_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, Even (n + 1) ↔ ¬Even n
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by grind
/-
**Int.even_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℤ}, Even (n - 1) ↔ ¬Even n
参数：n - 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma even_sub_one : Even (n - 1) ↔ ¬Even n := by grind
/-
**Int.even_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m n : ℤ}, Even (m * n) ↔ Even m ∨ Even n
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.emod_two_eq_zero_or_one`：emod_two_eq_zero_or_one (n : Int) : n % 2 =
 0 ∨ n % 2 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.mul_emod`：∀ (a b n : ℤ), a * b % n = a % n * (b % n) % n
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[parity_simps, grind =] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases emod_two_eq_zero_or_one m with h₁ | h₁ <;>
  rcases emod_two_eq_zero_or_one n with h₂ | h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]
/-
**Int.even_pow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {m : ℤ} {n : ℕ}, Even (m ^ n) ↔ Even m ∧ n ≠ 0
参数：m ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps, grind =] lemma even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction n with grind
/-
**Int.even_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_pow' {n : Nat} (h : n != 0) : Even (m ^ n) ↔ Even m
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m := by grind

@[simp, norm_cast, grind =]
/-
**Int.even_coe_nat** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：even_coe_nat (n : Nat) : Even (n : Int) ↔ Even n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]
/-
**Int.two_mul_ediv_two_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_mul_ediv_two_of_even : Even n -> 2 * (n / 2) = n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n := by grind
/-
**Int.ediv_two_mul_two_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：ediv_two_mul_two_of_even : Even n -> n / 2 * 2 = n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n := by grind

-- Here are examples of how `parity_simps` can be used with `Int`.
/-
**Int.** 是 Mathlib 中的一个示例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp +decide [*, parity_simps]
/-
**Int.** 是 Mathlib 中的一个示例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ¬Even (25394535 : ℤ) := by decide

@[simp]
/-
**Int.isSquare_sign_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isSquare_sign_iff {z : Int} : IsSquare z.sign ↔ 0 <= z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Std.IsLinearPreorder.toIsPreorder`：∀ {α : Type u} {inst : LE α} [self : 
Std.IsLinearPreorder α], Std.IsPreorder α
· 使用定理 `Std.IsLinearOrder.toIsLinearPreorder`：∀ {α : Type u} [inst : LE α] [self
 : Std.IsLinearOrder α], Std.IsLinearPreorder α
· 使用定理 `Lean.Grind.instIsLinearOrderInt`：Std.IsLinearOrder ℤ
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Int.sign_eq_neg_one_of_neg`：∀ {a : ℤ}, a < 0 → a.sign = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `Int.neg_nonneg`：∀ {a : ℤ}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem isSquare_sign_iff {z : ℤ} : IsSquare z.sign ↔ 0 ≤ z := by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by lia), ← neg_add', Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero_iff, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

end Int

