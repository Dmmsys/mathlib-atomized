/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

open Function Nat

namespace Int

/-
**Int.natCast_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natCast_strictMono : StrictMono (· : Nat -> Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
-/
theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

/-! ### Miscellaneous lemmas -/

/-
**Int.abs_eq_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (a : ℤ), |a| = ↑a.natAbs
参数：a : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.negSucc_lt_zero`：∀ (n : ℕ), Int.negSucc n < 0

--- 原说明 ---
### Miscellaneous lemmas
-/
theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| natCast_nonneg _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _
/-
**Int.natCast_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℤ), ↑n.natAbs = |n|
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
-/
@[norm_cast] lemma natCast_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := n.abs_eq_natAbs.symm
/-
**Int.natAbs_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_abs (a : Int) : natAbs |a| = natAbs a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natAbs_abs (a : ℤ) : natAbs |a| = natAbs a := by grind
/-
**Int.sign_mul_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sign_mul_abs (a : Int) : sign a * |a| = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.sign_mul_natAbs`：∀ (a : ℤ), a.sign * ↑a.natAbs = a
-/
theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [abs_eq_natAbs, sign_mul_natAbs a]
/-
**Int.sign_mul_self_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sign_mul_self_eq_abs (a : Int) : sign a * a = |a|
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.sign_mul_self_eq_natAbs`：sign_mul_self_eq_natAbs (a : Int) : sign a 
* a = natAbs a
-/
theorem sign_mul_self_eq_abs (a : ℤ) : sign a * a = |a| := by
  rw [abs_eq_natAbs, sign_mul_self_eq_natAbs]
/-
**Int.natAbs_le_self_sq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_le_self_sq (a : Int) : (Int.natAbs a : Int) <= a ^ 2
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_sq`：∀ (a : ℤ), ↑a.natAbs ^ 2 = a ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
-/
lemma natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq
/-
**Int.le_self_sq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：le_self_sq (b : Int) : b <= b ^ 2
参数：b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Int.le_natAbs`：∀ {a : ℤ}, a ≤ ↑a.natAbs
· 使用引理 `Int.natAbs_le_self_sq`：natAbs_le_self_sq (a : Int) : (Int.natAbs a : Int
) <= a ^ 2
-/
lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq
/-
**Int.abs_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℕ), |↑n| = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
@[norm_cast] lemma abs_natCast (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (natCast_nonneg n)
/-
**Int.natAbs_sub_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_sub_pos_iff {i j : Int} : 0 < natAbs (i - j) ↔ i != j
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natAbs_sub_pos_iff {i j : ℤ} : 0 < natAbs (i - j) ↔ i ≠ j := by
  grind
/-
**Int.natAbs_sub_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_sub_ne_zero_iff {i j : Int} : natAbs (i - j) != 0 ↔ i != j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n
· 使用定理 `Int.natAbs_sub_pos_iff`：natAbs_sub_pos_iff {i j : Int} : 0 < natAbs (i -
 j) ↔ i != j
-/
theorem natAbs_sub_ne_zero_iff {i j : ℤ} : natAbs (i - j) ≠ 0 ↔ i ≠ j :=
  Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

@[simp]
/-
**Int.abs_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_lt_one_iff {a : Int} : |a| < 1 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 := by
  grind
/-
**Int.abs_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_le_one_iff {a : Int} : |a| <= 1 ↔ a = 0 ∨ a = 1 ∨ a = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by
  grind
/-
**Int.one_le_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z|
参数：h₀ : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.add_one_le_iff`：∀ {a b : ℤ}, a + 1 ≤ b ↔ a < b
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
-/
theorem one_le_abs {z : ℤ} (h₀ : z ≠ 0) : 1 ≤ |z| :=
  add_one_le_iff.mpr (abs_pos.mpr h₀)
/-
**Int.eq_zero_of_abs_lt_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：eq_zero_of_abs_lt_dvd {m x : Int} (h1 : m ∣ x) (h2 : |x| < m) : x = 0
参数：h1 : m ∣ x；h2 : |x| < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `Int.natAbs_le_of_dvd_ne_zero`：natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn
 : n != 0) : natAbs m <= natAbs n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
-/
lemma eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  lia
/-
**Int.abs_sub_lt_of_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：abs_sub_lt_of_lt_lt {m a b : Nat} (ha : a < m) (hb : b < m) : |(b : Int) -
 a| < m
参数：ha : a < m；hb : b < m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abs_sub_lt_of_lt_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : |(b : ℤ) - a| < m := by
  grind

/-! #### `/`  -/

/-
**Int.ediv_eq_zero_of_lt_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ediv_eq_zero_of_lt_abs {a b : Int} (H1 : 0 <= a) (H2 : a < |b|) : a / b = 
0
参数：H1 : 0 <= a；H2 : a < |b|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.ediv_eq_zero_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a / b = 0
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_neg`：∀ (a b : ℤ), a / -b = -(a / b)

--- 原说明 ---
#### `/`
-/
theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
  match b, |b|, abs_eq_natAbs b, H2 with
  | (n : ℕ), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
  | -[n+1], _, rfl, H2 => neg_injective <| by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

/-! #### mod -/

@[simp]
/-
**Int.emod_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：emod_abs (a b : Int) : a % |b| = a % b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_by_cases`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] {a : α} (P : α → Prop), P a → P (-a) → P |a|
· 使用定理 `Int.emod_neg`：∀ (a b : ℤ), a % -b = a % b

--- 原说明 ---
#### mod
-/
theorem emod_abs (a b : ℤ) : a % |b| = a % b :=
  abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)
/-
**Int.emod_lt_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < |b|
参数：a : Int；H : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_abs`：emod_abs (a b : Int) : a % |b| = a % b
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
-/
theorem emod_lt_abs (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| := by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

/-! ### properties of `/` and `%` -/

/-
**Int.abs_ediv_le_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_ediv_le_abs : forall a b : Int, |a / b| <= |a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `Int.ediv_neg`：∀ (a b : ℤ), a / -b = -(a / b)
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|

--- 原说明 ---
### properties of `/` and `%`
-/
theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| :=
  suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs, abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le
    (match a, n with
      | (m : ℕ), n => Nat.div_le_self _ _
      | -[m+1], 0 => Nat.zero_le _
      | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))
/-
**Int.abs_sign_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_sign_of_ne_zero {z : Int} (hz : z != 0) : |z.sign| = 1
参数：hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.natAbs_sign_of_ne_zero`：∀ {z : ℤ}, z ≠ 0 → z.sign.natAbs = 1
· 使用定理 `Int.ofNat_one`：↑1 = 1
-/
theorem abs_sign_of_ne_zero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rw [abs_eq_natAbs, natAbs_sign_of_ne_zero hz, Int.ofNat_one]
/-
**Int.sign_eq_ediv_abs'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (a : ℤ), a.sign = a / |a|
参数：a : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_eq_of_eq_mul_left`：∀ {a b c : ℤ}, b ≠ 0 → a = c * b → a / b = c
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.sign_mul_abs`：sign_mul_abs (a : Int) : sign a * |a| = a
-/
protected theorem sign_eq_ediv_abs' (a : ℤ) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm
/-
**Int.sign_eq_abs_ediv** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (a : ℤ), a.sign = |a| / a
参数：a : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_eq_of_eq_mul_left`：∀ {a b c : ℤ}, b ≠ 0 → a = c * b → a / b = c
· 使用定理 `Int.sign_mul_self_eq_abs`：sign_mul_self_eq_abs (a : Int) : sign a * a = 
|a|
-/
protected theorem sign_eq_abs_ediv (a : ℤ) : sign a = |a| / a :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm

end Int

section Group
variable {G : Type*} [Group G]

@[to_additive (attr := simp) abs_zsmul_eq_zero]
/-
**zpow_abs_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_abs_eq_one (a : G) (n : Int) : a ^ |n| = 1 ↔ a ^ n = 1
参数：a : G；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `pow_natAbs_eq_one`：pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zpow_abs_eq_one (a : G) (n : ℤ) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs, zpow_natCast, pow_natAbs_eq_one]

end Group

