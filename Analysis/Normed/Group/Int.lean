/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Instances.Int

/-! # ℤ as a normed group -/

public section

open NNReal

variable {α : Type*}
namespace Int

/-
**Int.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup Int where norm n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAddCommGroup : NormedAddCommGroup ℤ where
  norm n := ‖(n : ℝ)‖
  dist_eq m n := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [abs_sub_comm, neg_add_eq_sub]

@[norm_cast]
/-
**Int.norm_cast_real** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：norm_cast_real (m : Int) : ‖(m : Real)‖ = ‖m‖
参数：m : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_cast_real (m : ℤ) : ‖(m : ℝ)‖ = ‖m‖ :=
  rfl
/-
**Int.norm_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)|
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_abs (n : ℤ) : ‖n‖ = |(n : ℝ)| :=
  rfl
/-
**Int.norm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：norm_natCast (n : Nat) : ‖(n : Int)‖ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_natCast (n : ℕ) : ‖(n : ℤ)‖ = n := by simp [Int.norm_eq_abs]
/-
**Int._root_.NNReal.natCast_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NNReal.natCast_natAbs (n : ℤ) : (n.natAbs : ℝ≥0) = ‖n‖₊ :=
  NNReal.eq <|
    calc
      ((n.natAbs : ℝ≥0) : ℝ) = (n.natAbs : ℤ) := by simp only [Int.cast_natCast, NNReal.coe_natCast]
      _ = |(n : ℝ)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm
/-
**Int.abs_le_floor_nnreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_le_floor_nnreal_iff (z : Int) (c : Real>=0) : |z| <= ⌊c⌋₊ ↔ ‖z‖₊ <= c
参数：z : Int；c : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NNReal.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = ‖n‖₊
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0) : |z| ≤ ⌊c⌋₊ ↔ ‖z‖₊ ≤ c := by
  rw [Int.abs_eq_natAbs, Int.ofNat_le, Nat.le_floor_iff zero_le, NNReal.natCast_natAbs z]

end Int

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `zsmul`.
section

variable [SeminormedCommGroup α]

@[to_additive norm_zsmul_le]
/-
**norm_zpow_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_zpow_le_mul_norm (n : Int) (a : α) : ‖a ^ n‖ <= ‖n‖ * ‖a‖
参数：n : Int；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Int)‖ = n
· 使用定理 `norm_pow_le_mul_norm`：∀ {E : Type u_5} [inst : SeminormedGroup E] {a : E
} {n : ℕ}, ‖a ^ n‖ ≤ ↑n * ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
theorem norm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖ ≤ ‖n‖ * ‖a‖ := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa [Int.norm_natCast] using norm_pow_le_mul_norm

@[to_additive nnnorm_zsmul_le]
/-
**nnnorm_zpow_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_zpow_le_mul_norm (n : Int) (a : α) : ‖a ^ n‖₊ <= ‖n‖₊ * ‖a‖₊
参数：n : Int；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_zpow_le_mul_norm`：norm_zpow_le_mul_norm (n : Int) (a : α) : ‖a ^ n‖
 <= ‖n‖ * ‖a‖
-/
theorem nnnorm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖₊ ≤ ‖n‖₊ * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using! norm_zpow_le_mul_norm n a

end

