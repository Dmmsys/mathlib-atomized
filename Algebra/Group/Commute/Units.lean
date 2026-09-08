/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about commuting pairs of elements involving units.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {M : Type*}

section Monoid
variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

namespace Commute

@[to_additive]
/-
**Commute.units_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_inv_right : Commute a u -> Commute a ↑u⁻¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_right`：units_inv_right {a : M} {x y : Mˣ} (h : Semi
conjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹
-/
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right

@[to_additive (attr := simp)]
/-
**Commute.units_inv_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_right_iff`：units_inv_right_iff {a : M} {x y : Mˣ} :
 SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y
-/
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff

@[to_additive]
/-
**Commute.units_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_inv_left : Commute (↑u) a -> Commute (↑u⁻¹) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_symm_left`：units_inv_symm_left {a : Mˣ} {x y : M} (
h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x
-/
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left

@[to_additive (attr := simp)]
/-
**Commute.units_inv_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_symm_left_iff`：units_inv_symm_left_iff {a : Mˣ} {x 
y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y
-/
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff

@[to_additive]
/-
**Commute.units_val** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_val : Commute u₁ u₂ -> Commute (u₁ : M) u₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_val`：units_val {a x y : Mˣ} (h : SemiconjBy a x y) : Se
miconjBy (a : M) x y
-/
theorem units_val : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_val

@[to_additive]
/-
**Commute.units_of_val** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_of_val : Commute (u₁ : M) u₂ -> Commute u₁ u₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_of_val`：units_of_val {a x y : Mˣ} (h : SemiconjBy (a : 
M) x y) : SemiconjBy a x y
-/
theorem units_of_val : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_val

@[to_additive (attr := simp)]
/-
**Commute.units_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_val_iff`：units_val_iff {a x y : Mˣ} : SemiconjBy (a : M
) x y ↔ SemiconjBy a x y
-/
theorem units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_val_iff

end Commute

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive /-- If the sum of two commuting elements is an additive unit, then the left summand is
an additive unit. -/]
/-
**Units.leftOfMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : M
ˣ where val
参数：u : Mˣ；a b : M；hu : a * b = u；hc : Commute a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive /-- If the sum of two commuting elements is an additive unit, then the right summand
is an additive unit. -/]
/-
**Units.rightOfMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : 
Mˣ
参数：u : Mˣ；a b : M；hu : a * b = u；hc : Commute a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.eq ▸ hu) hc.symm

@[to_additive]
/-
**Commute.isUnit_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsU
nit b
参数：h : Commute a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Commute.isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩

@[to_additive (attr := simp)]
/-
**isUnit_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).isUnit_mul_iff.trans and_self_iff

@[to_additive (attr := simp)]
/-
**Commute.units_zpow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.units_zpow_right (h : Commute a u) (m : Int) : Commute a ↑(u ^ m)
参数：h : Commute a u；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_zpow_right`：∀ {M : Type u_1} [inst : Monoid M] {a : M} 
{x y : Mˣ}, SemiconjBy a ↑x ↑y → ∀ (m : ℤ), SemiconjBy a ↑(x ^ m) ↑(y ^ m)
-/
lemma Commute.units_zpow_right (h : Commute a u) (m : ℤ) : Commute a ↑(u ^ m) :=
  SemiconjBy.units_zpow_right h m

@[to_additive (attr := simp)]
/-
**Commute.units_zpow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.units_zpow_left (h : Commute ↑u a) (m : Int) : Commute ↑(u ^ m) a
参数：h : Commute ↑u a；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `Commute.units_zpow_right`：Commute.units_zpow_right (h : Commute a u) (m 
: Int) : Commute a ↑(u ^ m)
-/
lemma Commute.units_zpow_left (h : Commute ↑u a) (m : ℤ) : Commute ↑(u ^ m) a :=
  (h.symm.units_zpow_right m).symm

/-- If a natural power of `x` is a unit, then `x` is a unit. -/
@[to_additive
/-- If a natural multiple of `x` is an additive unit, then `x` is an additive unit. -/]
/-
**Units.ofPow** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.ofPow (u : Mˣ) (x : M) {n : Nat} (hn : n != 0) (hu : x ^ n = u) : Mˣ
参数：u : Mˣ；x : M；hn : n != 0；hu : x ^ n = u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Units.ofPow (u : Mˣ) (x : M) {n : ℕ} (hn : n ≠ 0) (hu : x ^ n = u) : Mˣ :=
  u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)
/-
**isUnit_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 0 → (IsUnit (a ^ n
) ↔ IsUnit a)
参数：IsUnit (a ^ n) ↔ IsUnit a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
@[to_additive (attr := simp)] lemma isUnit_pow_iff (hn : n ≠ 0) : IsUnit (a ^ n) ↔ IsUnit a :=
  ⟨fun ⟨u, hu⟩ ↦ (u.ofPow a hn hu.symm).isUnit, IsUnit.pow n⟩

@[to_additive]
/-
**isUnit_pow_succ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
lemma isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit a := isUnit_pow_iff n.succ_ne_zero
/-
**isUnit_pow_iff_of_not_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUnit a) {n : Nat} : IsUnit (a ^ n) 
↔ n = 0
参数：hx : ¬ IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUnit a) {n : ℕ} :
    IsUnit (a ^ n) ↔ n = 0 := by
  rcases n with (_ | n) <;>
  simp [hx]

/-- If `a ^ n = 1`, `n ≠ 0`, then `a` is a unit. -/
@[to_additive (attr := simps!) /-- If `n • x = 0`, `n ≠ 0`, then `x` is an additive unit. -/]
/-
**Units.ofPowEqOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.ofPowEqOne (a : M) (n : Nat) (ha : a ^ n = 1) (hn : n != 0) : Mˣ
参数：a : M；n : Nat；ha : a ^ n = 1；hn : n != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a ^ n = 1`, `n ≠ 0`, then `a` is a unit.
-/
def Units.ofPowEqOne (a : M) (n : ℕ) (ha : a ^ n = 1) (hn : n ≠ 0) : Mˣ := Units.ofPow 1 a hn ha

@[to_additive (attr := simp)]
/-
**Units.pow_ofPowEqOne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Units.pow_ofPowEqOne (ha : a ^ n = 1) (hn : n != 0) : Units.ofPowEqOne _ n
 ha hn ^ n = 1
参数：ha : a ^ n = 1；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_ofPowEqOne`：∀ {M : Type u_1} [inst : Monoid M] (a : M) (n : ℕ)
 (ha : a ^ n = 1) (hn : n ≠ 0), ↑(Units.ofPowEqOne a n ha hn) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Units.pow_ofPowEqOne (ha : a ^ n = 1) (hn : n ≠ 0) :
    Units.ofPowEqOne _ n ha hn ^ n = 1 := Units.ext <| by simp [ha]

@[to_additive]
/-
**IsUnit.of_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n != 0) : IsUnit a
参数：ha : a ^ n = 1；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n ≠ 0) : IsUnit a :=
  (Units.ofPowEqOne _ n ha hn).isUnit

@[to_additive]
/-
**_root_.Units.commute_iff_inv_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.Units.commute_iff_inv_mul_cancel {u : Mˣ} {a : M} : Commute ↑u a ↔ 
↑u⁻¹ * a * u = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.commute_iff_inv_mul_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * a * u = a := by
  rw [mul_assoc, Units.inv_mul_eq_iff_eq_mul, eq_comm, Commute, SemiconjBy]

@[to_additive]
/-
**_root_.Units.commute_iff_inv_mul_cancel_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.Units.commute_iff_inv_mul_cancel_assoc {u : Mˣ} {a : M} : Commute ↑
u a ↔ ↑u⁻¹ * (a * u) = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.commute_iff_inv_mul_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * (a * u) = a := by
  rw [u.commute_iff_inv_mul_cancel, mul_assoc]

@[to_additive]
/-
**_root_.Units.commute_iff_mul_inv_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.Units.commute_iff_mul_inv_cancel {u : Mˣ} {a : M} : Commute ↑u a ↔ 
↑u * a * ↑u⁻¹ = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.commute_iff_mul_inv_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * a * ↑u⁻¹ = a := by
  rw [Units.mul_inv_eq_iff_eq_mul, Commute, SemiconjBy]

@[to_additive]
/-
**_root_.Units.commute_iff_mul_inv_cancel_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.Units.commute_iff_mul_inv_cancel_assoc {u : Mˣ} {a : M} : Commute ↑
u a ↔ ↑u * (a * ↑u⁻¹) = a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.commute_iff_mul_inv_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * (a * ↑u⁻¹) = a := by
  rw [u.commute_iff_mul_inv_cancel, mul_assoc]

end Monoid

namespace Commute

variable [DivisionMonoid M] {a b c d : M}

@[to_additive]
/-
**Commute.div_eq_div_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit 
d) : a / b = c / d ↔ a * d = c * b
参数：hbd : Commute b d；hb : IsUnit b；hd : IsUnit d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, hbd.right_comm,
    hd.div_mul_cancel]

@[to_additive]
/-
**Commute.mul_inv_eq_mul_inv_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd :
 IsUnit d) : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
参数：hbd : Commute b d；hb : IsUnit b；hd : IsUnit d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Commute.div_eq_div_iff_of_isUnit`：div_eq_div_iff_of_isUnit (hbd : Commut
e b d) (hb : IsUnit b) (hd : IsUnit d) : a / b = c / d ↔ a * d = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, hbd.div_eq_div_iff_of_isUnit hb hd]

@[to_additive]
/-
**Commute.inv_mul_eq_inv_mul_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd :
 IsUnit d) : b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c
参数：hbd : Commute b d；hb : IsUnit b；hd : IsUnit d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← (hd.mul hb).mul_right_inj, ← mul_assoc, mul_assoc d, hb.mul_inv_cancel, mul_one,
    ← mul_assoc, mul_assoc d, hbd.symm.left_comm, hd.mul_inv_cancel, mul_one]

end Commute

