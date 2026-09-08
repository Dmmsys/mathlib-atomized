/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The rational numbers are a commutative ring

This file contains the commutative ring instance on the rational numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists IsOrderedMonoid Field PNat Nat.gcd_greatest

namespace Rat

/-! ### Instances -/

/-
**Rat.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：commRing : CommRing Rat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.add_comm`：∀ {G : Type u} [self : AddCommGroup G] (a b : G),
 a + b = b + a
· 使用定理 `Rat.zero_mul`：∀ (a : ℚ), 0 * a = 0
· 使用定理 `Rat.mul_zero`：∀ (a : ℚ), a * 0 = 0
· 使用定理 `Rat.mul_add`：∀ (a b c : ℚ), a * (b + c) = a * b + a * c
· 使用定理 `Rat.add_mul`：∀ (a b c : ℚ), (a + b) * c = a * c + b * c
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a

--- 原说明 ---
### Instances
-/
instance commRing : CommRing ℚ where
  __ := addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ Int.one_ne_zero Int.one_ne_zero,
      ← divInt_one_one, Int.natCast_add, Int.natCast_one, mul_one]
/-
**Rat.commGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：commGroupWithZero : CommGroupWithZero Rat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.zpow_zero`：∀ (q : ℚ), q ^ 0 = 1
· 使用定理 `Rat.inv_zero`：0⁻¹ = 0
· 使用定理 `Rat.mul_inv_cancel`：∀ (a : ℚ), a ≠ 0 → a * a⁻¹ = 1
-/
instance commGroupWithZero : CommGroupWithZero ℚ :=
  { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := Rat.inv_zero
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul
    zpow z q := q ^ z
    zpow_zero' := Rat.zpow_zero
    zpow_succ' _ _ := by rw [Rat.zpow_natCast, Rat.zpow_natCast, Rat.pow_succ] }
/-
**Rat.isDomain** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：isDomain : IsDomain Rat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
-/
instance isDomain : IsDomain ℚ := NoZeroDivisors.to_isDomain _
/-- The characteristic of `ℚ` is 0. -/
@[stacks 09FS "Second part."]
/-
**Rat.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instCharZero : CharZero Rat where cast_injective a b hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The characteristic of `ℚ` is 0.
-/
instance instCharZero : CharZero ℚ where cast_injective a b hab := by simpa using congr_arg num hab

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

/-
**Rat.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：commSemiring : CommSemiring Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instan
ces non-computably.
-/
instance commSemiring : CommSemiring ℚ := by infer_instance
/-
**Rat.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：semiring : Semiring Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring : Semiring ℚ := by infer_instance

/-! ### Miscellaneous lemmas -/

/-
**Rat.divInt_div_divInt_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：divInt_div_divInt_cancel_left {x : Int} (hx : x != 0) (n d : Int) : n /. x
 / (d /. x) = n /. d
参数：hx : x != 0；n d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Rat.inv_divInt`：∀ (n d : ℤ), (Rat.divInt n d)⁻¹ = Rat.divInt d n
· 使用定理 `Rat.divInt_mul_divInt_cancel`：divInt_mul_divInt_cancel {x : Int} (hx : x
 != 0) (n d : Int) : n /. x * (x /. d) = n /. d

--- 原说明 ---
### Miscellaneous lemmas
-/
lemma divInt_div_divInt_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_divInt, divInt_mul_divInt_cancel hx]
/-
**Rat.divInt_div_divInt_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：divInt_div_divInt_cancel_right {x : Int} (hx : x != 0) (n d : Int) : x /. 
n / (x /. d) = d /. n
参数：hx : x != 0；n d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Rat.inv_divInt`：∀ (n d : ℤ), (Rat.divInt n d)⁻¹ = Rat.divInt d n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Rat.divInt_mul_divInt_cancel`：divInt_mul_divInt_cancel {x : Int} (hx : x
 != 0) (n d : Int) : n /. x * (x /. d) = n /. d
-/
lemma divInt_div_divInt_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_divInt, mul_comm, divInt_mul_divInt_cancel hx]
/-
**Rat.num_div_den** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) = r
参数：r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
-/
lemma num_div_den (r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r := by
  rw [← Int.cast_natCast, ← divInt_eq_div, num_divInt_den]
/-
**Rat.divInt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (num : ℕ) (den : ℤ) (n : ℕ), Rat.divInt (↑num) den ^ n = Rat.divInt (↑nu
m ^ n) (den ^ n)
参数：num : ℕ；den : ℤ；n : ℕ；↑num；↑num ^ n；den ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma divInt_pow (num : ℕ) (den : ℤ) (n : ℕ) : (num /. den) ^ n = num ^ n /. den ^ n := by
  simp [divInt_eq_div, div_pow]
/-
**Rat.mkRat_pow** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (num den n : ℕ), mkRat (↑num) den ^ n = mkRat (↑num ^ n) (den ^ n)
参数：num den n : ℕ；↑num；↑num ^ n；den ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mkRat_eq_divInt`：mkRat_eq_divInt (n d) : mkRat n d = n /. d
· 使用定理 `Rat.divInt_pow`：∀ (num : ℕ) (den : ℤ) (n : ℕ), Rat.divInt (↑num) den ^ n
 = Rat.divInt (↑num ^ n) (den ^ n)
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
-/
@[simp] lemma mkRat_pow (num den : ℕ) (n : ℕ) : mkRat num den ^ n = mkRat (num ^ n) (den ^ n) := by
  rw [mkRat_eq_divInt, mkRat_eq_divInt, divInt_pow, Int.natCast_pow]
/-
**Rat.natCast_eq_divInt** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：natCast_eq_divInt (n : Nat) : ↑n = n /. 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.intCast_eq_divInt`：intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1
-/
lemma natCast_eq_divInt (n : ℕ) : ↑n = n /. 1 := by rw [← Int.cast_natCast, intCast_eq_divInt]
/-
**Rat.mul_den_eq_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), q * ↑q.den = ↑q.num
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `Rat.divInt_mul_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ}, Rat.divInt n₁ d₁ * Rat
.divInt n₂ d₂ = Rat.divInt (n₁ * n₂) (d₁ * d₂)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Rat.divInt_mul_right`：∀ {n d a : ℤ}, a ≠ 0 → Rat.divInt (n * a) (d * a) 
= Rat.divInt n d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `Rat.mkRat_self`：∀ (a : ℚ), mkRat a.num a.den = a
· 使用定理 `Rat.divInt_one`：∀ (n : ℤ), Rat.divInt n 1 = ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mul_den_eq_num (q : ℚ) : q * q.den = q.num := by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by simp_all
  have : (q.den : ℤ) ≠ 0 := mod_cast q.den_ne_zero
  rw [divInt_mul_divInt, mul_comm (q.den : ℤ) 1, divInt_mul_right this]
/-
**Rat.den_mul_eq_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), ↑q.den * q = ↑q.num
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
-/
@[simp] lemma den_mul_eq_num (q : ℚ) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

end Rat

