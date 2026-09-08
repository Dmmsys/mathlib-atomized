/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Defs  -- shake: keep (Qq dependency)
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Int.Parity -- shake: keep (Qq dependency)
public meta import Mathlib.Util.Qq

/-! # Lemmas for the `field_simp` tactic

-/

public section

open List

namespace Mathlib.Tactic.FieldSimp
@[expose] public section

section zpow'

variable {α : Type*}

section
variable [GroupWithZero α]

open scoped Classical in
/-- This is a variant of integer exponentiation, defined for internal use in the `field_simp` tactic
implementation. It differs from the usual integer exponentiation in that `0 ^ 0` is `0`, not `1`.
With this choice, the function `n ↦ a ^ n` is always a homomorphism (`a ^ (n + m) = a ^ n * a ^ m`),
even if `a` is zero. -/
/-
**Mathlib.Tactic.FieldSimp.zpow'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Field
Simp`。
形式化陈述：zpow' (a : α) (n : Int) : α
参数：a : α；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a variant of integer exponentiation, defined for internal use in the `fi
eld_simp` tactic
implementation. It differs from the usual integer exponentiation in that `0 ^ 0`
 is `0`, not `1`.
With this choice, the function `n ↦ a ^ n` is always a homomorphism (`a ^ (n + m
) = a ^ n * a ^ m`),
even if `a` is zero.
-/
noncomputable def zpow' (a : α) (n : ℤ) : α :=
  if a = 0 ∧ n = 0 then 0 else a ^ n
/-
**Mathlib.Tactic.FieldSimp.zpow'_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (m n : ℤ),   Mathlib.Tac
tic.FieldSimp.zpow' a (m + n) = Mathlib.Tactic.FieldSimp.zpow' a m * Mathlib.Tac
tic.FieldSimp.zpow' a n
参数：a : α；m n : ℤ；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
-/
theorem zpow'_add (a : α) (m n : ℤ) :
    zpow' a (m + n) = zpow' a m * zpow' a n := by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]
/-
**Mathlib.Tactic.FieldSimp.zpow'_of_ne_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (n : ℤ), n ≠ 0 → Mathlib
.Tactic.FieldSimp.zpow' a n = a ^ n
参数：a : α；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpow'_of_ne_zero_right (a : α) (n : ℤ) (hn : n ≠ 0) : zpow' a n = a ^ n := by
  simp [zpow', hn]
/-
**Mathlib.Tactic.FieldSimp.zpow'_of_ne_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (n : ℤ), a ≠ 0 → Mathlib
.Tactic.FieldSimp.zpow' a n = a ^ n
参数：a : α；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpow'_of_ne_zero_left (a : α) (n : ℤ) (ha : a ≠ 0) : zpow' a n = a ^ n := by
  simp [zpow', ha]

@[simp]
/-
**Mathlib.Tactic.FieldSimp.zero_zpow'** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
FieldSimp`。
形式化陈述：zero_zpow' (n : Int) : zpow' (0 : α) n = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
-/
lemma zero_zpow' (n : ℤ) : zpow' (0 : α) n = 0 := by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn
/-
**Mathlib.Tactic.FieldSimp.zpow'_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (n : ℤ), Mathlib.Tactic.
FieldSimp.zpow' a n = 0 ↔ a = 0
参数：a : α；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_eq_zero_iff`：zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔
 a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_imp_iff_and_not`：∀ {a b : Prop} [Decidable a], ¬(a → b) ↔ 
a ∧ ¬b
-/
lemma zpow'_eq_zero_iff (a : α) (n : ℤ) : zpow' a n = 0 ↔ a = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]
/-
**Mathlib.Tactic.FieldSimp.one_zpow'** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：one_zpow' (n : Int) : zpow' (1 : α) n = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_zpow' (n : ℤ) : zpow' (1 : α) n = 1 := by
  simp [zpow']

@[simp]
/-
**Mathlib.Tactic.FieldSimp.zpow'_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α), Mathlib.Tactic.FieldSim
p.zpow' a 1 = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zpow'_one (a : α) : zpow' a 1 = a := by
  simp [zpow']
/-
**Mathlib.Tactic.FieldSimp.zpow'_zero_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α), Mathlib.Tactic.FieldSim
p.zpow' a 0 = a / a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma zpow'_zero_eq_div (a : α) : zpow' a 0 = a / a := by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]
/-
**Mathlib.Tactic.FieldSimp.zpow'_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] {a : α}, a ≠ 0 → Mathlib.Tactic.
FieldSimp.zpow' a 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
lemma zpow'_zero_of_ne_zero {a : α} (ha : a ≠ 0) : zpow' a 0 = 1 := by simp [zpow', ha]
/-
**Mathlib.Tactic.FieldSimp.zpow'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (n : ℤ),   Mathlib.Tacti
c.FieldSimp.zpow' a (-n) = (Mathlib.Tactic.FieldSimp.zpow' a n)⁻¹
参数：a : α；n : ℤ；-n；Mathlib.Tactic.FieldSimp.zpow' a n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma zpow'_neg (a : α) (n : ℤ) : zpow' a (-n) = (zpow' a n)⁻¹ := by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto
/-
**Mathlib.Tactic.FieldSimp.zpow'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) (m n : ℤ),   Mathlib.Tac
tic.FieldSimp.zpow' a (m * n) = Mathlib.Tactic.FieldSimp.zpow' (Mathlib.Tactic.F
ieldSimp.zpow' a m) n
参数：a : α；m n : ℤ；m * n；Mathlib.Tactic.FieldSimp.zpow' a m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Mathlib.Tactic.FieldSimp.zero_zpow'`：zero_zpow' (n : Int) : zpow' (0 : α
) n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
-/
lemma zpow'_mul (a : α) (m n : ℤ) : zpow' a (m * n) = zpow' (zpow' a m) n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simpa [zpow', ha, hm, hn] using zpow_mul a m n
/-
**Mathlib.Tactic.FieldSimp.zpow'_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.FieldSimp`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib
.Tactic.FieldSimp.zpow' a ↑n = a ^ n
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_of_ne_zero_right`：∀ {α : Type u_1} [inst 
: GroupWithZero α] (a : α) (n : ℤ), n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a n =
 a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zpow'_ofNat (a : α) {n : ℕ} (hn : n ≠ 0) : zpow' a n = a ^ n := by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn

end

/-
**Mathlib.Tactic.FieldSimp.mul_zpow'** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：mul_zpow' [CommGroupWithZero α] (n : Int) (a b : α) : zpow' (a * b) n = zp
ow' a n * zpow' b n
参数：n : Int；a b : α。
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Mathlib.Tactic.FieldSimp.zero_zpow'`：zero_zpow' (n : Int) : zpow' (0 : α
) n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
-/
lemma mul_zpow' [CommGroupWithZero α] (n : ℤ) (a b : α) :
    zpow' (a * b) n = zpow' a n * zpow' b n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simpa [zpow', ha, hb] using mul_zpow a b n
/-
**Mathlib.Tactic.FieldSimp.list_prod_zpow'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp`。
形式化陈述：list_prod_zpow' [CommGroupWithZero α] {r : Int} {l : List α} : zpow' (prod
 l) r = prod (map (fun x => zpow' x r) l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.FieldSimp.one_zpow'`：one_zpow' (n : Int) : zpow' (1 : α) 
n = 1
· 使用引理 `Mathlib.Tactic.FieldSimp.mul_zpow'`：mul_zpow' [CommGroupWithZero α] (n :
 Int) (a b : α) : zpow' (a * b) n = zpow' a n * zpow' b n
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem list_prod_zpow' [CommGroupWithZero α] {r : ℤ} {l : List α} :
    zpow' (prod l) r = prod (map (fun x ↦ zpow' x r) l) :=
  let fr : α →* α := ⟨⟨fun b ↦ zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod fr l

end zpow'

/-
**Mathlib.Tactic.FieldSimp.subst_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：subst_add {M : Type*} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * 
X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ = Y) (hy : a * Y = y) : x₁ + x₂ = y
参数：h₁ : x₁ = a * X₁；h₂ : x₂ = a * X₂；H_atom : X₁ + X₂ = Y；hy : a * Y = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subst_add {M : Type*} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ = Y) (hy : a * Y = y) :
    x₁ + x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_add]
/-
**Mathlib.Tactic.FieldSimp.subst_sub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.F
ieldSimp`。
形式化陈述：subst_sub {M : Type*} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) 
(h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) (hy : a * Y = y) : x₁ - x₂ = y
参数：h₁ : x₁ = a * X₁；h₂ : x₂ = a * X₂；H_atom : X₁ - X₂ = Y；hy : a * Y = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subst_sub {M : Type*} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) (hy : a * Y = y) :
    x₁ - x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_sub]
/-
**Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.FieldSimp`。
形式化陈述：eq_div_of_eq_one_of_subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h
 : l = l_n / 1) (hn : l_n = n) : l = n
参数：h : l = l_n / 1；hn : l_n = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem eq_div_of_eq_one_of_subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
    (hn : l_n = n) :
    l = n := by
  rw [h, hn, div_one]
/-
**Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst'** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.FieldSimp`。
形式化陈述：eq_div_of_eq_one_of_subst' {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (
h : l = 1 / l_d) (hn : l_d = d) : l = d⁻¹
参数：h : l = 1 / l_d；hn : l_d = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem eq_div_of_eq_one_of_subst' {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
    (hn : l_d = d) :
    l = d⁻¹ := by
  rw [h, hn, one_div]
/-
**Mathlib.Tactic.FieldSimp.eq_div_of_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp`。
形式化陈述：eq_div_of_subst {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d
) (hn : l_n = n) (hd : l_d = d) : l = n / d
参数：h : l = l_n / l_d；hn : l_n = n；hd : l_d = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_div_of_subst {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
    (hd : l_d = d) :
    l = n / d := by
  rw [h, hn, hd]
/-
**Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.FieldSimp`。
形式化陈述：eq_mul_of_eq_eq_eq_mul {M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) 
(h₂ : b = c) (h₃ : c = D * e) (h₄ : e = f) : a = D * f
参数：h₁ : a = b；h₂ : b = c；h₃ : c = D * e；h₄ : e = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_mul_of_eq_eq_eq_mul {M : Type*} [Mul M] {a b c D e f : M}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e) (h₄ : e = f) :
    a = D * f := by
  rw [h₁, h₂, h₃, h₄]
/-
**Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp`。
形式化陈述：eq_eq_cancel_eq {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁
 e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : L != 0) : (e₁ = e₂)
 = (f₁ = f₂)
参数：H₁ : e₁ = L * f₁；H₂ : e₂ = L * f₂；HL : L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_eq_cancel_eq {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : L ≠ 0) :
    (e₁ = e₂) = (f₁ = f₂) := by
  subst H₁ H₂
  rw [mul_right_inj' HL]
/-
**Mathlib.Tactic.FieldSimp.le_eq_cancel_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp`。
形式化陈述：le_eq_cancel_le {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulMon
o M] [PosMulReflectLE M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f
₂) (HL : 0 < L) : (e₁ <= e₂) = (f₁ <= f₂)
参数：H₁ : e₁ = L * f₁；H₂ : e₂ = L * f₂；HL : 0 < L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_eq_cancel_le {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulMono M]
    [PosMulReflectLE M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ ≤ e₂) = (f₁ ≤ f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_le_mul_iff_right₀ HL
/-
**Mathlib.Tactic.FieldSimp.lt_eq_cancel_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp`。
形式化陈述：lt_eq_cancel_lt {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulStr
ictMono M] [PosMulReflectLT M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) (H₂ : e₂ =
 L * f₂) (HL : 0 < L) : (e₁ < e₂) = (f₁ < f₂)
参数：H₁ : e₁ = L * f₁；H₂ : e₂ = L * f₂；HL : 0 < L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulStrictMono α]   [PosMulReflectLT 
α], 0 < a → (a *…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_eq_cancel_lt {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulStrictMono M]
    [PosMulReflectLT M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ < e₂) = (f₁ < f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_lt_mul_iff_of_pos_left HL

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/-- Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.  This is the
form to which the tactics reduce field expressions. -/
/-
**Mathlib.Tactic.FieldSimp.NF** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.FieldSim
p`。
形式化陈述：NF (M : Type*)
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field. 
 This is the
form to which the tactics reduce field expressions.
-/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
/-
**Mathlib.Tactic.FieldSimp.NF.cons** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fie
ldSimp.NF`。
形式化陈述：cons (p : Int × M) (l : NF M) : NF M
参数：p : Int × M；l : NF M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepe
nding another
pair `p : ℤ × M`.
-/
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/-- Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` term to the power of
the corresponding `ℤ` term, then multiply them all together. -/
/-
**Mathlib.Tactic.FieldSimp.NF.eval** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fie
ldSimp.NF`。
形式化陈述：eval [GroupWithZero M] (l : NF M) : M
参数：l : NF M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an e
lement of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` 
term to the power of
the corresponding `ℤ` term, then multiply them all together.
-/
noncomputable def eval [GroupWithZero M] (l : NF M) : M :=
  (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ zpow' x r)).prod

set_option backward.isDefEq.respectTransparency false in
/-
**Mathlib.Tactic.FieldSimp.NF.eval_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.FieldSimp.NF`。
形式化陈述：∀ {M : Type u_1} [inst : CommGroupWithZero M] (p : ℤ × M) (l : Mathlib.Tac
tic.FieldSimp.NF M),   (p ::ᵣ l).eval = l.eval * Mathlib.Tactic.FieldSimp.zpow' 
p.2 p.1
参数：p : ℤ × M；l : Mathlib.Tactic.FieldSimp.NF M；p ::ᵣ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem eval_cons [CommGroupWithZero M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * zpow' p.2 p.1 := by
  unfold eval cons
  simp [mul_comm]
/-
**Mathlib.Tactic.FieldSimp.NF.cons_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp.NF`。
形式化陈述：cons_ne_zero [GroupWithZero M] (r : Int) {x : M} (hx : x != 0) {l : NF M} 
(hl : l.eval != 0) : ((r, x) ::ᵣ l).eval != 0
参数：r : Int；hx : x != 0；hl : l.eval != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem cons_ne_zero [GroupWithZero M] (r : ℤ) {x : M} (hx : x ≠ 0) {l : NF M} (hl : l.eval ≠ 0) :
    ((r, x) ::ᵣ l).eval ≠ 0 := by
  unfold eval cons
  apply mul_ne_zero ?_ hl
  simp [zpow'_eq_zero_iff, hx]
/-
**Mathlib.Tactic.FieldSimp.NF.cons_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.FieldSimp.NF`。
形式化陈述：cons_pos [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulRe
flectLT M] [ZeroLEOneClass M] (r : Int) {x : M} (hx : 0 < x) {l : NF M} (hl : 0 
< l.eval) : 0 < ((r, x) ::ᵣ l).eval
参数：r : Int；hx : 0 < x；hl : 0 < l.eval。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_of_ne_zero_left`：∀ {α : Type u_1} [inst :
 GroupWithZero α] (a : α) (n : ℤ), a ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a n = 
a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
-/
theorem cons_pos [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M]
    [ZeroLEOneClass M] (r : ℤ) {x : M} (hx : 0 < x) {l : NF M} (hl : 0 < l.eval) :
    0 < ((r, x) ::ᵣ l).eval := by
  unfold eval cons
  apply mul_pos ?_ hl
  simp only
  rw [zpow'_of_ne_zero_left _ _ hx.ne']
  apply zpow_pos hx
/-
**Mathlib.Tactic.FieldSimp.NF.atom_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp.NF`。
形式化陈述：atom_eq_eval [GroupWithZero M] (x : M) : x = NF.eval [(1, x)]
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem atom_eq_eval [GroupWithZero M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
/-
**Mathlib.Tactic.FieldSimp.NF.one_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：one_eq_eval [GroupWithZero M] : (1:M) = NF.eval (M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_eval [GroupWithZero M] : (1:M) = NF.eval (M := M) [] := (rfl)
/-
**Mathlib.Tactic.FieldSimp.NF.mul_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) : x₁ * x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval * l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mul_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.mul_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) : x₁ * x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval * l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mul_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_add]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.mul_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) : x₁ * x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval * l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mul_eq_eval₃ [CommGroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.mul_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) : x₁ * x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval * l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]
/-
**Mathlib.Tactic.FieldSimp.NF.div_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) : x₁ / x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval / l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem div_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.div_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) : x₁ / x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval / l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem div_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, sub_eq_add_neg, zpow'_add]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.div_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) : x₁ / x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval / l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem div_eq_eval₃ [CommGroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]
/-
**Mathlib.Tactic.FieldSimp.NF.div_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.
eval) (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) : x₁ / x₂ = l.eval
参数：hx₁ : x₁ = l₁.eval；hx₂ : x₂ = l₂.eval；h : l₁.eval / l₂.eval = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]
/-
**Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.FieldSimp.NF`。
形式化陈述：eval_mul_eval_cons [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
 (h : L.eval * l.eval = l'.eval) : L.eval * ((n, e) ::ᵣ l).eval = ((n, e) ::ᵣ l'
).eval
参数：n : Int；e : M；h : L.eval * l.eval = l'.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem eval_mul_eval_cons [CommGroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    L.eval * ((n, e) ::ᵣ l).eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h, mul_assoc]
/-
**Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：eval_mul_eval_cons_zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (
h : L.eval * l.eval = l'.eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval) : L.eval * l
₀.eval = ((0, e) ::ᵣ l').eval
参数：h : L.eval * l.eval = l'.eval；h' : ((0, e) ::ᵣ l).eval = l₀.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
-/
theorem eval_mul_eval_cons_zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M}
    (h : L.eval * l.eval = l'.eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval) :
    L.eval * l₀.eval = ((0, e) ::ᵣ l').eval := by
  rw [← eval_mul_eval_cons 0 e h, h']
/-
**Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.FieldSimp.NF`。
形式化陈述：eval_cons_mul_eval [CommGroupWithZero M] (n : Int) (e : M) {L l l' : NF M}
 (h : L.eval * l.eval = l'.eval) : ((n, e) ::ᵣ L).eval * l.eval = ((n, e) ::ᵣ l'
).eval
参数：n : Int；e : M；h : L.eval * l.eval = l'.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem eval_cons_mul_eval [CommGroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * l.eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg** 是 Mathlib 中的一个定理，位于命
名空间 `Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：eval_cons_mul_eval_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : 
e != 0) {L l l' : NF M} (h : L.eval * l.eval = l'.eval) : ((n, e) ::ᵣ L).eval * 
((-n, e) ::ᵣ l).eval = l'.eval
参数：n : Int；he : e != 0；h : L.eval * l.eval = l'.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_zero_of_ne_zero`：∀ {α : Type u_1} [inst :
 GroupWithZero α] {a : α}, a ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_cons_mul_eval_cons_neg [CommGroupWithZero M] (n : ℤ) {e : M} (he : e ≠ 0)
    {L l l' : NF M} (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * ((-n, e) ::ᵣ l).eval = l'.eval := by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]
/-
**Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.FieldSimp.NF`。
形式化陈述：cons_eq_div_of_eq_div [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d :
 NF M} (h : t.eval = t_n.eval / t_d.eval) : ((n, e) ::ᵣ t).eval = ((n, e) ::ᵣ t_
n).eval / t_d.eval
参数：n : Int；e : M；h : t.eval = t_n.eval / t_d.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem cons_eq_div_of_eq_div [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((n, e) ::ᵣ t).eval = ((n, e) ::ᵣ t_n).eval / t_d.eval := by
  simp only [eval_cons, h, div_eq_mul_inv]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：cons_eq_div_of_eq_div' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d 
: NF M} (h : t.eval = t_n.eval / t_d.eval) : ((-n, e) ::ᵣ t).eval = t_n.eval / (
(n, e) ::ᵣ t_d).eval
参数：n : Int；e : M；h : t.eval = t_n.eval / t_d.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_neg`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α) (n : ℤ),   Mathlib.Tactic.FieldSimp.zpow' a (-n) = (Mathlib.Tactic
.FieldSimp.zpow' a n)⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem cons_eq_div_of_eq_div' [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((-n, e) ::ᵣ t).eval = t_n.eval / ((n, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.cons_zero_eq_div_of_eq_div** 是 Mathlib 中的一个定理，位于命名
空间 `Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：cons_zero_eq_div_of_eq_div [CommGroupWithZero M] (e : M) {t t_n t_d : NF M
} (h : t.eval = t_n.eval / t_d.eval) : ((0, e) ::ᵣ t).eval = ((1, e) ::ᵣ t_n).ev
al / ((1, e) ::ᵣ t_d).eval
参数：e : M；h : t.eval = t_n.eval / t_d.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_add`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α) (m n : ℤ),   Mathlib.Tactic.FieldSimp.zpow' a (m + n) = Mathlib.Ta
ctic.FieldSimp.zpow' a m…
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem cons_zero_eq_div_of_eq_div [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((0, e) ::ᵣ t).eval = ((1, e) ::ᵣ t_n).eval / ((1, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, ← zpow'_neg, ← add_neg_cancel (1:ℤ), zpow'_add]
  ac_rfl
/-
**Mathlib.Tactic.FieldSimp.NF.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.FieldSi
mp.NF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

set_option backward.isDefEq.respectTransparency false in
/-
**Mathlib.Tactic.FieldSimp.NF.eval_inv** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.FieldSimp.NF`。
形式化陈述：eval_inv [CommGroupWithZero M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹
参数：l : NF M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prod_inv`：∀ {K : Type u_8} [inst : DivisionCommMonoid K] (L : List 
K), L.prod⁻¹ = (List.map (fun x => x⁻¹) L).prod
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_neg`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α) (n : ℤ),   Mathlib.Tactic.FieldSimp.zpow' a (-n) = (Mathlib.Tactic
.FieldSimp.zpow' a n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_inv [CommGroupWithZero M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp +instances only [NF.eval, List.map_map, NF.instInv, List.prod_inv]
  congr! 2
  ext p
  simp [zpow'_neg]
/-
**Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.FieldSimp.NF`。
形式化陈述：one_div_eq_eval [CommGroupWithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
参数：l : NF M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_inv`：eval_inv [CommGroupWithZero M] (l 
: NF M) : (l⁻¹).eval = l.eval⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_eq_eval [CommGroupWithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]
/-
**Mathlib.Tactic.FieldSimp.NF.inv_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：inv_eq_eval [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval) : x⁻
¹ = (l⁻¹).eval
参数：h : x = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_inv`：eval_inv [CommGroupWithZero M] (l 
: NF M) : (l⁻¹).eval = l.eval⁻¹
-/
theorem inv_eq_eval [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]
/-
**Mathlib.Tactic.FieldSimp.NF.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.FieldSi
mp.NF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)
/-
**Mathlib.Tactic.FieldSimp.NF.zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.FieldSimp.NF`。
形式化陈述：∀ {M : Type u_1} (r : ℤ) (l : Mathlib.Tactic.FieldSimp.NF M),   l ^ r =   
  List.map       (fun x =>         match x with         | (a, x) => (r * a, x)) 
      l
参数：r : ℤ；l : Mathlib.Tactic.FieldSimp.NF M；fun x =>         match x with        
 | (a, x) => (r * a, x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Mathlib.Tactic.FieldSimp.NF.eval_zpow'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.FieldSimp.NF`。
形式化陈述：eval_zpow' [CommGroupWithZero M] (l : NF M) (r : Int) : (l ^ r).eval = zpo
w' l.eval r
参数：l : NF M；r : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.list_prod_zpow'`：list_prod_zpow' [CommGroupWith
Zero α] {r : Int} {l : List α} : zpow' (prod l) r = prod (map (fun x => zpow' x 
r) l)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_zpow' [CommGroupWithZero M] (l : NF M) (r : ℤ) :
    (l ^ r).eval = zpow' l.eval r := by
  unfold NF.eval at ⊢
  simp only [zpow_apply, list_prod_zpow', map_map]
  congr! 2
  ext p
  simp [← zpow'_mul, mul_comm]
/-
**Mathlib.Tactic.FieldSimp.NF.zpow_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.FieldSimp.NF`。
形式化陈述：zpow_eq_eval [CommGroupWithZero M] {l : NF M} {r : Int} (hr : r != 0) {x :
 M} (hx : x = l.eval) : x ^ r = (l ^ r).eval
参数：hr : r != 0；hx : x = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_of_ne_zero_right`：∀ {α : Type u_1} [inst 
: GroupWithZero α] (a : α) (n : ℤ), n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a n =
 a ^ n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_zpow'`：eval_zpow' [CommGroupWithZero M]
 (l : NF M) (r : Int) : (l ^ r).eval = zpow' l.eval r
-/
theorem zpow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℤ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [← zpow'_of_ne_zero_right x r hr, eval_zpow', hx]
/-
**Mathlib.Tactic.FieldSimp.NF.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.FieldSi
mp.NF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (NF M) ℕ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)
/-
**Mathlib.Tactic.FieldSimp.NF.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.FieldSimp.NF`。
形式化陈述：∀ {M : Type u_1} (r : ℕ) (l : Mathlib.Tactic.FieldSimp.NF M),   l ^ r =   
  List.map       (fun x =>         match x with         | (a, x) => (↑r * a, x))
       l
参数：r : ℕ；l : Mathlib.Tactic.FieldSimp.NF M；fun x =>         match x with        
 | (a, x) => (↑r * a, x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem pow_apply (r : ℕ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl
/-
**Mathlib.Tactic.FieldSimp.NF.eval_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.FieldSimp.NF`。
形式化陈述：eval_pow [CommGroupWithZero M] (l : NF M) (r : Nat) : (l ^ r).eval = zpow'
 l.eval r
参数：l : NF M；r : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_zpow'`：eval_zpow' [CommGroupWithZero M]
 (l : NF M) (r : Int) : (l ^ r).eval = zpow' l.eval r
-/
theorem eval_pow [CommGroupWithZero M] (l : NF M) (r : ℕ) : (l ^ r).eval = zpow' l.eval r :=
  eval_zpow' l r
/-
**Mathlib.Tactic.FieldSimp.NF.pow_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.FieldSimp.NF`。
形式化陈述：pow_eq_eval [CommGroupWithZero M] {l : NF M} {r : Nat} (hr : r != 0) {x : 
M} (hx : x = l.eval) : x ^ r = (l ^ r).eval
参数：hr : r != 0；hx : x = l.eval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_pow`：eval_pow [CommGroupWithZero M] (l 
: NF M) (r : Nat) : (l ^ r).eval = zpow' l.eval r
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
-/
theorem pow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℕ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_pow, hx]
  rw [zpow'_ofNat _ hr]
/-
**Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：eval_cons_of_pow_eq_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x :
 M} (hx : x != 0) (l : NF M) : ((r, x) ::ᵣ l).eval = NF.eval l
参数：hr : r = 0；hx : x != 0；l : NF M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_zero_of_ne_zero`：∀ {α : Type u_1} [inst :
 GroupWithZero α] {a : α}, a ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_cons_of_pow_eq_zero [CommGroupWithZero M] {r : ℤ} (hr : r = 0) {x : M} (hx : x ≠ 0)
    (l : NF M) :
    ((r, x) ::ᵣ l).eval = NF.eval l := by
  simp [hr, zpow'_zero_of_ne_zero hx]
/-
**Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq** 是 Mathlib 中的一个定理，位
于命名空间 `Mathlib.Tactic.FieldSimp.NF`。
形式化陈述：eval_cons_eq_eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t
' l' : NF M} (h : NF.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').eval = NF.eval l
') : ((r, x) ::ᵣ t).eval = NF.eval l'
参数：r : Int；x : M；h : NF.eval t = NF.eval t'；h' : ((r, x) ::ᵣ t').eval = NF.eval 
l'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
-/
theorem eval_cons_eq_eval_of_eq_of_eq [CommGroupWithZero M] (r : ℤ) (x : M) {t t' l' : NF M}
    (h : NF.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').eval = NF.eval l') :
    ((r, x) ::ᵣ t).eval = NF.eval l' := by
  rw [← h', eval_cons, eval_cons, h]

end NF
end

/-! ### Negations of algebraic operations -/

@[expose] public meta section Sign
open Lean Qq

variable {v : Level} {M : Q(Type v)}

/-- Inductive type representing the options for the sign of an element in a type-expression `M`

If the sign is "-", then we also carry an expression for a field instance on `M`, to allow us to
construct that negation when needed. -/
/-
**Mathlib.Tactic.FieldSimp.Sign** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Fiel
dSimp`。
形式化陈述：{v : Level} → Q(Type v) → Type
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductive type representing the options for the sign of an element in a type-exp
ression `M`

If the sign is "-", then we also carry an expression for a field instance on `M`
, to allow us to
construct that negation when needed.
-/
inductive Sign (M : Q(Type v))
  | plus
  | minus (iM : Q(Field $M))

/-- Given an expression `e : Q($M)`, construct an expression which is morally "± `e`", with the
choice between + and - determined by an object `g : Sign M`. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.expr** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.F
ieldSimp.Sign`。
形式化陈述：{v : Level} → {M : Q(Type v)} → Mathlib.Tactic.FieldSimp.Sign M → Q(«$M») 
→ Q(«$M»)
参数：Type v；«$M»；«$M»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `e : Q($M)`, construct an expression which is morally "± `e`
", with the
choice between + and - determined by an object `g : Sign M`.
-/
def Sign.expr : Sign M → Q($M) → Q($M)
  | plus, a => a
  | minus _, a => q(-$a)

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the product with `c` of (± `y`) (here taking the specified sign) is ± `c * y`. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.FieldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (c y : Q(«$M»)) →         (g : Mathlib.Tactic.FieldSimp.Sign M) →          
 MetaM             (have a := g.expr y;             have a_1 := g.expr q(«$c» * 
«$y»);             Q(«$a_1» = «$c» * «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；c y : Q(«$M»)；g : Mathlib.Tactic.FieldS
imp.Sign M；have a := g.expr y;             have a_1 := g.expr q(«$c» * «$y»);   
          Q(«$a_1» = «$c» * «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `y : Q($M)` with specified sign (either + or -), construct a
 proof that
the product with `c` of (± `y`) (here taking the specified sign) is ± `c * y`.
-/
def Sign.mulRight (iM : Q(CommGroupWithZero $M)) (c y : Q($M)) (g : Sign M) :
    MetaM Q($(g.expr q($c * $y)) = $c * $(g.expr y)) := do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(Eq.symm (mul_neg $c _))

/-- Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construct a proof that
the product of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁ * y₂`; return this
proof and the computed sign. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.mul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fi
eldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (y₁ y₂ : Q(«$M»)) →         (g₁ g₂ : Mathlib.Tactic.FieldSimp.Sign M) →    
       MetaM             ((G : Mathlib.Tactic.FieldSimp.Sign M) ×               
have a := G.expr q(«$y₁» * «$y₂»);               have a_1 := g₂.expr y₂;        
       have a_2 := g₁.expr y₁;               Q(«$a_2» * «$a_1» = «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；y₁ y₂ : Q(«$M»)；g₁ g₂ : Mathlib.Tactic.
FieldSimp.Sign M；(G : Mathlib.Tactic.FieldSimp.Sign M) ×               have a :=
 G.expr q(«$y₁» * «$y₂»);               have a_1 := g₂.expr y₂;               ha
ve a_2 := g₁.expr y₁;               Q(«$a_2» * «$a_1» = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construc
t a proof that
the product of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁ 
* y₂`; return this
proof and the computed sign.
-/
def Sign.mul (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) * $(g₂.expr y₂) = $(G.expr q($y₁ * $y₂)))) := do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(mul_neg $y₁ $y₂)⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_mul $y₁ $y₂)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_mul_neg $y₁ $y₂)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the inverse of (± `y`) (here taking the specified sign) is ± `y⁻¹`. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.inv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fi
eldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (y : Q(«$M»)) →         (g : Mathlib.Tactic.FieldSimp.Sign M) →           M
etaM             (have a := g.expr q(«$y»⁻¹);             have a_1 := g.expr y; 
            Q(«$a_1»⁻¹ = «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；y : Q(«$M»)；g : Mathlib.Tactic.FieldSim
p.Sign M；have a := g.expr q(«$y»⁻¹);             have a_1 := g.expr y;          
   Q(«$a_1»⁻¹ = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `y : Q($M)` with specified sign (either + or -), construct a
 proof that
the inverse of (± `y`) (here taking the specified sign) is ± `y⁻¹`.
-/
def Sign.inv (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Q($(g.expr y)⁻¹ = $(g.expr q($y⁻¹)))) := do
  match (dependent := true) g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(inv_neg (a := $y))

/-- Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construct a proof that
the quotient of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁ / y₂`; return this
proof and the computed sign. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.div** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fi
eldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (y₁ y₂ : Q(«$M»)) →         (g₁ g₂ : Mathlib.Tactic.FieldSimp.Sign M) →    
       MetaM             ((G : Mathlib.Tactic.FieldSimp.Sign M) ×               
have a := G.expr q(«$y₁» / «$y₂»);               have a_1 := g₂.expr y₂;        
       have a_2 := g₁.expr y₁;               Q(«$a_2» / «$a_1» = «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；y₁ y₂ : Q(«$M»)；g₁ g₂ : Mathlib.Tactic.
FieldSimp.Sign M；(G : Mathlib.Tactic.FieldSimp.Sign M) ×               have a :=
 G.expr q(«$y₁» / «$y₂»);               have a_1 := g₂.expr y₂;               ha
ve a_2 := g₁.expr y₁;               Q(«$a_2» / «$a_1» = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construc
t a proof that
the quotient of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁
 / y₂`; return this
proof and the computed sign.
-/
def Sign.div (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) / $(g₂.expr y₂) = $(G.expr q($y₁ / $y₂)))) := do
  match (dependent := true) g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(div_neg $y₁ (b := $y₂))⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_div $y₂ $y₁)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_div_neg_eq $y₁ $y₂)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the negation of (± `y`) (here taking the specified sign) is ∓ `y`. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.neg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fi
eldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(Field «$M»)) →       (y : Q(
«$M»)) →         (g : Mathlib.Tactic.FieldSimp.Sign M) →           MetaM        
     ((G : Mathlib.Tactic.FieldSimp.Sign M) ×               have a := G.expr y; 
              have a_1 := g.expr y;               Q(-«$a_1» = «$a»))
参数：Type v；iM : Q(Field «$M»)；y : Q(«$M»)；g : Mathlib.Tactic.FieldSimp.Sign M；(G 
: Mathlib.Tactic.FieldSimp.Sign M) ×               have a := G.expr y;          
     have a_1 := g.expr y;               Q(-«$a_1» = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `y : Q($M)` with specified sign (either + or -), construct a
 proof that
the negation of (± `y`) (here taking the specified sign) is ∓ `y`.
-/
def Sign.neg (iM : Q(Field $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Σ (G : Sign M), Q(-$(g.expr y) = $(G.expr y))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.minus iM, q(rfl)⟩
  | .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_neg $y)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the exponentiation to power `s : ℕ` of (± `y`) (here taking the specified signs) is ± `y ^ s`;
return this proof and the computed sign. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.pow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Fi
eldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (y : Q(«$M»)) →         (g : Mathlib.Tactic.FieldSimp.Sign M) →           (
s : ℕ) →             MetaM               ((G : Mathlib.Tactic.FieldSimp.Sign M) 
×                 have a := G.expr q(«$y» ^ «$s»);                 have a_1 := g
.expr y;                 Q(«$a_1» ^ «$s» = «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；y : Q(«$M»)；g : Mathlib.Tactic.FieldSim
p.Sign M；s : ℕ；(G : Mathlib.Tactic.FieldSimp.Sign M) ×                 have a :=
 G.expr q(«$y» ^ «$s»);                 have a_1 := g.expr y;                 Q(
«$a_1» ^ «$s» = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `y : Q($M)` with specified sign (either + or -), construct a
 proof that
the exponentiation to power `s : ℕ` of (± `y`) (here taking the specified signs)
 is ± `y ^ s`;
return this proof and the computed sign.
-/
def Sign.pow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : ℕ) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_pow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_pow $pf_s $y)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the exponentiation to power `s : ℤ` of (± `y`) (here taking the specified signs) is ± `y ^ s`;
return this proof and the computed sign. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.zpow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.F
ieldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     (y : Q(«$M»)) →         (g : Mathlib.Tactic.FieldSimp.Sign M) →           (
s : ℤ) →             MetaM               ((G : Mathlib.Tactic.FieldSimp.Sign M) 
×                 have a := G.expr q(«$y» ^ «$s»);                 have a_1 := g
.expr y;                 Q(«$a_1» ^ «$s» = «$a»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；y : Q(«$M»)；g : Mathlib.Tactic.FieldSim
p.Sign M；s : ℤ；(G : Mathlib.Tactic.FieldSimp.Sign M) ×                 have a :=
 G.expr q(«$y» ^ «$s»);                 have a_1 := g.expr y;                 Q(
«$a_1» ^ «$s» = «$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an expression `y : Q($M)` with specified sign (either + or -), construct a
 proof that
the exponentiation to power `s : ℤ` of (± `y`) (here taking the specified signs)
 is ± `y ^ s`;
return this proof and the computed sign.
-/
def Sign.zpow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : ℤ) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match (dependent := true) g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_zpow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_zpow $pf_s $y)⟩

/-- Given a proof that two expressions `y₁ y₂ : Q($M)` are equal, construct a proof that (± `y₁`)
and (± `y₂`) are equal, where the same sign is taken in both expression. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.congr** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
FieldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     {y y' : Q(«$M»)} →       (g : Mathli
b.Tactic.FieldSimp.Sign M) →         Q(«$y» = «$y'») →           have a := g.exp
r y';           have a_1 := g.expr y;           Q(«$a_1» = «$a»)
参数：Type v；«$M»；g : Mathlib.Tactic.FieldSimp.Sign M；«$y» = «$y'»。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a proof that two expressions `y₁ y₂ : Q($M)` are equal, construct a proof 
that (± `y₁`)
and (± `y₂`) are equal, where the same sign is taken in both expression.
-/
def Sign.congr {y y' : Q($M)} (g : Sign M) (pf : Q($y = $y')) : Q($(g.expr y)= $(g.expr y')) :=
  match g with
  | .plus => pf
  | .minus _ => q(congr_arg Neg.neg $pf)

/-- If `a` = ± `b`, `b = C * d`, and `d = e`, construct a proof that `a` = `C` * ± `e`. -/
/-
**Mathlib.Tactic.FieldSimp.Sign.mkEqMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.FieldSimp.Sign`。
形式化陈述：{v : Level} →   {M : Q(Type v)} →     (iM : Q(CommGroupWithZero «$M»)) →  
     {a b C d e : Q(«$M»)} →         {g : Mathlib.Tactic.FieldSimp.Sign M} →    
       (have a_1 := g.expr b;             Q(«$a» = «$a_1»)) →             Q(«$b»
 = «$C» * «$d») →               Q(«$d» = «$e») →                 MetaM          
         (have a_1 := g.expr e;                   Q(«$a» = «$C» * «$a_1»))
参数：Type v；iM : Q(CommGroupWithZero «$M»)；«$M»；have a_1 := g.expr b;             
Q(«$a» = «$a_1»)；«$b» = «$C» * «$d»；«$d» = «$e»；have a_1 := g.expr e;           
        Q(«$a» = «$C» * «$a_1»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a` = ± `b`, `b = C * d`, and `d = e`, construct a proof that `a` = `C` * ± `
e`.
-/
def Sign.mkEqMul (iM : Q(CommGroupWithZero $M)) {a b C d e : Q($M)} {g : Sign M}
      (pf₁ : Q($a = $(g.expr b))) (pf₂ : Q($b = $C * $d))
      (pf₃ : Q($d = $e)) : MetaM Q($a = $C * $(g.expr e)) := do
    let pf₂' : Q($(g.expr b) = $(g.expr q($C * $d))) := g.congr pf₂
    let pf' ← Sign.mulRight iM C d g
    pure q(eq_mul_of_eq_eq_eq_mul $pf₁ $pf₂' $pf' $(g.congr pf₃))

end Sign

end Mathlib.Tactic.FieldSimp

