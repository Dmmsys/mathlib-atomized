/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Unique

/-!
# The unit of the natural numbers
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Units -/

/-
**Nat.units_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：units_eq_one (u : Natˣ) : u = 1
参数：u : Natˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Nat.eq_one_of_dvd_one`：∀ {n : ℕ}, n ∣ 1 → n = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1

--- 原说明 ---
#### Units
-/
lemma units_eq_one (u : ℕˣ) : u = 1 := Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩
/-
**Nat.addUnits_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：addUnits_eq_zero (u : AddUnits Nat) : u = 0
参数：u : AddUnits Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddUnits.ext`：∀ {α : Type u} [inst : AddMonoid α] {u v : AddUnits α}, ↑u
 = ↑v → u = v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.eq_zero_of_add_eq_zero`：∀ {n m : ℕ}, n + m = 0 → n = 0 ∧ m = 0
· 使用定理 `AddUnits.val_neg`：∀ {α : Type u} [inst : AddMonoid α] (self : AddUnits α
), ↑self + self.neg = 0
-/
lemma addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1
/-
**Nat.unique_units** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：unique_units : Unique Natˣ where default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.units_eq_one`：units_eq_one (u : Natˣ) : u = 1
-/
instance unique_units : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one
/-
**Nat.unique_addUnits** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：unique_addUnits : Unique (AddUnits Nat) where default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.addUnits_eq_zero`：addUnits_eq_zero (u : AddUnits Nat) : u = 0
-/
instance unique_addUnits : Unique (AddUnits ℕ) where
  default := 0
  uniq := Nat.addUnits_eq_zero

/-- Alias of `isUnit_iff_eq_one` for discoverability. -/
/-
**Nat.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, IsUnit n ↔ n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isUnit_iff_eq_one`：isUnit_iff_eq_one : IsUnit a ↔ a = 1 where mp
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Alias of `isUnit_iff_eq_one` for discoverability.
-/
protected lemma isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 := isUnit_iff_eq_one

/-- Alias of `isAddUnit_iff_eq_zero` for discoverability. -/
/-
**Nat.isAddUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, IsAddUnit n ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAddUnit_iff_eq_zero`：∀ {M : Type u_1} [inst : AddMonoid M] {a : M} [Su
bsingleton (AddUnits M)], IsAddUnit a ↔ a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Alias of `isAddUnit_iff_eq_zero` for discoverability.
-/
protected lemma isAddUnit_iff {n : ℕ} : IsAddUnit n ↔ n = 0 := isAddUnit_iff_eq_zero

end Nat

