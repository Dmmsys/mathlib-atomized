/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `ZMod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

* A coercion `cast` is defined from `ZMod n` into any ring.
  This is a ring hom if the ring has characteristic dividing `n`

-/

@[expose] public section

assert_not_exists Field Submodule TwoSidedIdeal

open Function ZMod

namespace ZMod

/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain (ZMod 0) := inferInstanceAs (IsDomain ℤ)

/-- For non-zero `n : ℕ`, the ring `Fin n` is equivalent to `ZMod n`. -/
/-
**ZMod.finEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：(n : ℕ) → [NeZero n] → Fin n ≃+* ZMod n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For non-zero `n : ℕ`, the ring `Fin n` is equivalent to `ZMod n`.
-/
def finEquiv : ∀ (n : ℕ) [NeZero n], Fin n ≃+* ZMod n
  | 0, h => (h.ne _ rfl).elim
  | _ + 1, _ => .refl _
/-
**ZMod.charZero** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：charZero : CharZero (ZMod 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance charZero : CharZero (ZMod 0) := inferInstanceAs (CharZero ℤ)

/-- `val a` is a natural number defined as:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

See `ZMod.valMinAbs` for a variant that takes values in the integers.
-/
/-
**ZMod.val** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：{n : ℕ} → ZMod n → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`val a` is a natural number defined as:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivale
nce class

See `ZMod.valMinAbs` for a variant that takes values in the integers.
-/
def val : ∀ {n : ℕ}, ZMod n → ℕ
  | 0 => Int.natAbs
  | n + 1 => ((↑) : Fin (n + 1) → ℕ)
/-
**ZMod.val_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
参数：a : ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem val_lt {n : ℕ} [NeZero n] (a : ZMod n) : a.val < n := by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a

grind_pattern val_lt => a.val
/-
**ZMod.val_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_le {n : Nat} [NeZero n] (a : ZMod n) : a.val <= n
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
-/
theorem val_le {n : ℕ} [NeZero n] (a : ZMod n) : a.val ≤ n :=
  a.val_lt.le

@[simp]
/-
**ZMod.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ}, ZMod.val 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_zero : ∀ {n}, (0 : ZMod n).val = 0
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
/-
**ZMod.val_one'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_one' : (1 : ZMod 0).val = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_one' : (1 : ZMod 0).val = 1 :=
  rfl

@[simp]
/-
**ZMod.val_neg'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_neg' {n : ZMod 0} : (-n).val = n.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
-/
theorem val_neg' {n : ZMod 0} : (-n).val = n.val :=
  Int.natAbs_neg n

@[simp]
/-
**ZMod.val_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
-/
theorem val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val :=
  Int.natAbs_mul m n

@[simp]
/-
**ZMod.val_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
参数：n a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_natCast`：∀ (a n : ℕ) [inst : NeZero n], ↑↑a = a % n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem val_natCast (n a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast
/-
**ZMod.val_natCast_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_natCast_of_lt {n a : Nat} (h : a < n) : (a : ZMod n).val = a
参数：h : a < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
lemma val_natCast_of_lt {n a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rwa [val_natCast, Nat.mod_eq_of_lt]
/-
**ZMod.val_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_ofNat (n a : Nat) [a.AtLeastTwo] : (ofNat(a) : ZMod n).val = ofNat(a) 
% n
参数：n a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
-/
lemma val_ofNat (n a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ZMod n).val = ofNat(a) % n := val_natCast ..
/-
**ZMod.val_ofNat_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_ofNat_of_lt {n a : Nat} [a.AtLeastTwo] (han : a < n) : (ofNat(a) : ZMo
d n).val = ofNat(a)
参数：han : a < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.val_natCast_of_lt`：val_natCast_of_lt {n a : Nat} (h : a < n) : (a :
 ZMod n).val = a
-/
lemma val_ofNat_of_lt {n a : ℕ} [a.AtLeastTwo] (han : a < n) : (ofNat(a) : ZMod n).val = ofNat(a) :=
  val_natCast_of_lt han

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.val_unit'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.isUnit_iff`：isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1
· 使用定理 `Int.natAbs_eq_iff`：∀ {a : ℤ} {n : ℕ}, a.natAbs = n ↔ a = ↑n ∨ a = -↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1 := by
  simp only [val]
  rw [Int.isUnit_iff, Int.natAbs_eq_iff, Nat.cast_one]
/-
**ZMod.eq_one_of_isUnit_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：eq_one_of_isUnit_natCast {n : Nat} (h : IsUnit (n : ZMod 0)) : n = 1
参数：h : IsUnit (n : ZMod 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.val_unit'`：val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1
-/
lemma eq_one_of_isUnit_natCast {n : ℕ} (h : IsUnit (n : ZMod 0)) : n = 1 := by
  rw [← Nat.mod_zero n, ← val_natCast, val_unit'.mp h]
/-
**ZMod.charP** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：charP (n : Nat) : CharP (ZMod n) n where cast_eq_zero_iff
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Fin.natCast_eq_zero`：∀ {a n : ℕ} [inst : NeZero n], ↑a = 0 ↔ n ∣ a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
instance charP (n : ℕ) : CharP (ZMod n) n where
  cast_eq_zero_iff := by
    intro k
    rcases n with - | n
    · simp
    · exact Fin.natCast_eq_zero

-- Verify that `grind` can see that `ZMod n` has characteristic `n`.
/-
**ZMod.** 是 Mathlib 中的一个示例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n : ℕ) : Lean.Grind.IsCharP (ZMod n) n := inferInstance

@[simp]
/-
**ZMod.addOrderOf_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：addOrderOf_one (n : Nat) : addOrderOf (1 : ZMod n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
· 使用引理 `CharP.addOrderOf_one`：CharP.addOrderOf_one : CharP R (addOrderOf (1 : R)
) where cast_eq_zero_iff n
-/
theorem addOrderOf_one (n : ℕ) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)

/-- This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`.  The version
where `a ≠ 0` is `addOrderOf_coe'`. -/
@[simp]
/-
**ZMod.addOrderOf_coe** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：addOrderOf_coe (a : Nat) {n : Nat} (n0 : n != 0) : addOrderOf (a : ZMod n)
 = n / n.gcd a
参数：a : Nat；n0 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `addOrderOf_zero`：∀ {G : Type u_1} [inst : AddMonoid G], addOrderOf 0 = 1
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `addOrderOf_nsmul'`：∀ {G : Type u_1} [inst : AddMonoid G] (x : G) {n : ℕ}
, n ≠ 0 → addOrderOf (n • x) = addOrderOf x / (addOrderOf x).gcd n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `ZMod.addOrderOf_one`：addOrderOf_one (n : Nat) : addOrderOf (1 : ZMod n) 
= n

--- 原说明 ---
This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`.  T
he version
where `a ≠ 0` is `addOrderOf_coe'`.
-/
theorem addOrderOf_coe (a : ℕ) {n : ℕ} (n0 : n ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rcases a with - | a
  · simp only [Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a.succ_ne_zero, ZMod.addOrderOf_one]

/-- This lemma works in the case in which `a ≠ 0`.  The version where
`ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`. -/
@[simp]
/-
**ZMod.addOrderOf_coe'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：addOrderOf_coe' {a : Nat} (n : Nat) (a0 : a != 0) : addOrderOf (a : ZMod n
) = n / n.gcd a
参数：n : Nat；a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `addOrderOf_nsmul'`：∀ {G : Type u_1} [inst : AddMonoid G] (x : G) {n : ℕ}
, n ≠ 0 → addOrderOf (n • x) = addOrderOf x / (addOrderOf x).gcd n
· 使用定理 `ZMod.addOrderOf_one`：addOrderOf_one (n : Nat) : addOrderOf (1 : ZMod n) 
= n

--- 原说明 ---
This lemma works in the case in which `a ≠ 0`.  The version where
`ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`.
-/
theorem addOrderOf_coe' {a : ℕ} (n : ℕ) (a0 : a ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a0, ZMod.addOrderOf_one]

/-- We have that `ringChar (ZMod n) = n`. -/
/-
**ZMod.ringChar_zmod_n** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringChar.eq_iff`：eq_iff {p : Nat} : ringChar R = p ↔ CharP R p

--- 原说明 ---
We have that `ringChar (ZMod n) = n`.
-/
theorem ringChar_zmod_n (n : ℕ) : ringChar (ZMod n) = n := by
  rw [ringChar.eq_iff]
  exact ZMod.charP n
/-
**ZMod.natCast_self** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_self (n : Nat) : (n : ZMod n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
-/
theorem natCast_self (n : ℕ) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n

@[simp]
/-
**ZMod.natCast_self'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_self' (n : Nat) : (n + 1 : ZMod (n + 1)) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
-/
theorem natCast_self' (n : ℕ) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one, natCast_self (n + 1)]

@[aesop unsafe 75%]
/-
**ZMod.natCast_pow_eq_zero_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：natCast_pow_eq_zero_of_le (p : Nat) {m n : Nat} (h : n <= m) : (p ^ m : ZM
od (p ^ n)) = 0
参数：p : Nat；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natCast_pow_eq_zero_of_le (p : ℕ) {m n : ℕ} (h : n ≤ m) :
    (p ^ m : ZMod (p ^ n)) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← Nat.cast_pow]
  simp

section UniversalProperty

variable {n : ℕ} {R : Type*}

section

variable [AddGroupWithOne R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `ZMod.castHom` for a bundled version. -/
/-
**ZMod.cast** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：{R : Type u_1} → [AddGroupWithOne R] → {n : ℕ} → ZMod n → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `ZMod.castHom` for a bundled version.
-/
def cast : ∀ {n : ℕ}, ZMod n → R
  | 0 => Int.cast
  | _ + 1 => fun i => i.val


@[simp]
/-
**ZMod.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_zero : (cast (0 : ZMod n) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_zero : (cast (0 : ZMod n) : R) = 0 := by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp
/-
**ZMod.cast_eq_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a.val
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a.val := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

variable {S : Type*} [AddGroupWithOne S]

@[simp]
/-
**ZMod._root_.Prod.fst_zmod_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.fst_zmod_cast (a : ZMod n) : (cast a : R × S).fst = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

@[simp]
/-
**ZMod._root_.Prod.snd_zmod_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.snd_zmod_cast (a : ZMod n) : (cast a : R × S).snd = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

end

/-- So-named because the coercion is `Nat.cast` into `ZMod`. For `Nat.cast` into an arbitrary ring,
see `ZMod.natCast_val`. -/
/-
**ZMod.natCast_zmod_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a

--- 原说明 ---
So-named because the coercion is `Nat.cast` into `ZMod`. For `Nat.cast` into an 
arbitrary ring,
see `ZMod.natCast_val`.
-/
theorem natCast_zmod_val {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self
/-
**ZMod.natCast_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : Nat -> 
ZMod n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
-/
theorem natCast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : ℕ → ZMod n) :=
  natCast_zmod_val
/-
**ZMod.natCast_zmod_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : Nat -> ZMo
d n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `ZMod.natCast_rightInverse`：natCast_rightInverse [NeZero n] : Function.Ri
ghtInverse val ((↑) : Nat -> ZMod n)
-/
theorem natCast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : ℕ → ZMod n) :=
  natCast_rightInverse.surjective

set_option backward.isDefEq.respectTransparency false in
/-- So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` into an arbitrary
ring, see `ZMod.intCast_cast`. -/
@[norm_cast]
/-
**ZMod.intCast_zmod_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_zmod_cast (a : ZMod n) : ((cast a : Int) : ZMod n) = a
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` in
to an arbitrary
ring, see `ZMod.intCast_cast`.
-/
theorem intCast_zmod_cast (a : ZMod n) : ((cast a : ℤ) : ZMod n) = a := by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast]
    rw [Int.cast_natCast, natCast_zmod_val]
/-
**ZMod.intCast_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_rightInverse : Function.RightInverse (cast : ZMod n -> Int) ((↑) :
 Int -> ZMod n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
theorem intCast_rightInverse : Function.RightInverse (cast : ZMod n → ℤ) ((↑) : ℤ → ZMod n) :=
  intCast_zmod_cast
/-
**ZMod.intCast_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_surjective : Function.Surjective ((↑) : Int -> ZMod n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `ZMod.intCast_rightInverse`：intCast_rightInverse : Function.RightInverse 
(cast : ZMod n -> Int) ((↑) : Int -> ZMod n)
-/
theorem intCast_surjective : Function.Surjective ((↑) : ℤ → ZMod n) :=
  intCast_rightInverse.surjective
/-
**ZMod.** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {P : ZMod n → Prop} : (∀ x, P x) ↔ ∀ x : ℤ, P x := intCast_surjective.forall
/-
**ZMod.** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {P : ZMod n → Prop} : (∃ x, P x) ↔ ∃ x : ℤ, P x := intCast_surjective.exists
/-
**ZMod.cast_id** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ) (i : ZMod n), i.cast = i
参数：n : ℕ；i : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cast_id : ∀ (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
  | 0, _ => Int.cast_id
  | _ + 1, i => natCast_zmod_val i

@[simp]
/-
**ZMod.cast_id'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZMod.cast_id`：∀ (n : ℕ) (i : ZMod n), i.cast = i
-/
theorem cast_id' : (ZMod.cast : ZMod n → ZMod n) = id :=
  funext (cast_id n)

variable (R) [Ring R]

/-- The coercions are respectively `Nat.cast` and `ZMod.cast`. -/
@[simp]
/-
**ZMod.natCast_comp_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_comp_val [NeZero n] : ((↑) : Nat -> R) ∘ (val : ZMod n -> Nat) = c
ast
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The coercions are respectively `Nat.cast` and `ZMod.cast`.
-/
theorem natCast_comp_val [NeZero n] : ((↑) : ℕ → R) ∘ (val : ZMod n → ℕ) = cast := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`. -/
@[simp]
/-
**ZMod.intCast_comp_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_comp_cast : ((↑) : Int -> R) ∘ (cast : ZMod n -> Int) = cast
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`.
-/
theorem intCast_comp_cast : ((↑) : ℤ → R) ∘ (cast : ZMod n → ℤ) = cast := by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]

variable {R}

@[simp]
/-
**ZMod.natCast_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = cast i
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `ZMod.natCast_comp_val`：natCast_comp_val [NeZero n] : ((↑) : Nat -> R) ∘ 
(val : ZMod n -> Nat) = cast
-/
theorem natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = cast i :=
  congr_fun (natCast_comp_val R) i

@[simp]
/-
**ZMod.intCast_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_cast (i : ZMod n) : ((cast i : Int) : R) = cast i
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `ZMod.intCast_comp_cast`：intCast_comp_cast : ((↑) : Int -> R) ∘ (cast : Z
Mod n -> Int) = cast
-/
theorem intCast_cast (i : ZMod n) : ((cast i : ℤ) : R) = cast i :=
  congr_fun (intCast_comp_cast R) i
/-
**ZMod.cast_add_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_add_eq_ite {n : Nat} (a b : ZMod n) : (cast (a + b) : Int) = if (n : 
Int) <= cast a + cast b then (cast a + cast b - n : Int) else cast a + cast b
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.val_add_eq_ite`：val_add_eq_ite {n : Nat} (a b : Fin n) : (↑(a + b) :
 Nat) = if n <= a + b then a + b - n else a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem cast_add_eq_ite {n : ℕ} (a b : ZMod n) :
    (cast (a + b) : ℤ) =
      if (n : ℤ) ≤ cast a + cast b then (cast a + cast b - n : ℤ) else cast a + cast b := by
  rcases n with - | n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : ℕ) : ℤ) = if ((n + 1 : ℕ) : ℤ) ≤ (a : ℕ) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.natCast_succ]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {m : ℕ} [CharP R m]

@[simp]
/-
**ZMod.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1
参数：h : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CharP.CharOne.subsingleton`：∀ {R : Type u_1} [inst : NonAssocSemiring R]
 [CharP R 1], Subsingleton R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1 := by
  rcases n with - | n
  · exact Int.cast_one
  change ((1 % (n + 1) : ℕ) : R) = 1
  cases n
  · rw [Nat.dvd_one] at h
    subst m
    subsingleton [CharP.CharOne.subsingleton]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a
 + cast b
参数：h : m ∣ n；a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_sub_mod`：∀ {n : ℕ} (k : ℕ), n ∣ k - k % n
-/
theorem cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_add, Fin.val_add, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a
 * cast b
参数：h : m ∣ n；a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Fin.val_mul`：∀ {n : ℕ} (a b : Fin n), ↑(a * b) = ↑a * ↑b % n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_sub_mod`：∀ {n : ℕ} (k : ℕ), n ∣ k - k % n
-/
theorem cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_mul, Fin.val_mul, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

/-- The canonical ring homomorphism from `ZMod n` to a ring of characteristic dividing `n`.

See also `ZMod.lift` for a generalized version working in `AddGroup`s.
-/
/-
**ZMod.castHom** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n ->+* R where
 toFun
参数：h : m ∣ n；R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.cast_one`：cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1
· 使用定理 `ZMod.cast_mul`：cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod
 n) : R) = cast a * cast b
· 使用定理 `ZMod.cast_add`：cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod
 n) : R) = cast a + cast b

--- 原说明 ---
The canonical ring homomorphism from `ZMod n` to a ring of characteristic dividi
ng `n`.

See also `ZMod.lift` for a generalized version working in `AddGroup`s.
-/
def castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n →+* R where
  toFun := cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h

@[simp]
/-
**ZMod.castHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = cast i
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = cast i :=
  rfl

@[simp]
/-
**ZMod.cast_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a
 - cast b
参数：h : m ∣ n；a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b :=
  (castHom h R).map_sub a b

@[simp]
/-
**ZMod.cast_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_neg (h : m ∣ n) (a : ZMod n) : (cast (-a : ZMod n) : R) = -(cast a)
参数：h : m ∣ n；a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
-/
theorem cast_neg (h : m ∣ n) (a : ZMod n) : (cast (-a : ZMod n) : R) = -(cast a) :=
  (castHom h R).map_neg a

@[simp]
/-
**ZMod.cast_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_pow (h : m ∣ n) (a : ZMod n) (k : Nat) : (cast (a ^ k : ZMod n) : R) 
= (cast a) ^ k
参数：h : m ∣ n；a : ZMod n；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a) ^ k :=
  (castHom h R).map_pow a k

@[simp, norm_cast]
/-
**ZMod.cast_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_natCast (h : m ∣ n) (k : Nat) : (cast (k : ZMod n) : R) = k
参数：h : m ∣ n；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem cast_natCast (h : m ∣ n) (k : ℕ) : (cast (k : ZMod n) : R) = k :=
  map_natCast (castHom h R) k

@[simp, norm_cast]
/-
**ZMod.cast_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_intCast (h : m ∣ n) (k : Int) : (cast (k : ZMod n) : R) = k
参数：h : m ∣ n；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
-/
theorem cast_intCast (h : m ∣ n) (k : ℤ) : (cast (k : ZMod n) : R) = k :=
  map_intCast (castHom h R) k
/-
**ZMod.castHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：castHom_surjective (h : m ∣ n) : Function.Surjective (castHom h (ZMod m))
参数：h : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
-/
theorem castHom_surjective (h : m ∣ n) : Function.Surjective (castHom h (ZMod m)) :=
  fun a ↦ by obtain ⟨a, rfl⟩ := intCast_surjective a; exact ⟨a, map_intCast ..⟩

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

/-
**ZMod.cast_one'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_one' : (cast (1 : ZMod n) : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_one`：cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_one' : (cast (1 : ZMod n) : R) = 1 := by simp
/-
**ZMod.cast_add'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_add' (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_add`：cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod
 n) : R) = cast a + cast b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_add' (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by simp
/-
**ZMod.cast_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_mul' (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_mul`：cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod
 n) : R) = cast a * cast b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_mul' (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by simp
/-
**ZMod.cast_sub'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_sub' (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_sub`：cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod
 n) : R) = cast a - cast b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_sub' (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b := by simp
/-
**ZMod.cast_pow'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_pow' (a : ZMod n) (k : Nat) : (cast (a ^ k : ZMod n) : R) = (cast a :
 R) ^ k
参数：a : ZMod n；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_pow`：cast_pow (h : m ∣ n) (a : ZMod n) (k : Nat) : (cast (a ^ 
k : ZMod n) : R) = (cast a) ^ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_pow' (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k := by simp

@[norm_cast]
/-
**ZMod.cast_natCast'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_natCast' (k : Nat) : (cast (k : ZMod n) : R) = k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_natCast`：cast_natCast (h : m ∣ n) (k : Nat) : (cast (k : ZMod 
n) : R) = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_natCast' (k : ℕ) : (cast (k : ZMod n) : R) = k := by simp

@[norm_cast]
/-
**ZMod.cast_intCast'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_intCast' (k : Int) : (cast (k : ZMod n) : R) = k
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_intCast`：cast_intCast (h : m ∣ n) (k : Int) : (cast (k : ZMod 
n) : R) = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_intCast' (k : ℤ) : (cast (k : ZMod n) : R) = k := by simp

variable (R)
/-
**ZMod.castHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
-/
theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) := by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, CharP.intCast_eq_zero_iff R n, CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id
/-
**ZMod.castHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：castHom_bijective [Fintype R] (h : Fintype.card R = n) : Function.Bijectiv
e (ZMod.castHom (dvd_refl n) R)
参数：h : Fintype.card R = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `ZMod.castHom_injective`：castHom_injective : Function.Injective (ZMod.cas
tHom (dvd_refl n) R)
-/
theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) := by
  have : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, h, eq_self_iff_true, and_true]
  apply ZMod.castHom_injective

/-- The unique ring isomorphism between `ZMod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
/-
**ZMod.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R
参数：h : Fintype.card R = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `ZMod.castHom_bijective`：castHom_bijective [Fintype R] (h : Fintype.card 
R = n) : Function.Bijective (ZMod.castHom (dvd_refl n) R)

--- 原说明 ---
The unique ring isomorphism between `ZMod n` and a ring `R`
of characteristic `n` and cardinality `n`.
-/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)

/-- The unique ring isomorphism between `ZMod p` and a ring `R` of cardinality a prime `p`.

If you need any property of this isomorphism, first of all use `ringEquivOfPrime_eq_ringEquiv`
below (after `have : CharP R p := ...`) and deduce it by the results about `ZMod.ringEquiv`. -/
/-
**ZMod.ringEquivOfPrime** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：ringEquivOfPrime [Fintype R] {p : Nat} (hp : p.Prime) (hR : Fintype.card R
 = p) : ZMod p ≃+* R
参数：hp : p.Prime；hR : Fintype.card R = p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique ring isomorphism between `ZMod p` and a ring `R` of cardinality a pri
me `p`.

If you need any property of this isomorphism, first of all use `ringEquivOfPrime
_eq_ringEquiv`
below (after `have : CharP R p := ...`) and deduce it by the results about `ZMod
.ringEquiv`.
-/
noncomputable def ringEquivOfPrime [Fintype R] {p : ℕ} (hp : p.Prime) (hR : Fintype.card R = p) :
    ZMod p ≃+* R :=
  have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  -- The following line exists as `charP_of_card_eq_prime` in
  -- `Mathlib/Algebra/CharP/CharAndCard.lean`.
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
  ZMod.ringEquiv R hR

@[simp]
/-
**ZMod.ringEquivOfPrime_eq_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivOfPrime_eq_ringEquiv [Fintype R] {p : Nat} [CharP R p] (hp : p.Pr
ime) (hR : Fintype.card R = p) : ringEquivOfPrime R hp hR = ringEquiv R hR
参数：hp : p.Prime；hR : Fintype.card R = p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquivOfPrime_eq_ringEquiv [Fintype R] {p : ℕ} [CharP R p] (hp : p.Prime)
    (hR : Fintype.card R = p) : ringEquivOfPrime R hp hR = ringEquiv R hR := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity between `ZMod m` and `ZMod n` when `m = n`, as a ring isomorphism. -/
/-
**ZMod.ringEquivCongr** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr {m n : Nat} (h : m = n) : ZMod m ≃+* ZMod n
参数：h : m = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0

--- 原说明 ---
The identity between `ZMod m` and `ZMod n` when `m = n`, as a ring isomorphism.
-/
def ringEquivCongr {m n : ℕ} (h : m = n) : ZMod m ≃+* ZMod n := by
  rcases m with - | m <;> rcases n with - | n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  · exact
      { finCongr h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast, Fin.val_mul, Fin.val_mul, Fin.val_cast, Fin.val_cast, ← h]
        map_add' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast, Fin.val_add, Fin.val_add, Fin.val_cast, Fin.val_cast, ← h] }
/-
**ZMod.ringEquivCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (a : ℕ), ZMod.ringEquivCongr ⋯ = RingEquiv.refl (ZMod a)
参数：a : ℕ；ZMod a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma ringEquivCongr_refl (a : ℕ) : ringEquivCongr (rfl : a = a) = .refl _ := by
  cases a <;> rfl
/-
**ZMod.ringEquivCongr_refl_apply** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_refl_apply {a : Nat} (x : ZMod a) : ringEquivCongr rfl x = 
x
参数：x : ZMod a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.ringEquivCongr_refl`：∀ (a : ℕ), ZMod.ringEquivCongr ⋯ = RingEquiv.r
efl (ZMod a)
-/
lemma ringEquivCongr_refl_apply {a : ℕ} (x : ZMod a) : ringEquivCongr rfl x = x := by
  rw [ringEquivCongr_refl]
  rfl
/-
**ZMod.ringEquivCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_symm {a b : Nat} (hab : a = b) : (ringEquivCongr hab).symm 
= ringEquivCongr hab.symm
参数：hab : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ringEquivCongr_symm {a b : ℕ} (hab : a = b) :
    (ringEquivCongr hab).symm = ringEquivCongr hab.symm := by
  subst hab
  cases a <;> rfl
/-
**ZMod.ringEquivCongr_trans** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_trans {a b c : Nat} (hab : a = b) (hbc : b = c) : (ringEqui
vCongr hab).trans (ringEquivCongr hbc) = ringEquivCongr (hab.trans hbc)
参数：hab : a = b；hbc : b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ringEquivCongr_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) :
    (ringEquivCongr hab).trans (ringEquivCongr hbc) = ringEquivCongr (hab.trans hbc) := by
  subst hab hbc
  cases a <;> rfl
/-
**ZMod.ringEquivCongr_ringEquivCongr_apply** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_ringEquivCongr_apply {a b c : Nat} (hab : a = b) (hbc : b =
 c) (x : ZMod a) : ringEquivCongr hbc (ringEquivCongr hab x) = ringEquivCongr (h
ab.trans hbc) x
参数：hab : a = b；hbc : b = c；x : ZMod a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZMod.ringEquivCongr_trans`：ringEquivCongr_trans {a b c : Nat} (hab : a =
 b) (hbc : b = c) : (ringEquivCongr hab).trans (ringEquivCongr hbc) = ringEquivC
ongr (hab.trans…
-/
lemma ringEquivCongr_ringEquivCongr_apply {a b c : ℕ} (hab : a = b) (hbc : b = c) (x : ZMod a) :
    ringEquivCongr hbc (ringEquivCongr hab x) = ringEquivCongr (hab.trans hbc) x := by
  rw [← ringEquivCongr_trans hab hbc]
  rfl
/-
**ZMod.ringEquivCongr_val** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_val {a b : Nat} (h : a = b) (x : ZMod a) : ZMod.val ((ZMod.
ringEquivCongr h) x) = ZMod.val x
参数：h : a = b；x : ZMod a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ringEquivCongr_val {a b : ℕ} (h : a = b) (x : ZMod a) :
    ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x := by
  subst h
  cases a <;> rfl
/-
**ZMod.ringEquivCongr_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：ringEquivCongr_intCast {a b : Nat} (h : a = b) (z : Int) : ZMod.ringEquivC
ongr h z = z
参数：h : a = b；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma ringEquivCongr_intCast {a b : ℕ} (h : a = b) (z : ℤ) :
    ZMod.ringEquivCongr h z = z := map_intCast (ringEquivCongr h) z

end CharEq

end UniversalProperty

variable {m n : ℕ}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.val_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
参数：a : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_eq_zero : ∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, _ => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    exact Iff.rfl
/-
**ZMod.intCast_eq_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_intCast_iff (a b : Int) (c : Nat) : (a : ZMod c) = (b : ZMod c)
 ↔ a ≡ b [ZMOD c]
参数：a b : Int；c : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.intCast_eq_intCast`：intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD
 p]
-/
theorem intCast_eq_intCast_iff (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.intCast_eq_intCast (ZMod c) c
/-
**ZMod.intCast_eq_intCast_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_intCast_iff' (a b : Int) (c : Nat) : (a : ZMod c) = (b : ZMod c
) ↔ a % c = b % c
参数：a b : Int；c : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
-/
theorem intCast_eq_intCast_iff' (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.intCast_eq_intCast_iff a b c
/-
**ZMod.val_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMod n).val = a % n
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.intCast_eq_intCast_iff'`：intCast_eq_intCast_iff' (a b : Int) (c : N
at) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.cast_id`：∀ (n : ℕ) (i : ZMod n), i.cast = i
-/
theorem val_intCast {n : ℕ} (a : ℤ) [NeZero n] : ↑(a : ZMod n).val = a % n := by
  have hle : (0 : ℤ) ≤ ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : ℤ) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
/-
**ZMod.natCast_eq_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_natCast_iff (a b c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b
 [MOD c]
参数：a b c : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
-/
theorem natCast_eq_natCast_iff (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c
/-
**ZMod.natCast_eq_natCast_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_natCast_iff' (a b c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a % 
c = b % c
参数：a b c : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
-/
theorem natCast_eq_natCast_iff' (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.natCast_eq_natCast_iff a b c
/-
**ZMod.intCast_zmod_eq_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_zmod_eq_zero_iff_dvd (a : Int) (b : Nat) : (a : ZMod b) = 0 ↔ (b :
 Int) ∣ a
参数：a : Int；b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用定理 `Int.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a := by
  rw [← Int.cast_zero, ZMod.intCast_eq_intCast_iff, Int.modEq_zero_iff_dvd]
/-
**ZMod.intCast_eq_intCast_iff_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_intCast_iff_dvd_sub (a b : Int) (c : Nat) : (a : ZMod c) = ↑b ↔
 ↑c ∣ b - a
参数：a b : Int；c : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intCast_eq_intCast_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
/-
**ZMod.natCast_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b) = 0 ↔ b ∣ a
参数：a b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_eq_zero_iff (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `Int.emod_zero`：∀ (a : ℤ), a % 0 = a
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_intCast`：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMo
d n).val = a % n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZMod.val.eq_2`：∀ (n : ℕ), ZMod.val = Fin.val
-/
theorem coe_intCast (a : ℤ) : cast (a : ZMod n) = a % n := by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl
/-
**ZMod.intCast_cast_add** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：intCast_cast_add (x y : ZMod n) : (cast (x + y) : Int) = (cast x + cast y)
 % n
参数：x y : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
lemma intCast_cast_add (x y : ZMod n) : (cast (x + y) : ℤ) = (cast x + cast y) % n := by
  rw [← ZMod.coe_intCast, Int.cast_add, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]
/-
**ZMod.intCast_cast_mul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：intCast_cast_mul (x y : ZMod n) : (cast (x * y) : Int) = cast x * cast y %
 n
参数：x y : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
lemma intCast_cast_mul (x y : ZMod n) : (cast (x * y) : ℤ) = cast x * cast y % n := by
  rw [← ZMod.coe_intCast, Int.cast_mul, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]
/-
**ZMod.intCast_cast_sub** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：intCast_cast_sub (x y : ZMod n) : (cast (x - y) : Int) = (cast x - cast y)
 % n
参数：x y : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
lemma intCast_cast_sub (x y : ZMod n) : (cast (x - y) : ℤ) = (cast x - cast y) % n := by
  rw [← ZMod.coe_intCast, Int.cast_sub, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]
/-
**ZMod.intCast_cast_neg** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：intCast_cast_neg (x : ZMod n) : (cast (-x) : Int) = -cast x % n
参数：x : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_intCast`：coe_intCast (a : Int) : cast (a : ZMod n) = a % n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
lemma intCast_cast_neg (x : ZMod n) : (cast (-x) : ℤ) = -cast x % n := by
  rw [← ZMod.coe_intCast, Int.cast_neg, ZMod.intCast_zmod_cast]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.val_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_neg_one (n : Nat) : (-1 : ZMod n.succ).val = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.coe_neg_one`：coe_neg_one : ↑(-1 : Fin (n + 1)) = n
-/
theorem val_neg_one (n : ℕ) : (-1 : ZMod n.succ).val = n := by
  dsimp [val, Fin.val_neg']
  cases n
  · simp
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]

set_option backward.isDefEq.respectTransparency false in
/-- `-1 : ZMod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in `cast_neg`. -/
/-
**ZMod.cast_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_neg_one {R : Type*} [Ring R] (n : Nat) : cast (-1 : ZMod n) = (n - 1 
: R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZMod.val_neg_one`：val_neg_one (n : Nat) : (-1 : ZMod n.succ).val = n
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a

--- 原说明 ---
`-1 : ZMod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in
 `cast_neg`.
-/
theorem cast_neg_one {R : Type*} [Ring R] (n : ℕ) : cast (-1 : ZMod n) = (n - 1 : R) := by
  rcases n with - | n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.cast_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_sub_one {R : Type*} [Ring R] {n : Nat} (k : ZMod n) : (cast (k - 1 : 
ZMod n) : R) = (if k = 0 then (n : R) else cast k) - 1
参数：k : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `ZMod.cast_neg_one`：cast_neg_one {R : Type*} [Ring R] (n : Nat) : cast (-
1 : ZMod n) = (n - 1 : R)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.coe_sub_one`：coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 the
n n else a - 1
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem cast_sub_one {R : Type*} [Ring R] {n : ℕ} (k : ZMod n) :
    (cast (k - 1 : ZMod n) : R) = (if k = 0 then (n : R) else cast k) - 1 := by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · dsimp [ZMod, ZMod.cast]
      rw [Int.cast_sub, Int.cast_one]
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      rw [Fin.coe_sub_one, if_neg]
      · rw [Nat.cast_sub, Nat.cast_one]
        rwa [Fin.ext_iff, Fin.val_zero, ← Ne, ← Nat.one_le_iff_ne_zero] at hk
      · exact hk
/-
**ZMod.natCast_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_iff (p : Nat) (n : Nat) (z : ZMod p) [NeZero p] : ↑n = z ↔ exis
ts k, n = z.val + p * k
参数：p : Nat；n : Nat；z : ZMod p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem natCast_eq_iff (p : ℕ) (n : ℕ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast, Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add, natCast_zmod_val, Nat.cast_mul, natCast_self, zero_mul,
      add_zero]
/-
**ZMod.intCast_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_iff (p : Nat) (n : Int) (z : ZMod p) [NeZero p] : ↑n = z ↔ exis
ts k, n = z.val + p * k
参数：p : Nat；n : Int；z : ZMod p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_intCast`：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMo
d n).val = a % n
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ZMod.cast_id`：∀ (n : ℕ) (i : ZMod n), i.cast = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem intCast_eq_iff (p : ℕ) (n : ℤ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast, Int.emod_add_mul_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_val,
      ZMod.natCast_self, zero_mul, add_zero, cast_id]

@[push_cast, simp]
/-
**ZMod.intCast_mod** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_mod (a : Int) (b : Nat) : ((a % b : Int) : ZMod b) = (a : ZMod b)
参数：a : Int；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
-/
theorem intCast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b) := by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq
/-
**ZMod.ker_intCastAddHom** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ker_intCastAddHom (n : Nat) : (Int.castAddHom (ZMod n)).ker = AddSubgroup.
zmultiples (n : Int)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mem_zmultiples_iff`：Int.mem_zmultiples_iff {a b : Int} : b in AddSub
group.zmultiples a ↔ a ∣ b
· 使用定理 `AddMonoidHom.mem_ker`：∀ {G : Type u_1} [inst : AddGroup G] {M : Type u_7
} [inst_1 : AddZeroClass M] {f : G →+ M} {x : G}, x ∈ f.ker ↔ f x = 0
· 使用定理 `Int.coe_castAddHom`：∀ {α : Type u_3} [inst : AddGroupWithOne α], ⇑(Int.c
astAddHom α) = fun x => ↑x
· 使用定理 `ZMod.intCast_zmod_eq_zero_iff_dvd`：intCast_zmod_eq_zero_iff_dvd (a : Int
) (b : Nat) : (a : ZMod b) = 0 ↔ (b : Int) ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_intCastAddHom (n : ℕ) :
    (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples (n : ℤ) := by
  ext
  rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_castAddHom,
    intCast_zmod_eq_zero_iff_dvd]
/-
**ZMod.cast_injective_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_injective_of_le {m n : Nat} [nzm : NeZero m] (h : m <= n) : Function.
Injective (@cast (ZMod n) _ m)
参数：h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem cast_injective_of_le {m n : ℕ} [nzm : NeZero m] (h : m ≤ n) :
    Function.Injective (@cast (ZMod n) _ m) := by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [cast, val, natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hx.trans_le h), Nat.mod_eq_of_lt (hy.trans_le h)] at f
    apply Fin.ext
    exact f
/-
**ZMod.cast_zmod_eq_zero_iff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_zmod_eq_zero_iff_of_le {m n : Nat} [NeZero m] (h : m <= n) (a : ZMod 
m) : (cast a : ZMod n) = 0 ↔ a = 0
参数：h : m <= n；a : ZMod m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.cast_zero`：cast_zero : (cast (0 : ZMod n) : R) = 0
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `ZMod.cast_injective_of_le`：cast_injective_of_le {m n : Nat} [nzm : NeZer
o m] (h : m <= n) : Function.Injective (@cast (ZMod n) _ m)
-/
theorem cast_zmod_eq_zero_iff_of_le {m n : ℕ} [NeZero m] (h : m ≤ n) (a : ZMod m) :
    (cast a : ZMod n) = 0 ↔ a = 0 := by
  rw [← ZMod.cast_zero (n := m)]
  exact Injective.eq_iff' (cast_injective_of_le h) rfl

@[simp]
/-
**ZMod.natCast_toNat** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (p : ℕ) {z : ℤ}, 0 ≤ z → ↑z.toNat = ↑z
参数：p : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_toNat (p : ℕ) : ∀ {z : ℤ} (_h : 0 ≤ z), (z.toNat : ZMod p) = z
  | (n : ℕ), _h => by simp only [Int.cast_natCast, Int.toNat_natCast]
  | Int.negSucc n, h => by simp at h
/-
**ZMod.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_injective (n : Nat) [NeZero n] : Function.Injective (val : ZMod n -> N
at)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
theorem val_injective (n : ℕ) [NeZero n] : Function.Injective (val : ZMod n → ℕ) := by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h
/-
**ZMod.val_one_eq_one_mod** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_one_eq_one_mod (n : Nat) : (1 : ZMod n).val = 1 % n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
-/
theorem val_one_eq_one_mod (n : ℕ) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one, val_natCast]
/-
**ZMod.val_two_eq_two_mod** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_two_eq_two_mod (n : Nat) : (2 : ZMod n).val = 2 % n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
-/
theorem val_two_eq_two_mod (n : ℕ) : (2 : ZMod n).val = 2 % n := by
  rw [← Nat.cast_two, val_natCast]
/-
**ZMod.val_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
参数：n : Nat；1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_one_eq_one_mod`：val_one_eq_one_mod (n : Nat) : (1 : ZMod n).val
 = 1 % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : ZMod n).val = 1 := by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out
/-
**ZMod.val_one''** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_one'' : forall {n}, n != 1 -> (1 : ZMod n).val = 1 | 0, _ => rfl | 1, 
hn => by cases hn rfl | n + 2, _ => haveI : Fact (1 < n + 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma val_one'' : ∀ {n}, n ≠ 1 → (1 : ZMod n).val = 1
  | 0, _ => rfl
  | 1, hn => by cases hn rfl
  | n + 2, _ =>
    haveI : Fact (1 < n + 2) := ⟨by simp⟩
    ZMod.val_one _
/-
**ZMod.val_add** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val
) % n
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
-/
theorem val_add {n : ℕ} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add
/-
**ZMod.val_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_add_of_lt {n : Nat} {a b : ZMod n} (h : a.val + b.val < n) : (a + b).v
al = a.val + b.val
参数：h : a.val + b.val < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_add`：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val 
= (a.val + b.val) % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem val_add_of_lt {n : ℕ} {a b : ZMod n} (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  have : NeZero n := by constructor; rintro rfl; simp at h
  rw [ZMod.val_add, Nat.mod_eq_of_lt h]
/-
**ZMod.val_add_val_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_add_val_of_le {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.
val) : a.val + b.val = (a + b).val + n
参数：h : n <= a.val + b.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_add`：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val 
= (a.val + b.val) % n
· 使用定理 `Nat.add_mod_add_of_le_add_mod`：add_mod_add_of_le_add_mod {a b c : Nat} (
hc : c <= a % c + b % c) : (a + b) % c + c = a % c + b % c
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
-/
theorem val_add_val_of_le {n : ℕ} [NeZero n] {a b : ZMod n} (h : n ≤ a.val + b.val) :
    a.val + b.val = (a + b).val + n := by
  rw [val_add, Nat.add_mod_add_of_le_add_mod, Nat.mod_eq_of_lt (val_lt _),
    Nat.mod_eq_of_lt (val_lt _)]
  rwa [Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _)]
/-
**ZMod.val_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_add_of_le {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val)
 : (a + b).val = a.val + b.val - n
参数：h : n <= a.val + b.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_add_val_of_le`：val_add_val_of_le {n : Nat} [NeZero n] {a b : ZM
od n} (h : n <= a.val + b.val) : a.val + b.val = (a + b).val + n
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem val_add_of_le {n : ℕ} [NeZero n] {a b : ZMod n} (h : n ≤ a.val + b.val) :
    (a + b).val = a.val + b.val - n := by
  rw [val_add_val_of_le h]
  exact eq_tsub_of_add_eq rfl
/-
**ZMod.val_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_add_le {n : Nat} (a b : ZMod n) : (a + b).val <= a.val + b.val
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_add_le`：∀ (a b : ℤ), (a + b).natAbs ≤ a.natAbs + b.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_add`：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val 
= (a.val + b.val) % n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
-/
theorem val_add_le {n : ℕ} (a b : ZMod n) : (a + b).val ≤ a.val + b.val := by
  cases n
  · simpa [ZMod.val] using! Int.natAbs_add_le _ _
  · simpa [ZMod.val_add] using! Nat.mod_le _ _
/-
**ZMod.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b.val % n
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_mul`：∀ {n : ℕ} (a b : Fin n), ↑(a * b) = ↑a * ↑b % n
-/
theorem val_mul {n : ℕ} (a b : ZMod n) : (a * b).val = a.val * b.val % n := by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul
/-
**ZMod.val_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_mul_le {n : Nat} (a b : ZMod n) : (a * b).val <= a.val * b.val
参数：a b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_mul`：val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b
.val % n
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
-/
theorem val_mul_le {n : ℕ} (a b : ZMod n) : (a * b).val ≤ a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_le
/-
**ZMod.val_mul_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_mul_of_lt {n : Nat} {a b : ZMod n} (h : a.val * b.val < n) : (a * b).v
al = a.val * b.val
参数：h : a.val * b.val < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_mul`：val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b
.val % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem val_mul_of_lt {n : ℕ} {a b : ZMod n} (h : a.val * b.val < n) :
    (a * b).val = a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h
/-
**ZMod.val_mul_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_mul_iff_lt {n : Nat} [NeZero n] (a b : ZMod n) : (a * b).val = a.val *
 b.val ↔ a.val * b.val < n
参数：a b : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `ZMod.val_mul_of_lt`：val_mul_of_lt {n : Nat} {a b : ZMod n} (h : a.val * 
b.val < n) : (a * b).val = a.val * b.val
-/
theorem val_mul_iff_lt {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a * b).val = a.val * b.val ↔ a.val * b.val < n := by
  constructor <;> intro h
  · rw [← h]; apply ZMod.val_lt
  · apply ZMod.val_mul_of_lt h
/-
**ZMod.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：nontrivial (n : Nat) [Fact (1 < n)] : Nontrivial (ZMod n)
参数：n : Nat；1 < n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
-/
instance nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
      zero_ne_one <|
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩
/-
**ZMod.nontrivial'** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：nontrivial' : Nontrivial (ZMod 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nontrivial' : Nontrivial (ZMod 0) := by
  delta ZMod; infer_instance
/-
**ZMod.one_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：one_eq_zero_iff {n : Nat} : (1 : ZMod n) = 0 ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_eq_zero_iff {n : ℕ} : (1 : ZMod n) = 0 ↔ n = 1 := by
  rw [← Nat.cast_one, natCast_eq_zero_iff, Nat.dvd_one]

/-- The inversion on `ZMod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
/-
**ZMod.inv** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：(n : ℕ) → ZMod n → ZMod n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inversion on `ZMod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`.
-/
def inv : ∀ n : ℕ, ZMod n → ZMod n
  | 0, i => Int.sign i
  | n + 1, i => Nat.gcdA i.val (n + 1)
/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Inv (ZMod n) :=
  ⟨inv n⟩
/-
**ZMod.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ), 0⁻¹ = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.sign_zero`：Int.sign 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_zero : ∀ n : ℕ, (0 : ZMod n)⁻¹ = 0
  | 0 => Int.sign_zero
  | n + 1 =>
    show (Nat.gcdA _ (n + 1) : ZMod (n + 1)) = 0 by
      simp [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]
/-
**ZMod.mul_inv_eq_gcd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：mul_inv_eq_gcd {n : Nat} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_sign_self`：∀ (i : ℤ), i * i.sign = ↑i.natAbs
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
-/
theorem mul_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n := by
  rcases n with - | n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign_self]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self, zero_mul, add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) n.succ + n.succ * Nat.gcdB (val a) n.succ) := by
        push_cast
        rw [natCast_zmod_val]
        rfl
      _ = Nat.gcd a.val n.succ := by rw [← Nat.gcd_eq_gcd_ab a.val n.succ]; rfl
/-
**ZMod.inv_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ), 1⁻¹ = 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ZMod.val_one''`：val_one'' : forall {n}, n != 1 -> (1 : ZMod n).val = 1 |
 0, _ => rfl | 1, hn => by cases hn rfl | n + 2, _ => haveI : Fact (1 < n + 2)
· 使用定理 `Nat.gcd_one_left`：∀ (n : ℕ), Nat.gcd 1 n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.mul_inv_eq_gcd`：mul_inv_eq_gcd {n : Nat} (a : ZMod n) : a * a⁻¹ = N
at.gcd a.val n
-/
@[simp] protected lemma inv_one (n : ℕ) : (1⁻¹ : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

@[simp, grind =]
/-
**ZMod.natCast_mod** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_mod (a : Nat) (n : Nat) : ((a % n : Nat) : ZMod n) = a
参数：a : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CharP.cast_eq_mod`：cast_eq_mod (k : Nat) : (k : R) = (k % p : Nat)
-/
theorem natCast_mod (a : ℕ) (n : ℕ) : ((a % n : ℕ) : ZMod n) = a :=
  (CharP.cast_eq_mod (ZMod n) n a).symm
/-
**ZMod.intCast_eq_zero_iff_even** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_zero_iff_even {n : Int} : (n : ZMod 2) = 0 ↔ Even n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
-/
theorem intCast_eq_zero_iff_even {n : ℤ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.intCast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

alias ⟨_, _root_.Even.intCast_zmod_two⟩ := intCast_eq_zero_iff_even
/-
**ZMod.natCast_eq_zero_iff_even** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_zero_iff_even {n : Nat} : (n : ZMod 2) = 0 ↔ Even n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.intCast_eq_zero_iff_even`：intCast_eq_zero_iff_even {n : Int} : (n :
 ZMod 2) = 0 ↔ Even n
-/
theorem natCast_eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  mod_cast intCast_eq_zero_iff_even (n := n)

alias ⟨_, _root_.Even.natCast_zmod_two⟩ := natCast_eq_zero_iff_even
/-
**ZMod.intCast_eq_one_iff_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_eq_one_iff_odd {n : Int} : (n : ZMod 2) = 1 ↔ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用引理 `Int.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1 where mp
· 使用定理 `Int.ModEq.eq_1`：∀ (n a b : ℤ), (a ≡ b [ZMOD n]) = (a % n = b % n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intCast_eq_one_iff_odd {n : ℤ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff, Int.odd_iff, Int.ModEq]
  simp

alias ⟨_, _root_.Odd.intCast_zmod_two⟩ := intCast_eq_one_iff_odd
/-
**ZMod.natCast_eq_one_iff_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_eq_one_iff_odd {n : Nat} : (n : ZMod 2) = 1 ↔ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.intCast_eq_one_iff_odd`：intCast_eq_one_iff_odd {n : Int} : (n : ZMo
d 2) = 1 ↔ Odd n
-/
theorem natCast_eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n :=
  mod_cast intCast_eq_one_iff_odd (n := n)

alias ⟨_, _root_.Odd.natCast_zmod_two⟩ := natCast_eq_one_iff_odd
/-
**ZMod.natCast_ne_zero_iff_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natCast_ne_zero_iff_odd {n : Nat} : (n : ZMod 2) != 0 ↔ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natCast_ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  simp [natCast_eq_zero_iff_even]
/-
**ZMod.coe_mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_mul_inv_eq_one {n : Nat} (x : Nat) (h : Nat.Coprime x n) : ((x : ZMod 
n) * (x : ZMod n)⁻¹) = 1
参数：x : Nat；h : Nat.Coprime x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.mul_inv_eq_gcd`：mul_inv_eq_gcd {n : Nat} (a : ZMod n) : a * a⁻¹ = N
at.gcd a.val n
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    ((x : ZMod n) * (x : ZMod n)⁻¹) = 1 := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd, val_natCast, h, Nat.cast_one]
/-
**ZMod.mul_val_inv** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1
参数：hmn : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.inv_one`：∀ (n : ℕ), 1⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `ZMod.coe_mul_inv_eq_one`：coe_mul_inv_eq_one {n : Nat} (x : Nat) (h : Nat
.Coprime x n) : ((x : ZMod n) * (x : ZMod n)⁻¹) = 1
-/
lemma mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  have : NeZero n := ⟨hn⟩
  rw [ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one _ hmn]
/-
**ZMod.val_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：val_inv_mul (hmn : m.Coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1
参数：hmn : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ZMod.mul_val_inv`：mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).
val : ZMod n) = 1
-/
lemma val_inv_mul (hmn : m.Coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1 := by
  rw [mul_comm, mul_val_inv hmn]

/-- `unitOfCoprime` makes an element of `(ZMod n)ˣ` given
a natural number `x` and a proof that `x` is coprime to `n` -/
/-
**ZMod.unitOfCoprime** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：unitOfCoprime {n : Nat} (x : Nat) (h : Nat.Coprime x n) : (ZMod n)ˣ
参数：x : Nat；h : Nat.Coprime x n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.coe_mul_inv_eq_one`：coe_mul_inv_eq_one {n : Nat} (x : Nat) (h : Nat
.Coprime x n) : ((x : ZMod n) * (x : ZMod n)⁻¹) = 1

--- 原说明 ---
`unitOfCoprime` makes an element of `(ZMod n)ˣ` given
a natural number `x` and a proof that `x` is coprime to `n`
-/
def unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp]
/-
**ZMod.coe_unitOfCoprime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_unitOfCoprime {n : Nat} (x : Nat) (h : Nat.Coprime x n) : (unitOfCopri
me x h : ZMod n) = x
参数：x : Nat；h : Nat.Coprime x n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.val_coe_unit_coprime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ) : Nat.Coprime (u : ZMod n).
val n
参数：u : (ZMod n)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_neg'`：val_neg' {n : ZMod 0} : (-n).val = n.val
· 使用定理 `Nat.coprime_of_mul_modEq_one`：coprime_of_mul_modEq_one (b : Nat) {a n : 
Nat} (h : a * b ≡ 1 [MOD n]) : a.Coprime n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `ZMod.val_mul`：val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b
.val % n
· 使用定理 `ZMod.natCast_mod`：natCast_mod (a : Nat) (n : Nat) : ((a % n : Nat) : ZMo
d n) = a
-/
theorem val_coe_unit_coprime {n : ℕ} (u : (ZMod n)ˣ) : Nat.Coprime (u : ZMod n).val n := by
  rcases n with - | n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_inv_cancel u)
  rw [Units.val_one] at this
  rw [← natCast_eq_natCast_iff, Nat.cast_one, ← this]; clear this
  rw [← natCast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  rw [Units.val_mul, val_mul, natCast_mod]
/-
**ZMod.isUnit_iff_coprime** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZMod n) ↔ m.Coprime n
参数：m n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec, val_natCast, Nat.coprime_iff_gcd_eq_one] at H'
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← H']
  exact Nat.gcd_rec n m

@[simp]
/-
**ZMod.coprime_mod_iff_coprime** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：coprime_mod_iff_coprime (m n : Nat) : (m % n).Coprime n ↔ m.Coprime n
参数：m n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.gcd_eq`：gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coprime_mod_iff_coprime (m n : ℕ) : (m % n).Coprime n ↔ m.Coprime n := by
  suffices (m % n).gcd n = m.gcd n by grind
  exact Nat.ModEq.gcd_eq (by simp [Nat.ModEq])
/-
**ZMod.isUnit_prime_iff_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：isUnit_prime_iff_not_dvd {n p : Nat} (hp : p.Prime) : IsUnit (p : ZMod n) 
↔ ¬p ∣ n
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnit_prime_iff_not_dvd {n p : ℕ} (hp : p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n := by
  rw [isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp]
/-
**ZMod.isUnit_prime_of_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：isUnit_prime_of_not_dvd {n p : Nat} (hp : p.Prime) (h : ¬ p ∣ n) : IsUnit 
(p : ZMod n)
参数：hp : p.Prime；h : ¬ p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZMod.isUnit_prime_iff_not_dvd`：isUnit_prime_iff_not_dvd {n p : Nat} (hp 
: p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n
-/
lemma isUnit_prime_of_not_dvd {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : IsUnit (p : ZMod n) :=
  (isUnit_prime_iff_not_dvd hp).mpr h

/-- In `ZMod (p ^ d)` with `0 < d`, a natural number is a unit iff `p` does not divide it. -/
/-
**ZMod.isUnit_natCast_iff_not_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isUnit_natCast_iff_not_dvd_pow {p d a : Nat} (hp : p.Prime) (hd : 0 < d) :
 IsUnit (a : ZMod (p ^ d)) ↔ ¬ p ∣ a
参数：hp : p.Prime；hd : 0 < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Nat.coprime_pow_right_iff`：coprime_pow_right_iff {n : Nat} (hn : 0 < n) 
(a b : Nat) : Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In `ZMod (p ^ d)` with `0 < d`, a natural number is a unit iff `p` does not divi
de it.
-/
theorem isUnit_natCast_iff_not_dvd_pow {p d a : ℕ} (hp : p.Prime) (hd : 0 < d) :
    IsUnit (a : ZMod (p ^ d)) ↔ ¬ p ∣ a := by
  rw [isUnit_iff_coprime, Nat.coprime_pow_right_iff hd, Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

/-- In `ZMod (p ^ d)` with `0 < d`, the prime `p` is not a unit. -/
/-
**ZMod.prime_natCast_not_isUnit_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：prime_natCast_not_isUnit_pow {p d : Nat} (hp : p.Prime) (hd : 0 < d) : ¬ I
sUnit ((p : Nat) : ZMod (p ^ d))
参数：hp : p.Prime；hd : 0 < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.isUnit_prime_iff_not_dvd`：isUnit_prime_iff_not_dvd {n p : Nat} (hp 
: p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
In `ZMod (p ^ d)` with `0 < d`, the prime `p` is not a unit.
-/
theorem prime_natCast_not_isUnit_pow {p d : ℕ} (hp : p.Prime) (hd : 0 < d) :
    ¬ IsUnit ((p : ℕ) : ZMod (p ^ d)) := by
  simp [isUnit_prime_iff_not_dvd hp]
  lia

@[simp]
/-
**ZMod.inv_coe_unit** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：inv_coe_unit {n : Nat} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ
)
参数：u : (ZMod n)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_eq_of_mul_eq_one_right`：∀ {α : Type u} [inst : Monoid α] {u : 
αˣ} {a : α}, ↑u * a = 1 → ↑u⁻¹ = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.mul_inv_eq_gcd`：mul_inv_eq_gcd {n : Nat} (a : ZMod n) : a * a⁻¹ = N
at.gcd a.val n
-/
theorem inv_coe_unit {n : ℕ} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ) := by
  have := congr_arg ((↑) : ℕ → ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd, Nat.cast_one] at this
  exact (Units.inv_eq_of_mul_eq_one_right this).symm
/-
**ZMod.mul_inv_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：mul_inv_of_unit {n : Nat} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1
参数：a : ZMod n；h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.inv_coe_unit`：inv_coe_unit {n : Nat} (u : (ZMod n)ˣ) : (u : ZMod n)
⁻¹ = (u⁻¹ : (ZMod n)ˣ)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem mul_inv_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]
/-
**ZMod.inv_mul_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1
参数：a : ZMod n；h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ZMod.mul_inv_of_unit`：mul_inv_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a * a⁻¹ = 1
-/
theorem inv_mul_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_of_unit a h]

-- TODO: If we changed `⁻¹` so that `ZMod n` is always a `DivisionMonoid`,
-- then we could use the general lemma `inv_eq_of_mul_eq_one`
/-
**ZMod.inv_eq_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ) (a b : ZMod n), a * b = 1 → a⁻¹ = b
参数：n : ℕ；a b : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `ZMod.inv_mul_of_unit`：inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a⁻¹ * a = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem inv_eq_of_mul_eq_one (n : ℕ) (a b : ZMod n) (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

@[simp]
/-
**ZMod.inv_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：inv_neg_one (n : Nat) : (-1 : ZMod n)⁻¹ = -1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.inv_eq_of_mul_eq_one`：∀ (n : ℕ) (a b : ZMod n), a * b = 1 → a⁻¹ = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_neg_one (n : ℕ) : (-1 : ZMod n)⁻¹ = -1 :=
  ZMod.inv_eq_of_mul_eq_one n (-1) (-1) (by simp)
/-
**ZMod.inv_mul_eq_one_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：inv_mul_eq_one_of_isUnit {n : Nat} {a : ZMod n} (ha : IsUnit a) (b : ZMod 
n) : a⁻¹ * b = 1 ↔ a = b
参数：ha : IsUnit a；b : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ZMod.mul_inv_of_unit`：mul_inv_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a * a⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ZMod.inv_mul_of_unit`：inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a⁻¹ * a = 1
-/
lemma inv_mul_eq_one_of_isUnit {n : ℕ} {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    a⁻¹ * b = 1 ↔ a = b := by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  -- (see the "TODO" above)
  refine ⟨fun H ↦ ?_, fun H ↦ H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

-- TODO: this equivalence is true for `ZMod 0 = ℤ`, but needs to use different functions.
/-- Equivalence between the units of `ZMod n` and
the subtype of terms `x : ZMod n` for which `x.val` is coprime to `n` -/
/-
**ZMod.unitsEquivCoprime** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：unitsEquivCoprime {n : Nat} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.C
oprime x.val n } where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n

--- 原说明 ---
Equivalence between the units of `ZMod n` and
the subtype of terms `x : ZMod n` for which `x.val` is coprime to `n`
-/
def unitsEquivCoprime {n : ℕ} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.Coprime x.val n } where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp

set_option backward.isDefEq.respectTransparency false in
/-- The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` and `n`,
  the rings `ZMod (m * n)` and `ZMod m × ZMod n` are isomorphic.

See `Ideal.quotientInfRingEquivPiQuotient` for the Chinese remainder theorem for ideals in any
ring.
-/
/-
**ZMod.chineseRemainder** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：chineseRemainder {m n : Nat} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m ×
 ZMod n
参数：h : m.Coprime n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` an
d `n`,
  the rings `ZMod (m * n)` and `ZMod m × ZMod n` are isomorphic.

See `Ideal.quotientInfRingEquivPiQuotient` for the Chinese remainder theorem for
 ideals in any
ring.
-/
def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  let to_fun : ZMod (m * n) → ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n → ZMod (m * n) := fun x =>
    if m * n = 0 then
      if m = 1 then cast (RingHom.snd _ (ZMod n) x) else cast (RingHom.fst (ZMod m) _ x)
    else Nat.chineseRemainder h x.1.val x.2.val
  have inv : Function.LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun :=
    if hmn0 : m * n = 0 then by
      rcases h.eq_of_mul_eq_zero hmn0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases y
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases x
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
    else by
      have : NeZero (m * n) := ⟨hmn0⟩
      have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
      have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
      have left_inv : Function.LeftInverse inv_fun to_fun := by
        intro x
        dsimp only [to_fun, inv_fun, ZMod.castHom_apply]
        conv_rhs => rw [← ZMod.natCast_zmod_val x]
        rw [if_neg hmn0, ZMod.natCast_eq_natCast_iff, ← Nat.modEq_and_modEq_iff_modEq_mul h,
          Prod.fst_zmod_cast, Prod.snd_zmod_cast]
        refine
          ⟨(Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.left.trans ?_,
            (Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.right.trans ?_⟩
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
      exact ⟨left_inv, left_inv.rightInverse_of_card_le (by simp)⟩
  { toFun := to_fun,
    invFun := inv_fun,
    map_mul' := map_mul _
    map_add' := map_add _
    left_inv := inv.1
    right_inv := inv.2 }
/-
**ZMod.subsingleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：subsingleton_iff {n : Nat} : Subsingleton (ZMod n) ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subsingleton_iff {n : ℕ} : Subsingleton (ZMod n) ↔ n = 1 := by
  constructor
  · obtain (_ | _ | n) := n
    · simpa [ZMod] using not_subsingleton _
    · simp [ZMod]
    · simpa [ZMod] using not_subsingleton _
  · rintro rfl
    infer_instance
/-
**ZMod.nontrivial_iff** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：nontrivial_iff {n : Nat} : Nontrivial (ZMod n) ↔ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用引理 `ZMod.subsingleton_iff`：subsingleton_iff {n : Nat} : Subsingleton (ZMod n
) ↔ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nontrivial_iff {n : ℕ} : Nontrivial (ZMod n) ↔ n ≠ 1 := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]
/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (ZMod 2)ˣ where
  default := 1
  uniq := by decide

@[simp]
/-
**ZMod.add_self_eq_zero_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：add_self_eq_zero_iff_eq_zero {n : Nat} (hn : Odd n) {a : ZMod n} : a + a =
 0 ↔ a = 0
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.two_dvd_ne_zero`：∀ {n : ℕ}, ¬2 ∣ n ↔ n % 2 = 1
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `ZMod.coe_unitOfCoprime`：coe_unitOfCoprime {n : Nat} (x : Nat) (h : Nat.C
oprime x n) : (unitOfCoprime x h : ZMod n) = x
· 使用定理 `Units.mul_left_eq_zero`：mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 
↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_self_eq_zero_iff_eq_zero {n : ℕ} (hn : Odd n) {a : ZMod n} :
    a + a = 0 ↔ a = 0 := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two, ← @Nat.cast_two (ZMod n), ← ZMod.coe_unitOfCoprime 2 hn, Units.mul_left_eq_zero]
/-
**ZMod.ne_neg_self** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ne_neg_self {n : Nat} (hn : Odd n) {a : ZMod n} (ha : a != 0) : a != -a
参数：hn : Odd n；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `ZMod.add_self_eq_zero_iff_eq_zero`：add_self_eq_zero_iff_eq_zero {n : Nat
} (hn : Odd n) {a : ZMod n} : a + a = 0 ↔ a = 0
-/
theorem ne_neg_self {n : ℕ} (hn : Odd n) {a : ZMod n} (ha : a ≠ 0) : a ≠ -a := by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]
/-
**ZMod.neg_one_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：neg_one_ne_one {n : Nat} [Fact (2 < n)] : (-1 : ZMod n) != 1
参数：2 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.neg_one_ne_one`：CharP.neg_one_ne_one [AddGroupWithOne R] (p : Nat)
 [CharP R p] [Fact (2 < p)] : (-1 : R) != (1 : R)
-/
theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : ZMod n) ≠ 1 :=
  CharP.neg_one_ne_one (ZMod n) n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.neg_eq_self_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：neg_eq_self_mod_two (a : ZMod 2) : -a = a
参数：a : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> apply Fin.ext <;> simp; rfl

@[simp]
/-
**ZMod.intCast_abs_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：intCast_abs_mod_two (a : Int) : (↑|a| : ZMod 2) = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `ZMod.neg_eq_self_mod_two`：neg_eq_self_mod_two (a : ZMod 2) : -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
theorem intCast_abs_mod_two (a : ℤ) : (↑|a| : ZMod 2) = a := by
  cases le_total a 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]
/-
**ZMod.natAbs_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natAbs_mod_two (a : Int) : (a.natAbs : ZMod 2) = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `ZMod.intCast_abs_mod_two`：intCast_abs_mod_two (a : Int) : (↑|a| : ZMod 2
) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natAbs_mod_two (a : ℤ) : (a.natAbs : ZMod 2) = a := by
  simp
/-
**ZMod.val_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_ne_zero {n : Nat} (a : ZMod n) : a.val != 0 ↔ a != 0
参数：a : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
-/
theorem val_ne_zero {n : ℕ} (a : ZMod n) : a.val ≠ 0 ↔ a ≠ 0 :=
  (val_eq_zero a).not

@[simp]
/-
**ZMod.val_pos** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_pos {n : Nat} {a : ZMod n} : 0 < a.val ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem val_pos {n : ℕ} {a : ZMod n} : 0 < a.val ↔ a ≠ 0 := by
  simp [pos_iff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.val_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {n : ℕ}, 1 < n → ∀ (a : ZMod n), a.val = 1 ↔ a = 1
参数：a : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem val_eq_one : ∀ {n : ℕ} (_ : 1 < n) (a : ZMod n), a.val = 1 ↔ a = 1
  | 0, hn, _
  | 1, hn, _ => by simp at hn
  | n + 2, _, _ => by simp only [val, ZMod, Fin.ext_iff, Fin.val_one]
/-
**ZMod.neg_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：neg_eq_self_iff {n : Nat} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n
参数：a : ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomainOfNatNat`：IsDomain (ZMod 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
（共 40 条，此处仅展示前 30 条）
-/
theorem neg_eq_self_iff {n : ℕ} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  cases n
  · simp
  conv_lhs =>
    rw [← a.natCast_zmod_val, ← Nat.cast_two, ← Nat.cast_mul, natCast_eq_zero_iff]
  constructor
  · rintro ⟨m, he⟩
    rcases m with - | m
    · rw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨⟩⟩ | he)
      exact Or.inl (a.val_eq_zero.1 he)
    cases m
    · right
      rwa [show 0 + 1 = 1 from rfl, mul_one] at he
    refine (a.val_lt.not_ge <| Nat.le_of_mul_le_mul_left ?_ zero_lt_two).elim
    rw [he, mul_comm]
    apply Nat.mul_le_mul_left
    simp
  · rintro (rfl | h)
    · rw [val_zero, mul_zero]
      apply dvd_zero
    · rw [h]
/-
**ZMod.val_cast_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a : ZMod n).val = a
参数：h : a < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_natCast, Nat.mod_eq_of_lt h]
/-
**ZMod.val_cast_zmod_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_cast_zmod_lt {m : Nat} [NeZero m] (n : Nat) [NeZero n] (a : ZMod m) : 
(a.cast : ZMod n).val < m
参数：n : Nat；a : ZMod m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.val_cast_of_lt`：val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a
 : ZMod n).val = a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem val_cast_zmod_lt {m : ℕ} [NeZero m] (n : ℕ) [NeZero n] (a : ZMod m) :
    (a.cast : ZMod n).val < m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  by_cases! h : m < n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
    rw [← natCast_val, val_cast_of_lt]
    · apply a.val_lt
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · apply lt_of_lt_of_le (ZMod.val_lt _) (le_trans h (Nat.le_succ m))
/-
**ZMod.neg_val'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：neg_val' {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `Nat.ModEq.add_right_cancel'`：∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n
] → a ≡ b [MOD n]
· 使用定理 `Nat.ModEq.eq_1`：∀ (n a b : ℕ), (a ≡ b [MOD n]) = (a % n = b % n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_add`：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val 
= (a.val + b.val) % n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ZMod.val_le`：val_le {n : Nat} [NeZero n] (a : ZMod n) : a.val <= n
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
-/
theorem neg_val' {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
  calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' (val a)
        (by
          rw [Nat.ModEq, ← val_add, neg_add_cancel, tsub_add_cancel_of_le a.val_le, Nat.mod_self,
            val_zero])
/-
**ZMod.neg_val** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：neg_val {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 els
e n - a.val
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.neg_val'`：neg_val' {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = (
n - a.val) % n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.val_pos`：val_pos {n : Nat} {a : ZMod n} : 0 < a.val ↔ a != 0
-/
theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  exact Nat.sub_lt (NeZero.pos n) (val_pos.mpr h)
/-
**ZMod.val_neg_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_neg_of_ne_zero {n : Nat} [nz : NeZero n] (a : ZMod n) [na : NeZero a] 
: (-a).val = n - a.val
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.neg_val`：neg_val {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = if 
a = 0 then 0 else n - a.val
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem val_neg_of_ne_zero {n : ℕ} [nz : NeZero n] (a : ZMod n) [na : NeZero a] :
    (-a).val = n - a.val := by simp_all [neg_val a, na.out]
/-
**ZMod.val_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_sub {n : Nat} [NeZero n] {a b : ZMod n} (h : b.val <= a.val) : (a - b)
.val = a.val - b.val
参数：h : b.val <= a.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ZMod.val_add`：val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val 
= (a.val + b.val) % n
· 使用定理 `ZMod.val_neg_of_ne_zero`：val_neg_of_ne_zero {n : Nat} [nz : NeZero n] (a
 : ZMod n) [na : NeZero a] : (-a).val = n - a.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_mod_left`：∀ (x z : ℕ), (x + z) % x = z % x
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `tsub_lt_of_lt`：tsub_lt_of_lt (h : a < b) : a - c < b
-/
theorem val_sub {n : ℕ} [NeZero n] {a b : ZMod n} (h : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  by_cases hb : b = 0
  · cases hb; simp
  · have : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg, val_add, val_neg_of_ne_zero, ← Nat.add_sub_assoc (le_of_lt (val_lt _)),
      add_comm, Nat.add_sub_assoc h, Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))
/-
**ZMod.val_cast_eq_val_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_cast_eq_val_of_lt {m n : Nat} [nzm : NeZero m] {a : ZMod m} (h : a.val
 < n) : (a.cast : ZMod n).val = a.val
参数：h : a.val < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_cast_of_lt`：val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a
 < n) : (a : Fin n).val = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem val_cast_eq_val_of_lt {m n : ℕ} [nzm : NeZero m] {a : ZMod m}
    (h : a.val < n) : (a.cast : ZMod n).val = a.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero <| by rintro (rfl : n = 0); simp at h
  exact Fin.val_cast_of_lt h
/-
**ZMod.cast_cast_zmod_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_cast_zmod_of_le {m n : Nat} [hm : NeZero m] (h : m <= n) (a : ZMod m)
 : (cast (cast a : ZMod n) : ZMod m) = a
参数：h : m <= n；a : ZMod m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.cast_eq_val`：cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a
.val
· 使用定理 `ZMod.val_cast_eq_val_of_lt`：val_cast_eq_val_of_lt {m n : Nat} [nzm : NeZ
ero m] {a : ZMod m} (h : a.val < n) : (a.cast : ZMod n).val = a.val
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
-/
theorem cast_cast_zmod_of_le {m n : ℕ} [hm : NeZero m] (h : m ≤ n) (a : ZMod m) :
    (cast (cast a : ZMod n) : ZMod m) = a := by
  have : NeZero n := ⟨((Nat.zero_lt_of_ne_zero hm.out).trans_le h).ne'⟩
  rw [cast_eq_val, val_cast_eq_val_of_lt (a.val_lt.trans_le h), natCast_zmod_val]
/-
**ZMod.val_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_pow {m n : Nat} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n) 
: (a ^ m).val = a.val ^ m
参数：1 < n；h : a.val ^ m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `ZMod.val_pos`：val_pos {n : Nat} {a : ZMod n} : 0 < a.val ↔ a != 0
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `ZMod.val_mul`：val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b
.val % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem val_pow {m n : ℕ} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n) :
    (a ^ m).val = a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      obtain rfl | ha := eq_or_ne a 0
      · by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow, Nat.zero_lt_of_lt h]
      · exact lt_of_le_of_lt
         (Nat.pow_le_pow_right (by rwa [gt_iff_lt, ZMod.val_pos]) (Nat.le_succ m)) h
    rw [pow_succ, ZMod.val_mul, ih this, ← pow_succ, Nat.mod_eq_of_lt h]
/-
**ZMod.val_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：val_pow_le {m n : Nat} [Fact (1 < n)] {a : ZMod n} : (a ^ m).val <= a.val 
^ m
参数：1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ZMod.val_mul_le`：val_mul_le {n : Nat} (a b : ZMod n) : (a * b).val <= a.
val * b.val
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
-/
theorem val_pow_le {m n : ℕ} [Fact (1 < n)] {a : ZMod n} : (a ^ m).val ≤ a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    apply le_trans (ZMod.val_mul_le _ _)
    apply Nat.mul_le_mul_right _ ih
/-
**ZMod.natAbs_min_of_le_div_two** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：natAbs_min_of_le_div_two (n : Nat) (x y : Int) (he : (x : ZMod n) = y) (hl
 : x.natAbs <= n / 2) : x.natAbs <= y.natAbs
参数：n : Nat；x y : Int；he : (x : ZMod n) = y；hl : x.natAbs <= n / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.intCast_eq_intCast_iff_dvd_sub`：intCast_eq_intCast_iff_dvd_sub (a b
 : Int) (c : Nat) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Nat.div_mul_le_self`：∀ (m n : ℕ), m / n * n ≤ m
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
（共 33 条，此处仅展示前 30 条）
-/
theorem natAbs_min_of_le_div_two (n : ℕ) (x y : ℤ) (he : (x : ZMod n) = y) (hl : x.natAbs ≤ n / 2) :
    x.natAbs ≤ y.natAbs := by
  rw [intCast_eq_intCast_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.natAbs]
  refine le_trans (le_trans ((add_le_add_iff_left _).2 hl) ?_) (Int.natAbs_sub_le _ _)
  rw [add_sub_cancel_right, Int.natAbs_mul, Int.natAbs_natCast]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ <| Int.natAbs_pos.2 hm)
  rw [← mul_two]; apply Nat.div_mul_le_self

end ZMod

/-
**RingHom.ext_zmod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiring R] (f g : ZMod n 
->+* R) : f = g
参数：f g : ZMod n ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
-/
theorem RingHom.ext_zmod {n : ℕ} {R : Type*} [NonAssocSemiring R] (f g : ZMod n →+* R) : f = g := by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : ℤ →+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : ℤ →+* R := g.comp (Int.castRingHom (ZMod n))
  change φ k = ψ k
  rw [φ.ext_int ψ]

namespace ZMod

variable {n : ℕ} {R : Type*}

/-
**ZMod.subsingleton_ringHom** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n ->+* R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext_zmod`：RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiri
ng R] (f g : ZMod n ->+* R) : f = g
-/
instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n →+* R) :=
  ⟨RingHom.ext_zmod⟩
/-
**ZMod.subsingleton_ringEquiv** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.coe_ringHom_inj_iff`：coe_ringHom_inj_iff {R S : Type*} [NonAss
ocSemiring R] [NonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R ->+* S) = g
· 使用定理 `RingHom.ext_zmod`：RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiri
ng R] (f g : ZMod n ->+* R) : f = g
-/
instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZMod.ringHom_map_cast** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ringHom_map_cast [NonAssocRing R] (f : R ->+* ZMod n) (k : ZMod n) : f (ca
st k) = k
参数：f : R ->+* ZMod n；k : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ringHom_map_cast [NonAssocRing R] (f : R →+* ZMod n) (k : ZMod n) : f (cast k) = k := by
  cases n
  · dsimp +instances [ZMod, ZMod.cast] at f k ⊢
    simp
  · dsimp [ZMod.cast]
    rw [map_natCast, natCast_zmod_val]

/-- Any ring homomorphism into `ZMod n` has a right inverse. -/
/-
**ZMod.ringHom_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ringHom_rightInverse [NonAssocRing R] (f : R ->+* ZMod n) : Function.Right
Inverse (cast : ZMod n -> R) f
参数：f : R ->+* ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.ringHom_map_cast`：ringHom_map_cast [NonAssocRing R] (f : R ->+* ZMo
d n) (k : ZMod n) : f (cast k) = k

--- 原说明 ---
Any ring homomorphism into `ZMod n` has a right inverse.
-/
theorem ringHom_rightInverse [NonAssocRing R] (f : R →+* ZMod n) :
    Function.RightInverse (cast : ZMod n → R) f :=
  ringHom_map_cast f

/-- Any ring homomorphism into `ZMod n` is surjective. -/
/-
**ZMod.ringHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ringHom_surjective [NonAssocRing R] (f : R ->+* ZMod n) : Function.Surject
ive f
参数：f : R ->+* ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `ZMod.ringHom_rightInverse`：ringHom_rightInverse [NonAssocRing R] (f : R 
->+* ZMod n) : Function.RightInverse (cast : ZMod n -> R) f

--- 原说明 ---
Any ring homomorphism into `ZMod n` is surjective.
-/
theorem ringHom_surjective [NonAssocRing R] (f : R →+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).surjective

@[simp]
/-
**ZMod.castHom_self** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) :=
  Subsingleton.elim _ _

@[simp]
/-
**ZMod.castHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：castHom_comp {m d : Nat} (hm : n ∣ m) (hd : m ∣ d) : (castHom hm (ZMod n))
.comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZMod n)
参数：hm : n ∣ m；hd : m ∣ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext_zmod`：RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiri
ng R] (f g : ZMod n ->+* R) : f = g
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
-/
lemma castHom_comp {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (castHom hm (ZMod n)).comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZMod n) :=
  RingHom.ext_zmod _ _

section lift

variable (n) {A : Type*} [AddGroup A]

/-- The map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
/-
**ZMod.lift** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：lift : { f : Int ->+ A // f n = 0 } ≃ (ZMod n ->+ A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a

--- 原说明 ---
The map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.
-/
def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
  (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_intCastAddHom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          exact h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).liftOfRightInverse cast intCast_zmod_cast

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
/-
**ZMod.lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：lift_coe (x : Int) : lift n f (x : ZMod n) = f.val x
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.liftOfRightInverse_comp_apply`：∀ {G₁ : Type u_5} {G₂ : Type
 u_6} {G₃ : Type u_7} [inst : AddGroup G₁] [inst_1 : AddGroup G₂] [inst_2 : AddG
roup G₃]   (f : G₁ →+ G₂) (f_neg…
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f.val x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _
/-
**ZMod.lift_castAddHom** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：lift_castAddHom (x : Int) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.liftOfRightInverse_comp_apply`：∀ {G₁ : Type u_5} {G₂ : Type
 u_6} {G₃ : Type u_7} [inst : AddGroup G₁] [inst_1 : AddGroup G₂] [inst_2 : AddG
roup G₃]   (f : G₁ →+ G₂) (f_neg…
· 使用定理 `ZMod.intCast_zmod_cast`：intCast_zmod_cast (a : ZMod n) : ((cast a : Int)
 : ZMod n) = a
-/
theorem lift_castAddHom (x : ℤ) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

@[simp]
/-
**ZMod.lift_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：lift_comp_coe : ZMod.lift n f ∘ ((↑) : Int -> _) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZMod.lift_coe`：lift_coe (x : Int) : lift n f (x : ZMod n) = f.val x
-/
theorem lift_comp_coe : ZMod.lift n f ∘ ((↑) : ℤ → _) = f :=
  funext <| lift_coe _ _

@[simp]
/-
**ZMod.lift_comp_castAddHom** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `ZMod.lift_castAddHom`：lift_castAddHom (x : Int) : lift n f (Int.castAddH
om (ZMod n) x) = f.1 x
-/
theorem lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f :=
  AddMonoidHom.ext <| lift_castAddHom _ _
/-
**ZMod.lift_injective** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：lift_injective {f : {f : Int ->+ A // f n = 0}} : Injective (lift n f) ↔ f
orall m, f.1 m = 0 -> (m : ZMod n) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `ZMod.lift_coe`：lift_coe (x : Int) : lift n f (x : ZMod n) = f.val x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lift_injective {f : {f : ℤ →+ A // f n = 0}} :
    Injective (lift n f) ↔ ∀ m, f.1 m = 0 → (m : ZMod n) = 0 := by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    ZMod.intCast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

end lift

end ZMod

/-!
### Groups of bounded torsion

For `G` a group and `n` a natural number, `G` having torsion dividing `n`
(`∀ x : G, n • x = 0`) can be derived from `Module R G` where `R` has characteristic dividing `n`.

It is however painful to have the API for such groups `G` stated in this generality, as `R` does not
appear anywhere in the lemmas' return type. Instead of writing the API in terms of a general `R`, we
therefore specialise to the canonical ring of order `n`, namely `ZMod n`.

This spelling `Module (ZMod n) G` has the extra advantage of providing the canonical action by
`ZMod n`. It is however Type-valued, so we might want to acquire a Prop-valued version in the
future.
-/

section Module
variable {n : ℕ} {S G : Type*} [AddCommGroup G] [SetLike S G] [AddSubgroupClass S G] {K : S} {x : G}

section general
variable [Module (ZMod n) G] {x : G}

/-
**zmod_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zmod_smul_mem (hx : x in K) : forall a : ZMod n, a • x in K
参数：hx : x in K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
-/
lemma zmod_smul_mem (hx : x ∈ K) : ∀ a : ZMod n, a • x ∈ K := by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

/-- This cannot be made an instance because of the `[Module (ZMod n) G]` argument and the fact that
`n` only appears in the second argument of `SMulMemClass`, which is an `OutParam`. -/
/-
**smulMemClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smulMemClass : SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zmod_smul_mem`：zmod_smul_mem (hx : x in K) : forall a : ZMod n, a • x in
 K

--- 原说明 ---
This cannot be made an instance because of the `[Module (ZMod n) G]` argument an
d the fact that
`n` only appears in the second argument of `SMulMemClass`, which is an `OutParam
`.
-/
lemma smulMemClass : SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx := zmod_smul_mem hx _

namespace AddSubgroupClass

/-
**AddSubgroupClass.instZModSMul** 是 Mathlib 中的一个实例，位于命名空间 `AddSubgroupClass`。
形式化陈述：instZModSMul : SMul (ZMod n) K where smul a x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZModSMul : SMul (ZMod n) K where smul a x := ⟨a • x, zmod_smul_mem x.2 _⟩
/-
**AddSubgroupClass.coe_zmod_smul** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroupClass`。
形式化陈述：∀ {n : ℕ} {S : Type u_1} {G : Type u_2} [inst : AddCommGroup G] [inst_1 : 
SetLike S G] [inst_2 : AddSubgroupClass S G]   {K : S} [inst_3 : _root_.Module (
ZMod n) G] (a : ZMod n) (x : ↥K), ↑(a • x) = a • ↑x
参数：ZMod n；a : ZMod n；x : ↥K；a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zmod_smul (a : ZMod n) (x : K) : ↑(a • x) = (a • x : G) := rfl
/-
**AddSubgroupClass.instZModModule** 是 Mathlib 中的一个实例，位于命名空间 `AddSubgroupClass`。
形式化陈述：instZModModule : Module (ZMod n) K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZModModule : Module (ZMod n) K := fast_instance%
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

end AddSubgroupClass

variable (n)

/-
**ZModModule.char_nsmul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.char_nsmul_eq_zero (x : G) : n • x = 0
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ZModModule.char_nsmul_eq_zero (x : G) : n • x = 0 := by
  simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

variable (G) in
/-
**ZModModule.char_ne_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.char_ne_one [Nontrivial G] : n != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `ZModModule.char_nsmul_eq_zero`：ZModModule.char_nsmul_eq_zero (x : G) : n
 • x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ZModModule.char_ne_one [Nontrivial G] : n ≠ 1 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  exact hx <| by simpa using char_nsmul_eq_zero 1 x

variable (G) in
/-
**ZModModule.two_le_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.two_le_char [NeZero n] [Nontrivial G] : 2 <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `ZModModule.char_ne_one`：ZModModule.char_ne_one [Nontrivial G] : n != 1
-/
lemma ZModModule.two_le_char [NeZero n] [Nontrivial G] : 2 ≤ n := by
  have := NeZero.ne n
  have := char_ne_one n G
  lia
/-
**ZModModule.periodicPts_add_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.periodicPts_add_left [NeZero n] (x : G) : periodicPts (x + ·) =
 .univ
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_left_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ),
 (fun x => a + x)^[n] = fun x => n • a + x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ZModModule.char_nsmul_eq_zero`：ZModModule.char_nsmul_eq_zero (x : G) : n
 • x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.isFixedPt_id`：isFixedPt_id (x : α) : IsFixedPt id x
-/
lemma ZModModule.periodicPts_add_left [NeZero n] (x : G) : periodicPts (x + ·) = .univ :=
  Set.eq_univ_of_forall fun y ↦ ⟨n, NeZero.pos n, by
    simpa [char_nsmul_eq_zero, IsPeriodicPt] using! isFixedPt_id _⟩

end general

section two
variable [Module (ZMod 2) G]

/-
**ZModModule.add_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.add_self (x : G) : x + x = 0
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用引理 `ZModModule.char_nsmul_eq_zero`：ZModModule.char_nsmul_eq_zero (x : G) : n
 • x = 0
-/
lemma ZModModule.add_self (x : G) : x + x = 0 := by
  simpa [two_nsmul] using char_nsmul_eq_zero 2 x
/-
**ZModModule.neg_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.neg_eq_self (x : G) : -x = x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `ZModModule.add_self`：ZModModule.add_self (x : G) : x + x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ZModModule.neg_eq_self (x : G) : -x = x := by simp [add_self, eq_comm, ← sub_eq_zero]
/-
**ZModModule.sub_eq_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.sub_eq_add (x y : G) : x - y = x + y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ZModModule.neg_eq_self`：ZModModule.neg_eq_self (x : G) : -x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ZModModule.sub_eq_add (x y : G) : x - y = x + y := by simp [neg_eq_self, sub_eq_add_neg]
/-
**ZModModule.add_add_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZModModule.add_add_add_cancel (x y z : G) : (x + y) + (y + z) = x + z
参数：x y z : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZModModule.sub_eq_add`：ZModModule.sub_eq_add (x y : G) : x - y = x + y
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
-/
lemma ZModModule.add_add_add_cancel (x y z : G) : (x + y) + (y + z) = x + z := by
  simpa [sub_eq_add] using sub_add_sub_cancel x y z

end two
end Module

section Group
variable {α : Type*} [Group α] {n : ℕ}

@[to_additive (attr := simp) nsmul_zmod_val_inv_nsmul]
/-
**pow_zmod_val_inv_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_zmod_val_inv_pow (hn : (Nat.card α).gcd n = 1) (a : α) : (a ^ (n⁻¹ : Z
Mod (Nat.card α)).val) ^ n = a
参数：hn : (Nat.card α).gcd n = 1；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用引理 `pow_mod_natCard`：pow_mod_natCard {G} [Group G] (a : G) (n : Nat) : a ^ (
n % Nat.card G) = a ^ n
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `ZMod.mul_val_inv`：mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).
val : ZMod n) = 1
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `ZMod.val_one_eq_one_mod`：val_one_eq_one_mod (n : Nat) : (1 : ZMod n).val
 = 1 % n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma pow_zmod_val_inv_pow (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ (n⁻¹ : ZMod (Nat.card α)).val) ^ n = a := by
  replace hn : (Nat.card α).Coprime n := hn
  rw [← pow_mul', ← pow_mod_natCard, ← ZMod.val_natCast, Nat.cast_mul, ZMod.mul_val_inv hn.symm,
    ZMod.val_one_eq_one_mod, pow_mod_natCard, pow_one]

@[to_additive (attr := simp) zmod_val_inv_nsmul_nsmul]
/-
**pow_pow_zmod_val_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_pow_zmod_val_inv (hn : (Nat.card α).gcd n = 1) (a : α) : (a ^ n) ^ (n⁻
¹ : ZMod (Nat.card α)).val = a
参数：hn : (Nat.card α).gcd n = 1；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_right_comm`：pow_right_comm (a : M) (m n : Nat) : (a ^ m) ^ n = (a ^ 
n) ^ m
· 使用引理 `pow_zmod_val_inv_pow`：pow_zmod_val_inv_pow (hn : (Nat.card α).gcd n = 1)
 (a : α) : (a ^ (n⁻¹ : ZMod (Nat.card α)).val) ^ n = a
-/
lemma pow_pow_zmod_val_inv (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ n) ^ (n⁻¹ : ZMod (Nat.card α)).val = a := by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

end Group

open ZMod

/-- The range of `(m * · + k)` on natural numbers is the set of elements `≥ k` in the
residue class of `k` mod `m`. -/
/-
**Nat.range_mul_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.range_mul_add (m k : Nat) : Set.range (fun n : Nat => m * n + k) = {n 
: Nat | (n : ZMod m) = k ∧ k <= n}
参数：m k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The range of `(m * · + k)` on natural numbers is the set of elements `≥ k` in th
e
residue class of `k` mod `m`.
-/
lemma Nat.range_mul_add (m k : ℕ) :
    Set.range (fun n : ℕ ↦ m * n + k) = {n : ℕ | (n : ZMod m) = k ∧ k ≤ n} := by
  ext n
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  conv => enter [1, 1, y]; rw [add_comm, eq_comm]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨?_, le_iff_exists_add.mpr ⟨_, ha⟩⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · simpa using congr_arg ((↑) : ℕ → ZMod m) ha
  · obtain ⟨a, ha⟩ := le_iff_exists_add.mp H₂
    simp only [ha, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff] at H₁
    obtain ⟨b, rfl⟩ := H₁
    exact ⟨b, ha⟩

/-- Equivalence between `ℕ` and `ZMod N × ℕ`, sending `n` to `(n mod N, n / N)`. -/
/-
**Nat.residueClassesEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.residueClassesEquiv (N : Nat) [NeZero N] : Nat ≃ ZMod N × Nat where to
Fun n
参数：N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `ℕ` and `ZMod N × ℕ`, sending `n` to `(n mod N, n / N)`.
-/
def Nat.residueClassesEquiv (N : ℕ) [NeZero N] : ℕ ≃ ZMod N × ℕ where
  toFun n := (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, cast_add, cast_mul, natCast_self, zero_mul, natCast_val,
        cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val, mul_add_div (NeZero.pos _),
        (Nat.div_eq_zero_iff).2 <| .inr p.1.val_lt, add_zero]

-- there is a faster proof with Module.toAddMonoidEnd
/-
**ZMod.instSubsingletonModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZMod.instSubsingletonModule (n : Nat) (M : Type*) [AddCommMonoid M] : Subs
ingleton (Module (ZMod n) M)
参数：n : Nat；M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.ext'`：Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMo
noid M] (P Q : Module R M) (w : forall (r : R) (m : M), (haveI
· 使用定理 `ZMod.natCast_zmod_surjective`：natCast_zmod_surjective [NeZero n] : Funct
ion.Surjective ((↑) : Nat -> ZMod n)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
-/
instance ZMod.instSubsingletonModule (n : ℕ) (M : Type*) [AddCommMonoid M] :
    Subsingleton (Module (ZMod n) M) := by
  obtain _ | n := n
  · exact inferInstanceAs (Subsingleton (Module ℤ M))
  refine ⟨fun m1 m2 ↦ Module.ext' _ _ fun r m ↦ ?_⟩
  obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
  rw [(letI := m1; Nat.cast_smul_eq_nsmul _ r m), Nat.cast_smul_eq_nsmul _ r m]
