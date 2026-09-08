/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public meta import Mathlib.Data.Rat.Floor

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Rat.Floor

/-!
# Floor Function for Non-negative Rational Numbers

## Summary

We define the `FloorSemiring` instance on `ℚ≥0`, and relate its operators to `NNRat.cast`.

Note that we cannot talk about `Int.fract`, which currently only works for rings.

## Tags

nnrat, rationals, ℚ≥0, floor
-/

@[expose] public section

assert_not_exists Finset

namespace NNRat

/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FloorSemiring ℚ≥0 where
  floor q := ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]
/-
**NNRat.floor_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：floor_coe (q : Rat>=0) : ⌊(q : Rat)⌋₊ = ⌊q⌋₊
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem floor_coe (q : ℚ≥0) : ⌊(q : ℚ)⌋₊ = ⌊q⌋₊ := rfl

@[simp, norm_cast]
/-
**NNRat.ceil_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ceil_coe (q : Rat>=0) : ⌈(q : Rat)⌉₊ = ⌈q⌉₊
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ceil_coe (q : ℚ≥0) : ⌈(q : ℚ)⌉₊ = ⌈q⌉₊ := rfl

@[simp, norm_cast]
/-
**NNRat.coe_floor** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_floor (q : Rat>=0) : ↑⌊q⌋₊ = ⌊(q : Rat)⌋
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_floor_eq_floor`：Int.natCast_floor_eq_floor (ha : 0 <= a) : (
⌊a⌋₊ : Int) = ⌊a⌋
· 使用定理 `NNRat.coe_nonneg`：coe_nonneg (q : Rat>=0) : (0 : Rat) <= q
-/
theorem coe_floor (q : ℚ≥0) : ↑⌊q⌋₊ = ⌊(q : ℚ)⌋ := Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]
/-
**NNRat.coe_ceil** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_ceil (q : Rat>=0) : ↑⌈q⌉₊ = ⌈(q : Rat)⌉
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_ceil_eq_ceil`：Int.natCast_ceil_eq_ceil (ha : 0 <= a) : (⌈a⌉₊
 : Int) = ⌈a⌉
· 使用定理 `NNRat.coe_nonneg`：coe_nonneg (q : Rat>=0) : (0 : Rat) <= q
-/
theorem coe_ceil (q : ℚ≥0) : ↑⌈q⌉₊ = ⌈(q : ℚ)⌉ := Int.natCast_ceil_eq_ceil q.coe_nonneg
/-
**NNRat.floor_def** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), ⌊q⌋₊ = q.num / q.den
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `NNRat.coe_floor`：coe_floor (q : Rat>=0) : ↑⌊q⌋₊ = ⌊(q : Rat)⌋
· 使用定理 `Rat.floor_def'`：∀ {q : ℚ}, ⌊q⌋ = q.num / ↑q.den
· 使用定理 `Int.natCast_ediv`：∀ (m n : ℕ), ↑(m / n) = ↑m / ↑n
· 使用定理 `NNRat.den_coe`：∀ {q : ℚ≥0}, (↑q).den = q.den
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
-/
protected theorem floor_def (q : ℚ≥0) : ⌊q⌋₊ = q.num / q.den := by
  rw [← Int.natCast_inj, NNRat.coe_floor, Rat.floor_def', Int.natCast_ediv, den_coe, num_coe]

section Semifield

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

@[simp, norm_cast]
/-
**NNRat.floor_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：floor_cast (x : Rat>=0) : ⌊(x : K)⌋₊ = ⌊x⌋₊
参数：x : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.floor_eq_iff`：floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < 
↑n + 1
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem floor_cast (x : ℚ≥0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ :=
  (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]
/-
**NNRat.ceil_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ceil_cast (x : Rat>=0) : ⌈(x : K)⌉₊ = ⌈x⌉₊
参数：x : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `Nat.ceil_zero`：ceil_zero : ⌈(0 : R)⌉₊ = 0
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ceil_eq_iff`：ceil_eq_iff (hn : n != 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a
 <= n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem ceil_cast (x : ℚ≥0) : ⌈(x : K)⌉₊ = ⌈x⌉₊ := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

end Semifield

section Field

variable {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[simp, norm_cast]
/-
**NNRat.intFloor_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：intFloor_cast (x : Rat>=0) : ⌊(x : K)⌋ = ⌊(x : Rat)⌋
参数：x : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_floor`：coe_floor (q : Rat>=0) : ↑⌊q⌋₊ = ⌊(q : Rat)⌋
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Nat.floor_eq_iff`：floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < 
↑n + 1
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem intFloor_cast (x : ℚ≥0) : ⌊(x : K)⌋ = ⌊(x : ℚ)⌋ := by
  rw [Int.floor_eq_iff, ← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one, ← Nat.floor_eq_iff zero_le]

@[simp, norm_cast]
/-
**NNRat.intCeil_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：intCeil_cast (x : Rat>=0) : ⌈(x : K)⌉ = ⌈(x : Rat)⌉
参数：x : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ceil_eq_iff`：ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_ceil`：coe_ceil (q : Rat>=0) : ↑⌈q⌉₊ = ⌈(q : Rat)⌉
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `NNRat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat>=0 -> K)
· 使用定理 `Nat.ceil_lt_add_one`：ceil_lt_add_one (ha : 0 <= a) : (⌈a⌉₊ : R) < a + 1
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NNRat.cast_le_natCast`：cast_le_natCast {m : Rat>=0} {n : Nat} : (m : K) 
<= n ↔ m <= (n : Rat>=0)
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
-/
theorem intCeil_cast (x : ℚ≥0) : ⌈(x : K)⌉ = ⌈(x : ℚ)⌉ := by
  rw [Int.ceil_eq_iff, ← coe_ceil, sub_lt_iff_lt_add]
  constructor
  · exact_mod_cast NNRat.cast_strictMono <| Nat.ceil_lt_add_one zero_le
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

end Field

@[norm_cast]
/-
**NNRat.floor_natCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：floor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat>=0)⌋₊ = n / d
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.natFloor_natCast_div_natCast`：natFloor_natCast_div_natCast (n d : Na
t) : ⌊(↑n / ↑d : Rat)⌋₊ = n / d
-/
theorem floor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ≥0)⌋₊ = n / d :=
  Rat.natFloor_natCast_div_natCast n d

end NNRat

namespace Mathlib.Meta.NormNum

open Qq

/-!
### `norm_num` extension for `Nat.ceil`
-/

/-
**Mathlib.Meta.NormNum.IsNat.natCeil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.IsNat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [IsStrictOrd
eredRing R] [inst_3 : FloorSemiring R] (r : R)   (m : ℕ), Mathlib.Meta.NormNum.I
sNat r m → Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ m
参数：r : R；m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `norm_num` extension for `Nat.ceil`
-/
theorem IsNat.natCeil {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : ℕ) : IsNat r m → IsNat (⌈r⌉₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsInt.natCeil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.IsInt`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [inst_1 : LinearOrder R] [IsStrictOrdered
Ring R] [inst_3 : FloorSemiring R] (r : R)   (m : ℕ), Mathlib.Meta.NormNum.IsInt
 r (Int.negOfNat m) → Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ 0
参数：r : R；m : ℕ；Int.negOfNat m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem IsInt.natCeil {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
    (r : R) (m : ℕ) : IsInt r (.negOfNat m) → IsNat (⌈r⌉₊) 0 := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsNNRat.natCeil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsNNRat`。
形式化陈述：∀ {R : Type u_1} [inst : Semifield R] [inst_1 : LinearOrder R] [IsStrictOr
deredRing R] [inst_3 : FloorSemiring R]   (r : R) (n d : ℕ),   Mathlib.Meta.Norm
Num.IsNNRat r n d → ∀ (res : ℕ), ⌈↑n / ↑d⌉₊ = res → Mathlib.Meta.NormNum.IsNat ⌈
r⌉₊ res
参数：r : R；n d : ℕ；res : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `NNRat.ceil_cast`：ceil_cast (x : Rat>=0) : ⌈(x : K)⌉₊ = ⌈x⌉₊
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNRat.cast_div`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.natCeil {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsNNRat r n d) (res : ℕ)
    (hres : ⌈(n / d : ℚ≥0)⌉₊ = res) : IsNat ⌈r⌉₊ res := by
  constructor
  rw [← hres, h.to_eq rfl rfl, ← @NNRat.ceil_cast R]
  simp
/-
**Mathlib.Meta.NormNum.IsRat.natCeil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.IsRat`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOrder R] [IsStrictOrdere
dRing R] [inst_3 : FloorSemiring R] (r : R)   (n d : ℕ), Mathlib.Meta.NormNum.Is
Rat r (Int.negOfNat n) d → Mathlib.Meta.NormNum.IsNat ⌈r⌉₊ 0
参数：r : R；n d : ℕ；Int.negOfNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem IsRat.natCeil {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsRat r (.negOfNat n) d) : IsNat ⌈r⌉₊ 0 := by
  constructor
  simp [h.neg_to_eq, div_nonneg]

open Lean in
/-- `norm_num` extension for `Nat.ceil` -/
@[norm_num ⌈_⌉₊]
meta def evalNatCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α $instSemiring $instPartialOrder $instFloorSemiring $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(IsNat.natCeil $x _ $pb)
    | .isNegNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsInt.natCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let instSemifield ← synthInstanceQ q(Semifield $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := mkRawNatLit (⌈q⌉₊)
      letI : $z =Q ⌈($n / $d : NNRat)⌉₊ := ⟨⟩
      return .isNat q(inferInstance) z q(IsNNRat.natCeil _ $n $d $h $z rfl)
    | .isNegNNRat _ q n d h => do
      let instField ← synthInstanceQ q(Field $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsRat.natCeil _ _ _ $h)
  | _, _, _ => failure

end Mathlib.Meta.NormNum

