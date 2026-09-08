/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn, Sabbir Rahman
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas about powers in ordered fields.
-/

public section


variable {α : Type*}

open Function Int

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

/-
**Even.zpow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrdere
dRing α] {n : ℤ},   Even n → ∀ (a : α), 0 ≤ a ^ n
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add'`：zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 
0) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Even.zpow_nonneg (hn : Even n) (a : α) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _
/-
**zpow_two_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_two_nonneg (a : α) : 0 <= a ^ (2 : Int)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.zpow_nonneg`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrde
r α] [IsStrictOrderedRing α] {n : ℤ},   Even n → ∀ (a : α), 0 ≤ a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
-/
lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := even_two.zpow_nonneg _
/-
**zpow_neg_two_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_neg_two_nonneg (a : α) : 0 <= a ^ (-2 : Int)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.zpow_nonneg`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrde
r α] [IsStrictOrderedRing α] {n : ℤ},   Even n → ∀ (a : α), 0 ≤ a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_neg_two`：even_neg_two : Even (-2 : α)
-/
lemma zpow_neg_two_nonneg (a : α) : 0 ≤ a ^ (-2 : ℤ) := even_neg_two.zpow_nonneg _
/-
**Even.zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrdere
dRing α] {a : α} {n : ℤ},   Even n → a ≠ 0 → 0 < a ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Even.zpow_nonneg`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrde
r α] [IsStrictOrderedRing α] {n : ℤ},   Even n → ∀ (a : α), 0 ≤ a ^ n
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
-/
protected lemma Even.zpow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)
/-
**zpow_two_pos_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_two_pos_of_ne_zero (ha : a != 0) : 0 < a ^ (2 : Int)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.zpow_pos`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α
] [IsStrictOrderedRing α] {a : α} {n : ℤ},   Even n → a ≠ 0 → 0 < a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
-/
lemma zpow_two_pos_of_ne_zero (ha : a ≠ 0) : 0 < a ^ (2 : ℤ) := even_two.zpow_pos ha
/-
**Even.zpow_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Even.zpow_pos_iff (hn : Even n) (h : n != 0) : 0 < a ^ n ↔ a != 0
参数：hn : Even n；h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add'`：zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 
0) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `zpow_ne_zero_iff`：zpow_ne_zero_iff {n : Int} (hn : n != 0) : a ^ n != 0 
↔ a != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Even.zpow_pos_iff (hn : Even n) (h : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]
/-
**Odd.zpow_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `zpow_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Parti
alOrder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 ≤ a → ∀ (n : 
ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one₀`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] {a : G₀}, a ≠
 0 → ∀ (n : ℤ), a ^ (n + 1) = a ^ n * a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `Even.zpow_pos`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α
] [IsStrictOrderedRing α] {a : α} {n : ℤ},   Even n → a ≠ 0 → 0 < a ^ n
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha
/-
**Odd.zpow_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Odd`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrdere
dRing α] {a : α} {n : ℤ},   Odd n → (0 ≤ a ^ n ↔ 0 ≤ a)
参数：0 ≤ a ^ n ↔ 0 ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Odd.zpow_neg_iff`：Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0
-/
protected lemma Odd.zpow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff
/-
**Odd.zpow_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n <= 0 ↔ a <= 0
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Odd.zpow_neg_iff`：Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0
· 使用引理 `zpow_eq_zero_iff`：zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔
 a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用引理 `Even.zero`：Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.zpow_neg_iff, zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero
/-
**Odd.zpow_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Odd.zpow_nonpos_iff`：Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n <= 0 ↔ a <
= 0
-/
lemma Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp]
/-
**abs_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_zpow (a : α) (p : Int) : |a ^ p| = |a| ^ p
参数：a : α；p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem abs_zpow (a : α) (p : ℤ) : |a ^ p| = |a| ^ p := map_zpow₀ absHom a p
/-
**abs_neg_one_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_neg_one_zpow (p : Int) : |(-1 : α) ^ p| = 1
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zpow`：abs_zpow (a : α) (p : Int) : |a ^ p| = |a| ^ p
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_neg_one_zpow (p : ℤ) : |(-1 : α) ^ p| = 1 := by simp

omit [IsStrictOrderedRing α] in
/-
**Even.zpow_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Even.zpow_abs {p : Int} (hp : Even p) (a : α) : |a| ^ p = a ^ p
参数：hp : Even p；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Even.neg_zpow`：Even.neg_zpow : Even n -> forall a : α, (-a) ^ n = a ^ n
-/
theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) : |a| ^ p = a ^ p := by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]
/-
**zpow_eq_zpow_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_zpow_iff_of_ne_zero₀ (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
/-
**zpow_eq_zpow_iff_cases** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_zpow_iff_cases₀ : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]
/-
**zpow_eq_one_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_one_iff_of_ne_zero₀ (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_of_ne_zero₀ hn]
/-
**zpow_eq_one_iff_cases** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_one_iff_cases₀ : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_cases₀]
/-
**zpow_eq_neg_zpow_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_neg_zpow_iff₀ (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, zpow_neg, ← inv_neg, pow_eq_neg_pow_iff hb, inv_inj,
      zpow_natCast]
    simp [parity_simps]
/-
**zpow_eq_neg_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_neg_one_iff₀ : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

/-! ### Bernoulli's inequality -/

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
/-
**Nat.cast_le_pow_sub_div_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : Nat) : (n : α) <= (a ^ n - 1)
 / (a - 1)
参数：H : 1 < a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `le_sub_left_of_add_le`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : 
LE α] [AddLeftMono α] {a b c : α}, a + b ≤ c → b ≤ c - a
· 使用引理 `one_add_mul_sub_le_pow`：one_add_mul_sub_le_pow (H : -1 <= a) (n : Nat) :
 1 + n * (a - 1) <= a ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Bernoulli's inequality reformulated to estimate `(n : α)`.
-/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff₀ (sub_pos.2 H)).2 <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`Nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
/-
**Nat.cast_le_pow_div_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cast_le_pow_div_sub (H : 1 < a) (n : Nat) : (n : α) <= a ^ n / (a - 1)
参数：H : 1 < a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_le_pow_sub_div_sub`：Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n 
: Nat) : (n : α) <= (a ^ n - 1) / (a - 1)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`Nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the 
numerator.
-/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
  (n.cast_le_pow_sub_div_sub H).trans <|
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℤ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ ^ (_ : ℤ), Pow.pow _ (_ : ℤ)]
meta def evalZPow : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℤ)) ← withReducible (whnf e) | throwError "not ^"
  match (dependent := true) pα? with
  | none =>
    match ← core zα pα? a with
    | .nonzero pa =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonzero q(zpow_ne_zero $b $pa))
    | _ => pure .none
  | some pα =>
    let result ← catchNone do
      let _a ← synthInstanceQ q(Field $α)
      let _a ← synthInstanceQ q(LinearOrder $α)
      let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      match ← whnfR b with
      | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ =>
        guard (n % 2 = 0)
        have m : Q(ℕ) := mkRawNatLit (n / 2)
        haveI' : $b =Q $m + $m := ⟨⟩
        haveI' : $e =Q $a ^ $b := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
      | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
        let b' ← whnfR b'
        let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ -n where n is a literal"
        let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a ^ -n where n is a literal"
        guard (n % 2 = 0)
        have m : Q(ℕ) := mkRawNatLit (n / 2)
        haveI' : $b =Q (-$m) + (-$m) := ⟨⟩
        haveI' : $e =Q $a ^ $b := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
      | _ => throwError "not a ^ n where n is a literal or a negated literal"
    orElse result do
      let ra ← core zα pα a
      let ofNonneg (pa : Q(0 ≤ $a))
          (_oα : Q(Semifield $α)) (_oα : Q(LinearOrder $α)) (_oα : Q(IsStrictOrderedRing $α)) :
          MetaM (Strictness zα e pα) := do
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        pure (.nonnegative q(zpow_nonneg $pa $b))
      let ofNonzero (pa : Q($a ≠ 0)) (_oα : Q(GroupWithZero $α)) : MetaM (Strictness zα e pα) := do
        haveI' : $e =Q $a ^ $b := ⟨⟩
        let _a ← synthInstanceQ q(GroupWithZero $α)
        assumeInstancesCommute
        pure (.nonzero q(zpow_ne_zero $b $pa))
      match ra with
      | .positive pa =>
        try
          let _a ← synthInstanceQ q(Semifield $α)
          let _a ← synthInstanceQ q(LinearOrder $α)
          let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
          assumeInstancesCommute
          haveI' : $e =Q $a ^ $b := ⟨⟩
          pure (.positive q(zpow_pos $pa $b))
        catch e : Exception =>
          trace[Tactic.positivity.failure] "{e.toMessageData}"
          let sα ← synthInstanceQ q(Semifield $α)
          let oα ← synthInstanceQ q(LinearOrder $α)
          let iα ← synthInstanceQ q(IsStrictOrderedRing $α)
          orElse (← catchNone (ofNonneg q(le_of_lt $pa) sα oα iα))
            (ofNonzero q(ne_of_gt $pa) q(inferInstance))
      | .nonnegative pa =>
        ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
                    (← synthInstanceQ (_ : Q(Type u))) (← synthInstanceQ (_ : Q(Prop)))
      | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
      | .none => pure .none

end Mathlib.Meta.Positivity

