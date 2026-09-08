/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Fin.Rev

/-!
# Fin is a group

This file contains the additive and multiplicative monoid instances on `Fin n`.

See note [foundational algebra order theory].
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Nat

namespace Fin
variable {n : ℕ}

/-! ### Instances -/

/-
**Fin.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：addCommSemigroup (n : Nat) : AddCommSemigroup (Fin n) where add_assoc
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Instances
-/
instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [add_def, Nat.add_assoc]
  add_comm := by simp [add_def, Nat.add_comm]
/-
**Fin.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：addCommMonoid (n : Nat) [NeZero n] : AddCommMonoid (Fin n) where zero_add
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.zero_add`：∀ {n : ℕ} [inst : NeZero n] (k : Fin n), 0 + k = k
· 使用定理 `Fin.add_zero`：∀ {n : ℕ} [inst : NeZero n] (k : Fin n), k + 0 = k
-/
instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) where
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n

/--
This is not a global instance, but can introduced locally using `open Fin.NatCast in ...`.

This is not an instance because the `binop%` elaborator assumes that
there are no non-trivial coercion loops,
but this instance would introduce a coercion from `Nat` to `Fin n` and back.
Non-trivial loops lead to undesirable and counterintuitive elaboration behavior.

For example, for `x : Fin k` and `n : Nat`,
it causes `x < n` to be elaborated as `x < ↑n` rather than `↑x < n`,
silently introducing wraparound arithmetic.
-/
@[instance_reducible]
/-
**Fin.instAddMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where __
参数：n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not a global instance, but can introduced locally using `open Fin.NatCas
t in ...`.

This is not an instance because the `binop%` elaborator assumes that
there are no non-trivial coercion loops,
but this instance would introduce a coercion from `Nat` to `Fin n` and back.
Non-trivial loops lead to undesirable and counterintuitive elaboration behavior.

For example, for `x : Fin k` and `n : Nat`,
it causes `x < n` to be elaborated as `x < ↑n` rather than `↑x < n`,
silently introducing wraparound arithmetic.
-/
def instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where
  __ := (inferInstance : AddCommMonoid (Fin n))
  natCast i := Fin.ofNat n i
  natCast_zero := rfl
  natCast_succ _ := Fin.ext (add_mod _ _ _)

namespace NatCast

attribute [scoped instance] Fin.instAddMonoidWithOne

end NatCast

/-
**Fin.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：addCommGroup (n : Nat) [NeZero n] : AddCommGroup (Fin n) where __
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup (n : ℕ) [NeZero n] : AddCommGroup (Fin n) where
  __ := addCommMonoid n
  __ := neg n
  neg_add_cancel := fun ⟨a, ha⟩ ↦
    Fin.ext <| (Nat.mod_add_mod _ _ _).trans <| by
      rw [Fin.val_zero, Nat.sub_add_cancel, Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦
    Fin.ext <| by simp [Fin.sub_def, Fin.neg_def, Fin.add_def, Nat.add_comm]
  zsmul := zsmulRec

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
/-
**Fin.instInvolutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instInvolutiveNeg (n : Nat) : InvolutiveNeg (Fin n) where neg_neg
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `
Fin 0` too.
-/
instance instInvolutiveNeg (n : ℕ) : InvolutiveNeg (Fin n) where
  neg_neg := Nat.casesOn n finZeroElim fun _i ↦ neg_neg

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
/-
**Fin.instIsCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instIsCancelAdd (n : Nat) : IsCancelAdd (Fin n) where add_left_cancel
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `
Fin 0` too.
-/
instance instIsCancelAdd (n : ℕ) : IsCancelAdd (Fin n) where
  add_left_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_right_cancel

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
/-
**Fin.instAddLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instAddLeftCancelSemigroup (n : Nat) : AddLeftCancelSemigroup (Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `
Fin 0` too.
-/
instance instAddLeftCancelSemigroup (n : ℕ) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
/-
**Fin.instAddRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instAddRightCancelSemigroup (n : Nat) : AddRightCancelSemigroup (Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `
Fin 0` too.
-/
instance instAddRightCancelSemigroup (n : ℕ) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-! ### Miscellaneous lemmas -/

open scoped Fin.NatCast Fin.IntCast in
/-- Variant of `Fin.intCast_def` with `Nat.cast` on the RHS. -/
/-
**Fin.intCast_def'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：intCast_def' {n : Nat} [NeZero n] (x : Int) : (x : Fin n) = if 0 <= x then
 ↑x.natAbs else -↑x.natAbs
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.intCast_def`：∀ {n : ℕ} [inst : NeZero n] (x : ℤ), ↑x = if 0 ≤ x then
 Fin.ofNat n x.natAbs else -Fin.ofNat n x.natAbs

--- 原说明 ---
Variant of `Fin.intCast_def` with `Nat.cast` on the RHS.
-/
theorem intCast_def' {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then ↑x.natAbs else -↑x.natAbs :=
  Fin.intCast_def _
/-
**Fin.coe_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1
参数：a : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Fin.coe_neg_one`：coe_neg_one : ↑(-1 : Fin (n + 1)) = n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Fin.val_sub_one_of_ne_zero`：val_sub_one_of_ne_zero {i : Fin n} : haveI
-/
lemma coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  exact val_sub_one_of_ne_zero h

@[simp]
/-
**Fin.lt_sub_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_sub_iff {n : Nat} {a b : Fin n} : a < a - b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.coe_int_sub_eq_ite`：coe_int_sub_eq_ite {n : Nat} (u v : Fin n) : ((u
 - v : Fin n) : Int) = if v <= u then (u - v : Int) else (u - v : Int) + n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma lt_sub_iff {n : ℕ} {a b : Fin n} : a < a - b ↔ a < b := by
  fin_omega

@[simp]
/-
**Fin.sub_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sub_le_iff {n : Nat} {a b : Fin n} : a - b <= a ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Fin.not_le`：∀ {n : ℕ} {a b : Fin n}, ¬a ≤ b ↔ b < a
· 使用引理 `Fin.lt_sub_iff`：lt_sub_iff {n : Nat} {a b : Fin n} : a < a - b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sub_le_iff {n : ℕ} {a b : Fin n} : a - b ≤ a ↔ b ≤ a := by
  rw [← not_iff_not, Fin.not_le, Fin.not_le, lt_sub_iff]

@[simp]
/-
**Fin.lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_one_iff {n : Nat} (x : Fin (n + 2)) : x < 1 ↔ x = 0
参数：x : Fin (n + 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_one_iff {n : ℕ} (x : Fin (n + 2)) : x < 1 ↔ x = 0 := by
  simp [lt_def]
/-
**Fin.lt_sub_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0
参数：n + 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  simp
/-
**Fin.le_sub_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {k : Fin (n + 1)}, k ≤ k - 1 ↔ k = 0
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.fin_one_eq_zero`：∀ (a : Fin 1), a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Std.IsLinearPreorder.toIsPreorder`：∀ {α : Type u} {inst : LE α} [self : 
Std.IsLinearPreorder α], Std.IsPreorder α
· 使用定理 `Std.IsLinearOrder.toIsLinearPreorder`：∀ {α : Type u} [inst : LE α] [self
 : Std.IsLinearOrder α], Std.IsLinearPreorder α
· 使用定理 `Fin.instIsLinearOrder`：∀ {n : ℕ}, Std.IsLinearOrder (Fin n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.lt_sub_one_iff`：lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Fin.val_fin_lt`：val_fin_lt {n : Nat} {a b : Fin n} : (a : Nat) < (b : Na
t) ↔ a < b
· 使用定理 `Fin.val_inj`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b ↔ a = b
· 使用定理 `or_iff_left_iff_imp`：∀ {a b : Prop}, (a ∨ b ↔ a) ↔ b → a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
@[simp] lemma le_sub_one_iff {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  simp only [le_def]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, val_fin_lt, val_inj, lt_sub_one_iff, or_iff_left_iff_imp,
    eq_comm, sub_eq_iff_eq_add]
  simp
/-
**Fin.sub_one_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]
/-
**Fin.neg_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ), -Fin.last n = 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.last_add_one`：∀ (n : ℕ), Fin.last n + 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

open Fin.NatCast in
/-
**Fin.neg_natCast_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：neg_natCast_eq_one (n : Nat) : -(n : Fin (n + 1)) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.natCast_eq_last`：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last 
n
· 使用定理 `Fin.neg_last`：∀ (n : ℕ), -Fin.last n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_natCast_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp only [natCast_eq_last, neg_last]
/-
**Fin.rev_add** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_add (a b : Fin n) : rev (a + b) = rev a - b
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.last_sub`：last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
-/
lemma rev_add (a b : Fin n) : rev (a + b) = rev a - b := by
  cases n
  · exact a.elim0
  rw [← last_sub, ← last_sub, sub_add_eq_sub_sub]
/-
**Fin.rev_sub** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_sub (a b : Fin n) : rev (a - b) = rev a + b
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_eq_iff`：rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j
· 使用引理 `Fin.rev_add`：rev_add (a b : Fin n) : rev (a + b) = rev a - b
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
-/
lemma rev_sub (a b : Fin n) : rev (a - b) = rev a + b := by
  rw [rev_eq_iff, rev_add, rev_rev]
/-
**Fin.lt_add_one_of_succ_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_add_one_of_succ_lt {n : Nat} [NeZero n] {a : Fin n} (ha : a + 1 < n) : 
a < a + 1
参数：ha : a + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
· 使用定理 `Fin.coe_ofNat_eq_mod`：coe_ofNat_eq_mod (m n : Nat) [NeZero m] : ((ofNat(
n) : Fin m) : Nat) = ofNat(n) % m
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
lemma lt_add_one_of_succ_lt {n : ℕ} [NeZero n] {a : Fin n} (ha : a + 1 < n) : a < a + 1 := by
  rw [lt_def, val_add, coe_ofNat_eq_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt ha]
  lia
/-
**Fin.add_lt_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：add_lt_left_iff {n : Nat} {a b : Fin n} : a + b < a ↔ rev b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_lt_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev < j.rev ↔ j < i
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用引理 `Fin.rev_add`：rev_add (a b : Fin n) : rev (a + b) = rev a - b
· 使用引理 `Fin.lt_sub_iff`：lt_sub_iff {n : Nat} {a b : Fin n} : a < a - b ↔ a < b
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma add_lt_left_iff {n : ℕ} {a b : Fin n} : a + b < a ↔ rev b < a := by
  rw [← rev_lt_rev, Iff.comm, ← rev_lt_rev, rev_add, lt_sub_iff, rev_rev]

end Fin

