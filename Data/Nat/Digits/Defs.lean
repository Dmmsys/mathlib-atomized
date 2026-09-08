/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Defs
import all Init.Data.Repr  -- for exposing `toDigitsCore`

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

Also included is a bound on the length of `Nat.toDigits` from core.

## TODO

A basic `norm_digits` tactic for proving goals of the form `Nat.digits a b = l` where `a` and `b`
are numerals is not yet ported.
-/

@[expose] public section

assert_not_exists Finset

namespace Nat

variable {n : ℕ}

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
/-
**Nat.digitsAux0** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl.) An auxiliary definition for `digits`, to help get the desired definition
al unfolding.
-/
def digitsAux0 : ℕ → List ℕ
  | 0 => []
  | n + 1 => [n+1]

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
/-
**Nat.digitsAux1** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：digitsAux1 (n : Nat) : List Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl.) An auxiliary definition for `digits`, to help get the desired definition
al unfolding.
-/
def digitsAux1 (n : ℕ) : List ℕ :=
  List.replicate n 1

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
/-
**Nat.digitsAux** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：(b : ℕ) → 2 ≤ b → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl.) An auxiliary definition for `digits`, to help get the desired definition
al unfolding.
-/
@[semireducible] def digitsAux (b : ℕ) (h : 2 ≤ b) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    ((n + 1) % b) :: digitsAux b h ((n + 1) / b)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) h

@[simp]
/-
**Nat.digitsAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digitsAux_zero (b : Nat) (h : 2 <= b) : digitsAux b h 0 = []
参数：b : Nat；h : 2 <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digitsAux_zero (b : ℕ) (h : 2 ≤ b) : digitsAux b h 0 = [] := rfl
/-
**Nat.digitsAux_def** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digitsAux_def (b : Nat) (h : 2 <= b) (n : Nat) (w : 0 < n) : digitsAux b h
 n = (n % b) :: digitsAux b h (n / b)
参数：b : Nat；h : 2 <= b；n : Nat；w : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digitsAux.eq_2`：∀ (b : ℕ) (h : 2 ≤ b) (n : ℕ), b.digitsAux h n.succ 
= (n + 1) % b :: b.digitsAux h ((n + 1) / b)
-/
theorem digitsAux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) :
    digitsAux b h n = (n % b) :: digitsAux b h (n / b) := by
  cases n
  · cases w
  · rw [digitsAux]

/-- `digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `ofDigits b L = L.foldr (fun x y ↦ x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = List.replicate n 1`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `Nat.toDigits` in core, which is used for printing numerals.
In particular, `Nat.toDigits b 0 = ['0']`, while `digits b 0 = []`.
-/
/-
**Nat.digits** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `ofDigits b L = L.foldr (fun x y ↦ x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = List.replicate n 1`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `Nat.toDigits` in core, which is used for pr
inting numerals.
In particular, `Nat.toDigits b 0 = ['0']`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 => digitsAux (b + 2) (by simp)

@[simp]
/-
**Nat.digits_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_zero (b : Nat) : digits b 0 = []
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem digits_zero (b : ℕ) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digitsAux0, digitsAux1]
/-
**Nat.digits_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_zero_zero : digits 0 0 = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl

@[simp]
/-
**Nat.digits_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_zero_succ (n : Nat) : digits 0 n.succ = [n+1]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n+1] :=
  rfl
/-
**Nat.digits_zero_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → Nat.digits 0 n = [n]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_zero_succ' : ∀ {n : ℕ}, n ≠ 0 → digits 0 n = [n]
  | 0, h => (h rfl).elim
  | _ + 1, _ => rfl

@[simp]
/-
**Nat.digits_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_one (n : Nat) : digits 1 n = List.replicate n 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_one (n : ℕ) : digits 1 n = List.replicate n 1 :=
  rfl

-- no `@[simp]`: dsimp can prove this
/-
**Nat.digits_one_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_one_succ (n : Nat) : digits 1 (n + 1) = 1 :: digits 1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n :=
  rfl
/-
**Nat.digits_add_two_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_add_two_add_one (b n : Nat) : digits (b + 2) (n + 1) = ((n + 1) % (
b + 2)) :: digits (b + 2) ((n + 1) / (b + 2))
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digitsAux_def`：digitsAux_def (b : Nat) (h : 2 <= b) (n : Nat) (w : 0
 < n) : digitsAux b h n = (n % b) :: digitsAux b h (n / b)
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
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem digits_add_two_add_one (b n : ℕ) :
    digits (b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2)) := by
  simp [digits, digitsAux_def]

@[simp]
/-
**Nat.digits_of_two_le_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：digits_of_two_le_of_pos {b : Nat} (hb : 2 <= b) (hn : 0 < n) : Nat.digits 
b n = n % b :: Nat.digits b (n / b)
参数：hb : 2 <= b；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.eq_add_of_sub_eq`：∀ {a b c : ℕ}, b ≤ a → a - b = c → a = c + b
· 使用定理 `Nat.digits_add_two_add_one`：digits_add_two_add_one (b n : Nat) : digits 
(b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2))
-/
lemma digits_of_two_le_of_pos {b : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    Nat.digits b n = n % b :: Nat.digits b (n / b) := by
  rw [Nat.eq_add_of_sub_eq hb rfl, Nat.eq_add_of_sub_eq hn rfl, Nat.digits_add_two_add_one]
/-
**Nat.digits_def'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {b : ℕ}, 1 < b → ∀ {n : ℕ}, 0 < n → b.digits n = n % b :: b.digits (n / 
b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.digitsAux_def`：digitsAux_def (b : Nat) (h : 2 <= b) (n : Nat) (w : 0
 < n) : digitsAux b h n = (n % b) :: digitsAux b h (n / b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem digits_def' :
    ∀ {b : ℕ} (_ : 1 < b) {n : ℕ} (_ : 0 < n), digits b n = (n % b) :: digits b (n / b)
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | b + 2, _ => digitsAux_def _ (by simp) _

@[simp]
/-
**Nat.digits_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_of_lt (b x : Nat) (hx : x != 0) (hxb : x < b) : digits b x = [x]
参数：b x : Nat；hx : x != 0；hxb : x < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_add_two_add_one`：digits_add_two_add_one (b n : Nat) : digits 
(b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2))
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem digits_of_lt (b x : ℕ) (hx : x ≠ 0) (hxb : x < b) : digits b x = [x] := by
  rcases exists_eq_succ_of_ne_zero hx with ⟨x, rfl⟩
  rcases Nat.exists_eq_add_of_le' ((Nat.le_add_left 1 x).trans_lt hxb) with ⟨b, rfl⟩
  rw [digits_add_two_add_one, div_eq_of_lt hxb, digits_zero, mod_eq_of_lt hxb]
/-
**Nat.digits_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_add (b : Nat) (h : 1 < b) (x y : Nat) (hxb : x < b) (hxy : x != 0 ∨
 y != 0) : digits b (x + b * y) = x :: digits b y
参数：b : Nat；h : 1 < b；x y : Nat；hxb : x < b；hxy : x != 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.digits_of_lt`：digits_of_lt (b x : Nat) (hx : x != 0) (hxb : x < b) :
 digits b x = [x]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.digitsAux_def`：digitsAux_def (b : Nat) (h : 2 <= b) (n : Nat) (w : 0
 < n) : digitsAux b h n = (n % b) :: digitsAux b h (n / b)
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `Nat.add_mul_div_left`：∀ (x z : ℕ) {y : ℕ}, 0 < y → (x + y * z) / y = x /
 y + z
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
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 35 条，此处仅展示前 30 条）
-/
theorem digits_add (b : ℕ) (h : 1 < b) (x y : ℕ) (hxb : x < b) (hxy : x ≠ 0 ∨ y ≠ 0) :
    digits b (x + b * y) = x :: digits b y := by
  rcases Nat.exists_eq_add_of_le' h with ⟨b, rfl : _ = _ + 2⟩
  cases y
  · simp [hxb, hxy.resolve_right (absurd rfl)]
  dsimp [digits]
  rw [digitsAux_def]
  · congr
    · simp [Nat.add_mod, mod_eq_of_lt hxb]
    · simp [add_mul_div_left, div_eq_of_lt hxb]
  · apply Nat.succ_pos

-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
/-- `ofDigits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
/-
**Nat.ofDigits** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{α : Type u_1} → [Semiring α] → α → List ℕ → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofDigits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
def ofDigits {α : Type*} [Semiring α] (b : α) : List ℕ → α
  | [] => 0
  | h :: t => h + b * ofDigits b t
/-
**Nat.ofDigits_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α) (L : List Nat) : ofDigi
ts b L = List.foldr (fun x y => ↑x + b * y) 0 L
参数：b : α；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ofDigits_eq_foldr {α : Type*} [Semiring α] (b : α) (L : List ℕ) :
    ofDigits b L = List.foldr (fun x y => ↑x + b * y) 0 L := by
  induction L with
  | nil => rfl
  | cons d L ih => dsimp [ofDigits]; rw [ih]

@[simp]
/-
**Nat.ofDigits_nil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_nil {b : Nat} : ofDigits b [] = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDigits_nil {b : ℕ} : ofDigits b [] = 0 := rfl

@[simp]
/-
**Nat.ofDigits_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_singleton {b n : Nat} : ofDigits b [n] = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_singleton {b n : ℕ} : ofDigits b [n] = n := by simp [ofDigits]

@[simp]
/-
**Nat.ofDigits_one_cons** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_one_cons {α : Type*} [Semiring α] (h : Nat) (L : List Nat) : ofDi
gits (1 : α) (h :: L) = h + ofDigits 1 L
参数：h : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_one_cons {α : Type*} [Semiring α] (h : ℕ) (L : List ℕ) :
    ofDigits (1 : α) (h :: L) = h + ofDigits 1 L := by simp [ofDigits]
/-
**Nat.ofDigits_cons** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_cons {b hd} {tl : List Nat} : ofDigits b (hd :: tl) = hd + b * of
Digits b tl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDigits_cons {b hd} {tl : List ℕ} :
    ofDigits b (hd :: tl) = hd + b * ofDigits b tl := rfl
/-
**Nat.ofDigits_append** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDigits b (l1 ++ l2) = ofD
igits b l1 + b ^ l1.length * ofDigits b l2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.ofDigits.eq_2`：∀ {α : Type u_1} [inst : Semiring α] (b : α) (h : ℕ) 
(t : List ℕ), Nat.ofDigits b (h :: t) = ↑h + b * Nat.ofDigits b t
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 36 条，此处仅展示前 30 条）
-/
theorem ofDigits_append {b : ℕ} {l1 l2 : List ℕ} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 := by
  induction l1 with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits, List.cons_append, ofDigits, IH, List.length_cons, pow_succ']
    ring

@[simp]
/-
**Nat.ofDigits_append_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_append_zero {b : Nat} (l : List Nat) : ofDigits b (l ++ [0]) = of
Digits b l
参数：l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_append`：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDi
gits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2
· 使用定理 `Nat.ofDigits_singleton`：ofDigits_singleton {b n : Nat} : ofDigits b [n] 
= n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem ofDigits_append_zero {b : ℕ} (l : List ℕ) :
    ofDigits b (l ++ [0]) = ofDigits b l := by
  rw [ofDigits_append, ofDigits_singleton, mul_zero, add_zero]

@[simp]
/-
**Nat.ofDigits_replicate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_replicate_zero {b k : Nat} : ofDigits b (List.replicate k 0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_replicate_zero {b k : ℕ} : ofDigits b (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ofDigits_cons, ih]

@[simp]
/-
**Nat.ofDigits_append_replicate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_append_replicate_zero {b k : Nat} (l : List Nat) : ofDigits b (l 
++ List.replicate k 0) = ofDigits b l
参数：l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_append`：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDi
gits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.ofDigits_replicate_zero`：ofDigits_replicate_zero {b k : Nat} : ofDig
its b (List.replicate k 0) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_append_replicate_zero {b k : ℕ} (l : List ℕ) :
    ofDigits b (l ++ List.replicate k 0) = ofDigits b l := by
  rw [ofDigits_append]
  simp
/-
**Nat.ofDigits_reverse_cons** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_reverse_cons {b : Nat} (l : List Nat) (d : Nat) : ofDigits b (d :
: l).reverse = ofDigits b l.reverse + b ^ l.length * d
参数：l : List Nat；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `Nat.ofDigits_append`：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDi
gits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Nat.ofDigits_singleton`：ofDigits_singleton {b n : Nat} : ofDigits b [n] 
= n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_reverse_cons {b : ℕ} (l : List ℕ) (d : ℕ) :
    ofDigits b (d :: l).reverse = ofDigits b l.reverse + b ^ l.length * d := by
  simp only [List.reverse_cons]
  rw [ofDigits_append]
  simp
/-
**Nat.ofDigits_reverse_zero_cons** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_reverse_zero_cons {b : Nat} (l : List Nat) : ofDigits b (0 :: l).
reverse = ofDigits b l.reverse
参数：l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `Nat.ofDigits_append_zero`：ofDigits_append_zero {b : Nat} (l : List Nat) 
: ofDigits b (l ++ [0]) = ofDigits b l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_reverse_zero_cons {b : ℕ} (l : List ℕ) :
    ofDigits b (0 :: l).reverse = ofDigits b l.reverse := by
  simp only [List.reverse_cons, ofDigits_append_zero]

@[norm_cast]
/-
**Nat.coe_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coe_ofDigits (α : Type*) [Semiring α] (b : Nat) (L : List Nat) : ((ofDigit
s b L : Nat) : α) = ofDigits (b : α) L
参数：α : Type*；b : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem coe_ofDigits (α : Type*) [Semiring α] (b : ℕ) (L : List ℕ) :
    ((ofDigits b L : ℕ) : α) = ofDigits (b : α) L := by
  induction L with
  | nil => simp [ofDigits]
  | cons d L ih => dsimp [ofDigits]; push_cast; rw [ih]
/-
**Nat.digits_zero_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {b : ℕ}, b ≠ 0 → ∀ {L : List ℕ}, Nat.ofDigits b L = 0 → ∀ l ∈ L, l = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digits_zero_of_eq_zero {b : ℕ} (h : b ≠ 0) :
    ∀ {L : List ℕ} (_ : ofDigits b L = 0), ∀ l ∈ L, l = 0
  | _ :: _, h0, _, List.Mem.head .. => Nat.eq_zero_of_add_eq_zero_right h0
  | _ :: _, h0, _, List.Mem.tail _ hL =>
    digits_zero_of_eq_zero h (mul_right_injective₀ h (Nat.eq_zero_of_add_eq_zero_left h0)) _ hL
/-
**Nat.digits_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_ofDigits (b : Nat) (h : 1 < b) (L : List Nat) (w₁ : forall l in L, 
l < b) (w₂ : forall h : L != [], L.getLast h != 0) : digits b (ofDigits b L) = L
参数：b : Nat；h : 1 < b；L : List Nat；w₁ : forall l in L, l < b；w₂ : forall h : L !=
 [], L.getLast h != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.digits_add`：digits_add (b : Nat) (h : 1 < b) (x y : Nat) (hxb : x < 
b) (hxy : x != 0 ∨ y != 0) : digits b (x + b * y) = x :: digits b y
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Nat.digits_zero_of_eq_zero`：∀ {b : ℕ}, b ≠ 0 → ∀ {L : List ℕ}, Nat.ofDig
its b L = 0 → ∀ l ∈ L, l = 0
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem digits_ofDigits (b : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (w₂ : ∀ h : L ≠ [], L.getLast h ≠ 0) : digits b (ofDigits b L) = L := by
  induction L with
  | nil => simp
  | cons d L ih =>
    dsimp [ofDigits]
    replace w₂ := w₂ (by simp)
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_mem _ m
      · intro h
        rw [List.getLast_cons h] at w₂
        convert! w₂
    · exact w₁ d List.mem_cons_self
    · by_cases h' : L = []
      · rcases h' with rfl
        left
        simpa using w₂
      · right
        contrapose w₂
        refine digits_zero_of_eq_zero h.ne_bot w₂ _ ?_
        rw [List.getLast_cons h']
        exact List.getLast_mem h'
/-
**Nat.ofDigits_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_digits (b n : Nat) : ofDigits b (digits b n) = n
参数：b n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_singleton`：ofDigits_singleton {b n : Nat} : ofDigits b [n] 
= n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.ofDigits_one_cons`：ofDigits_one_cons {α : Type*} [Semiring α] (h : N
at) (L : List Nat) : ofDigits (1 : α) (h :: L) = h + ofDigits 1 L
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.digits_add_two_add_one`：digits_add_two_add_one (b n : Nat) : digits 
(b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2))
· 使用引理 `Nat.div_lt_self'`：div_lt_self' (a b : Nat) : (a + 1) / (b + 2) < a + 1
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
theorem ofDigits_digits (b n : ℕ) : ofDigits b (digits b n) = n := by
  rcases b with - | b
  · rcases n with - | n
    · rfl
    · simp
  · rcases b with - | b
    · induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.zero_add] at ih ⊢
        simp only [ih, add_comm 1, ofDigits_one_cons, Nat.cast_id, digits_one_succ]
    · induction n using Nat.strongRecOn with | ind n h => ?_
      cases n
      · rw [digits_zero]
        rfl
      · simp only [digits_add_two_add_one]
        dsimp [ofDigits]
        rw [h _ (Nat.div_lt_self' _ b)]
        rw [Nat.mod_add_div]
/-
**Nat.ofDigits_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum
参数：L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDigits_one (L : List ℕ) : ofDigits 1 L = L.sum := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ofDigits, List.sum_cons, ih]

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/


/-
**Nat.digits_eq_nil_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_eq_nil_iff_eq_zero {b n : Nat} : digits b n = [] ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Properties

This section contains various lemmas of properties relating to `digits` and `ofD
igits`.
-/
theorem digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 := by
  constructor
  · intro h
    have : ofDigits b (digits b n) = ofDigits b [] := by rw [h]
    convert! this
    rw [ofDigits_digits]
  · rintro rfl
    simp
/-
**Nat.digits_ne_nil_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_ne_nil_iff_ne_zero {b n : Nat} : digits b n != [] ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.digits_eq_nil_iff_eq_zero`：digits_eq_nil_iff_eq_zero {b n : Nat} : d
igits b n = [] ↔ n = 0
-/
theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero
/-
**Nat.digits_eq_cons_digits_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_eq_cons_digits_div {b n : Nat} (h : 1 < b) (w : n != 0) : digits b 
n = (n % b) :: digits b (n / b)
参数：h : 1 < b；w : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.digits_def'`：∀ {b : ℕ}, 1 < b → ∀ {n : ℕ}, 0 < n → b.digits n = n % 
b :: b.digits (n / b)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem digits_eq_cons_digits_div {b n : ℕ} (h : 1 < b) (w : n ≠ 0) :
    digits b n = (n % b) :: digits b (n / b) :=
  digits_def' h (Nat.pos_of_ne_zero w)
/-
**Nat.digits_getLast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_getLast {b : Nat} (m : Nat) (h : 1 < b) (p q) : (digits b m).getLas
t p = (digits b (m / b)).getLast q
参数：m : Nat；h : 1 < b；p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.digits_eq_cons_digits_div`：digits_eq_cons_digits_div {b n : Nat} (h 
: 1 < b) (w : n != 0) : digits b n = (n % b) :: digits b (n / b)
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
-/
theorem digits_getLast {b : ℕ} (m : ℕ) (h : 1 < b) (p q) :
    (digits b m).getLast p = (digits b (m / b)).getLast q := by
  by_cases hm : m = 0
  · simp [hm]
  simp only [digits_eq_cons_digits_div h hm]
  rw [List.getLast_cons]
/-
**Nat.digits.injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat.digits`。
形式化陈述：∀ (b : ℕ), Function.Injective b.digits
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
-/
theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (ofDigits_digits b)

@[simp]
/-
**Nat.digits_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_inj_iff {b n m : Nat} : b.digits n = b.digits m ↔ n = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.digits.injective`：∀ (b : ℕ), Function.Injective b.digits
-/
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff
/-
**Nat.mul_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mul_ofDigits (n : Nat) {b : Nat} {l : List Nat} : n * ofDigits b l = ofDig
its b (l.map (n * ·))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.ofDigits_cons`：ofDigits_cons {b hd} {tl : List Nat} : ofDigits b (hd
 :: tl) = hd + b * ofDigits b tl
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
theorem mul_ofDigits (n : ℕ) {b : ℕ} {l : List ℕ} :
    n * ofDigits b l = ofDigits b (l.map (n * ·)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, ofDigits_cons, ofDigits_cons, ← ih]
    ring
/-
**Nat.ofDigits_inj_of_len_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ofDigits_inj_of_len_eq {b : Nat} (hb : 1 < b) {L1 L2 : List Nat} (len : L1
.length = L2.length) (w1 : forall l in L1, l < b) (w2 : forall l in L2, l < b) (
h : ofDigits b L1 = ofDigits b L2) : L1 = L2
参数：hb : 1 < b；len : L1.length = L2.length；w1 : forall l in L1, l < b；w2 : forall
 l in L2, l < b；h : ofDigits b L1 = ofDigits b L2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `List.exists_cons_of_length_eq_add_one`：∀ {α : Type u_1} {n : ℕ} {l : Lis
t α}, l.length = n + 1 → ∃ h t, l = h :: t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
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
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `mul_left_cancel_iff_of_pos`：mul_left_cancel_iff_of_pos [PosMulReflectLE 
α] (a0 : 0 < a) : a * b = a * c ↔ b = c
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
-/
lemma ofDigits_inj_of_len_eq {b : ℕ} (hb : 1 < b) {L1 L2 : List ℕ}
    (len : L1.length = L2.length) (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b)
    (h : ofDigits b L1 = ofDigits b L2) : L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    simp only [List.length_nil] at len
    exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons D L ih => ?_
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [ofDigits_cons] at h
  have eqd : D = d := by
    have H : (D + b * ofDigits b L) % b = (d + b * ofDigits b l) % b := by rw [h]
    simpa [mod_eq_of_lt (w2 d List.mem_cons_self),
      mod_eq_of_lt (w1 D List.mem_cons_self)] using H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos (zero_lt_of_lt hb)] at h
  have := ih len (fun a ha ↦ w1 a <| List.mem_cons_of_mem D ha)
    (fun a ha ↦ w2 a <| List.mem_cons_of_mem d ha) h
  rw [eqd, this]

/-- The addition of ofDigits of two lists is equal to ofDigits of digit-wise addition of them -/
/-
**Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Nat`。
形式化陈述：ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq {b : Nat} {l1 l2 : 
List Nat} (h : l1.length = l2.length) : ofDigits b l1 + ofDigits b l2 = ofDigits
 b (l1.zipWith (· + ·) l2)
参数：h : l1.length = l2.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `List.zipWith_self`：∀ {α : Type u_1} {δ : Type u_2} {f : α → α → δ} {l : 
List α}, List.zipWith f l l = List.map (fun a => f a a) l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `Nat.instAssociativeHMul`：Std.Associative fun x1 x2 => x1 * x2
· 使用定理 `Nat.instCommutativeHMul`：Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `Nat.instAssociativeHAdd`：Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `Nat.instCommutativeHAdd`：Std.Commutative fun x1 x2 => x1 + x2

--- 原说明 ---
The addition of ofDigits of two lists is equal to ofDigits of digit-wise additio
n of them
-/
theorem ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq {b : ℕ} {l1 l2 : List ℕ}
    (h : l1.length = l2.length) :
    ofDigits b l1 + ofDigits b l2 = ofDigits b (l1.zipWith (· + ·) l2) := by
  induction l1 generalizing l2 with
  | nil => simp_all [eq_comm, List.length_eq_zero_iff, ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [List.length_cons, ofDigits_cons, add_left_inj,
        eq_comm, List.zipWith_cons_cons]
      rw [← ih₁ h.symm, mul_add]
      ac_rfl

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
/-
**Nat.digits_lt_base'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_lt_base' {b m : Nat} : forall {d}, d in digits (b + 2) m -> d < b +
 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.digits_add_two_add_one`：digits_add_two_add_one (b n : Nat) : digits 
(b + 2) (n + 1) = ((n + 1) % (b + 2)) :: digits (b + 2) ((n + 1) / (b + 2))
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The digits in the base b+2 expansion of n are all less than b+2
-/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b + 2) m → d < b + 2 := by
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro d hd
  rcases n with - | n
  · rw [digits_zero] at hd
    cases hd
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · exact n.succ.mod_lt (by linarith)
  · apply IH ((n + 1) / (b + 2))
    · apply Nat.div_lt_self <;> lia
    · assumption

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
/-
**Nat.digits_lt_base** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in digits b m) : d < b
参数：hb : 1 < b；hd : d in digits b m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.digits_lt_base'`：digits_lt_base' {b m : Nat} : forall {d}, d in digi
ts (b + 2) m -> d < b + 2

--- 原说明 ---
The digits in the base b expansion of n are all less than b, if b ≥ 2
-/
theorem digits_lt_base {b m d : ℕ} (hb : 1 < b) (hd : d ∈ digits b m) : d < b := by
  rcases b with (_ | _ | b) <;> simp_all [@digits_lt_base' _ m d]

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
/-
**Nat.ofDigits_lt_base_pow_length'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_lt_base_pow_length' {b : Nat} {l : List Nat} (hl : forall x in l,
 x < b + 2) : ofDigits (b + 2) l < (b + 2) ^ l.length
参数：hl : forall x in l, x < b + 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.ofDigits.eq_2`：∀ {α : Type u_1} [inst : Semiring α] (b : α) (h : ℕ) 
(t : List ℕ), Nat.ofDigits b (h :: t) = ↑h + b * Nat.ofDigits b t
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
an n-digit number in base b + 2 is less than (b + 2)^n
-/
theorem ofDigits_lt_base_pow_length' {b : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length := by
  induction l with
  | nil => simp [ofDigits]
  | cons hd tl IH =>
    rw [ofDigits, List.length_cons, pow_succ]
    have : (ofDigits (b + 2) tl + 1) * (b + 2) ≤ (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_mem _ hx)) (by rfl) (by simp only [zero_le])
        (Nat.zero_le _)
    suffices ↑hd < b + 2 by linarith
    exact hl hd List.mem_cons_self

/-- an n-digit number in base b is less than b^n if b > 1 -/
/-
**Nat.ofDigits_lt_base_pow_length** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_lt_base_pow_length {b : Nat} {l : List Nat} (hb : 1 < b) (hl : fo
rall x in l, x < b) : ofDigits b l < b ^ l.length
参数：hb : 1 < b；hl : forall x in l, x < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
an n-digit number in base b is less than b^n if b > 1
-/
theorem ofDigits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 1 < b) (hl : ∀ x ∈ l, x < b) :
    ofDigits b l < b ^ l.length := by
  rcases b with (_ | _ | b) <;> simp_all [ofDigits_lt_base_pow_length']

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
/-
**Nat.lt_base_pow_length_digits'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_base_pow_length_digits' {b m : Nat} : m < (b + 2) ^ (digits (b + 2) m).
length
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.ofDigits_lt_base_pow_length'`：ofDigits_lt_base_pow_length' {b : Nat}
 {l : List Nat} (hl : forall x in l, x < b + 2) : ofDigits (b + 2) l < (b + 2) ^
 l.length
· 使用定理 `Nat.digits_lt_base'`：digits_lt_base' {b m : Nat} : forall {d}, d in digi
ts (b + 2) m -> d < b + 2

--- 原说明 ---
Any number m is less than (b+2)^(number of digits in the base b + 2 representati
on of m)
-/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length := by
  convert! @ofDigits_lt_base_pow_length' b (digits (b + 2) m) fun _ => digits_lt_base'
  rw [ofDigits_digits (b + 2) m]

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
/-
**Nat.lt_base_pow_length_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_base_pow_length_digits {b m : Nat} (hb : 1 < b) : m < b ^ (digits b m).
length
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Any number m is less than b^(number of digits in the base b representation of m)
-/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 1 < b) : m < b ^ (digits b m).length := by
  rcases b with (_ | _ | b) <;> simp_all [lt_base_pow_length_digits']
/-
**Nat.digits_base_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_base_mul {b m : Nat} (hb : 1 < b) (hm : 0 < m) : b.digits (b * m) =
 0 :: b.digits m
参数：hb : 1 < b；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_def'`：∀ {b : ℕ}, 1 < b → ∀ {n : ℕ}, 0 < n → b.digits n = n % 
b :: b.digits (n / b)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `Nat.mul_div_right`：∀ (n : ℕ) {m : ℕ}, 0 < m → m * n / m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem digits_base_mul {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    b.digits (b * m) = 0 :: b.digits m := by
  rw [digits_def' hb (by positivity)]
  simp [mul_div_right m (by positivity)]
/-
**Nat.digits_base_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digits_base_pow_mul {b k m : Nat} (hb : 1 < b) (hm : 0 < m) : digits b (b 
^ k * m) = List.replicate k 0 ++ digits b m
参数：hb : 1 < b；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.digits_base_mul`：digits_base_mul {b m : Nat} (hb : 1 < b) (hm : 0 < 
m) : b.digits (b * m) = 0 :: b.digits m
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `List.replicate_succ`：∀ {α : Type u} {a : α} {n : ℕ}, List.replicate (n +
 1) a = a :: List.replicate n a
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
-/
theorem digits_base_pow_mul {b k m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    digits b (b ^ k * m) = List.replicate k 0 ++ digits b m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, digits_base_mul hb (by positivity), ih hm, List.replicate_succ,
      List.cons_append]
/-
**Nat.ofDigits_digits_append_digits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_digits_append_digits {b m n : Nat} : ofDigits b (digits b n ++ di
gits b m) = n + b ^ (digits b n).length * m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_append`：ofDigits_append {b : Nat} {l1 l2 : List Nat} : ofDi
gits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
-/
theorem ofDigits_digits_append_digits {b m n : ℕ} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [ofDigits_append, ofDigits_digits, ofDigits_digits]

@[gcongr, mono]
/-
**Nat.ofDigits_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofDigits_monotone {p q : Nat} (L : List Nat) (h : p <= q) : ofDigits p L <
= ofDigits q L
参数：L : List Nat；h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
-/
theorem ofDigits_monotone {p q : ℕ} (L : List ℕ) (h : p ≤ q) : ofDigits p L ≤ ofDigits q L := by
  induction L with
  | nil => rfl
  | cons _ _ hi =>
    simp only [ofDigits, cast_id, add_le_add_iff_left]
    exact Nat.mul_le_mul h hi
/-
**Nat.sum_le_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_le_ofDigits {p : Nat} (L : List Nat) (h : 1 <= p) : L.sum <= ofDigits 
p L
参数：L : List Nat；h : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofDigits_monotone`：ofDigits_monotone {p q : Nat} (L : List Nat) (h :
 p <= q) : ofDigits p L <= ofDigits q L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_one`：ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum
-/
theorem sum_le_ofDigits {p : ℕ} (L : List ℕ) (h : 1 ≤ p) : L.sum ≤ ofDigits p L :=
  (ofDigits_one L).symm ▸ ofDigits_monotone L h
/-
**Nat.digit_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：digit_sum_le (p n : Nat) : List.sum (digits p n) <= n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.digits_zero`：digits_zero (b : Nat) : digits b 0 = []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.digits_zero_succ`：digits_zero_succ (n : Nat) : digits 0 n.succ = [n+
1]
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `List.sum_nil`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α], [].sum = 
0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.ofDigits_one`：ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum
· 使用定理 `Nat.ofDigits_monotone`：ofDigits_monotone {p q : Nat} (L : List Nat) (h :
 p <= q) : ofDigits p L <= ofDigits q L
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem digit_sum_le (p n : ℕ) : List.sum (digits p n) ≤ n := by
  induction n with
  | zero => exact digits_zero _ ▸ Nat.le_refl (List.sum [])
  | succ n =>
    induction p with
    | zero => rw [digits_zero_succ, List.sum_cons, List.sum_nil, add_zero]
    | succ p =>
      nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one <| digits p.succ n.succ]
      exact ofDigits_monotone (digits p.succ n.succ) <| Nat.succ_pos p

/-- Interpreting as a base `p` number and dividing by `p` is the same as interpreting the tail.
-/
/-
**Nat.ofDigits_div_eq_ofDigits_tail** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ofDigits_div_eq_ofDigits_tail {p : Nat} (hpos : 0 < p) (digits : List Nat)
 (w₁ : forall l in digits, l < p) : ofDigits p digits / p = ofDigits p digits.ta
il
参数：hpos : 0 < p；digits : List Nat；w₁ : forall l in digits, l < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_mul_div_left`：∀ (x z : ℕ) {y : ℕ}, 0 < y → (x + y * z) / y = x /
 y + z
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.tail_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).tail = a
s

--- 原说明 ---
Interpreting as a base `p` number and dividing by `p` is the same as interpretin
g the tail.
-/
lemma ofDigits_div_eq_ofDigits_tail {p : ℕ} (hpos : 0 < p) (digits : List ℕ)
    (w₁ : ∀ l ∈ digits, l < p) : ofDigits p digits / p = ofDigits p digits.tail := by
  induction digits with
  | nil => simp [ofDigits]
  | cons hd tl =>
    refine Eq.trans (add_mul_div_left hd _ hpos) ?_
    rw [Nat.div_eq_of_lt <| w₁ _ List.mem_cons_self, zero_add, List.tail_cons]

/-- Interpreting as a base `p` number and dividing by `p^i` is the same as dropping `i`.
-/
/-
**Nat.ofDigits_div_pow_eq_ofDigits_drop** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ofDigits_div_pow_eq_ofDigits_drop {p : Nat} (i : Nat) (hpos : 0 < p) (digi
ts : List Nat) (w₁ : forall l in digits, l < p) : ofDigits p digits / p ^ i = of
Digits p (digits.drop i)
参数：i : Nat；hpos : 0 < p；digits : List Nat；w₁ : forall l in digits, l < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用引理 `Nat.ofDigits_div_eq_ofDigits_tail`：ofDigits_div_eq_ofDigits_tail {p : Na
t} (hpos : 0 < p) (digits : List Nat) (w₁ : forall l in digits, l < p) : ofDigit
s p digits / p = ofDigi…
· 使用定理 `List.mem_of_mem_drop`：∀ {α : Type u_1} {a : α} {i : ℕ} {l : List α}, a ∈
 List.drop i l → a ∈ l
· 使用定理 `List.drop_one`：∀ {α : Type u_1} {l : List α}, List.drop 1 l = l.tail
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Interpreting as a base `p` number and dividing by `p^i` is the same as dropping 
`i`.
-/
lemma ofDigits_div_pow_eq_ofDigits_drop
    {p : ℕ} (i : ℕ) (hpos : 0 < p) (digits : List ℕ) (w₁ : ∀ l ∈ digits, l < p) :
    ofDigits p digits / p ^ i = ofDigits p (digits.drop i) := by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hi, ofDigits_div_eq_ofDigits_tail hpos
      (List.drop i digits) fun x hx ↦ w₁ x <| List.mem_of_mem_drop hx, ← List.drop_one,
      List.drop_drop, add_comm]

/-- Dividing `n` by `p^i` is like truncating the first `i` digits of `n` in base `p`.
-/
/-
**Nat.self_div_pow_eq_ofDigits_drop** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：self_div_pow_eq_ofDigits_drop {p : Nat} (i n : Nat) (h : 2 <= p) : n / p ^
 i = ofDigits p ((p.digits n).drop i)
参数：i n : Nat；h : 2 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用引理 `Nat.ofDigits_div_pow_eq_ofDigits_drop`：ofDigits_div_pow_eq_ofDigits_drop
 {p : Nat} (i : Nat) (hpos : 0 < p) (digits : List Nat) (w₁ : forall l in digits
, l < p) : ofDigits p digit…
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b

--- 原说明 ---
Dividing `n` by `p^i` is like truncating the first `i` digits of `n` in base `p`
.
-/
lemma self_div_pow_eq_ofDigits_drop {p : ℕ} (i n : ℕ) (h : 2 ≤ p) :
    n / p ^ i = ofDigits p ((p.digits n).drop i) := by
  convert!
    ofDigits_div_pow_eq_ofDigits_drop i (zero_lt_of_lt h) (p.digits n)
      (fun l hl ↦ digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

/-- Interpreting as a base `p` number and modulo `p^i` is the same as taking the first `i` digits.
-/
/-
**Nat.ofDigits_mod_pow_eq_ofDigits_take** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ofDigits_mod_pow_eq_ofDigits_take {p : Nat} (i : Nat) (hpos : 0 < p) (digi
ts : List Nat) (w₁ : forall l in digits, l < p) : ofDigits p digits % p ^ i = of
Digits p (digits.take i)
参数：i : Nat；hpos : 0 < p；digits : List Nat；w₁ : forall l in digits, l < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.mod_one`：∀ (x : ℕ), x % 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_succ_cons`：∀ {α : Type u} {a : α} {as : List α} {i : ℕ}, List.
take (i + 1) (a :: as) = a :: List.take i as
· 使用定理 `Nat.ofDigits_cons`：ofDigits_cons {b hd} {tl : List Nat} : ofDigits b (hd
 :: tl) = hd + b * ofDigits b tl
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Nat.le_pow`：∀ {a b : ℕ}, 0 < b → a ≤ a ^ b
· 使用定理 `Nat.add_one_pos`：∀ (n : ℕ), 0 < n + 1
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.mul_mod_mul_left`：∀ (z x y : ℕ), z * x % (z * y) = z * (x % y)
· 使用定理 `Nat.add_lt_of_lt_sub`：∀ {a b c : ℕ}, a < c - b → a + b < c
· 使用定理 `Nat.mul_sub`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α

--- 原说明 ---
Interpreting as a base `p` number and modulo `p^i` is the same as taking the fir
st `i` digits.
-/
lemma ofDigits_mod_pow_eq_ofDigits_take
    {p : ℕ} (i : ℕ) (hpos : 0 < p) (digits : List ℕ) (w₁ : ∀ l ∈ digits, l < p) :
    ofDigits p digits % p ^ i = ofDigits p (digits.take i) := by
  induction i generalizing digits with
  | zero => simp [mod_one]
  | succ i ih =>
    cases digits with
    | nil => simp
    | cons hd tl =>
      rw [List.take_succ_cons, ofDigits_cons, ofDigits_cons,
        ← ih _ fun x hx ↦ w₁ x <| List.mem_cons_of_mem hd hx, add_mod,
        mod_eq_of_lt <| lt_of_lt_of_le (w₁ hd List.mem_cons_self) (le_pow <| add_one_pos i),
        pow_succ', mul_mod_mul_left, mod_eq_of_lt]
      apply add_lt_of_lt_sub
      apply lt_of_lt_of_le (b := p)
      · exact w₁ hd List.mem_cons_self
      · rw [← Nat.mul_sub]
        exact Nat.le_mul_of_pos_right _ <| Nat.sub_pos_of_lt <| mod_lt _ <| pow_pos hpos i

/-- `n` modulo `p^i` is like taking the least significant `i` digits of `n` in base `p`.
-/
/-
**Nat.self_mod_pow_eq_ofDigits_take** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：self_mod_pow_eq_ofDigits_take {p : Nat} (i n : Nat) (h : 2 <= p) : n % p ^
 i = ofDigits p ((p.digits n).take i)
参数：i n : Nat；h : 2 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用引理 `Nat.ofDigits_mod_pow_eq_ofDigits_take`：ofDigits_mod_pow_eq_ofDigits_take
 {p : Nat} (i : Nat) (hpos : 0 < p) (digits : List Nat) (w₁ : forall l in digits
, l < p) : ofDigits p digit…
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b

--- 原说明 ---
`n` modulo `p^i` is like taking the least significant `i` digits of `n` in base 
`p`.
-/
lemma self_mod_pow_eq_ofDigits_take {p : ℕ} (i n : ℕ) (h : 2 ≤ p) :
    n % p ^ i = ofDigits p ((p.digits n).take i) := by
  convert!
    ofDigits_mod_pow_eq_ofDigits_take i (zero_lt_of_lt h) (p.digits n)
      (fun l hl ↦ digits_lt_base h hl)
  exact (ofDigits_digits p n).symm

/-! ### `Nat.toDigits` length -/

/-
**Nat.toDigitsCore_lens_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toDigitsCore_lens_eq_aux (b f : Nat) : forall (n : Nat) (l1 l2 : List Char
), l1.length = l2.length -> (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCo
re b f n l2).length
参数：b f : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `trivial`：True

--- 原说明 ---
### `Nat.toDigits` length
-/
lemma toDigitsCore_lens_eq_aux (b f : Nat) :
    ∀ (n : Nat) (l1 l2 : List Char), l1.length = l2.length →
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with (simp only [Nat.toDigitsCore]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    if hx : n / b = 0 then
      simp only [hx, if_true, List.length, congrArg (fun l ↦ l + 1) hlen]
    else
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l ↦ l + 1) hlen] at ih
      exact ih trivial
/-
**Nat.toDigitsCore_lens_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toDigitsCore_lens_eq (b f : Nat) : forall (n : Nat) (c : Char) (tl : List 
Char), (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).l
ength + 1
参数：b f : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toDigitsCore_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
  | succ f ih =>
    grind
/-
**Nat.nat_repr_len_aux** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) : n < b ^ e.succ -> n / b
 < b ^ e
参数：n b e : Nat；h_b_pos : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
-/
lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) : n < b ^ e.succ → n / b < b ^ e := by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

/-- The String representation produced by toDigitsCore has the proper length relative to
the number of digits in `n < e` for some base `b`. Since this works with any base,
it can be used for binary, decimal, and hex. -/
/-
**Nat.toDigitsCore_length** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toDigitsCore_length (b f n e : Nat) (h_e_pos : 0 < e) (hlt : n < b ^ e) : 
(Nat.toDigitsCore b f n []).length <= e
参数：b f n e : Nat；h_e_pos : 0 < e；hlt : n < b ^ e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.lt_irrefl`：∀ (n : ℕ), ¬n < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Nat.toDigitsCore_lens_eq`：toDigitsCore_lens_eq (b f : Nat) : forall (n :
 Nat) (c : Char) (tl : List Char), (Nat.toDigitsCore b f n (c :: tl)).length = (
Nat.toDigitsCo…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.add_one_pos`：∀ (n : ℕ), 0 < n + 1
· 使用定理 `Nat.div_lt_of_lt_mul`：∀ {m n k : ℕ}, m < n * k → m / n < k
· 使用定理 `Nat.pow_add_one'`：∀ {m n : ℕ}, m ^ (n + 1) = m * m ^ n

--- 原说明 ---
The String representation produced by toDigitsCore has the proper length relativ
e to
the number of digits in `n < e` for some base `b`. Since this works with any bas
e,
it can be used for binary, decimal, and hex.
-/
lemma toDigitsCore_length (b f n e : Nat) (h_e_pos : 0 < e) (hlt : n < b ^ e) :
    (Nat.toDigitsCore b f n []).length ≤ e := by
  induction f generalizing n e hlt h_e_pos with
  | zero => simp only [toDigitsCore, List.length, zero_le]
  | succ f ih =>
    simp only [toDigitsCore]
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      cases e with
      | zero =>
        rw [zero_add, pow_one] at hlt
        simp [Nat.div_eq_of_lt hlt]
      | succ e =>
        specialize ih (n / b) _ (add_one_pos e) (Nat.div_lt_of_lt_mul <| by rwa [← pow_add_one'])
        split_ifs
        · simp
        · simp only [toDigitsCore_lens_eq b f (n / b) (Nat.digitChar <| n % b),
            Nat.succ_le_succ_iff, ih]

/-- The core implementation of `Nat.toDigits` returns a String with length less than or equal to the
number of digits in the base-`b` number (represented by `e`). For example, the string
representation of any number less than `b ^ 3` has a length less than or equal to 3. -/
/-
**Nat.toDigits_length** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toDigits_length (b n e : Nat) : 0 < e -> n < b ^ e -> (Nat.toDigits b n).l
ength <= e
参数：b n e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.toDigitsCore_length`：toDigitsCore_length (b f n e : Nat) (h_e_pos : 
0 < e) (hlt : n < b ^ e) : (Nat.toDigitsCore b f n []).length <= e

--- 原说明 ---
The core implementation of `Nat.toDigits` returns a String with length less than
 or equal to the
number of digits in the base-`b` number (represented by `e`). For example, the s
tring
representation of any number less than `b ^ 3` has a length less than or equal t
o 3.
-/
lemma toDigits_length (b n e : Nat) : 0 < e → n < b ^ e → (Nat.toDigits b n).length ≤ e :=
  toDigitsCore_length _ _ _ _

/-- The core implementation of `Nat.repr` returns a String with length less than or equal to the
number of digits in the decimal number (represented by `e`). For example, the decimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or equal to 3. -/
/-
**Nat.repr_length** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：repr_length (n e : Nat) : 0 < e -> n < 10 ^ e -> (Nat.repr n).length <= e
参数：n e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.length_ofList`：∀ {l : List Char}, (String.ofList l).length = l.le
ngth
· 使用引理 `Nat.toDigits_length`：toDigits_length (b n e : Nat) : 0 < e -> n < b ^ e 
-> (Nat.toDigits b n).length <= e

--- 原说明 ---
The core implementation of `Nat.repr` returns a String with length less than or 
equal to the
number of digits in the decimal number (represented by `e`). For example, the de
cimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or e
qual to 3.
-/
lemma repr_length (n e : Nat) : 0 < e → n < 10 ^ e → (Nat.repr n).length ≤ e := by
  simpa [Nat.repr] using toDigits_length _ _ _

end Nat

