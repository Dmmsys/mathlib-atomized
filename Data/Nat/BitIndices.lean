/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.List.Sort

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `List` of indices of `1`s in the
binary expansion of `n`. If `s : Finset ℕ` and `n = ∑ i ∈ s, 2 ^ i`, then
`Nat.bitIndices n` is the sorted list of elements of `s`.

The lemma `sum_map_two_pow_bitIndices` proves that summing `2 ^ i` over this list gives `n`.
This is used in `Combinatorics.colex` to construct a bijection `equivBitIndices : ℕ ≃ Finset ℕ`.

## TODO

Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

@[expose] public section

open List
namespace Nat

variable {a n : ℕ}

/-- The function which maps each natural number `∑ i ∈ s, 2 ^ i` to the list of
elements of `s` in increasing order. -/
/-
**Nat.bitIndices** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：bitIndices (n : Nat) : List Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function which maps each natural number `∑ i ∈ s, 2 ^ i` to the list of
elements of `s` in increasing order.
-/
def bitIndices (n : ℕ) : List ℕ :=
  @binaryRec (fun _ ↦ List ℕ) [] (fun b _ s ↦ b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n
/-
**Nat.bitIndices_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.bitIndices 0 = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem bitIndices_zero : bitIndices 0 = [] := by simp [bitIndices]
/-
**Nat.bitIndices_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.bitIndices 1 = [0]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem bitIndices_one : bitIndices 1 = [0] := by simp [bitIndices]
/-
**Nat.bitIndices_bit_true** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitIndices_bit_true (n : Nat) : bitIndices (bit true n) = 0 :: ((bitIndice
s n).map (· + 1))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
-/
theorem bitIndices_bit_true (n : ℕ) :
    bitIndices (bit true n) = 0 :: ((bitIndices n).map (· + 1)) :=
  binaryRec_eq _ _ (.inl rfl)
/-
**Nat.bitIndices_bit_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitIndices_bit_false (n : Nat) : bitIndices (bit false n) = (bitIndices n)
.map (· + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
-/
theorem bitIndices_bit_false (n : ℕ) :
    bitIndices (bit false n) = (bitIndices n).map (· + 1) :=
  binaryRec_eq _ _ (.inl rfl)
/-
**Nat.bitIndices_two_mul_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n + 1).bitIndices = 0 :: List.map (fun x => x + 1) n.bitIn
dices
参数：n : ℕ；2 * n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bitIndices_bit_true`：bitIndices_bit_true (n : Nat) : bitIndices (bit
 true n) = 0 :: ((bitIndices n).map (· + 1))
· 使用定理 `Nat.bit_true`：bit_true : bit true = (2 * · + 1)
-/
@[simp] theorem bitIndices_two_mul_add_one (n : ℕ) :
    bitIndices (2 * n + 1) = 0 :: (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_true, bit_true]
/-
**Nat.bitIndices_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n).bitIndices = List.map (fun x => x + 1) n.bitIndices
参数：n : ℕ；2 * n；fun x => x + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bitIndices_bit_false`：bitIndices_bit_false (n : Nat) : bitIndices (b
it false n) = (bitIndices n).map (· + 1)
· 使用定理 `Nat.bit_false`：bit_false : bit false = (2 * ·)
-/
@[simp] theorem bitIndices_two_mul (n : ℕ) :
    bitIndices (2 * n) = (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_false, bit_false]
/-
**Nat.bitIndices_sorted** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.bitIndices.SortedLT
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bitIndices_zero`：Nat.bitIndices 0 = []
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `Nat.bitIndices_two_mul`：∀ (n : ℕ), (2 * n).bitIndices = List.map (fun x 
=> x + 1) n.bitIndices
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bitIndices_two_mul_add_one`：∀ (n : ℕ), (2 * n + 1).bitIndices = 0 ::
 List.map (fun x => x + 1) n.bitIndices
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] theorem bitIndices_sorted {n : ℕ} : n.bitIndices.SortedLT := by
  induction n using binaryRec with
  | zero => simp [sortedLT_iff_pairwise]
  | bit b n hs =>
    suffices List.Pairwise (fun a b ↦ a < b) n.bitIndices by
      cases b <;> simpa [sortedLT_iff_pairwise, bit_false, bit_true, List.pairwise_map]
    exact List.Pairwise.imp (by simp) hs.pairwise
/-
**Nat.bitIndices_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.bitIndices.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.nodup`：∀ {α : Type u} {l : List α} {r : α → α → Prop} [Std
.Irrefl r], List.Pairwise r l → l.Nodup
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `Nat.bitIndices_sorted`：∀ {n : ℕ}, n.bitIndices.SortedLT
-/
@[simp] theorem bitIndices_nodup {n : ℕ} : n.bitIndices.Nodup := bitIndices_sorted.pairwise.nodup
/-
**Nat.bitIndices_two_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (k n : ℕ), (2 ^ k * n).bitIndices = List.map (fun x => x + k) n.bitIndic
es
参数：k n : ℕ；2 ^ k * n；fun x => x + k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.bitIndices_two_mul`：∀ (n : ℕ), (2 * n).bitIndices = List.map (fun x 
=> x + 1) n.bitIndices
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `comp_add_right`：∀ {α : Type u_1} [inst : AddSemigroup α] (x y : α), ((fu
n x_1 => x_1 + x) ∘ fun x => x + y) = fun x_1 => x_1 + (y + x)
-/
@[simp] theorem bitIndices_two_pow_mul (k n : ℕ) :
    bitIndices (2 ^ k * n) = (bitIndices n).map (· + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm, pow_add, pow_one, mul_assoc, bitIndices_two_mul, ih, List.map_map, comp_add_right]
    simp [add_comm (a := 1)]
/-
**Nat.bitIndices_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (k : ℕ), (2 ^ k).bitIndices = [k]
参数：k : ℕ；2 ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.bitIndices_two_pow_mul`：∀ (k n : ℕ), (2 ^ k * n).bitIndices = List.m
ap (fun x => x + k) n.bitIndices
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.bitIndices_one`：Nat.bitIndices 1 = [0]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem bitIndices_two_pow (k : ℕ) : bitIndices (2 ^ k) = [k] := by
  rw [← mul_one (a := 2 ^ k), bitIndices_two_pow_mul]; simp
/-
**Nat.sum_map_two_pow_bitIndices** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (List.map (fun i => 2 ^ i) n.bitIndices).sum = n
参数：n : ℕ；List.map (fun i => 2 ^ i) n.bitIndices。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bitIndices_zero`：Nat.bitIndices 0 = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.bitIndices_two_mul`：∀ (n : ℕ), (2 * n).bitIndices = List.map (fun x 
=> x + 1) n.bitIndices
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用引理 `List.sum_map_mul_left`：sum_map_mul_left : (l.map fun b => r * f b).sum =
 r * (l.map f).sum
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bitIndices_two_mul_add_one`：∀ (n : ℕ), (2 * n + 1).bitIndices = 0 ::
 List.map (fun x => x + 1) n.bitIndices
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
@[simp] theorem sum_map_two_pow_bitIndices (n : ℕ) :
    (n.bitIndices.map (fun i ↦ 2 ^ i)).sum = n := by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    have hrw : (fun i ↦ 2 ^ i) ∘ (fun x ↦ x + 1) = fun i ↦ 2 * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    cases b
    · simpa [hrw, List.sum_map_mul_left]
    simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

@[deprecated (since := "2026-05-15")] alias twoPowSum_bitIndices := sum_map_two_pow_bitIndices
/-
**Nat.mem_bitIndices** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {i n : ℕ}, i ∈ n.bitIndices ↔ n.testBit i = true
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.bitIndices_zero`：Nat.bitIndices 0 = []
· 使用定理 `Nat.zero_testBit`：∀ (i : ℕ), Nat.testBit 0 i = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.bitIndices_two_mul`：∀ (n : ℕ), (2 * n).bitIndices = List.map (fun x 
=> x + 1) n.bitIndices
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.testBit_add_one`：∀ (x i : ℕ), x.testBit (i + 1) = (x / 2).testBit i
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.bitIndices_two_mul_add_one`：∀ (n : ℕ), (2 * n + 1).bitIndices = 0 ::
 List.map (fun x => x + 1) n.bitIndices
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.mul_add_mod_self_left`：∀ (a b c : ℕ), (a * b + c) % a = c % a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
（共 32 条，此处仅展示前 30 条）
-/
@[simp] theorem mem_bitIndices {i n : ℕ} : i ∈ n.bitIndices ↔ n.testBit i := by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp
  | bit b n ih => cases b <;> cases i <;> simp_all [Nat.testBit_add_one, Nat.mul_add_div]

/--
Together with `Nat.sum_map_bitIndices_two_pow`, this implies a bijection between `ℕ` and `Finset ℕ`.
See `Finset.equivBitIndices` for this bijection.
-/
/-
**Nat.bitIndices_sum_map_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitIndices_sum_map_two_pow {L : List Nat} (hL : List.SortedLT L) : (L.map 
(fun i => 2 ^ i)).sum.bitIndices = L
参数：hL : List.SortedLT L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitIndices_sum_map_two_pow._unary`：∀ (_x : (L : List ℕ) ×' L.SortedL
T), (List.map (fun i => 2 ^ i) _x.1).sum.bitIndices = _x.1

--- 原说明 ---
Together with `Nat.sum_map_bitIndices_two_pow`, this implies a bijection between
 `ℕ` and `Finset ℕ`.
See `Finset.equivBitIndices` for this bijection.
-/
theorem bitIndices_sum_map_two_pow {L : List ℕ} (hL : List.SortedLT L) :
    (L.map (fun i ↦ 2 ^ i)).sum.bitIndices = L := by
  cases L with | nil => simp | cons a L =>
  obtain ⟨haL, hL⟩ := pairwise_cons.1 hL.pairwise
  simp_rw [Nat.lt_iff_add_one_le] at haL
  have h' : ∃ (L₀ : List ℕ), L₀.SortedLT ∧ L = L₀.map (· + a + 1) := by
    refine ⟨L.map (· - (a+1)), ?_, ?_⟩
    · rwa [sortedLT_iff_pairwise, pairwise_map, Pairwise.and_mem,
        Pairwise.iff (S := fun x y ↦ x ∈ L ∧ y ∈ L ∧ x < y), ← Pairwise.and_mem]
      simp only [and_congr_right_iff]
      exact fun x y hx _ ↦ by rw [tsub_lt_tsub_iff_right (haL _ hx)]
    have h' : ∀ x ∈ L, ((fun x ↦ x + a + 1) ∘ (fun x ↦ x - (a + 1))) x = x := fun x hx ↦ by
      simp only [add_assoc, Function.comp_apply]; rw [tsub_add_cancel_of_le (haL _ hx)]
    simp [List.map_congr_left h']
  obtain ⟨L₀, hL₀, rfl⟩ := h'
  have hrw : (2 ^ ·) ∘ (· + a + 1) = fun i ↦ 2 ^ a * (2 * 2 ^ i) := by
    ext x; simp only [Function.comp_apply, pow_add, pow_one]; ac_rfl
  simp only [List.map_cons, List.map_map, List.sum_map_mul_left, List.sum_cons, hrw]
  nth_rw 1 [← mul_one (a := 2 ^ a)]
  rw [← mul_add, bitIndices_two_pow_mul, add_comm, bitIndices_two_mul_add_one,
    bitIndices_sum_map_two_pow hL₀]
  simp [add_comm (a := 1), add_assoc]
termination_by L.length

@[deprecated (since := "2026-05-15")] alias bitIndices_twoPowsum := bitIndices_sum_map_two_pow
/-
**Nat.two_pow_le_of_mem_bitIndices** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：two_pow_le_of_mem_bitIndices (ha : a in n.bitIndices) : 2 ^ a <= n
参数：ha : a in n.bitIndices。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ge_two_pow_of_testBit`：∀ {i x : ℕ}, x.testBit i = true → x ≥ 2 ^ i
-/
theorem two_pow_le_of_mem_bitIndices (ha : a ∈ n.bitIndices) : 2 ^ a ≤ n :=
  ge_two_pow_of_testBit (by simpa using ha)
/-
**Nat.notMem_bitIndices_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：notMem_bitIndices_self (n : Nat) : n ∉ n.bitIndices
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
· 使用定理 `Nat.two_pow_le_of_mem_bitIndices`：two_pow_le_of_mem_bitIndices (ha : a i
n n.bitIndices) : 2 ^ a <= n
-/
theorem notMem_bitIndices_self (n : ℕ) : n ∉ n.bitIndices :=
  fun h ↦ n.lt_two_pow_self.not_ge <| two_pow_le_of_mem_bitIndices h

end Nat

