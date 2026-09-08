/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LucasPrimality

/-!
# Fermat numbers

The Fermat numbers are a sequence of natural numbers defined as `Nat.fermatNumber n = 2^(2^n) + 1`,
for all natural numbers `n`.

## Main theorems

- `Nat.coprime_fermatNumber_fermatNumber`: two distinct Fermat numbers are coprime.
- `Nat.pepin_primality`: For 0 < n, Fermat number Fₙ is prime if `3 ^ (2 ^ (2 ^ n - 1)) = -1 mod Fₙ`
- `fermat_primeFactors_one_lt`: For 1 < n, Prime factors the Fermat number Fₙ are of
  form `k * 2 ^ (n + 2) + 1`.
-/

@[expose] public section

open Function

namespace Nat

open Finset Nat ZMod

/-- Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`. -/
/-
**Nat.fermatNumber** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：fermatNumber (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`.
-/
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
/-
**Nat.fermatNumber_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.fermatNumber 0 = 3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fermatNumber_zero : fermatNumber 0 = 3 := rfl
/-
**Nat.fermatNumber_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.fermatNumber 1 = 5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fermatNumber_one : fermatNumber 1 = 5 := rfl
/-
**Nat.fermatNumber_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.fermatNumber 2 = 17
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fermatNumber_two : fermatNumber 2 = 17 := rfl
/-
**Nat.fermatNumber_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_strictMono : StrictMono fermatNumber
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem fermatNumber_strictMono : StrictMono fermatNumber := by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, Nat.pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]
/-
**Nat.fermatNumber_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_mono : Monotone fermatNumber
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.fermatNumber_strictMono`：fermatNumber_strictMono : StrictMono fermat
Number
-/
lemma fermatNumber_mono : Monotone fermatNumber := fermatNumber_strictMono.monotone
/-
**Nat.fermatNumber_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_injective : Injective fermatNumber
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Nat.fermatNumber_strictMono`：fermatNumber_strictMono : StrictMono fermat
Number
-/
lemma fermatNumber_injective : Injective fermatNumber := fermatNumber_strictMono.injective
/-
**Nat.three_le_fermatNumber** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：three_le_fermatNumber (n : Nat) : 3 <= fermatNumber n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.fermatNumber_mono`：fermatNumber_mono : Monotone fermatNumber
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma three_le_fermatNumber (n : ℕ) : 3 ≤ fermatNumber n := fermatNumber_mono n.zero_le
/-
**Nat.two_lt_fermatNumber** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_lt_fermatNumber (n : Nat) : 2 < fermatNumber n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.three_le_fermatNumber`：three_le_fermatNumber (n : Nat) : 3 <= fermat
Number n
-/
lemma two_lt_fermatNumber (n : ℕ) : 2 < fermatNumber n := three_le_fermatNumber _
/-
**Nat.fermatNumber_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_ne_one (n : Nat) : fermatNumber n != 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.three_le_fermatNumber`：three_le_fermatNumber (n : Nat) : 3 <= fermat
Number n
-/
lemma fermatNumber_ne_one (n : ℕ) : fermatNumber n ≠ 1 := by have := three_le_fermatNumber n; lia
/-
**Nat.odd_fermatNumber** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_fermatNumber (n : Nat) : Odd (fermatNumber n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
· 使用定理 `Even.pow_of_ne_zero`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even 
a → ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem odd_fermatNumber (n : ℕ) : Odd (fermatNumber n) :=
  (even_two.pow_of_ne_zero (pow_pos two_pos n).ne').add_one
/-
**Nat.prod_fermatNumber** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_fermatNumber (n : Nat) : ∏ k in range n, fermatNumber k = fermatNumbe
r n - 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `Nat.fermatNumber.eq_1`：∀ (n : ℕ), n.fermatNumber = 2 ^ 2 ^ n + 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sq_sub_sq`：∀ (a b : ℕ), a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 39 条，此处仅展示前 30 条）
-/
theorem prod_fermatNumber (n : ℕ) : ∏ k ∈ range n, fermatNumber k = fermatNumber n - 2 := by
  induction n with | zero => rfl | succ n hn =>
  rw [prod_range_succ, hn, fermatNumber, fermatNumber, mul_comm,
    (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by lia), ← sq_sub_sq]
  ring_nf
  lia
/-
**Nat.fermatNumber_eq_prod_add_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_eq_prod_add_two (n : Nat) : fermatNumber n = ∏ k in range n, 
fermatNumber k + 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prod_fermatNumber`：prod_fermatNumber (n : Nat) : ∏ k in range n, fer
matNumber k = fermatNumber n - 2
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Nat.two_lt_fermatNumber`：two_lt_fermatNumber (n : Nat) : 2 < fermatNumbe
r n
-/
theorem fermatNumber_eq_prod_add_two (n : ℕ) :
    fermatNumber n = ∏ k ∈ range n, fermatNumber k + 2 := by
  rw [prod_fermatNumber, Nat.sub_add_cancel]
  exact le_of_lt <| two_lt_fermatNumber _
/-
**Nat.fermatNumber_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_succ (n : Nat) : fermatNumber (n + 1) = (fermatNumber n - 1) 
^ 2 + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.fermatNumber.eq_1`：∀ (n : ℕ), n.fermatNumber = 2 ^ 2 ^ n + 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem fermatNumber_succ (n : ℕ) : fermatNumber (n + 1) = (fermatNumber n - 1) ^ 2 + 1 := by
  rw [fermatNumber, pow_succ, mul_comm, pow_mul', fermatNumber, add_tsub_cancel_right]
/-
**Nat.two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq** 是 Mathlib 中的一个定理，位于命名
空间 `Nat`。
形式化陈述：two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq (n : Nat) : 2 * (fermat
Number n - 1) ^ 2 <= (fermatNumber (n + 1)) ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
（共 51 条，此处仅展示前 30 条）
-/
theorem two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq (n : ℕ) :
    2 * (fermatNumber n - 1) ^ 2 ≤ (fermatNumber (n + 1)) ^ 2 := by
  simp only [fermatNumber, add_tsub_cancel_right]
  have : 0 ≤ 1 + 2 ^ (2 ^ n * 4) := le_add_left _ _
  ring_nf
  lia
/-
**Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq** 是 Ma
thlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : N
at) : fermatNumber (n + 2) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 
1) ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_sub_self_right`：∀ (a b : ℕ), a + b - b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 53 条，此处仅展示前 30 条）
-/
theorem fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : ℕ) :
    fermatNumber (n + 2) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  simp only [fermatNumber, add_sub_self_right]
  rw [← add_sub_self_right (2 ^ 2 ^ (n + 2) + 1) <| 2 * 2 ^ 2 ^ (n + 1)]
  ring_nf

end Nat

open Nat

/-
**Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n
 : Nat) : (fermatNumber (n + 2) : Int) = (fermatNumber (n + 1)) ^ 2 - 2 * (ferma
tNumber n - 1) ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq`
：fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : Nat) :
 fermatNumber (n + 2) = (fermatNumber (n + 1)) ^ 2 - 2 * (fer…
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq`：two_mul_fermatNu
mber_sub_one_sq_le_fermatNumber_sq (n : Nat) : 2 * (fermatNumber n - 1) ^ 2 <= (
fermatNumber (n + 1)) ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : ℕ) :
    (fermatNumber (n + 2) : ℤ) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  rw [Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq,
    Nat.cast_sub <| two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq n]
  simp only [fermatNumber, push_cast, add_tsub_cancel_right]

namespace Nat

open Finset
/--
**Goldbach's theorem** : no two distinct Fermat numbers share a common factor greater than one.

From a letter to Euler, see page 37 in [juskevic2022].
-/
/-
**Nat.coprime_fermatNumber_fermatNumber** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_fermatNumber_fermatNumber {m n : Nat} (hmn : m != n) : Coprime (fe
rmatNumber m) (fermatNumber n)
参数：hmn : m != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_add_right`：∀ {a b c : ℕ}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.fermatNumber_eq_prod_add_two`：fermatNumber_eq_prod_add_two (n : Nat)
 : fermatNumber n = ∏ k in range n, fermatNumber k + 2
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Odd.not_two_dvd_nat`：∀ {n : ℕ}, Odd n → ¬2 ∣ n
· 使用定理 `Nat.odd_fermatNumber`：odd_fermatNumber (n : Nat) : Odd (fermatNumber n)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
**Goldbach's theorem** : no two distinct Fermat numbers share a common factor gr
eater than one.

From a letter to Euler, see page 37 in [juskevic2022].
-/
theorem coprime_fermatNumber_fermatNumber {m n : ℕ} (hmn : m ≠ n) :
    Coprime (fermatNumber m) (fermatNumber n) := by
  wlog hmn' : m < n
  · simpa only [coprime_comm] using this hmn.symm (by lia)
  let d := (fermatNumber m).gcd (fermatNumber n)
  have h_n : d ∣ fermatNumber n := gcd_dvd_right ..
  have h_m : d ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_left _ _).trans <| dvd_prod_of_mem _
    <| mem_range.mpr hmn').mp <| fermatNumber_eq_prod_add_two _ ▸ h_n
  refine ((dvd_prime prime_two).mp h_m).resolve_right fun h_two ↦ ?_
  exact (odd_fermatNumber _).not_two_dvd_nat (h_two ▸ h_n)
/-
**Nat.pairwise_coprime_fermatNumber** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pairwise_coprime_fermatNumber : Pairwise fun m n => Coprime (fermatNumber 
m) (fermatNumber n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_fermatNumber_fermatNumber`：coprime_fermatNumber_fermatNumber
 {m n : Nat} (hmn : m != n) : Coprime (fermatNumber m) (fermatNumber n)
-/
lemma pairwise_coprime_fermatNumber :
    Pairwise fun m n ↦ Coprime (fermatNumber m) (fermatNumber n) :=
  fun _m _n ↦ coprime_fermatNumber_fermatNumber

open ZMod

/-- Prime `a ^ n + 1` implies `n` is a power of two (**Fermat primes**). -/
/-
**Nat.pow_of_pow_add_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_of_pow_add_prime {a n : Nat} (ha : 1 < a) (hn : n != 0) (hP : (a ^ n +
 1).Prime) : exists m : Nat, n = 2 ^ m
参数：ha : 1 < a；hn : n != 0；hP : (a ^ n + 1).Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_two_pow_mul_odd`：exists_eq_two_pow_mul_odd {n : Nat} (hn :
 n != 0) : exists k m : Nat, Odd m ∧ n = 2 ^ k * m
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Odd.nat_add_dvd_pow_add_pow`：∀ (x y : ℕ) {n : ℕ}, Odd n → x + y ∣ x ^ n 
+ y ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_eq_self_iff`：∀ {a b : ℕ}, 1 < a → (a ^ b = a ↔ b = 1)
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
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
· 使用定理 `Nat.Prime.dvd_iff_eq`：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Prime `a ^ n + 1` implies `n` is a power of two (**Fermat primes**).
-/
theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

/-- `Fₙ = 2^(2^n)+1` is prime if `3^(2^(2^n-1)) = -1 mod Fₙ` (**Pépin's test**). -/
/-
**Nat.pepin_primality** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pepin_primality (n : Nat) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatN
umber n))) : (fermatNumber n).Prime
参数：n : Nat；h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.two_lt_fermatNumber`：two_lt_fermatNumber (n : Nat) : 2 < fermatNumbe
r n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.one_le_two_pow`：∀ {n : ℕ}, 1 ≤ 2 ^ n
· 使用定理 `lucas_primality`：lucas_primality (p : Nat) (a : ZMod p) (ha : a ^ (p - 1
) = 1) (hd : forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1) : p
.Prim…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ZMod.neg_one_ne_one`：neg_one_ne_one {n : Nat} [Fact (2 < n)] : (-1 : ZMo
d n) != 1

--- 原说明 ---
`Fₙ = 2^(2^n)+1` is prime if `3^(2^(2^n-1)) = -1 mod Fₙ` (**Pépin's test**).
-/
lemma pepin_primality (n : ℕ) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  have := Fact.mk (two_lt_fermatNumber n)
  unfold fermatNumber at h this
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq]
  · intro p hp1 hp2
    rw [Nat.add_sub_cancel, (Nat.prime_dvd_prime_iff_eq hp1 prime_two).mp (hp1.dvd_of_dvd_pow hp2),
        key, pow_succ, Nat.mul_div_cancel _ two_pos, ← pow_succ, ← key, h]
    exact neg_one_ne_one

/-- `Fₙ = 2^(2^n)+1` is prime if `3^((Fₙ - 1)/2) = -1 mod Fₙ` (**Pépin's test**). -/
/-
**Nat.pepin_primality'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pepin_primality' (n : Nat) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMo
d (fermatNumber n))) : (fermatNumber n).Prime
参数：n : Nat；h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.pepin_primality`：pepin_primality (n : Nat) (h : 3 ^ (2 ^ (2 ^ n - 1)
) = (-1 : ZMod (fermatNumber n))) : (fermatNumber n).Prime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.fermatNumber.eq_1`：∀ (n : ℕ), n.fermatNumber = 2 ^ 2 ^ n + 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.pow_div`：∀ {x m n : ℕ}, n ≤ m → 0 < x → x ^ m / x ^ n = x ^ (m - n)
· 使用定理 `Nat.one_le_two_pow`：∀ {n : ℕ}, 1 ≤ 2 ^ n
· 使用定理 `Nat.zero_lt_two`：0 < 2

--- 原说明 ---
`Fₙ = 2^(2^n)+1` is prime if `3^((Fₙ - 1)/2) = -1 mod Fₙ` (**Pépin's test**).
-/
lemma pepin_primality' (n : ℕ) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  apply pepin_primality
  rw [← h]
  congr
  rw [fermatNumber, add_tsub_cancel_right, Nat.pow_div Nat.one_le_two_pow Nat.zero_lt_two]


/-- Prime factors of `a ^ (2 ^ n) + 1` are of form `k * 2 ^ (n + 1) + 1`. -/
/-
**Nat.pow_pow_add_primeFactors_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_pow_add_primeFactors_one_lt {a n p : Nat} (hp : p.Prime) (hp2 : p != 2
) (hpdvd : p ∣ a ^ (2 ^ n) + 1) : exists k, p = k * 2 ^ (n + 1) + 1
参数：hp : p.Prime；hp2 : p != 2；hpdvd : p ∣ a ^ (2 ^ n) + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `zero_eq_neg`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, 0 = 
-a ↔ a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `orderOf_eq_prime_pow`：orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin
 : x ^ p ^ (n + 1) = 1) : orderOf x = p ^ (n + 1)
· 使用定理 `ZMod.neg_one_ne_one`：neg_one_ne_one {n : Nat} [Fact (2 < n)] : (-1 : ZMo
d n) != 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Prime factors of `a ^ (2 ^ n) + 1` are of form `k * 2 ^ (n + 1) + 1`.
-/
lemma pow_pow_add_primeFactors_one_lt {a n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ a ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 1) + 1 := by
  have : Fact (2 < p) := Fact.mk (lt_of_le_of_ne hp.two_le hp2.symm)
  have : Fact p.Prime := Fact.mk hp
  have ha1 : (a : ZMod p) ^ (2 ^ n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (natCast_eq_zero_iff (a ^ (2 ^ n) + 1) p).mpr hpdvd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero n two_ne_zero), zero_eq_neg] at ha1
    exact one_ne_zero ha1
  have ha : orderOf (a : ZMod p) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [ha1]
      exact neg_one_ne_one
    · rw [pow_succ, pow_mul, ha1, neg_one_sq]
  simpa [ha, dvd_def, Nat.sub_eq_iff_eq_add hp.one_le, mul_comm] using orderOf_dvd_card_sub_one ha0

-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 2) + 1`. -/
/-
**Nat.fermat_primeFactors_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：fermat_primeFactors_one_lt (n p : Nat) (hn : 1 < n) (hp : p.Prime) (hpdvd 
: p ∣ fermatNumber n) : exists k, p = k * 2 ^ (n + 2) + 1
参数：n p : Nat；hn : 1 < n；hp : p.Prime；hpdvd : p ∣ fermatNumber n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.ne_two_of_dvd_nat`：Odd.ne_two_of_dvd_nat {m n : Nat} (hn : Odd n) (h
m : m ∣ n) : m != 2
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
· 使用定理 `Even.pow_of_ne_zero`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even 
a → ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.pow_pow_add_primeFactors_one_lt`：pow_pow_add_primeFactors_one_lt {a 
n p : Nat} (hp : p.Prime) (hp2 : p != 2) (hpdvd : p ∣ a ^ (2 ^ n) + 1) : exists 
k, p = k * 2 ^ (n + 1) + …
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.exists_sq_eq_two_iff`：exists_sq_eq_two_iff (hp : p != 2) : IsSquare
 (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Prime factors of `a ^ (2 ^ n) + 1` are of form `k * 2 ^ (n + 1) + 1`. - /
lemma pow_pow_add_primeFactors_one_lt {a n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ a ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 1) + 1 := by
  have : Fact (2 < p) := Fact.mk (lt_of_le_of_ne hp.two_le hp2.symm)
  have : Fact p.Prime := Fact.mk hp
  have ha1 : (a : ZMod p) ^ (2 ^ n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (natCast_eq_zero_iff (a ^ (2 ^ n) + 1) p).mpr hpdvd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero n two_ne_zero), zero_eq_neg] at ha1
    exact one_ne_zero ha1
  have ha : orderOf (a : ZMod p) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [ha1]
      exact neg_one_ne_one
    · rw [pow_succ, pow_mul, ha1, neg_one_sq]
  simpa [ha, dvd_def, Nat.sub_eq_iff_eq_add hp.one_le, mul_comm] using orderOf_d
vd_card_sub_one ha0

-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 2
) + 1`.
-/
lemma fermat_primeFactors_one_lt (n p : ℕ) (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ fermatNumber n) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p ≠ 2 := by
    exact (even_two.pow_of_ne_zero <| pow_ne_zero n two_ne_zero).add_one.ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [add_assoc, pow_add, ← mul_assoc, ← mod_add_mod, mul_mod]
    simp
  obtain ⟨a, ha⟩ := (exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  suffices h : p ∣ a.val ^ (2 ^ (n + 1)) + 1 by
    exact pow_pow_add_primeFactors_one_lt hp hp2 h
  rw [fermatNumber] at hpdvd
  rw [← natCast_eq_zero_iff, Nat.cast_add _ 1, Nat.cast_one, Nat.cast_pow] at hpdvd ⊢
  rwa [natCast_val, ZMod.cast_id, pow_succ', pow_mul, sq, ← ha]


-- TODO: move to NumberTheory.Mersenne, once we have that.
/-!
### Primality of Mersenne numbers `Mₙ = a ^ n - 1`
-/

/-- Prime `a ^ n - 1` implies `a = 2` and prime `n`. -/
/-
**Nat.prime_of_pow_sub_one_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_of_pow_sub_one_prime {a n : Nat} (hn1 : n != 1) (hP : (a ^ n - 1).Pr
ime) : a = 2 ∧ n.Prime
参数：hn1 : n != 1；hP : (a ^ n - 1).Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.one_lt_pow_iff`：∀ {n : ℕ}, n ≠ 0 → ∀ {a : ℕ}, 1 < a ^ n ↔ 1 < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Nat.sub_dvd_pow_sub_pow`：∀ (x y n : ℕ), x - y ∣ x ^ n - y ^ n
· 使用定理 `Nat.pow_eq_self_iff`：∀ {a b : ℕ}, 1 < a → (a ^ b = a ↔ b = 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_one_cancel`：∀ {a b : ℕ}, 0 < a → 0 < b → a - 1 = b - 1 → a = b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.Prime.dvd_iff_eq`：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.sub_eq_iff_eq_add`：∀ {b a c : ℕ}, b ≤ a → (a - b = c ↔ a = c + b)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def`：prime_def {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, m ∣ p 
-> m = 1 ∨ m = p
· 使用定理 `Nat.two_le_iff`：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Prime `a ^ n - 1` implies `a = 2` and prime `n`.
-/
theorem prime_of_pow_sub_one_prime {a n : ℕ} (hn1 : n ≠ 1) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n ≠ 0 := fun h ↦ (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    let h := Nat.sub_dvd_pow_sub_pow a 1 n
    rw [one_pow, hP.dvd_iff_eq (mt (Nat.sub_eq_iff_eq_add ha1.le).mp hn1), eq_comm] at h
    exact (pow_eq_self_iff ha1).mp (Nat.sub_one_cancel ha0 (pow_pos ha0 n) h).symm
  subst ha2
  refine ⟨rfl, Nat.prime_def.mpr ⟨(two_le_iff n).mpr ⟨hn0, hn1⟩, fun d hdn ↦ ?_⟩⟩
  have hinj : ∀ x y, 2 ^ x - 1 = 2 ^ y - 1 → x = y :=
    fun x y h ↦ Nat.pow_right_injective le_rfl (sub_one_cancel (pow_pos ha0 x) (pow_pos ha0 y) h)
  let h := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 (n / d)
  rw [one_pow, ← pow_mul, Nat.mul_div_cancel' hdn] at h
  exact (hP.eq_one_or_self_of_dvd (2 ^ d - 1) h).imp (hinj d 1) (hinj d n)

end Nat

