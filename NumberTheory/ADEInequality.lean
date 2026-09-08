/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `ADEInequality.A' q r`, the multiset `{1,q,r}`
* `ADEInequality.D' r`, the multiset `{2,2,r}`
* `ADEInequality.E6`, the multiset `{2,3,3}`
* `ADEInequality.E7`, the multiset `{2,3,4}`
* `ADEInequality.E8`, the multiset `{2,3,5}`
* `ADEInequality.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/

@[expose] public section


namespace ADEInequality

open Multiset


/-- `A' q r := {1,q,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
/-
**ADEInequality.A'** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：A' (q r : Nat+) : Multiset Nat+
参数：q r : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A' q r := {1,q,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.
-/
def A' (q r : ℕ+) : Multiset ℕ+ :=
  {1, q, r}

/-- `A r := {1,1,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
/-
**ADEInequality.A** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：A (r : Nat+) : Multiset Nat+
参数：r : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A r := {1,1,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$.
-/
def A (r : ℕ+) : Multiset ℕ+ :=
  A' 1 r

/-- `D' r := {2,2,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
/-
**ADEInequality.D'** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：D' (r : Nat+) : Multiset Nat+
参数：r : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`D' r := {2,2,r}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$.
-/
def D' (r : ℕ+) : Multiset ℕ+ :=
  {2, 2, r}

/-- `E' r := {2,3,r}` is a `Multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
/-
**ADEInequality.E'** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：E' (r : Nat+) : Multiset Nat+
参数：r : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E' r := {2,3,r}` is a `Multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$.
-/
def E' (r : ℕ+) : Multiset ℕ+ :=
  {2, 3, r}

/-- `E6 := {2,3,3}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
/-
**ADEInequality.E6** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：E6 : Multiset Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E6 := {2,3,3}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$.
-/
def E6 : Multiset ℕ+ :=
  E' 3

/-- `E7 := {2,3,4}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
/-
**ADEInequality.E7** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：E7 : Multiset Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E7 := {2,3,4}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$.
-/
def E7 : Multiset ℕ+ :=
  E' 4

/-- `E8 := {2,3,5}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
/-
**ADEInequality.E8** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：E8 : Multiset Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E8 := {2,3,5}` is a `Multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$.
-/
def E8 : Multiset ℕ+ :=
  E' 5

/-- `sumInv pqr` for a `pqr : Multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
/-
**ADEInequality.sumInv** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：sumInv (pqr : Multiset Nat+) : Rat
参数：pqr : Multiset Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sumInv pqr` for a `pqr : Multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`.
-/
def sumInv (pqr : Multiset ℕ+) : ℚ :=
  Multiset.sum (pqr.map fun (x : ℕ+) => x⁻¹)
/-
**ADEInequality.sumInv_pqr** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} = (p : Rat)⁻¹ + (q : Rat)⁻¹ +
 (r : Rat)⁻¹
参数：p q r : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumInv_pqr (p q r : ℕ+) : sumInv {p, q, r} = (p : ℚ)⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹ := by
  simp only [sumInv, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]

/-- A multiset `pqr` of positive natural numbers is `Admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
/-
**ADEInequality.Admissible** 是 Mathlib 中的一个定义，位于命名空间 `ADEInequality`。
形式化陈述：Admissible (pqr : Multiset Nat+) : Prop
参数：pqr : Multiset Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiset `pqr` of positive natural numbers is `Admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`.
-/
def Admissible (pqr : Multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr
/-
**ADEInequality.admissible_A'** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：admissible_A' (q r : Nat+) : Admissible (A' q r)
参数：q r : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem admissible_A' (q r : ℕ+) : Admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩
/-
**ADEInequality.admissible_D'** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：admissible_D' (n : Nat+) : Admissible (D' n)
参数：n : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem admissible_D' (n : ℕ+) : Admissible (D' n) :=
  Or.inr <| Or.inl ⟨n, rfl⟩
/-
**ADEInequality.admissible_E'3** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：ADEInequality.Admissible (ADEInequality.E' 3)
参数：ADEInequality.E' 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem admissible_E'3 : Admissible (E' 3) :=
  Or.inr <| Or.inr <| Or.inl rfl
/-
**ADEInequality.admissible_E'4** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：ADEInequality.Admissible (ADEInequality.E' 4)
参数：ADEInequality.E' 4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem admissible_E'4 : Admissible (E' 4) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
/-
**ADEInequality.admissible_E'5** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：ADEInequality.Admissible (ADEInequality.E' 5)
参数：ADEInequality.E' 5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem admissible_E'5 : Admissible (E' 5) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
/-
**ADEInequality.admissible_E6** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：admissible_E6 : Admissible E6
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ADEInequality.admissible_E'3`：ADEInequality.Admissible (ADEInequality.E'
 3)
-/
theorem admissible_E6 : Admissible E6 :=
  admissible_E'3
/-
**ADEInequality.admissible_E7** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：admissible_E7 : Admissible E7
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ADEInequality.admissible_E'4`：ADEInequality.Admissible (ADEInequality.E'
 4)
-/
theorem admissible_E7 : Admissible E7 :=
  admissible_E'4
/-
**ADEInequality.admissible_E8** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：admissible_E8 : Admissible E8
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ADEInequality.admissible_E'5`：ADEInequality.Admissible (ADEInequality.E'
 5)
-/
theorem admissible_E8 : Admissible E8 :=
  admissible_E'5
/-
**ADEInequality.Admissible.one_lt_sumInv** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequalit
y.Admissible`。
形式化陈述：∀ {pqr : Multiset ℕ+}, ADEInequality.Admissible pqr → 1 < ADEInequality.su
mInv pqr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ADEInequality.Admissible.eq_1`：∀ (pqr : Multiset ℕ+),   ADEInequality.Ad
missible pqr =     ((∃ q r, ADEInequality.A' q r = pqr) ∨       (∃ r, ADEInequal
ity.D' r = pqr) ∨ A…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ADEInequality.A'.eq_1`：∀ (q r : ℕ+), ADEInequality.A' q r = {1, q, r}
· 使用定理 `ADEInequality.sumInv_pqr`：sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} =
 (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ADEInequality.D'.eq_1`：∀ (r : ℕ+), ADEInequality.D' r = {2, 2, r}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 35 条，此处仅展示前 30 条）
-/
theorem Admissible.one_lt_sumInv {pqr : Multiset ℕ+} : Admissible pqr → 1 < sumInv pqr := by
  rw [Admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sumInv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sumInv_pqr]
    norm_num
  all_goals
    rw [← H, E', sumInv_pqr]
    norm_num
/-
**ADEInequality.lt_three** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：lt_three {p q r : Nat+} (hpq : p <= q) (hqr : q <= r) (H : 1 < sumInv {p, 
q, r}) : p < 3
参数：hpq : p <= q；hqr : q <= r；H : 1 < sumInv {p, q, r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ADEInequality.sumInv_pqr`：sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} =
 (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
-/
theorem lt_three {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r) (H : 1 < sumInv {p, q, r}) : p < 3 := by
  contrapose! H
  rw [sumInv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  have hp : (p : ℚ)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hq : (q : ℚ)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3q)
  have hr : (r : ℚ)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3r)
  calc
    (p : ℚ)⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹ ≤ 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add hp hq) hr
    _ = 1 := by norm_num
/-
**ADEInequality.lt_four** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：lt_four {q r : Nat+} (hqr : q <= r) (H : 1 < sumInv {2, q, r}) : q < 4
参数：hqr : q <= r；H : 1 < sumInv {2, q, r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ADEInequality.sumInv_pqr`：sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} =
 (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
-/
theorem lt_four {q r : ℕ+} (hqr : q ≤ r) (H : 1 < sumInv {2, q, r}) : q < 4 := by
  contrapose! H
  rw [sumInv_pqr]
  have h4r := H.trans hqr
  have hq : (q : ℚ)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hr : (r : ℚ)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h4r)
  calc
    (2⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹) ≤ 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl hq) hr
    _ = 1 := by norm_num
/-
**ADEInequality.lt_six** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：lt_six {r : Nat+} (H : 1 < sumInv {2, 3, r}) : r < 6
参数：H : 1 < sumInv {2, 3, r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ADEInequality.sumInv_pqr`：sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} =
 (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
-/
theorem lt_six {r : ℕ+} (H : 1 < sumInv {2, 3, r}) : r < 6 := by
  contrapose! H
  rw [sumInv_pqr]
  have hr : (r : ℚ)⁻¹ ≤ 6⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  calc
    (2⁻¹ + 3⁻¹ + (r : ℚ)⁻¹ : ℚ) ≤ 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) hr
    _ = 1 := by norm_num
/-
**ADEInequality.admissible_of_one_lt_sumInv_aux'** 是 Mathlib 中的一个定理，位于命名空间 `ADEI
nequality`。
形式化陈述：admissible_of_one_lt_sumInv_aux' {p q r : Nat+} (hpq : p <= q) (hqr : q <=
 r) (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r}
参数：hpq : p <= q；hqr : q <= r；H : 1 < sumInv {p, q, r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ADEInequality.lt_three`：lt_three {p q r : Nat+} (hpq : p <= q) (hqr : q 
<= r) (H : 1 < sumInv {p, q, r}) : p < 3
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `ADEInequality.admissible_A'`：admissible_A' (q r : Nat+) : Admissible (A'
 q r)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ADEInequality.lt_four`：lt_four {q r : Nat+} (hqr : q <= r) (H : 1 < sumI
nv {2, q, r}) : q < 4
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `ADEInequality.admissible_D'`：admissible_D' (n : Nat+) : Admissible (D' n
)
· 使用定理 `ADEInequality.lt_six`：lt_six {r : Nat+} (H : 1 < sumInv {2, 3, r}) : r <
 6
· 使用定理 `ADEInequality.admissible_E6`：admissible_E6 : Admissible E6
· 使用定理 `ADEInequality.admissible_E7`：admissible_E7 : Admissible E7
· 使用定理 `ADEInequality.admissible_E8`：admissible_E8 : Admissible E8
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem admissible_of_one_lt_sumInv_aux' {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r)
    (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r} := by
  have hp3 : p < 3 := lt_three hpq hqr H
  -- Porting note: `interval_cases` doesn't support `ℕ+` yet.
  replace hp3 := Finset.mem_Iio.mpr hp3
  conv at hp3 => change p ∈ ({1, 2} : Multiset ℕ+)
  fin_cases hp3
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  replace hq4 := Finset.mem_Ico.mpr ⟨hpq, hq4⟩; clear hpq
  conv at hq4 => change q ∈ ({2, 3} : Multiset ℕ+)
  fin_cases hq4
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  replace hr6 := Finset.mem_Ico.mpr ⟨hqr, hr6⟩; clear hqr
  conv at hr6 => change r ∈ ({3, 4, 5} : Multiset ℕ+)
  fin_cases hr6
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8
/-
**ADEInequality.admissible_of_one_lt_sumInv_aux** 是 Mathlib 中的一个定理，位于命名空间 `ADEIn
equality`。
形式化陈述：admissible_of_one_lt_sumInv_aux : forall {pqr : List Nat+} (_ : pqr.Sorted
LE) (_ : pqr.length = 3) (_ : 1 < sumInv pqr), Admissible pqr | [p, q, r], hs, _
, H => by obtain ⟨⟨hpq, -⟩, hqr⟩ : (p <= q ∧ p <= r) ∧ q <= r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `ADEInequality.admissible_of_one_lt_sumInv_aux'`：admissible_of_one_lt_sum
Inv_aux' {p q r : Nat+} (hpq : p <= q) (hqr : q <= r) (H : 1 < sumInv {p, q, r})
 : Admissible {p, q, r}
-/
theorem admissible_of_one_lt_sumInv_aux :
    ∀ {pqr : List ℕ+} (_ : pqr.SortedLE) (_ : pqr.length = 3) (_ : 1 < sumInv pqr),
      Admissible pqr
  | [p, q, r], hs, _, H => by
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r := by simpa using hs.pairwise
    exact admissible_of_one_lt_sumInv_aux' hpq hqr H
/-
**ADEInequality.admissible_of_one_lt_sumInv** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequa
lity`。
形式化陈述：admissible_of_one_lt_sumInv {p q r : Nat+} (H : 1 < sumInv {p, q, r}) : Ad
missible {p, q, r}
参数：H : 1 < sumInv {p, q, r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `Multiset.pairwise_sort`：pairwise_sort : (sort s r).Pairwise r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sort_eq`：sort_eq : ↑(sort s r) = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ADEInequality.admissible_of_one_lt_sumInv_aux`：admissible_of_one_lt_sumI
nv_aux : forall {pqr : List Nat+} (_ : pqr.SortedLE) (_ : pqr.length = 3) (_ : 1
 < sumInv pqr), Admissible pqr | [p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.length_sort`：length_sort : (sort s r).length = card s
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem admissible_of_one_lt_sumInv {p q r : ℕ+} (H : 1 < sumInv {p, q, r}) :
    Admissible {p, q, r} := by
  simp only [Admissible]
  let S := sort (α := ℕ+) {p, q, r}
  have hS : S.SortedLE := (pairwise_sort _ _).sortedLE
  have hpqr : ({p, q, r} : Multiset ℕ+) = S := (sort_eq {p, q, r} LE.le).symm
  rw [hpqr]
  rw [hpqr] at H
  apply admissible_of_one_lt_sumInv_aux hS _ H
  simp only [S, insert_eq_cons, length_sort, card_cons, card_singleton]

/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `Admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
/-
**ADEInequality.classification** 是 Mathlib 中的一个定理，位于命名空间 `ADEInequality`。
形式化陈述：classification (p q r : Nat+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r
}
参数：p q r : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ADEInequality.admissible_of_one_lt_sumInv`：admissible_of_one_lt_sumInv {
p q r : Nat+} (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r}
· 使用定理 `ADEInequality.Admissible.one_lt_sumInv`：∀ {pqr : Multiset ℕ+}, ADEInequa
lity.Admissible pqr → 1 < ADEInequality.sumInv pqr

--- 原说明 ---
A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `Admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
theorem classification (p q r : ℕ+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩

end ADEInequality

