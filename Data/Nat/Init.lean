/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.Nat.Lemmas
public import Batteries.Util.LibraryNote
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/

@[expose] public section

library_note «foundational algebra order theory» /--
Batteries has a home-baked development of the algebraic and order-theoretic theory of `ℕ` and `ℤ`
which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness
libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in
finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:
* `Mathlib/Data/Nat/Basic.lean` for the continuation of the home-baked development on `ℕ`
* `Mathlib/Data/Int/Init.lean` for the continuation of the home-baked development on `ℤ`
* `Mathlib/Algebra/Group/Nat/Defs.lean` for the monoid instances on `ℕ`
* `Mathlib/Algebra/Group/Int/Defs.lean` for the group instance on `ℤ`
* `Mathlib/Algebra/Ring/Nat.lean` for the semiring instance on `ℕ`
* `Mathlib/Algebra/Ring/Int/Defs.lean` for the ring instance on `ℤ`
* `Mathlib/Algebra/Order/Group/Nat.lean` for the ordered monoid instance on `ℕ`
* `Mathlib/Algebra/Order/Group/Int.lean` for the ordered group instance on `ℤ`
* `Mathlib/Algebra/Order/Ring/Nat.lean` for the ordered semiring instance on `ℕ`
* `Mathlib/Algebra/Order/Ring/Int.lean` for the ordered ring instance on `ℤ`
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d e m n k : ℕ} {p : ℕ → Prop}

/-! ### `succ`, `pred` -/

/-
**Nat.succ_pos'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_pos' : 0 < succ n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
### `succ`, `pred`
-/
lemma succ_pos' : 0 < succ n := succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff
/-
**Nat.two_lt_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  | n + 3, _, _, _ => le_add_left 3 n
/-
**Nat.two_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.Simproc.add_eq_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b = c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp

/-! ### `add` -/

/-! ### `sub` -/

/-! ### `mul` -/

/-
**Nat.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mul_def : Nat.mul m n = m * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_eq`：∀ {x y : ℕ}, x.mul y = x * y

--- 原说明 ---
### `mul`
-/
lemma mul_def : Nat.mul m n = m * n := mul_eq
/-
**Nat.two_mul_ne_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_ne_two_mul_add_one : 2 * n != 2 * m + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

/-! ### `div` -/

/-
**Nat.le_div_two_iff_mul_two_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_div_two_iff_mul_two_le {n m : Nat} : m <= n / 2 ↔ (m : Int) * 2 <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.ofNat_two`：↑2 = 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### `div`
-/
lemma le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, ← Int.ofNat_le, Int.natCast_mul, Int.ofNat_two]

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
/-
**Nat.div_lt_self'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_lt_self' (a b : Nat) : (a + 1) / (b + 2) < a + 1
参数：a b : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ

--- 原说明 ---
A version of `Nat.div_lt_self` using successors, rather than additional hypothes
es.
-/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))
/-
**Nat.two_mul_odd_div_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1
参数：hn : n % 2 = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  lia

/-! ### `pow` -/

/-
**Nat.one_le_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_le_pow' (n m : Nat) : 1 <= (m + 1) ^ n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
### `pow`
-/
lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp]
/-
**Nat.rec_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：rec_zero {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1)) : 
Nat.rec h0 h 0 = h0
参数：h0 : C 0；h : forall n, C n -> C (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the 
lemmas
proved above, and some of the results in later sections depend on the definition
s in this section.
-/
lemma rec_zero {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl

-- Not `@[simp]` since `simp` can reduce the whole term.
/-
**Nat.rec_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：rec_add_one {C : Nat -> Sort*} (h0 : C 0) (h : forall n, C n -> C (n + 1))
 (n : Nat) : Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n)
参数：h0 : C 0；h : forall n, C n -> C (n + 1)；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl
/-
**Nat.rec_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {C : ℕ → Sort u_1} (h0 : C 0) (h : (n : ℕ) → C n → C (n + 1)), Nat.rec h
0 h 1 = h 0 h0
参数：h0 : C 0；h : (n : ℕ) → C n → C (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
@[elab_as_elim]
/-
**Nat.leRec** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{n : ℕ} →   {motive : (m : ℕ) → n ≤ m → Sort u_1} →     motive n ⋯ → (⦃k :
 ℕ⦄ → (h : n ≤ k) → motive k h → motive (k + 1) ⋯) → {m : ℕ} → (h : n ≤ m) → mot
ive m h
参数：m : ℕ；⦃k : ℕ⦄ → (h : n ≤ k) → motive k h → motive (k + 1) ⋯；h : n ≤ m。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ

--- 原说明 ---
Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k
 ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
def leRec {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    ∀ {m} (h : n ≤ m), motive m h
  | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
  | m + 1, H =>
    (le_succ_iff.1 H).by_cases
      (fun h : n ≤ m ↦ le_succ_of_le h <| leRec refl le_succ_of_le h)
      (fun h : n = m + 1 ↦ h ▸ refl)

-- This verifies the signatures of the recursor matches the builtin one, as promised in the
-- above.
/-
**Nat.leRec_eq_leRec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：leRec_eq_leRec : @Nat.leRec.{0} = @Nat.le.rec
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
-/
theorem leRec_eq_leRec : @Nat.leRec.{0} = @Nat.le.rec := rfl

@[simp]
/-
**Nat.leRec_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (refl : motive n (N
at.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motive k h -> motive (k
 + 1) (le_succ_of_le h)) : (leRec (motive
参数：m : Nat；refl : motive n (Nat.le_refl _)；le_succ_of_le : forall ⦃k⦄ (h : n <= 
k), motive k h -> motive (k + 1) (le_succ_of_le h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma leRec_self {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    (leRec (motive := motive) refl le_succ_of_le (Nat.le_refl _) :
    motive n (Nat.le_refl _)) = refl := by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]
/-
**Nat.leRec_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (refl : motive n (N
at.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motive k h -> motive (k
 + 1) (le_succ_of_le h)) (h1 : n <= m) {h2 : n <= m + 1} : (leRec (motive
参数：m : Nat；refl : motive n (Nat.le_refl _)；le_succ_of_le : forall ⦃k⦄ (h : n <= 
k), motive k h -> motive (k + 1) (le_succ_of_le h)；h1 : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.leRec.eq_2`：∀ {n : ℕ} {motive : (m : ℕ) → n ≤ m → Sort u_1} (refl : 
motive n ⋯)   (le_succ_of_le : ⦃k : ℕ⦄ → (h : n ≤ k) → motive k h → motive (k + 
1) ⋯…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Or.by_cases.eq_1`：∀ {p q : Prop} [inst : Decidable p] {α : Sort u} (h : 
p ∨ q) (h₁ : p → α) (h₂ : q → α),   h.by_cases h₁ h₂ = if hp : p then h₁ hp else
 h₂ ⋯
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma leRec_succ {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h))
    (h1 : n ≤ m) {h2 : n ≤ m + 1} :
    (leRec (motive := motive) refl le_succ_of_le h2) =
      le_succ_of_le h1 (leRec (motive := motive) refl le_succ_of_le h1) := by
  conv =>
    lhs
    rw [leRec, Or.by_cases, dif_pos h1]
/-
**Nat.leRec_succ'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRec_succ' {n} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_l
e) : (leRec (motive
参数：m : Nat；refl le_succ_of_le。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma leRec_succ' {n} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le) :
    (leRec (motive := motive) refl le_succ_of_le (le_succ _)) = le_succ_of_le _ refl := by
  rw [leRec_succ, leRec_self]
/-
**Nat.leRec_trans** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRec_trans {n m k} {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_
of_le) (hnm : n <= m) (hmk : m <= k) : leRec (motive
参数：m : Nat；refl le_succ_of_le；hnm : n <= m；hmk : m <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma leRec_trans {n m k} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    leRec (motive := motive) refl le_succ_of_le (Nat.le_trans hnm hmk) =
      leRec
        (leRec refl (fun _ h => le_succ_of_le h) hnm)
        (fun _ h => le_succ_of_le <| Nat.le_trans hnm h) hmk := by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]
/-
**Nat.leRec_succ_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRec_succ_left {motive : (m : Nat) -> n <= m -> Sort*} (refl le_succ_of_l
e) {m} (h1 : n <= m) (h2 : n + 1 <= m) : -- the `@` is needed for this to elabor
ate, even though we only provide explicit arguments! @leRec _ _ (le_succ_of_le (
Nat.le_refl _) refl) (fun _ h ih => le_succ_of_le (le_of_succ_le h) ih) _ h2 = l
eRec (motive
参数：m : Nat；refl le_succ_of_le；h1 : n <= m；h2 : n + 1 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_trans`：leRec_trans {n m k} {motive : (m : Nat) -> n <= m -> So
rt*} (refl le_succ_of_le) (hnm : n <= m) (hmk : m <= k) : leRec (motive
· 使用引理 `Nat.leRec_succ'`：leRec_succ' {n} {motive : (m : Nat) -> n <= m -> Sort*}
 (refl le_succ_of_le) : (leRec (motive
-/
lemma leRec_succ_left {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl le_succ_of_le) {m} (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    -- the `@` is needed for this to elaborate, even though we only provide explicit arguments!
    @leRec _ _ (le_succ_of_le (Nat.le_refl _) refl)
        (fun _ h ih => le_succ_of_le (le_of_succ_le h) ih) _ h2 =
      leRec (motive := motive) refl le_succ_of_le h1 := by
  rw [leRec_trans _ _ (le_succ n) h2, leRec_succ']

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRec`. -/
@[elab_as_elim]
/-
**Nat.leRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：leRecOn {C : Nat -> Sort*} {n : Nat} : forall {m}, n <= m -> (forall {k}, 
C k -> C (k + 1)) -> C n -> C m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each 
`k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assump
tion is only made
when `k ≥ n`, see `Nat.leRec`.
-/
def leRecOn {C : ℕ → Sort*} {n : ℕ} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m :=
  fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h
/-
**Nat.leRecOn_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}, C k -> C (k + 1)} 
(x : C n) : (leRecOn n.le_refl next x : C n) = x
参数：k + 1；x : C n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma leRecOn_self {C : ℕ → Sort*} {n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x :=
  leRec_self _ _
/-
**Nat.leRecOn_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h2 : n <= m + 1} {nex
t} (x : C n) : (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m)
参数：h1 : n <= m；x : C n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma leRecOn_succ {C : ℕ → Sort*} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m) :=
  leRec_succ _ _ _
/-
**Nat.leRecOn_succ'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_succ' {C : Nat -> Sort*} {n} {h : n <= n + 1} {next : forall {k}, 
C k -> C (k + 1)} (x : C n) : (leRecOn h next x : C (n + 1)) = next x
参数：k + 1；x : C n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.leRec_succ'`：leRec_succ' {n} {motive : (m : Nat) -> n <= m -> Sort*}
 (refl le_succ_of_le) : (leRec (motive
-/
lemma leRecOn_succ' {C : ℕ → Sort*} {n} {h : n ≤ n + 1} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x :=
  leRec_succ' _ _
/-
**Nat.leRecOn_trans** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_trans {C : Nat -> Sort*} {n m k} (hnm : n <= m) (hmk : m <= k) {ne
xt} (x : C n) : (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) = leRecOn hmk (
@next) (leRecOn hnm (@next) x)
参数：hnm : n <= m；hmk : m <= k；x : C n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.leRec_trans`：leRec_trans {n m k} {motive : (m : Nat) -> n <= m -> So
rt*} (refl le_succ_of_le) (hnm : n <= m) (hmk : m <= k) : leRec (motive
-/
lemma leRecOn_trans {C : ℕ → Sort*} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) =
      leRecOn hmk (@next) (leRecOn hnm (@next) x) :=
  leRec_trans _ _ _ _
/-
**Nat.leRecOn_succ_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_succ_left {C : Nat -> Sort*} {n m} {next : forall {k}, C k -> C (k
 + 1)} (x : C n) (h1 : n <= m) (h2 : n + 1 <= m) : (leRecOn h2 next (next x) : C
 m) = (leRecOn h1 next x : C m)
参数：k + 1；x : C n；h1 : n <= m；h2 : n + 1 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.leRec_succ_left`：leRec_succ_left {motive : (m : Nat) -> n <= m -> So
rt*} (refl le_succ_of_le) {m} (h1 : n <= m) (h2 : n + 1 <= m) : -- the `@` is ne
eded for …
-/
lemma leRecOn_succ_left {C : ℕ → Sort*} {n m}
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) :=
  leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

@[deprecated (since := "2026-03-05")] alias strongRec' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRec'_spec := Nat.strongRec_eq
@[deprecated (since := "2026-03-05")] alias strongRecOn' := Nat.strongRec
@[deprecated (since := "2026-03-05")] alias strongRecOn'_beta := Nat.strongRec_eq

/-- Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`).

This is an alias of `Nat.leRec`, specialized to `Prop`. -/
@[elab_as_elim]
/-
**Nat.le_induction** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_induction {m : Nat} {P : forall n, m <= n -> Prop} (base : P m m.le_ref
l) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le hmn)) : forall n hm
n, P n hmn
参数：base : P m m.le_refl；succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ

--- 原说明 ---
Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induct
ion` (or the same
for `induction'`).

This is an alias of `Nat.leRec`, specialized to `Prop`.
-/
lemma le_induction {m : ℕ} {P : ∀ n, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (le_succ_of_le hmn)) : ∀ n hmn, P n hmn :=
  @Nat.leRec (motive := P) _ base succ

/-- Induction principle deriving the next case from the two previous ones. -/
@[elab_as_elim]
/-
**Nat.twoStepInduction** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{motive : ℕ → Sort u_1} →   motive 0 → motive 1 → ((n : ℕ) → motive n → mo
tive (n + 1) → motive (n + 2)) → (a : ℕ) → motive a
参数：(n : ℕ) → motive n → motive (n + 1) → motive (n + 2)；a : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle deriving the next case from the two previous ones.
-/
def twoStepInduction {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (more : ∀ n, motive n → motive (n + 1) → motive (n + 2)) : ∀ a, motive a
  | 0 => zero
  | 1 => one
  | _ + 2 => more _ (twoStepInduction zero one more _) (twoStepInduction zero one more _)

/-- Induction principle deriving the next case from the `k` previous ones. Use as
```
induction n using stepInduction 3 with
| base n hn => ...
| step n ih => ...
``` -/
@[elab_as_elim]
/-
**Nat.stepInduction** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：stepInduction {motive : Nat -> Sort*} (k : Nat) (base : forall i < k, moti
ve i) (step : forall n, (forall i < k, motive (n + i)) -> motive (n + k)) (a : N
at) : motive a
参数：k : Nat；base : forall i < k, motive i；step : forall n, (forall i < k, motive 
(n + i)) -> motive (n + k)；a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle deriving the next case from the `k` previous ones. Use as
```
induction n using stepInduction 3 with
| base n hn => ...
| step n ih => ...
```
-/
def stepInduction {motive : ℕ → Sort*} (k : ℕ) (base : ∀ i < k, motive i)
    (step : ∀ n, (∀ i < k, motive (n + i)) → motive (n + k)) (a : ℕ) : motive a :=
  if h : a < k then base _ h else
  (show a - k + k = a by lia) ▸ step (a - k) fun _ _ ↦ stepInduction k base step _

@[elab_as_elim]
/-
**Nat.strong_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n, p m) → p n) → p n
参数：n : ℕ；∀ (n : ℕ), (∀ m < n, p m) → p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem strong_induction_on {p : ℕ → Prop} (n : ℕ)
    (h : ∀ n, (∀ m < n, p m) → p n) : p n :=
  Nat.strongRecOn n h
/-
**Nat.case_strong_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ), (∀ m ≤ n, p m) → p (n + 1)) → 
p a
参数：a : ℕ；∀ (n : ℕ), (∀ m ≤ n, p m) → p (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem case_strong_induction_on {p : ℕ → Prop} (a : ℕ) (hz : p 0)
    (hi : ∀ n, (∀ m ≤ n, p m) → p (n + 1)) : p a :=
  Nat.caseStrongRecOn a hz hi

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `k < n`, then `P n` implies `P m` for
all `m ≤ n`.
Also works for functions to `Sort*`.

For a version also assuming `m ≤ k`, see `Nat.decreasingInduction'`. -/
@[elab_as_elim]
/-
**Nat.decreasingInduction** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：decreasingInduction {n} {motive : (m : Nat) -> m <= n -> Sort*} (of_succ :
 forall k (h : k < n), motive (k + 1) h -> motive k (le_of_succ_le h)) (self : m
otive n (Nat.le_refl _)) {m} (mn : m <= n) : motive m mn
参数：m : Nat；of_succ : forall k (h : k < n), motive (k + 1) h -> motive k (le_of_s
ucc_le h)；self : motive n (Nat.le_refl _)；mn : m <= n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ

--- 原说明 ---
Decreasing induction: if `P (k+1)` implies `P k` for all `k < n`, then `P n` imp
lies `P m` for
all `m ≤ n`.
Also works for functions to `Sort*`.

For a version also assuming `m ≤ k`, see `Nat.decreasingInduction'`.
-/
def decreasingInduction {n} {motive : (m : ℕ) → m ≤ n → Sort*}
    (of_succ : ∀ k (h : k < n), motive (k + 1) h → motive k (le_of_succ_le h))
    (self : motive n (Nat.le_refl _)) {m} (mn : m ≤ n) : motive m mn := by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]
/-
**Nat.decreasingInduction_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：decreasingInduction_self {n} {motive : (m : Nat) -> m <= n -> Sort*} (of_s
ucc self) : (decreasingInduction (motive
参数：m : Nat；of_succ self。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma decreasingInduction_self {n} {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_refl _)) = self := by
  dsimp only [decreasingInduction]
  rw [leRec_self]
/-
**Nat.decreasingInduction_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：decreasingInduction_succ {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} (
of_succ self) (mn : m <= n) (msn : m <= n + 1) : (decreasingInduction (motive
参数：m : Nat；of_succ self；mn : m <= n；msn : m <= n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
-/
lemma decreasingInduction_succ {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self)
    (mn : m ≤ n) (msn : m ≤ n + 1) :
    (decreasingInduction (motive := motive) of_succ self msn : motive m msn) =
      decreasingInduction (motive := fun m h => motive m (le_succ_of_le h))
        (fun _ _ => of_succ _ _) (of_succ _ _ self) mn := by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]
/-
**Nat.decreasingInduction_succ'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：decreasingInduction_succ' {n} {motive : (m : Nat) -> m <= n + 1 -> Sort*} 
(of_succ self) : decreasingInduction (motive
参数：m : Nat；of_succ self。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRec_succ'`：leRec_succ' {n} {motive : (m : Nat) -> n <= m -> Sort*}
 (refl le_succ_of_le) : (leRec (motive
-/
lemma decreasingInduction_succ' {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self) :
    decreasingInduction (motive := motive) of_succ self n.le_succ = of_succ _ _ self := by
  dsimp only [decreasingInduction]; rw [leRec_succ']
/-
**Nat.decreasingInduction_trans** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：decreasingInduction_trans {motive : (m : Nat) -> m <= k -> Sort*} (hmn : m
 <= n) (hnk : n <= k) (of_succ self) : (decreasingInduction (motive
参数：m : Nat；hmn : m <= n；hnk : n <= k；of_succ self。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.decreasingInduction_self`：decreasingInduction_self {n} {motive : (m 
: Nat) -> m <= n -> Sort*} (of_succ self) : (decreasingInduction (motive
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用引理 `Nat.decreasingInduction_succ`：decreasingInduction_succ {n} {motive : (m 
: Nat) -> m <= n + 1 -> Sort*} (of_succ self) (mn : m <= n) (msn : m <= n + 1) :
 (decreasingInduct…
-/
lemma decreasingInduction_trans {motive : (m : ℕ) → m ≤ k → Sort*} (hmn : m ≤ n) (hnk : n ≤ k)
    (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_trans hmn hnk) : motive m _) =
    decreasingInduction (fun _ _ => of_succ _ _) (decreasingInduction of_succ self hnk) hmn := by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk), ih, decreasingInduction_succ]
/-
**Nat.decreasingInduction_succ_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：decreasingInduction_succ_left {motive : (m : Nat) -> m <= n -> Sort*} (of_
succ self) (smn : m + 1 <= n) (mn : m <= n) : decreasingInduction (motive
参数：m : Nat；of_succ self；smn : m + 1 <= n；mn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用引理 `Nat.decreasingInduction_trans`：decreasingInduction_trans {motive : (m : 
Nat) -> m <= k -> Sort*} (hmn : m <= n) (hnk : n <= k) (of_succ self) : (decreas
ingInduction (motiv…
· 使用引理 `Nat.decreasingInduction_succ'`：decreasingInduction_succ' {n} {motive : (
m : Nat) -> m <= n + 1 -> Sort*} (of_succ self) : decreasingInduction (motive
-/
lemma decreasingInduction_succ_left {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self)
    (smn : m + 1 ≤ n) (mn : m ≤ n) :
    decreasingInduction (motive := motive) of_succ self mn =
      of_succ m smn (decreasingInduction of_succ self smn) := by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn),
    decreasingInduction_trans (n := m + 1) (Nat.le_succ m),
    decreasingInduction_succ']

/-- Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the rectangle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
/-
**Nat.strongSubRecursion** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{P : ℕ → ℕ → Sort u_1} → ((m n : ℕ) → ((x y : ℕ) → x < m → y < n → P x y) 
→ P m n) → (n m : ℕ) → P n m
参数：(m n : ℕ) → ((x y : ℕ) → x < m → y < n → P x y) → P m n；n m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the recta
ngle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler di
rectly if possible,
since this produces equation lemmas.
-/
def strongSubRecursion {P : ℕ → ℕ → Sort*} (H : ∀ m n, (∀ x y, x < m → y < n → P x y) → P m n) :
    ∀ n m : ℕ, P n m
  | n, m => H n m fun x y _ _ ↦ strongSubRecursion H x y

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P m 0` and `P 0 n` for all `m n : ℕ`, and for any
`m n : ℕ` we can extend `P` from `(m, n + 1)` and `(m + 1, n)` to `(m + 1, n + 1)` then we have
`P m n` for all `m n : ℕ`.

Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
/-
**Nat.pincerRecursion** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{P : ℕ → ℕ → Sort u_1} →   ((m : ℕ) → P m 0) → ((n : ℕ) → P 0 n) → ((x y :
 ℕ) → P x y.succ → P x.succ y → P x.succ y.succ) → (n m : ℕ) → P n m
参数：(m : ℕ) → P m 0；(n : ℕ) → P 0 n；(x y : ℕ) → P x y.succ → P x.succ y → P x.suc
c y.succ；n m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ℕ → ℕ → Sort*`, if we have `P m 0` and `P 0 n` for all `m n : ℕ`, and
 for any
`m n : ℕ` we can extend `P` from `(m, n + 1)` and `(m + 1, n)` to `(m + 1, n + 1
)` then we have
`P m n` for all `m n : ℕ`.

Note that for non-`Prop` output it is preferable to use the equation compiler di
rectly if possible,
since this produces equation lemmas.
-/
def pincerRecursion {P : ℕ → ℕ → Sort*} (Ha0 : ∀ m : ℕ, P m 0) (H0b : ∀ n : ℕ, P 0 n)
    (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ n m : ℕ, P n m
  | m, 0 => Ha0 m
  | 0, n => H0b n
  | Nat.succ _, Nat.succ _ => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`.

Weakens the assumptions of `Nat.decreasingInduction`. -/
@[elab_as_elim]
/-
**Nat.decreasingInduction'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：decreasingInduction' {P : Nat -> Sort*} (h : forall k < n, m <= k -> P (k 
+ 1) -> P k) (mn : m <= n) (hP : P n) : P m
参数：h : forall k < n, m <= k -> P (k + 1) -> P k；mn : m <= n；hP : P n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m

--- 原说明 ---
Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n`
 implies `P m`.
Also works for functions to `Sort*`.

Weakens the assumptions of `Nat.decreasingInduction`.
-/
def decreasingInduction' {P : ℕ → Sort*} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) : P m := by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) (Nat.le_refl _)
      (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
/-
**Nat.diag_induction** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：diag_induction (P : Nat -> Nat -> Prop) (ha : forall a, P (a + 1) (a + 1))
 (hb : forall b, P 0 (b + 1)) (hd : forall a b, a < b -> P (a + 1) b -> P a (b +
 1) -> P (a + 1) (b + 1)) : forall a b, a < b -> P a b | 0, _ + 1, _ => hb _ | a
 + 1, b + 1, h => by apply hd _ _ (Nat.add_lt_add_iff_right.1 h) · have : a + 1 
= b ∨ a + 1 < b
参数：P : Nat -> Nat -> Prop；ha : forall a, P (a + 1) (a + 1)；hb : forall b, P 0 (b
 + 1)；hd : forall a b, a < b -> P (a + 1) b -> P a (b + 1) -> P (a + 1) (b + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.diag_induction._unary`：∀ (P : ℕ → ℕ → Prop),   (∀ (a : ℕ), P (a + 1)
 (a + 1)) →     (∀ (b : ℕ), P 0 (b + 1)) →       (∀ (a b : ℕ), a < b → P (a + 1)
 b → P a (b + 1…

--- 原说明 ---
Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a
 < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and f
or all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b +
 1)` is true.
-/
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, _ + 1, _ => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ (Nat.add_lt_add_iff_right.1 h)
    · have : a + 1 = b ∨ a + 1 < b := by lia
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h

/-! ### `mod`, `dvd` -/

/-
**Nat.not_pos_pow_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_pos_pow_dvd {a n : Nat} (ha : 1 < a) (hn : 1 < n) : ¬ a ^ n ∣ a
参数：ha : 1 < a；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)

--- 原说明 ---
### `mod`, `dvd`
-/
lemma not_pos_pow_dvd {a n : ℕ} (ha : 1 < a) (hn : 1 < n) : ¬ a ^ n ∣ a :=
  not_dvd_of_pos_of_lt (Nat.lt_trans Nat.zero_lt_one ha)
    (lt_of_eq_of_lt (Nat.pow_one a).symm ((Nat.pow_lt_pow_iff_right ha).2 hn))

@[simp]
/-
**Nat.not_two_dvd_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), ¬2 ∣ 2 * n + 1
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ 2 * n + 1 := by
  lia

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`. -/
/-
**Nat.dvd_add_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m ∣ m + n ↔ m ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_add_right`：∀ {a b c : ℕ}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a

--- 原说明 ---
A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.
-/
@[simp] protected lemma dvd_add_self_left : m ∣ m + n ↔ m ∣ n := Nat.dvd_add_right (Nat.dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`. -/
/-
**Nat.dvd_add_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m ∣ n + m ↔ m ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_add_left`：∀ {a b c : ℕ}, a ∣ c → (a ∣ b + c ↔ a ∣ b)
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a

--- 原说明 ---
A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.
-/
@[simp] protected lemma dvd_add_self_right : m ∣ n + m ↔ m ∣ n := Nat.dvd_add_left (Nat.dvd_refl m)

/-- Two natural numbers are equal if and only if they have the same multiples. -/
/-
**Nat.dvd_right_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_right_iff_eq : (forall a : Nat, m ∣ a ↔ n ∣ a) ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two natural numbers are equal if and only if they have the same multiples.
-/
lemma dvd_right_iff_eq : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
/-
**Nat.dvd_left_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_left_iff_eq : (forall a : Nat, a ∣ m ↔ a ∣ n) ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two natural numbers are equal if and only if they have the same divisors.
-/
lemma dvd_left_iff_eq : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-! ### Decidability of predicates -/

/-
**Nat.decidableLoHi** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：decidableLoHi (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P] : Decidabl
e (forall x, lo <= x -> x < hi -> P x)
参数：lo hi : Nat；P : Nat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Decidability of predicates
-/
instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ x < hi - lo, P (lo + x)) <| by
    refine ⟨fun al x hl hh ↦ ?_,
      fun al x h ↦ al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this
/-
**Nat.decidableLoHiLe** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：decidableLoHiLe (lo hi : Nat) (P : Nat -> Prop) [DecidablePred P] : Decida
ble (forall x, lo <= x -> x <= hi -> P x)
参数：lo hi : Nat；P : Nat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
    forall₂_congr fun _ _ ↦ imp_congr Nat.lt_succ_iff Iff.rfl
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) [NeZero n] : NeZero n.natAbs where
  out := n.natAbs_ne_zero.mpr (NeZero.ne n)

/-! ### `Nat.AtLeastTwo` -/

/-- A type class for natural numbers which are greater than or equal to `2`.

`NeZero` and `AtLeastTwo` are used for numeric literals, and also for groups of related lemmas
sharing a common value of `n` that needs to be nonzero, or at least `2`, and where it is
convenient to pass this information implicitly. Instances for these classes cover some of the
cases where it is most structurally obvious from the syntactic form of `n` that it satisfies the
required conditions, such as `m + 1`. Less widely used cases may be defined as lemmas rather than
global instances and then made into instances locally where needed. If implicit arguments,
appearing before other explicit arguments, are allowed to be `autoParam`s in a future version of
Lean, such an `autoParam` that is proved `by lia` might be a more general replacement for the
use of typeclass inference for this purpose. -/
/-
**Nat.AtLeastTwo** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class for natural numbers which are greater than or equal to `2`.

`NeZero` and `AtLeastTwo` are used for numeric literals, and also for groups of 
related lemmas
sharing a common value of `n` that needs to be nonzero, or at least `2`, and whe
re it is
convenient to pass this information implicitly. Instances for these classes cove
r some of the
cases where it is most structurally obvious from the syntactic form of `n` that 
it satisfies the
required conditions, such as `m + 1`. Less widely used cases may be defined as l
emmas rather than
global instances and then made into instances locally where needed. If implicit 
arguments,
appearing before other explicit arguments, are allowed to be `autoParam`s in a f
uture version of
Lean, such an `autoParam` that is proved `by lia` might be a more general replac
ement for the
use of typeclass inference for this purpose.
-/
class AtLeastTwo (n : ℕ) : Prop where
  prop : 2 ≤ n

-- Note: the following should stay axiom-free, since it is used whenever one writes the symbol
-- `2` in an abstract additive monoid...
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [NeZero n] : (n + 1).AtLeastTwo :=
  ⟨add_le_add (one_le_iff_ne_zero.mpr (NeZero.ne n)) (Nat.le_refl 1)⟩

namespace AtLeastTwo

variable {n : ℕ} [n.AtLeastTwo]

/-
**Nat.AtLeastTwo.one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat.AtLeastTwo`。
形式化陈述：one_lt : 1 < n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
-/
lemma one_lt : 1 < n := prop
/-
**Nat.AtLeastTwo.ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat.AtLeastTwo`。
形式化陈述：ne_one : n != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用引理 `Nat.AtLeastTwo.one_lt`：one_lt : 1 < n
-/
lemma ne_one : n ≠ 1 := Nat.ne_of_gt one_lt
/-
**Nat.AtLeastTwo.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.AtLeastTwo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toNeZero (n : ℕ) [n.AtLeastTwo] : NeZero n :=
  ⟨Nat.ne_of_gt (Nat.le_of_lt one_lt)⟩

variable (n) in
/-
**Nat.AtLeastTwo.neZero_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat.AtLeastTwo`。
形式化陈述：neZero_sub_one : NeZero (n - 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
-/
lemma neZero_sub_one : NeZero (n - 1) := ⟨by have := prop (n := n); lia⟩

end AtLeastTwo

end Nat

