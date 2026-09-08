/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!

# `compute_degree` and `monicity`: tactics for explicit polynomials

This file defines two related tactics: `compute_degree` and `monicity`.

Using `compute_degree` when the goal is of one of the seven forms
* `natDegree f ≤ d` (or `<`),
* `degree f ≤ d` (or `<`),
* `natDegree f = d`,
* `degree f = d`,
* `coeff f d = r`, if `d` is the degree of `f`,

tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Using `monicity` when the goal is of the form `Monic f` tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Both tactics admit a `!` modifier (`compute_degree!` and `monicity!`) instructing
Lean to try harder to close the goal.

See the doc-strings for more details.

## Future work

* Currently, `compute_degree` does not deal correctly with some edge cases.  For instance,
  ```lean
  example [Semiring R] : natDegree (C 0 : R[X]) = 0 := by
    compute_degree
  --  ⊢ 0 ≠ 0
  ```
  Still, it may not be worth to provide special support for `natDegree f = 0`.
* Make sure that numerals in coefficients are treated correctly.
* Make sure that `compute_degree` works with goals of the form `degree f ≤ ↑d`, with an
  explicit coercion from `ℕ` on the RHS.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree`, `natDegree` and `coeff` are equally supported.

## Implementation details

Assume that `f : R[X]` is a polynomial with coefficients in a semiring `R` and
`d` is either in `ℕ` or in `WithBot ℕ`.

If the goal has the form `natDegree f < d`, then we convert it to two separate goals:
* `natDegree f ≤ ?_`, on which we apply the following steps;
* `?_ < d`;

where `?_` is a metavariable that `compute_degree` computes in its process.
We proceed similarly for `degree f < d`.

If the goal has the form `natDegree f = d`, then we convert it to three separate goals:
* `natDegree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Similarly, an initial goal of the form `degree f = d` gives rise to goals of the form
* `degree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Next, we apply successively lemmas whose side-goals all have the shape
* `natDegree f ≤ d`;
* `degree f ≤ d`;
* `coeff f d = r`;

plus possibly "numerical" identities and choices of elements in `ℕ`, `WithBot ℕ`, and `R`.

Recursing into `f`, we break apart additions, multiplications, powers, subtractions,...
The leaves of the process are
* numerals, `C a`, `X` and `monomial a n`, to which we assign degree `0`, `1` and `a` respectively;
* `fvar`s `f`, to which we tautologically assign degree `natDegree f`.
-/

public meta section

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section recursion_lemmas
/-!
### Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree` on (almost) all the leaves of its recursion.
-/

variable {R : Type*}

section semiring
variable [Semiring R]

/-
**Mathlib.Tactic.ComputeDegree.natDegree_C_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.ComputeDegree`。
形式化陈述：natDegree_C_le (a : R) : natDegree (C a) <= 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
/-
**Mathlib.Tactic.ComputeDegree.natDegree_natCast_le** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.ComputeDegree`。
形式化陈述：natDegree_natCast_le (n : Nat) : natDegree (n : R[X]) <= 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_natCast`：natDegree_natCast (n : Nat) : natDegree (n
 : R[X]) = 0
-/
theorem natDegree_natCast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_natCast _).le
/-
**Mathlib.Tactic.ComputeDegree.natDegree_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.ComputeDegree`。
形式化陈述：natDegree_zero_le : natDegree (0 : R[X]) <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
-/
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
/-
**Mathlib.Tactic.ComputeDegree.natDegree_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.ComputeDegree`。
形式化陈述：natDegree_one_le : natDegree (1 : R[X]) <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
-/
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le
/-
**Mathlib.Tactic.ComputeDegree.coeff_add_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.ComputeDegree`。
形式化陈述：coeff_add_of_eq {n : Nat} {a b : R} {f g : R[X]} (h_add_left : f.coeff n =
 a) (h_add_right : g.coeff n = b) : (f + g).coeff n = a + b
参数：h_add_left : f.coeff n = a；h_add_right : g.coeff n = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
-/
theorem coeff_add_of_eq {n : ℕ} {a b : R} {f g : R[X]}
    (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_›; apply coeff_add
/-
**Mathlib.Tactic.ComputeDegree.coeff_mul_add_of_le_natDegree_of_eq_ite** 是 Mathl
ib 中的一个定理，位于命名空间 `Mathlib.Tactic.ComputeDegree`。
形式化陈述：coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : Nat} {a b : R} {f g : R
[X]} (h_mul_left : natDegree f <= df) (h_mul_right : natDegree g <= dg) (h_mul_l
eft : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg <= d) : (f *
 g).coeff d = if d = df + dg then a * b else 0
参数：h_mul_left : natDegree f <= df；h_mul_right : natDegree g <= dg；h_mul_left : f
.coeff df = a；h_mul_right : g.coeff dg = b；ddf : df + dg <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_mul_add_eq_of_natDegree_le`：coeff_mul_add_eq_of_natDegr
ee_le {df dg : Nat} {f g : R[X]} (hdf : natDegree f <= df) (hdg : natDegree g <=
 dg) : (f * g).coeff (df + dg) = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.natDegree_mul_le_of_le`：natDegree_mul_le_of_le (hp : natDegre
e p <= m) (hg : natDegree q <= n) : natDegree (p * q) <= m + n
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
-/
theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : ℕ} {a b : R} {f g : R[X]}
    (h_mul_left : natDegree f ≤ df) (h_mul_right : natDegree g ≤ dg)
    (h_mul_left : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg ≤ d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_eq_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h
/-
**Mathlib.Tactic.ComputeDegree.coeff_pow_of_natDegree_le_of_eq_ite'** 是 Mathlib 
中的一个定理，位于命名空间 `Mathlib.Tactic.ComputeDegree`。
形式化陈述：coeff_pow_of_natDegree_le_of_eq_ite' {m n o : Nat} {a : R} {p : R[X]} (h_p
ow : natDegree p <= n) (h_exp : m * n <= o) (h_pow_bas : coeff p n = a) : coeff 
(p ^ m) o = if o = m * n then a ^ m else 0
参数：h_pow : natDegree p <= n；h_exp : m * n <= o；h_pow_bas : coeff p n = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_pow_of_natDegree_le`：coeff_pow_of_natDegree_le (pn : p.
natDegree <= n) : (p ^ m).coeff (m * n) = p.coeff n ^ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.natDegree_pow_le_of_le`：natDegree_pow_le_of_le (n : Nat) (hp 
: natDegree p <= m) : natDegree (p ^ n) <= n * m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
-/
theorem coeff_pow_of_natDegree_le_of_eq_ite' {m n o : ℕ} {a : R} {p : R[X]}
    (h_pow : natDegree p ≤ n) (h_exp : m * n ≤ o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

section SMul

variable {S : Type*} [SMulZeroClass S R] {n : ℕ} {a : S} {f : R[X]}

/-
**Mathlib.Tactic.ComputeDegree.natDegree_smul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间
 `Mathlib.Tactic.ComputeDegree`。
形式化陈述：natDegree_smul_le_of_le (hf : natDegree f <= n) : natDegree (a • f) <= n
参数：hf : natDegree f <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_smul_le`：natDegree_smul_le {S : Type*} [SMulZeroCla
ss S R] (a : S) (p : R[X]) : natDegree (a • p) <= natDegree p
-/
theorem natDegree_smul_le_of_le (hf : natDegree f ≤ n) :
    natDegree (a • f) ≤ n :=
  (natDegree_smul_le a f).trans hf
/-
**Mathlib.Tactic.ComputeDegree.degree_smul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.ComputeDegree`。
形式化陈述：degree_smul_le_of_le (hf : degree f <= n) : degree (a • f) <= n
参数：hf : degree f <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
-/
theorem degree_smul_le_of_le (hf : degree f ≤ n) :
    degree (a • f) ≤ n :=
  (degree_smul_le a f).trans hf
/-
**Mathlib.Tactic.ComputeDegree.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.ComputeDegree`。
形式化陈述：coeff_smul : (a • f).coeff n = a • f.coeff n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_smul : (a • f).coeff n = a • f.coeff n := rfl

end SMul

section congr_lemmas

/-- The following two lemmas should be viewed as a hand-made "congr"-lemmas.
They achieve the following goals.
* They introduce *two* fresh metavariables replacing the given one `deg`,
  one for the `natDegree ≤` computation and one for the `coeff =` computation.
  This helps `compute_degree`, since it does not "pre-estimate" the degree,
  but it "picks it up along the way".
* They split checking the inequality `coeff p n ≠ 0` into the task of
  finding a value `c` for the `coeff` and then
  proving that this value is non-zero by `coeff_ne_zero`.
-/
/-
**Mathlib.Tactic.ComputeDegree.natDegree_eq_of_le_of_coeff_ne_zero'** 是 Mathlib 
中的一个定理，位于命名空间 `Mathlib.Tactic.ComputeDegree`。
形式化陈述：natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : Nat} {c : R} {p : R[X]} (h
_natDeg_le : natDegree p <= m) (coeff_eq : coeff p o = c) (coeff_ne_zero : c != 
0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) : natDegree p = deg
参数：h_natDeg_le : natDegree p <= m；coeff_eq : coeff p o = c；coeff_ne_zero : c != 
0；deg_eq_deg : m = deg；coeff_eq_deg : o = deg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n

--- 原说明 ---
The following two lemmas should be viewed as a hand-made "congr"-lemmas.
They achieve the following goals.
* They introduce *two* fresh metavariables replacing the given one `deg`,
  one for the `natDegree ≤` computation and one for the `coeff =` computation.
  This helps `compute_degree`, since it does not "pre-estimate" the degree,
  but it "picks it up along the way".
* They split checking the inequality `coeff p n ≠ 0` into the task of
  finding a value `c` for the `coeff` and then
  proving that this value is non-zero by `coeff_ne_zero`.
-/
theorem natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : ℕ} {c : R} {p : R[X]}
    (h_natDeg_le : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    natDegree p = deg := by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›
/-
**Mathlib.Tactic.ComputeDegree.degree_eq_of_le_of_coeff_ne_zero'** 是 Mathlib 中的一
个定理，位于命名空间 `Mathlib.Tactic.ComputeDegree`。
形式化陈述：degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot Nat} {c : R} {p : R[X
]} (h_deg_le : degree p <= m) (coeff_eq : coeff p (WithBot.unbotD 0 deg) = c) (c
oeff_ne_zero : c != 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) : degree 
p = deg
参数：h_deg_le : degree p <= m；coeff_eq : coeff p (WithBot.unbotD 0 deg) = c；coeff_
ne_zero : c != 0；deg_eq_deg : m = deg；coeff_eq_deg : o = deg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.ne_bot_iff_exists`：ne_bot_iff_exists {x : WithBot α} : x != ⊥ ↔ 
exists a : α, ↑a = x
· 使用定理 `Polynomial.degree_eq_of_le_of_coeff_ne_zero`：degree_eq_of_le_of_coeff_ne
_zero (pn : p.degree <= n) (p1 : p.coeff n != 0) : p.degree = n
-/
theorem degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot ℕ} {c : R} {p : R[X]}
    (h_deg_le : degree p ≤ m) (coeff_eq : coeff p (WithBot.unbotD 0 deg) = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

variable {m n : ℕ} {f : R[X]} {r : R}
/-
**Mathlib.Tactic.ComputeDegree.coeff_congr_lhs** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.ComputeDegree`。
形式化陈述：coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n 
= r
参数：h : coeff f m = r；natDeg_eq_coeff : m = n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r :=
  natDeg_eq_coeff ▸ h
/-
**Mathlib.Tactic.ComputeDegree.coeff_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.ComputeDegree`。
形式化陈述：coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r 
= s) : coeff f n = s
参数：h : coeff f m = r；natDeg_eq_coeff : m = n；rs : r = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
    coeff f n = s :=
  natDeg_eq_coeff ▸ rs ▸ h

end congr_lemmas

end semiring

section ring
variable [Ring R]

/-
**Mathlib.Tactic.ComputeDegree.natDegree_intCast_le** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.ComputeDegree`。
形式化陈述：natDegree_intCast_le (n : Int) : natDegree (n : R[X]) <= 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_intCast`：natDegree_intCast (n : Int) : natDegree (n
 : R[X]) = 0
-/
theorem natDegree_intCast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_intCast _).le
/-
**Mathlib.Tactic.ComputeDegree.coeff_sub_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.ComputeDegree`。
形式化陈述：coeff_sub_of_eq {n : Nat} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg 
: g.coeff n = b) : (f - g).coeff n = a - b
参数：hf : f.coeff n = a；hg : g.coeff n = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
-/
theorem coeff_sub_of_eq {n : ℕ} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply coeff_sub
/-
**Mathlib.Tactic.ComputeDegree.coeff_intCast_ite** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.ComputeDegree`。
形式化陈述：coeff_intCast_ite {n : Nat} {a : Int} : (Int.cast a : R[X]).coeff n = ite 
(n = 0) a 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_intCast_ite {n : ℕ} {a : ℤ} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

end ring

end recursion_lemmas

section Tactic

open Lean Elab Tactic Meta Expr

/-- `twoHeadsArgs e` takes an `Expr`ession `e` as input and recurses into `e` to make sure
that `e` looks like `lhs ≤ rhs`, `lhs < rhs` or `lhs = rhs` and that `lhs` is one of
`natDegree f, degree f, coeff f d`.
It returns
* the function being applied on the LHS (`natDegree`, `degree`, or `coeff`),
  or else `.anonymous` if it's none of these;
* the name of the relation (`Eq`, `LE.le` or `LT.lt`), or else `.anonymous` if it's none of these;
* either
  * `.inl zero`, `.inl one`, or `.inl many` if the polynomial in a numeral;
  * or `.inr` of the head symbol of `f`;
  * or `.inl .anonymous` if inapplicable;
* if it exists, whether the `rhs` is a metavariable;
* if the LHS is `coeff f d`, whether `d` is a metavariable.

This is all the data needed to figure out whether `compute_degree` can make progress on `e`
and, if so, which lemma it should apply.

Sample outputs:
* `natDegree (f + g) ≤ d => (natDegree, LE.le, HAdd.hAdd, d.isMVar, none)` (similarly for `=`);
* `degree (f * g) = d => (degree, Eq, HMul.hMul, d.isMVar, none)` (similarly for `≤`);
* `coeff (1 : ℕ[X]) c = x => (coeff, Eq, one, x.isMVar, c.isMVar)` (no `≤` option!).
-/
/-
**Mathlib.Tactic.ComputeDegree.twoHeadsArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.ComputeDegree`。
形式化陈述：twoHeadsArgs (e : Expr) : Name × Name × (Name oplus Name) × List Bool
参数：e : Expr。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Lean.Name.instLawfulBEq`：LawfulBEq Name

--- 原说明 ---
`twoHeadsArgs e` takes an `Expr`ession `e` as input and recurses into `e` to mak
e sure
that `e` looks like `lhs ≤ rhs`, `lhs < rhs` or `lhs = rhs` and that `lhs` is on
e of
`natDegree f, degree f, coeff f d`.
It returns
* the function being applied on the LHS (`natDegree`, `degree`, or `coeff`),
  or else `.anonymous` if it's none of these;
* the name of the relation (`Eq`, `LE.le` or `LT.lt`), or else `.anonymous` if i
t's none of these;
* either
  * `.inl zero`, `.inl one`, or `.inl many` if the polynomial in a numeral;
  * or `.inr` of the head symbol of `f`;
  * or `.inl .anonymous` if inapplicable;
* if it exists, whether the `rhs` is a metavariable;
* if the LHS is `coeff f d`, whether `d` is a metavariable.

This is all the data needed to figure out whether `compute_degree` can make prog
ress on `e`
and, if so, which lemma it should apply.

Sample outputs:
* `natDegree (f + g) ≤ d => (natDegree, LE.le, HAdd.hAdd, d.isMVar, none)` (simi
larly for `=`);
* `degree (f * g) = d => (degree, Eq, HMul.hMul, d.isMVar, none)` (similarly for
 `≤`);
* `coeff (1 : ℕ[X]) c = x => (coeff, Eq, one, x.isMVar, c.isMVar)` (no `≤` optio
n!).
-/
def twoHeadsArgs (e : Expr) : Name × Name × (Name ⊕ Name) × List Bool := Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs])       => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LT.lt, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous, [])
  let (ndeg_or_deg_or_coeff, pol, and?) ← match lhs.getAppFnArgs with
    | (na@``Polynomial.natDegree, #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.degree,    #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.coeff,     #[_, _, pol, c])  => (na, pol, [rhs.isMVar, c.isMVar])
    | _ => return (.anonymous, eq_or_le, .inl .anonymous, [])
  let head := match pol.numeral? with
    -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
    | some 0 => .inl `zero
    | some 1 => .inl `one
    | some _ => .inl `many
    | none => match pol.getAppFnArgs with
      | (``DFunLike.coe, #[_, _, _, _, polFun, _]) =>
        let na := polFun.getAppFn.constName
        if na ∈ [``Polynomial.monomial, ``Polynomial.C] then
          .inr na
        else
          .inl .anonymous
      | (na, _) => .inr na
  (ndeg_or_deg_or_coeff, eq_or_le, head, and?)

/--
`getCongrLemma (lhs_name, rel_name, Mvars?)` returns the name of a lemma that preprocesses
one of the seven targets
*  `natDegree f ≤ d`;
*  `natDegree f < d`;
*  `natDegree f = d`;
*  `degree f ≤ d`;
*  `degree f < d`;
*  `degree f = d`.
*  `coeff f d = r`.

The end goals are of the form
* `natDegree f ≤ ?_`, `degree f ≤ ?_`, `coeff f ?_ = ?_`, or `?_ < d` with fresh metavariables;
* `coeff f m ≠ s` with `m, s` not necessarily metavariables;
* several equalities/inequalities between expressions and assignments for metavariables.

`getCongrLemma` gets called at the very beginning of `compute_degree` and whenever an intermediate
goal does not have the right metavariables.
Note that the side-goals of the congruence lemma are neither of the form `natDegree f = d` nor
of the form `degree f = d`.

`getCongrLemma` admits an optional "debug" flag: `getCongrLemma data true` prints the name of
the congruence lemma that it returns.
-/
/-
**Mathlib.Tactic.ComputeDegree.getCongrLemma** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.ComputeDegree`。
形式化陈述：getCongrLemma (twoH : Name × Name × List Bool) (debug : Bool
参数：twoH : Name × Name × List Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`getCongrLemma (lhs_name, rel_name, Mvars?)` returns the name of a lemma that pr
eprocesses
one of the seven targets
*  `natDegree f ≤ d`;
*  `natDegree f < d`;
*  `natDegree f = d`;
*  `degree f ≤ d`;
*  `degree f < d`;
*  `degree f = d`.
*  `coeff f d = r`.

The end goals are of the form
* `natDegree f ≤ ?_`, `degree f ≤ ?_`, `coeff f ?_ = ?_`, or `?_ < d` with fresh
 metavariables;
* `coeff f m ≠ s` with `m, s` not necessarily metavariables;
* several equalities/inequalities between expressions and assignments for metava
riables.

`getCongrLemma` gets called at the very beginning of `compute_degree` and whenev
er an intermediate
goal does not have the right metavariables.
Note that the side-goals of the congruence lemma are neither of the form `natDeg
ree f = d` nor
of the form `degree f = d`.

`getCongrLemma` admits an optional "debug" flag: `getCongrLemma data true` print
s the name of
the congruence lemma that it returns.
-/
def getCongrLemma (twoH : Name × Name × List Bool) (debug : Bool := false) : Name :=
  let nam := match twoH with
    | (_,           ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
    | (_,           ``LT.lt, [rhs]) => if rhs then ``id else ``lt_of_le_of_lt
    | (``natDegree, ``Eq, [rhs])    => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree,    ``Eq, [rhs])    => if rhs then ``id else ``degree_eq_of_le_of_coeff_ne_zero'
    | (``coeff,     ``Eq, [rhs, c]) =>
      match rhs, c with
      | false, false => ``coeff_congr
      | false, true  => ``Eq.trans
      | true, false  => ``coeff_congr_lhs
      | true, true   => ``id
    | _ => ``id
  if debug then
    let last := nam.lastComponentAsString
    let natr := if last == "trans" then nam.toString else last
    dbg_trace f!"congr lemma: '{natr}'"
    nam
  else
    nam

/--
`dispatchLemma twoH` takes its input `twoH` from the output of `twoHeadsArgs`.

Using the information contained in `twoH`, it decides which lemma is the most appropriate.

`dispatchLemma` is essentially the main dictionary for `compute_degree`.
-/
--  Internally, `dispatchLemma` produces 3 names: these are the lemmas that are appropriate
--  for goals of the form `natDegree f ≤ d`, `degree f ≤ d`, `coeff f d = a`, in this order.
/-
**Mathlib.Tactic.ComputeDegree.dispatchLemma** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.ComputeDegree`。
形式化陈述：dispatchLemma (twoH : Name × Name × (Name oplus Name) × List Bool) (debug 
: Bool
参数：twoH : Name × Name × (Name oplus Name) × List Bool。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEqBool`：LawfulBEq Bool
-/
def dispatchLemma
    (twoH : Name × Name × (Name ⊕ Name) × List Bool) (debug : Bool := false) : Name :=
  match twoH with
    | (.anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
    | (_, .anonymous, _) => ``id -- `twoH` gave default value, so we do nothing
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n  {head}"
      -- if there is some non-metavariable on the way, we "congr" it away
      if false ∈ bools then getCongrLemma (na1, na2, bools) debug
      else
      -- otherwise, we select either the first, second or third element of the triple in `nas` below
      let π (natDegLE : Name) (degLE : Name) (coeff : Name) : Name := Id.run do
        let lem := match na1, na2 with
          | ``natDegree, ``LE.le => natDegLE
          | ``degree, ``LE.le => degLE
          | ``coeff, ``Eq => coeff
          | _, ``LE.le => ``le_rfl
          | _, _ => ``rfl
        if debug then
          dbg_trace f!"{lem.lastComponentAsString}\n{msg}"
        lem
      match head with
        | .inl `zero => π ``natDegree_zero_le ``degree_zero_le ``coeff_zero
        | .inl `one  => π ``natDegree_one_le ``degree_one_le ``coeff_one
        | .inl `many => π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inl .anonymous => π ``le_rfl ``le_rfl ``rfl
        | .inr ``HAdd.hAdd =>
          π ``natDegree_add_le_of_le ``degree_add_le_of_le ``coeff_add_of_eq
        | .inr ``HSub.hSub =>
          π ``natDegree_sub_le_of_le ``degree_sub_le_of_le ``coeff_sub_of_eq
        | .inr ``HMul.hMul =>
          π ``natDegree_mul_le_of_le ``degree_mul_le_of_le ``coeff_mul_add_of_le_natDegree_of_eq_ite
        | .inr ``HPow.hPow =>
          π ``natDegree_pow_le_of_le ``degree_pow_le_of_le ``coeff_pow_of_natDegree_le_of_eq_ite'
        | .inr ``Neg.neg =>
          π ``natDegree_neg_le_of_le ``degree_neg_le_of_le ``coeff_neg
        | .inr ``Polynomial.X =>
          π ``natDegree_X_le ``degree_X_le ``coeff_X
        | .inr ``Nat.cast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``NatCast.natCast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``Int.cast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``IntCast.intCast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``Polynomial.monomial =>
          π ``natDegree_monomial_le ``degree_monomial_le ``coeff_monomial
        | .inr ``Polynomial.C =>
          π ``natDegree_C_le ``degree_C_le ``coeff_C
        | .inr ``HSMul.hSMul =>
          π ``natDegree_smul_le_of_le ``degree_smul_le_of_le ``coeff_smul
        | _ => π ``le_rfl ``le_rfl ``rfl

/-- `tryRfl mvs` takes as input a list of `MVarId`s, scans them partitioning them into two
lists: the goals containing some metavariables and the goals not containing any metavariable.

If a goal containing a metavariable has the form `?_ = x`, `x = ?_`, where `?_` is a metavariable
and `x` is an expression that does not involve metavariables, then it closes this goal using `rfl`,
effectively assigning the metavariable to `x`.

If a goal does not contain metavariables, it tries `rfl` on it.

It returns the list of `MVarId`s, beginning with the ones that initially involved (`Expr`)
metavariables followed by the rest.
-/
/-
**Mathlib.Tactic.ComputeDegree.tryRfl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
ComputeDegree`。
形式化陈述：tryRfl (mvs : List MVarId) : MetaM (List MVarId)
参数：mvs : List MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tryRfl mvs` takes as input a list of `MVarId`s, scans them partitioning them in
to two
lists: the goals containing some metavariables and the goals not containing any 
metavariable.

If a goal containing a metavariable has the form `?_ = x`, `x = ?_`, where `?_` 
is a metavariable
and `x` is an expression that does not involve metavariables, then it closes thi
s goal using `rfl`,
effectively assigning the metavariable to `x`.

If a goal does not contain metavariables, it tries `rfl` on it.

It returns the list of `MVarId`s, beginning with the ones that initially involve
d (`Expr`)
metavariables followed by the rest.
-/
def tryRfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (yesMV, noMV) ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
  let tried_rfl ← noMV.mapM fun g => g.applyConst ``rfl <|> return [g]
  let assignable ← yesMV.mapM fun g => do
    let tgt ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.flatten ++ tried_rfl.flatten)

@[deprecated (since := "2026-05-27")] alias try_rfl := tryRfl

/--
`splitApply mvs static` takes two lists of `MVarId`s.  The first list, `mvs`,
corresponds to goals that are potentially within the scope of `compute_degree`:
namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f d = r`.

`splitApply` determines which of these goals are actually within the scope, it applies the relevant
lemma and returns two lists: the left-over goals of all the applications, followed by the
concatenation of the previous `static` list, followed by the newly discovered goals outside of the
scope of `compute_degree`. -/
/-
**Mathlib.Tactic.ComputeDegree.splitApply** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.ComputeDegree`。
形式化陈述：splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarI
d))
参数：mvs static : List MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`splitApply mvs static` takes two lists of `MVarId`s.  The first list, `mvs`,
corresponds to goals that are potentially within the scope of `compute_degree`:
namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f d
 = r`.

`splitApply` determines which of these goals are actually within the scope, it a
pplies the relevant
lemma and returns two lists: the left-over goals of all the applications, follow
ed by the
concatenation of the previous `static` list, followed by the newly discovered go
als outside of the
scope of `compute_degree`.
-/
def splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
  let (can_progress, curr_static) ← mvs.partitionM fun mv => do
    return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
  let progress ← can_progress.mapM fun mv => do
    let lem := dispatchLemma <| twoHeadsArgs (← mv.getType'')
    mv.applyConst <| lem
  return (progress.flatten, static ++ curr_static)

/-- `miscomputedDegree? deg false_goals` takes as input
* an `Expr`ession `deg`, representing the degree of a polynomial
  (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`);
* a list of `MVarId`s `false_goals`.

Although inconsequential for this function, the list of goals `false_goals` reduces to `False`
if `norm_num`med.
`miscomputedDegree?` extracts error information from goals of the form
* `a ≠ b`, assuming it comes from `⊢ coeff_of_given_degree ≠ 0` —
  reducing to `False` means that the coefficient that was supposed to vanish, does not;
* `a ≤ b`, assuming it comes from `⊢ degree_of_subterm ≤ degree_of_polynomial` —
  reducing to `False` means that there is a term of degree that is apparently too large;
* `a = b`, assuming it comes from `⊢ computed_degree ≤ given_degree` —
  reducing to `False` means that there is a term of degree that is apparently too large.

The cases `a ≠ b` and `a = b` are not a perfect match with the top coefficient:
reducing to `False` is not exactly correlated with a coefficient being non-zero.
It does mean that `compute_degree` reduced the initial goal to an unprovable state
(unless there was already a contradiction in the initial hypotheses!), but it is indicative that
there may be some problem.
-/
/-
**Mathlib.Tactic.ComputeDegree.miscomputedDegree** 是 Mathlib 中的一个定义，位于命名空间 `Math
lib.Tactic.ComputeDegree`。
形式化陈述：miscomputedDegree? (deg : Expr) : List Expr -> List MessageData | tgt::tgt
s => let rest
参数：deg : Expr。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`miscomputedDegree? deg false_goals` takes as input
* an `Expr`ession `deg`, representing the degree of a polynomial
  (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`);
* a list of `MVarId`s `false_goals`.

Although inconsequential for this function, the list of goals `false_goals` redu
ces to `False`
if `norm_num`med.
`miscomputedDegree?` extracts error information from goals of the form
* `a ≠ b`, assuming it comes from `⊢ coeff_of_given_degree ≠ 0` —
  reducing to `False` means that the coefficient that was supposed to vanish, do
es not;
* `a ≤ b`, assuming it comes from `⊢ degree_of_subterm ≤ degree_of_polynomial` —
  reducing to `False` means that there is a term of degree that is apparently to
o large;
* `a = b`, assuming it comes from `⊢ computed_degree ≤ given_degree` —
  reducing to `False` means that there is a term of degree that is apparently to
o large.

The cases `a ≠ b` and `a = b` are not a perfect match with the top coefficient:
reducing to `False` is not exactly correlated with a coefficient being non-zero.
It does mean that `compute_degree` reduced the initial goal to an unprovable sta
te
(unless there was already a contradiction in the initial hypotheses!), but it is
 indicative that
there may be some problem.
-/
def miscomputedDegree? (deg : Expr) : List Expr → List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq? then
      m!"* there may be a term of naïve degree {lhs}" :: rest
    else rest
  | [] => []

/--
`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.
-/
syntax (name := computeDegree) "compute_degree" "!"? : tactic

initialize registerTraceClass `Tactic.compute_degree

@[tactic_alt computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)

elab_rules : tactic | `(tactic| compute_degree $[!%$bang]?) => focus <| withMainContext do
  let goal ← getMainGoal
  let gt ← goal.getType''
  let deg? := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let twoH := twoHeadsArgs gt
  match twoH with
    | (_, .anonymous, _) => throwError m!"'compute_degree' inapplicable. \
        The goal{indentD gt}\nis expected to be '≤', '<' or '='."
    | (.anonymous, _, _) => throwError m!"'compute_degree' inapplicable. \
        The LHS must be an application of 'natDegree', 'degree', or 'coeff'."
    | _ =>
      let lem := dispatchLemma twoH
      trace[Tactic.compute_degree]
        f!"'compute_degree' first applies lemma '{lem.lastComponentAsString}'"
      let mut (gls, static) := (← goal.applyConst lem, [])
      while gls != [] do (gls, static) ← splitApply gls static
      let rfled ← tryRfl static
      setGoals rfled
      --  simplify the left-hand sides, since this is where the degree computations leave
      --  expressions such as `max (0 * 1) (max (1 + 0 + 3 * 4) (7 * 0))`
      evalTactic
        (← `(tactic| try any_goals conv_lhs =>
                       (simp +decide only [Nat.cast_withBot]; norm_num)))
      if bang.isSome then
        let mut false_goals : Array MVarId := #[]
        let mut new_goals : Array MVarId := #[]
        for g in ← getGoals do
          let gs' ← run g do evalTactic (←
            `(tactic| try (any_goals norm_num <;> norm_cast <;> try assumption)))
          new_goals := new_goals ++ gs'.toArray
          if ← gs'.anyM fun g' => g'.withContext do return (← g'.getType'').isConstOf ``False then
            false_goals := false_goals.push g
        setGoals new_goals.toList
        if let some deg := deg? then
          let errors := miscomputedDegree? deg (← false_goals.mapM (MVarId.getType'' ·)).toList
          unless errors.isEmpty do
            throwError Lean.MessageData.joinSep
              (m!"The given degree is '{deg}'.  However,\n" :: errors) "\n"

/-- `monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.
-/
macro (name := monicityMacro) "monicity" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree))

@[tactic_alt monicityMacro]
macro "monicity!" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree!))

end Tactic

end Mathlib.Tactic.ComputeDegree

/-!
We register `compute_degree` with the `hint` tactic.
-/
register_hint 1000 compute_degree
register_try?_tactic (priority := 1000) compute_degree

