/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Michael Stoll
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# L-series

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

* `LSeries.term f s n` is the `n`th term of the L-series of the sequence `f` at `s : ℂ`.
  We define it to be zero when `n = 0`.

* `LSeries f` is the L-series with a given sequence `f` as its coefficients. This is not the
  analytic continuation (which does not necessarily exist), just the sum of the infinite series if
  it exists and zero otherwise.

* `LSeriesSummable f s` indicates that the L-series of `f` converges at `s : ℂ`.

* `LSeriesHasSum f s a` expresses that the L-series of `f` converges (absolutely) at `s : ℂ` to
  `a : ℂ`.

## Main Results

* `LSeriesSummable_of_isBigO_rpow`: the `LSeries` of a sequence `f` such that `f = O(n^(x-1))`
  converges at `s` when `x < s.re`.

* `LSeriesSummable.isBigO_rpow`: if the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`.

## Notation

We introduce `L` as notation for `LSeries` and `↗f` as notation for `fun n : ℕ ↦ (f n : ℂ)`,
both scoped to `LSeries.notation`. The latter makes it convenient to use arithmetic functions
or Dirichlet characters (or anything that coerces to a function `N → R`, where `ℕ` coerces
to `N` and `R` coerces to `ℂ`) as arguments to `LSeries` etc.

## Reference

For some background on the design decisions made when implementing L-series in Mathlib
(and applications motivating the development), see the paper
[Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
by David Loeffler and Michael Stoll.

## Tags

L-series
-/

@[expose] public section

open Complex

/-!
### The terms of an L-series

We define the `n`th term evaluated at a complex number `s` of the L-series associated
to a sequence `f : ℕ → ℂ`, `LSeries.term f s n`, and provide some basic API.

We set `LSeries.term f s 0 = 0`, and for positive `n`, `LSeries.term f s n = f n / n ^ s`.
-/

namespace LSeries

/-- The `n`th term of the L-series of `f` evaluated at `s`. We set it to zero when `n = 0`. -/
noncomputable
/-
**LSeries.term** 是 Mathlib 中的一个定义，位于命名空间 `LSeries`。
形式化陈述：term (f : Nat -> Complex) (s : Complex) (n : Nat) : Complex
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n / n ^ s
/-
**LSeries.term_def** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_def (f : Nat -> Complex) (s : Complex) (n : Nat) : term f s n = if n 
= 0 then 0 else f n / n ^ s
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma term_def (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term f s n = if n = 0 then 0 else f n / n ^ s :=
  rfl

/-- An alternate spelling of `term_def` for the case `f 0 = 0`. -/
/-
**LSeries.term_def** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_def (f : Nat -> Complex) (s : Complex) (n : Nat) : term f s n = if n 
= 0 then 0 else f n / n ^ s
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate spelling of `term_def` for the case `f 0 = 0`.
-/
lemma term_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]

@[simp]
/-
**LSeries.term_zero** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_zero (f : Nat -> Complex) (s : Complex) : term f s 0 = 0
参数：f : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma term_zero (f : ℕ → ℂ) (s : ℂ) : term f s 0 = 0 := rfl

-- We put `hn` first for convenience, so that we can write `rw [LSeries.term_of_ne_zero hn]` etc.
@[simp]
/-
**LSeries.term_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Nat -> Complex) (s : Complex)
 : term f s n = f n / n ^ s
参数：hn : n != 0；f : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma term_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℂ) (s : ℂ) :
    term f s n = f n / n ^ s :=
  if_neg hn

/--
If `s ≠ 0`, then the `if .. then .. else` construction in `LSeries.term` isn't needed, since
`0 ^ s = 0`.
-/
/-
**LSeries.term_of_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_of_ne_zero' {s : Complex} (hs : s != 0) (f : Nat -> Complex) (n : Nat
) : term f s n = f n / n ^ s
参数：hs : s != 0；f : Nat -> Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_zero`：term_zero (f : Nat -> Complex) (s : Complex) : term f
 s 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s

--- 原说明 ---
If `s ≠ 0`, then the `if .. then .. else` construction in `LSeries.term` isn't n
eeded, since
`0 ^ s = 0`.
-/
lemma term_of_ne_zero' {s : ℂ} (hs : s ≠ 0) (f : ℕ → ℂ) (n : ℕ) :
    term f s n = f n / n ^ s := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero, Nat.cast_zero, zero_cpow hs, div_zero]
  · rw [term_of_ne_zero hn]
/-
**LSeries.term_congr** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_congr {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) (s
 : Complex) (n : Nat) : term f s n = term g s n
参数：h : forall {n}, n != 0 -> f n = g n；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma term_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) (n : ℕ) :
    term f s n = term g s n := by
  rcases eq_or_ne n 0 with hn | hn <;> simp [hn, h]
/-
**LSeries.pow_mul_term_eq** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：pow_mul_term_eq (f : Nat -> Complex) (s : Complex) (n : Nat) : (n + 1) ^ s
 * term f s (n + 1) = f (n + 1)
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_div_assoc'`：mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Complex.natCast_add_one_cpow_ne_zero`：natCast_add_one_cpow_ne_zero (n : 
Nat) (z : Complex) : (n + 1 : Complex) ^ z != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_mul_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (n + 1) ^ s * term f s (n + 1) = f (n + 1) := by
  simp [term, natCast_add_one_cpow_ne_zero n _, mul_div_assoc']
/-
**LSeries.norm_term_eq** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：norm_term_eq (f : Nat -> Complex) (s : Complex) (n : Nat) : ‖term f s n‖ =
 if n = 0 then 0 else ‖f n‖ / n ^ s.re
参数：f : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.norm_div`：∀ (z w : ℂ), ‖z / w‖ = ‖z‖ / ‖w‖
· 使用引理 `Complex.norm_natCast_cpow_of_pos`：norm_natCast_cpow_of_pos {n : Nat} (hn
 : 0 < n) (s : Complex) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma norm_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]
/-
**LSeries.norm_term_le** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：norm_term_le {f g : Nat -> Complex} (s : Complex) {n : Nat} (h : ‖f n‖ <= 
‖g n‖) : ‖term f s n‖ <= ‖term g s n‖
参数：s : Complex；h : ‖f n‖ <= ‖g n‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.norm_term_eq`：norm_term_eq (f : Nat -> Complex) (s : Complex) (n
 : Nat) : ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma norm_term_le {f g : ℕ → ℂ} (s : ℂ) {n : ℕ} (h : ‖f n‖ ≤ ‖g n‖) :
    ‖term f s n‖ ≤ ‖term g s n‖ := by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr
/-
**LSeries.norm_term_le_of_re_le_re** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：norm_term_le_of_re_le_re (f : Nat -> Complex) {s s' : Complex} (h : s.re <
= s'.re) (n : Nat) : ‖term f s' n‖ <= ‖term f s n‖
参数：f : Nat -> Complex；h : s.re <= s'.re；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.norm_term_eq`：norm_term_eq (f : Nat -> Complex) (s : Complex) (n
 : Nat) : ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
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
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma norm_term_le_of_re_le_re (f : ℕ → ℂ) {s s' : ℂ} (h : s.re ≤ s'.re) (n : ℕ) :
    ‖term f s' n‖ ≤ ‖term f s n‖ := by
  simp only [norm_term_eq]
  split
  · next => rfl
  · next hn => gcongr; exact Nat.one_le_cast.mpr <| Nat.one_le_iff_ne_zero.mpr hn

section positivity

open scoped ComplexOrder

/-
**LSeries.term_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_nonneg {a : Nat -> Complex} {n : Nat} (h : 0 <= a n) (x : Real) : 0 <
= term a x n
参数：h : 0 <= a n；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_def`：term_def (f : Nat -> Complex) (s : Complex) (n : Nat) 
: term f s n = if n = 0 then 0 else f n / n ^ s
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Complex.inv_natCast_cpow_ofReal_pos`：inv_natCast_cpow_ofReal_pos {n : Na
t} (hn : n != 0) (x : Real) : 0 < ((n : Complex) ^ (x : Complex))⁻¹
-/
lemma term_nonneg {a : ℕ → ℂ} {n : ℕ} (h : 0 ≤ a n) (x : ℝ) : 0 ≤ term a x n := by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]
/-
**LSeries.term_pos** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_pos {a : Nat -> Complex} {n : Nat} (hn : n != 0) (h : 0 < a n) (x : R
eal) : 0 < term a x n
参数：hn : n != 0；h : 0 < a n；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用引理 `Complex.inv_natCast_cpow_ofReal_pos`：inv_natCast_cpow_ofReal_pos {n : Na
t} (hn : n != 0) (x : Real) : 0 < ((n : Complex) ^ (x : Complex))⁻¹
-/
lemma term_pos {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) (h : 0 < a n) (x : ℝ) : 0 < term a x n := by
  simpa only [term_of_ne_zero hn] using! mul_pos h <| inv_natCast_cpow_ofReal_pos hn x

end positivity

end LSeries

/-!
### Definition of the L-series and related statements

We define `LSeries f s` of `f : ℕ → ℂ` as the sum over `LSeries.term f s`.
We also provide predicates `LSeriesSummable f s` stating that `LSeries f s` is summable
and `LSeriesHasSum f s a` stating that the L-series of `f` is summable at `s` and converges
to `a : ℂ`.
-/

open LSeries

/-- The value of the L-series of the sequence `f` at the point `s`
if it converges absolutely there, and `0` otherwise. -/
noncomputable
/-
**LSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeries (f : Nat -> Complex) (s : Complex) : Complex
参数：f : Nat -> Complex；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n, term f s n

/-- Congruence for `LSeries` with the evaluation variable `s`. -/
/-
**LSeries_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n)
 (s : Complex) : LSeries f s = LSeries g s
参数：h : forall {n}, n != 0 -> f n = g n；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用引理 `LSeries.term_congr`：term_congr {f g : Nat -> Complex} (h : forall {n}, n
 != 0 -> f n = g n) (s : Complex) (n : Nat) : term f s n = term g s n

--- 原说明 ---
Congruence for `LSeries` with the evaluation variable `s`.
-/
lemma LSeries_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) :
    LSeries f s = LSeries g s :=
  tsum_congr <| term_congr h s

/-- An alternate spelling of `LSeries` as `∑' n, f n / n ^ s` for the case `f 0 = 0`. -/
/-
**LSeries_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate spelling of `LSeries` as `∑' n, f n / n ^ s` for the case `f 0 = 0`
.
-/
lemma LSeries_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) :
    LSeries f s = ∑' n, f n / (n ^ s) := by
  simp [LSeries, LSeries.term_def₀ hf, cpow_neg, div_eq_mul_inv]

/-- `LSeriesSummable f s` indicates that the L-series of `f` converges absolutely at `s`. -/
/-
**LSeriesSummable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeriesSummable (f : Nat -> Complex) (s : Complex) : Prop
参数：f : Nat -> Complex；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LSeriesSummable f s` indicates that the L-series of `f` converges absolutely at
 `s`.
-/
def LSeriesSummable (f : ℕ → ℂ) (s : ℂ) : Prop :=
  Summable (term f s)
/-
**LSeriesSummable_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_congr {f g : Nat -> Complex} (s : Complex) (h : forall {n}
, n != 0 -> f n = g n) : LSeriesSummable f s ↔ LSeriesSummable g s
参数：s : Complex；h : forall {n}, n != 0 -> f n = g n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, (∀ (b : 
β), …
· 使用引理 `LSeries.term_congr`：term_congr {f g : Nat -> Complex} (h : forall {n}, n
 != 0 -> f n = g n) (s : Complex) (n : Nat) : term f s n = term g s n
-/
lemma LSeriesSummable_congr {f g : ℕ → ℂ} (s : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  summable_congr <| term_congr h s

open Filter in
/-- If `f` and `g` agree on large `n : ℕ` and the `LSeries` of `f` converges at `s`,
then so does that of `g`. -/
/-
**LSeriesSummable.congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.congr' {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTo
p] g) (hf : LSeriesSummable f s) : LSeriesSummable g s
参数：s : Complex；h : f =ᶠ[atTop] g；hf : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_norm_iff`：summable_norm_iff {α E : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x
 => ‖f …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Filter.sdiff_mem`：sdiff_mem {s t : Set α} (hs : s in f) (ht : tᶜ in f) :
 s \ t in f
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `f` and `g` agree on large `n : ℕ` and the `LSeries` of `f` converges at `s`,
then so does that of `g`.
-/
lemma LSeriesSummable.congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) :
    LSeriesSummable g s := by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
    refine ⟨S \ {0}, sdiff_mem hS <| (Set.finite_singleton 0).compl_mem_cofinite, fun n hn ↦ ?_⟩
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hn
    simp [hn.2, hS' hn.1]
  exact this.symm.mono fun n hn ↦ by simp [hn]

open Filter in
/-- If `f` and `g` agree on large `n : ℕ`, then the `LSeries` of `f` converges at `s`
if and only if that of `g` does. -/
/-
**LSeriesSummable_congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_congr' {f g : Nat -> Complex} (s : Complex) (h : f =ᶠ[atTo
p] g) : LSeriesSummable f s ↔ LSeriesSummable g s
参数：s : Complex；h : f =ᶠ[atTop] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.congr'`：LSeriesSummable.congr' {f g : Nat -> Complex} (s
 : Complex) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) : LSeriesSummable g s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `f` and `g` agree on large `n : ℕ`, then the `LSeries` of `f` converges at `s
`
if and only if that of `g` does.
-/
lemma LSeriesSummable_congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  ⟨fun H ↦ H.congr' s h, fun H ↦ H.congr' s h.symm⟩
/-
**LSeries.eq_zero_of_not_LSeriesSummable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeries.eq_zero_of_not_LSeriesSummable (f : Nat -> Complex) (s : Complex) 
: ¬ LSeriesSummable f s -> LSeries f s = 0
参数：f : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
-/
theorem LSeries.eq_zero_of_not_LSeriesSummable (f : ℕ → ℂ) (s : ℂ) :
    ¬ LSeriesSummable f s → LSeries f s = 0 :=
  tsum_eq_zero_of_not_summable

@[simp]
/-
**LSeriesSummable_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeriesSummable_zero {s : Complex} : LSeriesSummable 0 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeries.term_def`：term_def (f : Nat -> Complex) (s : Complex) (n : Nat) 
: term f s n = if n = 0 then 0 else f n / n ^ s
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem LSeriesSummable_zero {s : ℂ} : LSeriesSummable 0 s := by
  simp [LSeriesSummable, funext (term_def 0 s), summable_zero]

/-- This states that the L-series of the sequence `f` converges absolutely at `s` and that
the value there is `a`. -/
/-
**LSeriesHasSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeriesHasSum (f : Nat -> Complex) (s a : Complex) : Prop
参数：f : Nat -> Complex；s a : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This states that the L-series of the sequence `f` converges absolutely at `s` an
d that
the value there is `a`.
-/
def LSeriesHasSum (f : ℕ → ℂ) (s a : ℂ) : Prop :=
  HasSum (term f s) a
/-
**LSeriesHasSum.LSeriesSummable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.LSeriesSummable {f : Nat -> Complex} {s a : Complex} (h : LS
eriesHasSum f s a) : LSeriesSummable f s
参数：h : LSeriesHasSum f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
-/
lemma LSeriesHasSum.LSeriesSummable {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable
/-
**LSeriesHasSum.LSeries_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.LSeries_eq {f : Nat -> Complex} {s a : Complex} (h : LSeries
HasSum f s a) : LSeries f s = a
参数：h : LSeriesHasSum f s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma LSeriesHasSum.LSeries_eq {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq
/-
**LSeriesSummable.LSeriesHasSum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.LSeriesHasSum {f : Nat -> Complex} {s : Complex} (h : LSer
iesSummable f s) : LSeriesHasSum f s (LSeries f s)
参数：h : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
lemma LSeriesSummable.LSeriesHasSum {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum
/-
**LSeriesHasSum_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum_iff {f : Nat -> Complex} {s a : Complex} : LSeriesHasSum f s
 a ↔ LSeriesSummable f s ∧ LSeries f s = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesHasSum.LSeriesSummable`：LSeriesHasSum.LSeriesSummable {f : Nat ->
 Complex} {s a : Complex} (h : LSeriesHasSum f s a) : LSeriesSummable f s
· 使用引理 `LSeriesHasSum.LSeries_eq`：LSeriesHasSum.LSeries_eq {f : Nat -> Complex} 
{s a : Complex} (h : LSeriesHasSum f s a) : LSeries f s = a
· 使用引理 `LSeriesSummable.LSeriesHasSum`：LSeriesSummable.LSeriesHasSum {f : Nat ->
 Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesHasSum f s (LSeries f
 s)
-/
lemma LSeriesHasSum_iff {f : ℕ → ℂ} {s a : ℂ} :
    LSeriesHasSum f s a ↔ LSeriesSummable f s ∧ LSeries f s = a :=
  ⟨fun H ↦ ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ ↦ H₂ ▸ H₁.LSeriesHasSum⟩
/-
**LSeriesHasSum_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum_congr {f g : Nat -> Complex} (s a : Complex) (h : forall {n}
, n != 0 -> f n = g n) : LSeriesHasSum f s a ↔ LSeriesHasSum g s a
参数：s a : Complex；h : forall {n}, n != 0 -> f n = g n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeriesSummable_congr`：LSeriesSummable_congr {f g : Nat -> Complex} (s :
 Complex) (h : forall {n}, n != 0 -> f n = g n) : LSeriesSummable f s ↔ LSeriesS
ummable g s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma LSeriesHasSum_congr {f g : ℕ → ℂ} (s a : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
    LSeriesHasSum f s a ↔ LSeriesHasSum g s a := by
  simp [LSeriesHasSum_iff, LSeriesSummable_congr s h, LSeries_congr h s]
/-
**LSeriesSummable.of_re_le_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.of_re_le_re {f : Nat -> Complex} {s s' : Complex} (h : s.r
e <= s'.re) (hf : LSeriesSummable f s) : LSeriesSummable f s'
参数：h : s.re <= s'.re；hf : LSeriesSummable f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LSeriesSummable.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeriesSummable f s = Summa
ble (LSeries.term f s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `summable_norm_iff`：summable_norm_iff {α E : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x
 => ‖f …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `LSeries.norm_term_le_of_re_le_re`：norm_term_le_of_re_le_re (f : Nat -> C
omplex) {s s' : Complex} (h : s.re <= s'.re) (n : Nat) : ‖term f s' n‖ <= ‖term 
f s n‖
-/
lemma LSeriesSummable.of_re_le_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re ≤ s'.re)
    (hf : LSeriesSummable f s) : LSeriesSummable f s' := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_le_of_re_le_re f h)
/-
**LSeriesSummable_iff_of_re_eq_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeriesSummable_iff_of_re_eq_re {f : Nat -> Complex} {s s' : Complex} (h :
 s.re = s'.re) : LSeriesSummable f s ↔ LSeriesSummable f s'
参数：h : s.re = s'.re。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.of_re_le_re`：LSeriesSummable.of_re_le_re {f : Nat -> Com
plex} {s s' : Complex} (h : s.re <= s'.re) (hf : LSeriesSummable f s) : LSeriesS
ummable f s'
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem LSeriesSummable_iff_of_re_eq_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re = s'.re) :
    LSeriesSummable f s ↔ LSeriesSummable f s' :=
  ⟨fun H ↦ H.of_re_le_re h.le, fun H ↦ H.of_re_le_re h.symm.le⟩

/-- The indicator function of `{1} ⊆ ℕ` with values in `ℂ`. -/
/-
**LSeries.delta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeries.delta (n : Nat) : Complex
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indicator function of `{1} ⊆ ℕ` with values in `ℂ`.
-/
def LSeries.delta (n : ℕ) : ℂ :=
  if n = 1 then 1 else 0

/-!
### Notation
-/

@[inherit_doc]
scoped[LSeries.notation] notation "L" => LSeries

/-- We introduce notation `↗f` for `f` interpreted as a function `ℕ → ℂ`.

Let `R` be a ring with a coercion to `ℂ`. Then we can write `↗χ` when `χ : DirichletCharacter R`
or `↗f` when `f : ArithmeticFunction R` or simply `f : N → R` with a coercion from `ℕ` to `N`
as an argument to `LSeries`, `LSeriesHasSum`, `LSeriesSummable` etc. -/
scoped[LSeries.notation] notation:max "↗" f:max => fun n : ℕ ↦ (f n : ℂ)

@[inherit_doc]
scoped[LSeries.notation] notation "δ" => delta

/-!
### LSeries of 0 and δ
-/

@[simp]
/-
**LSeries_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_zero : LSeries 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### LSeries of 0 and δ
-/
lemma LSeries_zero : LSeries 0 = 0 := by
  ext
  simp [LSeries, LSeries.term]

section delta

open scoped LSeries.notation

namespace LSeries

open Nat Complex

/-
**LSeries.term_delta** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_delta (s : Complex) (n : Nat) : term δ s n = if n = 1 then 1 else 0
参数：s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
-/
lemma term_delta (s : ℂ) (n : ℕ) : term δ s n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases eq_or_ne n 1 with hn' | hn' <;>
    simp [hn, hn', delta]
/-
**LSeries.mul_delta_eq_smul_delta** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：mul_delta_eq_smul_delta {f : Nat -> Complex} : f * δ = f 1 • δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma mul_delta_eq_smul_delta {f : ℕ → ℂ} : f * δ = f 1 • δ := by
  ext n
  by_cases hn : n = 1 <;>
  simp [hn, delta]
/-
**LSeries.mul_delta** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：mul_delta {f : Nat -> Complex} (h : f 1 = 1) : f * δ = δ
参数：h : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.mul_delta_eq_smul_delta`：mul_delta_eq_smul_delta {f : Nat -> Com
plex} : f * δ = f 1 • δ
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma mul_delta {f : ℕ → ℂ} (h : f 1 = 1) : f * δ = δ := by
  rw [mul_delta_eq_smul_delta, h, one_smul]
/-
**LSeries.delta_mul_eq_smul_delta** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：delta_mul_eq_smul_delta {f : Nat -> Complex} : δ * f = f 1 • δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.mul_delta_eq_smul_delta`：mul_delta_eq_smul_delta {f : Nat -> Com
plex} : f * δ = f 1 • δ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma delta_mul_eq_smul_delta {f : ℕ → ℂ} : δ * f = f 1 • δ :=
  mul_comm δ f ▸ mul_delta_eq_smul_delta
/-
**LSeries.delta_mul** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：delta_mul {f : Nat -> Complex} (h : f 1 = 1) : δ * f = δ
参数：h : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.mul_delta`：mul_delta {f : Nat -> Complex} (h : f 1 = 1) : f * δ 
= δ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma delta_mul {f : ℕ → ℂ} (h : f 1 = 1) : δ * f = δ :=
  mul_comm δ f ▸ mul_delta h

end LSeries

/-- The L-series of `δ` is the constant function `1`. -/
/-
**LSeries_delta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_delta : LSeries δ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_delta`：term_delta (s : Complex) (n : Nat) : term δ s n = if
 n = 1 then 1 else 0
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-series of `δ` is the constant function `1`.
-/
lemma LSeries_delta : LSeries δ = 1 := by
  ext
  simp [LSeries, LSeries.term_delta]

end delta


/-!
### Criteria for and consequences of summability of L-series

We relate summability of L-series with bounds on the coefficients in terms of powers of `n`.
-/

/-- If the `LSeries` of `f` is summable at `s`, then `f n` is bounded in absolute value
by a constant times `n^(re s)`. -/
/-
**LSeriesSummable.le_const_mul_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.le_const_mul_rpow {f : Nat -> Complex} {s : Complex} (h : 
LSeriesSummable f s) : exists C, forall n != 0, ‖f n‖ <= C * n ^ s.re
参数：h : LSeriesSummable f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι
} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_
3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `LSeries.norm_term_eq`：norm_term_eq (f : Nat -> Complex) (s : Complex) (n
 : Nat) : ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re

--- 原说明 ---
If the `LSeries` of `f` is summable at `s`, then `f n` is bounded in absolute va
lue
by a constant times `n^(re s)`.
-/
lemma LSeriesSummable.le_const_mul_rpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ s.re := by
  replace h := h.norm
  use tsum fun n ↦ ‖term f s n‖
  by_contra! ⟨n, hn₀, hn⟩
  have := h.le_tsum n fun _ _ ↦ norm_nonneg _
  rw [norm_term_eq, if_neg hn₀,
    div_le_iff₀ <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

open Filter in
/-- If the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`. -/
/-
**LSeriesSummable.isBigO_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.isBigO_rpow {f : Nat -> Complex} {s : Complex} (h : LSerie
sSummable f s) : f =O[atTop] fun n => (n : Real) ^ s.re
参数：h : LSeriesSummable f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.le_const_mul_rpow`：LSeriesSummable.le_const_mul_rpow {f 
: Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) : exists C, forall n !
= 0, ‖f n‖ <= C * n ^ s…
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0

--- 原说明 ---
If the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`.
-/
lemma LSeriesSummable.isBigO_rpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    f =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
  refine Asymptotics.IsBigO.of_bound C <| eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  convert! hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg n.cast_nonneg, abs_of_nonneg n.cast_nonneg]

/-- If `f n` is bounded in absolute value by a constant times `n^(x-1)` and `re s > x`,
then the `LSeries` of `f` is summable at `s`. -/
/-
**LSeriesSummable_of_le_const_mul_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_of_le_const_mul_rpow {f : Nat -> Complex} {x : Real} {s : 
Complex} (hs : x < s.re) (h : exists C, forall n != 0, ‖f n‖ <= C * n ^ (x - 1))
 : LSeriesSummable f s
参数：hs : x < s.re；h : exists C, forall n != 0, ‖f n‖ <= C * n ^ (x - 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
If `f n` is bounded in absolute value by a constant times `n^(x-1)` and `re s > 
x`,
then the `LSeries` of `f` is summable at `s`.
-/
lemma LSeriesSummable_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ} (hs : x < s.re)
    (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
  have hC₀ : 0 ≤ C := (norm_nonneg <| f 1).trans <| by simpa using hC 1 one_ne_zero
  have hsum : Summable fun n : ℕ ↦ ‖(C : ℂ) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
    refine Summable.mul_left _ <|
      Summable.of_norm_bounded_eventually_nat (g := fun n ↦ (n : ℝ) ^ (-s.re + x - 1)) ?_ ?_
    · simpa
    · simp only [norm_norm, Filter.eventually_atTop]
      refine ⟨1, fun n hn ↦ le_of_eq ?_⟩
      simp only [norm_natCast_cpow_of_pos hn, add_re, sub_re, neg_re, ofReal_re, one_re]
      ring_nf
  refine Summable.of_norm <| hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [term_zero, norm_zero] using norm_nonneg _
  have hn' : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [term_of_ne_zero hn.ne', norm_div, norm_natCast_cpow_of_pos hn, div_le_iff₀ hn',
    norm_real, Real.norm_of_nonneg hC₀, div_eq_mul_inv, mul_assoc,
    ← Real.rpow_neg <| Nat.cast_nonneg _, ← Real.rpow_add <| Nat.cast_pos.mpr hn]
  simpa using hC n <| Nat.pos_iff_ne_zero.mp hn

open Filter Finset Real Nat in
/-- If `f = O(n^(x-1))` and `re s > x`, then the `LSeries` of `f` is summable at `s`. -/
/-
**LSeriesSummable_of_isBigO_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_of_isBigO_rpow {f : Nat -> Complex} {x : Real} {s : Comple
x} (hs : x < s.re) (h : f =O[atTop] fun n => (n : Real) ^ (x - 1)) : LSeriesSumm
able f s
参数：hs : x < s.re；h : f =O[atTop] fun n => (n : Real) ^ (x - 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `LSeriesSummable_of_le_const_mul_rpow`：LSeriesSummable_of_le_const_mul_rp
ow {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re) (h : exists C, 
forall n != 0, ‖f n‖ <= C …
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `f = O(n^(x-1))` and `re s > x`, then the `LSeries` of `f` is summable at `s`
.
-/
lemma LSeriesSummable_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ} (hs : x < s.re)
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
  have hC'₀ : 0 ≤ C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans <| le_max_right ..
  have hCC' : C ≤ C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n hn₀ ↦ ?_⟩
  rcases le_or_gt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : ℝ) ≤ n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs, abs_rpow_of_nonneg hn₀, abs_of_nonneg hn₀]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn₀
    refine (div_le_iff₀ <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
    refine (le_max' _ _ <| mem_insert_of_mem ?_).trans <| le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

/-- If `f` is bounded, then its `LSeries` is summable at `s` when `re s > 1`. -/
/-
**LSeriesSummable_of_bounded_of_one_lt_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeriesSummable_of_bounded_of_one_lt_re {f : Nat -> Complex} {m : Real} (h
 : forall n != 0, ‖f n‖ <= m) {s : Complex} (hs : 1 < s.re) : LSeriesSummable f 
s
参数：h : forall n != 0, ‖f n‖ <= m；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable_of_le_const_mul_rpow`：LSeriesSummable_of_le_const_mul_rp
ow {f : Nat -> Complex} {x : Real} {s : Complex} (hs : x < s.re) (h : exists C, 
forall n != 0, ‖f n‖ <= C …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `f` is bounded, then its `LSeries` is summable at `s` when `re s > 1`.
-/
theorem LSeriesSummable_of_bounded_of_one_lt_re {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, ‖f n‖ ≤ m) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow hs ⟨m, fun n hn ↦ by simp [h n hn]⟩

/-- If `f` is bounded, then its `LSeries` is summable at `s : ℝ` when `s > 1`. -/
/-
**LSeriesSummable_of_bounded_of_one_lt_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LSeriesSummable_of_bounded_of_one_lt_real {f : Nat -> Complex} {m : Real} 
(h : forall n != 0, ‖f n‖ <= m) {s : Real} (hs : 1 < s) : LSeriesSummable f s
参数：h : forall n != 0, ‖f n‖ <= m；hs : 1 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LSeriesSummable_of_bounded_of_one_lt_re`：LSeriesSummable_of_bounded_of_o
ne_lt_re {f : Nat -> Complex} {m : Real} (h : forall n != 0, ‖f n‖ <= m) {s : Co
mplex} (hs : 1 < s.re) : LSer…

--- 原说明 ---
If `f` is bounded, then its `LSeries` is summable at `s : ℝ` when `s > 1`.
-/
theorem LSeriesSummable_of_bounded_of_one_lt_real {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, ‖f n‖ ≤ m) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable f s :=
  LSeriesSummable_of_bounded_of_one_lt_re h <| by simp [hs]
