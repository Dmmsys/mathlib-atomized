/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.RelClasses

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `EuclideanDomain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `Div` and `Mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `Algebra.EuclideanDomain.Basic` for most of the theorems about Euclidean domains,
including Bézout's lemma.

See `Algebra.EuclideanDomain.Instances` for the fact that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well-founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `EuclideanDomain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/

@[expose] public section

universe u

/-- A `EuclideanDomain` is a non-trivial commutative ring with a division and a remainder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a Euclidean domain usually includes a valuation function `R → ℕ`.
  This definition is slightly generalised to include a well-founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation. -/
@[wikidata Q867345]
/-
**EuclideanDomain** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `EuclideanDomain` is a non-trivial commutative ring with a division and a rema
inder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a Euclidean domain usually includes a valuation function `R 
→ ℕ`.
  This definition is slightly generalised to include a well-founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.
-/
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
  /-- A division function (denoted `/`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `%` denotes `remainder`. -/
  protected quotient : R → R → R
  /-- Division by zero should always give zero by convention. -/
  protected quotient_zero : ∀ a, quotient a 0 = 0
  /-- A remainder function (denoted `%`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `/` denotes `quotient`. -/
  protected remainder : R → R → R
  /-- The property that links the quotient and remainder functions.
    This allows us to compute GCDs and LCMs. -/
  protected quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
  /-- A well-founded relation on `R`, satisfying `r (a % b) b`.
    This ensures that the GCD algorithm always terminates. -/
  protected r : R → R → Prop
  /-- The relation `r` must be well-founded.
    This ensures that the GCD algorithm always terminates. -/
  r_wellFounded : WellFounded r
  /-- The relation `r` satisfies `r (a % b) b`. -/
  protected remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
  /-- An additional constraint on `r`. -/
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a

/-
Lean has far more theorems about fields than about Euclidean domains. We thus
lower the priority of `Euclideandomain.toCommRing`, encouraging typeclass inference
to try `Field.toCommRing` first. Without this priority-lowering, typeclass inference
finds the more inefficient path `Field.toEuclideanDomain.toCommRing` by default. This
priority change saves over 500G instructions across mathlib. See
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/We.20need.20to.20talk.20about.20Euclidean.20Domains/near/594655420
-/
-- see Note [lower instance priority]
attribute [instance 100] EuclideanDomain.toCommRing

namespace EuclideanDomain

variable {R : Type u} [EuclideanDomain R]

/-- Abbreviated notation for the well-founded relation `r` in a Euclidean domain. -/
local infixl:50 " ≺ " => EuclideanDomain.r

local instance wellFoundedRelation : WellFoundedRelation R where
  rel := EuclideanDomain.r
  wf := r_wellFounded

/-
**EuclideanDomain.isWellFounded** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanDomain`。
形式化陈述：isWellFounded : IsWellFounded R (· ≺ ·) where wf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.r_wellFounded`：∀ {R : Type u} [self : EuclideanDomain R]
, WellFounded EuclideanDomain.r
-/
instance isWellFounded : IsWellFounded R (· ≺ ·) where
  wf := r_wellFounded

-- see Note [lower instance priority]
/-
**EuclideanDomain.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

-- see Note [lower instance priority]
/-
**EuclideanDomain.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩
/-
**EuclideanDomain.div_add_mod** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_add_mod (a b : R) : b * (a / b) + a % b = a
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.quotient_mul_add_remainder_eq`：∀ {R : Type u} [self : Eu
clideanDomain R] (a b : R),   b * EuclideanDomain.quotient a b + EuclideanDomain
.remainder a b = a
-/
theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _
/-
**EuclideanDomain.mod_add_div** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_add_div (a b : R) : a % b + b * (a / b) = a
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
-/
theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)
/-
**EuclideanDomain.mod_add_div'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_add_div' (m k : R) : m % k + m / k * k = m
参数：m k : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mod_add_div`：mod_add_div (a b : R) : a % b + b * (a / b)
 = a
-/
theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _
/-
**EuclideanDomain.div_add_mod'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_add_mod' (m k : R) : m / k * k + m % k = m
参数：m k : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
-/
theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _
/-
**EuclideanDomain.mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.remainder_lt`：∀ {R : Type u} [self : EuclideanDomain R] 
(a : R) {b : R}, b ≠ 0 → EuclideanDomain.r (EuclideanDomain.remainder a b) b
-/
theorem mod_lt : ∀ (a) {b : R}, b ≠ 0 → a % b ≺ b :=
  EuclideanDomain.remainder_lt
/-
**EuclideanDomain.mul_right_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_right_not_lt {a : R} (b) (h : a != 0) : ¬a * b ≺ b
参数：b；h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mul_left_not_lt`：∀ {R : Type u} [self : EuclideanDomain 
R] (a : R) {b : R}, b ≠ 0 → ¬EuclideanDomain.r (a * b) a
-/
theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h

@[simp]
/-
**EuclideanDomain.mod_zero** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_zero (a : R) : a % 0 = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
-/
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0
/-
**EuclideanDomain.lt_one** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lt_one (a : R) : a ≺ (1 : R) -> a = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `EuclideanDomain.mul_left_not_lt`：∀ {R : Type u} [self : EuclideanDomain 
R] (a : R) {b : R}, b ≠ 0 → ¬EuclideanDomain.r (a * b) a
-/
theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 :=
  haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

@[simp]
/-
**EuclideanDomain.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_zero (a : R) : a / 0 = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.quotient_zero`：∀ {R : Type u} [self : EuclideanDomain R]
 (a : R), EuclideanDomain.quotient a 0 = 0
-/
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a

section

@[elab_as_elim]
/-
**EuclideanDomain.GCD.induction** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain.GCD`。
形式化陈述：∀ {R : Type u} [inst : EuclideanDomain R] {P : R → R → Prop} (a b : R),   
(∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b % a) a → P a b) → P a b
参数：a b : R；∀ (x : R), P 0 x；∀ (a b : R), a ≠ 0 → P (b % a) a → P a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction._unary`：∀ {R : Type u} [inst : EuclideanDo
main R] {P : R → R → Prop},   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b % 
a) a → P a b) → ∀ (_x : (_…
-/
theorem GCD.induction {P : R → R → Prop} (a b : R) (H0 : ∀ x, P 0 x)
    (H1 : ∀ a b, a ≠ 0 → P (b % a) a → P a b) : P a b := by
  classical
  exact if a0 : a = 0 then
    a0.symm ▸ H0 b
  else
    have _ := mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a

end

section GCD

variable [DecidableEq R]

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
/-
**EuclideanDomain.gcd** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd (a b : R) : R
参数：a b : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and f
or
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b`
-/
def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a

@[simp]
/-
**EuclideanDomain.gcd_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_zero_left (a : R) : gcd 0 a = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (a b : R),   EuclideanDomain.gcd a b =     if a0 : a = 0 th
en b     else …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl

/-- An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcdAux` takes in two triples, and from these recursively computes the next triple:
```
xgcdAux (r, s, t) (r', s', t') = xgcdAux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
/-
**EuclideanDomain.xgcdAux** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcdAux (r s t r' s' t' : R) : R × R × R
参数：r s t r' s' t' : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value 
of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`)
, and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t 
* y`).
The function `xgcdAux` takes in two triples, and from these recursively computes
 the next triple:
```
xgcdAux (r, s, t) (r', s', t') = xgcdAux (r' % r, s' - (r' / r) * s, t' - (r' / 
r) * t) (r, s, t)
```
-/
def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r

@[simp]
/-
**EuclideanDomain.xgcd_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcdAux.eq_def`：∀ {R : Type u} [inst : EuclideanDomain R
] [inst_1 : DecidableEq R] (r s t r' s' t' : R),   EuclideanDomain.xgcdAux r s t
 r' s' t' =     if _…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcdAux
  exact if_pos rfl
/-
**EuclideanDomain.xgcdAux_rec** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcdAux_rec {r s t r' s' t' : R} (h : r != 0) : xgcdAux r s t r' s' t' = x
gcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcdAux.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] 
[inst_1 : DecidableEq R] (r s t r' s' t' : R),   EuclideanDomain.xgcdAux r s t r
' s' t' =     if _…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
/-
**EuclideanDomain.xgcd** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcd (x y : R) : R × R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`.
-/
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
/-
**EuclideanDomain.gcdA** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：gcdA (x y : R) : R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `a` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdA (x y : R) : R :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
/-
**EuclideanDomain.gcdB** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：gcdB (x y : R) : R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `b` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdB (x y : R) : R :=
  (xgcd x y).2

@[simp]
/-
**EuclideanDomain.gcdA_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcdA_zero_left {s : R} : gcdA 0 s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [in
st_1 : DecidableEq R] (x y : R),   EuclideanDomain.xgcd x y = (EuclideanDomain.x
gcdAux x 1 0 y …
· 使用定理 `EuclideanDomain.xgcd_zero_left`：xgcd_zero_left {s t r' s' t' : R} : xgcd
Aux 0 s t r' s' t' = (r', s', t')
-/
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]

@[simp]
/-
**EuclideanDomain.gcdB_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcdB_zero_left {s : R} : gcdB 0 s = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [in
st_1 : DecidableEq R] (x y : R),   EuclideanDomain.xgcd x y = (EuclideanDomain.x
gcdAux x 1 0 y …
· 使用定理 `EuclideanDomain.xgcd_zero_left`：xgcd_zero_left {s t r' s' t' : R} : xgcd
Aux 0 s t r' s' t' = (r', s', t')
-/
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]
/-
**EuclideanDomain.xgcd_val** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  rfl

end GCD

section LCM

variable [DecidableEq R]

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
/-
**EuclideanDomain.lcm** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm (x y : R) : R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and f
or
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c`
-/
def lcm (x y : R) : R :=
  x * y / gcd x y

end LCM

end EuclideanDomain

