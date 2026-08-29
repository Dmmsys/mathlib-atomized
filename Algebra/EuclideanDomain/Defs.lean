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
/--
Definition of `EuclideanDomain` / `EuclideanDomain` 的定义

English:
class EuclideanDomain
  parameters: (R : Type u)
  extends: CommRing R, Nontrivial R
  axioms and operations (8):
    - quotient : R -> R -> R
    - quotient_zero : forall a, quotient a 0 = 0
    - remainder : R -> R -> R
    - quotient_mul_add_remainder_eq : forall a b, b * quotient a b + remainder a b = a
    - r : R -> R -> Prop
    - r_wellFounded : WellFounded r
    - remainder_lt : forall (a) {b}, b != 0 -> r (remainder a b) b
    - mul_left_not_lt : forall (a) {b}, b != 0 -> ¬r (a * b) a

中文:
类 欧几里得整环
  参数: (R : 类型u)
  继承: 交换环 R, 非平凡 R
  公理与运算 (8 个):
    - quotient : R -> R -> R
    - quotient_zero : 对任意 a, quotient a 0 = 0
    - remainder : R -> R -> R
    - quotient_mul_add_remainder_eq : 对任意 a b, b * quotient a b + remainder a b = a
    - r : R -> R -> 命题
    - r_wellFounded : 良基 r
    - remainder_lt : 对任意 (a) {b}, b != 0 -> r (remainder a b) b
    - mul_left_not_lt : 对任意 (a) {b}, b != 0 -> ¬r (a * b) a
-/
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
  /-- A division function (denoted `/`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `%` denotes `remainder`. -/
  protected quotient : R -> R -> R
  /-- Division by zero should always give zero by convention. -/
  protected quotient_zero : forall a, quotient a 0 = 0
  /-- A remainder function (denoted `%`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `/` denotes `quotient`. -/
  protected remainder : R -> R -> R
  /-- The property that links the quotient and remainder functions.
    This allows us to compute GCDs and LCMs. -/
  protected quotient_mul_add_remainder_eq : forall a b, b * quotient a b + remainder a b = a
  /-- A well-founded relation on `R`, satisfying `r (a % b) b`.
    This ensures that the GCD algorithm always terminates. -/
  protected r : R -> R -> Prop
  /-- The relation `r` must be well-founded.
    This ensures that the GCD algorithm always terminates. -/
  r_wellFounded : WellFounded r
  /-- The relation `r` satisfies `r (a % b) b`. -/
  protected remainder_lt : forall (a) {b}, b != 0 -> r (remainder a b) b
  /-- An additional constraint on `r`. -/
  mul_left_not_lt : forall (a) {b}, b != 0 -> ¬r (a * b) a

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

/--
Instance `isWellFounded` / 实例 `isWellFounded`

English:
instance isWellFounded
  signature: : IsWellFounded R (· ≺ ·) where
  body: r_wellFounded

中文:
实例 isWellFounded
  签名: : 是良基 R (· ≺ ·) where
  定义体: r_wellFounded

Depends on / 依赖: r_wellFounded
-/
instance isWellFounded : IsWellFounded R (· ≺ ·) where
  wf := r_wellFounded

-- see Note [lower instance priority]
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

-- see Note [lower instance priority]
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩

/--
theorem `div_add_mod` / 定理 `div_add_mod`

English:
theorem div_add_mod
  given: (a b : R)
  statement: b * (a / b) + a % b = a
  proof: EuclideanDomain.quotient_mul_add_remainder_eq _ _

中文:
定理 div_add_mod
  条件: (a b : R)
  结论: b * (a / b) + a % b = a
  证明: EuclideanDomain.quotient_mul_add_remainder_eq _ _

Depends on / 依赖: EuclideanDomain, EuclideanDomain.quotient_mul_add_remainder_eq, quotient_mul_add_remainder_eq
-/
theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _

/--
theorem `mod_add_div` / 定理 `mod_add_div`

English:
theorem mod_add_div
  given: (a b : R)
  statement: a % b + b * (a / b) = a
  proof: (add_comm _ _).trans (div_add_mod _ _)

中文:
定理 mod_add_div
  条件: (a b : R)
  结论: a % b + b * (a / b) = a
  证明: (add_comm _ _).trans (div_add_mod _ _)

Depends on / 依赖: add_comm, div_add_mod
-/
theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)

/--
theorem `mod_add_div'` / 定理 `mod_add_div'`

English:
theorem mod_add_div'
  given: (m k : R)
  statement: m % k + m / k * k = m
  proof: by
  rw [mul_comm]
  exact mod_add_div _ _

中文:
定理 mod_add_div'
  条件: (m k : R)
  结论: m % k + m / k * k = m
  证明: by
  rw [mul_comm]
  exact mod_add_div _ _

Depends on / 依赖: mod_add_div, mul_comm
-/
theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _

/--
theorem `div_add_mod'` / 定理 `div_add_mod'`

English:
theorem div_add_mod'
  given: (m k : R)
  statement: m / k * k + m % k = m
  proof: by
  rw [mul_comm]
  exact div_add_mod _ _

中文:
定理 div_add_mod'
  条件: (m k : R)
  结论: m / k * k + m % k = m
  证明: by
  rw [mul_comm]
  exact div_add_mod _ _

Depends on / 依赖: div_add_mod, mul_comm
-/
theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _

/--
theorem `mod_lt` / 定理 `mod_lt`

English:
theorem mod_lt
  statement: forall (a) {b : R}, b != 0 -> a % b ≺ b
  proof: EuclideanDomain.remainder_lt

中文:
定理 mod_lt
  结论: 对任意 (a) {b : R}, b != 0 -> a % b ≺ b
  证明: EuclideanDomain.remainder_lt

Depends on / 依赖: EuclideanDomain, EuclideanDomain.remainder_lt, remainder_lt
-/
theorem mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b :=
  EuclideanDomain.remainder_lt

/--
theorem `mul_right_not_lt` / 定理 `mul_right_not_lt`

English:
theorem mul_right_not_lt
  given: {a : R} (b) (h : a != 0)
  statement: ¬a * b ≺ b
  proof: by
  rw [mul_comm]
  exact mul_left_not_lt b h

@[simp]

中文:
定理 mul_right_not_lt
  条件: {a : R} (b) (h : a != 0)
  结论: ¬a * b ≺ b
  证明: by
  rw [mul_comm]
  exact mul_left_not_lt b h

@[simp]

Depends on / 依赖: mul_comm, mul_left_not_lt
-/
theorem mul_right_not_lt {a : R} (b) (h : a != 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h

@[simp]
/--
theorem `mod_zero` / 定理 `mod_zero`

English:
theorem mod_zero
  given: (a : R)
  statement: a % 0 = a
  proof: by simpa only [zero_mul, zero_add] using div_add_mod a 0

中文:
定理 mod_zero
  条件: (a : R)
  结论: a % 0 = a
  证明: by simpa only [zero_mul, zero_add] using div_add_mod a 0

Depends on / 依赖: div_add_mod, zero_add, zero_mul
-/
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0

/--
theorem `lt_one` / 定理 `lt_one`

English:
theorem lt_one
  given: (a : R)
  statement: a ≺ (1 : R) -> a = 0
  proof: haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

@[simp]

中文:
定理 lt_one
  条件: (a : R)
  结论: a ≺ (1 : R) -> a = 0
  证明: haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

@[simp]

Depends on / 依赖: Classical, Classical.dec, mul_left_not_lt, not_imp_not, one_mul
-/
theorem lt_one (a : R) : a ≺ (1 : R) -> a = 0 :=
  haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (a : R)
  statement: a / 0 = 0
  proof: EuclideanDomain.quotient_zero a

中文:
定理 div_zero
  条件: (a : R)
  结论: a / 0 = 0
  证明: EuclideanDomain.quotient_zero a

Depends on / 依赖: EuclideanDomain, EuclideanDomain.quotient_zero, quotient_zero
-/
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a

section

@[elab_as_elim]
/--
theorem `GCD.induction` / 定理 `GCD.induction`

English:
theorem GCD.induction
  statement: {P : R -> R -> Prop} (a b : R) (H0 : forall x, P 0 x)
  proof: by
  classical
  exact if a0 : a = 0 then
    a0.symm ▸ H0 b
  else
    have _ := mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a

中文:
定理 GCD.induction
  结论: {P : R -> R -> 命题} (a b : R) (H0 : 对任意 x, P 0 x)
  证明: by
  classical
  exact if a0 : a = 0 then
    a0.symm ▸ H0 b
  else
    have _ := mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a

Depends on / 依赖: GCD.induction, a0.symm, classical, mod_lt, termination_by
-/
theorem GCD.induction {P : R -> R -> Prop} (a b : R) (H0 : forall x, P 0 x)
    (H1 : forall a b, a != 0 -> P (b % a) a -> P a b) : P a b := by
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

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (a b : R)
  body: if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a

@[simp]

中文:
定义 最大公约数
  签名: (a b : R)
  定义体: if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a

@[simp]

Depends on / 依赖: mod_lt, termination_by
-/
def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a

@[simp]
/--
theorem `gcd_zero_left` / 定理 `gcd_zero_left`

English:
theorem gcd_zero_left
  given: (a : R)
  statement: gcd 0 a = a
  proof: by
  rw [gcd]
  exact if_pos rfl

中文:
定理 gcd_zero_left
  条件: (a : R)
  结论: 最大公约数 0 a = a
  证明: by
  rw [gcd]
  exact if_pos rfl

Depends on / 依赖: if_pos
-/
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl

/--
Definition of `xgcdAux` / `xgcdAux` 的定义

English:
definition xgcdAux
  signature: (r s t r' s' t' : R)
  body: if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r

@[simp]

中文:
定义 xgcdAux
  签名: (r s t r' s' t' : R)
  定义体: if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r

@[simp]

Depends on / 依赖: mod_lt, termination_by, xgcdAux
-/
def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r

@[simp]
/--
theorem `xgcd_zero_left` / 定理 `xgcd_zero_left`

English:
theorem xgcd_zero_left
  given: {s t r' s' t' : R}
  statement: xgcdAux 0 s t r' s' t' = (r', s', t')
  proof: by
  unfold xgcdAux
  exact if_pos rfl

中文:
定理 xgcd_zero_left
  条件: {s t r' s' t' : R}
  结论: xgcdAux 0 s t r' s' t' = (r', s', t')
  证明: by
  unfold xgcdAux
  exact if_pos rfl

Depends on / 依赖: if_pos, xgcdAux
-/
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcdAux
  exact if_pos rfl

/--
theorem `xgcdAux_rec` / 定理 `xgcdAux_rec`

English:
theorem xgcdAux_rec
  given: {r s t r' s' t' : R} (h : r != 0)
  proof: by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h

中文:
定理 xgcdAux_rec
  条件: {r s t r' s' t' : R} (h : r != 0)
  证明: by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h

Depends on / 依赖: if_neg, xgcdAux
-/
theorem xgcdAux_rec {r s t r' s' t' : R} (h : r != 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h

/--
Definition of `xgcd` / `xgcd` 的定义

English:
definition xgcd
  signature: (x y : R)
  body: (xgcdAux x 1 0 y 0 1).2

中文:
定义 xgcd
  签名: (x y : R)
  定义体: (xgcdAux x 1 0 y 0 1).2

Depends on / 依赖: xgcdAux
-/
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2

/--
Definition of `gcdA` / `gcdA` 的定义

English:
definition gcdA
  signature: (x y : R)
  body: (xgcd x y).1

中文:
定义 gcdA
  签名: (x y : R)
  定义体: (xgcd x y).1
-/
def gcdA (x y : R) : R :=
  (xgcd x y).1

/--
Definition of `gcdB` / `gcdB` 的定义

English:
definition gcdB
  signature: (x y : R)
  body: (xgcd x y).2

@[simp]

中文:
定义 gcdB
  签名: (x y : R)
  定义体: (xgcd x y).2

@[simp]
-/
def gcdB (x y : R) : R :=
  (xgcd x y).2

@[simp]
/--
theorem `gcdA_zero_left` / 定理 `gcdA_zero_left`

English:
theorem gcdA_zero_left
  given: {s : R}
  statement: gcdA 0 s = 0
  proof: by
  unfold gcdA
  rw [xgcd]; rw [xgcd_zero_left]

@[simp]

中文:
定理 gcdA_zero_left
  条件: {s : R}
  结论: gcdA 0 s = 0
  证明: by
  unfold gcdA
  rw [xgcd]; rw [xgcd_zero_left]

@[simp]

Depends on / 依赖: xgcd_zero_left
-/
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd]; rw [xgcd_zero_left]

@[simp]
/--
theorem `gcdB_zero_left` / 定理 `gcdB_zero_left`

English:
theorem gcdB_zero_left
  given: {s : R}
  statement: gcdB 0 s = 1
  proof: by
  unfold gcdB
  rw [xgcd]; rw [xgcd_zero_left]

中文:
定理 gcdB_zero_left
  条件: {s : R}
  结论: gcdB 0 s = 1
  证明: by
  unfold gcdB
  rw [xgcd]; rw [xgcd_zero_left]

Depends on / 依赖: semigroupDvd, xgcd_zero_left
-/
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd]; rw [xgcd_zero_left]

/--
theorem `xgcd_val` / 定理 `xgcd_val`

English:
theorem xgcd_val
  given: (x y : R)
  statement: xgcd x y = (gcdA x y, gcdB x y)
  proof: rfl

中文:
定理 xgcd_val
  条件: (x y : R)
  结论: xgcd x y = (gcdA x y, gcdB x y)
  证明: rfl
-/
theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  rfl

end GCD

section LCM

variable [DecidableEq R]

/--
Definition of `lcm` / `lcm` 的定义

English:
definition lcm
  signature: (x y : R)
  body: x * y / gcd x y

中文:
定义 最小公倍数
  签名: (x y : R)
  定义体: x * y / gcd x y
-/
def lcm (x y : R) : R :=
  x * y / gcd x y

end LCM

end EuclideanDomain
