/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Rat.Init

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `FieldTheory` folder.

## Main definitions

* `DivisionSemiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `DivisionRing`: Nontrivial ring with multiplicative inverses for nonzero elements.
* `Semifield`: Commutative division semiring.
* `Field`: Commutative division ring.
* `IsField`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `GroupWithZero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `GroupWithZero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

@[expose] public section

assert_not_imported Mathlib.Tactic.Common

-- `NeZero` theory should not be needed in the basic algebraic hierarchy
assert_not_imported Mathlib.Algebra.NeZero

assert_not_exists MonoidHom Set

open Function

universe u

variable {K : Type*}

/-- The default definition of the coercion `ℚ≥0 → K` for a division semiring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionSemiring` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
/-
**NNRat.castRec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NNRat.castRec [NatCast K] [Div K] (q : Rat>=0) : K
参数：q : Rat>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The default definition of the coercion `ℚ≥0 → K` for a division semiring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionSemiring` are allowed to overrid
e that default for
better definitional properties). Instead, use the coercion.
-/
def NNRat.castRec [NatCast K] [Div K] (q : ℚ≥0) : K := q.num / q.den

/-- The default definition of the coercion `ℚ → K` for a division ring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionRing` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
/-
**Rat.castRec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rat.castRec [NatCast K] [IntCast K] [Div K] (q : Rat) : K
参数：q : Rat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The default definition of the coercion `ℚ → K` for a division ring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionRing` are allowed to override th
at default for
better definitional properties). Instead, use the coercion.
-/
def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den

/-- A `DivisionSemiring` is a `Semiring` with multiplicative inverses for nonzero elements.

An instance of `DivisionSemiring K` includes maps `nnratCast : ℚ≥0 → K` and `nnqsmul : ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance since we
need to control the specific definitions for some special cases of `K` (in particular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the division semiring has positive characteristic `p`, our division by zero convention forces
`nnratCast (1 / p) = 1 / 0 = 0`. -/
/-
**DivisionSemiring** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K, NNRatCas
t K where protected nnratCast
参数：K : Type*。
继承自：Semiring K, GroupWithZero K, NNRatCast K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DivisionSemiring` is a `Semiring` with multiplicative inverses for nonzero el
ements.

An instance of `DivisionSemiring K` includes maps `nnratCast : ℚ≥0 → K` and `nnq
smul : ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K
` instance since we
need to control the specific definitions for some special cases of `K` (in parti
cular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the division semiring has positive characteristic `p`, our division by zero c
onvention forces
`nnratCast (1 / p) = 1 / 0 = 0`.
-/
class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K, NNRatCast K where
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be propositionally equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : ℚ≥0 → K → K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl

/-- A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.

An instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need
to control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also note [forgetful inheritance]. Similarly, there are maps `nnratCast ℚ≥0 → K` and
`nnqsmul : ℚ≥0 → K → K` to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance.

If the division ring has positive characteristic `p`, our division by zero convention forces
`ratCast (1 / p) = 1 / 0 = 0`. -/
/-
**DivisionRing** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：DivisionRing (K : Type*) extends Ring K, DivInvMonoid K, Nontrivial K, NNR
atCast K, RatCast K where /-- For a nonzero `a`, `a⁻¹` is a right multiplicative
 inverse. -/ protected mul_inv_cancel : forall (a : K), a != 0 -> a * a⁻¹ = 1 /-
- The inverse of `0` is `0` by convention. -/ protected inv_zero : (0 : K)⁻¹ = 0
 protected nnratCast
参数：K : Type*。
继承自：Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.

An instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ →
 K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` inst
ance since we need
to control the specific definitions for some special cases of `K` (in particular
 `K = ℚ` itself).
See also note [forgetful inheritance]. Similarly, there are maps `nnratCast ℚ≥0 
→ K` and
`nnqsmul : ℚ≥0 → K → K` to implement the `DivisionSemiring K → Algebra ℚ≥0 K` in
stance.

If the division ring has positive characteristic `p`, our division by zero conve
ntion forces
`ratCast (1 / p) = 1 / 0 = 0`.
-/
class DivisionRing (K : Type*)
  extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
  /-- The inverse of `0` is `0` by convention. -/
  protected inv_zero : (0 : K)⁻¹ = 0
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : ℚ≥0 → K → K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected ratCast_def (q : ℚ) : (Rat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Unless there is a risk of a `Module ℚ _` instance diamond, write `qsmul := _`. This will set
  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : ℚ → K → K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : ℚ) (x : K) : qsmul a x = Rat.cast a * x := by intros; rfl

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing K] : DivisionSemiring K :=
  { ‹DivisionRing K› with }

/-- A `Semifield` is a `CommSemiring` with multiplicative inverses for nonzero elements.

An instance of `Semifield K` includes maps `nnratCast : ℚ≥0 → K` and `nnqsmul : ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance since we
need to control the specific definitions for some special cases of `K` (in particular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the semifield has positive characteristic `p`, our division by zero convention forces
`nnratCast (1 / p) = 1 / 0 = 0`. -/
/-
**Semifield** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Semifield` is a `CommSemiring` with multiplicative inverses for nonzero eleme
nts.

An instance of `Semifield K` includes maps `nnratCast : ℚ≥0 → K` and `nnqsmul : 
ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K
` instance since we
need to control the specific definitions for some special cases of `K` (in parti
cular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the semifield has positive characteristic `p`, our division by zero conventio
n forces
`nnratCast (1 / p) = 1 / 0 = 0`.
-/
class Semifield (K : Type*) extends CommSemiring K, DivisionSemiring K, CommGroupWithZero K

/-- A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.

An instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need
to control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also note [forgetful inheritance].

If the field has positive characteristic `p`, our division by zero convention forces
`ratCast (1 / p) = 1 / 0 = 0`. -/
@[stacks 09FD "first part"]
/-
**Field** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.

An instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`
.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` inst
ance since we need
to control the specific definitions for some special cases of `K` (in particular
 `K = ℚ` itself).
See also note [forgetful inheritance].

If the field has positive characteristic `p`, our division by zero convention fo
rces
`ratCast (1 / p) = 1 / 0 = 0`.
-/
class Field (K : Type u) extends CommRing K, DivisionRing K

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Field.toSemifield [Field K] : Semifield K := { ‹Field K› with }

namespace NNRat
variable [DivisionSemiring K]

/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) smulDivisionSemiring : SMul ℚ≥0 K := ⟨DivisionSemiring.nnqsmul⟩
/-
**NNRat.cast_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionSemiring.nnratCast_def`：∀ {K : Type u_2} [self : DivisionSemirin
g K] (q : ℚ≥0), ↑q = ↑q.num / ↑q.den
-/
lemma cast_def (q : ℚ≥0) : (q : K) = q.num / q.den := DivisionSemiring.nnratCast_def _
/-
**NNRat.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：smul_def (q : Rat>=0) (a : K) : q • a = q * a
参数：q : Rat>=0；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionSemiring.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionSemiring 
K] (q : ℚ≥0) (a : K), DivisionSemiring.nnqsmul q a = ↑q * a
-/
lemma smul_def (q : ℚ≥0) (a : K) : q • a = q * a := DivisionSemiring.nnqsmul_def q a

variable (K)
/-
**NNRat.smul_one_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (K : Type u_1) [inst : DivisionSemiring K] (q : ℚ≥0), q • 1 = ↑q
参数：K : Type u_1；q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] lemma smul_one_eq_cast (q : ℚ≥0) : q • (1 : K) = q := by rw [NNRat.smul_def, mul_one]

end NNRat

namespace Rat
variable [DivisionRing K]

/-
**Rat.cast_def** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_def (q : Rat) : (q : K) = q.num / q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.ratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ), ↑q = ↑q.num / ↑q.den
-/
lemma cast_def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _
/-
**Rat.cast_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : Rat) : K) = a / b
参数：a b h1 h2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
-/
lemma cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a / b := cast_def _
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) smulDivisionRing : SMul ℚ K :=
  ⟨DivisionRing.qsmul⟩
/-
**Rat.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：smul_def (a : Rat) (x : K) : a • x = ↑a * x
参数：a : Rat；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.qsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (a : ℚ)
 (x : K), DivisionRing.qsmul a x = ↑a * x
-/
theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x

@[simp]
/-
**Rat.smul_one_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：smul_one_eq_cast (A : Type*) [DivisionRing A] (m : Rat) : m • (1 : A) = ↑m
参数：A : Type*；m : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_one_eq_cast (A : Type*) [DivisionRing A] (m : ℚ) : m • (1 : A) = ↑m := by
  rw [Rat.smul_def, mul_one]

end Rat

/-- `OfScientific.ofScientific` is the simp-normal form. -/
@[simp]
/-
**Rat.ofScientific_eq_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.ofScientific_eq_ofScientific (m : Nat) (s : Bool) (e : Nat) : Rat.ofSc
ientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OfScientific.ofScientific` is the simp-normal form.
-/
theorem Rat.ofScientific_eq_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e := rfl
