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

/--
Definition of `NNRat.castRec` / `NNRat.castRec` 的定义

English:
definition NNRat.castRec
  signature: [NatCast K] [Div K] (q : Rat>=0)
  body: q.num / q.den

中文:
定义 NNRat.castRec
  签名: [自然数嵌入 K] [除法 K] (q : 有理数>=0)
  定义体: q.num / q.den

Depends on / 依赖: q.den, q.num
-/
def NNRat.castRec [NatCast K] [Div K] (q : Rat>=0) : K := q.num / q.den

/--
Definition of `Rat.castRec` / `Rat.castRec` 的定义

English:
definition Rat.castRec
  signature: [NatCast K] [IntCast K] [Div K] (q : Rat)
  body: q.num / q.den

中文:
定义 有理数.castRec
  签名: [自然数嵌入 K] [整数嵌入 K] [除法 K] (q : 有理数)
  定义体: q.num / q.den

Depends on / 依赖: q.den, q.num
-/
def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : Rat) : K := q.num / q.den

/--
Definition of `DivisionSemiring` / `DivisionSemiring` 的定义

English:
class DivisionSemiring
  parameters: (K : Type*)
  extends: Semiring K, GroupWithZero K, NNRatCast K
  axioms and operations (4):
    - nnratCast : = NNRat.castRec
    - nnratCast_def((q : Rat>=0)) : (NNRat.cast q : K) = q.num / q.den  [default: by intros; rfl]
    - nnqsmul : Rat>=0 -> K -> K
    - nnqsmul_def((q : Rat>=0) (a : K)) : nnqsmul q a = NNRat.cast q * a  [default: by intros; rfl]

中文:
类 除半环
  参数: (K : 类型)
  继承: 半环 K, 带零群 K, 非负有理数嵌入 K
  公理与运算 (4 个):
    - nnratCast : = NNRat.castRec
    - nnratCast_def((q : 有理数>=0)) : (NNRat.cast q : K) = q.num / q.den  [默认: by intros; rfl]
    - nnqsmul : 有理数>=0 -> K -> K
    - nnqsmul_def((q : 有理数>=0) (a : K)) : nnqsmul q a = NNRat.cast q * a  [默认: by intros; rfl]

Depends on / 依赖: NNRat.castRec, castRec
-/
class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K, NNRatCast K where
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be propositionally equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : Rat>=0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : Rat>=0 -> K -> K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : Rat>=0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl

/--
Definition of `DivisionRing` / `DivisionRing` 的定义

English:
class DivisionRing
  parameters: (K : Type*)
  extends: Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K
  axioms and operations (10):
    - mul_inv_cancel : forall (a : K), a != 0 -> a * a⁻¹ = 1
    - inv_zero : (0 : K)⁻¹ = 0
    - nnratCast : = NNRat.castRec
    - nnratCast_def((q : Rat>=0)) : (NNRat.cast q : K) = q.num / q.den  [default: by intros; rfl]
    - nnqsmul : Rat>=0 -> K -> K
    - nnqsmul_def((q : Rat>=0) (a : K)) : nnqsmul q a = NNRat.cast q * a  [default: by intros; rfl]
    - ratCast : = Rat.castRec
    - ratCast_def((q : Rat)) : (Rat.cast q : K) = q.num / q.den  [default: by intros; rfl]
    - qsmul : Rat -> K -> K
    - qsmul_def((a : Rat) (x : K)) : qsmul a x = Rat.cast a * x  [default: by intros; rfl]

中文:
类 除环
  参数: (K : 类型)
  继承: 环 K, 除逆幺半群 K, 非平凡 K, 非负有理数嵌入 K, 有理数嵌入 K
  公理与运算 (10 个):
    - mul_inv_cancel : 对任意 (a : K), a != 0 -> a * a⁻¹ = 1
    - inv_zero : (0 : K)⁻¹ = 0
    - nnratCast : = NNRat.castRec
    - nnratCast_def((q : 有理数>=0)) : (NNRat.cast q : K) = q.num / q.den  [默认: by intros; rfl]
    - nnqsmul : 有理数>=0 -> K -> K
    - nnqsmul_def((q : 有理数>=0) (a : K)) : nnqsmul q a = NNRat.cast q * a  [默认: by intros; rfl]
    - ratCast : = 有理数.castRec
    - ratCast_def((q : 有理数)) : (有理数.cast q : K) = q.num / q.den  [默认: by intros; rfl]
    - qsmul : 有理数 -> K -> K
    - qsmul_def((a : 有理数) (x : K)) : qsmul a x = 有理数.cast a * x  [默认: by intros; rfl]

Depends on / 依赖: NNRat.castRec, castRec
-/
class DivisionRing (K : Type*)
  extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : forall (a : K), a != 0 -> a * a⁻¹ = 1
  /-- The inverse of `0` is `0` by convention. -/
  protected inv_zero : (0 : K)⁻¹ = 0
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : Rat>=0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : Rat>=0 -> K -> K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : Rat>=0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected ratCast_def (q : Rat) : (Rat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Unless there is a risk of a `Module ℚ _` instance diamond, write `qsmul := _`. This will set
  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : Rat -> K -> K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : Rat) (x : K) : qsmul a x = Rat.cast a * x := by intros; rfl

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing K] : DivisionSemiring K :=
  { ‹DivisionRing K› with }

/--
Definition of `Semifield` / `Semifield` 的定义

English:
class Semifield
  parameters: (K : Type*)
  extends: CommSemiring K, DivisionSemiring K, CommGroupWithZero K
  (no additional axioms)

中文:
类 半域
  参数: (K : 类型)
  继承: 交换半环 K, 除半环 K, 带零交换群 K
  (无附加公理)
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
/--
Definition of `Field` / `Field` 的定义

English:
class Field
  parameters: (K : Type u)
  extends: CommRing K, DivisionRing K
  (no additional axioms)

中文:
类 域
  参数: (K : 类型u)
  继承: 交换环 K, 除环 K
  (无附加公理)

Depends on / 依赖: EuclideanDomain, IsDomain
-/
class Field (K : Type u) extends CommRing K, DivisionRing K

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield [Field K] : Semifield K := { ‹Field K› with }

namespace NNRat
variable [DivisionSemiring K]

instance (priority := 100) smulDivisionSemiring : SMul Rat>=0 K := ⟨DivisionSemiring.nnqsmul⟩

/--
lemma `cast_def` / 引理 `cast_def`

English:
lemma cast_def
  given: (q : Rat>=0)
  statement: (q : K) = q.num / q.den
  proof: DivisionSemiring.nnratCast_def _

中文:
引理 cast_def
  条件: (q : 有理数>=0)
  结论: (q : K) = q.num / q.den
  证明: DivisionSemiring.nnratCast_def _

Depends on / 依赖: DivisionSemiring, DivisionSemiring.nnratCast_def, nnratCast_def
-/
lemma cast_def (q : Rat>=0) : (q : K) = q.num / q.den := DivisionSemiring.nnratCast_def _
/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (q : Rat>=0) (a : K)
  statement: q • a = q * a
  proof: DivisionSemiring.nnqsmul_def q a

中文:
引理 smul_def
  条件: (q : 有理数>=0) (a : K)
  结论: q • a = q * a
  证明: DivisionSemiring.nnqsmul_def q a

Depends on / 依赖: DivisionSemiring, DivisionSemiring.nnqsmul_def, nnqsmul_def
-/
lemma smul_def (q : Rat>=0) (a : K) : q • a = q * a := DivisionSemiring.nnqsmul_def q a

variable (K)

/--
lemma `smul_one_eq_cast` / 引理 `smul_one_eq_cast`

English:
lemma smul_one_eq_cast
  given: (q : Rat>=0)
  statement: q • (1 : K) = q
  proof: by rw [NNRat.smul_def, mul_one]

中文:
引理 smul_one_eq_cast
  条件: (q : 有理数>=0)
  结论: q • (1 : K) = q
  证明: by rw [NNRat.smul_def, mul_one]
-/
@[simp] lemma smul_one_eq_cast (q : Rat>=0) : q • (1 : K) = q := by rw [NNRat.smul_def, mul_one]

end NNRat

namespace Rat
variable [DivisionRing K]

/--
lemma `cast_def` / 引理 `cast_def`

English:
lemma cast_def
  given: (q : Rat)
  statement: (q : K) = q.num / q.den
  proof: DivisionRing.ratCast_def _

中文:
引理 cast_def
  条件: (q : 有理数)
  结论: (q : K) = q.num / q.den
  证明: DivisionRing.ratCast_def _

Depends on / 依赖: DivisionRing, DivisionRing.ratCast_def, ratCast_def
-/
lemma cast_def (q : Rat) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _

/--
lemma `cast_mk'` / 引理 `cast_mk'`

English:
lemma cast_mk'
  given: (a b h1 h2)
  statement: ((⟨a, b, h1, h2⟩ : Rat) : K) = a / b
  proof: cast_def _

中文:
引理 cast_mk'
  条件: (a b h1 h2)
  结论: ((⟨a, b, h1, h2⟩ : 有理数) : K) = a / b
  证明: cast_def _

Depends on / 依赖: cast_def
-/
lemma cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : Rat) : K) = a / b := cast_def _

instance (priority := 100) smulDivisionRing : SMul Rat K :=
  ⟨DivisionRing.qsmul⟩

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (a : Rat) (x : K)
  statement: a • x = ↑a * x
  proof: DivisionRing.qsmul_def a x

@[simp]

中文:
定理 smul_def
  条件: (a : 有理数) (x : K)
  结论: a • x = ↑a * x
  证明: DivisionRing.qsmul_def a x

@[simp]

Depends on / 依赖: DivisionRing, DivisionRing.qsmul_def, qsmul_def
-/
theorem smul_def (a : Rat) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x

@[simp]
/--
theorem `smul_one_eq_cast` / 定理 `smul_one_eq_cast`

English:
theorem smul_one_eq_cast
  given: (A : Type*) [DivisionRing A] (m : Rat)
  statement: m • (1 : A) = ↑m
  proof: by
  rw [Rat.smul_def]; rw [mul_one]

中文:
定理 smul_one_eq_cast
  条件: (A : 类型) [除环 A] (m : 有理数)
  结论: m • (1 : A) = ↑m
  证明: by
  rw [Rat.smul_def]; rw [mul_one]

Depends on / 依赖: Rat.smul_def, mul_one, smul_def
-/
theorem smul_one_eq_cast (A : Type*) [DivisionRing A] (m : Rat) : m • (1 : A) = ↑m := by
  rw [Rat.smul_def]; rw [mul_one]

end Rat

/-- `OfScientific.ofScientific` is the simp-normal form. -/
@[simp]
/--
theorem `Rat.ofScientific_eq_ofScientific` / 定理 `Rat.ofScientific_eq_ofScientific`

English:
theorem Rat.ofScientific_eq_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

中文:
定理 有理数.ofScientific_eq_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: rfl
-/
theorem Rat.ofScientific_eq_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e := rfl
