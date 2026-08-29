/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
module

public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# `ring`-like tactics

The core normalization procedure for ring-like tactics that solve equations in commutative
(semi)rings where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (living in `BaseType`; for `ring` this is a rational embedded into the semiring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`r • a`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The extension to exponents means that something like `2 * 2^n * b = b * 2^(n+1)` can be proved,
even though it is not strictly speaking an equation in the language of commutative rings.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ExSum` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.

The outline of the file:
- Define a mutual inductive family of types `ExSum`, `ExProd`, `ExBase`,
  which can represent expressions with `+`, `*`, `^` and some parametric `BaseType`.
  The mutual induction ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ExSum` type,
  thus allowing us to map expressions to `ExSum` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `Ex*` types)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents. Unfortunately this has to be done with a separate inductive
  type due to universe issues outlined later in this file.

## Caveats and future work

The normalized form of an expression is the one that is useful for the tactic,
but not as nice to read. To remedy this, the user-facing normalization calls `ringNFCore`.

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring` solves the goal,
but `a / a := 1 by ring` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/

public meta section

assert_not_exists IsOrderedMonoid

namespace Mathlib.Tactic
namespace Ring.Common

open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/--
Definition of `sNat` / `sNat` 的定义

English:
definition sNat
  signature: : Q(CommSemiring Nat)
  body: q(Nat.instCommSemiring)

中文:
定义 sNat
  签名: : Q(CommSemiring 自然数)
  定义体: q(Nat.instCommSemiring)

Depends on / 依赖: Nat.instCommSemiring, instCommSemiring
-/
def sNat : Q(CommSemiring Nat) := q(Nat.instCommSemiring)

/--
Definition of `_root_.Mathlib.Tactic.Ring.RatCoeff` / `_root_.Mathlib.Tactic.Ring.RatCoeff` 的定义

English:
structure _root_.Mathlib.Tactic.Ring.RatCoeff
  parameters: {u : Lean.Level} {α : Q(Type u)} (e : Q($α))
  axioms and operations (2):
    - value : Rat
    - hyp : Option Expr

中文:
结构 _root_.Mathlib.Tactic.Ring.RatCoeff
  参数: {u : Lean.Level} {α : Q(类型u)} (e : Q($α))
  公理与运算 (2 个):
    - value : Rat
    - hyp : Option Expr
-/
structure _root_.Mathlib.Tactic.Ring.RatCoeff {u : Lean.Level} {α : Q(Type u)} (e : Q($α)) where
  /-- The value represented by `e`. Should not be zero. -/
  value : Rat
  /-- If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  hyp : Option Expr
deriving Inhabited

/--
Definition of `btNat` / `btNat` 的定义

English:
abbreviation btNat
  signature: (e : Q(Nat))
  body: _root_.Mathlib.Tactic.Ring.RatCoeff q($e)

中文:
缩写 btNat
  签名: (e : Q(自然数))
  定义体: _root_.Mathlib.Tactic.Ring.RatCoeff q($e)

Depends on / 依赖: Mathlib, RatCoeff, Tactic, _root_, _root_.Mathlib.Tactic.Ring.RatCoeff
-/
abbrev btNat (e : Q(Nat)) : Type := _root_.Mathlib.Tactic.Ring.RatCoeff q($e)

instance (e : Expr) : Inhabited btNat e := ⟨⟨0, none⟩⟩

universe u v

/-!
## The ExNat types

The `Ex{Base,Prod,Sum}Nat` types are equivalent to `Ex{Base,Prod,Sum} btℕ sℕ`. `ExProdNat` is only
used to represent exponents in `ExProd`s. We cannot use `ExProd btℕ sℕ` in the `mul` constructor
of `ExProd` because `BaseType` is a parameter and not an index. Making `BaseType` an index
(i.e. moving it to the right of the colon) would require including it as an argument to each
constructor, raising the universe level of `ExProd` from `Type` to `Type 1`; that is:
```
inductive ExProd : ∀ {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) (e : Q($α)), Type
  | const {u : Lean.Level} {α : Q(Type u)} {BaseType} {sα} {e : Q($α)} (value : BaseType e) :
      ExProd BaseType sα e
  | mul {u : Lean.Level} {α : Q(Type u)} {BaseType} {sα} {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase BaseType sα x → ExProd btℕ sℕ e → ExProd BaseType sα b →
      ExProd BaseType sα q($x ^ $e * $b)
```
would fail to compile because `ExProd` lives in `Type 1`.

Lean does not support monadic computation in `Type 1` in its core monad types,
so we cannot tolerate this universe bump.
-/

mutual


/-- `ExBaseNat e` stores the structure of a normalized expression `e : Q(ℕ)`, which appears
as the base of an exponent expression `e^n`. The `sum` constructor is only used when the exponent
`n` is not a constant.

Used to represent normalized natural number expressions in exponents.

`ExBaseNat q($e)` is equivalent to `ExBase btℕ sℕ q($e)`, and one can cast between the two. -/
meta inductive ExBaseNat : (e : Q(Nat)) -> Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which `ring` cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `e : Q($α)` contains a representative of this class.
  -/
  | atom {e} (id : Nat) : ExBaseNat e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSumNat e) : ExBaseNat e

/-- `ExProdNat e` stores the structure of a normalized monomial expression `e : Q(ℕ)`.
A monomial here is a product of powers of `ExBaseNat` expressions, terminated by a (nonzero)
constant coefficient.

Used to represent normalized natural number expressions in exponents.

`ExProdNat q($e)` is equivalent to `ExProd btℕ sℕ q($e)`, and one can cast between the two.
-/
meta inductive ExProdNat : (e : Q(Nat)) -> Type
  /-- A coefficient `value`, holding the data that `ring` uses to represent rational coefficients.
  In this case these happen to always be natural numbers. -/
  | const {e : Q(Nat)} (value : btNat e) : ExProdNat e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBaseNat`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {x : Q(Nat)} {e : Q(Nat)} {b : Q(Nat)} :
    ExBaseNat x -> ExProdNat e -> ExProdNat b -> ExProdNat q($x ^ $e * $b)

/-- `ExSumNat e` stores the structure of a normalized polynomial expression `e : Q(ℕ)`, which is
a sum of monomials.

Used to represent normalized natural number expressions in exponents.

`ExSumNat q($e)` is equivalent to `ExSum btℕ sℕ q($e)`, and one can cast between the two. -/
meta inductive ExSumNat : (e : Q(Nat)) -> Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSumNat q(0)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q(Nat)} : ExProdNat a -> ExSumNat b -> ExSumNat q($a + $b)
end

/-!
The `BaseType` parameter is used to specify how constant coefficients are stored. In the ring
tactic we need only to store coefficients as normalizations to rational numbers, but in a future
algebra tactic the base type may itself be a normalized ring expression.
-/

mutual

/-- `ExBase BaseType sα e` stores the structure of a normalized expression `e`, which appears
as the base of an exponent expression `e^n`. The `sum` constructor is only used when the exponent
`n` is not a constant. -/
meta inductive ExBase {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) -> Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which a `ring`-like tactic cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `e : Q($α)` contains a representative of this class.
  -/
  | atom {e} (id : Nat) : ExBase BaseType sα e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSum BaseType sα e) : ExBase BaseType sα e


/-- `ExProd BaseType sα e` stores the structure of a normalized monomial expression `e`.
A monomial here is a product of powers of `ExBase` expressions, terminated by a (nonzero) constant
coefficient. The data of the constant coefficient is stored in the `BaseType`. -/
meta inductive ExProd {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) -> Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | const {e : Q($α)} (value : BaseType e) : ExProd BaseType sα e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.)
  -/
  | mul {x : Q($α)} {e : Q(Nat)} {b : Q($α)} :
    ExBase BaseType sα x -> ExProdNat e -> ExProd BaseType sα b -> ExProd BaseType sα q($x ^ $e * $b)

/-- `ExSum BaseType sα e` stores the structure of a normalized polynomial expression `e`, which is
a sum of monomials. -/
meta inductive ExSum {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) -> Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSum BaseType sα q(0 : $α)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q($α)} :
    ExProd BaseType sα a -> ExSum BaseType sα b -> ExSum BaseType sα q($a + $b)

end

variable {u : Lean.Level}

/--
Definition of `Result` / `Result` 的定义

English:
structure Result
  parameters: {α : Q(Type u)} (E : Q($α) -> Type*) (e : Q($α))
  axioms and operations (3):
    - expr : Q($α)
    - val : E expr
    - proof : Q($e = $expr)

中文:
结构 Result
  参数: {α : Q(类型u)} (E : Q($α) -> 类型) (e : Q($α))
  公理与运算 (3 个):
    - expr : Q($α)
    - val : E expr
    - proof : Q($e = $expr)
-/
structure Result {α : Q(Type u)} (E : Q($α) -> Type*) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

instance {α : Q(Type u)} {E : Q($α) -> Type} {e : Q($α)} [Inhabited (Σ e, E e)] :
    Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩


/--
Definition of `RingCompare` / `RingCompare` 的定义

English:
structure RingCompare
  parameters: {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
  axioms and operations (2):
    - eq : forall {x y : Q($α)}, BaseType x -> BaseType y -> Bool
    - compare : forall {x y : Q($α)}, BaseType x -> BaseType y -> Ordering

中文:
结构 RingCompare
  参数: {u : Lean.Level} {α : Q(类型u)} (BaseType : Q($α) -> Type)
  公理与运算 (2 个):
    - eq : 对任意 {x y : Q($α)}, BaseType x -> BaseType y -> 布尔
    - compare : 对任意 {x y : Q($α)}, BaseType x -> BaseType y -> Ordering
-/
structure RingCompare {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type) where
  /-- Returns whether two coefficients are equal -/
  eq : forall {x y : Q($α)}, BaseType x -> BaseType y -> Bool
  /-- Returns whether `x` is less than, equal to or greater than `y`. Can be any total order. -/
  compare : forall {x y : Q($α)}, BaseType x -> BaseType y -> Ordering

/--
Definition of `RingCompute` / `RingCompute` 的定义

English:
structure RingCompute
  parameters: {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
  extends: RingCompare BaseType
  axioms and operations (9):
    - add({x y : Q($α)}) : BaseType x -> BaseType y -> MetaM ((Result BaseType q($x + $y)) × (Option Q(IsNat ($x + $y) 0)))
    - mul({x y : Q($α)}) : BaseType x -> BaseType y -> MetaM (Result BaseType q($x * $y))
    - cast((v : Lean.Level) (β : Q(Type v)) (_ : Q(CommSemiring $β)) (_ : Q(SMul $β $α)) (x : Q($β))) : AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(forall a : $α, $x • a = $y * a))
    - neg({x : Q($α)} (rα : Q(CommRing $α))) : BaseType x -> MetaM (Result BaseType q(-$x))
    - pow({x : Q($α)} {b : Q(Nat)}) : BaseType x -> (vb : ExProdNat q($b)) -> OptionT MetaM (Result BaseType q($x ^ $b))
    - inv({x : Q($α)} (czα : Option Q(CharZero $α)) (fα : Q(Semifield $α))) : BaseType x -> AtomM (Option <| Result BaseType q($x⁻¹))
    - derive((x : Q($α))) : MetaM (Result (ExSum BaseType sα) q($x))
    - isOne({x : Q($α)}) : BaseType x -> Option Q(NormNum.IsNat $x 1)
    - one : Result BaseType q((nat_lit 1).rawCast)

中文:
结构 RingCompute
  参数: {u : Lean.Level} {α : Q(类型u)} (BaseType : Q($α) -> Type)
  继承: RingCompare BaseType
  公理与运算 (9 个):
    - add({x y : Q($α)}) : BaseType x -> BaseType y -> MetaM ((Result BaseType q($x + $y)) × (Option Q(Is自然数 ($x + $y) 0)))
    - mul({x y : Q($α)}) : BaseType x -> BaseType y -> MetaM (Result BaseType q($x * $y))
    - cast((v : Lean.Level) (β : Q(类型v)) (_ : Q(CommSemiring $β)) (_ : Q(SMul $β $α)) (x : Q($β))) : AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(对任意 a : $α, $x • a = $y * a))
    - neg({x : Q($α)} (rα : Q(CommRing $α))) : BaseType x -> MetaM (Result BaseType q(-$x))
    - pow({x : Q($α)} {b : Q(自然数)}) : BaseType x -> (vb : ExProd自然数 q($b)) -> OptionT MetaM (Result BaseType q($x ^ $b))
    - inv({x : Q($α)} (czα : Option Q(CharZero $α)) (fα : Q(Semifield $α))) : BaseType x -> AtomM (Option <| Result BaseType q($x⁻¹))
    - derive((x : Q($α))) : MetaM (Result (ExSum BaseType sα) q($x))
    - isOne({x : Q($α)}) : BaseType x -> Option Q(NormNum.Is自然数 $x 1)
    - one : Result BaseType q((nat_lit 1).rawCast)
-/
structure RingCompute {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
  (sα : Q(CommSemiring $α)) extends RingCompare BaseType where
  /-- Evaluate the sum of two coefficients.

  If the result is zero returns a proof of this fact, which is used to remove zero terms. -/
  add {x y : Q($α)} : BaseType x -> BaseType y ->
    MetaM ((Result BaseType q($x + $y)) × (Option Q(IsNat ($x + $y) 0)))
  /-- Evaluate the product of two coefficients. -/
  mul {x y : Q($α)} : BaseType x -> BaseType y -> MetaM (Result BaseType q($x * $y))
  /-- Given a commutative ring `β` with a scalar multiplication action on `α` and a `x : β`, cast
  `x` to `α` such that the scalar multiplication turns into normal multiplication. Typically one
  can think of `α` as being an algebra over `β`, but this file does not know about `Algebra`s. -/
  cast (v : Lean.Level) (β : Q(Type v)) (_ : Q(CommSemiring $β))
      (_ : Q(SMul $β $α)) (x : Q($β)) :
    AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(forall a : $α, $x • a = $y * a))
  /-- Evaluate the negation of a coefficient. -/
  neg {x : Q($α)} (rα : Q(CommRing $α)) : BaseType x -> MetaM (Result BaseType q(-$x))
  /-- Raise a coefficient to some natural power.

  The exponent is not necessarily a natural literal. If the tactic can only raise coefficients to
  the power of a literal (e.g. `ring`), it should check for this and return `none` otherwise. -/
  pow {x : Q($α)} {b : Q(Nat)} : BaseType x -> (vb : ExProdNat q($b)) ->
    OptionT MetaM (Result BaseType q($x ^ $b))
  /-- Evaluate the inverse of a coefficient. -/
  inv {x : Q($α)} (czα : Option Q(CharZero $α)) (fα : Q(Semifield $α)) : BaseType x ->
    AtomM (Option <| Result BaseType q($x⁻¹))
  /-- Evaluate an expression as a potential coefficient. -/
  derive (x : Q($α)) : MetaM (Result (ExSum BaseType sα) q($x))
  /-- Decides whether a coefficient is 1 and returns a proof if so. -/
  isOne {x : Q($α)} : BaseType x -> Option Q(NormNum.IsNat $x 1)
  /-- The number 1 represented as a BaseType. -/
  one : Result BaseType q((nat_lit 1).rawCast)

instance {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) -> Type)
    (sα : Q(CommSemiring $α)) : CoeOut (RingCompute BaseType sα) (RingCompare BaseType) where
  coe x := x.toRingCompare

instance (u : Lean.Level) (α : Q(Type u)) (BaseType : Q($α) -> Type) [forall e, Nonempty (BaseType e)]
(sα : Q(CommSemiring «$α»)) : Nonempty
    Common.RingCompute (BaseType) sα := ⟨{
  eq := default
  compare := default
  add := default
  mul := default
  cast _ _ _ _ _ _ := do return ⟨_, .zero (BaseType := BaseType) (sα := sα), default⟩
  neg := default
  pow := default
  inv := default
  derive := default
  isOne := default
  one :=
    have (e : Q($α)) : Inhabited (BaseType e) := Classical.inhabited_of_nonempty'
    default
}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExBaseNat e)
  body: ⟨default, .atom 0⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExBase自然数 e)
  定义体: ⟨default, .atom 0⟩
-/
instance : Inhabited (Σ e, ExBaseNat e) := ⟨default, .atom 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExSumNat e)
  body: ⟨_, .zero⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExSum自然数 e)
  定义体: ⟨_, .zero⟩
-/
instance : Inhabited (Σ e, ExSumNat e) := ⟨_, .zero⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExProdNat e)
  body: ⟨default, .const default⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExProd自然数 e)
  定义体: ⟨default, .const default⟩
-/
instance : Inhabited (Σ e, ExProdNat e) := ⟨default, .const default⟩

variable {u : Lean.Level} {α : Q(Type u)} {bt : Q($α) -> Type} {sα : Q(CommSemiring $α)}
   [forall e, Inhabited (bt e)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExBase bt sα e)
  body: ⟨default, .atom 0⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExBase bt sα e)
  定义体: ⟨default, .atom 0⟩
-/
instance : Inhabited (Σ e, ExBase bt sα e) := ⟨default, .atom 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExSum bt sα e)
  body: ⟨_, .zero⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExSum bt sα e)
  定义体: ⟨_, .zero⟩
-/
instance : Inhabited (Σ e, ExSum bt sα e) := ⟨_, .zero⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Σ e, ExProd bt sα e)
  body: ⟨default, .const default⟩

中文:
实例 :
  签名: Inhabited (Σ e, ExProd bt sα e)
  定义体: ⟨default, .const default⟩
-/
instance : Inhabited (Σ e, ExProd bt sα e) := ⟨default, .const default⟩

variable (rc : RingCompute bt sα) (rcNat : RingCompute btNat sNat)

mutual

/--
Definition of `ExBaseNat.toExBase` / `ExBaseNat.toExBase` 的定义

English:
definition ExBaseNat.toExBase
  signature: (e : Q(Nat))
  body: fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩

中文:
定义 ExBaseNat.toExBase
  签名: (e : Q(自然数))
  定义体: fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩
-/
partial def ExBaseNat.toExBase (e : Q(Nat)) : ExBaseNat e -> Σ e', ExBase btNat sNat e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩

/--
Definition of `ExProdNat.toExProd` / `ExProdNat.toExProd` 的定义

English:
definition ExProdNat.toExProd
  signature: (e : Q(Nat))
  body: fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩

中文:
定义 ExProdNat.toExProd
  签名: (e : Q(自然数))
  定义体: fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩
-/
partial def ExProdNat.toExProd (e : Q(Nat)) : ExProdNat e -> Σ e', ExProd btNat sNat e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩

/--
Definition of `ExSumNat.toExSum` / `ExSumNat.toExSum` 的定义

English:
definition ExSumNat.toExSum
  signature: (e : Q(Nat))
  body: fun
  | .zero => ⟨_, .zero (BaseType := btNat) (sα := sNat)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩

中文:
定义 ExSumNat.toExSum
  签名: (e : Q(自然数))
  定义体: fun
  | .zero => ⟨_, .zero (BaseType := btNat) (sα := sNat)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩
-/
partial def ExSumNat.toExSum (e : Q(Nat)) : ExSumNat e -> Σ e', ExSum btNat sNat e' := fun
  | .zero => ⟨_, .zero (BaseType := btNat) (sα := sNat)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩

end

mutual

/--
Definition of `ExBase.toExBaseNat` / `ExBase.toExBaseNat` 的定义

English:
definition ExBase.toExBaseNat
  signature: (e : Q(Nat))
  body: fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩

中文:
定义 ExBase.toExBaseNat
  签名: (e : Q(自然数))
  定义体: fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩
-/
partial def ExBase.toExBaseNat (e : Q(Nat)) : ExBase btNat sNat e -> Σ e', ExBaseNat e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩

/--
Definition of `ExProd.toExProdNat` / `ExProd.toExProdNat` 的定义

English:
definition ExProd.toExProdNat
  signature: (e : Q(Nat))
  body: fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩

中文:
定义 ExProd.toExProdNat
  签名: (e : Q(自然数))
  定义体: fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩
-/
partial def ExProd.toExProdNat (e : Q(Nat)) : ExProd btNat sNat e -> Σ e', ExProdNat e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩

/--
Definition of `ExSum.toExSumNat` / `ExSum.toExSumNat` 的定义

English:
definition ExSum.toExSumNat
  signature: (e : Q(Nat))
  body: fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩

中文:
定义 ExSum.toExSumNat
  签名: (e : Q(自然数))
  定义体: fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩
-/
partial def ExSum.toExSumNat (e : Q(Nat)) : ExSum btNat sNat e -> Σ e', ExSumNat e' := fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩

end

section

/--
Definition of `ExBase.toProd` / `ExBase.toProd` 的定义

English:
definition ExBase.toProd
  body: let ⟨_, one, pf⟩ := rc.one
  ⟨_, .mul va vb (.const (one)), q(by rw [← $pf])⟩

中文:
定义 ExBase.toProd
  定义体: let ⟨_, one, pf⟩ := rc.one
  ⟨_, .mul va vb (.const (one)), q(by rw [← $pf])⟩

Depends on / 依赖: rc.one
-/
def ExBase.toProd
    {a : Q($α)} {b : Q(Nat)}
    (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b * (nat_lit 1).rawCast) :=
  let ⟨_, one, pf⟩ := rc.one
  ⟨_, .mul va vb (.const (one)), q(by rw [← $pf])⟩

/--
Definition of `ExProd.toSum` / `ExProd.toSum` 的定义

English:
definition ExProd.toSum
  signature: {e : Q($α)} (v : ExProd bt sα e)
  body: .add v .zero

中文:
定义 ExProd.toSum
  签名: {e : Q($α)} (v : ExProd bt sα e)
  定义体: .add v .zero
-/
def ExProd.toSum {e : Q($α)} (v : ExProd bt sα e) : ExSum bt sα q($e + 0) :=
  .add v .zero



-- Partial because the termination checker failed
mutual

variable (rcNat : RingCompare btNat)

/--
Definition of `ExBase.eq` / `ExBase.eq` 的定义

English:
definition ExBase.eq

中文:
定义 ExBase.eq
-/
partial def ExBase.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExBase bt sα a -> ExBase bt sα b -> Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq rc b
  | _, _ => false

@[inherit_doc ExBase.eq]
/--
Definition of `ExProd.eq` / `ExProd.eq` 的定义

English:
definition ExProd.eq

中文:
定义 ExProd.eq
-/
partial def ExProd.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExProd bt sα a -> ExProd bt sα b -> Bool
  | .const i, .const j => rc.eq i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq rc b₁ && a₂.toExProd.2.eq rcNat b₂.toExProd.2 && a₃.eq rc b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
/--
Definition of `ExSum.eq` / `ExSum.eq` 的定义

English:
definition ExSum.eq

中文:
定义 ExSum.eq
-/
partial def ExSum.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExSum bt sα a -> ExSum bt sα b -> Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq rc b₁ && a₂.eq rc b₂
  | _, _ => false
end

mutual

variable (rcNat : RingCompute btNat sNat)

/--
Definition of `ExBase.cmp` / `ExBase.cmp` 的定义

English:
definition ExBase.cmp
  signature: {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}

中文:
定义 ExBase.cmp
  签名: {u : Lean.Level} {α : Q(类型u)} {bt} {sα : Q(CommSemiring $α)}
-/
partial def ExBase.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExBase bt sα a -> ExBase bt sα b -> Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp rc b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
/--
Definition of `ExProd.cmp` / `ExProd.cmp` 的定义

English:
definition ExProd.cmp
  signature: {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}

中文:
定义 ExProd.cmp
  签名: {u : Lean.Level} {α : Q(类型u)} {bt} {sα : Q(CommSemiring $α)}
-/
partial def ExProd.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExProd bt sα a -> ExProd bt sα b -> Ordering
  | .const i, .const j => rc.compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ =>
.then (a₃.cmp rc b₃) (a₁.cmp rc b₁).then (a₂.toExProd.2.cmp rcNat b₂.toExProd.2)
  | .const _, .mul .. => .lt
  | .mul .., .const _ => .gt

@[inherit_doc ExBase.cmp]
/--
Definition of `ExSum.cmp` / `ExSum.cmp` 的定义

English:
definition ExSum.cmp
  signature: {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}

中文:
定义 ExSum.cmp
  签名: {u : Lean.Level} {α : Q(类型u)} {bt} {sα : Q(CommSemiring $α)}
-/
partial def ExSum.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExSum bt sα a -> ExSum bt sα b -> Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp rc b₁).then (a₂.cmp rc b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

variable {R : Type*} [CommSemiring R]

section

/--
Definition of `ExProd.coeff` / `ExProd.coeff` 的定义

English:
definition ExProd.coeff
  signature: {e : Q($α)}

中文:
定义 ExProd.coeff
  签名: {e : Q($α)}
-/
def ExProd.coeff {e : Q($α)} :
  ExProd bt sα e -> Σ c, bt c
  | .const q => ⟨_, q⟩
  | .mul _ _ v => v.coeff
end

variable (bt) (sα) in
/--
Inductive type `Overlap` / 归纳类型 `Overlap`

English:
inductive Overlap
  parameters: (e : Q($α))
  constructors (2):
    - zero: (_ : Q(IsNat $e (nat_lit 0)))
    - nonzero: (_ : Result (ExProd bt sα) e)

中文:
归纳类型 Overlap
  参数: (e : Q($α))
  构造子 (2 个):
    - zero: (_ : Q(Is自然数 $e (nat_lit 0)))
    - nonzero: (_ : Result (ExProd bt sα) e)
-/
inductive Overlap (e : Q($α)) : Type where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExProd bt sα) e)

variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : R}


/--
theorem `add_overlap_pf` / 定理 `add_overlap_pf`

English:
theorem add_overlap_pf
  given: (x : R) (e) (pq_pf : a + b = c)
  proof: by subst_vars; simp [mul_add]

中文:
定理 add_overlap_pf
  条件: (x : R) (e) (pq_pf : a + b = c)
  证明: by subst_vars; simp [mul_add]

Depends on / 依赖: mul_add
-/
theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]

/--
theorem `add_overlap_pf_zero` / 定理 `add_overlap_pf_zero`

English:
theorem add_overlap_pf_zero
  given: (x : R) (e)

中文:
定理 add_overlap_pf_zero
  条件: (x : R) (e)
-/
theorem add_overlap_pf_zero (x : R) (e) :
    IsNat (a + b) (nat_lit 0) -> IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m} [Pure m] : MonadLift Option (OptionT m) where
monadLift f := .mk pure f

/--
Definition of `evalAddOverlap` / `evalAddOverlap` 的定义

English:
definition evalAddOverlap
  signature: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b)
  body: do
  Lean.Core.checkSystem decl_name%.toString
  match (dependent := true) va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add za zb
    match isZero with
| .some pf => pure .zero q($pf)
    | .none =>
      assumeInstancesCommute
pure .nonzero ⟨_, .const zc, q($pf)⟩
  

中文:
定义 evalAddOverlap
  签名: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b)
  定义体: do
  Lean.Core.checkSystem decl_name%.toString
  match (dependent := true) va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add za zb
    match isZero with
| .some pf => pure .zero q($pf)
    | .none =>
      assumeInstancesCommute
pure .nonzero ⟨_, .const zc, q($pf)⟩
  
-/
def evalAddOverlap {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    OptionT MetaM (Overlap bt sα q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match (dependent := true) va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add za zb
    match isZero with
| .some pf => pure .zero q($pf)
    | .none =>
      assumeInstancesCommute
pure .nonzero ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    guard (va₁.eq rcNat rc vb₁ && va₂.toExProd.2.eq rcNat rcNat vb₂.toExProd.2)
have : a₁ =Q b₁ := ⟨⟩; have : a₂ =Q b₂ := ⟨⟩
    match ← evalAddOverlap va₃ vb₃ with
| .zero p => pure .zero q(add_overlap_pf_zero $a₁ $a₂ $p)
    | .nonzero ⟨_, vc, p⟩ =>
pure .nonzero ⟨_, .mul va₁ va₂ vc, q(add_overlap_pf $a₁ $a₂ $p)⟩
  | _, _ => OptionT.fail

/--
theorem `add_pf_zero_add` / 定理 `add_pf_zero_add`

English:
theorem add_pf_zero_add
  given: (b : R)
  statement: 0 + b = b
  proof: by simp

中文:
定理 add_pf_zero_add
  条件: (b : R)
  结论: 0 + b = b
  证明: by simp
-/
theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

/--
theorem `add_pf_add_zero` / 定理 `add_pf_add_zero`

English:
theorem add_pf_add_zero
  given: (a : R)
  statement: a + 0 = a
  proof: by simp

中文:
定理 add_pf_add_zero
  条件: (a : R)
  结论: a + 0 = a
  证明: by simp
-/
theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

/--
theorem `add_pf_add_overlap` / 定理 `add_pf_add_overlap`

English:
theorem add_pf_add_overlap
  proof: by
  subst_vars; simp [add_assoc, add_left_comm]

中文:
定理 add_pf_add_overlap
  证明: by
  subst_vars; simp [add_assoc, add_left_comm]

Depends on / 依赖: add_assoc, add_left_comm
-/
theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

/--
theorem `add_pf_add_overlap_zero` / 定理 `add_pf_add_overlap_zero`

English:
theorem add_pf_add_overlap_zero
  proof: by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

中文:
定理 add_pf_add_overlap_zero
  证明: by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

Depends on / 依赖: Nat.cast_zero, add_add_add_comm, add_pf_zero_add, cast_zero
-/
theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

/--
theorem `add_pf_add_lt` / 定理 `add_pf_add_lt`

English:
theorem add_pf_add_lt
  given: (a₁ : R) (_ : a₂ + b = c)
  statement: (a₁ + a₂) + b = a₁ + c
  proof: by simp [*, add_assoc]

中文:
定理 add_pf_add_lt
  条件: (a₁ : R) (_ : a₂ + b = c)
  结论: (a₁ + a₂) + b = a₁ + c
  证明: by simp [*, add_assoc]

Depends on / 依赖: add_assoc
-/
theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

/--
theorem `add_pf_add_gt` / 定理 `add_pf_add_gt`

English:
theorem add_pf_add_gt
  given: (b₁ : R) (_ : a + b₂ = c)
  statement: a + (b₁ + b₂) = b₁ + c
  proof: by
  subst_vars; simp [add_left_comm]

中文:
定理 add_pf_add_gt
  条件: (b₁ : R) (_ : a + b₂ = c)
  结论: a + (b₁ + b₂) = b₁ + c
  证明: by
  subst_vars; simp [add_left_comm]

Depends on / 依赖: add_left_comm
-/
theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

/--
Definition of `evalAdd` / `evalAdd` 的定义

English:
definition evalAdd
  signature: {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b)
  body: Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .zero, vb => do return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => do return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ => do
    have va := .add va₁ va₂; have vb := 

中文:
定义 evalAdd
  签名: {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b)
  定义体: Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .zero, vb => do return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => do return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ => do
    have va := .add va₁ va₂; have vb := 
-/
partial def evalAdd {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
MetaM Result (ExSum bt sα) q($a + $b) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .zero, vb => do return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => do return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ => do
    have va := .add va₁ va₂; have vb := .add vb₁ vb₂ -- FIXME: why does `va@(...)` fail?
    match ← (evalAddOverlap rc rcNat va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp rcNat rc vb₁ then
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩


/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (a : R)
  statement: (nat_lit 1).rawCast * a = a
  proof: by simp [Nat.rawCast]

中文:
定理 one_mul
  条件: (a : R)
  结论: (nat_lit 1).rawCast * a = a
  证明: by simp [Nat.rawCast]
-/
theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: (a : R)
  statement: a * (nat_lit 1).rawCast = a
  proof: by simp [Nat.rawCast]

中文:
定理 mul_one
  条件: (a : R)
  结论: a * (nat_lit 1).rawCast = a
  证明: by simp [Nat.rawCast]
-/
theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

/--
theorem `mul_pf_left` / 定理 `mul_pf_left`

English:
theorem mul_pf_left
  given: (a₁ : R) (a₂) (_ : a₃ * b = c)
  proof: by
  subst_vars; rw [mul_assoc]

中文:
定理 mul_pf_left
  条件: (a₁ : R) (a₂) (_ : a₃ * b = c)
  证明: by
  subst_vars; rw [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) :
    (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]

/--
theorem `mul_pf_right` / 定理 `mul_pf_right`

English:
theorem mul_pf_right
  given: (b₁ : R) (b₂) (_ : a * b₃ = c)
  proof: by
  subst_vars; rw [mul_left_comm]

中文:
定理 mul_pf_right
  条件: (b₁ : R) (b₂) (_ : a * b₃ = c)
  证明: by
  subst_vars; rw [mul_left_comm]

Depends on / 依赖: mul_left_comm
-/
theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) :
    a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]

/--
theorem `mul_pp_pf_overlap` / 定理 `mul_pp_pf_overlap`

English:
theorem mul_pp_pf_overlap
  given: {ea eb e : Nat} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c)
  proof: by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

中文:
定理 mul_pp_pf_overlap
  条件: {ea eb e : 自然数} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c)
  证明: by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

Depends on / 依赖: mul_mul_mul_comm, pow_add
-/
theorem mul_pp_pf_overlap {ea eb e : Nat} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

/--
Definition of `evalMulProd` / `evalMulProd` 的定义

English:
definition evalMulProd
  signature: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b)
  body: Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .const za, .const zb => do
    let ⟨_, zc, pf⟩ ← rc.mul za zb
    assumeInstancesCommute
    return ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, vb@(.const _) => do
    let ⟨_, vc, pc⟩ ← evalMulProd va₃ vb
    r

中文:
定义 evalMulProd
  签名: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b)
  定义体: Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .const za, .const zb => do
    let ⟨_, zc, pf⟩ ← rc.mul za zb
    assumeInstancesCommute
    return ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, vb@(.const _) => do
    let ⟨_, vc, pc⟩ ← evalMulProd va₃ vb
    r
-/
partial def evalMulProd {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
MetaM Result (ExProd bt sα) q($a * $b) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .const za, .const zb => do
    let ⟨_, zc, pf⟩ ← rc.mul za zb
    assumeInstancesCommute
    return ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, vb@(.const _) => do
    let ⟨_, vc, pc⟩ ← evalMulProd va₃ vb
    return ⟨_, .mul va₁ va₂ vc, q(mul_pf_left $a₁ $a₂ $pc)⟩
  | va@(.const _), .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    let ⟨_, vc, pc⟩ ← evalMulProd va vb₃
    return ⟨_, .mul vb₁ vb₂ vc, q(mul_pf_right $b₁ $b₂ $pc)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ => do
    have va := .mul vxa vea va₂; have vb := .mul vxb veb vb₂ -- FIXME: why does `va@(...)` fail?
    let ⟨ea', vea'⟩ := vea.toExProd
    let ⟨eb', veb'⟩ := veb.toExProd
    if vxa.eq rcNat rc vxb then
have : xa =Q xb := ⟨⟩
      if let some (.nonzero ⟨ec', vec', pec'⟩) ← (evalAddOverlap rcNat rcNat vea' veb').run then
        let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb₂
        let ⟨ec, vec⟩ := vec'.toExProdNat
have : ea =Q ea' := ⟨⟩
have : eb =Q eb' := ⟨⟩
have : ec =Q ec' := ⟨⟩
        return ⟨_, .mul vxa vec vc, q(mul_pp_pf_overlap $xa $pec' $pc)⟩
    if let .lt := (vxa.cmp rcNat rc vxb).then (vea'.cmp rcNat rcNat veb') then
      let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb
      return ⟨_, .mul vxa vea vc, q(mul_pf_left $xa $ea $pc)⟩
    else
      let ⟨_, vc, pc⟩ ← evalMulProd va vb₂
      return ⟨_, .mul vxb veb vc, q(mul_pf_right $xb $eb $pc)⟩

/--
theorem `mul_zero` / 定理 `mul_zero`

English:
theorem mul_zero
  given: (a : R)
  statement: a * 0 = 0
  proof: by simp

中文:
定理 mul_zero
  条件: (a : R)
  结论: a * 0 = 0
  证明: by simp
-/
theorem mul_zero (a : R) : a * 0 = 0 := by simp

/--
theorem `mul_add` / 定理 `mul_add`

English:
theorem mul_add
  given: {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d)
  proof: by
  subst_vars; simp [_root_.mul_add]

中文:
定理 mul_add
  条件: {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d)
  证明: by
  subst_vars; simp [_root_.mul_add]

Depends on / 依赖: _root_, _root_.mul_add, mul_add
-/
theorem mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by
  subst_vars; simp [_root_.mul_add]

/--
Definition of `evalMul₁` / `evalMul₁` 的定义

English:
definition evalMul₁
  signature: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExSum bt sα b)
  body: match vb with
  | .zero => do return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁.toSum vc₂
    return ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

中文:
定义 evalMul₁
  签名: {a b : Q($α)} (va : ExProd bt sα a) (vb : ExSum bt sα b)
  定义体: match vb with
  | .zero => do return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁.toSum vc₂
    return ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

Depends on / 依赖: evalAdd, evalMulProd, mul_add, mul_zero, return
-/
def evalMul₁ {a b : Q($α)} (va : ExProd bt sα a) (vb : ExSum bt sα b) :
MetaM Result (ExSum bt sα) q($a * $b) :=
  match vb with
  | .zero => do return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁.toSum vc₂
    return ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  given: (b : R)
  statement: 0 * b = 0
  proof: by simp

中文:
定理 zero_mul
  条件: (b : R)
  结论: 0 * b = 0
  证明: by simp
-/
theorem zero_mul (b : R) : 0 * b = 0 := by simp

/--
theorem `add_mul` / 定理 `add_mul`

English:
theorem add_mul
  given: {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d)
  proof: by subst_vars; simp [_root_.add_mul]

中文:
定理 add_mul
  条件: {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d)
  证明: by subst_vars; simp [_root_.add_mul]

Depends on / 依赖: _root_, _root_.add_mul, add_mul
-/
theorem add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

/--
Definition of `evalMul` / `evalMul` 的定义

English:
definition evalMul
  signature: {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b)
  body: match va with
  | .zero => do return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcNat va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

中文:
定义 evalMul
  签名: {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b)
  定义体: match va with
  | .zero => do return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcNat va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

Depends on / 依赖: add_mul, evalAdd, evalMul, return, zero_mul
-/
def evalMul {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
MetaM Result (ExSum bt sα) q($a * $b) :=
  match va with
  | .zero => do return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcNat va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcNat vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩


/--
theorem `neg_one_mul` / 定理 `neg_one_mul`

English:
theorem neg_one_mul
  given: {R} [CommRing R] {a b : R} (_ : (-1 : R) * a = b)
  proof: by subst_vars; simp

中文:
定理 neg_one_mul
  条件: {R} [CommRing R] {a b : R} (_ : (-1 : R) * a = b)
  证明: by subst_vars; simp
-/
theorem neg_one_mul {R} [CommRing R] {a b : R} (_ : (-1 : R) * a = b) :
    -a = b := by subst_vars; simp

/--
theorem `neg_mul` / 定理 `neg_mul`

English:
theorem neg_mul
  statement: {R} [CommRing R] (a₁ : R) (a₂) {a₃ b : R}
  proof: by subst_vars; simp

中文:
定理 neg_mul
  结论: {R} [CommRing R] (a₁ : R) (a₂) {a₃ b : R}
  证明: by subst_vars; simp
-/
theorem neg_mul {R} [CommRing R] (a₁ : R) (a₂) {a₃ b : R}
    (_ : -a₃ = b) : -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by subst_vars; simp

/--
Definition of `evalNegProd` / `evalNegProd` 的定义

English:
definition evalNegProd
  signature: {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a)
  body: Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const za => do
    let ⟨b, zb, pb⟩ ← rc.neg q($rα) za
    return ⟨b, .const zb, q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb,

中文:
定义 evalNegProd
  签名: {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a)
  定义体: Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const za => do
    let ⟨b, zb, pb⟩ ← rc.neg q($rα) za
    return ⟨b, .const zb, q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb,

Depends on / 依赖: Lean.Core.checkSystem, assumeInstancesCommute, checkSystem, decl_name, evalNegProd, neg_mul, rc.neg, return, toString
-/
def evalNegProd {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a) :
MetaM Result (ExProd bt sα) q(-$a) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const za => do
    let ⟨b, zb, pb⟩ ← rc.neg q($rα) za
    return ⟨b, .const zb, q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb, q(neg_mul $a₁ $a₂ $pb)⟩

/--
theorem `neg_zero` / 定理 `neg_zero`

English:
theorem neg_zero
  given: {R} [CommRing R]
  statement: -(0 : R) = 0
  proof: by simp

中文:
定理 neg_zero
  条件: {R} [CommRing R]
  结论: -(0 : R) = 0
  证明: by simp
-/
theorem neg_zero {R} [CommRing R] : -(0 : R) = 0 := by simp

/--
theorem `neg_add` / 定理 `neg_add`

English:
theorem neg_add
  statement: {R} [CommRing R] {a₁ a₂ b₁ b₂ : R}
  proof: by
  subst_vars; simp [add_comm]

中文:
定理 neg_add
  结论: {R} [CommRing R] {a₁ a₂ b₁ b₂ : R}
  证明: by
  subst_vars; simp [add_comm]

Depends on / 依赖: add_comm
-/
theorem neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by
  subst_vars; simp [add_comm]

/--
Definition of `evalNeg` / `evalNeg` 的定义

English:
definition evalNeg
  signature: {a : Q($α)} (rα : Q(CommRing $α)) (va : ExSum bt sα a)
  body: match va with
  | .zero => do
    assumeInstancesCommute
    return ⟨_, .zero, q(neg_zero (R := $α))⟩
  | .add va₁ va₂ => do
    assumeInstancesCommute
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd rc rα va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rα va₂
    return ⟨_, .add vb₁ vb₂, q(neg_add $pb₁ $pb₂)⟩

中文:
定义 evalNeg
  签名: {a : Q($α)} (rα : Q(CommRing $α)) (va : ExSum bt sα a)
  定义体: match va with
  | .zero => do
    assumeInstancesCommute
    return ⟨_, .zero, q(neg_zero (R := $α))⟩
  | .add va₁ va₂ => do
    assumeInstancesCommute
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd rc rα va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rα va₂
    return ⟨_, .add vb₁ vb₂, q(neg_add $pb₁ $pb₂)⟩

Depends on / 依赖: assumeInstancesCommute, evalNeg, evalNegProd, neg_add, neg_zero, return
-/
def evalNeg {a : Q($α)} (rα : Q(CommRing $α)) (va : ExSum bt sα a) :
MetaM Result (ExSum bt sα) q(-$a) :=
  match va with
  | .zero => do
    assumeInstancesCommute
    return ⟨_, .zero, q(neg_zero (R := $α))⟩
  | .add va₁ va₂ => do
    assumeInstancesCommute
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd rc rα va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rα va₂
    return ⟨_, .add vb₁ vb₂, q(neg_add $pb₁ $pb₂)⟩


/--
theorem `sub_pf` / 定理 `sub_pf`

English:
theorem sub_pf
  statement: {R} [CommRing R] {a b c d : R}
  proof: by subst_vars; simp [sub_eq_add_neg]

中文:
定理 sub_pf
  结论: {R} [CommRing R] {a b c d : R}
  证明: by subst_vars; simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem sub_pf {R} [CommRing R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

/--
Definition of `evalSub` / `evalSub` 的定义

English:
definition evalSub
  signature: {a b : Q($α)}
  body: do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcNat va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩

中文:
定义 evalSub
  签名: {a b : Q($α)}
  定义体: do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcNat va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩
-/
def evalSub {a b : Q($α)}
    (rα : Q(CommRing $α)) (va : ExSum bt sα a) (vb : ExSum bt sα b) :
MetaM Result (ExSum bt sα) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcNat va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩


/--
theorem `pow_prod_atom` / 定理 `pow_prod_atom`

English:
theorem pow_prod_atom
  given: (a : R) (b) {e : R} (h : (a + 0) ^ b * (nat_lit 1).rawCast = e)
  proof: by
  simp [← h]

中文:
定理 pow_prod_atom
  条件: (a : R) (b) {e : R} (h : (a + 0) ^ b * (nat_lit 1).rawCast = e)
  证明: by
  simp [← h]
-/
theorem pow_prod_atom (a : R) (b) {e : R} (h : (a + 0) ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e := by
  simp [← h]

/--
Definition of `evalPowProdAtom` / `evalPowProdAtom` 的定义

English:
definition evalPowProdAtom
  signature: {a : Q($α)} {b : Q(Nat)} (va : ExProd bt sα a) (vb : ExProdNat b)
  body: let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd rc vb
  ⟨_, vc, q(pow_prod_atom $a $b $pc)⟩

中文:
定义 evalPowProdAtom
  签名: {a : Q($α)} {b : Q(自然数)} (va : ExProd bt sα a) (vb : ExProd自然数 b)
  定义体: let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd rc vb
  ⟨_, vc, q(pow_prod_atom $a $b $pc)⟩

Depends on / 依赖: ExBase, ExBase.sum, pow_prod_atom, toProd, va.toSum
-/
def evalPowProdAtom {a : Q($α)} {b : Q(Nat)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b) :=
    let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd rc vb
  ⟨_, vc, q(pow_prod_atom $a $b $pc)⟩

/--
theorem `pow_atom` / 定理 `pow_atom`

English:
theorem pow_atom
  given: (a : R) (b) {e : R} (h : a ^ b * (nat_lit 1).rawCast = e)
  proof: by
  simp [← h]

中文:
定理 pow_atom
  条件: (a : R) (b) {e : R} (h : a ^ b * (nat_lit 1).rawCast = e)
  证明: by
  simp [← h]
-/
theorem pow_atom (a : R) (b) {e : R} (h : a ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e + 0 := by
  simp [← h]

/--
Definition of `evalPowAtom` / `evalPowAtom` 的定义

English:
definition evalPowAtom
  signature: {a : Q($α)} {b : Q(Nat)} (va : ExBase bt sα a) (vb : ExProdNat b)
  body: let ⟨_, vc, pc⟩ := (va.toProd rc vb)
  ⟨_, vc.toSum, q(pow_atom $a $b $pc)⟩

中文:
定义 evalPowAtom
  签名: {a : Q($α)} {b : Q(自然数)} (va : ExBase bt sα a) (vb : ExProd自然数 b)
  定义体: let ⟨_, vc, pc⟩ := (va.toProd rc vb)
  ⟨_, vc.toSum, q(pow_atom $a $b $pc)⟩

Depends on / 依赖: pow_atom, toProd, va.toProd, vc.toSum
-/
def evalPowAtom {a : Q($α)} {b : Q(Nat)} (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExSum bt sα) q($a ^ $b) :=
  let ⟨_, vc, pc⟩ := (va.toProd rc vb)
  ⟨_, vc.toSum, q(pow_atom $a $b $pc)⟩

/--
theorem `const_pos` / 定理 `const_pos`

English:
theorem const_pos
  given: (n : Nat) (h : Nat.ble 1 n = true)
  statement: 0 < (n.rawCast : Nat)
  proof: Nat.le_of_ble_eq_true h

中文:
定理 const_pos
  条件: (n : 自然数) (h : 自然数.ble 1 n = true)
  结论: 0 < (n.rawCast : 自然数)
  证明: Nat.le_of_ble_eq_true h

Depends on / 依赖: Nat.le_of_ble_eq_true, le_of_ble_eq_true
-/
theorem const_pos (n : Nat) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : Nat) := Nat.le_of_ble_eq_true h

/--
theorem `mul_exp_pos` / 定理 `mul_exp_pos`

English:
theorem mul_exp_pos
  given: {a₁ a₂ : Nat} (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂)
  statement: 0 < a₁ ^ n * a₂
  proof: Nat.mul_pos (Nat.pow_pos h₁) h₂

中文:
定理 mul_exp_pos
  条件: {a₁ a₂ : 自然数} (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂)
  结论: 0 < a₁ ^ n * a₂
  证明: Nat.mul_pos (Nat.pow_pos h₁) h₂

Depends on / 依赖: Nat.mul_pos, Nat.pow_pos, mul_pos, pow_pos
-/
theorem mul_exp_pos {a₁ a₂ : Nat} (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ :=
  Nat.mul_pos (Nat.pow_pos h₁) h₂

/--
theorem `add_pos_left` / 定理 `add_pos_left`

English:
theorem add_pos_left
  given: {a₁ : Nat} (a₂) (h : 0 < a₁)
  statement: 0 < a₁ + a₂
  proof: Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

中文:
定理 add_pos_left
  条件: {a₁ : 自然数} (a₂) (h : 0 < a₁)
  结论: 0 < a₁ + a₂
  证明: Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

Depends on / 依赖: Nat.le_add_right, Nat.lt_of_lt_of_le, le_add_right, lt_of_lt_of_le
-/
theorem add_pos_left {a₁ : Nat} (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

/--
theorem `add_pos_right` / 定理 `add_pos_right`

English:
theorem add_pos_right
  given: {a₂ : Nat} (a₁) (h : 0 < a₂)
  statement: 0 < a₁ + a₂
  proof: Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual -- partial only to speed up compilation

中文:
定理 add_pos_right
  条件: {a₂ : 自然数} (a₁) (h : 0 < a₂)
  结论: 0 < a₁ + a₂
  证明: Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual -- partial only to speed up compilation

Depends on / 依赖: Nat.le_add_left, Nat.lt_of_lt_of_le, le_add_left, lt_of_lt_of_le
-/
theorem add_pos_right {a₂ : Nat} (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual -- partial only to speed up compilation

/--
Definition of `ExBaseNat.evalPos` / `ExBaseNat.evalPos` 的定义

English:
definition ExBaseNat.evalPos
  signature: {a : Q(Nat)} (va : ExBaseNat a)
  body: match va with
  | .atom _ => none
  | .sum va => va.evalPos

中文:
定义 ExBaseNat.evalPos
  签名: {a : Q(自然数)} (va : ExBase自然数 a)
  定义体: match va with
  | .atom _ => none
  | .sum va => va.evalPos
-/
partial def ExBaseNat.evalPos {a : Q(Nat)} (va : ExBaseNat a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

/--
Definition of `ExProdNat.evalPos` / `ExProdNat.evalPos` 的定义

English:
definition ExProdNat.evalPos
  signature: {a : Q(Nat)} (va : ExProdNat a)
  body: match va with
  | .const _ =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(Nat) := a.appArg!
haveI : a =Q Nat.rawCast lit := ⟨⟩
haveI p : Nat.ble 1 lit =Q true := ⟨⟩
    some q(const_pos $lit $p)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    l

中文:
定义 ExProdNat.evalPos
  签名: {a : Q(自然数)} (va : ExProd自然数 a)
  定义体: match va with
  | .const _ =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(Nat) := a.appArg!
haveI : a =Q Nat.rawCast lit := ⟨⟩
haveI p : Nat.ble 1 lit =Q true := ⟨⟩
    some q(const_pos $lit $p)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    l
-/
partial def ExProdNat.evalPos {a : Q(Nat)} (va : ExProdNat a) : Option Q(0 < $a) :=
  match va with
  | .const _ =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(Nat) := a.appArg!
haveI : a =Q Nat.rawCast lit := ⟨⟩
haveI p : Nat.ble 1 lit =Q true := ⟨⟩
    some q(const_pos $lit $p)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

/--
Definition of `ExSumNat.evalPos` / `ExSumNat.evalPos` 的定义

English:
definition ExSumNat.evalPos
  signature: {a : Q(Nat)} (va : ExSumNat a)
  body: match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

中文:
定义 ExSumNat.evalPos
  签名: {a : Q(自然数)} (va : ExSum自然数 a)
  定义体: match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)
-/
partial def ExSumNat.evalPos {a : Q(Nat)} (va : ExSumNat a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

end

/--
theorem `pow_one` / 定理 `pow_one`

English:
theorem pow_one
  given: (a : R)
  statement: a ^ nat_lit 1 = a
  proof: by simp

中文:
定理 pow_one
  条件: (a : R)
  结论: a ^ nat_lit 1 = a
  证明: by simp
-/
theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp

/--
theorem `pow_bit0` / 定理 `pow_bit0`

English:
theorem pow_bit0
  given: {k : Nat} (_ : (a : R) ^ k = b) (_ : b * b = c)
  proof: by
  subst_vars; simp [Nat.succ_mul, pow_add]

中文:
定理 pow_bit0
  条件: {k : 自然数} (_ : (a : R) ^ k = b) (_ : b * b = c)
  证明: by
  subst_vars; simp [Nat.succ_mul, pow_add]

Depends on / 依赖: Nat.succ_mul, pow_add, succ_mul
-/
theorem pow_bit0 {k : Nat} (_ : (a : R) ^ k = b) (_ : b * b = c) :
    a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]

/--
theorem `pow_bit1` / 定理 `pow_bit1`

English:
theorem pow_bit1
  given: {k : Nat} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d)
  proof: by
  subst_vars; simp [Nat.succ_mul, pow_add]

中文:
定理 pow_bit1
  条件: {k : 自然数} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d)
  证明: by
  subst_vars; simp [Nat.succ_mul, pow_add]

Depends on / 依赖: Nat.succ_mul, pow_add, succ_mul
-/
theorem pow_bit1 {k : Nat} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
    a ^ (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)) = d := by
  subst_vars; simp [Nat.succ_mul, pow_add]

/--
Definition of `evalPowNat` / `evalPowNat` 的定义

English:
definition evalPowNat
  signature: {a : Q($α)} (va : ExSum bt sα a) (n : Q(Nat))
  body: do
  let nn := n.natLit!
  if nn = 1 then
have : n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(Nat) := mkRawNatLit nm
    if nn &&& 1 = 0 then
have : n =Q 2 * m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcNat vb vb


中文:
定义 evalPowNat
  签名: {a : Q($α)} (va : ExSum bt sα a) (n : Q(自然数))
  定义体: do
  let nn := n.natLit!
  if nn = 1 then
have : n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(Nat) := mkRawNatLit nm
    if nn &&& 1 = 0 then
have : n =Q 2 * m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcNat vb vb

-/
partial def evalPowNat {a : Q($α)} (va : ExSum bt sα a) (n : Q(Nat)) :
MetaM Result (ExSum bt sα) q($a ^ $n) := do
  let nn := n.natLit!
  if nn = 1 then
have : n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(Nat) := mkRawNatLit nm
    if nn &&& 1 = 0 then
have : n =Q 2 * m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcNat vb vb
      return ⟨_, vc, q(pow_bit0 $pb $pc)⟩
    else
have : n =Q 2 * m + 1 := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcNat vb vb
      let ⟨_, vd, pd⟩ ← evalMul rc rcNat vc va
      return ⟨_, vd, q(pow_bit1 $pb $pc $pd)⟩

/--
theorem `one_pow` / 定理 `one_pow`

English:
theorem one_pow
  given: {a : R} (b : Nat) (ha : IsNat a 1)
  statement: a ^ b = a
  proof: by
  simp [ha.out]

中文:
定理 one_pow
  条件: {a : R} (b : 自然数) (ha : Is自然数 a 1)
  结论: a ^ b = a
  证明: by
  simp [ha.out]

Depends on / 依赖: ha.out
-/
theorem one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a := by
  simp [ha.out]

/--
theorem `mul_pow` / 定理 `mul_pow`

English:
theorem mul_pow
  statement: {ea₁ b c₁ : Nat} {xa₁ : R}
  proof: by
  subst_vars; simp [_root_.mul_pow, pow_mul]

中文:
定理 mul_pow
  结论: {ea₁ b c₁ : 自然数} {xa₁ : R}
  证明: by
  subst_vars; simp [_root_.mul_pow, pow_mul]

Depends on / 依赖: _root_, _root_.mul_pow, mul_pow, pow_mul
-/
theorem mul_pow {ea₁ b c₁ : Nat} {xa₁ : R}
    (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂ := by
  subst_vars; simp [_root_.mul_pow, pow_mul]

/--
theorem `mul_pow_mul` / 定理 `mul_pow_mul`

English:
theorem mul_pow_mul
  statement: {ea₁ b c₁ : Nat} {xa₁ c₃ d : R} (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂)
  proof: by
  subst_vars; simp [_root_.mul_pow, pow_mul, Nat.rawCast]

中文:
定理 mul_pow_mul
  结论: {ea₁ b c₁ : 自然数} {xa₁ c₃ d : R} (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂)
  证明: by
  subst_vars; simp [_root_.mul_pow, pow_mul, Nat.rawCast]

Depends on / 依赖: Nat.rawCast, _root_, _root_.mul_pow, mul_pow, pow_mul, rawCast
-/
theorem mul_pow_mul {ea₁ b c₁ : Nat} {xa₁ c₃ d : R} (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂)
    (_ : xa₁ ^ c₁ * (nat_lit 1).rawCast = c₃) (_ : c₃ * c₂ = d) :
    (xa₁ ^ ea₁ * a₂ : R) ^ b = d := by
  subst_vars; simp [_root_.mul_pow, pow_mul, Nat.rawCast]

-- needed to lift from `OptionT CoreM` to `OptionT MetaM`
private local instance {m m'} [MonadLiftT m m'] : MonadLiftT (OptionT m) (OptionT m') where
  monadLift x := OptionT.mk x.run

/--
Definition of `evalPowProd` / `evalPowProd` 的定义

English:
definition evalPowProd
  signature: {a : Q($α)} {b : Q(Nat)} (va : ExProd bt sα a) (vb : ExProdNat b)
  body: do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd bt sα) q($a ^ $b)) :=
    match va with
    | va@(.const za) => do
      match rc.isOne za with
      | .some pf =>
        return ⟨_, va, q(one_pow $b $pf)⟩
      | .none =>
        -- NOTE: rc.pow may fail, e.

中文:
定义 evalPowProd
  签名: {a : Q($α)} {b : Q(自然数)} (va : ExProd bt sα a) (vb : ExProd自然数 b)
  定义体: do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd bt sα) q($a ^ $b)) :=
    match va with
    | va@(.const za) => do
      match rc.isOne za with
      | .some pf =>
        return ⟨_, va, q(one_pow $b $pf)⟩
      | .none =>
        -- NOTE: rc.pow may fail, e.
-/
def evalPowProd {a : Q($α)} {b : Q(Nat)} (va : ExProd bt sα a) (vb : ExProdNat b) :
MetaM Result (ExProd bt sα) q($a ^ $b) := do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd bt sα) q($a ^ $b)) :=
    match va with
    | va@(.const za) => do
      match rc.isOne za with
      | .some pf =>
        return ⟨_, va, q(one_pow $b $pf)⟩
      | .none =>
        -- NOTE: rc.pow may fail, e.g. for `ring` when `vb` is not a constant.
        let ⟨_, zc, pc⟩ ← rc.pow za vb
        return ⟨_, .const zc, q($pc)⟩
    | .mul vxa₁ (e := ea₁) vea₁ va₂ => do
      let ⟨ea₁', vea₁'⟩ := vea₁.toExProd
      let ⟨b', vb'⟩ := vb.toExProd
      let ⟨c₁, vc₁, pc₁⟩ ← evalMulProd rcNat rcNat vea₁' vb'
      let ⟨c₁', vc₁'⟩ := vc₁.toExProdNat
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      let ⟨_, vc₃, pc₃⟩ := vxa₁.toProd rc vc₁'
      let ⟨_, vd, pd⟩ ← evalMulProd rc rcNat vc₃ vc₂
have : c₁ =Q c₁' := ⟨⟩
have : b =Q b' := ⟨⟩
have : ea₁ =Q ea₁' := ⟨⟩
      return ⟨_, vd, q(mul_pow_mul $pc₁ $pc₂ $pc₃ $pd)⟩
  return (← res.run).getD (evalPowProdAtom rc va vb)

/--
Definition of `ExtractCoeff` / `ExtractCoeff` 的定义

English:
structure ExtractCoeff
  parameters: (e : Q(Nat))
  axioms and operations (4):
    - k : Q(Nat)
    - e' : Q(Nat)
    - ve' : ExProdNat e'
    - p : Q($e = $e' * $k)

中文:
结构 ExtractCoeff
  参数: (e : Q(自然数))
  公理与运算 (4 个):
    - k : Q(自然数)
    - e' : Q(自然数)
    - ve' : ExProd自然数 e'
    - p : Q($e = $e' * $k)
-/
structure ExtractCoeff (e : Q(Nat)) where
  /-- A raw natural number literal. -/
  k : Q(Nat)
  /-- The result of extracting the coefficient is a monic monomial. -/
  e' : Q(Nat)
  /-- `e'` is a monomial. -/
  ve' : ExProdNat e'
  /-- The proof that `e` splits into the coefficient `k` and the monic monomial `e'`. -/
  p : Q($e = $e' * $k)

/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: (k : Nat) {e : Nat} (h : (nat_lit 1).rawCast = e)
  proof: by simp [← h]

中文:
定理 coeff_one
  条件: (k : 自然数) {e : 自然数} (h : (nat_lit 1).rawCast = e)
  证明: by simp [← h]
-/
theorem coeff_one (k : Nat) {e : Nat} (h : (nat_lit 1).rawCast = e) :
  k.rawCast = e * k := by simp [← h]

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  statement: {a₃ c₂ k : Nat}
  proof: by
  subst_vars; rw [mul_assoc]

中文:
定理 coeff_mul
  结论: {a₃ c₂ k : 自然数}
  证明: by
  subst_vars; rw [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem coeff_mul {a₃ c₂ k : Nat}
    (a₁ a₂ : Nat) (_ : a₃ = c₂ * k) : a₁ ^ a₂ * a₃ = (a₁ ^ a₂ * c₂) * k := by
  subst_vars; rw [mul_assoc]

/--
Definition of `extractCoeff` / `extractCoeff` 的定义

English:
definition extractCoeff
  signature: {a : Q(Nat)} (va : ExProdNat a)
  body: match va with
  | .const _ => Id.run do
    have k : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast k := ⟨⟩
    assumeInstancesCommute
    let ⟨_, one, pf⟩ := rcNat.one
    return ⟨k, _, .const (one), q(coeff_one $k $pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoef

中文:
定义 extractCoeff
  签名: {a : Q(自然数)} (va : ExProd自然数 a)
  定义体: match va with
  | .const _ => Id.run do
    have k : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast k := ⟨⟩
    assumeInstancesCommute
    let ⟨_, one, pf⟩ := rcNat.one
    return ⟨k, _, .const (one), q(coeff_one $k $pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoef

Depends on / 依赖: Id.run, Nat.rawCast, a.appArg, appArg, assumeInstancesCommute, coeff_mul, coeff_one, extractCoeff, rawCast, rcNat.one, return, structural, termination_by
-/
def extractCoeff {a : Q(Nat)} (va : ExProdNat a) : ExtractCoeff a :=
  match va with
  | .const _ => Id.run do
    have k : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast k := ⟨⟩
    assumeInstancesCommute
    let ⟨_, one, pf⟩ := rcNat.one
    return ⟨k, _, .const (one), q(coeff_one $k $pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₃
    ⟨k, _, .mul va₁ va₂ vc, q(coeff_mul $a₁ $a₂ $pc)⟩
termination_by structural a

/--
theorem `pow_one_cast` / 定理 `pow_one_cast`

English:
theorem pow_one_cast
  given: (a : R)
  statement: a ^ (nat_lit 1).rawCast = a
  proof: by simp

中文:
定理 pow_one_cast
  条件: (a : R)
  结论: a ^ (nat_lit 1).rawCast = a
  证明: by simp
-/
theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp

/--
theorem `pow_one_cast_of_isNat` / 定理 `pow_one_cast_of_isNat`

English:
theorem pow_one_cast_of_isNat
  given: (a : R) (b : Nat) (hb : IsNat b 1)
  proof: by simp [hb.out]

中文:
定理 pow_one_cast_of_isNat
  条件: (a : R) (b : 自然数) (hb : Is自然数 b 1)
  证明: by simp [hb.out]

Depends on / 依赖: hb.out
-/
theorem pow_one_cast_of_isNat (a : R) (b : Nat) (hb : IsNat b 1) :
    a ^ b = a := by simp [hb.out]

/--
theorem `zero_pow` / 定理 `zero_pow`

English:
theorem zero_pow
  given: {b : Nat} (_ : 0 < b)
  statement: (0 : R) ^ b = 0
  proof: match b with | b+1 => by simp [pow_succ]

中文:
定理 zero_pow
  条件: {b : 自然数} (_ : 0 < b)
  结论: (0 : R) ^ b = 0
  证明: match b with | b+1 => by simp [pow_succ]

Depends on / 依赖: pow_succ
-/
theorem zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0 := match b with | b+1 => by simp [pow_succ]

/--
theorem `single_pow` / 定理 `single_pow`

English:
theorem single_pow
  given: {b : Nat} (_ : (a : R) ^ b = c)
  statement: (a + 0) ^ b = c + 0
  proof: by
  simp [*]

中文:
定理 single_pow
  条件: {b : 自然数} (_ : (a : R) ^ b = c)
  结论: (a + 0) ^ b = c + 0
  证明: by
  simp [*]
-/
theorem single_pow {b : Nat} (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by
  simp [*]

/--
theorem `pow_nat` / 定理 `pow_nat`

English:
theorem pow_nat
  given: {b c k : Nat} {d e : R} (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e)
  proof: by
  subst_vars; simp [pow_mul]

中文:
定理 pow_nat
  条件: {b c k : 自然数} {d e : R} (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e)
  证明: by
  subst_vars; simp [pow_mul]

Depends on / 依赖: pow_mul
-/
theorem pow_nat {b c k : Nat} {d e : R} (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e) :
    (a : R) ^ b = e := by
  subst_vars; simp [pow_mul]

/--
Definition of `evalPow₁` / `evalPow₁` 的定义

English:
definition evalPow₁
  signature: {a : Q($α)} {b : Q(Nat)} (va : ExSum bt sα a) (vb : ExProdNat b)
  body: do
let notPowOne : MetaM Result (ExSum bt sα) q($a ^ $b) :=
    match va with
    | .zero => do match vb.evalPos with
      | some p => return ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
      | none => return evalPowAtom rc (.sum .zero) vb
    | ExSum.add va .zero => do -- TODO: using `.add` here takes a 

中文:
定义 evalPow₁
  签名: {a : Q($α)} {b : Q(自然数)} (va : ExSum bt sα a) (vb : ExProd自然数 b)
  定义体: do
let notPowOne : MetaM Result (ExSum bt sα) q($a ^ $b) :=
    match va with
    | .zero => do match vb.evalPos with
      | some p => return ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
      | none => return evalPowAtom rc (.sum .zero) vb
    | ExSum.add va .zero => do -- TODO: using `.add` here takes a 
-/
partial def evalPow₁ {a : Q($α)} {b : Q(Nat)} (va : ExSum bt sα a) (vb : ExProdNat b) :
MetaM Result (ExSum bt sα) q($a ^ $b) := do
let notPowOne : MetaM Result (ExSum bt sα) q($a ^ $b) :=
    match va with
    | .zero => do match vb.evalPos with
      | some p => return ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
      | none => return evalPowAtom rc (.sum .zero) vb
    | ExSum.add va .zero => do -- TODO: using `.add` here takes a while to compile?
      let ⟨_, vc, pc⟩ ← evalPowProd rc rcNat va vb
      return ⟨_, vc.toSum, q(single_pow $pc)⟩
    | va => do
      -- FIXME: condition used to be k.coeff > 1. Should go back to something like this.
      let ⟨k, _, vc, pc⟩ := extractCoeff rcNat vb
      if k.natLit! > 1 then
        let ⟨_, vd, pd⟩ ← evalPow₁ va vc
        let ⟨_, ve, pe⟩ ← evalPowNat rc rcNat vd k
        return ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
      else
        return evalPowAtom rc (.sum va) vb
  match vb with
  | .const zb => do
    match rcNat.isOne zb with
    | .some pf =>
      assumeInstancesCommute
      return ⟨_, va, q(pow_one_cast_of_isNat $a _ $pf)⟩
    | .none => notPowOne
  | _ =>
    notPowOne

/--
theorem `pow_zero` / 定理 `pow_zero`

English:
theorem pow_zero
  given: (a : R) {e : R} (h : (nat_lit 1).rawCast = e)
  proof: by simp [← h]

中文:
定理 pow_zero
  条件: (a : R) {e : R} (h : (nat_lit 1).rawCast = e)
  证明: by simp [← h]
-/
theorem pow_zero (a : R) {e : R} (h : (nat_lit 1).rawCast = e) :
    a ^ 0 = e + 0 := by simp [← h]

/--
theorem `pow_add` / 定理 `pow_add`

English:
theorem pow_add
  statement: {b₁ b₂ : Nat} {d : R}
  proof: by
  subst_vars; simp [_root_.pow_add]

中文:
定理 pow_add
  结论: {b₁ b₂ : 自然数} {d : R}
  证明: by
  subst_vars; simp [_root_.pow_add]

Depends on / 依赖: _root_, _root_.pow_add, pow_add
-/
theorem pow_add {b₁ b₂ : Nat} {d : R}
    (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d := by
  subst_vars; simp [_root_.pow_add]

/--
Definition of `evalPow` / `evalPow` 的定义

English:
definition evalPow
  signature: {a : Q($α)} {b : Q(Nat)} (va : ExSum bt sα a) (vb : ExSumNat b)
  body: match vb with
  | .zero => do
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcNat

中文:
定义 evalPow
  签名: {a : Q($α)} {b : Q(自然数)} (va : ExSum bt sα a) (vb : ExSum自然数 b)
  定义体: match vb with
  | .zero => do
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcNat

Depends on / 依赖: ExProd, ExProd.const, assumeInstancesCommute, evalMul, evalPow, pow_add, pow_zero, rc.one, return
-/
def evalPow {a : Q($α)} {b : Q(Nat)} (va : ExSum bt sα a) (vb : ExSumNat b) :
MetaM Result (ExSum bt sα) q($a ^ $b) :=
  match vb with
  | .zero => do
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcNat va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcNat vc₁ vc₂
    return ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

/--
Definition of `Cache` / `Cache` 的定义

English:
structure Cache
  parameters: {α : Q(Type u)} (sα : Q(CommSemiring $α))
  axioms and operations (3):
    - rα : Option Q(CommRing $α)
    - dsα : Option Q(Semifield $α)
    - czα : Option Q(CharZero $α)

中文:
结构 Cache
  参数: {α : Q(类型u)} (sα : Q(CommSemiring $α))
  公理与运算 (3 个):
    - rα : Option Q(CommRing $α)
    - dsα : Option Q(Semifield $α)
    - czα : Option Q(CharZero $α)
-/
structure Cache {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- A ring instance on `α`, if available. -/
  rα : Option Q(CommRing $α)
  /-- A division semiring instance on `α`, if available. -/
  dsα : Option Q(Semifield $α)
  /-- A characteristic zero ring instance on `α`, if available. -/
  czα : Option Q(CharZero $α)

/--
Definition of `mkCache` / `mkCache` 的定义

English:
definition mkCache
  signature: {α : Q(Type u)} (sα : Q(CommSemiring $α))
  body: return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }

中文:
定义 mkCache
  签名: {α : Q(类型u)} (sα : Q(CommSemiring $α))
  定义体: return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }

Depends on / 依赖: CharZero, CommRing, Semifield, return, toOption, trySynthInstanceQ
-/
def mkCache {α : Q(Type u)} (sα : Q(CommSemiring $α)) : MetaM (Cache sα) :=
  return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }

/--
theorem `toProd_pf` / 定理 `toProd_pf`

English:
theorem toProd_pf
  given: (p : (a : R) = a') {e : Nat} (hone : (nat_lit 1).rawCast = e)
  proof: by simp [← hone, *]

中文:
定理 toProd_pf
  条件: (p : (a : R) = a') {e : 自然数} (hone : (nat_lit 1).rawCast = e)
  证明: by simp [← hone, *]
-/
theorem toProd_pf (p : (a : R) = a') {e : Nat} (hone : (nat_lit 1).rawCast = e) :
    a = a' ^ e * (nat_lit 1).rawCast := by simp [← hone, *]

/--
theorem `atom_pf` / 定理 `atom_pf`

English:
theorem atom_pf
  statement: (a : R) {e : Nat} (hone : (nat_lit 1).rawCast = e)
  proof: by
  simp [← hone, ← hb]

中文:
定理 atom_pf
  结论: (a : R) {e : 自然数} (hone : (nat_lit 1).rawCast = e)
  证明: by
  simp [← hone, ← hb]
-/
theorem atom_pf (a : R) {e : Nat} (hone : (nat_lit 1).rawCast = e)
    (hb : a ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by
  simp [← hone, ← hb]

/--
theorem `atom_pf'` / 定理 `atom_pf'`

English:
theorem atom_pf'
  statement: (p : (a : R) = a') {e : Nat} (hone : (nat_lit 1).rawCast = e)
  proof: by simp [← hone, ← hb, *]

中文:
定理 atom_pf'
  结论: (p : (a : R) = a') {e : 自然数} (hone : (nat_lit 1).rawCast = e)
  证明: by simp [← hone, ← hb, *]
-/
theorem atom_pf' (p : (a : R) = a') {e : Nat} (hone : (nat_lit 1).rawCast = e)
    (hb : a' ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by simp [← hone, ← hb, *]

/--
Definition of `evalAtom` / `evalAtom` 的定义

English:
definition evalAtom
  signature: (e : Q($α))
  body: do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ⟨_, one, pf_one⟩ := rcNat.one
  let one := ExProdNat.const (one)
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd rc one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proo

中文:
定义 evalAtom
  签名: (e : Q($α))
  定义体: do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ⟨_, one, pf_one⟩ := rcNat.one
  let one := ExProdNat.const (one)
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd rc one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proo
-/
def evalAtom (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ⟨_, one, pf_one⟩ := rcNat.one
  let one := ExProdNat.const (one)
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd rc one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proof? with
  | none =>
have : e =Q e' := ⟨⟩
    q(atom_pf $e $pf_one $pb)
  | some (p : Q($e = $a')) =>
    q(atom_pf' $p $pf_one $pb)⟩

/--
theorem `inv_mul` / 定理 `inv_mul`

English:
theorem inv_mul
  statement: {R} [Semifield R] {a₁ a₂ a₃ b₁ b₃ c}
  proof: by subst_vars; simp

nonrec theorem inv_zero {R} [Semifield R] : (0 : R)⁻¹ = 0 := inv_zero

中文:
定理 inv_mul
  结论: {R} [Semifield R] {a₁ a₂ a₃ b₁ b₃ c}
  证明: by subst_vars; simp

nonrec theorem inv_zero {R} [Semifield R] : (0 : R)⁻¹ = 0 := inv_zero
-/
theorem inv_mul {R} [Semifield R] {a₁ a₂ a₃ b₁ b₃ c}
    (_ : (a₁⁻¹ : R) = b₁) (_ : (a₃⁻¹ : R) = b₃)
    (_ : b₃ * (b₁ ^ a₂ * (nat_lit 1).rawCast) = c) :
    (a₁ ^ a₂ * a₃ : R)⁻¹ = c := by subst_vars; simp

nonrec theorem inv_zero {R} [Semifield R] : (0 : R)⁻¹ = 0 := inv_zero

/--
theorem `inv_single` / 定理 `inv_single`

English:
theorem inv_single
  statement: {R} [Semifield R] {a b : R}
  proof: by simp [*]

中文:
定理 inv_single
  结论: {R} [Semifield R] {a b : R}
  证明: by simp [*]
-/
theorem inv_single {R} [Semifield R] {a b : R}
    (_ : (a : R)⁻¹ = b) : (a + 0)⁻¹ = b + 0 := by simp [*]
/--
theorem `inv_add` / 定理 `inv_add`

English:
theorem inv_add
  given: {a₁ a₂ : Nat} (_ : ((a₁ : Nat) : R) = b₁) (_ : ((a₂ : Nat) : R) = b₂)
  proof: by
  subst_vars; simp

中文:
定理 inv_add
  条件: {a₁ a₂ : 自然数} (_ : ((a₁ : 自然数) : R) = b₁) (_ : ((a₂ : 自然数) : R) = b₂)
  证明: by
  subst_vars; simp
-/
theorem inv_add {a₁ a₂ : Nat} (_ : ((a₁ : Nat) : R) = b₁) (_ : ((a₂ : Nat) : R) = b₂) :
    ((a₁ + a₂ : Nat) : R) = b₁ + b₂ := by
  subst_vars; simp

section

variable (dsα : Q(Semifield $α))

/--
Definition of `evalInvAtom` / `evalInvAtom` 的定义

English:
definition evalInvAtom
  signature: (a : Q($α))
  body: do
  let (i, ⟨b', _⟩) ← addAtomQ q($a⁻¹)
  pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩

中文:
定义 evalInvAtom
  签名: (a : Q($α))
  定义体: do
  let (i, ⟨b', _⟩) ← addAtomQ q($a⁻¹)
  pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩
-/
def evalInvAtom (a : Q($α)) : AtomM (Result (ExBase bt sα) q($a⁻¹)) := do
  let (i, ⟨b', _⟩) ← addAtomQ q($a⁻¹)
  pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩

/--
Definition of `ExProd.evalInv` / `ExProd.evalInv` 的定义

English:
definition ExProd.evalInv
  signature: {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExProd bt sα a)
  body: Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const c => do
    match ← rc.inv czα q($dsα) c with
    | some ⟨_, vd, pd⟩ => pure ⟨_, .const vd, q($pd)⟩
    | none =>
      let ⟨_, vc, pc⟩ ← evalInvAtom dsα a
      let ⟨_, one, pf⟩ := rcNat.one
      let ⟨_, vc', pc'⟩ := vc.toProd

中文:
定义 ExProd.evalInv
  签名: {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExProd bt sα a)
  定义体: Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const c => do
    match ← rc.inv czα q($dsα) c with
    | some ⟨_, vd, pd⟩ => pure ⟨_, .const vd, q($pd)⟩
    | none =>
      let ⟨_, vc, pc⟩ ← evalInvAtom dsα a
      let ⟨_, one, pf⟩ := rcNat.one
      let ⟨_, vc', pc'⟩ := vc.toProd

Depends on / 依赖: ExProdNat, ExProdNat.const, Lean.Core.checkSystem, checkSystem, decl_name, evalInv, evalInvAtom, rc.inv, rcNat.one, toProd, toProd_pf, toString, vc.toProd
-/
def ExProd.evalInv {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExProd bt sα a) :
    AtomM (Result (ExProd bt sα) q($a⁻¹)) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const c => do
    match ← rc.inv czα q($dsα) c with
    | some ⟨_, vd, pd⟩ => pure ⟨_, .const vd, q($pd)⟩
    | none =>
      let ⟨_, vc, pc⟩ ← evalInvAtom dsα a
      let ⟨_, one, pf⟩ := rcNat.one
      let ⟨_, vc', pc'⟩ := vc.toProd rc (ExProdNat.const (one))
      pure ⟨_, vc', q($pc' ▸ toProd_pf $pc $pf)⟩
  | .mul (x := a₁) (e := _a₂) _va₁ va₂ va₃ => do
    let ⟨_b₁, vb₁, pb₁⟩ ← evalInvAtom dsα a₁
    let ⟨_b₃, vb₃, pb₃⟩ ← va₃.evalInv czα
    let ⟨_b₁', vb₁', pb₁'⟩ := (vb₁.toProd rc va₂)
    let ⟨c, vc, pc⟩ ← evalMulProd rc rcNat vb₃ vb₁'
    assumeInstancesCommute
    pure ⟨c, vc, q(inv_mul $pb₁ $pb₃ ($pb₁' ▸ $pc))⟩

/--
Definition of `ExSum.evalInv` / `ExSum.evalInv` 的定义

English:
definition ExSum.evalInv
  signature: {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExSum bt sα a)
  body: match va with
  | ExSum.zero => pure ⟨_, .zero, (q(inv_zero (R := $α)) : Expr)⟩
  | ExSum.add va ExSum.zero => do
    let ⟨_, vb, pb⟩ ← va.evalInv rc rcNat dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom dsα a
    let ⟨_, one, pf⟩ := rcNat.on

中文:
定义 ExSum.evalInv
  签名: {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExSum bt sα a)
  定义体: match va with
  | ExSum.zero => pure ⟨_, .zero, (q(inv_zero (R := $α)) : Expr)⟩
  | ExSum.add va ExSum.zero => do
    let ⟨_, vb, pb⟩ ← va.evalInv rc rcNat dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom dsα a
    let ⟨_, one, pf⟩ := rcNat.on

Depends on / 依赖: ExProdNat, ExProdNat.const, ExSum.add, ExSum.zero, assumeInstancesCommute, atom_pf, evalInv, evalInvAtom, inv_single, inv_zero, rcNat.one, toProd, va.evalInv, vb.toProd, vb.toSum
-/
def ExSum.evalInv {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExSum bt sα a) :
    AtomM (Result (ExSum bt sα) q($a⁻¹)) :=
  match va with
  | ExSum.zero => pure ⟨_, .zero, (q(inv_zero (R := $α)) : Expr)⟩
  | ExSum.add va ExSum.zero => do
    let ⟨_, vb, pb⟩ ← va.evalInv rc rcNat dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom dsα a
    let ⟨_, one, pf⟩ := rcNat.one
    let ⟨_', vb', pb'⟩ := vb.toProd rc (ExProdNat.const (one))
    assumeInstancesCommute
    pure ⟨_, vb'.toSum, q(atom_pf' $pb $pf $pb')⟩

end

/--
theorem `div_pf` / 定理 `div_pf`

English:
theorem div_pf
  statement: {R} [Semifield R] {a b c d : R}
  proof: by
  subst_vars; simp [div_eq_mul_inv]

中文:
定理 div_pf
  结论: {R} [Semifield R] {a b c d : R}
  证明: by
  subst_vars; simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_pf {R} [Semifield R] {a b c d : R}
    (_ : b⁻¹ = c) (_ : a * c = d) : a / b = d := by
  subst_vars; simp [div_eq_mul_inv]

/--
Definition of `evalDiv` / `evalDiv` 的定义

English:
definition evalDiv
  signature: {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
  body: do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcNat rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcNat va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩

中文:
定义 evalDiv
  签名: {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
  定义体: do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcNat rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcNat va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩
-/
def evalDiv {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
    (va : ExSum bt sα a) (vb : ExSum bt sα b) : AtomM (Result (ExSum bt sα) q($a / $b)) := do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcNat rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcNat va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩

/--
theorem `add_congr` / 定理 `add_congr`

English:
theorem add_congr
  given: (_ : a = a') (_ : b = b') (_ : a' + b' = c)
  statement: (a + b : R) = c
  proof: by
  subst_vars; rfl

中文:
定理 add_congr
  条件: (_ : a = a') (_ : b = b') (_ : a' + b' = c)
  结论: (a + b : R) = c
  证明: by
  subst_vars; rfl
-/
theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl

/--
theorem `mul_congr` / 定理 `mul_congr`

English:
theorem mul_congr
  given: (_ : a = a') (_ : b = b') (_ : a' * b' = c)
  statement: (a * b : R) = c
  proof: by
  subst_vars; rfl

中文:
定理 mul_congr
  条件: (_ : a = a') (_ : b = b') (_ : a' * b' = c)
  结论: (a * b : R) = c
  证明: by
  subst_vars; rfl
-/
theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
  subst_vars; rfl

/--
theorem `nsmul_congr` / 定理 `nsmul_congr`

English:
theorem nsmul_congr
  given: {a a' : Nat} (_ : (a : Nat) = a') (_ : b = b') (_ : a' • b' = c)
  proof: by
  subst_vars; rfl

中文:
定理 nsmul_congr
  条件: {a a' : 自然数} (_ : (a : 自然数) = a') (_ : b = b') (_ : a' • b' = c)
  证明: by
  subst_vars; rfl
-/
theorem nsmul_congr {a a' : Nat} (_ : (a : Nat) = a') (_ : b = b') (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl

/--
theorem `zsmul_congr` / 定理 `zsmul_congr`

English:
theorem zsmul_congr
  statement: {R} [CommRing R] {b b' c : R} {a a' : Int} (_ : (a : Int) = a') (_ : b = b')
  proof: by
  subst_vars; rfl

中文:
定理 zsmul_congr
  结论: {R} [CommRing R] {b b' c : R} {a a' : 整数} (_ : (a : 整数) = a') (_ : b = b')
  证明: by
  subst_vars; rfl
-/
theorem zsmul_congr {R} [CommRing R] {b b' c : R} {a a' : Int} (_ : (a : Int) = a') (_ : b = b')
    (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl

/--
theorem `pow_congr` / 定理 `pow_congr`

English:
theorem pow_congr
  statement: {b b' : Nat} (_ : a = a') (_ : b = b')
  proof: by subst_vars; rfl

中文:
定理 pow_congr
  结论: {b b' : 自然数} (_ : a = a') (_ : b = b')
  证明: by subst_vars; rfl
-/
theorem pow_congr {b b' : Nat} (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl

/--
theorem `neg_congr` / 定理 `neg_congr`

English:
theorem neg_congr
  statement: {R} [CommRing R] {a a' b : R} (_ : a = a')
  proof: by subst_vars; rfl

中文:
定理 neg_congr
  结论: {R} [CommRing R] {a a' b : R} (_ : a = a')
  证明: by subst_vars; rfl
-/
theorem neg_congr {R} [CommRing R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl

/--
theorem `sub_congr` / 定理 `sub_congr`

English:
theorem sub_congr
  statement: {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
  proof: by subst_vars; rfl

中文:
定理 sub_congr
  结论: {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
  证明: by subst_vars; rfl
-/
theorem sub_congr {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl

/--
theorem `inv_congr` / 定理 `inv_congr`

English:
theorem inv_congr
  statement: {R} [Semifield R] {a a' b : R} (_ : a = a')
  proof: by subst_vars; rfl

中文:
定理 inv_congr
  结论: {R} [Semifield R] {a a' b : R} (_ : a = a')
  证明: by subst_vars; rfl
-/
theorem inv_congr {R} [Semifield R] {a a' b : R} (_ : a = a')
    (_ : a'⁻¹ = b) : (a⁻¹ : R) = b := by subst_vars; rfl

/--
theorem `div_congr` / 定理 `div_congr`

English:
theorem div_congr
  statement: {R} [Semifield R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
  proof: by subst_vars; rfl

中文:
定理 div_congr
  结论: {R} [Semifield R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
  证明: by subst_vars; rfl
-/
theorem div_congr {R} [Semifield R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' / b' = c) : (a / b : R) = c := by subst_vars; rfl

/--
theorem `smul_congr` / 定理 `smul_congr`

English:
theorem smul_congr
  statement: {R α : Type*} [CommSemiring α] [SMul R α]
  proof: by
  subst_vars
  simp [*]

中文:
定理 smul_congr
  结论: {R α : 类型} [CommSemiring α] [SMul R α]
  证明: by
  subst_vars
  simp [*]
-/
theorem smul_congr {R α : Type*} [CommSemiring α] [SMul R α]
    {r : R} {a b t c : α}
    (_ : a = b) (_ : forall (x : α), r • x = t * x) (_ : t * b = c) :
    r • a = c := by
  subst_vars
  simp [*]

/--
Definition of `Cache.nat` / `Cache.nat` 的定义

English:
definition Cache.nat
  signature: : Cache sNat
  body: { rα := none, dsα := none, czα := some q(inferInstance) }

中文:
定义 Cache.nat
  签名: : Cache s自然数
  定义体: { rα := none, dsα := none, czα := some q(inferInstance) }
-/
def Cache.nat : Cache sNat := { rα := none, dsα := none, czα := some q(inferInstance) }

-- Note this is not the same as whether the result of `eval` is an atom. (e.g. consider `x + 0`.)
/--
Definition of `isAtomOrDerivable` / `isAtomOrDerivable` 的定义

English:
definition isAtomOrDerivable
  body: do
  let els := try
pure some some (← rc.derive e)
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _
  | ``HSMul.hSMul, _, _
  | ``HPow.hPow, _, _ 

中文:
定义 isAtomOrDerivable
  定义体: do
  let els := try
pure some some (← rc.derive e)
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _
  | ``HSMul.hSMul, _, _
  | ``HPow.hPow, _, _ 
-/
def isAtomOrDerivable
    (c : Cache sα) (e : Q($α)) : AtomM (Option (Option (Result (ExSum bt sα) e))) := do
  let els := try
pure some some (← rc.derive e)
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _
  | ``HSMul.hSMul, _, _
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _
  | ``Neg.neg, some _, _
  | ``HSub.hSub, some _, _ | ``Sub.sub, some _, _
  | ``Inv.inv, _, some _
  | ``HDiv.hDiv, _, some _ | ``Div.div, _, some _ => pure none
  | _, _, _ => els

end

variable (rcNat : RingCompute btNat sNat) in

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.

* `rc` tells us how to normalize constants in `α`.
* `rcℕ` tells us how to normalize constants in exponents.
-/
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {u : Lean.Level}
  body: Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcNat e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
 

中文:
定义 eval
  签名: {u : Lean.Level}
  定义体: Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcNat e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
 
-/
partial def eval {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) -> Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcNat e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalAdd rc rcNat va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalMul rc rcNat va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R _ _ (@instHSMul _ _ $inst) $r $a) =>
      try
        let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
        let ⟨_, vb, pb⟩ ← eval rc c a
        let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _
        let ⟨_, vc, pc⟩ ← evalMul rc rcNat vt vb
        return ⟨_, vc, q(smul_congr $pb $pt $pc)⟩
      catch _ => els
    | _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, pb⟩ ← eval rcNat .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
have : b =Q b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow rc rcNat va vb'
      pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | ``Neg.neg, some rα, _ => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← evalNeg rc rα va
      pure ⟨b, vb, q(neg_congr $pa $p)⟩
    | _ => els
  | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalSub rc rcNat rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← va.evalInv rc rcNat dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalDiv rc rcNat dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els

end Mathlib.Tactic.Ring.Common
