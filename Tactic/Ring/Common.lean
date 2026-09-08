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
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
/-
**Mathlib.Tactic.Ring.Common.s** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring.Co
mmon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
def sℕ : Q(CommSemiring ℕ) := q(Nat.instCommSemiring)

/--
The data used by `ring` to represent coefficients. `e` is a raw rat cast.

We include `e` as a parameter even though it is unused in this definition because it lets us use
`Qq` type annotations in the `RingCompute` structure, and so that it can be used with the `Result`
type defined below.
-/
/-
**Mathlib.Tactic.Ring.Common._root_.Mathlib.Tactic.Ring.RatCoeff** 是 Mathlib 中的一
个结构，位于命名空间 `Mathlib.Tactic.Ring.Common`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data used by `ring` to represent coefficients. `e` is a raw rat cast.

We include `e` as a parameter even though it is unused in this definition becaus
e it lets us use
`Qq` type annotations in the `RingCompute` structure, and so that it can be used
 with the `Result`
type defined below.
-/
structure _root_.Mathlib.Tactic.Ring.RatCoeff {u : Lean.Level} {α : Q(Type u)} (e : Q($α)) where
  /-- The value represented by `e`. Should not be zero. -/
  value : ℚ
  /-- If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  hyp : Option Expr
deriving Inhabited

/-- The data used to represent coefficients in exponents. This is the same data that `ring` uses. -/
/-
**Mathlib.Tactic.Ring.Common.bt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Ring
.Common`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data used to represent coefficients in exponents. This is the same data that
 `ring` uses.
-/
abbrev btℕ (e : Q(ℕ)) : Type := _root_.Mathlib.Tactic.Ring.RatCoeff q($e)
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : Expr) : Inhabited <| btℕ e := ⟨⟨0, none⟩⟩

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
meta inductive ExBaseNat : (e : Q(ℕ)) → Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which `ring` cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `e : Q($α)` contains a representative of this class.
  -/
  | atom {e} (id : ℕ) : ExBaseNat e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSumNat e) : ExBaseNat e

/-- `ExProdNat e` stores the structure of a normalized monomial expression `e : Q(ℕ)`.
A monomial here is a product of powers of `ExBaseNat` expressions, terminated by a (nonzero)
constant coefficient.

Used to represent normalized natural number expressions in exponents.

`ExProdNat q($e)` is equivalent to `ExProd btℕ sℕ q($e)`, and one can cast between the two.
-/
meta inductive ExProdNat : (e : Q(ℕ)) → Type
  /-- A coefficient `value`, holding the data that `ring` uses to represent rational coefficients.
  In this case these happen to always be natural numbers. -/
  | const {e : Q(ℕ)} (value : btℕ e) : ExProdNat e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBaseNat`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {x : Q(ℕ)} {e : Q(ℕ)} {b : Q(ℕ)} :
    ExBaseNat x → ExProdNat e → ExProdNat b → ExProdNat q($x ^ $e * $b)

/-- `ExSumNat e` stores the structure of a normalized polynomial expression `e : Q(ℕ)`, which is
a sum of monomials.

Used to represent normalized natural number expressions in exponents.

`ExSumNat q($e)` is equivalent to `ExSum btℕ sℕ q($e)`, and one can cast between the two. -/
meta inductive ExSumNat : (e : Q(ℕ)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSumNat q(0)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q(ℕ)} : ExProdNat a → ExSumNat b → ExSumNat q($a + $b)
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
meta inductive ExBase {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which a `ring`-like tactic cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `e : Q($α)` contains a representative of this class.
  -/
  | atom {e} (id : ℕ) : ExBase BaseType sα e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSum BaseType sα e) : ExBase BaseType sα e


/-- `ExProd BaseType sα e` stores the structure of a normalized monomial expression `e`.
A monomial here is a product of powers of `ExBase` expressions, terminated by a (nonzero) constant
coefficient. The data of the constant coefficient is stored in the `BaseType`. -/
meta inductive ExProd {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | const {e : Q($α)} (value : BaseType e) : ExProd BaseType sα e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.)
  -/
  | mul {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase BaseType sα x → ExProdNat e → ExProd BaseType sα b → ExProd BaseType sα q($x ^ $e * $b)

/-- `ExSum BaseType sα e` stores the structure of a normalized polynomial expression `e`, which is
a sum of monomials. -/
meta inductive ExSum {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSum BaseType sα q(0 : $α)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q($α)} :
    ExProd BaseType sα a → ExSum BaseType sα b → ExSum BaseType sα q($a + $b)

end

variable {u : Lean.Level}

/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(typically one of `ExSum`, `ExProd`, `ExBase` or `BaseType`) is a (normalized) element `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
-/
/-
**Mathlib.Tactic.Ring.Common.Result** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (Q(«$α») → Type u_1) → Q(«$α») → Type u_1
参数：Type u；Q(«$α») → Type u_1；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of evaluating an (unnormalized) expression `e` into the type family `
E`
(typically one of `ExSum`, `ExProd`, `ExBase` or `BaseType`) is a (normalized) e
lement `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
-/
structure Result {α : Q(Type u)} (E : Q($α) → Type*) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Q(Type u)} {E : Q($α) → Type} {e : Q($α)} [Inhabited (Σ e, E e)] :
    Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩


/-- Defines how comparisons and binary equality are computed in the base type. These are separated
from RingCompute because they can often be defined without using instance caches. -/
/-
**Mathlib.Tactic.Ring.Common.RingCompare** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (Q(«$α») → Type) → Type
参数：Type u；Q(«$α») → Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defines how comparisons and binary equality are computed in the base type. These
 are separated
from RingCompute because they can often be defined without using instance caches
.
-/
structure RingCompare {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type) where
  /-- Returns whether two coefficients are equal -/
  eq : ∀ {x y : Q($α)}, BaseType x → BaseType y → Bool
  /-- Returns whether `x` is less than, equal to or greater than `y`. Can be any total order. -/
  compare : ∀ {x y : Q($α)}, BaseType x → BaseType y → Ordering

/-- Stores all of the normalization procedures on the coefficient type.

`ring` implements these using `norm_num`
`algebra` will implement these using `ring` -/
/-
**Mathlib.Tactic.Ring.Common.RingCompute** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (Q(«$α») → Type) → Q(CommSemiring «$α») → 
Type
参数：Type u；Q(«$α») → Type；CommSemiring «$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stores all of the normalization procedures on the coefficient type.

`ring` implements these using `norm_num`
`algebra` will implement these using `ring`
-/
structure RingCompute {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
  (sα : Q(CommSemiring $α)) extends RingCompare BaseType where
  /-- Evaluate the sum of two coefficients.

  If the result is zero returns a proof of this fact, which is used to remove zero terms. -/
  add {x y : Q($α)} : BaseType x → BaseType y →
    MetaM ((Result BaseType q($x + $y)) × (Option Q(IsNat ($x + $y) 0)))
  /-- Evaluate the product of two coefficients. -/
  mul {x y : Q($α)} : BaseType x → BaseType y → MetaM (Result BaseType q($x * $y))
  /-- Given a commutative ring `β` with a scalar multiplication action on `α` and a `x : β`, cast
  `x` to `α` such that the scalar multiplication turns into normal multiplication. Typically one
  can think of `α` as being an algebra over `β`, but this file does not know about `Algebra`s. -/
  cast (v : Lean.Level) (β : Q(Type v)) (_ : Q(CommSemiring $β))
      (_ : Q(SMul $β $α)) (x : Q($β)) :
    AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(∀ a : $α, $x • a = $y * a))
  /-- Evaluate the negation of a coefficient. -/
  neg {x : Q($α)} (rα : Q(CommRing $α)) : BaseType x → MetaM (Result BaseType q(-$x))
  /-- Raise a coefficient to some natural power.

  The exponent is not necessarily a natural literal. If the tactic can only raise coefficients to
  the power of a literal (e.g. `ring`), it should check for this and return `none` otherwise. -/
  pow {x : Q($α)} {b : Q(ℕ)} : BaseType x → (vb : ExProdNat q($b)) →
    OptionT MetaM (Result BaseType q($x ^ $b))
  /-- Evaluate the inverse of a coefficient. -/
  inv {x : Q($α)} (czα : Option Q(CharZero $α)) (fα : Q(Semifield $α)) : BaseType x →
    AtomM (Option <| Result BaseType q($x⁻¹))
  /-- Evaluate an expression as a potential coefficient. -/
  derive (x : Q($α)) : MetaM (Result (ExSum BaseType sα) q($x))
  /-- Decides whether a coefficient is 1 and returns a proof if so. -/
  isOne {x : Q($α)} : BaseType x → Option Q(NormNum.IsNat $x 1)
  /-- The number 1 represented as a BaseType. -/
  one : Result BaseType q((nat_lit 1).rawCast)
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : CoeOut (RingCompute BaseType sα) (RingCompare BaseType) where
  coe x := x.toRingCompare
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (u : Lean.Level) (α : Q(Type u)) (BaseType : Q($α) → Type) [∀ e, Nonempty (BaseType e)]
    (sα : Q(CommSemiring «$α»)) : Nonempty <|
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
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExBaseNat e) := ⟨default, .atom 0⟩
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExSumNat e) := ⟨_, .zero⟩
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExProdNat e) := ⟨default, .const default⟩

variable {u : Lean.Level} {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)}
   [∀ e, Inhabited (bt e)]
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExBase bt sα e) := ⟨default, .atom 0⟩
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExSum bt sα e) := ⟨_, .zero⟩
/-
**Mathlib.Tactic.Ring.Common.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring.Com
mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Σ e, ExProd bt sα e) := ⟨default, .const default⟩

variable (rc : RingCompute bt sα) (rcℕ : RingCompute btℕ sℕ)

mutual

/-- Cast `ExBaseNat` to `ExBase btℕ sℕ`. -/
/-
**Mathlib.Tactic.Ring.Common.ExBaseNat.toExBase** 是 Mathlib 中的一个不透明定义，位于命名空间 `Ma
thlib.Tactic.Ring.Common.ExBaseNat`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExBaseNat e →     (e' : Q(ℕ)) × 
Mathlib.Tactic.Ring.Common.ExBase Mathlib.Tactic.Ring.Common.btℕ Mathlib.Tactic.
Ring.Common.sℕ e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExBaseNat` to `ExBase btℕ sℕ`.
-/
partial def ExBaseNat.toExBase (e : Q(ℕ)) : ExBaseNat e → Σ e', ExBase btℕ sℕ e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩

/-- Cast `ExProdNat` to `ExProd btℕ sℕ`. -/
/-
**Mathlib.Tactic.Ring.Common.ExProdNat.toExProd** 是 Mathlib 中的一个不透明定义，位于命名空间 `Ma
thlib.Tactic.Ring.Common.ExProdNat`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExProdNat e →     (e' : Q(ℕ)) × 
Mathlib.Tactic.Ring.Common.ExProd Mathlib.Tactic.Ring.Common.btℕ Mathlib.Tactic.
Ring.Common.sℕ e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExProdNat` to `ExProd btℕ sℕ`.
-/
partial def ExProdNat.toExProd (e : Q(ℕ)) : ExProdNat e → Σ e', ExProd btℕ sℕ e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩

/-- Cast `ExSumNat` to `ExSum btℕ sℕ`. -/
/-
**Mathlib.Tactic.Ring.Common.ExSumNat.toExSum** 是 Mathlib 中的一个不透明定义，位于命名空间 `Math
lib.Tactic.Ring.Common.ExSumNat`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExSumNat e →     (e' : Q(ℕ)) × M
athlib.Tactic.Ring.Common.ExSum Mathlib.Tactic.Ring.Common.btℕ Mathlib.Tactic.Ri
ng.Common.sℕ e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExSumNat` to `ExSum btℕ sℕ`.
-/
partial def ExSumNat.toExSum (e : Q(ℕ)) : ExSumNat e → Σ e', ExSum btℕ sℕ e' := fun
  | .zero => ⟨_, .zero (BaseType := btℕ) (sα := sℕ)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩

end

mutual

/-- Cast `ExBase btℕ sℕ` to `ExBaseNat`. -/
/-
**Mathlib.Tactic.Ring.Common.ExBase.toExBaseNat** 是 Mathlib 中的一个不透明定义，位于命名空间 `Ma
thlib.Tactic.Ring.Common.ExBase`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExBase Mathlib.Tactic.Ring.Commo
n.btℕ Mathlib.Tactic.Ring.Common.sℕ e →     (e' : Q(ℕ)) × Mathlib.Tactic.Ring.Co
mmon.ExBaseNat e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExBase btℕ sℕ` to `ExBaseNat`.
-/
partial def ExBase.toExBaseNat (e : Q(ℕ)) : ExBase btℕ sℕ e → Σ e', ExBaseNat e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩

/-- Cast `ExProd btℕ sℕ` to `ExProdNat`. -/
/-
**Mathlib.Tactic.Ring.Common.ExProd.toExProdNat** 是 Mathlib 中的一个不透明定义，位于命名空间 `Ma
thlib.Tactic.Ring.Common.ExProd`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExProd Mathlib.Tactic.Ring.Commo
n.btℕ Mathlib.Tactic.Ring.Common.sℕ e →     (e' : Q(ℕ)) × Mathlib.Tactic.Ring.Co
mmon.ExProdNat e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExProd btℕ sℕ` to `ExProdNat`.
-/
partial def ExProd.toExProdNat (e : Q(ℕ)) : ExProd btℕ sℕ e → Σ e', ExProdNat e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩

/-- Cast `ExSum btℕ sℕ` to `ExSumNat`. -/
/-
**Mathlib.Tactic.Ring.Common.ExSum.toExSumNat** 是 Mathlib 中的一个不透明定义，位于命名空间 `Math
lib.Tactic.Ring.Common.ExSum`。
形式化陈述：(e : Q(ℕ)) →   Mathlib.Tactic.Ring.Common.ExSum Mathlib.Tactic.Ring.Common
.btℕ Mathlib.Tactic.Ring.Common.sℕ e →     (e' : Q(ℕ)) × Mathlib.Tactic.Ring.Com
mon.ExSumNat e'
参数：ℕ；ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `ExSum btℕ sℕ` to `ExSumNat`.
-/
partial def ExSum.toExSumNat (e : Q(ℕ)) : ExSum btℕ sℕ e → Σ e', ExSumNat e' := fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩

end

section

/-- Embed an exponent (an `ExBase, ExProd` pair) as an `ExProd` by multiplying by 1. -/
/-
**Mathlib.Tactic.Ring.Common.ExBase.toProd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.Ring.Common.ExBase`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         {a : Q(«$α»)} →             {b : Q(ℕ)} →               Mathlib.Tactic.R
ing.Common.ExBase bt sα a →                 Mathlib.Tactic.Ring.Common.ExProdNat
 b →                   Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Co
mmon.ExProd bt sα)                     q(«$a» ^ «$b» * Nat.rawCast 1)
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.ExProd bt sα；
«$a» ^ «$b» * Nat.rawCast 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed an exponent (an `ExBase, ExProd` pair) as an `ExProd` by multiplying by 1.
-/
def ExBase.toProd
    {a : Q($α)} {b : Q(ℕ)}
    (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b * (nat_lit 1).rawCast) :=
  let ⟨_, one, pf⟩ := rc.one
  ⟨_, .mul va vb (.const  (one)), q(by rw [← $pf])⟩

/-- Embed `ExProd` in `ExSum` by adding 0. -/
/-
**Mathlib.Tactic.Ring.Common.ExProd.toSum** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         {e : Q(«$α»)} → Mathlib.Tactic.Ring.Common.ExPro
d bt sα e → Mathlib.Tactic.Ring.Common.ExSum bt sα q(«$e» + 0)
参数：Type u；«$α»；CommSemiring «$α»；«$α»；«$e» + 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed `ExProd` in `ExSum` by adding 0.
-/
def ExProd.toSum {e : Q($α)} (v : ExProd bt sα e) : ExSum bt sα q($e + 0) :=
  .add v .zero



-- Partial because the termination checker failed
mutual

variable (rcℕ : RingCompare btℕ)

/-- Equality test for expressions. This is not a `BEq` instance because it is heterogeneous. -/
/-
**Mathlib.Tactic.Ring.Common.ExBase.eq** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common.ExBase`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompare Mathlib.Tactic.Ring.Common.btℕ →   
{u : Level} →     {α : Q(Type u)} →       {bt : Q(«$α») → Type} →         {sα : 
Q(CommSemiring «$α»)} →           Mathlib.Tactic.Ring.Common.RingCompare bt →   
          {a b : Q(«$α»)} →               Mathlib.Tactic.Ring.Common.ExBase bt s
α a → Mathlib.Tactic.Ring.Common.ExBase bt sα b → Bool
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality test for expressions. This is not a `BEq` instance because it is hetero
geneous.
-/
partial def ExBase.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq rc b
  | _, _ => false

@[inherit_doc ExBase.eq]
/-
**Mathlib.Tactic.Ring.Common.ExProd.eq** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common.ExProd`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompare Mathlib.Tactic.Ring.Common.btℕ →   
{u : Level} →     {α : Q(Type u)} →       {bt : Q(«$α») → Type} →         {sα : 
Q(CommSemiring «$α»)} →           Mathlib.Tactic.Ring.Common.RingCompare bt →   
          {a b : Q(«$α»)} →               Mathlib.Tactic.Ring.Common.ExProd bt s
α a → Mathlib.Tactic.Ring.Common.ExProd bt sα b → Bool
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def ExProd.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Bool
  | .const i, .const j => rc.eq i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq rc b₁ && a₂.toExProd.2.eq rcℕ b₂.toExProd.2 && a₃.eq rc b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
/-
**Mathlib.Tactic.Ring.Common.ExSum.eq** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tact
ic.Ring.Common.ExSum`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompare Mathlib.Tactic.Ring.Common.btℕ →   
{u : Level} →     {α : Q(Type u)} →       {bt : Q(«$α») → Type} →         {sα : 
Q(CommSemiring «$α»)} →           Mathlib.Tactic.Ring.Common.RingCompare bt →   
          {a b : Q(«$α»)} → Mathlib.Tactic.Ring.Common.ExSum bt sα a → Mathlib.T
actic.Ring.Common.ExSum bt sα b → Bool
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def ExSum.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq rc b₁ && a₂.eq rc b₂
  | _, _ => false
end

mutual

variable (rcℕ : RingCompute btℕ sℕ)

/--
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
/-
**Mathlib.Tactic.Ring.Common.ExBase.cmp** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.Ring.Common.ExBase`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ Math
lib.Tactic.Ring.Common.sℕ →   {u : Level} →     {α : Q(Type u)} →       {bt : Q(
«$α») → Type} →         {sα : Q(CommSemiring «$α»)} →           Mathlib.Tactic.R
ing.Common.RingCompare bt →             {a b : Q(«$α»)} →               Mathlib.
Tactic.Ring.Common.ExBase bt sα a → Mathlib.Tactic.Ring.Common.ExBase bt sα b → 
Ordering
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
partial def ExBase.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp rc b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
/-
**Mathlib.Tactic.Ring.Common.ExProd.cmp** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.Ring.Common.ExProd`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ Math
lib.Tactic.Ring.Common.sℕ →   {u : Level} →     {α : Q(Type u)} →       {bt : Q(
«$α») → Type} →         {sα : Q(CommSemiring «$α»)} →           Mathlib.Tactic.R
ing.Common.RingCompare bt →             {a b : Q(«$α»)} →               Mathlib.
Tactic.Ring.Common.ExProd bt sα a → Mathlib.Tactic.Ring.Common.ExProd bt sα b → 
Ordering
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def ExProd.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Ordering
  | .const i, .const j => rc.compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ =>
    (a₁.cmp rc b₁).then (a₂.toExProd.2.cmp rcℕ b₂.toExProd.2) |>.then (a₃.cmp rc b₃)
  | .const _, .mul .. => .lt
  | .mul .., .const _ => .gt

@[inherit_doc ExBase.cmp]
/-
**Mathlib.Tactic.Ring.Common.ExSum.cmp** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common.ExSum`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ Math
lib.Tactic.Ring.Common.sℕ →   {u : Level} →     {α : Q(Type u)} →       {bt : Q(
«$α») → Type} →         {sα : Q(CommSemiring «$α»)} →           Mathlib.Tactic.R
ing.Common.RingCompare bt →             {a b : Q(«$α»)} →               Mathlib.
Tactic.Ring.Common.ExSum bt sα a → Mathlib.Tactic.Ring.Common.ExSum bt sα b → Or
dering
参数：Type u；«$α»；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def ExSum.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp rc b₁).then (a₂.cmp rc b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

variable {R : Type*} [CommSemiring R]

section

/-- Get the leading coefficient of an `ExProd`. -/
/-
**Mathlib.Tactic.Ring.Common.ExProd.coeff** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} → {e : Q(«$α»)} → Mathlib.Tactic.Ring.Common.ExProd bt sα 
e → (c : Q(«$α»)) × bt c
参数：Type u；«$α»；CommSemiring «$α»；«$α»；c : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the leading coefficient of an `ExProd`.
-/
def ExProd.coeff {e : Q($α)} :
  ExProd bt sα e → Σ c, bt c
  | .const q => ⟨_, q⟩
  | .mul _ _ v => v.coeff
end

variable (bt) (sα) in
/--
Two monomials are said to "overlap" if they differ by a constant factor, in which case the
constants just add. When this happens, the constant may be either zero (if the monomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
/-
**Mathlib.Tactic.Ring.Common.Overlap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (Q(«$α») → Type) → Q(CommSemiring «$α») → 
Q(«$α») → Type
参数：Type u；Q(«$α») → Type；CommSemiring «$α»；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two monomials are said to "overlap" if they differ by a constant factor, in whic
h case the
constants just add. When this happens, the constant may be either zero (if the m
onomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
inductive Overlap (e : Q($α)) : Type where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExProd bt sα) e)

variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : R}

/-! ### Addition -/

/-
**Mathlib.Tactic.Ring.Common.add_overlap_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b c : R} (x : R) (e : ℕ), a + 
b = c → x ^ e * a + x ^ e * b = x ^ e * c
参数：x : R；e : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Addition
-/
theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]
/-
**Mathlib.Tactic.Ring.Common.add_overlap_pf_zero** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b : R} (x : R) (e : ℕ),   Math
lib.Meta.NormNum.IsNat (a + b) 0 → Mathlib.Meta.NormNum.IsNat (x ^ e * a + x ^ e
 * b) 0
参数：x : R；e : ℕ；a + b；x ^ e * a + x ^ e * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_overlap_pf_zero (x : R) (e) :
    IsNat (a + b) (nat_lit 0) → IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m} [Pure m] : MonadLift Option (OptionT m) where
  monadLift f := .mk <| pure f

/--
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
/-
**Mathlib.Tactic.Ring.Common.evalAddOverlap** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               Mathl
ib.Tactic.Ring.Common.ExProd bt sα a →                 Mathlib.Tactic.Ring.Commo
n.ExProd bt sα b →                   OptionT MetaM (Mathlib.Tactic.Ring.Common.O
verlap bt sα q(«$a» + «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；Mathlib.Tactic.Ring.Common.Overlap bt sα q
(«$a» + «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `
none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
def evalAddOverlap {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    OptionT MetaM (Overlap bt sα q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match (dependent := true) va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add za zb
    match isZero with
    | .some pf => pure <| .zero q($pf)
    | .none =>
      assumeInstancesCommute
      pure <| .nonzero ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    guard (va₁.eq rcℕ rc vb₁ && va₂.toExProd.2.eq rcℕ rcℕ vb₂.toExProd.2)
    have : $a₁ =Q $b₁ := ⟨⟩; have : $a₂ =Q $b₂ := ⟨⟩
    match ← evalAddOverlap va₃ vb₃ with
    | .zero p => pure <| .zero q(add_overlap_pf_zero $a₁ $a₂ $p)
    | .nonzero ⟨_, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul va₁ va₂ vc, q(add_overlap_pf $a₁ $a₂ $p)⟩
  | _, _ => OptionT.fail
/-
**Mathlib.Tactic.Ring.Common.add_pf_zero_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (b : R), 0 + b = b
参数：b : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_pf_zero_add (b : R) : 0 + b = b := by simp
/-
**Mathlib.Tactic.Ring.Common.add_pf_add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), a + 0 = a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_pf_add_zero (a : R) : a + 0 = a := by simp
/-
**Mathlib.Tactic.Ring.Common.add_pf_add_overlap** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b
₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂ + (b₁ + b₂) = c₁ + c₂
参数：b₁ + b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]
/-
**Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Me
ta.NormNum.IsNat (a₁ + b₁) 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) = c
参数：a₁ + b₁；b₁ + b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]
/-
**Mathlib.Tactic.Ring.Common.add_pf_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c
 → a₁ + a₂ + b = a₁ + c
参数：a₁ : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]
/-
**Mathlib.Tactic.Ring.Common.add_pf_add_gt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c
 → a + (b₁ + b₂) = b₁ + c
参数：b₁ : R；b₁ + b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

/-- Adds two polynomials `va, vb` together to get a normalized result polynomial.

* `0 + b = b`
* `a + 0 = a`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
/-
**Mathlib.Tactic.Ring.Common.evalAdd** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tacti
c.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               Mathl
ib.Tactic.Ring.Common.ExSum bt sα a →                 Mathlib.Tactic.Ring.Common
.ExSum bt sα b →                   MetaM (Mathlib.Tactic.Ring.Common.Result (Mat
hlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» + «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；Mathlib.Tactic.Ring.Common.Result (Mathlib
.Tactic.Ring.Common.ExSum bt sα) q(«$a» + «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds two polynomials `va, vb` together to get a normalized result polynomial.

* `0 + b = b`
* `a + 0 = a`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap
`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
partial def evalAdd {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a + $b) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va, vb with
  | .zero, vb => do return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => do return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ => do
    have va := .add va₁ va₂; have vb := .add vb₁ vb₂ -- FIXME: why does `va@(...)` fail?
    match ← (evalAddOverlap rc rcℕ va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp rcℕ rc vb₁ then
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩

/-! ### Multiplication -/

/-
**Mathlib.Tactic.Ring.Common.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), Nat.rawCast 1 * a = a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Multiplication
-/
theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]
/-
**Mathlib.Tactic.Ring.Common.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), a * Nat.rawCast 1 = a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]
/-
**Mathlib.Tactic.Ring.Common.mul_pf_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a
₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂ * c
参数：a₁ : R；a₂ : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) :
    (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]
/-
**Mathlib.Tactic.Ring.Common.mul_pf_right** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a
 * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c
参数：b₁ : R；b₂ : ℕ；b₁ ^ b₂ * b₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) :
    a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]
/-
**Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : 
R),   ea + eb = e → a₂ * b₂ = c → x ^ ea * a₂ * (x ^ eb * b₂) = x ^ e * c
参数：x : R；x ^ eb * b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_pp_pf_overlap {ea eb e : ℕ} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

/-- Multiplies two monomials `va, vb` together to get a normalized result monomial.

* `x * y = (x * y)` (for `x`, `y` coefficients)
* `x * (b₁ * b₂) = b₁ * (b₂ * x)` (for `x` coefficient)
* `(a₁ * a₂) * y = a₁ * (a₂ * y)` (for `y` coefficient)
* `(x ^ ea * a₂) * (x ^ eb * b₂) = x ^ (ea + eb) * (a₂ * b₂)`
  (if `ea` and `eb` are identical except coefficient)
* `(a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂))` (if `a₁.lt b₁`)
* `(a₁ * a₂) * (b₁ * b₂) = b₁ * ((a₁ * a₂) * b₂)` (if not `a₁.lt b₁`)
-/
/-
**Mathlib.Tactic.Ring.Common.evalMulProd** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.T
actic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               Mathl
ib.Tactic.Ring.Common.ExProd bt sα a →                 Mathlib.Tactic.Ring.Commo
n.ExProd bt sα b →                   MetaM (Mathlib.Tactic.Ring.Common.Result (M
athlib.Tactic.Ring.Common.ExProd bt sα) q(«$a» * «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；Mathlib.Tactic.Ring.Common.Result (Mathlib
.Tactic.Ring.Common.ExProd bt sα) q(«$a» * «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplies two monomials `va, vb` together to get a normalized result monomial.

* `x * y = (x * y)` (for `x`, `y` coefficients)
* `x * (b₁ * b₂) = b₁ * (b₂ * x)` (for `x` coefficient)
* `(a₁ * a₂) * y = a₁ * (a₂ * y)` (for `y` coefficient)
* `(x ^ ea * a₂) * (x ^ eb * b₂) = x ^ (ea + eb) * (a₂ * b₂)`
  (if `ea` and `eb` are identical except coefficient)
* `(a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂))` (if `a₁.lt b₁`)
* `(a₁ * a₂) * (b₁ * b₂) = b₁ * ((a₁ * a₂) * b₂)` (if not `a₁.lt b₁`)
-/
partial def evalMulProd {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    MetaM <| Result (ExProd bt sα) q($a * $b) :=
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
    if vxa.eq rcℕ rc vxb then
      have : $xa =Q $xb := ⟨⟩
      if let some (.nonzero ⟨ec', vec', pec'⟩) ← (evalAddOverlap rcℕ rcℕ vea' veb').run then
        let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb₂
        let ⟨ec, vec⟩ := vec'.toExProdNat
        have : $ea =Q $ea' := ⟨⟩
        have : $eb =Q $eb' := ⟨⟩
        have : $ec =Q $ec' := ⟨⟩
        return ⟨_, .mul vxa vec vc, q(mul_pp_pf_overlap $xa $pec' $pc)⟩
    if let .lt := (vxa.cmp rcℕ rc vxb).then (vea'.cmp rcℕ rcℕ veb') then
      let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb
      return ⟨_, .mul vxa vea vc, q(mul_pf_left $xa $ea $pc)⟩
    else
      let ⟨_, vc, pc⟩ ← evalMulProd va vb₂
      return ⟨_, .mul vxb veb vc, q(mul_pf_right $xb $eb $pc)⟩
/-
**Mathlib.Tactic.Ring.Common.mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), a * 0 = 0
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_zero (a : R) : a * 0 = 0 := by simp
/-
**Mathlib.Tactic.Ring.Common.mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ =
 c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * (b₁ + b₂) = d
参数：b₁ + b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by
  subst_vars; simp [_root_.mul_add]

/-- Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polynomial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
/-
**Mathlib.Tactic.Ring.Common.evalMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               Mathl
ib.Tactic.Ring.Common.ExSum bt sα a →                 Mathlib.Tactic.Ring.Common
.ExSum bt sα b →                   MetaM (Mathlib.Tactic.Ring.Common.Result (Mat
hlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» * «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；Mathlib.Tactic.Ring.Common.Result (Mathlib
.Tactic.Ring.Common.ExSum bt sα) q(«$a» * «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polyn
omial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
def evalMul₁ {a b : Q($α)} (va : ExProd bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a * $b) :=
  match vb with
  | .zero => do return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd rc rcℕ va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd rc rcℕ vc₁.toSum vc₂
    return ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩
/-
**Mathlib.Tactic.Ring.Common.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (b : R), 0 * b = 0
参数：b : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_mul (b : R) : 0 * b = 0 := by simp
/-
**Mathlib.Tactic.Ring.Common.add_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b =
 c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂) * b = d
参数：a₁ + a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

/-- Multiplies two polynomials `va, vb` together to get a normalized result polynomial.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
/-
**Mathlib.Tactic.Ring.Common.evalMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               Mathl
ib.Tactic.Ring.Common.ExSum bt sα a →                 Mathlib.Tactic.Ring.Common
.ExSum bt sα b →                   MetaM (Mathlib.Tactic.Ring.Common.Result (Mat
hlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» * «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；Mathlib.Tactic.Ring.Common.Result (Mathlib
.Tactic.Ring.Common.ExSum bt sα) q(«$a» * «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplies two polynomials `va, vb` together to get a normalized result polynomi
al.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
def evalMul {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a * $b) :=
  match va with
  | .zero => do return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcℕ va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

/-! ### Negation -/

/-
**Mathlib.Tactic.Ring.Common.neg_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {a b : R}, -1 * a = b → -a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Negation
-/
theorem neg_one_mul {R} [CommRing R] {a b : R} (_ : (-1 : R) * a = b) :
    -a = b := by subst_vars; simp
/-
**Mathlib.Tactic.Ring.Common.neg_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b
 → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
参数：a₁ : R；a₂ : ℕ；a₁ ^ a₂ * a₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mul {R} [CommRing R] (a₁ : R) (a₂) {a₃ b : R}
    (_ : -a₃ = b) : -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by subst_vars; simp

/-- Negates a monomial `va` to get another monomial.

* `-c = (-c)` (for `c` coefficient)
* `-(a₁ * a₂) = a₁ * -a₂`
-/
/-
**Mathlib.Tactic.Ring.Common.evalNegProd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         {a : Q(«$α»)} →             (rα : Q(CommRing «$α»)) →               Mat
hlib.Tactic.Ring.Common.ExProd bt sα a →                 MetaM (Mathlib.Tactic.R
ing.Common.Result (Mathlib.Tactic.Ring.Common.ExProd bt sα) q(-«$a»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；rα : Q(CommRing «$α»)；Mathlib.Tactic.Ring.
Common.Result (Mathlib.Tactic.Ring.Common.ExProd bt sα) q(-«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negates a monomial `va` to get another monomial.

* `-c = (-c)` (for `c` coefficient)
* `-(a₁ * a₂) = a₁ * -a₂`
-/
def evalNegProd {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a) :
    MetaM <| Result (ExProd bt sα) q(-$a) :=
  Lean.Core.checkSystem decl_name%.toString *>
  match va with
  | .const za => do
    let ⟨b, zb, pb⟩ ← rc.neg q($rα) za
    return ⟨b, .const zb,  q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb, q(neg_mul $a₁ $a₂ $pb)⟩
/-
**Mathlib.Tactic.Ring.Common.neg_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R], -0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_zero {R} [CommRing R] : -(0 : R) = 0 := by simp
/-
**Mathlib.Tactic.Ring.Common.neg_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b
₂ → -(a₁ + a₂) = b₁ + b₂
参数：a₁ + a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by
  subst_vars; simp [add_comm]

/-- Negates a polynomial `va` to get another polynomial.

* `-0 = 0` (for `c` coefficient)
* `-(a₁ + a₂) = -a₁ + -a₂`
-/
/-
**Mathlib.Tactic.Ring.Common.evalNeg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         {a : Q(«$α»)} →             (rα : Q(CommRing «$α»)) →               Mat
hlib.Tactic.Ring.Common.ExSum bt sα a →                 MetaM (Mathlib.Tactic.Ri
ng.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(-«$a»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；rα : Q(CommRing «$α»)；Mathlib.Tactic.Ring.
Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(-«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negates a polynomial `va` to get another polynomial.

* `-0 = 0` (for `c` coefficient)
* `-(a₁ + a₂) = -a₁ + -a₂`
-/
def evalNeg {a : Q($α)} (rα : Q(CommRing $α)) (va : ExSum bt sα a) :
    MetaM <| Result (ExSum bt sα) q(-$a) :=
  match va with
  | .zero => do
    assumeInstancesCommute
    return ⟨_, .zero, q(neg_zero (R := $α))⟩
  | .add va₁ va₂ => do
    assumeInstancesCommute
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd rc rα va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rα va₂
    return ⟨_, .add vb₁ vb₂, q(neg_add $pb₁ $pb₂)⟩

/-! ### Subtraction -/

/-
**Mathlib.Tactic.Ring.Common.sub_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ri
ng.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {a b c d : R}, -b = c → a + c = d → a
 - b = d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Subtraction
-/
theorem sub_pf {R} [CommRing R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

/-- Subtracts two polynomials `va, vb` to get a normalized result polynomial.

* `a - b = a + -b`
-/
/-
**Mathlib.Tactic.Ring.Common.evalSub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               (rα :
 Q(CommRing «$α»)) →                 Mathlib.Tactic.Ring.Common.ExSum bt sα a → 
                  Mathlib.Tactic.Ring.Common.ExSum bt sα b →                    
 MetaM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt s
α) q(«$a» - «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；rα : Q(CommRing «$α»)；Mathlib.Tactic.Ring.
Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» - «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtracts two polynomials `va, vb` to get a normalized result polynomial.

* `a - b = a + -b`
-/
def evalSub {a b : Q($α)}
    (rα : Q(CommRing $α)) (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcℕ va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩

/-! ### Exponentiation -/

/-
**Mathlib.Tactic.Ring.Common.pow_prod_atom** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R) (b : ℕ) {e : R}, (a + 0) 
^ b * Nat.rawCast 1 = e → a ^ b = e
参数：a : R；b : ℕ；a + 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Exponentiation
-/
theorem pow_prod_atom (a : R) (b) {e : R} (h : (a + 0) ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e := by
  simp [← h]

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
/-
**Mathlib.Tactic.Ring.Common.evalPowProdAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         {a : Q(«$α»)} →             {b : Q(ℕ)} →               Mathlib.Tactic.R
ing.Common.ExProd bt sα a →                 Mathlib.Tactic.Ring.Common.ExProdNat
 b →                   Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Co
mmon.ExProd bt sα) q(«$a» ^ «$b»)
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.ExProd bt sα；
«$a» ^ «$b»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to ju
st build an
exponent expression. (This has a slightly different normalization than `evalPowA
tom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
def evalPowProdAtom {a : Q($α)} {b : Q(ℕ)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b) :=
    let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd rc vb
  ⟨_, vc, q(pow_prod_atom $a $b $pc)⟩
/-
**Mathlib.Tactic.Ring.Common.pow_atom** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R) (b : ℕ) {e : R}, a ^ b * 
Nat.rawCast 1 = e → a ^ b = e + 0
参数：a : R；b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_atom (a : R) (b) {e : R} (h : a ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e + 0 := by
  simp [← h]

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
/-
**Mathlib.Tactic.Ring.Common.evalPowAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         {a : Q(«$α»)} →             {b : Q(ℕ)} →               Mathlib.Tactic.R
ing.Common.ExBase bt sα a →                 Mathlib.Tactic.Ring.Common.ExProdNat
 b →                   Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Co
mmon.ExSum bt sα) q(«$a» ^ «$b»)
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.ExSum bt sα；«
$a» ^ «$b»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to ju
st build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
def evalPowAtom {a : Q($α)} {b : Q(ℕ)} (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExSum bt sα) q($a ^ $b) :=
  let ⟨_, vc, pc⟩ := (va.toProd rc vb)
  ⟨_, vc.toSum, q(pow_atom $a $b $pc)⟩
/-
**Mathlib.Tactic.Ring.Common.const_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ (n : ℕ), Nat.ble 1 n = true → 0 < n.rawCast
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
theorem const_pos (n : ℕ) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : ℕ) := Nat.le_of_ble_eq_true h
/-
**Mathlib.Tactic.Ring.Common.mul_exp_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {a₁ a₂ : ℕ} (n : ℕ), 0 < a₁ → 0 < a₂ → 0 < a₁ ^ n * a₂
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
-/
theorem mul_exp_pos {a₁ a₂ : ℕ} (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ :=
  Nat.mul_pos (Nat.pow_pos h₁) h₂
/-
**Mathlib.Tactic.Ring.Common.add_pos_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Ring.Common`。
形式化陈述：∀ {a₁ : ℕ} (a₂ : ℕ), 0 < a₁ → 0 < a₁ + a₂
参数：a₂ : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem add_pos_left {a₁ : ℕ} (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)
/-
**Mathlib.Tactic.Ring.Common.add_pos_right** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：∀ {a₂ : ℕ} (a₁ : ℕ), 0 < a₂ → 0 < a₁ + a₂
参数：a₁ : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem add_pos_right {a₂ : ℕ} (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual -- partial only to speed up compilation

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* Atoms are not (necessarily) positive
* Sums defer to `ExSum.evalPos`
-/
/-
**Mathlib.Tactic.Ring.Common.ExBaseNat.evalPos** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mat
hlib.Tactic.Ring.Common.ExBaseNat`。
形式化陈述：{a : Q(ℕ)} → Mathlib.Tactic.Ring.Common.ExBaseNat a → Option Q(0 < «$a»)
参数：ℕ；0 < «$a»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempts to prove that a polynomial expression in `ℕ` is positive.

* Atoms are not (necessarily) positive
* Sums defer to `ExSum.evalPos`
-/
partial def ExBaseNat.evalPos {a : Q(ℕ)} (va : ExBaseNat a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

/-- Attempts to prove that a monomial expression in `ℕ` is positive.

* `0 < c` (where `c` is a numeral) is true by the normalization invariant (`c` is not zero)
* `0 < x ^ e * b` if `0 < x` and `0 < b`
-/
/-
**Mathlib.Tactic.Ring.Common.ExProdNat.evalPos** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mat
hlib.Tactic.Ring.Common.ExProdNat`。
形式化陈述：{a : Q(ℕ)} → Mathlib.Tactic.Ring.Common.ExProdNat a → Option Q(0 < «$a»)
参数：ℕ；0 < «$a»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempts to prove that a monomial expression in `ℕ` is positive.

* `0 < c` (where `c` is a numeral) is true by the normalization invariant (`c` i
s not zero)
* `0 < x ^ e * b` if `0 < x` and `0 < b`
-/
partial def ExProdNat.evalPos {a : Q(ℕ)} (va : ExProdNat a) : Option Q(0 < $a) :=
  match va with
  | .const _ =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(ℕ) := a.appArg!
    haveI : $a =Q Nat.rawCast $lit := ⟨⟩
    haveI p : Nat.ble 1 $lit =Q true := ⟨⟩
    some q(const_pos $lit $p)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* `0 < 0` fails
* `0 < a + b` if `0 < a` or `0 < b`
-/
/-
**Mathlib.Tactic.Ring.Common.ExSumNat.evalPos** 是 Mathlib 中的一个不透明定义，位于命名空间 `Math
lib.Tactic.Ring.Common.ExSumNat`。
形式化陈述：{a : Q(ℕ)} → Mathlib.Tactic.Ring.Common.ExSumNat a → Option Q(0 < «$a»)
参数：ℕ；0 < «$a»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempts to prove that a polynomial expression in `ℕ` is positive.

* `0 < 0` fails
* `0 < a + b` if `0 < a` or `0 < b`
-/
partial def ExSumNat.evalPos {a : Q(ℕ)} (va : ExSumNat a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

end

/-
**Mathlib.Tactic.Ring.Common.pow_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), a ^ 1 = a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp
/-
**Mathlib.Tactic.Ring.Common.pow_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b c : R} {k : ℕ}, a ^ k = b → 
b * b = c → a ^ Nat.mul 2 k = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_bit0 {k : ℕ} (_ : (a : R) ^ k = b) (_ : b * b = c) :
    a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]
/-
**Mathlib.Tactic.Ring.Common.pow_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a b c : R} {k : ℕ} {d : R},   a 
^ k = b → b * b = c → c * a = d → a ^ (Nat.mul 2 k).add 1 = d
参数：Nat.mul 2 k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_bit1 {k : ℕ} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
    a ^ (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)) = d := by
  subst_vars; simp [Nat.succ_mul, pow_add]

/--
The main case of exponentiation of ring expressions is when `va` is a polynomial and `n` is a
nonzero literal expression, like `(x + y)^5`. In this case we work out the polynomial completely
into a sum of monomials.

* `x ^ 1 = x`
* `x ^ (2*n) = x ^ n * x ^ n`
* `x ^ (2*n+1) = x ^ n * x ^ n * x`
-/
/-
**Mathlib.Tactic.Ring.Common.evalPowNat** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a : Q(«$α»)} →               Mathlib
.Tactic.Ring.Common.ExSum bt sα a →                 (n : Q(ℕ)) →                
   MetaM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt
 sα) q(«$a» ^ «$n»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；n : Q(ℕ)；Mathlib.Tactic.Ring.Common.Result
 (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» ^ «$n»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main case of exponentiation of ring expressions is when `va` is a polynomial
 and `n` is a
nonzero literal expression, like `(x + y)^5`. In this case we work out the polyn
omial completely
into a sum of monomials.

* `x ^ 1 = x`
* `x ^ (2*n) = x ^ n * x ^ n`
* `x ^ (2*n+1) = x ^ n * x ^ n * x`
-/
partial def evalPowNat {a : Q($α)} (va : ExSum bt sα a) (n : Q(ℕ)) :
    MetaM <| Result (ExSum bt sα) q($a ^ $n) := do
  let nn := n.natLit!
  if nn = 1 then
    have : $n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      have : $n =Q 2 * $m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      return ⟨_, vc, q(pow_bit0 $pb $pc)⟩
    else
      have : $n =Q 2 * $m + 1 := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc va
      return ⟨_, vd, q(pow_bit1 $pb $pc $pd)⟩
/-
**Mathlib.Tactic.Ring.Common.one_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a : R} (b : ℕ), Mathlib.Meta.Nor
mNum.IsNat a 1 → a ^ b = a
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_pow {a : R} (b : ℕ) (ha : IsNat a 1) : a ^ b = a := by
  simp [ha.out]
/-
**Mathlib.Tactic.Ring.Common.mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ :
 R},   ea₁ * b = c₁ → a₂ ^ b = c₂ → (xa₁ ^ ea₁ * a₂) ^ b = xa₁ ^ c₁ * c₂
参数：xa₁ ^ ea₁ * a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_pow {ea₁ b c₁ : ℕ} {xa₁ : R}
    (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂ := by
  subst_vars; simp [_root_.mul_pow, pow_mul]
/-
**Mathlib.Tactic.Ring.Common.mul_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c
₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂ → xa₁ ^ c₁ * Nat.rawCast 1 = c₃ → c₃ * c₂
 = d → (xa₁ ^ ea₁ * a₂) ^ b = d
参数：xa₁ ^ ea₁ * a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_pow_mul {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R} (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂)
    (_ : xa₁ ^ c₁ * (nat_lit 1).rawCast = c₃) (_ : c₃ * c₂ = d) :
    (xa₁ ^ ea₁ * a₂ : R) ^ b = d := by
  subst_vars; simp [_root_.mul_pow, pow_mul, Nat.rawCast]

-- needed to lift from `OptionT CoreM` to `OptionT MetaM`
private local instance {m m'} [MonadLiftT m m'] : MonadLiftT (OptionT m) (OptionT m') where
  monadLift x := OptionT.mk x.run

/-- There are several special cases when exponentiating monomials:

* `1 ^ n = 1`
* `x ^ y = (x ^ y)` when `x` is a constant (Note this may fail if e.g. `y` is not a constant)
* `(a * b) ^ e = a ^ e * b ^ e`

In all other cases we use `evalPowProdAtom`.
-/
/-
**Mathlib.Tactic.Ring.Common.evalPowProd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a : Q(«$α»)} →               {b : Q(
ℕ)} →                 Mathlib.Tactic.Ring.Common.ExProd bt sα a →               
    Mathlib.Tactic.Ring.Common.ExProdNat b →                     MetaM (Mathlib.
Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExProd bt sα) q(«$a» ^ «$b
»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.Result (Mathl
ib.Tactic.Ring.Common.ExProd bt sα) q(«$a» ^ «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are several special cases when exponentiating monomials:

* `1 ^ n = 1`
* `x ^ y = (x ^ y)` when `x` is a constant (Note this may fail if e.g. `y` is no
t a constant)
* `(a * b) ^ e = a ^ e * b ^ e`

In all other cases we use `evalPowProdAtom`.
-/
def evalPowProd {a : Q($α)} {b : Q(ℕ)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    MetaM <| Result (ExProd bt sα) q($a ^ $b) := do
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
      let ⟨c₁, vc₁, pc₁⟩ ← evalMulProd rcℕ rcℕ vea₁' vb'
      let ⟨c₁', vc₁'⟩ := vc₁.toExProdNat
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      let ⟨_, vc₃, pc₃⟩ := vxa₁.toProd rc vc₁'
      let ⟨_, vd, pd⟩ ← evalMulProd rc rcℕ vc₃ vc₂
      have : $c₁ =Q $c₁' := ⟨⟩
      have : $b =Q $b' := ⟨⟩
      have : $ea₁ =Q $ea₁' := ⟨⟩
      return ⟨_, vd, q(mul_pow_mul $pc₁ $pc₂ $pc₃ $pd)⟩
  return (← res.run).getD (evalPowProdAtom rc va vb)

/--
The result of `extractCoeff` is a numeral and a proof that the original expression
factors by this numeral.
-/
/-
**Mathlib.Tactic.Ring.Common.ExtractCoeff** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.T
actic.Ring.Common`。
形式化陈述：Q(ℕ) → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of `extractCoeff` is a numeral and a proof that the original expressi
on
factors by this numeral.
-/
structure ExtractCoeff (e : Q(ℕ)) where
  /-- A raw natural number literal. -/
  k : Q(ℕ)
  /-- The result of extracting the coefficient is a monic monomial. -/
  e' : Q(ℕ)
  /-- `e'` is a monomial. -/
  ve' : ExProdNat e'
  /-- The proof that `e` splits into the coefficient `k` and the monic monomial `e'`. -/
  p : Q($e = $e' * $k)
/-
**Mathlib.Tactic.Ring.Common.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 = e → k.rawCast = e * k
参数：k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_one (k : ℕ) {e : ℕ} (h : (nat_lit 1).rawCast = e) :
  k.rawCast = e * k := by simp [← h]
/-
**Mathlib.Tactic.Ring.Common.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {a₃ c₂ k : ℕ} (a₁ a₂ : ℕ), a₃ = c₂ * k → a₁ ^ a₂ * a₃ = a₁ ^ a₂ * c₂ * k
参数：a₁ a₂ : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_mul {a₃ c₂ k : ℕ}
    (a₁ a₂ : ℕ) (_ : a₃ = c₂ * k) : a₁ ^ a₂ * a₃ = (a₁ ^ a₂ * c₂) * k := by
  subst_vars; rw [mul_assoc]

/-- Given a monomial expression `va`, splits off the leading coefficient `k` and the remainder
`e'`, stored in the `ExtractCoeff` structure.

* `c = 1 * c` (if `c` is a constant)
* `a * b = (a * b') * k` if `b = b' * k`
-/
/-
**Mathlib.Tactic.Ring.Common.extractCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.Ring.Common`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ Math
lib.Tactic.Ring.Common.sℕ →   {a : Q(ℕ)} → Mathlib.Tactic.Ring.Common.ExProdNat 
a → Mathlib.Tactic.Ring.Common.ExtractCoeff a
参数：ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monomial expression `va`, splits off the leading coefficient `k` and the
 remainder
`e'`, stored in the `ExtractCoeff` structure.

* `c = 1 * c` (if `c` is a constant)
* `a * b = (a * b') * k` if `b = b' * k`
-/
def extractCoeff {a : Q(ℕ)} (va : ExProdNat a) : ExtractCoeff a :=
  match va with
  | .const _ => Id.run do
    have k : Q(ℕ) := a.appArg!
    have : $a =Q Nat.rawCast $k := ⟨⟩
    assumeInstancesCommute
    let ⟨_, one, pf⟩ := rcℕ.one
    return ⟨k, _, .const (one), q(coeff_one $k $pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₃
    ⟨k, _, .mul va₁ va₂ vc, q(coeff_mul $a₁ $a₂ $pc)⟩
termination_by structural a
/-
**Mathlib.Tactic.Ring.Common.pow_one_cast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R), a ^ Nat.rawCast 1 = a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp
/-
**Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.Nor
mNum.IsNat b 1 → a ^ b = a
参数：a : R；b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_one_cast_of_isNat (a : R) (b : ℕ) (hb : IsNat b 1) :
    a ^ b = a := by simp [hb.out]
/-
**Mathlib.Tactic.Ring.Common.zero_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {b : ℕ}, 0 < b → 0 ^ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_pow {b : ℕ} (_ : 0 < b) : (0 : R) ^ b = 0 := match b with | b+1 => by simp [pow_succ]
/-
**Mathlib.Tactic.Ring.Common.single_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a c : R} {b : ℕ}, a ^ b = c → (a
 + 0) ^ b = c + 0
参数：a + 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_pow {b : ℕ} (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by
  simp [*]
/-
**Mathlib.Tactic.Ring.Common.pow_nat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a : R} {b c k : ℕ} {d e : R}, b 
= c * k → a ^ c = d → d ^ k = e → a ^ b = e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_nat {b c k : ℕ} {d e : R} (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e) :
    (a : R) ^ b = e := by
  subst_vars; simp [pow_mul]

/-- Exponentiates a polynomial `va` by a monomial `vb`, including several special cases.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 + 0` using `evalPowAtom`.
-/
/-
**Mathlib.Tactic.Ring.Common.evalPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a : Q(«$α»)} →               {b : Q(
ℕ)} →                 Mathlib.Tactic.Ring.Common.ExSum bt sα a →                
   Mathlib.Tactic.Ring.Common.ExSumNat b →                     MetaM (Mathlib.Ta
ctic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» ^ «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.Result (Mathl
ib.Tactic.Ring.Common.ExSum bt sα) q(«$a» ^ «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exponentiates a polynomial `va` by a monomial `vb`, including several special ca
ses.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 + 0` using `evalPowAtom`.
-/
partial def evalPow₁ {a : Q($α)} {b : Q(ℕ)} (va : ExSum bt sα a) (vb : ExProdNat b) :
    MetaM <| Result (ExSum bt sα) q($a ^ $b) := do
  let notPowOne : MetaM <| Result (ExSum bt sα) q($a ^ $b) :=
    match va with
    | .zero => do match vb.evalPos with
      | some p => return ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
      | none => return evalPowAtom rc (.sum .zero) vb
    | ExSum.add va .zero => do -- TODO: using `.add` here takes a while to compile?
      let ⟨_, vc, pc⟩ ← evalPowProd rc rcℕ va vb
      return ⟨_, vc.toSum, q(single_pow $pc)⟩
    | va => do
      -- FIXME: condition used to be k.coeff > 1. Should go back to something like this.
      let ⟨k, _, vc, pc⟩ := extractCoeff rcℕ vb
      if k.natLit! > 1 then
        let ⟨_, vd, pd⟩ ← evalPow₁ va vc
        let ⟨_, ve, pe⟩ ← evalPowNat rc rcℕ vd k
        return ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
      else
        return evalPowAtom rc (.sum va) vb
  match vb with
  | .const zb => do
    match rcℕ.isOne zb with
    | .some pf =>
      assumeInstancesCommute
      return ⟨_, va, q(pow_one_cast_of_isNat $a _ $pf)⟩
    | .none => notPowOne
  | _ =>
    notPowOne
/-
**Mathlib.Tactic.Ring.Common.pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (a : R) {e : R}, Nat.rawCast 1 = 
e → a ^ 0 = e + 0
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_zero (a : R) {e : R} (h : (nat_lit 1).rawCast = e) :
    a ^ 0 = e + 0 := by simp [← h]
/-
**Mathlib.Tactic.Ring.Common.pow_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R}
,   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = d → a ^ (b₁ + b₂) = d
参数：b₁ + b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_add {b₁ b₂ : ℕ} {d : R}
    (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d := by
  subst_vars; simp [_root_.pow_add]

/-- Exponentiates two polynomials `va, vb`.

* `a ^ 0 = 1`
* `a ^ (b₁ + b₂) = a ^ b₁ * a ^ b₂`
-/
/-
**Mathlib.Tactic.Ring.Common.evalPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a : Q(«$α»)} →               {b : Q(
ℕ)} →                 Mathlib.Tactic.Ring.Common.ExSum bt sα a →                
   Mathlib.Tactic.Ring.Common.ExSumNat b →                     MetaM (Mathlib.Ta
ctic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» ^ «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；ℕ；Mathlib.Tactic.Ring.Common.Result (Mathl
ib.Tactic.Ring.Common.ExSum bt sα) q(«$a» ^ «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exponentiates two polynomials `va, vb`.

* `a ^ 0 = 1`
* `a ^ (b₁ + b₂) = a ^ b₁ * a ^ b₂`
-/
def evalPow {a : Q($α)} {b : Q(ℕ)} (va : ExSum bt sα a) (vb : ExSumNat b) :
    MetaM <| Result (ExSum bt sα) q($a ^ $b) :=
  match vb with
  | .zero => do
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ => do
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcℕ va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

/-- This cache contains data required by the `ring` tactic during execution. -/
/-
**Mathlib.Tactic.Ring.Common.Cache** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → Q(CommSemiring «$α») → Type
参数：Type u；CommSemiring «$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This cache contains data required by the `ring` tactic during execution.
-/
structure Cache {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- A ring instance on `α`, if available. -/
  rα : Option Q(CommRing $α)
  /-- A division semiring instance on `α`, if available. -/
  dsα : Option Q(Semifield $α)
  /-- A characteristic zero ring instance on `α`, if available. -/
  czα : Option Q(CharZero $α)

/-- Create a new cache for `α` by doing the necessary instance searches. -/
/-
**Mathlib.Tactic.Ring.Common.mkCache** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (sα : Q(CommSemiring «$α»)) → MetaM (Mathl
ib.Tactic.Ring.Common.Cache sα)
参数：Type u；sα : Q(CommSemiring «$α»)；Mathlib.Tactic.Ring.Common.Cache sα。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a new cache for `α` by doing the necessary instance searches.
-/
def mkCache {α : Q(Type u)} (sα : Q(CommSemiring $α)) : MetaM (Cache sα) :=
  return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }
/-
**Mathlib.Tactic.Ring.Common.toProd_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a a' : R}, a = a' → ∀ {e : ℕ}, N
at.rawCast 1 = e → a = a' ^ e * Nat.rawCast 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toProd_pf (p : (a : R) = a') {e : ℕ} (hone : (nat_lit 1).rawCast = e) :
    a = a' ^ e * (nat_lit 1).rawCast := by simp [← hone, *]
/-
**Mathlib.Tactic.Ring.Common.atom_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {b : R} (a : R) {e : ℕ},   Nat.ra
wCast 1 = e → a ^ e * Nat.rawCast 1 = b → a = b + 0
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem atom_pf (a : R) {e : ℕ} (hone : (nat_lit 1).rawCast = e)
    (hb : a ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by
  simp [← hone, ← hb]
/-
**Mathlib.Tactic.Ring.Common.atom_pf'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a a' b : R},   a = a' → ∀ {e : ℕ
}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCast 1 = b → a = b + 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem atom_pf' (p : (a : R) = a') {e : ℕ} (hone : (nat_lit 1).rawCast = e)
    (hb : a' ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by simp [← hone, ← hb, *]

/--
Evaluates an atom, an expression where `ring` can find no additional structure.

* `a = a ^ 1 * 1 + 0`
-/
/-
**Mathlib.Tactic.Ring.Common.evalAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             (e : Q(«$α»)) →               Mathlib
.Tactic.AtomM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExS
um bt sα) e)
参数：Type u；«$α»；CommSemiring «$α»；e : Q(«$α»)；Mathlib.Tactic.Ring.Common.Result (
Mathlib.Tactic.Ring.Common.ExSum bt sα) e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates an atom, an expression where `ring` can find no additional structure.

* `a = a ^ 1 * 1 + 0`
-/
def evalAtom (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ⟨_, one, pf_one⟩ := rcℕ.one
  let one := ExProdNat.const (one)
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd rc one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proof? with
  | none =>
    have : $e =Q $e' := ⟨⟩
    q(atom_pf $e $pf_one $pb)
  | some (p : Q($e = $a')) =>
    q(atom_pf' $p $pf_one $pb)⟩
/-
**Mathlib.Tactic.Ring.Common.inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_2} [inst : Semifield R] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R}, 
  a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * Nat.rawCast 1) = c → (a₁ ^ a₂ * a₃)⁻¹ 
= c
参数：b₁ ^ a₂ * Nat.rawCast 1；a₁ ^ a₂ * a₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul {R} [Semifield R] {a₁ a₂ a₃ b₁ b₃ c}
    (_ : (a₁⁻¹ : R) = b₁) (_ : (a₃⁻¹ : R) = b₃)
    (_ : b₃ * (b₁ ^ a₂ * (nat_lit 1).rawCast) = c) :
    (a₁ ^ a₂ * a₃ : R)⁻¹ = c := by subst_vars; simp

nonrec theorem inv_zero {R} [Semifield R] : (0 : R)⁻¹ = 0 := inv_zero
/-
**Mathlib.Tactic.Ring.Common.inv_single** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : Semifield R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b +
 0
参数：a + 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_single {R} [Semifield R] {a b : R}
    (_ : (a : R)⁻¹ = b) : (a + 0)⁻¹ = b + 0 := by simp [*]
/-
**Mathlib.Tactic.Ring.Common.inv_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {b₁ b₂ : R} {a₁ a₂ : ℕ}, ↑a₁ = b₁
 → ↑a₂ = b₂ → ↑(a₁ + a₂) = b₁ + b₂
参数：a₁ + a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_add {a₁ a₂ : ℕ} (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) :
    ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by
  subst_vars; simp

section

variable (dsα : Q(Semifield $α))

/-- Applies `⁻¹` to a polynomial to get an atom. -/
/-
**Mathlib.Tactic.Ring.Common.evalInvAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         (dsα : Q(Semifield «$α»)) →           (a : Q(«$α
»)) →             Mathlib.Tactic.AtomM (Mathlib.Tactic.Ring.Common.Result (Mathl
ib.Tactic.Ring.Common.ExBase bt sα) q(«$a»⁻¹))
参数：Type u；«$α»；CommSemiring «$α»；dsα : Q(Semifield «$α»)；a : Q(«$α»)；Mathlib.Tac
tic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExBase bt sα) q(«$a»⁻¹)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `⁻¹` to a polynomial to get an atom.
-/
def evalInvAtom (a : Q($α)) : AtomM (Result (ExBase bt sα) q($a⁻¹)) := do
  let (i, ⟨b', _⟩) ← addAtomQ q($a⁻¹)
  pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩

/-- Inverts a polynomial `va` to get a normalized result polynomial.

* `c⁻¹ = (c⁻¹)` if `c` is a constant
* `(a ^ b * c)⁻¹ = a⁻¹ ^ b * c⁻¹`
-/
/-
**Mathlib.Tactic.Ring.Common.ExProd.evalInv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.Ring.Common.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             (dsα : Q(Semifield «$α»)) →          
     {a : Q(«$α»)} →                 Option Q(CharZero «$α») →                  
 Mathlib.Tactic.Ring.Common.ExProd bt sα a →                     Mathlib.Tactic.
AtomM                       (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.R
ing.Common.ExProd bt sα) q(«$a»⁻¹))
参数：Type u；«$α»；CommSemiring «$α»；dsα : Q(Semifield «$α»)；«$α»；CharZero «$α»；Math
lib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExProd bt sα) q(«$a»⁻¹
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverts a polynomial `va` to get a normalized result polynomial.

* `c⁻¹ = (c⁻¹)` if `c` is a constant
* `(a ^ b * c)⁻¹ = a⁻¹ ^ b * c⁻¹`
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
      let ⟨_, one, pf⟩ := rcℕ.one
      let ⟨_, vc', pc'⟩ := vc.toProd rc (ExProdNat.const (one))
      pure ⟨_, vc', q($pc' ▸ toProd_pf $pc $pf)⟩
  | .mul (x := a₁) (e := _a₂) _va₁ va₂ va₃ => do
    let ⟨_b₁, vb₁, pb₁⟩ ← evalInvAtom dsα a₁
    let ⟨_b₃, vb₃, pb₃⟩ ← va₃.evalInv czα
    let ⟨_b₁', vb₁', pb₁'⟩ := (vb₁.toProd rc va₂)
    let ⟨c, vc, pc⟩ ← evalMulProd rc rcℕ vb₃ vb₁'
    assumeInstancesCommute
    pure ⟨c, vc, q(inv_mul $pb₁ $pb₃ ($pb₁' ▸ $pc))⟩

/-- Inverts a polynomial `va` to get a normalized result polynomial.

* `0⁻¹ = 0`
* `a⁻¹ = (a⁻¹)` if `a` is a nontrivial sum
-/
/-
**Mathlib.Tactic.Ring.Common.ExSum.evalInv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.Ring.Common.ExSum`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             (dsα : Q(Semifield «$α»)) →          
     {a : Q(«$α»)} →                 Option Q(CharZero «$α») →                  
 Mathlib.Tactic.Ring.Common.ExSum bt sα a →                     Mathlib.Tactic.A
tomM                       (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ri
ng.Common.ExSum bt sα) q(«$a»⁻¹))
参数：Type u；«$α»；CommSemiring «$α»；dsα : Q(Semifield «$α»)；«$α»；CharZero «$α»；Math
lib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a»⁻¹)
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverts a polynomial `va` to get a normalized result polynomial.

* `0⁻¹ = 0`
* `a⁻¹ = (a⁻¹)` if `a` is a nontrivial sum
-/
def ExSum.evalInv {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExSum bt sα a) :
    AtomM (Result (ExSum bt sα) q($a⁻¹)) :=
  match va with
  | ExSum.zero => pure ⟨_, .zero, (q(inv_zero (R := $α)) : Expr)⟩
  | ExSum.add va ExSum.zero => do
    let ⟨_, vb, pb⟩ ← va.evalInv rc rcℕ dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom dsα a
    let ⟨_, one, pf⟩ := rcℕ.one
    let ⟨_', vb', pb'⟩ := vb.toProd rc (ExProdNat.const (one))
    assumeInstancesCommute
    pure ⟨_, vb'.toSum, q(atom_pf' $pb $pf $pb')⟩

end

/-
**Mathlib.Tactic.Ring.Common.div_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ri
ng.Common`。
形式化陈述：∀ {R : Type u_2} [inst : Semifield R] {a b c d : R}, b⁻¹ = c → a * c = d →
 a / b = d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_pf {R} [Semifield R] {a b c d : R}
    (_ : b⁻¹ = c) (_ : a * c = d) : a / b = d := by
  subst_vars; simp [div_eq_mul_inv]

/-- Divides two polynomials `va, vb` to get a normalized result polynomial.

* `a / b = a * b⁻¹`
-/
/-
**Mathlib.Tactic.Ring.Common.evalDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ M
athlib.Tactic.Ring.Common.sℕ →             {a b : Q(«$α»)} →               (rα :
 Q(Semifield «$α»)) →                 Option Q(CharZero «$α») →                 
  Mathlib.Tactic.Ring.Common.ExSum bt sα a →                     Mathlib.Tactic.
Ring.Common.ExSum bt sα b →                       Mathlib.Tactic.AtomM          
               (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.Ex
Sum bt sα) q(«$a» / «$b»))
参数：Type u；«$α»；CommSemiring «$α»；«$α»；rα : Q(Semifield «$α»)；CharZero «$α»；Mathl
ib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) q(«$a» / «
$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divides two polynomials `va, vb` to get a normalized result polynomial.

* `a / b = a * b⁻¹`
-/
def evalDiv {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
    (va : ExSum bt sα a) (vb : ExSum bt sα b) : AtomM (Result (ExSum bt sα) q($a / $b)) := do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcℕ rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcℕ va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩
/-
**Mathlib.Tactic.Ring.Common.add_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a a' b b' c : R}, a = a' → b = b
' → a' + b' = c → a + b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.mul_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a a' b b' c : R}, a = a' → b = b
' → a' * b' = c → a * b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
  subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.nsmul_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {b b' c : R} {a a' : ℕ}, a = a' →
 b = b' → a' • b' = c → a • b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nsmul_congr {a a' : ℕ} (_ : (a : ℕ) = a') (_ : b = b') (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.zsmul_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {b b' c : R} {a a' : ℤ}, a = a' → b =
 b' → a' • b' = c → a • b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zsmul_congr {R} [CommRing R] {b b' c : R} {a a' : ℤ} (_ : (a : ℤ) = a') (_ : b = b')
    (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.pow_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a a' c : R} {b b' : ℕ}, a = a' →
 b = b' → a' ^ b' = c → a ^ b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_congr {b b' : ℕ} (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.neg_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {a a' b : R}, a = a' → -a' = b → -a =
 b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem neg_congr {R} [CommRing R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.sub_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {a a' b b' c : R}, a = a' → b = b' → 
a' - b' = c → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sub_congr {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.inv_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : Semifield R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻
¹ = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inv_congr {R} [Semifield R] {a a' b : R} (_ : a = a')
    (_ : a'⁻¹ = b) : (a⁻¹ : R) = b := by subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.div_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Ring.Common`。
形式化陈述：∀ {R : Type u_2} [inst : Semifield R] {a a' b b' c : R}, a = a' → b = b' →
 a' / b' = c → a / b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem div_congr {R} [Semifield R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' / b' = c) : (a / b : R) = c := by subst_vars; rfl
/-
**Mathlib.Tactic.Ring.Common.smul_congr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Ring.Common`。
形式化陈述：∀ {R : Type u_2} {α : Type u_3} [inst : CommSemiring α] [inst_1 : SMul R α
] {r : R} {a b t c : α},   a = b → (∀ (x : α), r • x = t * x) → t * b = c → r • 
a = c
参数：∀ (x : α), r • x = t * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smul_congr {R α : Type*} [CommSemiring α] [SMul R α]
    {r : R} {a b t c : α}
    (_ : a = b) (_ : ∀ (x : α), r • x = t * x) (_ : t * b = c) :
    r • a = c := by
  subst_vars
  simp [*]

/-- A precomputed `Cache` for `ℕ`. -/
/-
**Mathlib.Tactic.Ring.Common.Cache.nat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Ring.Common.Cache`。
形式化陈述：Mathlib.Tactic.Ring.Common.Cache Mathlib.Tactic.Ring.Common.sℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precomputed `Cache` for `ℕ`.
-/
def Cache.nat : Cache sℕ := { rα := none, dsα := none, czα := some q(inferInstance) }

/-- Checks whether `e` would be processed by `eval` as a ring expression,
or otherwise if it is an atom or something simplifiable via `norm_num`.

We use this in `ring_nf` to avoid rewriting atoms unnecessarily.

Returns:
* `none` if `eval` would process `e` as an algebraic ring expression
* `some none` if `eval` would treat `e` as an atom.
* `some (some r)` if `eval` would not process `e` as an algebraic ring expression,
  but `NormNum.derive` can nevertheless simplify `e`, with result `r`.
-/
-- Note this is not the same as whether the result of `eval` is an atom. (e.g. consider `x + 0`.)
/-
**Mathlib.Tactic.Ring.Common.isAtomOrDerivable** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.Ring.Common`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {bt : Q(«$α») → Type} →       {sα : 
Q(CommSemiring «$α»)} →         Mathlib.Tactic.Ring.Common.RingCompute bt sα →  
         Mathlib.Tactic.Ring.Common.Cache sα →             (e : Q(«$α»)) →      
         Mathlib.Tactic.AtomM                 (Option (Option (Mathlib.Tactic.Ri
ng.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) e)))
参数：Type u；«$α»；CommSemiring «$α»；e : Q(«$α»)；Option (Option (Mathlib.Tactic.Ring
.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) e))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isAtomOrDerivable
    (c : Cache sα) (e : Q($α)) : AtomM (Option (Option (Result (ExSum bt sα) e))) := do
  let els := try
      pure <| some <| some (← rc.derive e)
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

variable (rcℕ : RingCompute btℕ sℕ) in

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.

* `rc` tells us how to normalize constants in `α`.
* `rcℕ` tells us how to normalize constants in exponents.
-/
/- Note: Some other functions include similar `match` statement on all valid head symbols. Any
changes to `eval` should be kept in sync:
* `Common.isAtomOrDerivable`
* `Algebra.collectScalarRings`
-/
/-
**Mathlib.Tactic.Ring.Common.eval** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.R
ing.Common`。
形式化陈述：Mathlib.Tactic.Ring.Common.RingCompute Mathlib.Tactic.Ring.Common.btℕ Math
lib.Tactic.Ring.Common.sℕ →   {u : Level} →     {α : Q(Type u)} →       {bt : Q(
«$α») → Type} →         {sα : Q(CommSemiring «$α»)} →           Mathlib.Tactic.R
ing.Common.RingCompute bt sα →             Mathlib.Tactic.Ring.Common.Cache sα →
               (e : Q(«$α»)) →                 Mathlib.Tactic.AtomM (Mathlib.Tac
tic.Ring.Common.Result (Mathlib.Tactic.Ring.Common.ExSum bt sα) e)
参数：Type u；«$α»；CommSemiring «$α»；e : Q(«$α»)；Mathlib.Tactic.Ring.Common.Result (
Mathlib.Tactic.Ring.Common.ExSum bt sα) e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: Some other functions include similar `match` statement on all valid head s
ymbols. Any
changes to `eval` should be kept in sync:
* `Common.isAtomOrDerivable`
* `Algebra.collectScalarRings`
-/
partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcℕ e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R _ _ (@instHSMul _ _ $inst) $r $a) =>
      try
        let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
        let ⟨_, vb, pb⟩ ← eval rc c a
        let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _
        let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vt vb
        return ⟨_, vc, q(smul_congr $pb $pt $pc)⟩
      catch _ => els
    | _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
      have : $b =Q $b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
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
      let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← va.evalInv rc rcℕ dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els

end Mathlib.Tactic.Ring.Common

