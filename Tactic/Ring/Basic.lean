/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
module

public import Mathlib.Tactic.Ring.Common
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat -- for the `Ord Rat` instance

/-!
# `ring` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`n • a`; the multiplier must have type `ℕ` or `ℤ`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The extension to exponents means that something like `2 * 2^n * b = b * 2^(n+1)` can be proved,
even though it is not strictly speaking an equation in the language of commutative rings.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
We use `Mathlib.Tactic.Ring.Common` to implement the normal forms and normalization procedure.

This file defines the evaluation of basic operations such as addition and multiplication of the
rational coefficients as embedded inside the (semi)ring. This is done using `norm_num`.

It further implements the core `ring1` tactic.

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
namespace Ring

open Mathlib.Meta Qq Lean.Meta AtomM
open NormNum hiding Result
open Common (Result)

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

variable {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))

@[expose, reducible, inherit_doc Common.ExBase]
/--
Definition of `ExBase` / `ExBase` 的定义

English:
definition ExBase
  body: Common.ExBase RatCoeff sα
@[expose, reducible, inherit_doc Common.ExProd]

中文:
定义 ExBase
  定义体: Common.ExBase RatCoeff sα
@[expose, reducible, inherit_doc Common.ExProd]

Depends on / 依赖: Common, Common.ExBase, ExBase, RatCoeff
-/
def ExBase := Common.ExBase RatCoeff sα
@[expose, reducible, inherit_doc Common.ExProd]
/--
Definition of `ExProd` / `ExProd` 的定义

English:
definition ExProd
  body: Common.ExProd RatCoeff sα
@[expose, reducible, inherit_doc Common.ExSum]

中文:
定义 ExProd
  定义体: Common.ExProd RatCoeff sα
@[expose, reducible, inherit_doc Common.ExSum]

Depends on / 依赖: Common, Common.ExProd, ExProd, RatCoeff
-/
def ExProd := Common.ExProd RatCoeff sα
@[expose, reducible, inherit_doc Common.ExSum]
/--
Definition of `ExSum` / `ExSum` 的定义

English:
definition ExSum
  body: Common.ExSum RatCoeff sα

中文:
定义 ExSum
  定义体: Common.ExSum RatCoeff sα

Depends on / 依赖: Common, Common.ExSum, RatCoeff
-/
def ExSum := Common.ExSum RatCoeff sα

section
variable {R : Type*} [CommSemiring R] {a : R}

/--
theorem `cast_pos` / 定理 `cast_pos`

English:
theorem cast_pos
  given: {n : Nat}
  statement: IsNat (a : R) n -> a = n.rawCast + 0

中文:
定理 cast_pos
  条件: {n : 自然数}
  结论: 是自然数 (a : R) n -> a = n.rawCast + 0
-/
theorem cast_pos {n : Nat} : IsNat (a : R) n -> a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]

/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  statement: IsNat (a : R) (nat_lit 0) -> a = 0

中文:
定理 cast_zero
  结论: 是自然数 (a : R) (nat_lit 0) -> a = 0
-/
theorem cast_zero : IsNat (a : R) (nat_lit 0) -> a = 0
  | ⟨e⟩ => by simp [e]

/--
theorem `cast_neg` / 定理 `cast_neg`

English:
theorem cast_neg
  given: {n : Nat} {R} [Ring R] {a : R}

中文:
定理 cast_neg
  条件: {n : 自然数} {R} [环 R] {a : R}
-/
theorem cast_neg {n : Nat} {R} [Ring R] {a : R} :
    IsInt a (.negOfNat n) -> a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]

/--
theorem `cast_nnrat` / 定理 `cast_nnrat`

English:
theorem cast_nnrat
  given: {n : Nat} {d : Nat} {R} [DivisionSemiring R] {a : R}

中文:
定理 cast_nnrat
  条件: {n : 自然数} {d : 自然数} {R} [除半环 R] {a : R}
-/
theorem cast_nnrat {n : Nat} {d : Nat} {R} [DivisionSemiring R] {a : R} :
    IsNNRat a n d -> a = NNRat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

/--
theorem `cast_rat` / 定理 `cast_rat`

English:
theorem cast_rat
  given: {n : Int} {d : Nat} {R} [DivisionRing R] {a : R}

中文:
定理 cast_rat
  条件: {n : 整数} {d : 自然数} {R} [除环 R] {a : R}
-/
theorem cast_rat {n : Int} {d : Nat} {R} [DivisionRing R] {a : R} :
    IsRat a n d -> a = Rat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

end

section
/--
Definition of `ExProd.mkNat` / `ExProd.mkNat` 的定义

English:
definition ExProd.mkNat
  signature: (n : Nat)
  body: let lit : Q(Nat) := .lit (.natVal n)
  ⟨q(($lit).rawCast : $α), .const ⟨n, none⟩⟩

中文:
定义 ExProd.mk自然数
  签名: (n : 自然数)
  定义体: let lit : Q(Nat) := .lit (.natVal n)
  ⟨q(($lit).rawCast : $α), .const ⟨n, none⟩⟩

Depends on / 依赖: natVal, rawCast
-/
def ExProd.mkNat (n : Nat) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(Nat) := .lit (.natVal n)
  ⟨q(($lit).rawCast : $α), .const ⟨n, none⟩⟩

/--
Definition of `ExProd.mkNegNat` / `ExProd.mkNegNat` 的定义

English:
definition ExProd.mkNegNat
  signature: (_ : Q(Ring $α)) (n : Nat)
  body: let lit : Q(Nat) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const ⟨(-n), none⟩⟩

中文:
定义 ExProd.mkNeg自然数
  签名: (_ : Q(环 $α)) (n : 自然数)
  定义体: let lit : Q(Nat) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const ⟨(-n), none⟩⟩

Depends on / 依赖: Int.negOfNat, mkRawNatLit, negOfNat, rawCast
-/
def ExProd.mkNegNat (_ : Q(Ring $α)) (n : Nat) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(Nat) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const ⟨(-n), none⟩⟩

/--
Definition of `ExProd.mkNNRat` / `ExProd.mkNNRat` 的定义

English:
definition ExProd.mkNNRat
  signature: (_ : Q(DivisionSemiring $α)) (q : Rat) (n : Q(Nat)) (d : Q(Nat)) (h : Expr)
  body: ⟨q(NNRat.rawCast $n $d : $α), .const ⟨q, h⟩⟩

中文:
定义 ExProd.mkNNRat
  签名: (_ : Q(除半环 $α)) (q : 有理数) (n : Q(自然数)) (d : Q(自然数)) (h : Expr)
  定义体: ⟨q(NNRat.rawCast $n $d : $α), .const ⟨q, h⟩⟩

Depends on / 依赖: NNRat.rawCast, rawCast
-/
def ExProd.mkNNRat (_ : Q(DivisionSemiring $α)) (q : Rat) (n : Q(Nat)) (d : Q(Nat)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(NNRat.rawCast $n $d : $α), .const ⟨q, h⟩⟩

/--
Definition of `ExProd.mkNegNNRat` / `ExProd.mkNegNNRat` 的定义

English:
definition ExProd.mkNegNNRat
  signature: (_ : Q(DivisionRing $α)) (q : Rat) (n : Q(Nat)) (d : Q(Nat)) (h : Expr)
  body: ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const ⟨q, h⟩⟩

中文:
定义 ExProd.mkNegNNRat
  签名: (_ : Q(除环 $α)) (q : 有理数) (n : Q(自然数)) (d : Q(自然数)) (h : Expr)
  定义体: ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const ⟨q, h⟩⟩

Depends on / 依赖: Rat.rawCast, negOfNat, rawCast
-/
def ExProd.mkNegNNRat (_ : Q(DivisionRing $α)) (q : Rat) (n : Q(Nat)) (d : Q(Nat)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const ⟨q, h⟩⟩
end

/--
Definition of `evalCast` / `evalCast` 的定义

English:
definition evalCast
  signature: {α : Q(Type u)} (sα : Q(CommSemiring $α)) {e : Q($α)}
  body: ExProd.mkNat sα lit.natLit!
have : e' =Q ($lit).rawCast := ⟨⟩
    pure ⟨_, s.toSum, q(cast_pos $p)⟩
  /- In the following cases, Qq needs help identifying the `0` in the produced type with the `0`
  in the expected type, which arise from different instances. -/
  | .isNegNat rα lit p =>
    pure ⟨_, (ExProd.mkNegNat sα rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  | .isNNRat dsα q n d p =>
    pure ⟨_, (ExProd.mkNNRat sα dsα q n d q(IsNNRat.den_nz $p)).2.toSum, (q(cast_nnrat $p) : Expr)⟩
  | .isNegNNRat dα q n d p =>
    pure ⟨_, (ExProd.mkNegNNRat sα dα q n d q(IsRat.den_nz $p)).2.toSum, (q(cast_rat $p) : Expr)⟩
  | _ => none

中文:
定义 evalCast
  签名: {α : Q(类型u)} (sα : Q(交换半环 $α)) {e : Q($α)}
  定义体: ExProd.mkNat sα lit.natLit!
have : e' =Q ($lit).rawCast := ⟨⟩
    pure ⟨_, s.toSum, q(cast_pos $p)⟩
  /- In the following cases, Qq needs help identifying the `0` in the produced type with the `0`
  in the expected type, which arise from different instances. -/
  | .isNegNat rα lit p =>
    pure ⟨_, (ExProd.mkNegNat sα rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  | .isNNRat dsα q n d p =>
    pure ⟨_, (ExProd.mkNNRat sα dsα q n d q(IsNNRat.den_nz $p)).2.toSum, (q(cast_nnrat $p) : Expr)⟩
  | .isNegNNRat dα q n d p =>
    pure ⟨_, (ExProd.mkNegNNRat sα dα q n d q(IsRat.den_nz $p)).2.toSum, (q(cast_rat $p) : Expr)⟩
  | _ => none

Depends on / 依赖: ExProd, ExProd.mkNat, lit.natLit, natLit
-/
def evalCast {α : Q(Type u)} (sα : Q(CommSemiring $α)) {e : Q($α)} :
    NormNum.Result e -> Option (Result (ExSum sα) e)
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(cast_zero $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    have ⟨e', s⟩ := ExProd.mkNat sα lit.natLit!
have : e' =Q ($lit).rawCast := ⟨⟩
    pure ⟨_, s.toSum, q(cast_pos $p)⟩
  /- In the following cases, Qq needs help identifying the `0` in the produced type with the `0`
  in the expected type, which arise from different instances. -/
  | .isNegNat rα lit p =>
    pure ⟨_, (ExProd.mkNegNat sα rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  | .isNNRat dsα q n d p =>
    pure ⟨_, (ExProd.mkNNRat sα dsα q n d q(IsNNRat.den_nz $p)).2.toSum, (q(cast_nnrat $p) : Expr)⟩
  | .isNegNNRat dα q n d p =>
    pure ⟨_, (ExProd.mkNegNNRat sα dα q n d q(IsRat.den_nz $p)).2.toSum, (q(cast_rat $p) : Expr)⟩
  | _ => none

section

variable {R : Type*} [CommSemiring R] {n : Nat} {a₁ a₂ a₃ : Nat} {b₁ b₂ b₃ : R}


/--
theorem `natCast_nat` / 定理 `natCast_nat`

English:
theorem natCast_nat
  given: (n)
  statement: ((Nat.rawCast n : Nat) : R) = Nat.rawCast n
  proof: by simp

中文:
定理 natCast_nat
  条件: (n)
  结论: ((自然数.rawCast n : 自然数) : R) = 自然数.rawCast n
  证明: by simp
-/
theorem natCast_nat (n) : ((Nat.rawCast n : Nat) : R) = Nat.rawCast n := by simp

/--
theorem `natCast_mul` / 定理 `natCast_mul`

English:
theorem natCast_mul
  statement: {a₁ a₃ : Nat} (a₂) (_ : ((a₁ : Nat) : R) = b₁)
  proof: by
  subst_vars; simp

中文:
定理 natCast_mul
  结论: {a₁ a₃ : 自然数} (a₂) (_ : ((a₁ : 自然数) : R) = b₁)
  证明: by
  subst_vars; simp
-/
theorem natCast_mul {a₁ a₃ : Nat} (a₂) (_ : ((a₁ : Nat) : R) = b₁)
    (_ : ((a₃ : Nat) : R) = b₃) : ((a₁ ^ a₂ * a₃ : Nat) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp

/--
theorem `natCast_zero` / 定理 `natCast_zero`

English:
theorem natCast_zero
  statement: ((0 : Nat) : R) = 0
  proof: Nat.cast_zero

中文:
定理 natCast_zero
  结论: ((0 : 自然数) : R) = 0
  证明: Nat.cast_zero

Depends on / 依赖: Nat.cast_zero, cast_zero
-/
theorem natCast_zero : ((0 : Nat) : R) = 0 := Nat.cast_zero

/--
theorem `natCast_add` / 定理 `natCast_add`

English:
theorem natCast_add
  statement: {a₁ a₂ : Nat}
  proof: by
  subst_vars; simp

mutual -- partial only to speed up compilation

中文:
定理 natCast_add
  结论: {a₁ a₂ : 自然数}
  证明: by
  subst_vars; simp

mutual -- partial only to speed up compilation
-/
theorem natCast_add {a₁ a₂ : Nat}
    (_ : ((a₁ : Nat) : R) = b₁) (_ : ((a₂ : Nat) : R) = b₂) : ((a₁ + a₂ : Nat) : R) = b₁ + b₂ := by
  subst_vars; simp

mutual -- partial only to speed up compilation

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q Nat) (_ : $sβ =Q inferInstance)

/--
Definition of `ExBase.evalNatCast` / `ExBase.evalNatCast` 的定义

English:
definition ExBase.evalNatCast
  signature: {a : Q(Nat)} (va : ExBase sβ a)
  body: match va with
  | .atom _ => do
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalNatCast va
    pure ⟨_, .sum vc, p⟩

中文:
定义 ExBase.eval自然数Cast
  签名: {a : Q(自然数)} (va : ExBase sβ a)
  定义体: match va with
  | .atom _ => do
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalNatCast va
    pure ⟨_, .sum vc, p⟩
-/
partial def ExBase.evalNatCast {a : Q(Nat)} (va : ExBase sβ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalNatCast va
    pure ⟨_, .sum vc, p⟩

/--
Definition of `ExProd.evalNatCast` / `ExProd.evalNatCast` 的定义

English:
definition ExProd.evalNatCast
  signature: {a : Q(Nat)} (va : ExProd sβ a)
  body: match va with
  | .const ⟨c, hc⟩ =>
    have n : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast n := ⟨⟩
    pure ⟨q(Nat.rawCast $n), .const ⟨c, hc⟩, q(natCast_nat (R := $α) $n)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalNatCast va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalNatCast va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

中文:
定义 ExProd.eval自然数Cast
  签名: {a : Q(自然数)} (va : ExProd sβ a)
  定义体: match va with
  | .const ⟨c, hc⟩ =>
    have n : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast n := ⟨⟩
    pure ⟨q(Nat.rawCast $n), .const ⟨c, hc⟩, q(natCast_nat (R := $α) $n)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalNatCast va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalNatCast va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩
-/
partial def ExProd.evalNatCast {a : Q(Nat)} (va : ExProd sβ a) : AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ =>
    have n : Q(Nat) := a.appArg!
have : a =Q Nat.rawCast n := ⟨⟩
    pure ⟨q(Nat.rawCast $n), .const ⟨c, hc⟩, q(natCast_nat (R := $α) $n)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalNatCast va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalNatCast va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

/--
Definition of `ExSum.evalNatCast` / `ExSum.evalNatCast` 的定义

English:
definition ExSum.evalNatCast
  signature: {a : Q(Nat)} (va : ExSum sβ a)
  body: do
  assumeInstancesCommute
  match (dependent := true) va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalNatCast va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalNatCast va₂
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

中文:
定义 ExSum.eval自然数Cast
  签名: {a : Q(自然数)} (va : ExSum sβ a)
  定义体: do
  assumeInstancesCommute
  match (dependent := true) va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalNatCast va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalNatCast va₂
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩
-/
partial def ExSum.evalNatCast {a : Q(Nat)} (va : ExSum sβ a) : AtomM (Result (ExSum sα) q($a)) := do
  assumeInstancesCommute
  match (dependent := true) va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalNatCast va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalNatCast va₂
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

end


/--
theorem `natCast_int` / 定理 `natCast_int`

English:
theorem natCast_int
  given: {R} [CommRing R] (n)
  statement: ((Nat.rawCast n : Int) : R) = Nat.rawCast n
  proof: by simp

中文:
定理 natCast_int
  条件: {R} [交换环 R] (n)
  结论: ((自然数.rawCast n : 整数) : R) = 自然数.rawCast n
  证明: by simp
-/
theorem natCast_int {R} [CommRing R] (n) : ((Nat.rawCast n : Int) : R) = Nat.rawCast n := by simp

/--
theorem `intCast_negOfNat_Int` / 定理 `intCast_negOfNat_Int`

English:
theorem intCast_negOfNat_Int
  given: {R} [CommRing R] (n)
  proof: by simp

中文:
定理 intCast_negOf自然数_整数
  条件: {R} [交换环 R] (n)
  证明: by simp
-/
theorem intCast_negOfNat_Int {R} [CommRing R] (n) :
    ((Int.rawCast (Int.negOfNat n) : Int) : R) = Int.rawCast (Int.negOfNat n) := by simp

/--
theorem `intCast_mul` / 定理 `intCast_mul`

English:
theorem intCast_mul
  statement: {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : Int} (a₂) (_ : ((a₁ : Int) : R) = b₁)
  proof: by
  subst_vars; simp

中文:
定理 intCast_mul
  结论: {R} [交换环 R] {b₁ b₃ : R} {a₁ a₃ : 整数} (a₂) (_ : ((a₁ : 整数) : R) = b₁)
  证明: by
  subst_vars; simp
-/
theorem intCast_mul {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : Int} (a₂) (_ : ((a₁ : Int) : R) = b₁)
    (_ : ((a₃ : Int) : R) = b₃) : ((a₁ ^ a₂ * a₃ : Int) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp

/--
theorem `intCast_zero` / 定理 `intCast_zero`

English:
theorem intCast_zero
  given: {R} [CommRing R]
  statement: ((0 : Int) : R) = 0
  proof: Int.cast_zero

中文:
定理 intCast_zero
  条件: {R} [交换环 R]
  结论: ((0 : 整数) : R) = 0
  证明: Int.cast_zero

Depends on / 依赖: Int.cast_zero, cast_zero
-/
theorem intCast_zero {R} [CommRing R] : ((0 : Int) : R) = 0 := Int.cast_zero

/--
theorem `intCast_add` / 定理 `intCast_add`

English:
theorem intCast_add
  statement: {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : Int}
  proof: by
  subst_vars; simp


mutual

中文:
定理 intCast_add
  结论: {R} [交换环 R] {b₁ b₂ : R} {a₁ a₂ : 整数}
  证明: by
  subst_vars; simp


mutual
-/
theorem intCast_add {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : Int}
    (_ : ((a₁ : Int) : R) = b₁) (_ : ((a₂ : Int) : R) = b₂) : ((a₁ + a₂ : Int) : R) = b₁ + b₂ := by
  subst_vars; simp


mutual

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q Int) (_ : $sβ =Q inferInstance)

/--
Definition of `ExBase.evalIntCast` / `ExBase.evalIntCast` 的定义

English:
definition ExBase.evalIntCast
  signature: {a : Q(Int)} (rα : Q(CommRing $α)) (va : ExBase sβ a)
  body: match va with
  | .atom _ => do
    assumeInstancesCommute
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalIntCast rα va
    pure ⟨_, .sum vc, p⟩

中文:
定义 ExBase.eval整数Cast
  签名: {a : Q(整数)} (rα : Q(交换环 $α)) (va : ExBase sβ a)
  定义体: match va with
  | .atom _ => do
    assumeInstancesCommute
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalIntCast rα va
    pure ⟨_, .sum vc, p⟩

Depends on / 依赖: Eq.refl, ExSum.evalIntCast, addAtomQ, assumeInstancesCommute, evalIntCast
-/
def ExBase.evalIntCast {a : Q(Int)} (rα : Q(CommRing $α)) (va : ExBase sβ a) :
    AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    assumeInstancesCommute
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalIntCast rα va
    pure ⟨_, .sum vc, p⟩


/--
Definition of `ExProd.evalIntCast` / `ExProd.evalIntCast` 的定义

English:
definition ExProd.evalIntCast
  signature: {a : Q(Int)} (rα : Q(CommRing $α)) (va : ExProd sβ a)
  body: match va with
  | .const ⟨c, hc⟩ => do
    match a with
    | ~q(Nat.rawCast $m) =>
      pure ⟨q(Nat.rawCast $m), .const ⟨c, hc⟩, q(natCast_int (R := $α) $m)⟩
    | ~q(Int.rawCast (Int.negOfNat $m)) =>
      pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const ⟨c, hc⟩, q(intCast_negOfNat_Int (R := $α) $m)⟩
  | .mul (e := a₂) (x := x) (b := b) va₁ va₂ va₃ => do
have : a =Q x ^ a₂ * b := ⟨⟩
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalIntCast rα va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalIntCast rα va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, (q(intCast_mul $a₂ $pb₁ $pb₃))⟩

中文:
定义 ExProd.eval整数Cast
  签名: {a : Q(整数)} (rα : Q(交换环 $α)) (va : ExProd sβ a)
  定义体: match va with
  | .const ⟨c, hc⟩ => do
    match a with
    | ~q(Nat.rawCast $m) =>
      pure ⟨q(Nat.rawCast $m), .const ⟨c, hc⟩, q(natCast_int (R := $α) $m)⟩
    | ~q(Int.rawCast (Int.negOfNat $m)) =>
      pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const ⟨c, hc⟩, q(intCast_negOfNat_Int (R := $α) $m)⟩
  | .mul (e := a₂) (x := x) (b := b) va₁ va₂ va₃ => do
have : a =Q x ^ a₂ * b := ⟨⟩
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalIntCast rα va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalIntCast rα va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, (q(intCast_mul $a₂ $pb₁ $pb₃))⟩

Depends on / 依赖: ExBase, ExBase.evalIntCast, ExProd, ExProd.evalIntCast, Int.negOfNat, Int.rawCast, Nat.rawCast, assumeInstancesCommute, evalIntCast, intCast_negOfNat_Int, natCast_int, negOfNat, rawCast
-/
def ExProd.evalIntCast {a : Q(Int)} (rα : Q(CommRing $α)) (va : ExProd sβ a) :
    AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ => do
    match a with
    | ~q(Nat.rawCast $m) =>
      pure ⟨q(Nat.rawCast $m), .const ⟨c, hc⟩, q(natCast_int (R := $α) $m)⟩
    | ~q(Int.rawCast (Int.negOfNat $m)) =>
      pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const ⟨c, hc⟩, q(intCast_negOfNat_Int (R := $α) $m)⟩
  | .mul (e := a₂) (x := x) (b := b) va₁ va₂ va₃ => do
have : a =Q x ^ a₂ * b := ⟨⟩
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalIntCast rα va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalIntCast rα va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, (q(intCast_mul $a₂ $pb₁ $pb₃))⟩

/--
Definition of `ExSum.evalIntCast` / `ExSum.evalIntCast` 的定义

English:
definition ExSum.evalIntCast
  signature: {a : Q(Int)} (rα : Q(CommRing $α))
  body: match va with
  | .zero => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(intCast_zero)⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalIntCast rα va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalIntCast rα va₂
    assumeInstancesCommute
    pure ⟨_, .add vb₁ vb₂, (q(intCast_add $pb₁ $pb₂))⟩

中文:
定义 ExSum.eval整数Cast
  签名: {a : Q(整数)} (rα : Q(交换环 $α))
  定义体: match va with
  | .zero => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(intCast_zero)⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalIntCast rα va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalIntCast rα va₂
    assumeInstancesCommute
    pure ⟨_, .add vb₁ vb₂, (q(intCast_add $pb₁ $pb₂))⟩

Depends on / 依赖: ExProd, ExProd.evalIntCast, ExSum.evalIntCast, assumeInstancesCommute, evalIntCast, intCast_add, intCast_zero
-/
def ExSum.evalIntCast {a : Q(Int)} (rα : Q(CommRing $α))
    (va : ExSum sβ a) :
    AtomM (Result (ExSum sα) q($a)) :=
  match va with
  | .zero => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(intCast_zero)⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalIntCast rα va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalIntCast rα va₂
    assumeInstancesCommute
    pure ⟨_, .add vb₁ vb₂, (q(intCast_add $pb₁ $pb₂))⟩

end


mutual

/--
Definition of `ExBase.cast` / `ExBase.cast` 的定义

English:
definition ExBase.cast
  body: ExSum.cast a; ⟨_, .sum vb⟩

中文:
定义 ExBase.cast
  定义体: ExSum.cast a; ⟨_, .sum vb⟩

Depends on / 依赖: ExSum.cast
-/
def ExBase.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExBase sα a -> Σ a, ExBase sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := ExSum.cast a; ⟨_, .sum vb⟩

/--
Definition of `ExProd.cast` / `ExProd.cast` 的定义

English:
definition ExProd.cast

中文:
定义 ExProd.cast
-/
def ExProd.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExProd sα a -> Σ a, ExProd sβ a
  | .const ⟨i, h⟩ => ⟨a, .const ⟨i, h⟩⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul (ExBase.cast a₁).2 a₂ (ExProd.cast a₃).2⟩

/--
Definition of `ExSum.cast` / `ExSum.cast` 的定义

English:
definition ExSum.cast

中文:
定义 ExSum.cast
-/
def ExSum.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExSum sα a -> Σ a, ExSum sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add (ExProd.cast a₁).2 (ExSum.cast a₂).2⟩

end

/--
lemma `smul_eq_mul` / 引理 `smul_eq_mul`

English:
lemma smul_eq_mul
  given: {α : Type*} [Mul α] {a a' : α} (h : a = a') (b : α)
  statement: a • b = a' * b
  proof: by
  subst h
  rfl

中文:
引理 smul_eq_mul
  条件: {α : 类型} [乘法 α] {a a' : α} (h : a = a') (b : α)
  结论: a • b = a' * b
  证明: by
  subst h
  rfl
-/
lemma smul_eq_mul {α : Type*} [Mul α] {a a' : α} (h : a = a') (b : α) : a • b = a' * b := by
  subst h
  rfl

/--
theorem `Nat.smul_eq_mul` / 定理 `Nat.smul_eq_mul`

English:
theorem Nat.smul_eq_mul
  given: {n n' : Nat} {r : R} (hr : n = r) (hn : n' = n) (a : R)
  statement: n' • a = r * a
  proof: by
  subst_vars
  simp only [nsmul_eq_mul]

中文:
定理 自然数.smul_eq_mul
  条件: {n n' : 自然数} {r : R} (hr : n = r) (hn : n' = n) (a : R)
  结论: n' • a = r * a
  证明: by
  subst_vars
  simp only [nsmul_eq_mul]

Depends on / 依赖: nsmul_eq_mul
-/
theorem Nat.smul_eq_mul {n n' : Nat} {r : R} (hr : n = r) (hn : n' = n) (a : R) : n' • a = r * a := by
  subst_vars
  simp only [nsmul_eq_mul]

/--
theorem `Int.smul_eq_mul` / 定理 `Int.smul_eq_mul`

English:
theorem Int.smul_eq_mul
  given: {R} {n n' : Int} {r : R} [CommRing R] (hr : n = r) (hn : n' = n) (a : R)
  proof: by
  subst_vars
  simp only [zsmul_eq_mul]

中文:
定理 整数.smul_eq_mul
  条件: {R} {n n' : 整数} {r : R} [交换环 R] (hr : n = r) (hn : n' = n) (a : R)
  证明: by
  subst_vars
  simp only [zsmul_eq_mul]

Depends on / 依赖: zsmul_eq_mul
-/
theorem Int.smul_eq_mul {R} {n n' : Int} {r : R} [CommRing R] (hr : n = r) (hn : n' = n) (a : R) :
    n' • a = r * a := by
  subst_vars
  simp only [zsmul_eq_mul]

/--
Definition of `RatCoeff.toResult` / `RatCoeff.toResult` 的定义

English:
definition RatCoeff.toResult
  signature: {a : Q($α)}

中文:
定义 RatCoeff.toResult
  签名: {a : Q($α)}
-/
def RatCoeff.toResult {a : Q($α)} : RatCoeff a -> NormNum.Result a
| ⟨q, h⟩ => Result.ofRawRat q a h

/--
Definition of `RatCoeff.ofResult` / `RatCoeff.ofResult` 的定义

English:
definition RatCoeff.ofResult
  signature: {a : Q($α)} (res : NormNum.Result a)
  body: do
  let ⟨qc, hc⟩ ← res.toRatNZ
  let ⟨c, pc⟩ := res.toRawEq
  return ⟨q($c), ⟨qc, hc⟩, q($pc)⟩

中文:
定义 RatCoeff.ofResult
  签名: {a : Q($α)} (res : NormNum.Result a)
  定义体: do
  let ⟨qc, hc⟩ ← res.toRatNZ
  let ⟨c, pc⟩ := res.toRawEq
  return ⟨q($c), ⟨qc, hc⟩, q($pc)⟩
-/
def RatCoeff.ofResult {a : Q($α)} (res : NormNum.Result a) : Option Result RatCoeff a := do
  let ⟨qc, hc⟩ ← res.toRatNZ
  let ⟨c, pc⟩ := res.toRawEq
  return ⟨q($c), ⟨qc, hc⟩, q($pc)⟩

namespace RingCompute
mutual

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
  body: do
  let res ← za.toResult.add zb.toResult
  let isZero ← match res with
    | Result.isNat _inst lit pf =>
      if lit.natLit! == 0 then
pure some (pf : Q(IsNat ($a + $b) 0))
      else
        pure none
    | _ => pure none
  let r ← RatCoeff.ofResult res
  return ⟨r, isZero⟩

中文:
定义 add
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α))
  定义体: do
  let res ← za.toResult.add zb.toResult
  let isZero ← match res with
    | Result.isNat _inst lit pf =>
      if lit.natLit! == 0 then
pure some (pf : Q(IsNat ($a + $b) 0))
      else
        pure none
    | _ => pure none
  let r ← RatCoeff.ofResult res
  return ⟨r, isZero⟩
-/
partial def add {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a b : Q($α)} (za : RatCoeff a) (zb : RatCoeff b) :
    MetaM (Result RatCoeff q($a + $b) × Option Q(IsNat ($a + $b) 0)) := do
  let res ← za.toResult.add zb.toResult
  let isZero ← match res with
    | Result.isNat _inst lit pf =>
      if lit.natLit! == 0 then
pure some (pf : Q(IsNat ($a + $b) 0))
      else
        pure none
    | _ => pure none
  let r ← RatCoeff.ofResult res
  return ⟨r, isZero⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
  body: do
  let res ← za.toResult.mul zb.toResult
  return ← RatCoeff.ofResult res

中文:
定义 mul
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α))
  定义体: do
  let res ← za.toResult.mul zb.toResult
  return ← RatCoeff.ofResult res
-/
partial def mul {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a b : Q($α)} (za : RatCoeff a) (zb : RatCoeff b) :
    MetaM (Result RatCoeff q($a * $b)) := do
  let res ← za.toResult.mul zb.toResult
  return ← RatCoeff.ofResult res

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (cα : Common.Cache sα)
  body: do
  let cβ ← Common.mkCache sβ
  let ⟨x', vx, px⟩ ← Common.eval (ringCompute .nat) (ringCompute cβ) cβ x
  if (← isDefEq sα sβ) then
    have : u =QL v := ⟨⟩
have : α =Q β := ⟨⟩
have : sα =Q sβ := ⟨⟩
    let ⟨b, vb⟩ := (ExSum.cast (u := v) (v := u) (sα := sβ) (sβ := sα) vx)
have : b =Q x' := ⟨⟩
    assumeInstancesCommute
    return ⟨_, vb, q(smul_eq_mul $px)⟩
  match v, β, sβ, cα.rα with
  | 0, ~q(Nat), ~q(inferInstance), _ =>
    let ⟨y, vy, py⟩ ← ExSum.evalNatCast sα sβ vx
    assumeInstancesCommute
    return ⟨y, vy, q(Nat.smul_eq_mul $py $px)⟩
  | 0, ~q(Int), ~q(inferInstance), some rα =>
    let ⟨y, vy, py⟩ ← ExSum.evalIntCast sα sβ rα vx
    assumeInstancesCommute
    return ⟨y, vy, q(Int.smul_eq_mul $py $px)⟩
  | _ => failure

中文:
定义 cast
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α)) (cα : Common.Cache sα)
  定义体: do
  let cβ ← Common.mkCache sβ
  let ⟨x', vx, px⟩ ← Common.eval (ringCompute .nat) (ringCompute cβ) cβ x
  if (← isDefEq sα sβ) then
    have : u =QL v := ⟨⟩
have : α =Q β := ⟨⟩
have : sα =Q sβ := ⟨⟩
    let ⟨b, vb⟩ := (ExSum.cast (u := v) (v := u) (sα := sβ) (sβ := sα) vx)
have : b =Q x' := ⟨⟩
    assumeInstancesCommute
    return ⟨_, vb, q(smul_eq_mul $px)⟩
  match v, β, sβ, cα.rα with
  | 0, ~q(Nat), ~q(inferInstance), _ =>
    let ⟨y, vy, py⟩ ← ExSum.evalNatCast sα sβ vx
    assumeInstancesCommute
    return ⟨y, vy, q(Nat.smul_eq_mul $py $px)⟩
  | 0, ~q(Int), ~q(inferInstance), some rα =>
    let ⟨y, vy, py⟩ ← ExSum.evalIntCast sα sβ rα vx
    assumeInstancesCommute
    return ⟨y, vy, q(Int.smul_eq_mul $py $px)⟩
  | _ => failure
-/
partial def cast {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (cα : Common.Cache sα)
    (v : Lean.Level) (β : Q(Type v)) (sβ : Q(CommSemiring $β)) (_smul : Q(SMul $β $α))
    (x : Q($β)) :
    AtomM ((y : Q($α)) × Common.ExSum RatCoeff sα q($y) ×
      Q(forall (a : $α), $x • a = $y * a)) := do
  let cβ ← Common.mkCache sβ
  let ⟨x', vx, px⟩ ← Common.eval (ringCompute .nat) (ringCompute cβ) cβ x
  if (← isDefEq sα sβ) then
    have : u =QL v := ⟨⟩
have : α =Q β := ⟨⟩
have : sα =Q sβ := ⟨⟩
    let ⟨b, vb⟩ := (ExSum.cast (u := v) (v := u) (sα := sβ) (sβ := sα) vx)
have : b =Q x' := ⟨⟩
    assumeInstancesCommute
    return ⟨_, vb, q(smul_eq_mul $px)⟩
  match v, β, sβ, cα.rα with
  | 0, ~q(Nat), ~q(inferInstance), _ =>
    let ⟨y, vy, py⟩ ← ExSum.evalNatCast sα sβ vx
    assumeInstancesCommute
    return ⟨y, vy, q(Nat.smul_eq_mul $py $px)⟩
  | 0, ~q(Int), ~q(inferInstance), some rα =>
    let ⟨y, vy, py⟩ ← ExSum.evalIntCast sα sβ rα vx
    assumeInstancesCommute
    return ⟨y, vy, q(Int.smul_eq_mul $py $px)⟩
  | _ => failure

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: {u : Lean.Level} {α : Q(Type u)}
  body: do
  let res ← za.toResult.neg q(inferInstance)
  -- We have to unpack this result due to instance issues.
  let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
  return ⟨_, vc, q($pc)⟩

中文:
定义 neg
  签名: {u : Lean.Level} {α : Q(类型u)}
  定义体: do
  let res ← za.toResult.neg q(inferInstance)
  -- We have to unpack this result due to instance issues.
  let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
  return ⟨_, vc, q($pc)⟩
-/
partial def neg {u : Lean.Level} {α : Q(Type u)}
    {a : Q($α)} (_crα : Q(CommRing $α)) (za : RatCoeff a) :
    MetaM (Result RatCoeff q(-$a)) := do
  let res ← za.toResult.neg q(inferInstance)
  -- We have to unpack this result due to instance issues.
  let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
  return ⟨_, vc, q($pc)⟩

/--
Definition of `pow` / `pow` 的定义

English:
definition pow
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
  body: do
  match vb with
  | .const _ =>
    have lit : Q(Nat) := b.appArg!
    let res ← (NormNum.evalPow.core q($a ^ $lit) q(HPow.hPow) q($a) lit lit
      q(IsNat.raw_refl $lit) q(inferInstance) za.toResult).run
    match res with
    | none => OptionT.fail
    | some res =>
have : b =Q lit := ⟨⟩
      let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
      return ⟨_, vc, q($pc)⟩
  | _ => OptionT.fail

中文:
定义 pow
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α))
  定义体: do
  match vb with
  | .const _ =>
    have lit : Q(Nat) := b.appArg!
    let res ← (NormNum.evalPow.core q($a ^ $lit) q(HPow.hPow) q($a) lit lit
      q(IsNat.raw_refl $lit) q(inferInstance) za.toResult).run
    match res with
    | none => OptionT.fail
    | some res =>
have : b =Q lit := ⟨⟩
      let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
      return ⟨_, vc, q($pc)⟩
  | _ => OptionT.fail
-/
partial def pow {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a : Q($α)} {b : Q(Nat)} (za : RatCoeff a)
    (vb : Common.ExProdNat q($b)) :
    OptionT MetaM (Result RatCoeff q($a ^ $b)) := do
  match vb with
  | .const _ =>
    have lit : Q(Nat) := b.appArg!
    let res ← (NormNum.evalPow.core q($a ^ $lit) q(HPow.hPow) q($a) lit lit
      q(IsNat.raw_refl $lit) q(inferInstance) za.toResult).run
    match res with
    | none => OptionT.fail
    | some res =>
have : b =Q lit := ⟨⟩
      let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
      return ⟨_, vc, q($pc)⟩
  | _ => OptionT.fail

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: {u : Lean.Level} {α : Q(Type u)} (_sα : Q(CommSemiring $α))
  body: do
  match (← (Lean.observing? <| za.toResult.inv _ czα :)) with
  | some res =>
    let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
    return some ⟨_, vc, q($pc)⟩
  | none => return none

中文:
定义 inv
  签名: {u : Lean.Level} {α : Q(类型u)} (_sα : Q(交换半环 $α))
  定义体: do
  match (← (Lean.observing? <| za.toResult.inv _ czα :)) with
  | some res =>
    let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
    return some ⟨_, vc, q($pc)⟩
  | none => return none
-/
partial def inv {u : Lean.Level} {α : Q(Type u)} (_sα : Q(CommSemiring $α))
    {a : Q($α)} (czα : Option Q(CharZero $α)) (_sfα : Q(Semifield $α)) (za : RatCoeff a) :
    AtomM (Option (Result RatCoeff q($a⁻¹))) := do
  match (← (Lean.observing? <| za.toResult.inv _ czα :)) with
  | some res =>
    let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
    return some ⟨_, vc, q($pc)⟩
  | none => return none

/--
Definition of `derive` / `derive` 的定义

English:
definition derive
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (x : Q($α))
  body: do
  let res ← NormNum.derive x
  let ⟨_, va, pa⟩ ← evalCast sα res
  return ⟨_, va, q($pa)⟩

中文:
定义 derive
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α)) (x : Q($α))
  定义体: do
  let res ← NormNum.derive x
  let ⟨_, va, pa⟩ ← evalCast sα res
  return ⟨_, va, q($pa)⟩
-/
partial def derive {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (x : Q($α)) :
    MetaM (Result (Common.ExSum RatCoeff sα) q($x)) := do
  let res ← NormNum.derive x
  let ⟨_, va, pa⟩ ← evalCast sα res
  return ⟨_, va, q($pa)⟩

/--
Definition of `isOne` / `isOne` 的定义

English:
definition isOne
  signature: {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
  body: do
  let ⟨qx, _hx⟩ := zx
  if qx == 1 then
have : x =Q Nat.rawCast 1 := ⟨⟩
    assumeInstancesCommute
    return q(⟨rfl⟩)
  else
    failure

中文:
定义 isOne
  签名: {u : Lean.Level} {α : Q(类型u)} (sα : Q(交换半环 $α))
  定义体: do
  let ⟨qx, _hx⟩ := zx
  if qx == 1 then
have : x =Q Nat.rawCast 1 := ⟨⟩
    assumeInstancesCommute
    return q(⟨rfl⟩)
  else
    failure
-/
partial def isOne {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {x : Q($α)} (zx : RatCoeff x) : Option Q(IsNat $x 1) := do
  let ⟨qx, _hx⟩ := zx
  if qx == 1 then
have : x =Q Nat.rawCast 1 := ⟨⟩
    assumeInstancesCommute
    return q(⟨rfl⟩)
  else
    failure

/--
Definition of `_root_.Mathlib.Tactic.Ring.ringCompare` / `_root_.Mathlib.Tactic.Ring.ringCompare` 的定义

English:
definition _root_.Mathlib.Tactic.Ring.ringCompare
  signature: {u : Lean.Level} {α : Q(Type u)}
  body: zx.value == zy.value
  compare zx zy := compare zx.value zy.value

中文:
定义 _root_.Mathlib.Tactic.环.ringCompare
  签名: {u : Lean.Level} {α : Q(类型u)}
  定义体: zx.value == zy.value
  compare zx zy := compare zx.value zy.value
-/
partial def _root_.Mathlib.Tactic.Ring.ringCompare {u : Lean.Level} {α : Q(Type u)} :
    Common.RingCompare (α := α) RatCoeff where
  eq zx zy := zx.value == zy.value
  compare zx zy := compare zx.value zy.value

/--
Definition of `_root_.Mathlib.Tactic.Ring.ringCompute` / `_root_.Mathlib.Tactic.Ring.ringCompute` 的定义

English:
definition _root_.Mathlib.Tactic.Ring.ringCompute
  body: add sα
  mul := mul sα
  cast := cast sα cα
  neg := neg
  pow := pow sα
  inv := inv sα
  derive := derive sα
  isOne := isOne sα
  one := ⟨q((nat_lit 1).rawCast), ⟨1, none⟩, q(rfl)⟩
  toRingCompare := ringCompare

中文:
定义 _root_.Mathlib.Tactic.环.ringCompute
  定义体: add sα
  mul := mul sα
  cast := cast sα cα
  neg := neg
  pow := pow sα
  inv := inv sα
  derive := derive sα
  isOne := isOne sα
  one := ⟨q((nat_lit 1).rawCast), ⟨1, none⟩, q(rfl)⟩
  toRingCompare := ringCompare
-/
partial def _root_.Mathlib.Tactic.Ring.ringCompute
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} (cα : Common.Cache sα) :
    Common.RingCompute RatCoeff sα where
  add := add sα
  mul := mul sα
  cast := cast sα cα
  neg := neg
  pow := pow sα
  inv := inv sα
  derive := derive sα
  isOne := isOne sα
  one := ⟨q((nat_lit 1).rawCast), ⟨1, none⟩, q(rfl)⟩
  toRingCompare := ringCompare

end
end RingCompute

/--
Definition of `rcNat` / `rcNat` 的定义

English:
definition rcNat
  signature: : Common.RingCompute (u := 0) Common.btNat Common.sNat
  body: Ring.ringCompute .nat

universe u

中文:
定义 rc自然数
  签名: : Common.RingCompute (u := 0) Common.bt自然数 Common.s自然数
  定义体: Ring.ringCompute .nat

universe u

Depends on / 依赖: Common, Common.btNat, Common.sNat, Ring.ringCompute, ringCompute
-/
def rcNat : Common.RingCompute (u := 0) Common.btNat Common.sNat := Ring.ringCompute .nat

universe u

/--
Definition of `CSLift` / `CSLift` 的定义

English:
class CSLift
  parameters: (α : Type u) (β : outParam (Type u))
  axioms and operations (2):
    - lift : α -> β
    - inj : Function.Injective lift

中文:
类 CSLift
  参数: (α : 类型u) (β : outParam (类型u))
  公理与运算 (2 个):
    - lift : α -> β
    - inj : 函数.单射 lift
-/
class CSLift (α : Type u) (β : outParam (Type u)) where
  /-- `lift` is the "canonical injection" from `α` to `β` -/
  lift : α -> β
  /-- `lift` is an injective function -/
  inj : Function.Injective lift

/--
Definition of `CSLiftVal` / `CSLiftVal` 的定义

English:
class CSLiftVal
  parameters: {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β)
  axioms and operations (1):
    - eq : b = CSLift.lift a

中文:
类 CSLiftVal
  参数: {α} {β : outParam (类型u)} [CSLift α β] (a : α) (b : outParam β)
  公理与运算 (1 个):
    - eq : b = CSLift.lift a
-/
class CSLiftVal {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β) : Prop where
  /-- The output value `b` is equal to the lift of `a`. This can be supplied by the default
  instance which sets `b := lift a`, but `ring` will treat this as an atom so it is more useful
  when there are other instances which distribute addition or multiplication. -/
  eq : b = CSLift.lift a

instance (priority := low) {α β} [CSLift α β] (a : α) : CSLiftVal a (CSLift.lift a) := ⟨rfl⟩

/--
theorem `of_lift` / 定理 `of_lift`

English:
theorem of_lift
  statement: {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
  proof: inst.2 by rwa [← h1.1, ← h2.1]

中文:
定理 of_lift
  结论: {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
  证明: inst.2 by rwa [← h1.1, ← h2.1]
-/
theorem of_lift {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
    [h1 : CSLiftVal a a'] [h2 : CSLiftVal b b'] (h : a' = b') : a = b :=
inst.2 by rwa [← h1.1, ← h2.1]

open Lean Parser.Tactic Elab Command Elab.Tactic

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {α} {a b c : α} (_ : (a : α) = c) (_ : b = c)
  statement: a = b
  proof: by subst_vars; rfl

中文:
定理 of_eq
  条件: {α} {a b c : α} (_ : (a : α) = c) (_ : b = c)
  结论: a = b
  证明: by subst_vars; rfl
-/
theorem of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl

/--
This is a routine which is used to clean up the unsolved subgoal
of a failed `ring1` application. It is overridden in `Mathlib/Tactic/Ring/RingNF.lean`
to apply the `ring_nf` simp set to the goal.
-/
initialize ringCleanupRef : IO.Ref (Expr -> MetaM Expr) ← IO.mkRef pure

/--
Definition of `proveEq` / `proveEq` 的定义

English:
definition proveEq
  signature: (g : MVarId)
  body: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
try Except.ok < > synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' -> $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq

中文:
定义 proveEq
  签名: (g : MVarId)
  定义体: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
try Except.ok < > synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' -> $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq
-/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
try Except.ok < > synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' -> $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  ringCore {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    let c ← Common.mkCache sα
    profileitM Exception "ring" (← getOptions) do
      let ⟨a, va, pa⟩ ← Common.eval rcNat (ringCompute c) c e₁
      let ⟨b, vb, pb⟩ ← Common.eval rcNat (ringCompute c) c e₂
      unless va.eq rcNat (ringCompute c) vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
have : a =Q b := ⟨⟩
      return q(of_eq $pa $pb)

/--
`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g => do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt ring1] macro "ring1!" : tactic => `(tactic| ring1 !)

end
end Mathlib.Tactic.Ring
